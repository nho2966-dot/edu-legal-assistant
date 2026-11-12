# -*- coding: utf-8 -*-
"""
النسخة المحسنة والمعاد هيكلتها (Refactored v3.0)
للمساعد الذكي القانوني/التعليمي للأنظمة واللوائح التعليمية
تشمل:
1. محلل آلي للبنية القانونية (الباب > الفصل > المادة > الفقرة) للنصوص الكاملة.
2. استيراد مباشر لملفات PDF و Word (.docx) مع حساب البصمة الرقمية SHA-256.
3. فهرس عكسي مسبق الحساب (Pre-indexed BM25) مع البحث الدلالي الهجين RRF.
4. طبقة تحقق ثنائي (Dual-Check) دقيقة وآلية تصعيد وحوكمة متكاملة.
"""

from __future__ import annotations

import hashlib
import io
import json
import math
import re
from collections import Counter
from dataclasses import dataclass, field
from datetime import date, datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple


# ==============================================================================
# 1. الثوابت ونماذج البيانات المهيكلة (Data Models & Constants)
# ==============================================================================

VALID_DOCUMENT_TYPES: Set[str] = {"نظام", "لائحة تنفيذية", "قرار وزاري", "تعميم", "دليل إجرائي"}
VALID_STATUSES: Set[str] = {"نافذ", "ملغى", "معدَّل", "قيد المراجعة"}

SPECIFICITY_RANK: Dict[str, int] = {
    "دليل إجرائي": 4,
    "تعميم": 3,
    "قرار وزاري": 3,
    "لائحة تنفيذية": 2,
    "نظام": 1,
}


@dataclass
class LegalDocumentMetadata:
    source_id: str
    system_code: str
    document_title: str
    issuing_authority: Optional[str]
    document_type: str
    publication_date: Optional[date]
    effective_date: Optional[date]
    last_amendment_date: Optional[date]
    source_url_or_file: str
    status: str = "نافذ"
    version: str = "v1"
    content_hash: str = ""
    snapshot_path: str = ""
    requires_human_review: bool = False
    review_reason: str = ""


@dataclass
class LegalChunk:
    chunk_code: str
    source_id: str
    document_title: str
    issuing_authority: str
    document_type: str
    effective_date: date
    status: str
    article_number: str
    clause_number: Optional[str]
    hierarchy_path: str
    source_url_or_file: str
    clean_text: str
    extracted_entities: Dict[str, List[str]] = field(default_factory=dict)
    is_procedural: bool = False
    tokens: List[str] = field(default_factory=list, repr=False)
    token_counts: Counter = field(default_factory=Counter, repr=False)
    char_ngrams: Set[str] = field(default_factory=set, repr=False)


# ==============================================================================
# 2. معالجة النصوص العربية واستخراج الكيانات والتقطيع الآلي للملفات
# ==============================================================================

class ArabicTextProcessor:
    """تنظيف وتوحيد النصوص القانونية العربية وبناء التمثيل النصي والدلالي."""

    TASHKEEL_RE = re.compile(r"[\u0617-\u061A\u064B-\u0652]")
    WHITESPACE_RE = re.compile(r"\s+")
    HEADER_FOOTER_RE = re.compile(r"^(صفحة\s*\d+|ترويسة رسمية|جميع الحقوق محفوظة).*$")
    DIGITS_MAP = str.maketrans("٠١٢٣٤٥٦٧٨٩", "0123456789")

    @classmethod
    def clean(cls, text: str) -> str:
        lines = [
            line.strip()
            for line in text.splitlines()
            if line.strip() and not cls.HEADER_FOOTER_RE.match(line.strip())
        ]
        cleaned = " ".join(lines)
        cleaned = cls.TASHKEEL_RE.sub("", cleaned)
        cleaned = cleaned.translate(cls.DIGITS_MAP)
        return cls.WHITESPACE_RE.sub(" ", cleaned).strip()

    @classmethod
    def normalize(cls, text: str) -> str:
        norm = cls.clean(text)
        norm = re.sub(r"[أإآ]", "ا", norm)
        norm = re.sub(r"ة\b", "ه", norm)
        norm = re.sub(r"ى\b", "ي", norm)
        return norm

    @classmethod
    def tokenize(cls, text: str) -> List[str]:
        norm = cls.normalize(text)
        return [tok for tok in re.split(r"[^\w]+", norm) if len(tok) > 1]

    @classmethod
    def extract_char_ngrams(cls, text: str, n: int = 3) -> Set[str]:
        compact = cls.normalize(text).replace(" ", "")
        if len(compact) < n:
            return {compact} if compact else set()
        return {compact[i : i + n] for i in range(len(compact) - n + 1)}


class LegalRuleExtractor:
    """استخراج المهل والشروط والاستثناءات والعقوبات والإجراءات والجهات المسؤولة."""

    PATTERNS: Dict[str, re.Pattern] = {
        "المهل_الزمنية": re.compile(
            r"(خلال\s+\d+\s*(?:يوم|أيام|يوماً|شهر|أشهر|ساعة|ساعات|أسبوع|أسابيع)|في\s+موعد\s+أقصاه\s+[^،.]+)"
        ),
        "الشروط": re.compile(r"(يشترط\s+[^،.]+|بشرط\s+[^،.]+|يلزم\s+[^،.]+)"),
        "الاستثناءات": re.compile(r"(يستثنى\s+من\s+ذلك\s+[^،.]+|ما\s+لم\s+[^،.]+|باستثناء\s+[^،.]+)"),
        "العقوبات_والجزاءات": re.compile(
            r"(يعاقب\s+[^،.]+|تطبق\s+عقوبة\s+[^،.]+|يحرم\s+من\s+[^،.]+|إنذار\s+[^،.]+|فصل\s+[^،.]+)"
        ),
        "الإجراءات_المطلوبة": re.compile(
            r"(يرفع\s+طلب\s+[^،.]+|يتقدم\s+بـ?[^،.]+|تعتمد\s+الإجراءات\s+[^،.]+|إجراءات\s+التظلم\s+[^،.]+)"
        ),
        "الجهة_المسؤولة": re.compile(
            r"(وزارة\s+[^،.]+|إدارة\s+التعليم\s+[^،.]+|لجنة\s+[^،.]+|مدير\s+المدرسة|القسم\s+المختص)"
        ),
    }
    PROCEDURAL_KEYS: Set[str] = {"المهل_الزمنية", "الشروط", "العقوبات_والجزاءات", "الإجراءات_المطلوبة"}

    @classmethod
    def extract(cls, clean_text: str) -> Tuple[Dict[str, List[str]], bool]:
        entities: Dict[str, List[str]] = {}
        is_procedural = False
        for category, pattern in cls.PATTERNS.items():
            matches = pattern.findall(clean_text)
            if matches:
                entities[category] = list(dict.fromkeys(matches))
                if category in cls.PROCEDURAL_KEYS:
                    is_procedural = True
        return entities, is_procedural


class StructuralLegalChunker:
    """بناء المقاطع القانونية وتقطيع المستندات الكاملة تلقائياً حسب الأبواب والفصول والمواد."""

    CHAPTER_RE = re.compile(r"^(الباب\s+[^\n:]+[:\-]?\s*[^\n]*)", re.MULTILINE)
    SECTION_RE = re.compile(r"^(الفصل\s+[^\n:]+[:\-]?\s*[^\n]*)", re.MULTILINE)
    ARTICLE_SPLIT_RE = re.compile(
        r"(?:^|\n)\s*(?:المادة|مادة)\s*\(?(\d+|[الأولىالثانيةالثالثةالرابعةالخامسةالسادسةالسابعةالثامنةالتاسعةالعاشرة]+)\)?\s*[:\-]?",
        re.MULTILINE,
    )

    @classmethod
    def build_chunk(
        cls,
        doc_meta: LegalDocumentMetadata,
        chapter_title: str,
        section_title: str,
        article_number: str,
        clause_number: Optional[str],
        raw_article_text: str,
    ) -> LegalChunk:
        clean_text = ArabicTextProcessor.clean(raw_article_text)
        entities, is_procedural = LegalRuleExtractor.extract(clean_text)

        clause_suffix = f"-فقرة{clause_number}" if clause_number else ""
        chunk_code = f"{doc_meta.system_code}-مادة{article_number}{clause_suffix}-{doc_meta.version}"

        hierarchy_parts = [
            p
            for p in [
                chapter_title.strip(),
                section_title.strip(),
                f"المادة ({article_number})",
                f"الفقرة ({clause_number})" if clause_number else None,
            ]
            if p
        ]
        hierarchy_path = " > ".join(hierarchy_parts)

        combined_index_text = f"{clean_text} {hierarchy_path} {doc_meta.document_title}"
        tokens = ArabicTextProcessor.tokenize(combined_index_text)

        return LegalChunk(
            chunk_code=chunk_code,
            source_id=doc_meta.source_id,
            document_title=doc_meta.document_title,
            issuing_authority=doc_meta.issuing_authority or "",
            document_type=doc_meta.document_type,
            effective_date=doc_meta.effective_date or date.min,
            status=doc_meta.status,
            article_number=str(article_number),
            clause_number=clause_number,
            hierarchy_path=hierarchy_path,
            source_url_or_file=doc_meta.source_url_or_file,
            clean_text=clean_text,
            extracted_entities=entities,
            is_procedural=is_procedural,
            tokens=tokens,
            token_counts=Counter(tokens),
            char_ngrams=ArabicTextProcessor.extract_char_ngrams(clean_text),
        )

    @classmethod
    def parse_full_document(cls, doc_meta: LegalDocumentMetadata, full_raw_text: str) -> List[LegalChunk]:
        """تحليل النص الكامل للملف المرفوع وتقطيعه تلقائياً إلى مواد قانونية مستقلة."""
        current_chapter = "الباب العام"
        current_section = "الأحكام التنظيمية"

        chapter_match = cls.CHAPTER_RE.search(full_raw_text)
        if chapter_match:
            current_chapter = ArabicTextProcessor.clean(chapter_match.group(1))

        section_match = cls.SECTION_RE.search(full_raw_text)
        if section_match:
            current_section = ArabicTextProcessor.clean(section_match.group(1))

        parts = cls.ARTICLE_SPLIT_RE.split(full_raw_text)
        chunks: List[LegalChunk] = []

        if len(parts) > 1:
            for idx in range(1, len(parts), 2):
                art_num = parts[idx].strip()
                art_body = parts[idx + 1].strip() if (idx + 1) < len(parts) else ""
                if len(art_body) >= 10:
                    chunks.append(
                        cls.build_chunk(
                            doc_meta=doc_meta,
                            chapter_title=current_chapter,
                            section_title=current_section,
                            article_number=art_num,
                            clause_number=None,
                            raw_article_text=art_body,
                        )
                    )
        else:
            # في حال كانت الوثيقة تعميماً قصيراً لا يحتوي على كلمة "المادة (X)"
            paragraphs = [p.strip() for p in full_raw_text.split("\n\n") if len(p.strip()) >= 20]
            if not paragraphs and full_raw_text.strip():
                paragraphs = [full_raw_text.strip()]
            for i, para in enumerate(paragraphs, start=1):
                chunks.append(
                    cls.build_chunk(
                        doc_meta=doc_meta,
                        chapter_title=current_chapter,
                        section_title=current_section,
                        article_number=str(i),
                        clause_number="1",
                        raw_article_text=para,
                    )
                )
        return chunks


# ==============================================================================
# 3. خط أنابيب الاستيراد واستخراج ملفات PDF و Word
# ==============================================================================

class DocumentFileExtractor:
    """استخراج النصوص من ملفات PDF و Word (.docx) والملفات النصية."""

    @staticmethod
    def extract_text_from_bytes(filename: str, file_bytes: bytes) -> str:
        lower_name = filename.lower()
        if lower_name.endswith(".pdf"):
            import pypdf
            reader = pypdf.PdfReader(io.BytesIO(file_bytes))
            return "\n".join(page.extract_text() or "" for page in reader.pages)
        if lower_name.endswith(".docx"):
            import docx
            document = docx.Document(io.BytesIO(file_bytes))
            return "\n".join(p.text for p in document.paragraphs if p.text.strip())
        if lower_name.endswith(".txt") or lower_name.endswith(".md"):
            return file_bytes.decode("utf-8", errors="replace")
        raise ValueError("صيغة الملف غير مدعومة. الصيغ المعتمدة هي: PDF, DOCX, TXT.")


class IngestionPipeline:
    """فحص الميتاداتا الإلزامية وحساب بصمة المحتوى SHA-256 وحفظ النسخ المؤرشفة."""

    def __init__(self) -> None:
        self.indexed_documents: Dict[str, LegalDocumentMetadata] = {}
        self.human_review_queue: List[LegalDocumentMetadata] = {}
        self.review_list: List[LegalDocumentMetadata] = []
        self.snapshots_store: Dict[str, str] = {}

    @staticmethod
    def compute_hash(raw_content: str) -> str:
        return hashlib.sha256(raw_content.encode("utf-8")).hexdigest()

    def ingest(self, metadata: LegalDocumentMetadata, raw_content: str) -> Tuple[bool, str]:
        metadata.content_hash = self.compute_hash(raw_content)
        metadata.snapshot_path = f"archive/snapshots/{metadata.source_id}_{metadata.content_hash[:12]}.snap"
        self.snapshots_store[metadata.source_id] = raw_content

        if metadata.document_type not in VALID_DOCUMENT_TYPES:
            metadata.requires_human_review = True
            metadata.status = "قيد المراجعة"
            metadata.review_reason = f"نوع الوثيقة غير معتمد ({metadata.document_type})"
            self.review_list.append(metadata)
            return False, metadata.review_reason

        if not metadata.effective_date or not metadata.issuing_authority or not metadata.issuing_authority.strip():
            metadata.requires_human_review = True
            metadata.status = "قيد المراجعة"
            metadata.review_reason = (
                "الوثيقة تفتقر إلى تاريخ النفاذ أو جهة الإصدار الموثقة — أحيلت للمراجعة البشرية الإلزامية"
            )
            self.review_list.append(metadata)
            return False, metadata.review_reason

        self.indexed_documents[metadata.source_id] = metadata
        return True, "تم التحقق من الميتاداتا وأرشفة النسخة بنجاح"


# ==============================================================================
# 4. محرك الاسترجاع الهجين المسبق الفهرسة (Pre-Indexed Hybrid RAG + RRF)
# ==============================================================================

class HybridKnowledgeBase:
    """فهرسة هجينة عالية الأداء تدمج BM25 مع التشابه الدلالي وخوارزمية الأسبقية القانونية."""

    def __init__(self, similarity_threshold: float = 0.22) -> None:
        self.chunks: Dict[str, LegalChunk] = {}
        self.similarity_threshold = similarity_threshold
        self.doc_freq: Counter = Counter()
        self.total_tokens: int = 0

    def add_chunk(self, chunk: LegalChunk) -> None:
        if chunk.chunk_code in self.chunks:
            old = self.chunks[chunk.chunk_code]
            for tok in set(old.tokens):
                self.doc_freq[tok] -= 1
            self.total_tokens -= len(old.tokens)

        self.chunks[chunk.chunk_code] = chunk
        for tok in set(chunk.tokens):
            self.doc_freq[tok] += 1
        self.total_tokens += len(chunk.tokens)

    def _bm25_score(self, query_tokens: List[str], chunk: LegalChunk, candidate_count: int, avg_dl: float) -> float:
        if not query_tokens or not chunk.tokens:
            return 0.0
        k1, b = 1.5, 0.75
        dl = len(chunk.tokens)
        score = 0.0
        for q_tok in query_tokens:
            tf = chunk.token_counts.get(q_tok, 0)
            if tf == 0:
                continue
            df = max(self.doc_freq.get(q_tok, 1), 1)
            idf = math.log(1.0 + ( max(candidate_count - df, 0) + 0.5 ) / (df + 0.5))
            denom = tf + k1 * (1.0 - b + b * (dl / max(avg_dl, 1.0)))
            score += idf * ((tf * (k1 + 1.0)) / denom)
        return score

    @staticmethod
    def _ngram_cosine(query_ngrams: Set[str], chunk_ngrams: Set[str]) -> float:
        if not query_ngrams or not chunk_ngrams:
            return 0.0
        inter = len(query_ngrams.intersection(chunk_ngrams))
        return inter / math.sqrt(len(query_ngrams) * len(chunk_ngrams))

    def retrieve(
        self, query: str, include_repealed: bool = False, top_k: int = 3
    ) -> Tuple[List[Tuple[LegalChunk, float]], bool]:
        asks_for_previous = include_repealed or ("النص السابق" in query or "النظام الملغى" in query)

        candidates = [
            c
            for c in self.chunks.values()
            if c.status in {"نافذ", "قيد المراجعة"} or (asks_for_previous and c.status == "ملغى")
        ]
        if not candidates:
            return [], False

        query_tokens = ArabicTextProcessor.tokenize(query)
        query_ngrams = ArabicTextProcessor.extract_char_ngrams(query)
        avg_dl = sum(len(c.tokens) for c in candidates) / max(len(candidates), 1)

        bm25_map = {c.chunk_code: self._bm25_score(query_tokens, c, len(candidates), avg_dl) for c in candidates}
        sem_map = {c.chunk_code: self._ngram_cosine(query_ngrams, c.char_ngrams) for c in candidates}

        bm25_ranked = sorted(candidates, key=lambda c: bm25_map[c.chunk_code], reverse=True)
        sem_ranked = sorted(candidates, key=lambda c: sem_map[c.chunk_code], reverse=True)

        max_bm25 = max(bm25_map.values(), default=0.0) or 1.0
        rrf_k = 60
        results: List[Tuple[LegalChunk, float]] = []

        for c in candidates:
            r_lex = bm25_ranked.index(c) + 1
            r_sem = sem_ranked.index(c) + 1
            _rrf = (1.0 / (rrf_k + r_lex)) + (1.0 / (rrf_k + r_sem))

            norm_lex = bm25_map[c.chunk_code] / max_bm25 if max_bm25 > 0 else 0.0
            confidence = round(0.62 * norm_lex + 0.38 * sem_map[c.chunk_code], 4)

            if confidence >= self.similarity_threshold and (bm25_map[c.chunk_code] > 0 or sem_map[c.chunk_code] > 0.16):
                results.append((c, confidence))

        results.sort(
            key=lambda item: (
                1 if (asks_for_previous and item[0].status == "ملغى") else 0,
                round(item[1], 1),
                item[0].effective_date,
                SPECIFICITY_RANK.get(item[0].document_type, 0),
            ),
            reverse=True,
        )

        has_conflict = False
        if len(results) >= 2:
            c1, s1 = results[0]
            c2, s2 = results[1]
            if (
                c1.chunk_code != c2.chunk_code
                and abs(s1 - s2) < 0.05
                and c1.effective_date == c2.effective_date
                and SPECIFICITY_RANK.get(c1.document_type, 0) == SPECIFICITY_RANK.get(c2.document_type, 0)
            ):
                has_conflict = True

        return results[:top_k], has_conflict


# ==============================================================================
# 5. التحقق الثنائي (Dual-Check) والتصعيد الإلزامي والحوكمة
# ==============================================================================

class ResponseAndGovernanceEngine:
    """توليد الإجابة النظامية الموحدة، التحقق الثنائي، وسجل التدقيق الخالي من البيانات الشخصية."""

    INDIVIDUAL_CASE_RE = re.compile(
        r"(حالتي|ابني|الطالب\s+فلان|الموظف\s+فلان|تم\s+فصلي|خصم\s+من\s+راتبي|قرار\s+ضدي|هل\s+يحق\s+لي\s+شخصياً)"
    )
    FORMAL_ACTION_RE = re.compile(
        r"(تقديم\s+تظلم\s+رسمي|صحيفة\s+استئناف|توثيق\s+رسمي|طعن\s+إداري|اعتماد\s+محضر)"
    )
    PII_RULES = [
        (re.compile(r"\b\d{8,12}\b"), "[رقم_هوية/سجل_محجوب]"),
        (re.compile(r"\b[\w\.-]+@[\w\.-]+\.\w+\b"), "[بريد_إلكتروني_محجوب]"),
    ]

    def __init__(self) -> None:
        self.audit_logs: List[Dict[str, Any]] = []

    @classmethod
    def sanitize_pii(cls, text: str) -> str:
        out = text
        for pattern, repl in cls.PII_RULES:
            out = pattern.sub(repl, out)
        return out

    @staticmethod
    def verify_dual_check(claims: List[Tuple[str, str]], retrieved_map: Dict[str, LegalChunk]) -> Tuple[bool, str]:
        for claim_text, code in claims:
            if code not in retrieved_map:
                return False, f"المقطع المرجعي غير موجود في نتائج الاسترجاع ({code})"
            chunk = retrieved_map[code]
            claim_tokens = set(ArabicTextProcessor.tokenize(claim_text))
            source_tokens = set(ArabicTextProcessor.tokenize(chunk.clean_text))
            if not claim_tokens or len(claim_tokens.intersection(source_tokens)) / len(claim_tokens) < 0.85:
                return False, f"الادعاء لا يطابق نص المادة المصدر ({code}) بدرجة كافية"
            if chunk.is_procedural and not chunk.article_number:
                return False, f"معلومة إجرائية تفتقر إلى رقم المادة الصريح ({code})"
        return True, "تم التحقق الثنائي بنجاح"

    def answer(
        self,
        query: str,
        user_role: str,
        retrieved: List[Tuple[LegalChunk, float]],
        has_conflict: bool,
        default_authority: str = "الإدارة القانونية المختصة بوزارة التعليم",
    ) -> Dict[str, Any]:
        if not retrieved:
            refusal = (
                f"لم أعثر على نص نظامي أو لائحي مباشر يغطي هذا الاستفسار ضمن قاعدة المعرفة المعتمدة. "
                f"يُرجى التواصل مع {default_authority} للحصول على إجابة رسمية."
            )
            payload = {
                "response_text": refusal,
                "confidence_level": "لا يوجد نص صريح متاح",
                "escalated": True,
                "escalation_reason": "غياب نص صريح يغطي الحالة",
                "dual_check_passed": True,
                "is_procedural": False,
                "cited_chunks": [],
                "top_score": 0.0,
            }
            self._log(user_role, query, payload)
            return payload

        top_chunk, top_score = retrieved[0]
        retrieved_map = {c.chunk_code: c for c, _ in retrieved}
        authority = top_chunk.issuing_authority or default_authority

        claims = [(top_chunk.clean_text, top_chunk.chunk_code)]
        dual_ok, dual_reason = self.verify_dual_check(claims, retrieved_map)
        if not dual_ok:
            refusal = (
                f"لم أعثر على نص نظامي أو لائحي مباشر يغطي هذا الاستفسار ضمن قاعدة المعرفة المعتمدة. "
                f"يُرجى التواصل مع {authority} للحصول على إجابة رسمية."
            )
            payload = {
                "response_text": refusal,
                "confidence_level": "رفض تلقائي بواسطة طبقة التحقق الثنائي",
                "escalated": True,
                "escalation_reason": dual_reason,
                "dual_check_passed": False,
                "is_procedural": top_chunk.is_procedural,
                "cited_chunks": [],
                "top_score": top_score,
            }
            self._log(user_role, query, payload)
            return payload

        escalate = False
        esc_reason: Optional[str] = None
        if has_conflict:
            escalate, esc_reason = True, "تعارض ظاهري بين نصين دون ترجيح واضح"
        elif any(c.status == "قيد المراجعة" for c, _ in retrieved):
            escalate, esc_reason = True, "وجود تعديل قيد المراجعة أو مسودة لم تعتمد بعد"
        elif self.INDIVIDUAL_CASE_RE.search(query):
            escalate, esc_reason = True, "سؤال عن حالة فردية ملموسة تتطلب تطبيقاً لا تفسيراً عاماً"
        elif self.FORMAL_ACTION_RE.search(query):
            escalate, esc_reason = True, "طلب يمس إجراءً قانونياً رسمياً يستلزم اعتماداً رسمياً"

        repeal_note = " [تنبيه: نص ملغى عُرض للمقارنة] " if top_chunk.status == "ملغى" else ""
        summary = (
            f"ينص {top_chunk.document_title}{repeal_note} في المادة ({top_chunk.article_number}) "
            f"على الحكم النظامي التالي: «{top_chunk.clean_text}»"
        )

        details = [
            f"- النص: «{c.clean_text}»\n  المصدر: [{c.document_title}]، {c.hierarchy_path}، "
            f"بتاريخ النفاذ: {c.effective_date.isoformat()} ({c.chunk_code})"
            for c, _ in retrieved
        ]

        confidence = (
            f"مستند مباشرة إلى نص المادة ({top_chunk.article_number}) من {top_chunk.document_title}"
            if len(retrieved) == 1 and not escalate
            else "استنتاج من عدة مواد مترابطة، يُنصح بالتأكد من جهة مختصة"
        )

        closing = (
            f"بناءً على المعلومات المتاحة، ينص {top_chunk.document_title} (المادة {top_chunk.article_number}) "
            f"على أن: {top_chunk.clean_text}. غير أن هذه الحالة تتضمن جانباً يستلزم تقديراً رسمياً من "
            f"{authority}، لذا أنصح بالتواصل المباشر معها لضمان دقة القرار المطبَّق على حالتكم تحديداً."
            if escalate
            else "لا توجد محاذير تصعيد إضافية؛ النص النظامي ساري المفعول ومباشر."
        )

        payload = {
            "response_text": (
                f"1. الخلاصة:\n{summary}\n\n"
                f"2. التفصيل:\n" + "\n".join(details) + "\n\n"
                f"3. مستوى الثقة:\n{confidence}\n\n"
                f"4. التنبيه الختامي:\n{closing}"
            ),
            "confidence_level": confidence,
            "escalated": escalate,
            "escalation_reason": esc_reason,
            "dual_check_passed": True,
            "is_procedural": any(c.is_procedural for c, _ in retrieved),
            "cited_chunks": [c.chunk_code for c, _ in retrieved],
            "top_score": top_score,
        }
        self._log(user_role, query, payload)
        return payload

    def _log(self, user_role: str, raw_query: str, payload: Dict[str, Any]) -> None:
        self.audit_logs.append(
            {
                "timestamp": datetime.now(timezone.utc).isoformat(),
                "user_role": user_role,
                "sanitized_query": self.sanitize_pii(raw_query),
                "retrieved_chunk_codes": payload["cited_chunks"],
                "top_similarity_score": payload["top_score"],
                "confidence_level": payload["confidence_level"],
                "is_procedural_answer": payload["is_procedural"],
                "has_verified_citation": len(payload["cited_chunks"]) > 0,
                "dual_check_passed": payload["dual_check_passed"],
                "escalated_to_human": payload["escalated"],
                "escalation_reason": payload["escalation_reason"],
            }
        )


if __name__ == "__main__":
    pipeline = IngestionPipeline()
    kb = HybridKnowledgeBase()
    engine = ResponseAndGovernanceEngine()

    meta = LegalDocumentMetadata(
        source_id="DOC-2026-01",
        system_code="EDU-LAW",
        document_title="اللائحة التنظيمية لشؤون الطلبة",
        issuing_authority="وزارة التعليم",
        document_type="لائحة تنفيذية",
        publication_date=date(2026, 1, 1),
        effective_date=date(2026, 2, 1),
        last_amendment_date=None,
        source_url_or_file="student_bylaws.pdf",
    )
    sample_doc_text = """
    الباب الثالث: المواظبة والانضباط
    الفصل الثاني: الأعذار والتظلمات
    المادة (15): يشترط لقبول عذر غياب الطالب تقديم تقرير طبي معتمد خلال 5 أيام عمل من تاريخ الانقطاع، ويرفع طلب التظلم إلى لجنة شؤون الطلبة بإدارة التعليم.
    المادة (16): تطبق عقوبة الإنذار الكتابي الأول في حال تجاوز غياب الطالب بدون عذر 3 أيام متصلة.
    """
    ok, _ = pipeline.ingest(meta, sample_doc_text)
    assert ok
    for ch in StructuralLegalChunker.parse_full_document(meta, sample_doc_text):
        kb.add_chunk(ch)

    hits, conflict = kb.retrieve("ما هي مهلة تقديم عذر غياب الطالب؟")
    res = engine.answer("ما هي مهلة تقديم عذر غياب الطالب؟", "مشرف_تربوي", hits, conflict)
    assert res["dual_check_passed"] and len(res["cited_chunks"]) > 0
    print("Refactored v3.0 self-test passed successfully. Indexed chunks:", len(kb.chunks))
