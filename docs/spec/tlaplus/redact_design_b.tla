---- MODULE redact_design_b ----
\* Redact Design B: Embed-before-Redact（問題のある設計）
\* ADR-0003: 比較用 - 先に埋め込み、後でredact
\*
\* 検証する性質:
\* - 反例発見を期待: 機密情報がベクトルに含まれる

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
  Text,
  Vector,
  SensitiveTokens  \* 機密トークンの集合

VARIABLES
  pendingTexts,
  rawEmbeddings,    \* redact前の埋め込み（機密情報含む可能性）
  finalEmbeddings

vars == <<pendingTexts, rawEmbeddings, finalEmbeddings>>

\* ========== 型定義 ==========

SensitivityLevel == {"public", "internal", "confidential"}

\* ========== ヘルパー関数 ==========

\* テキストに機密トークンが含まれるか
ContainsSensitive(text) ==
  text \in SensitiveTokens

\* Redact処理（機密トークンを除去）
Redact(text) ==
  IF ContainsSensitive(text) THEN CHOOSE t \in Text: ~ContainsSensitive(t) ELSE text

\* ========== 初期状態 ==========

Init ==
  /\ pendingTexts = {}
  /\ rawEmbeddings = {}
  /\ finalEmbeddings = {}

\* ========== アクション ==========

\* ステップ1: テキスト受付
SubmitText(text, sensitivity) ==
  /\ pendingTexts' = pendingTexts \cup {[content |-> text, sensitivity |-> sensitivity]}
  /\ UNCHANGED <<rawEmbeddings, finalEmbeddings>>

\* ステップ2: 埋め込み生成（Redact前 - 問題: 機密情報がベクトルに含まれる）
Embed(rec) ==
  /\ rec \in pendingTexts
  /\ \E vec \in Vector:
       rawEmbeddings' = rawEmbeddings \cup {
         [text |-> rec.content, vector |-> vec, sensitivity |-> rec.sensitivity,
          containsSensitive |-> ContainsSensitive(rec.content)]
       }
  /\ pendingTexts' = pendingTexts \ {rec}
  /\ UNCHANGED <<finalEmbeddings>>

\* ステップ3: Redact処理（埋め込み後 - 問題: ベクトルから機密情報は除去できない）
RedactAfterEmbed(emb) ==
  /\ emb \in rawEmbeddings
  \* 問題: ベクトルはそのまま（機密情報が埋め込まれたまま）
  /\ finalEmbeddings' = finalEmbeddings \cup {
       [text |-> Redact(emb.text), vector |-> emb.vector,
        containsSensitive |-> emb.containsSensitive,  \* まだTRUEの可能性
        sensitivity |-> emb.sensitivity]
     }
  /\ rawEmbeddings' = rawEmbeddings \ {emb}
  /\ UNCHANGED <<pendingTexts>>

\* ========== 次状態 ==========

Next ==
  \/ \E t \in Text, s \in SensitivityLevel: SubmitText(t, s)
  \/ \E rec \in pendingTexts: Embed(rec)
  \/ \E emb \in rawEmbeddings: RedactAfterEmbed(emb)

Spec == Init /\ [][Next]_vars

\* ========== 安全性不変条件 ==========

\* 埋め込みに機密情報が含まれない（反例発見を期待）
\* この不変条件は設計Bの問題を示すために意図的に破られる
Inv_NoSensitiveInEmbedding ==
  \A emb \in finalEmbeddings:
    emb.containsSensitive = FALSE

\* 状態制約（状態爆発対策）
StateConstraint ==
  /\ Cardinality(finalEmbeddings) <= 3
  /\ Cardinality(pendingTexts) <= 2
  /\ Cardinality(rawEmbeddings) <= 2

====
