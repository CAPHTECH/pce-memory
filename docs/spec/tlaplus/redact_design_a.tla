---- MODULE redact_design_a ----
\* Redact Design A: Redact-before-Embed
\* ADR-0003: 採用案 - 先にredact、後で埋め込み
\*
\* 検証する性質:
\* - Confidentialデータの埋め込みに機密情報が含まれない

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
  Text,
  Vector,
  SensitiveTokens  \* 機密トークンの集合

VARIABLES
  pendingTexts,
  redactedTexts,
  embeddings

vars == <<pendingTexts, redactedTexts, embeddings>>

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
  /\ redactedTexts = {}
  /\ embeddings = {}

\* ========== アクション ==========

\* ステップ1: テキスト受付
SubmitText(text, sensitivity) ==
  /\ pendingTexts' = pendingTexts \cup {[content |-> text, sensitivity |-> sensitivity]}
  /\ UNCHANGED <<redactedTexts, embeddings>>

\* ステップ2: Redact処理（Confidentialは必須redact）
RedactText(rec) ==
  /\ rec \in pendingTexts
  /\ LET redactedContent == IF rec.sensitivity = "confidential"
                            THEN Redact(rec.content)
                            ELSE rec.content
         \* Confidentialはredact済みなのでsensitiveではない
         isSensitive == IF rec.sensitivity = "confidential"
                        THEN FALSE
                        ELSE ContainsSensitive(rec.content)
     IN redactedTexts' = redactedTexts \cup {
          [content |-> redactedContent, sensitivity |-> rec.sensitivity,
           containsSensitive |-> isSensitive]
        }
  /\ pendingTexts' = pendingTexts \ {rec}
  /\ UNCHANGED <<embeddings>>

\* ステップ3: 埋め込み生成（Redact済みテキストのみ）
Embed(rec) ==
  /\ rec \in redactedTexts
  /\ \E vec \in Vector:
       embeddings' = embeddings \cup {
         [text |-> rec.content, vector |-> vec,
          containsSensitive |-> rec.containsSensitive,
          sensitivity |-> rec.sensitivity]
       }
  /\ redactedTexts' = redactedTexts \ {rec}
  /\ UNCHANGED <<pendingTexts>>

\* ========== 次状態 ==========

Next ==
  \/ \E t \in Text, s \in SensitivityLevel: SubmitText(t, s)
  \/ \E rec \in pendingTexts: RedactText(rec)
  \/ \E rec \in redactedTexts: Embed(rec)

Spec == Init /\ [][Next]_vars

\* ========== 安全性不変条件 ==========

\* Confidentialデータの埋め込みに機密情報が含まれない
Inv_NoSensitiveInConfidentialEmbedding ==
  \A emb \in embeddings:
    emb.sensitivity = "confidential" => emb.containsSensitive = FALSE

\* 状態制約（状態爆発対策）
StateConstraint ==
  /\ Cardinality(embeddings) <= 3
  /\ Cardinality(pendingTexts) <= 2
  /\ Cardinality(redactedTexts) <= 2

====
