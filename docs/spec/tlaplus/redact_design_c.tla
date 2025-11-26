---- MODULE redact_design_c ----
\* Redact Design C: 選択可能（問題のある設計）
\* ADR-0003: 比較用 - リクエストごとに順序を指定
\*
\* 検証する性質:
\* - 反例発見を期待: 誤選択による漏洩リスク

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
  Text,
  Vector,
  SensitiveTokens  \* 機密トークンの集合

VARIABLES
  pendingTexts,
  embeddings,
  leakedData  \* 漏洩検出用

vars == <<pendingTexts, embeddings, leakedData>>

\* ========== 型定義 ==========

SensitivityLevel == {"public", "internal", "confidential"}
RedactOrder == {"redact_first", "embed_first"}

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
  /\ embeddings = {}
  /\ leakedData = {}

\* ========== アクション ==========

\* テキスト受付（順序指定付き）
SubmitText(text, sensitivity, order) ==
  /\ pendingTexts' = pendingTexts \cup {
       [content |-> text, sensitivity |-> sensitivity, order |-> order]
     }
  /\ UNCHANGED <<embeddings, leakedData>>

\* 処理（順序に応じて処理）
Process(rec) ==
  /\ rec \in pendingTexts
  /\ \E vec \in Vector:
       LET processed == IF rec.order = "redact_first"
                        THEN [text |-> Redact(rec.content), vector |-> vec,
                              containsSensitive |-> FALSE]
                        ELSE [text |-> rec.content, vector |-> vec,
                              containsSensitive |-> ContainsSensitive(rec.content)]
       IN /\ embeddings' = embeddings \cup {processed}
          \* 漏洩検出: Confidentialデータがembed_firstで処理された場合
          /\ IF rec.sensitivity = "confidential" /\ rec.order = "embed_first"
             THEN leakedData' = leakedData \cup {rec.content}
             ELSE UNCHANGED leakedData
  /\ pendingTexts' = pendingTexts \ {rec}

\* ========== 次状態 ==========

Next ==
  \/ \E t \in Text, s \in SensitivityLevel, o \in RedactOrder: SubmitText(t, s, o)
  \/ \E rec \in pendingTexts: Process(rec)

Spec == Init /\ [][Next]_vars

\* ========== 安全性不変条件 ==========

\* 漏洩データがない（反例発見を期待）
\* この不変条件は設計Cの問題を示すために意図的に破られる
Inv_NoLeakedData ==
  leakedData = {}

\* 状態制約（状態爆発対策）
StateConstraint ==
  /\ Cardinality(embeddings) <= 3
  /\ Cardinality(pendingTexts) <= 2
  /\ Cardinality(leakedData) <= 2

====
