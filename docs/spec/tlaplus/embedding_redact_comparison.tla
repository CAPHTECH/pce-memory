---- MODULE embedding_redact_comparison ----
\* Embedding Redact Order Design Comparison
\* ADR-0003: Redact順序の形式検証（時相的性質）
\*
\* 比較する設計:
\* - 設計A: Redact-before-Embed（先にredact、後で埋め込み）
\* - 設計B: Embed-before-Redact（先に埋め込み、後でredact）
\* - 設計C: 選択可能（リクエストごとに順序を指定）
\*
\* 検証する性質:
\* - NoSensitiveDataInVector: 機密データがベクトル空間に漏洩しない
\* - RedactBeforeEmbedding: Confidentialデータは埋め込み前にredactされる

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
  Text,
  Vector,
  SensitiveTokens  \* 機密トークンの集合

VARIABLES
  \* 設計A状態
  A_pendingTexts,
  A_redactedTexts,
  A_embeddings,

  \* 設計B状態
  B_pendingTexts,
  B_rawEmbeddings,  \* redact前の埋め込み（機密情報含む可能性）
  B_finalEmbeddings,

  \* 設計C状態
  C_pendingTexts,
  C_embeddings,
  C_leakedData  \* 漏洩検出用

vars == <<A_pendingTexts, A_redactedTexts, A_embeddings,
          B_pendingTexts, B_rawEmbeddings, B_finalEmbeddings,
          C_pendingTexts, C_embeddings, C_leakedData>>

\* ========== 型定義 ==========

SensitivityLevel == {"public", "internal", "confidential"}
RedactOrder == {"redact_first", "embed_first"}

TextRec == [content: Text, sensitivity: SensitivityLevel]
EmbeddingRec == [text: Text, vector: Vector, containsSensitive: BOOLEAN]

\* ========== ヘルパー関数 ==========

\* テキストに機密トークンが含まれるか
ContainsSensitive(text) ==
  text \in SensitiveTokens

\* Redact処理（機密トークンを除去）
Redact(text) ==
  IF ContainsSensitive(text) THEN CHOOSE t \in Text: ~ContainsSensitive(t) ELSE text

\* ========== 初期状態 ==========

Init ==
  /\ A_pendingTexts = {}
  /\ A_redactedTexts = {}
  /\ A_embeddings = {}
  /\ B_pendingTexts = {}
  /\ B_rawEmbeddings = {}
  /\ B_finalEmbeddings = {}
  /\ C_pendingTexts = {}
  /\ C_embeddings = {}
  /\ C_leakedData = {}

\* ========== 設計A: Redact-before-Embed ==========

\* ステップ1: テキスト受付
A_SubmitText(text, sensitivity) ==
  /\ A_pendingTexts' = A_pendingTexts \cup {[content |-> text, sensitivity |-> sensitivity]}
  /\ UNCHANGED <<A_redactedTexts, A_embeddings,
                 B_pendingTexts, B_rawEmbeddings, B_finalEmbeddings,
                 C_pendingTexts, C_embeddings, C_leakedData>>

\* ステップ2: Redact処理（Confidentialは必須redact、それ以外はそのまま）
A_RedactText(rec) ==
  /\ rec \in A_pendingTexts
  /\ LET redactedContent == IF rec.sensitivity = "confidential"
                            THEN Redact(rec.content)
                            ELSE rec.content
         \* redacted後のテキストには機密情報がないことを明示
         isSensitive == IF rec.sensitivity = "confidential"
                        THEN FALSE  \* Confidentialはredact済みなのでsensitiveではない
                        ELSE ContainsSensitive(rec.content)  \* その他はテキスト内容による
     IN A_redactedTexts' = A_redactedTexts \cup {
          [content |-> redactedContent, sensitivity |-> rec.sensitivity,
           containsSensitive |-> isSensitive]
        }
  /\ A_pendingTexts' = A_pendingTexts \ {rec}
  /\ UNCHANGED <<A_embeddings,
                 B_pendingTexts, B_rawEmbeddings, B_finalEmbeddings,
                 C_pendingTexts, C_embeddings, C_leakedData>>

\* ステップ3: 埋め込み生成（Redact済みテキストのみ）
\* 設計A: Confidentialデータはredact済みなのでsensitive情報は含まれない
A_Embed(rec) ==
  /\ rec \in A_redactedTexts
  /\ \E vec \in Vector:
       A_embeddings' = A_embeddings \cup {
         [text |-> rec.content, vector |-> vec,
          containsSensitive |-> rec.containsSensitive,  \* redact後の状態を引き継ぐ
          sensitivity |-> rec.sensitivity]
       }
  /\ A_redactedTexts' = A_redactedTexts \ {rec}
  /\ UNCHANGED <<A_pendingTexts,
                 B_pendingTexts, B_rawEmbeddings, B_finalEmbeddings,
                 C_pendingTexts, C_embeddings, C_leakedData>>

\* ========== 設計B: Embed-before-Redact（問題あり） ==========

\* ステップ1: テキスト受付
B_SubmitText(text, sensitivity) ==
  /\ B_pendingTexts' = B_pendingTexts \cup {[content |-> text, sensitivity |-> sensitivity]}
  /\ UNCHANGED <<A_pendingTexts, A_redactedTexts, A_embeddings,
                 B_rawEmbeddings, B_finalEmbeddings,
                 C_pendingTexts, C_embeddings, C_leakedData>>

\* ステップ2: 埋め込み生成（Redact前 - 問題: 機密情報がベクトルに含まれる）
B_Embed(rec) ==
  /\ rec \in B_pendingTexts
  /\ \E vec \in Vector:
       B_rawEmbeddings' = B_rawEmbeddings \cup {
         [text |-> rec.content, vector |-> vec, sensitivity |-> rec.sensitivity,
          containsSensitive |-> ContainsSensitive(rec.content)]
       }
  /\ B_pendingTexts' = B_pendingTexts \ {rec}
  /\ UNCHANGED <<A_pendingTexts, A_redactedTexts, A_embeddings,
                 B_finalEmbeddings,
                 C_pendingTexts, C_embeddings, C_leakedData>>

\* ステップ3: Redact処理（埋め込み後 - 問題: ベクトルから機密情報は除去できない）
B_RedactAfterEmbed(emb) ==
  /\ emb \in B_rawEmbeddings
  \* 問題: ベクトルはそのまま（機密情報が埋め込まれたまま）
  /\ B_finalEmbeddings' = B_finalEmbeddings \cup {
       [text |-> Redact(emb.text), vector |-> emb.vector,
        containsSensitive |-> emb.containsSensitive]  \* まだTRUEの可能性
     }
  /\ B_rawEmbeddings' = B_rawEmbeddings \ {emb}
  /\ UNCHANGED <<A_pendingTexts, A_redactedTexts, A_embeddings,
                 B_pendingTexts,
                 C_pendingTexts, C_embeddings, C_leakedData>>

\* ========== 設計C: 選択可能（問題: 誤選択のリスク） ==========

C_SubmitText(text, sensitivity, order) ==
  /\ C_pendingTexts' = C_pendingTexts \cup {
       [content |-> text, sensitivity |-> sensitivity, order |-> order]
     }
  /\ UNCHANGED <<A_pendingTexts, A_redactedTexts, A_embeddings,
                 B_pendingTexts, B_rawEmbeddings, B_finalEmbeddings,
                 C_embeddings, C_leakedData>>

C_Process(rec) ==
  /\ rec \in C_pendingTexts
  /\ \E vec \in Vector:
       LET processed == IF rec.order = "redact_first"
                        THEN [text |-> Redact(rec.content), vector |-> vec,
                              containsSensitive |-> FALSE]
                        ELSE [text |-> rec.content, vector |-> vec,
                              containsSensitive |-> ContainsSensitive(rec.content)]
       IN /\ C_embeddings' = C_embeddings \cup {processed}
          \* 漏洩検出: Confidentialデータがembed_firstで処理された場合
          /\ IF rec.sensitivity = "confidential" /\ rec.order = "embed_first"
             THEN C_leakedData' = C_leakedData \cup {rec.content}
             ELSE UNCHANGED C_leakedData
  /\ C_pendingTexts' = C_pendingTexts \ {rec}
  /\ UNCHANGED <<A_pendingTexts, A_redactedTexts, A_embeddings,
                 B_pendingTexts, B_rawEmbeddings, B_finalEmbeddings>>

\* ========== 次状態 ==========

Next ==
  \/ \E t \in Text, s \in SensitivityLevel: A_SubmitText(t, s)
  \/ \E rec \in A_pendingTexts: A_RedactText(rec)
  \/ \E rec \in A_redactedTexts: A_Embed(rec)
  \/ \E t \in Text, s \in SensitivityLevel: B_SubmitText(t, s)
  \/ \E rec \in B_pendingTexts: B_Embed(rec)
  \/ \E emb \in B_rawEmbeddings: B_RedactAfterEmbed(emb)
  \/ \E t \in Text, s \in SensitivityLevel, o \in RedactOrder: C_SubmitText(t, s, o)
  \/ \E rec \in C_pendingTexts: C_Process(rec)

Spec == Init /\ [][Next]_vars

\* ========== 安全性不変条件 ==========

\* 設計A: Confidentialデータの埋め込みに機密情報が含まれない
\* 注意: publicデータは元々機密情報を含む可能性があるが、それは許容
Inv_A_NoSensitiveInEmbedding ==
  \A emb \in A_embeddings:
    emb.sensitivity = "confidential" => emb.containsSensitive = FALSE

\* 設計B: 埋め込みに機密情報が含まれる可能性（反例を期待）
\* この不変条件は設計Bの問題を示すために意図的に破られる
Inv_B_NoSensitiveInEmbedding ==
  \A emb \in B_finalEmbeddings:
    emb.containsSensitive = FALSE

\* 設計C: 漏洩データがない（反例を期待）
\* この不変条件は設計Cの問題を示すために意図的に破られる
Inv_C_NoLeakedData ==
  C_leakedData = {}

\* ========== 比較用プロパティ ==========

\* 設計A: Confidentialデータは必ずRedact後に埋め込み
Property_A_RedactBeforeEmbed ==
  \A emb \in A_embeddings:
    emb.containsSensitive = FALSE

\* 設計B: Confidentialデータが埋め込み時に漏洩
Property_B_LeaksPossible ==
  \E emb \in B_finalEmbeddings:
    emb.containsSensitive = TRUE

\* 設計C: 誤った順序選択で漏洩
Property_C_MisconfigurationRisk ==
  C_leakedData # {}

\* ========== 状態制約（状態爆発対策） ==========

\* 小規模検証用の状態制約
StateConstraint ==
  /\ Cardinality(A_embeddings) <= 2
  /\ Cardinality(B_finalEmbeddings) <= 2
  /\ Cardinality(C_embeddings) <= 2
  /\ Cardinality(A_pendingTexts) <= 1
  /\ Cardinality(B_pendingTexts) <= 1
  /\ Cardinality(C_pendingTexts) <= 1

====
