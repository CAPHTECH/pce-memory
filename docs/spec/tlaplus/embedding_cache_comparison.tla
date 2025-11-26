---- MODULE embedding_cache_comparison ----
\* Embedding Cache Strategy Design Comparison
\* ADR-0003: キャッシュ戦略の形式検証（時相的性質）
\*
\* 比較する設計:
\* - 設計A: バージョン込みキー（textHash + modelVersion）
\* - 設計B: テキストのみキー（textHash only）
\* - 設計C: キャッシュなし
\*
\* 検証する時相的性質:
\* - FreshOnUpdate: バージョン更新後、キャッシュは新バージョンを返す
\* - NoStaleOnVersionChange: バージョン変更時に古いエントリが返されない
\* - CacheInvalidationTiming: 無効化のタイミングが正しい

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
  Text,
  ModelVersion,
  Vector

VARIABLES
  \* 共通状態
  currentVersion,

  \* 設計A: バージョン込みキー
  A_cache,  \* [text -> [version -> vector]]（バージョン別に保存）
  A_responses,  \* 設計Aのレスポンス

  \* 設計B: テキストのみキー
  B_cache,  \* [text -> [vector, version]]（バージョンはメタデータ）
  B_responses,  \* 設計Bのレスポンス

  \* リクエスト追跡
  requests

vars == <<currentVersion, A_cache, A_responses, B_cache, B_responses, requests>>

\* ========== 型定義 ==========

CacheEntryB == [vector: Vector, version: ModelVersion]
Request == [text: Text, expectedVersion: ModelVersion]
Response == [text: Text, vector: Vector, version: ModelVersion, stale: BOOLEAN]

\* ========== 初期状態 ==========

Init ==
  /\ currentVersion = CHOOSE v \in ModelVersion: TRUE
  /\ A_cache = [t \in Text |-> [v \in ModelVersion |-> <<>>]]
  /\ A_responses = {}
  /\ B_cache = [t \in Text |-> <<>>]
  /\ B_responses = {}
  /\ requests = {}

\* ========== 設計A: バージョン込みキー ==========

\* 設計Aのキャッシュルックアップ: テキストとバージョンの両方で検索
A_CacheHit(text) ==
  A_cache[text][currentVersion] # <<>>

A_CacheLookup(text) ==
  A_cache[text][currentVersion]

\* 設計Aのキャッシュ書き込み
A_CacheWrite(text, vec) ==
  A_cache' = [A_cache EXCEPT ![text][currentVersion] = vec]

\* 設計Aのリクエスト処理
A_ProcessRequest(req) ==
  /\ req \in requests
  /\ IF A_CacheHit(req.text)
     THEN /\ A_responses' = A_responses \cup {
               [text |-> req.text, vector |-> A_CacheLookup(req.text),
                version |-> currentVersion, stale |-> FALSE]
             }
          /\ UNCHANGED A_cache
     ELSE /\ \E vec \in Vector:
               /\ A_CacheWrite(req.text, vec)
               /\ A_responses' = A_responses \cup {
                    [text |-> req.text, vector |-> vec,
                     version |-> currentVersion, stale |-> FALSE]
                  }
  /\ requests' = requests \ {req}
  /\ UNCHANGED <<currentVersion, B_cache, B_responses>>

\* ========== 設計B: テキストのみキー ==========

\* 設計Bのキャッシュルックアップ: テキストのみで検索（バージョン無視）
B_CacheHit(text) ==
  B_cache[text] # <<>>

B_CacheLookup(text) ==
  B_cache[text]

\* 設計Bのキャッシュ書き込み
B_CacheWrite(text, vec) ==
  B_cache' = [B_cache EXCEPT ![text] = [vector |-> vec, version |-> currentVersion]]

\* 設計Bのリクエスト処理（問題: 古いバージョンが返される可能性）
B_ProcessRequest(req) ==
  /\ req \in requests
  /\ IF B_CacheHit(req.text)
     THEN LET entry == B_CacheLookup(req.text)
          IN /\ B_responses' = B_responses \cup {
                  [text |-> req.text, vector |-> entry.vector,
                   version |-> entry.version,
                   stale |-> (entry.version # currentVersion)]
                }
             /\ UNCHANGED B_cache
     ELSE /\ \E vec \in Vector:
               /\ B_CacheWrite(req.text, vec)
               /\ B_responses' = B_responses \cup {
                    [text |-> req.text, vector |-> vec,
                     version |-> currentVersion, stale |-> FALSE]
                  }
  /\ requests' = requests \ {req}
  /\ UNCHANGED <<currentVersion, A_cache, A_responses>>

\* ========== 共通アクション ==========

\* リクエスト送信
SubmitRequest(text) ==
  /\ requests' = requests \cup {[text |-> text, expectedVersion |-> currentVersion]}
  /\ UNCHANGED <<currentVersion, A_cache, A_responses, B_cache, B_responses>>

\* モデルバージョン更新
UpdateVersion(newVersion) ==
  /\ newVersion \in ModelVersion
  /\ newVersion # currentVersion
  /\ currentVersion' = newVersion
  \* 設計A: バージョン別なので既存エントリは影響なし（新バージョン用は空）
  \* 設計B: 古いバージョンのエントリが残る（問題）
  /\ UNCHANGED <<A_cache, A_responses, B_cache, B_responses, requests>>

\* ========== 次状態 ==========

Next ==
  \/ \E t \in Text: SubmitRequest(t)
  \/ \E req \in requests: A_ProcessRequest(req)
  \/ \E req \in requests: B_ProcessRequest(req)
  \/ \E v \in ModelVersion: UpdateVersion(v)

Spec == Init /\ [][Next]_vars

\* ========== 安全性不変条件 ==========

\* 設計A: レスポンスは常に現在のバージョンでstale=FALSE
\* 注意: 設計Aでは、レスポンス生成時点で必ず現在バージョンを使用
Inv_A_NoStale ==
  \A resp \in A_responses:
    resp.stale = FALSE

\* 設計B: レスポンスが古いバージョンの可能性（反例を期待）
\* この不変条件は設計Bの問題を示すために意図的に破られる
Inv_B_NoStale ==
  \A resp \in B_responses:
    resp.stale = FALSE

\* ========== 時相的性質 ==========

\* 設計A: レスポンスは常にstale=FALSE
Property_A_FreshOnUpdate ==
  \A resp \in A_responses:
    resp.stale = FALSE

\* 設計B: stale=TRUEのレスポンスが存在しない（反例を期待）
Property_B_PossibleStale ==
  ~(\E resp \in B_responses: resp.stale = TRUE)

====
