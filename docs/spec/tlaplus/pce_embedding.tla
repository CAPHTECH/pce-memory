---- MODULE pce_embedding ----
\* PCE Memory Embedding System - TLA+ Specification
\* ADR-0003: Embedding設計の形式検証
\*
\* 検証対象（時相的不変条件）:
\* - NoRequestLoss: プロバイダー障害時もリクエストは失われない
\* - EventualBatchCompletion: バッチ内の全アイテムは最終的に処理される
\* - CacheInvalidationFlow: モデルバージョン変更時のキャッシュ無効化
\* - ProviderFailover: プライマリ障害時のフォールバック

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
  Text,           \* テキストの集合
  ModelVersion,   \* モデルバージョンの集合
  Vector,         \* ベクトルの集合
  RequestId,      \* リクエストIDの集合
  MaxBatchSize,   \* バッチサイズ上限
  MaxRequests     \* 最大リクエスト数

VARIABLES
  \* Provider状態
  primaryProvider,     \* [status, modelVersion]
  fallbackProvider,    \* [status, modelVersion]

  \* キャッシュ状態
  cache,               \* [text -> [vector, modelVersion]]
  currentModelVersion, \* 現在のモデルバージョン

  \* リクエスト状態
  pendingRequests,     \* 保留中リクエスト {[text, requestId]}
  processingRequests,  \* 処理中リクエスト {[text, requestId, provider]}
  completedRequests,   \* 完了リクエスト {[text, requestId, vector]}
  failedRequests,      \* 失敗リクエスト {[text, requestId, error]}

  \* バッチ状態
  batchQueue,          \* バッチキュー Seq([text, requestId])
  currentBatch,        \* 現在処理中のバッチ

  \* メトリクス
  requestCounter

vars == <<primaryProvider, fallbackProvider, cache, currentModelVersion,
          pendingRequests, processingRequests, completedRequests, failedRequests,
          batchQueue, currentBatch, requestCounter>>

\* ========== 型定義 ==========

ProviderStatus == {"available", "unavailable", "degraded"}
ProviderRec == [status: ProviderStatus, modelVersion: ModelVersion]
CacheEntry == [vector: Vector, modelVersion: ModelVersion]
RequestRec == [text: Text, requestId: RequestId]
ProcessingRec == [text: Text, requestId: RequestId, provider: {"primary", "fallback"}]
CompletedRec == [text: Text, requestId: RequestId, vector: Vector]
ErrorType == {"PROVIDER_UNAVAILABLE", "TIMEOUT", "UNKNOWN"}
FailedRec == [text: Text, requestId: RequestId, error: ErrorType]

\* ========== 型不変条件 ==========

TypeInv ==
  /\ primaryProvider \in ProviderRec
  /\ fallbackProvider \in ProviderRec
  /\ cache \in [Text -> CacheEntry \cup {<<>>}]  \* 空エントリも許可
  /\ currentModelVersion \in ModelVersion
  /\ pendingRequests \in SUBSET RequestRec
  /\ processingRequests \in SUBSET ProcessingRec
  /\ completedRequests \in SUBSET CompletedRec
  /\ failedRequests \in SUBSET FailedRec
  /\ batchQueue \in Seq(RequestRec)
  /\ currentBatch \in SUBSET RequestRec
  /\ requestCounter \in 0..MaxRequests

\* ========== 初期状態 ==========

Init ==
  /\ primaryProvider = [status |-> "available", modelVersion |-> CHOOSE v \in ModelVersion : TRUE]
  /\ fallbackProvider = [status |-> "available", modelVersion |-> primaryProvider.modelVersion]
  /\ cache = [t \in Text |-> <<>>]
  /\ currentModelVersion = primaryProvider.modelVersion
  /\ pendingRequests = {}
  /\ processingRequests = {}
  /\ completedRequests = {}
  /\ failedRequests = {}
  /\ batchQueue = << >>
  /\ currentBatch = {}
  /\ requestCounter = 0

\* ========== ヘルパー関数 ==========

\* キャッシュヒット判定
CacheHit(text) ==
  /\ cache[text] # <<>>
  /\ cache[text].modelVersion = currentModelVersion

\* 利用可能なプロバイダーを取得
AvailableProvider ==
  IF primaryProvider.status = "available" THEN "primary"
  ELSE IF fallbackProvider.status = "available" THEN "fallback"
  ELSE "none"

\* リクエストIDが既に使用されているか
RequestIdUsed(rid) ==
  \/ \E r \in pendingRequests: r.requestId = rid
  \/ \E r \in processingRequests: r.requestId = rid
  \/ \E r \in completedRequests: r.requestId = rid
  \/ \E r \in failedRequests: r.requestId = rid
  \/ \E i \in 1..Len(batchQueue): batchQueue[i].requestId = rid
  \/ \E r \in currentBatch: r.requestId = rid

\* ========== アクション ==========

\* 単一リクエストの発行
SubmitRequest(text, rid) ==
  /\ requestCounter < MaxRequests
  /\ ~RequestIdUsed(rid)
  /\ pendingRequests' = pendingRequests \cup {[text |-> text, requestId |-> rid]}
  /\ requestCounter' = requestCounter + 1
  /\ UNCHANGED <<primaryProvider, fallbackProvider, cache, currentModelVersion,
                 processingRequests, completedRequests, failedRequests,
                 batchQueue, currentBatch>>

\* キャッシュヒット時の即時応答
ProcessCacheHit(req) ==
  /\ req \in pendingRequests
  /\ CacheHit(req.text)
  /\ completedRequests' = completedRequests \cup {
       [text |-> req.text, requestId |-> req.requestId, vector |-> cache[req.text].vector]
     }
  /\ pendingRequests' = pendingRequests \ {req}
  /\ UNCHANGED <<primaryProvider, fallbackProvider, cache, currentModelVersion,
                 processingRequests, failedRequests, batchQueue, currentBatch, requestCounter>>

\* キャッシュミス時のプロバイダー呼び出し開始
StartProcessing(req) ==
  /\ req \in pendingRequests
  /\ ~CacheHit(req.text)
  /\ AvailableProvider # "none"
  /\ processingRequests' = processingRequests \cup {
       [text |-> req.text, requestId |-> req.requestId, provider |-> AvailableProvider]
     }
  /\ pendingRequests' = pendingRequests \ {req}
  /\ UNCHANGED <<primaryProvider, fallbackProvider, cache, currentModelVersion,
                 completedRequests, failedRequests, batchQueue, currentBatch, requestCounter>>

\* プロバイダー処理完了（成功）
CompleteProcessing(proc, vec) ==
  /\ proc \in processingRequests
  /\ vec \in Vector
  /\ LET providerRec == IF proc.provider = "primary" THEN primaryProvider ELSE fallbackProvider
     IN providerRec.status = "available"
  /\ completedRequests' = completedRequests \cup {
       [text |-> proc.text, requestId |-> proc.requestId, vector |-> vec]
     }
  /\ cache' = [cache EXCEPT ![proc.text] = [vector |-> vec, modelVersion |-> currentModelVersion]]
  /\ processingRequests' = processingRequests \ {proc}
  /\ UNCHANGED <<primaryProvider, fallbackProvider, currentModelVersion,
                 pendingRequests, failedRequests, batchQueue, currentBatch, requestCounter>>

\* プロバイダー処理失敗
FailProcessing(proc) ==
  /\ proc \in processingRequests
  /\ LET providerRec == IF proc.provider = "primary" THEN primaryProvider ELSE fallbackProvider
     IN providerRec.status = "unavailable"
  /\ failedRequests' = failedRequests \cup {
       [text |-> proc.text, requestId |-> proc.requestId, error |-> "PROVIDER_UNAVAILABLE"]
     }
  /\ processingRequests' = processingRequests \ {proc}
  /\ UNCHANGED <<primaryProvider, fallbackProvider, cache, currentModelVersion,
                 pendingRequests, completedRequests, batchQueue, currentBatch, requestCounter>>

\* プロバイダーフェイルオーバー（処理中リクエストの再試行）
FailoverRetry(proc) ==
  /\ proc \in processingRequests
  /\ proc.provider = "primary"
  /\ primaryProvider.status = "unavailable"
  /\ fallbackProvider.status = "available"
  /\ processingRequests' = (processingRequests \ {proc}) \cup {
       [text |-> proc.text, requestId |-> proc.requestId, provider |-> "fallback"]
     }
  /\ UNCHANGED <<primaryProvider, fallbackProvider, cache, currentModelVersion,
                 pendingRequests, completedRequests, failedRequests,
                 batchQueue, currentBatch, requestCounter>>

\* プライマリプロバイダー障害
PrimaryFail ==
  /\ primaryProvider.status = "available"
  /\ primaryProvider' = [primaryProvider EXCEPT !.status = "unavailable"]
  /\ UNCHANGED <<fallbackProvider, cache, currentModelVersion,
                 pendingRequests, processingRequests, completedRequests, failedRequests,
                 batchQueue, currentBatch, requestCounter>>

\* プライマリプロバイダー復旧
PrimaryRecover ==
  /\ primaryProvider.status = "unavailable"
  /\ primaryProvider' = [primaryProvider EXCEPT !.status = "available"]
  /\ UNCHANGED <<fallbackProvider, cache, currentModelVersion,
                 pendingRequests, processingRequests, completedRequests, failedRequests,
                 batchQueue, currentBatch, requestCounter>>

\* モデルバージョン更新（キャッシュ無効化）
UpdateModelVersion(newVersion) ==
  /\ newVersion \in ModelVersion
  /\ newVersion # currentModelVersion
  /\ currentModelVersion' = newVersion
  /\ primaryProvider' = [primaryProvider EXCEPT !.modelVersion = newVersion]
  /\ fallbackProvider' = [fallbackProvider EXCEPT !.modelVersion = newVersion]
  \* キャッシュ全無効化
  /\ cache' = [t \in Text |-> <<>>]
  /\ UNCHANGED <<pendingRequests, processingRequests, completedRequests, failedRequests,
                 batchQueue, currentBatch, requestCounter>>

\* バッチリクエストの追加
AddToBatch(text, rid) ==
  /\ requestCounter < MaxRequests
  /\ ~RequestIdUsed(rid)
  /\ Len(batchQueue) < MaxBatchSize
  /\ batchQueue' = Append(batchQueue, [text |-> text, requestId |-> rid])
  /\ requestCounter' = requestCounter + 1
  /\ UNCHANGED <<primaryProvider, fallbackProvider, cache, currentModelVersion,
                 pendingRequests, processingRequests, completedRequests, failedRequests,
                 currentBatch>>

\* バッチ処理開始
StartBatchProcessing ==
  /\ Len(batchQueue) > 0
  /\ currentBatch = {}
  /\ AvailableProvider # "none"
  /\ currentBatch' = {batchQueue[i] : i \in 1..Len(batchQueue)}
  /\ batchQueue' = << >>
  /\ UNCHANGED <<primaryProvider, fallbackProvider, cache, currentModelVersion,
                 pendingRequests, processingRequests, completedRequests, failedRequests,
                 requestCounter>>

\* バッチアイテムの完了
CompleteBatchItem(item, vec) ==
  /\ item \in currentBatch
  /\ vec \in Vector
  /\ AvailableProvider # "none"
  /\ completedRequests' = completedRequests \cup {
       [text |-> item.text, requestId |-> item.requestId, vector |-> vec]
     }
  /\ cache' = [cache EXCEPT ![item.text] = [vector |-> vec, modelVersion |-> currentModelVersion]]
  /\ currentBatch' = currentBatch \ {item}
  /\ UNCHANGED <<primaryProvider, fallbackProvider, currentModelVersion,
                 pendingRequests, processingRequests, failedRequests,
                 batchQueue, requestCounter>>

\* ========== 次状態 ==========

Next ==
  \/ \E t \in Text, rid \in RequestId: SubmitRequest(t, rid)
  \/ \E req \in pendingRequests: ProcessCacheHit(req)
  \/ \E req \in pendingRequests: StartProcessing(req)
  \/ \E proc \in processingRequests, vec \in Vector: CompleteProcessing(proc, vec)
  \/ \E proc \in processingRequests: FailProcessing(proc)
  \/ \E proc \in processingRequests: FailoverRetry(proc)
  \/ PrimaryFail
  \/ PrimaryRecover
  \/ \E v \in ModelVersion: UpdateModelVersion(v)
  \/ \E t \in Text, rid \in RequestId: AddToBatch(t, rid)
  \/ StartBatchProcessing
  \/ \E item \in currentBatch, vec \in Vector: CompleteBatchItem(item, vec)

Spec == Init /\ [][Next]_vars

\* ========== 安全性不変条件 ==========

\* 安全性: キャッシュ内のエントリは現在のモデルバージョンのみ
Inv_CacheVersionConsistency ==
  \A t \in Text: cache[t] # <<>> => cache[t].modelVersion = currentModelVersion

\* 安全性: リクエストIDは一意
Inv_UniqueRequestId ==
  /\ \A r1, r2 \in completedRequests: r1 # r2 => r1.requestId # r2.requestId
  /\ \A r1, r2 \in failedRequests: r1 # r2 => r1.requestId # r2.requestId

\* 安全性: プロバイダーが両方unavailableの場合、新規処理は開始されない
Inv_NoProcessingWithoutProvider ==
  (primaryProvider.status = "unavailable" /\ fallbackProvider.status = "unavailable")
    => processingRequests = {}

\* ========== ライブネス条件 ==========

\* ライブネス: 全ての保留中リクエストは最終的に完了または失敗する
Liveness_EventualResponse ==
  \A req \in pendingRequests:
    <>((\E c \in completedRequests: c.requestId = req.requestId) \/
       (\E f \in failedRequests: f.requestId = req.requestId))

\* ライブネス: 全てのバッチアイテムは最終的に処理される
Liveness_BatchCompletion ==
  <>[] (currentBatch = {})

\* フェアネス: プロバイダーは最終的に復旧する
Fairness_ProviderRecovery ==
  WF_vars(PrimaryRecover)

\* ========== 複合仕様 ==========

FairSpec == Spec /\ Fairness_ProviderRecovery

====
