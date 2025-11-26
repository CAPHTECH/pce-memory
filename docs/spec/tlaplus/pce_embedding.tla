---- MODULE pce_embedding ----
\* PCE Memory Embedding System - TLA+ Specification
\* ADR-0003: Embedding設計の形式検証
\*
\* 検証対象（時相的不変条件）:
\* - NoRequestLoss: プロバイダー障害時もリクエストは失われない
\* - EventualBatchCompletion: バッチ内の全アイテムは最終的に処理される
\* - CacheInvalidationFlow: モデルバージョン変更時のキャッシュ無効化
\* - ProviderFailover: プライマリ障害時のフォールバック
\*
\* 修正履歴:
\* - v2: ProcessingRecにmodelVersionを追加（処理開始時のバージョン追跡）
\* - v2: Inv_UniqueRequestIdを全コンテナに拡張
\* - v2: CompleteProcessingでバージョン不一致時の処理を追加
\* - v2: 新しいエラータイプSTALE_MODEL_VERSIONを追加

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
  processingRequests,  \* 処理中リクエスト {[text, requestId, provider, modelVersion]}
  completedRequests,   \* 完了リクエスト {[text, requestId, vector, modelVersion]}
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

\* v2: ProcessingRecにmodelVersionを追加（処理開始時点のバージョンを記録）
ProcessingRec == [text: Text, requestId: RequestId, provider: {"primary", "fallback"}, modelVersion: ModelVersion]

\* v2: CompletedRecにmodelVersionを追加（どのバージョンで処理されたか記録）
CompletedRec == [text: Text, requestId: RequestId, vector: Vector, modelVersion: ModelVersion]

\* v2: STALE_MODEL_VERSIONエラーを追加
ErrorType == {"PROVIDER_UNAVAILABLE", "TIMEOUT", "UNKNOWN", "STALE_MODEL_VERSION"}
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

\* v2: リクエストIDが既に使用されているか（全コンテナをチェック）
RequestIdUsed(rid) ==
  \/ \E r \in pendingRequests: r.requestId = rid
  \/ \E r \in processingRequests: r.requestId = rid
  \/ \E r \in completedRequests: r.requestId = rid
  \/ \E r \in failedRequests: r.requestId = rid
  \/ \E i \in 1..Len(batchQueue): batchQueue[i].requestId = rid
  \/ \E r \in currentBatch: r.requestId = rid

\* v2: 全コンテナからリクエストIDの集合を取得
AllRequestIds ==
  {r.requestId : r \in pendingRequests} \cup
  {r.requestId : r \in processingRequests} \cup
  {r.requestId : r \in completedRequests} \cup
  {r.requestId : r \in failedRequests} \cup
  {batchQueue[i].requestId : i \in 1..Len(batchQueue)} \cup
  {r.requestId : r \in currentBatch}

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
       [text |-> req.text, requestId |-> req.requestId,
        vector |-> cache[req.text].vector, modelVersion |-> cache[req.text].modelVersion]
     }
  /\ pendingRequests' = pendingRequests \ {req}
  /\ UNCHANGED <<primaryProvider, fallbackProvider, cache, currentModelVersion,
                 processingRequests, failedRequests, batchQueue, currentBatch, requestCounter>>

\* v2: キャッシュミス時のプロバイダー呼び出し開始（modelVersionを記録）
StartProcessing(req) ==
  /\ req \in pendingRequests
  /\ ~CacheHit(req.text)
  /\ AvailableProvider # "none"
  /\ processingRequests' = processingRequests \cup {
       [text |-> req.text, requestId |-> req.requestId,
        provider |-> AvailableProvider, modelVersion |-> currentModelVersion]
     }
  /\ pendingRequests' = pendingRequests \ {req}
  /\ UNCHANGED <<primaryProvider, fallbackProvider, cache, currentModelVersion,
                 completedRequests, failedRequests, batchQueue, currentBatch, requestCounter>>

\* v2: プロバイダー処理完了（バージョンチェック付き）
CompleteProcessing(proc, vec) ==
  /\ proc \in processingRequests
  /\ vec \in Vector
  /\ LET providerRec == IF proc.provider = "primary" THEN primaryProvider ELSE fallbackProvider
     IN providerRec.status = "available"
  \* v2: バージョンが一致する場合のみ成功
  /\ proc.modelVersion = currentModelVersion
  /\ completedRequests' = completedRequests \cup {
       [text |-> proc.text, requestId |-> proc.requestId,
        vector |-> vec, modelVersion |-> proc.modelVersion]
     }
  /\ cache' = [cache EXCEPT ![proc.text] = [vector |-> vec, modelVersion |-> proc.modelVersion]]
  /\ processingRequests' = processingRequests \ {proc}
  /\ UNCHANGED <<primaryProvider, fallbackProvider, currentModelVersion,
                 pendingRequests, failedRequests, batchQueue, currentBatch, requestCounter>>

\* v2: バージョン不一致時の処理失敗（古いモデルで処理された結果は破棄）
CompleteProcessingStale(proc) ==
  /\ proc \in processingRequests
  /\ LET providerRec == IF proc.provider = "primary" THEN primaryProvider ELSE fallbackProvider
     IN providerRec.status = "available"
  \* バージョンが不一致
  /\ proc.modelVersion # currentModelVersion
  \* 失敗として記録（古いバージョンの結果は使用しない）
  /\ failedRequests' = failedRequests \cup {
       [text |-> proc.text, requestId |-> proc.requestId, error |-> "STALE_MODEL_VERSION"]
     }
  /\ processingRequests' = processingRequests \ {proc}
  /\ UNCHANGED <<primaryProvider, fallbackProvider, cache, currentModelVersion,
                 pendingRequests, completedRequests, batchQueue, currentBatch, requestCounter>>

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

\* v2: プロバイダーフェイルオーバー（modelVersionを保持）
FailoverRetry(proc) ==
  /\ proc \in processingRequests
  /\ proc.provider = "primary"
  /\ primaryProvider.status = "unavailable"
  /\ fallbackProvider.status = "available"
  /\ processingRequests' = (processingRequests \ {proc}) \cup {
       [text |-> proc.text, requestId |-> proc.requestId,
        provider |-> "fallback", modelVersion |-> proc.modelVersion]
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

\* v2: バッチアイテムの完了（現在のバージョンを使用）
CompleteBatchItem(item, vec) ==
  /\ item \in currentBatch
  /\ vec \in Vector
  /\ AvailableProvider # "none"
  /\ completedRequests' = completedRequests \cup {
       [text |-> item.text, requestId |-> item.requestId,
        vector |-> vec, modelVersion |-> currentModelVersion]
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
  \/ \E proc \in processingRequests: CompleteProcessingStale(proc)  \* v2: 追加
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

\* v2: キャッシュ内のエントリは現在のモデルバージョンのみ
\* 注意: CompleteProcessingがproc.modelVersionを使用するため、
\*       バージョン不一致時はキャッシュに書き込まれない
Inv_CacheVersionConsistency ==
  \A t \in Text: cache[t] # <<>> => cache[t].modelVersion = currentModelVersion

\* v2: リクエストIDは全コンテナで一意（相互排他）
Inv_UniqueRequestId ==
  \* 各コンテナ内での一意性
  /\ \A r1, r2 \in pendingRequests: r1 # r2 => r1.requestId # r2.requestId
  /\ \A r1, r2 \in processingRequests: r1 # r2 => r1.requestId # r2.requestId
  /\ \A r1, r2 \in completedRequests: r1 # r2 => r1.requestId # r2.requestId
  /\ \A r1, r2 \in failedRequests: r1 # r2 => r1.requestId # r2.requestId
  /\ \A r1, r2 \in currentBatch: r1 # r2 => r1.requestId # r2.requestId
  \* コンテナ間での相互排他
  /\ \A r1 \in pendingRequests, r2 \in processingRequests: r1.requestId # r2.requestId
  /\ \A r1 \in pendingRequests, r2 \in completedRequests: r1.requestId # r2.requestId
  /\ \A r1 \in pendingRequests, r2 \in failedRequests: r1.requestId # r2.requestId
  /\ \A r1 \in processingRequests, r2 \in completedRequests: r1.requestId # r2.requestId
  /\ \A r1 \in processingRequests, r2 \in failedRequests: r1.requestId # r2.requestId
  /\ \A r1 \in completedRequests, r2 \in failedRequests: r1.requestId # r2.requestId
  \* batchQueueとcurrentBatchも含める
  /\ \A i \in 1..Len(batchQueue), r \in pendingRequests: batchQueue[i].requestId # r.requestId
  /\ \A i \in 1..Len(batchQueue), r \in processingRequests: batchQueue[i].requestId # r.requestId
  /\ \A i \in 1..Len(batchQueue), r \in completedRequests: batchQueue[i].requestId # r.requestId
  /\ \A i \in 1..Len(batchQueue), r \in failedRequests: batchQueue[i].requestId # r.requestId
  /\ \A r1 \in currentBatch, r2 \in pendingRequests: r1.requestId # r2.requestId
  /\ \A r1 \in currentBatch, r2 \in processingRequests: r1.requestId # r2.requestId
  /\ \A r1 \in currentBatch, r2 \in completedRequests: r1.requestId # r2.requestId
  /\ \A r1 \in currentBatch, r2 \in failedRequests: r1.requestId # r2.requestId
  /\ \A i \in 1..Len(batchQueue), r \in currentBatch: batchQueue[i].requestId # r.requestId

\* 安全性: プロバイダーが両方unavailableの場合、新規処理は開始されない
Inv_NoProcessingWithoutProvider ==
  (primaryProvider.status = "unavailable" /\ fallbackProvider.status = "unavailable")
    => processingRequests = {}

\* v2: 完了したリクエストが現在のバージョンならキャッシュと一致
\* 注意: 古いバージョンで完了したリクエストは、バージョン更新後にキャッシュと不一致になりうる（正常動作）
Inv_CompletedVersionConsistency ==
  \A c \in completedRequests:
    (c.modelVersion = currentModelVersion /\ cache[c.text] # <<>>) =>
      cache[c.text].modelVersion = c.modelVersion

\* v2: 処理中リクエストが古いバージョンで開始されていた場合の検出
Inv_ProcessingVersionTracking ==
  \A proc \in processingRequests:
    proc.modelVersion \in ModelVersion

\* ========== ライブネス条件 ==========

\* ライブネス: 全ての保留中リクエストは最終的に完了または失敗する
Liveness_EventualResponse ==
  \A req \in pendingRequests:
    <>((\E c \in completedRequests: c.requestId = req.requestId) \/
       (\E f \in failedRequests: f.requestId = req.requestId))

\* ライブネス: 全てのバッチアイテムは最終的に処理される
Liveness_BatchCompletion ==
  <>[] (currentBatch = {})

\* ライブネス: 処理中リクエストは最終的に完了または失敗する
Liveness_ProcessingCompletion ==
  \A proc \in processingRequests:
    <>((\E c \in completedRequests: c.requestId = proc.requestId) \/
       (\E f \in failedRequests: f.requestId = proc.requestId))

\* フェアネス: プロバイダーは最終的に復旧する
Fairness_ProviderRecovery ==
  WF_vars(PrimaryRecover)

\* ========== 複合仕様 ==========

FairSpec == Spec /\ Fairness_ProviderRecovery

====
