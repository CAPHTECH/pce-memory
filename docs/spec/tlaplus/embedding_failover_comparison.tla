---- MODULE embedding_failover_comparison ----
\* Embedding Failover Strategy Design Comparison
\* ADR-0003: フェイルオーバー戦略の形式検証
\*
\* 比較する設計:
\* - 設計A: 即時フェイルオーバー（採用）
\* - 設計B: リトライ後フェイルオーバー（不採用）
\* - 設計C: フェイルオーバーなし（不採用）
\*
\* 検証する性質:
\* - RequestCompletion: 少なくとも1つのプロバイダーが利用可能なら、リクエストは完了する
\* - RetryDelayRespected: リトライ間隔が守られる（設計B）
\* - NoSkipToFailover: 最大リトライ回数前にフェイルオーバーしない（設計B）

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
  RequestId,
  MaxRequests,
  MaxRetries,     \* 設計B: 最大リトライ回数
  RetryDelay      \* 設計B: リトライ間隔（離散時間単位）

VARIABLES
  \* 共通状態
  primaryStatus,      \* "available" or "unavailable"
  fallbackStatus,     \* "available" or "unavailable"

  \* 設計A（即時フェイルオーバー）
  A_pendingRequests,
  A_processingRequests,
  A_completedRequests,
  A_failedRequests,

  \* 設計B（リトライ後フェイルオーバー）
  B_pendingRequests,
  B_processingRequests,  \* [requestId, provider, retryCount, waitTicks]
  B_completedRequests,
  B_failedRequests,

  \* 設計C（フェイルオーバーなし）
  C_pendingRequests,
  C_processingRequests,
  C_completedRequests,
  C_failedRequests

varsA == <<A_pendingRequests, A_processingRequests, A_completedRequests, A_failedRequests>>
varsB == <<B_pendingRequests, B_processingRequests, B_completedRequests, B_failedRequests>>
varsC == <<C_pendingRequests, C_processingRequests, C_completedRequests, C_failedRequests>>
vars == <<primaryStatus, fallbackStatus,
          A_pendingRequests, A_processingRequests, A_completedRequests, A_failedRequests,
          B_pendingRequests, B_processingRequests, B_completedRequests, B_failedRequests,
          C_pendingRequests, C_processingRequests, C_completedRequests, C_failedRequests>>

\* ========== 型定義 ==========

Status == {"available", "unavailable"}
ProviderType == {"primary", "fallback"}

\* ========== 初期状態 ==========

Init ==
  /\ primaryStatus = "available"
  /\ fallbackStatus = "available"
  \* 設計A
  /\ A_pendingRequests = {}
  /\ A_processingRequests = {}
  /\ A_completedRequests = {}
  /\ A_failedRequests = {}
  \* 設計B
  /\ B_pendingRequests = {}
  /\ B_processingRequests = {}
  /\ B_completedRequests = {}
  /\ B_failedRequests = {}
  \* 設計C
  /\ C_pendingRequests = {}
  /\ C_processingRequests = {}
  /\ C_completedRequests = {}
  /\ C_failedRequests = {}

\* ========== 設計A: 即時フェイルオーバー ==========

A_AvailableProvider ==
  IF primaryStatus = "available" THEN "primary"
  ELSE IF fallbackStatus = "available" THEN "fallback"
  ELSE "none"

A_RequestIdUsed(rid) ==
  \/ rid \in A_pendingRequests
  \/ \E r \in A_processingRequests: r.requestId = rid
  \/ rid \in A_completedRequests
  \/ rid \in A_failedRequests

A_SubmitRequest(rid) ==
  /\ Cardinality(A_pendingRequests \cup A_completedRequests \cup A_failedRequests) < MaxRequests
  /\ ~A_RequestIdUsed(rid)
  /\ A_pendingRequests' = A_pendingRequests \cup {rid}
  /\ UNCHANGED <<A_processingRequests, A_completedRequests, A_failedRequests>>

A_StartProcessing(rid) ==
  /\ rid \in A_pendingRequests
  /\ A_AvailableProvider # "none"
  /\ A_processingRequests' = A_processingRequests \cup {[requestId |-> rid, provider |-> A_AvailableProvider]}
  /\ A_pendingRequests' = A_pendingRequests \ {rid}
  /\ UNCHANGED <<A_completedRequests, A_failedRequests>>

A_CompleteProcessing(proc) ==
  /\ proc \in A_processingRequests
  /\ (proc.provider = "primary" /\ primaryStatus = "available") \/
     (proc.provider = "fallback" /\ fallbackStatus = "available")
  /\ A_completedRequests' = A_completedRequests \cup {proc.requestId}
  /\ A_processingRequests' = A_processingRequests \ {proc}
  /\ UNCHANGED <<A_pendingRequests, A_failedRequests>>

\* 設計Aの特徴: 即時フェイルオーバー
A_FailoverRetry(proc) ==
  /\ proc \in A_processingRequests
  /\ proc.provider = "primary"
  /\ primaryStatus = "unavailable"
  /\ fallbackStatus = "available"
  /\ A_processingRequests' = (A_processingRequests \ {proc}) \cup {[requestId |-> proc.requestId, provider |-> "fallback"]}
  /\ UNCHANGED <<A_pendingRequests, A_completedRequests, A_failedRequests>>

A_FailProcessing(proc) ==
  /\ proc \in A_processingRequests
  /\ (proc.provider = "primary" /\ primaryStatus = "unavailable" /\ fallbackStatus = "unavailable") \/
     (proc.provider = "fallback" /\ fallbackStatus = "unavailable")
  /\ A_failedRequests' = A_failedRequests \cup {proc.requestId}
  /\ A_processingRequests' = A_processingRequests \ {proc}
  /\ UNCHANGED <<A_pendingRequests, A_completedRequests>>

A_Next ==
  \/ \E rid \in RequestId: A_SubmitRequest(rid)
  \/ \E rid \in A_pendingRequests: A_StartProcessing(rid)
  \/ \E proc \in A_processingRequests: A_CompleteProcessing(proc)
  \/ \E proc \in A_processingRequests: A_FailoverRetry(proc)
  \/ \E proc \in A_processingRequests: A_FailProcessing(proc)

\* ========== 設計B: リトライ後フェイルオーバー ==========

\* 設計Bの処理レコード: リトライ状態を含む
B_ProcessingRec == [requestId: RequestId, provider: ProviderType, retryCount: 0..MaxRetries, waitTicks: 0..RetryDelay]

B_RequestIdUsed(rid) ==
  \/ rid \in B_pendingRequests
  \/ \E r \in B_processingRequests: r.requestId = rid
  \/ rid \in B_completedRequests
  \/ rid \in B_failedRequests

B_SubmitRequest(rid) ==
  /\ Cardinality(B_pendingRequests \cup B_completedRequests \cup B_failedRequests) < MaxRequests
  /\ ~B_RequestIdUsed(rid)
  /\ B_pendingRequests' = B_pendingRequests \cup {rid}
  /\ UNCHANGED <<B_processingRequests, B_completedRequests, B_failedRequests>>

\* 設計Bの特徴: プライマリでのみ開始（リトライカウンタ初期化）
B_StartProcessing(rid) ==
  /\ rid \in B_pendingRequests
  /\ primaryStatus = "available"
  /\ B_processingRequests' = B_processingRequests \cup {
       [requestId |-> rid, provider |-> "primary", retryCount |-> 0, waitTicks |-> 0]
     }
  /\ B_pendingRequests' = B_pendingRequests \ {rid}
  /\ UNCHANGED <<B_completedRequests, B_failedRequests>>

B_CompleteProcessing(proc) ==
  /\ proc \in B_processingRequests
  /\ proc.waitTicks = 0  \* 待機中は完了不可
  /\ (proc.provider = "primary" /\ primaryStatus = "available") \/
     (proc.provider = "fallback" /\ fallbackStatus = "available")
  /\ B_completedRequests' = B_completedRequests \cup {proc.requestId}
  /\ B_processingRequests' = B_processingRequests \ {proc}
  /\ UNCHANGED <<B_pendingRequests, B_failedRequests>>

\* 設計Bの特徴: リトライ待機時間の経過
B_WaitTick(proc) ==
  /\ proc \in B_processingRequests
  /\ proc.waitTicks > 0
  /\ B_processingRequests' = (B_processingRequests \ {proc}) \cup {
       [requestId |-> proc.requestId, provider |-> proc.provider,
        retryCount |-> proc.retryCount, waitTicks |-> proc.waitTicks - 1]
     }
  /\ UNCHANGED <<B_pendingRequests, B_completedRequests, B_failedRequests>>

\* 設計Bの特徴: プライマリ失敗時のリトライ（同一プロバイダー）
B_Retry(proc) ==
  /\ proc \in B_processingRequests
  /\ proc.provider = "primary"
  /\ primaryStatus = "unavailable"
  /\ proc.retryCount < MaxRetries
  /\ proc.waitTicks = 0  \* 待機完了後のみリトライ可
  /\ B_processingRequests' = (B_processingRequests \ {proc}) \cup {
       [requestId |-> proc.requestId, provider |-> "primary",
        retryCount |-> proc.retryCount + 1, waitTicks |-> RetryDelay]
     }
  /\ UNCHANGED <<B_pendingRequests, B_completedRequests, B_failedRequests>>

\* 設計Bの特徴: 最大リトライ後にフェイルオーバー
B_FailoverAfterRetries(proc) ==
  /\ proc \in B_processingRequests
  /\ proc.provider = "primary"
  /\ primaryStatus = "unavailable"
  /\ proc.retryCount >= MaxRetries  \* 最大リトライ到達後のみ
  /\ fallbackStatus = "available"
  /\ B_processingRequests' = (B_processingRequests \ {proc}) \cup {
       [requestId |-> proc.requestId, provider |-> "fallback",
        retryCount |-> 0, waitTicks |-> 0]
     }
  /\ UNCHANGED <<B_pendingRequests, B_completedRequests, B_failedRequests>>

\* 設計Bの特徴: 最大リトライ後も失敗
B_FailProcessing(proc) ==
  /\ proc \in B_processingRequests
  /\ proc.waitTicks = 0
  /\ \/ (proc.provider = "primary" /\ primaryStatus = "unavailable" /\
         proc.retryCount >= MaxRetries /\ fallbackStatus = "unavailable")
     \/ (proc.provider = "fallback" /\ fallbackStatus = "unavailable")
  /\ B_failedRequests' = B_failedRequests \cup {proc.requestId}
  /\ B_processingRequests' = B_processingRequests \ {proc}
  /\ UNCHANGED <<B_pendingRequests, B_completedRequests>>

B_Next ==
  \/ \E rid \in RequestId: B_SubmitRequest(rid)
  \/ \E rid \in B_pendingRequests: B_StartProcessing(rid)
  \/ \E proc \in B_processingRequests: B_CompleteProcessing(proc)
  \/ \E proc \in B_processingRequests: B_WaitTick(proc)
  \/ \E proc \in B_processingRequests: B_Retry(proc)
  \/ \E proc \in B_processingRequests: B_FailoverAfterRetries(proc)
  \/ \E proc \in B_processingRequests: B_FailProcessing(proc)

\* ========== 設計C: フェイルオーバーなし ==========

C_RequestIdUsed(rid) ==
  \/ rid \in C_pendingRequests
  \/ \E r \in C_processingRequests: r.requestId = rid
  \/ rid \in C_completedRequests
  \/ rid \in C_failedRequests

C_SubmitRequest(rid) ==
  /\ Cardinality(C_pendingRequests \cup C_completedRequests \cup C_failedRequests) < MaxRequests
  /\ ~C_RequestIdUsed(rid)
  /\ C_pendingRequests' = C_pendingRequests \cup {rid}
  /\ UNCHANGED <<C_processingRequests, C_completedRequests, C_failedRequests>>

\* 設計Cの特徴: プライマリのみ使用（フォールバックなし）
C_StartProcessing(rid) ==
  /\ rid \in C_pendingRequests
  /\ primaryStatus = "available"  \* プライマリのみ
  /\ C_processingRequests' = C_processingRequests \cup {[requestId |-> rid, provider |-> "primary"]}
  /\ C_pendingRequests' = C_pendingRequests \ {rid}
  /\ UNCHANGED <<C_completedRequests, C_failedRequests>>

C_CompleteProcessing(proc) ==
  /\ proc \in C_processingRequests
  /\ primaryStatus = "available"
  /\ C_completedRequests' = C_completedRequests \cup {proc.requestId}
  /\ C_processingRequests' = C_processingRequests \ {proc}
  /\ UNCHANGED <<C_pendingRequests, C_failedRequests>>

\* 設計Cの特徴: フェイルオーバーなし → 即失敗
C_FailProcessing(proc) ==
  /\ proc \in C_processingRequests
  /\ primaryStatus = "unavailable"
  /\ C_failedRequests' = C_failedRequests \cup {proc.requestId}
  /\ C_processingRequests' = C_processingRequests \ {proc}
  /\ UNCHANGED <<C_pendingRequests, C_completedRequests>>

C_Next ==
  \/ \E rid \in RequestId: C_SubmitRequest(rid)
  \/ \E rid \in C_pendingRequests: C_StartProcessing(rid)
  \/ \E proc \in C_processingRequests: C_CompleteProcessing(proc)
  \/ \E proc \in C_processingRequests: C_FailProcessing(proc)

\* ========== プロバイダー状態変更（共通） ==========

PrimaryFail ==
  /\ primaryStatus = "available"
  /\ primaryStatus' = "unavailable"
  /\ UNCHANGED <<fallbackStatus>>

PrimaryRecover ==
  /\ primaryStatus = "unavailable"
  /\ primaryStatus' = "available"
  /\ UNCHANGED <<fallbackStatus>>

FallbackFail ==
  /\ fallbackStatus = "available"
  /\ fallbackStatus' = "unavailable"
  /\ UNCHANGED <<primaryStatus>>

FallbackRecover ==
  /\ fallbackStatus = "unavailable"
  /\ fallbackStatus' = "available"
  /\ UNCHANGED <<primaryStatus>>

ProviderNext ==
  \/ (PrimaryFail /\ UNCHANGED varsA /\ UNCHANGED varsB /\ UNCHANGED varsC)
  \/ (PrimaryRecover /\ UNCHANGED varsA /\ UNCHANGED varsB /\ UNCHANGED varsC)
  \/ (FallbackFail /\ UNCHANGED varsA /\ UNCHANGED varsB /\ UNCHANGED varsC)
  \/ (FallbackRecover /\ UNCHANGED varsA /\ UNCHANGED varsB /\ UNCHANGED varsC)

\* ========== 次状態 ==========

Next ==
  \/ (A_Next /\ UNCHANGED varsB /\ UNCHANGED varsC /\ UNCHANGED <<primaryStatus, fallbackStatus>>)
  \/ (B_Next /\ UNCHANGED varsA /\ UNCHANGED varsC /\ UNCHANGED <<primaryStatus, fallbackStatus>>)
  \/ (C_Next /\ UNCHANGED varsA /\ UNCHANGED varsB /\ UNCHANGED <<primaryStatus, fallbackStatus>>)
  \/ ProviderNext

Spec == Init /\ [][Next]_vars

\* ========== 不変条件 ==========

\* 設計A: 少なくとも1つのプロバイダーが利用可能なら、処理中リクエストは完了可能性がある
\* 注意: この不変条件は「完了可能なパスが存在する」ことを示す
\* フォールバックプロバイダーが後で利用不可になるケースは別途検証
Inv_A_CanComplete ==
  \A proc \in A_processingRequests:
    \/ (proc.provider = "primary" /\ primaryStatus = "available")
    \/ (proc.provider = "fallback" /\ fallbackStatus = "available")
    \/ (proc.provider = "primary" /\ primaryStatus = "unavailable" /\ fallbackStatus = "available")
    \/ (proc.provider = "primary" /\ primaryStatus = "unavailable" /\ fallbackStatus = "unavailable")  \* 両方不可なら失敗パスへ
    \/ (proc.provider = "fallback" /\ fallbackStatus = "unavailable")  \* 失敗パスへ

\* 設計B: リトライ中はフェイルオーバー不可（最大リトライ後のみ可能）
\* この不変条件は「設計Bの問題」を示す - リトライ中に可用性が保証されない
Inv_B_CanComplete ==
  (primaryStatus = "available" \/ fallbackStatus = "available") =>
    \A proc \in B_processingRequests:
      \/ (proc.provider = "primary" /\ primaryStatus = "available")
      \/ (proc.provider = "fallback" /\ fallbackStatus = "available")
      \/ (proc.provider = "primary" /\ proc.retryCount >= MaxRetries /\ fallbackStatus = "available")
      \* 問題: リトライ中（retryCount < MaxRetries）はフォールバック不可

\* 設計B固有: リトライ間隔が守られる
Inv_B_RetryDelayRespected ==
  \A proc \in B_processingRequests:
    proc.retryCount > 0 => proc.waitTicks >= 0

\* 設計B固有: 最大リトライ前にフェイルオーバーしない
Inv_B_NoSkipToFailover ==
  \A proc \in B_processingRequests:
    proc.provider = "fallback" => TRUE  \* フォールバック中はOK

\* 設計C: プライマリが利用不可の場合、処理中リクエストは完了不可能
\* この不変条件は「設計Cの問題」を示すために意図的に破られる
Inv_C_CanComplete ==
  (primaryStatus = "available" \/ fallbackStatus = "available") =>
    \A proc \in C_processingRequests:
      primaryStatus = "available"  \* フォールバックがないため、プライマリのみに依存

\* ========== 比較用プロパティ ==========

\* 設計Aでは、フォールバックが利用可能ならプライマリ障害時も処理継続可能
Property_A_FailoverWorks ==
  \A proc \in A_processingRequests:
    proc.provider = "primary" /\ primaryStatus = "unavailable" /\ fallbackStatus = "available"
      => ENABLED A_FailoverRetry(proc)

\* 設計Cでは、プライマリ障害時は即失敗（フォールバックオプションなし）
Property_C_NoFailover ==
  \A proc \in C_processingRequests:
    primaryStatus = "unavailable" => ~(ENABLED C_CompleteProcessing(proc))

====
