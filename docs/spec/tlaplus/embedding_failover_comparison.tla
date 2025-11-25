---- MODULE embedding_failover_comparison ----
\* Embedding Failover Strategy Design Comparison
\* ADR-0003: フェイルオーバー戦略の形式検証
\*
\* 比較する設計:
\* - 設計A: 即時フェイルオーバー（採用）
\* - 設計C: フェイルオーバーなし（不採用）
\*
\* 検証する性質:
\* - RequestCompletion: 少なくとも1つのプロバイダーが利用可能なら、リクエストは完了する

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
  RequestId,
  MaxRequests

VARIABLES
  \* 共通状態
  primaryStatus,      \* "available" or "unavailable"
  fallbackStatus,     \* "available" or "unavailable"

  \* 設計A（即時フェイルオーバー）
  A_pendingRequests,
  A_processingRequests,
  A_completedRequests,
  A_failedRequests,

  \* 設計C（フェイルオーバーなし）
  C_pendingRequests,
  C_processingRequests,
  C_completedRequests,
  C_failedRequests

varsA == <<A_pendingRequests, A_processingRequests, A_completedRequests, A_failedRequests>>
varsC == <<C_pendingRequests, C_processingRequests, C_completedRequests, C_failedRequests>>
vars == <<primaryStatus, fallbackStatus, A_pendingRequests, A_processingRequests, A_completedRequests, A_failedRequests, C_pendingRequests, C_processingRequests, C_completedRequests, C_failedRequests>>

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
  \/ (PrimaryFail /\ UNCHANGED varsA /\ UNCHANGED varsC)
  \/ (PrimaryRecover /\ UNCHANGED varsA /\ UNCHANGED varsC)
  \/ (FallbackFail /\ UNCHANGED varsA /\ UNCHANGED varsC)
  \/ (FallbackRecover /\ UNCHANGED varsA /\ UNCHANGED varsC)

\* ========== 次状態 ==========

Next ==
  \/ (A_Next /\ UNCHANGED varsC /\ UNCHANGED <<primaryStatus, fallbackStatus>>)
  \/ (C_Next /\ UNCHANGED varsA /\ UNCHANGED <<primaryStatus, fallbackStatus>>)
  \/ ProviderNext

Spec == Init /\ [][Next]_vars

\* ========== 不変条件 ==========

\* 設計A: 少なくとも1つのプロバイダーが利用可能なら、処理中リクエストは最終的に完了可能
Inv_A_CanComplete ==
  (primaryStatus = "available" \/ fallbackStatus = "available") =>
    \A proc \in A_processingRequests:
      (proc.provider = "primary" /\ primaryStatus = "available") \/
      (proc.provider = "fallback" /\ fallbackStatus = "available") \/
      (proc.provider = "primary" /\ fallbackStatus = "available")  \* フェイルオーバー可能

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
