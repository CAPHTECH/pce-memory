---- MODULE pce_memory ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Scope, AllowTag, PolicyVersion, ContentHash, RateLimitBuckets, ACId,
          Rid, Time, ReqCounterMax, OpTag,
          MinScore, MaxScore, FeedbackDelta, RateLimitCap, RefillPerTick

VARIABLES policyApplied, claims, acs, logs, rateState, critic, reqCounter

MinInt(a, b) == IF a < b THEN a ELSE b
Cap(b) == RateLimitCap

RequestRec == [op: OpTag, ts: Time, ok: BOOLEAN, req: Rid]
BoundedSeq(S, n) == { s \in Seq(S) : Len(s) <= n }
DefaultScope == CHOOSE s \in Scope : TRUE
AnotherScope == CHOOSE s \in Scope : s # DefaultScope

\* 型制約
TypeInv == /\ policyApplied \in {TRUE, FALSE}
           /\ claims \in [ContentHash -> [scope: Scope, allow: SUBSET AllowTag]]
           /\ acs \in [ACId -> [claims: SUBSET ContentHash, allow: SUBSET AllowTag, scope: SUBSET Scope, expires: Time]]
           /\ logs \in BoundedSeq(RequestRec, ReqCounterMax)
           /\ rateState \in [RateLimitBuckets -> 0..RateLimitCap]
           /\ critic \in [ContentHash -> MinScore..MaxScore]
           /\ reqCounter \in 0..ReqCounterMax

ReqSet == { logs[i].req : i \in 1..Len(logs) }
CanLog == Len(logs) < ReqCounterMax

Init == /\ policyApplied = FALSE
        /\ claims = [c \in ContentHash |-> [scope |-> IF c = CHOOSE x \in ContentHash : TRUE THEN DefaultScope ELSE AnotherScope, allow |-> {}]]
        /\ acs = [id \in ACId |-> [claims |-> {}, allow |-> {}, scope |-> {}, expires |-> 0]]
        /\ logs = << >>
        /\ rateState = [b \in RateLimitBuckets |-> 0]
        /\ critic = [c \in ContentHash |-> MinScore]
        /\ reqCounter = 0

\* アクション
ApplyPolicy == /\ ~policyApplied
               /\ policyApplied' = TRUE
               /\ UNCHANGED <<claims, acs, logs, rateState, critic, reqCounter>>

Upsert(ch, sc, allowSet, rid) == /\ policyApplied
                                  /\ ch \notin DOMAIN claims
                                  /\ rid \notin ReqSet
                                  /\ CanLog
                                  /\ claims' = [claims EXCEPT ![ch] = [scope |-> sc, allow |-> allowSet]]
                                  /\ critic' = [critic EXCEPT ![ch] = MinScore]
                                  /\ logs' = Append(logs, [op |-> "upsert", ts |-> Len(logs), ok |-> TRUE, req |-> rid])
                                  /\ reqCounter' = reqCounter + 1
                                  /\ UNCHANGED <<policyApplied, acs, rateState>>

Activate(id, scopeSet, allowSet, now, ttl, rid) == /\ policyApplied
                                                    /\ id \in ACId
                                                    /\ rid \notin ReqSet
                                                    /\ acs' = [acs EXCEPT ![id] = [claims |-> {ch \in DOMAIN claims : claims[ch].scope \in scopeSet /\ claims[ch].allow \intersect allowSet # {}}, allow |-> allowSet, scope |-> scopeSet, expires |-> now+ttl]]
                                                    /\ CanLog
                                                    /\ logs' = Append(logs, [op |-> "activate", ts |-> Len(logs), ok |-> TRUE, req |-> rid])
                                                    /\ reqCounter' = reqCounter + 1
                                                    /\ UNCHANGED <<policyApplied, claims, rateState, critic>>
                                                    

BoundaryValidate(payloadAllowed, rid) == /\ policyApplied
                                          /\ payloadAllowed
                                          /\ rid \notin ReqSet
                                          /\ CanLog
                                          /\ logs' = Append(logs, [op |-> "validate", ts |-> Len(logs), ok |-> TRUE, req |-> rid])
                                          /\ reqCounter' = reqCounter + 1
                                          /\ UNCHANGED <<policyApplied, claims, acs, rateState, critic>>

BoundaryValidateDeny(rid) == /\ policyApplied
                              /\ rid \notin ReqSet
                              /\ CanLog
                              /\ logs' = Append(logs, [op |-> "validate.deny", ts |-> Len(logs), ok |-> FALSE, req |-> rid])
                              /\ reqCounter' = reqCounter + 1
                              /\ UNCHANGED <<policyApplied, claims, acs, rateState, critic>>

Feedback(ch, rid) == /\ policyApplied
                      /\ ch \in DOMAIN claims
                      /\ rid \notin ReqSet
                      /\ CanLog
                      /\ critic' = [critic EXCEPT ![ch] = MinInt(MaxScore, critic[ch] + FeedbackDelta)]
                      /\ logs' = Append(logs, [op |-> "feedback", ts |-> Len(logs), ok |-> TRUE, req |-> rid])
                      /\ reqCounter' = reqCounter + 1
                      /\ UNCHANGED <<policyApplied, claims, acs, rateState>>

FeedbackAny(ch) == \E rid \in Rid: Feedback(ch, rid)

ExpireAC(now) == /\ policyApplied
                  /\ acs' = [id \in DOMAIN acs |->
                             IF acs[id].expires <= now
                                THEN [claims |-> {}, allow |-> {}, scope |-> {}, expires |-> acs[id].expires]
                                ELSE acs[id]]
                  /\ logs' = logs
                  /\ reqCounter' = reqCounter
                  /\ UNCHANGED <<policyApplied, claims, rateState, critic>>

RateLimit(bucket, cost, rid) == /\ policyApplied
                                 /\ bucket \in RateLimitBuckets
                                 /\ cost \in Nat
                                 /\ rid \notin ReqSet
                                 /\ rateState' = [rateState EXCEPT ![bucket] = MinInt(RateLimitCap, rateState[bucket] + cost)]
                                 /\ CanLog
                                 /\ logs' = Append(logs, [op |-> "rate", ts |-> Len(logs), ok |-> TRUE, req |-> rid])
                                 /\ reqCounter' = reqCounter + 1
                                 /\ UNCHANGED <<policyApplied, claims, acs, critic>>

ResetRate(bucket, rid) == /\ policyApplied
                           /\ bucket \in RateLimitBuckets
                           /\ rateState[bucket] > 0
                           /\ rid \notin ReqSet
                           /\ CanLog
                           /\ rateState' = [rateState EXCEPT ![bucket] = 0]
                           /\ logs' = Append(logs, [op |-> "rate.reset", ts |-> Len(logs), ok |-> TRUE, req |-> rid])
                           /\ reqCounter' = reqCounter + 1
                           /\ UNCHANGED <<policyApplied, claims, acs, critic>>

RefillTick == /\ policyApplied
              /\ UNCHANGED <<policyApplied, claims, acs, rateState, logs, critic, reqCounter>>

ActivateAny == \E id \in ACId,
                 scopeSet \in SUBSET Scope,
                 allowSet \in SUBSET AllowTag,
                 now \in Time,
                 ttl \in Time,
                 rid \in Rid : Activate(id, scopeSet, allowSet, now, ttl, rid)

Next == ApplyPolicy
        \/ (\E ch \in ContentHash, sc \in Scope, allowSet \in SUBSET AllowTag, rid \in Rid: Upsert(ch, sc, allowSet, rid))
        \/ ActivateAny
        \/ (\E payloadAllowed \in BOOLEAN, rid \in Rid: BoundaryValidate(payloadAllowed, rid))
        \/ (\E rid \in Rid: BoundaryValidateDeny(rid))
        \/ (\E ch \in ContentHash, rid \in Rid: Feedback(ch, rid))
        \/ (\E now \in Time: ExpireAC(now))
        \/ RefillTick

Fairness == WF_<<policyApplied, claims, acs, logs, rateState, critic, reqCounter>>(RefillTick)
Live_ActivateEventually == policyApplied => <> (\E id \in ACId : acs[id].claims # {})
Spec == Init /\ [][Next]_<<policyApplied, claims, acs, logs, rateState, critic, reqCounter>> /\ Fairness

\* 安全性
Inv_NoDuplicateHash == \A ch1, ch2 \in DOMAIN claims : ch1 # ch2 => claims[ch1] /= claims[ch2]
Inv_AC_Allowed == \A id \in DOMAIN acs : \A ch \in acs[id].claims : claims[ch].scope \in acs[id].scope /\ claims[ch].allow \intersect acs[id].allow # {}
Inv_RateNonNegative == \A b \in RateLimitBuckets : rateState[b] \in Nat
Inv_CriticBounds == \A ch \in DOMAIN critic : MinScore <= critic[ch] /\ critic[ch] <= MaxScore
Inv_LogReqUnique == \A i, j \in 1..Len(logs) : i # j => logs[i].req # logs[j].req
Inv_ReqCounterMonotone == reqCounter >= Len(logs)
Inv_LogsMonotone == \A i \in 1..(Len(logs)-1) : logs[i].ts <= logs[i+1].ts

====
