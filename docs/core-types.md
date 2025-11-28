# Core Module Type Definitions (TypeScript + fp-ts)

> **目的**: pce-memory の Core モジュール（extractor/integrator/retriever/critic）の型定義を、Law-Driven Engineering (LDE) の原則に基づいて定義する。
> **Storage**: DuckDB を使用
> **Error Handling**: fp-ts の Either/TaskEither/ReaderTaskEither パターンを使用

---

## 0. 前提と原則

### 0.1 Law-Driven Engineering (LDE) 原則

- **Type-Driven Design**: 型システムで不正な状態を表現不可能にする
- **Property-Based Testing**: 不変条件をテストで検証
- **Functional Purity**: 副作用を明示的に型で表現
- **Error as Values**: 例外を使わず Either/TaskEither でエラーを値として扱う

### 0.2 依存ライブラリ

```typescript
import * as E from 'fp-ts/Either';
import * as TE from 'fp-ts/TaskEither';
import * as RTE from 'fp-ts/ReaderTaskEither';
import * as O from 'fp-ts/Option';
import { pipe, flow } from 'fp-ts/function';
import * as t from 'io-ts';
import { Brand } from 'io-ts';
```

---

## 1. Domain Types (基盤型定義)

### 1.1 Branded Types (ブランド型)

```typescript
// ID types with runtime validation
interface ClaimIdBrand {
  readonly ClaimId: unique symbol;
}
export type ClaimId = Brand<string, ClaimIdBrand>;

interface ObservationIdBrand {
  readonly ObservationId: unique symbol;
}
export type ObservationId = Brand<string, ObservationIdBrand>;

interface ActiveContextIdBrand {
  readonly ActiveContextId: unique symbol;
}
export type ActiveContextId = Brand<string, ActiveContextIdBrand>;

interface EntityIdBrand {
  readonly EntityId: unique symbol;
}
export type EntityId = Brand<string, EntityIdBrand>;

interface RelationIdBrand {
  readonly RelationId: unique symbol;
}
export type RelationId = Brand<string, RelationIdBrand>;

interface PolicyVersionBrand {
  readonly PolicyVersion: unique symbol;
}
export type PolicyVersion = Brand<string, PolicyVersionBrand>;

interface EvidenceIdBrand {
  readonly EvidenceId: unique symbol;
}
export type EvidenceId = Brand<string, EvidenceIdBrand>;

interface FeedbackIdBrand {
  readonly FeedbackId: unique symbol;
}
export type FeedbackId = Brand<string, FeedbackIdBrand>;

// SemVer validation regex
const semverRegex =
  /^\d+\.\d+\.\d+(-[0-9A-Za-z-]+(\.[0-9A-Za-z-]+)*)?(\+[0-9A-Za-z-]+(\.[0-9A-Za-z-]+)*)?$/;

// ID constructors with validation (returning CoreError)
export const ClaimId = {
  codec: t.brand(t.string, (s): s is ClaimId => s.startsWith('clm_'), 'ClaimId'),
  make: (s: string): E.Either<PCEError, ClaimId> =>
    s.startsWith('clm_') ? E.right(s as ClaimId) : E.left(CoreError.invalidId('ClaimId', s)),
};

export const ObservationId = {
  codec: t.brand(t.string, (s): s is ObservationId => s.startsWith('obs_'), 'ObservationId'),
  make: (s: string): E.Either<PCEError, ObservationId> =>
    s.startsWith('obs_')
      ? E.right(s as ObservationId)
      : E.left(CoreError.invalidId('ObservationId', s)),
};

export const ActiveContextId = {
  codec: t.brand(t.string, (s): s is ActiveContextId => s.startsWith('ac_'), 'ActiveContextId'),
  make: (s: string): E.Either<PCEError, ActiveContextId> =>
    s.startsWith('ac_')
      ? E.right(s as ActiveContextId)
      : E.left(CoreError.invalidId('ActiveContextId', s)),
};

export const EntityId = {
  codec: t.brand(t.string, (s): s is EntityId => s.startsWith('ent_'), 'EntityId'),
  make: (s: string): E.Either<PCEError, EntityId> =>
    s.startsWith('ent_') ? E.right(s as EntityId) : E.left(CoreError.invalidId('EntityId', s)),
};

export const RelationId = {
  codec: t.brand(t.string, (s): s is RelationId => s.startsWith('rel_'), 'RelationId'),
  make: (s: string): E.Either<PCEError, RelationId> =>
    s.startsWith('rel_') ? E.right(s as RelationId) : E.left(CoreError.invalidId('RelationId', s)),
};

export const EvidenceId = {
  codec: t.brand(t.string, (s): s is EvidenceId => s.startsWith('evd_'), 'EvidenceId'),
  make: (s: string): E.Either<PCEError, EvidenceId> =>
    s.startsWith('evd_') ? E.right(s as EvidenceId) : E.left(CoreError.invalidId('EvidenceId', s)),
};

export const FeedbackId = {
  codec: t.brand(t.string, (s): s is FeedbackId => s.startsWith('fb_'), 'FeedbackId'),
  make: (s: string): E.Either<PCEError, FeedbackId> =>
    s.startsWith('fb_') ? E.right(s as FeedbackId) : E.left(CoreError.invalidId('FeedbackId', s)),
};

export const PolicyVersion = {
  codec: t.brand(t.string, (s): s is PolicyVersion => semverRegex.test(s), 'PolicyVersion'),
  make: (s: string): E.Either<PCEError, PolicyVersion> =>
    semverRegex.test(s) ? E.right(s as PolicyVersion) : E.left(CoreError.invalidPolicyVersion(s)),
};
```

### 1.2 Enums (列挙型)

```typescript
// Claim kind (PCE 仕様に準拠)
export const ClaimKind = t.keyof({
  fact: null,
  preference: null,
  task: null,
  policy_hint: null,
});
export type ClaimKind = t.TypeOf<typeof ClaimKind>;

// Scope (PCE の Pace Layering に対応)
export const Scope = t.keyof({
  session: null, // micro - fast (秒〜日)
  project: null, // meso - medium (週〜月)
  principle: null, // macro - slow (年〜十年)
});
export type Scope = t.TypeOf<typeof Scope>;

// Boundary class (機密性分類)
export const BoundaryClass = t.keyof({
  public: null,
  internal: null,
  pii: null,
  secret: null,
});
export type BoundaryClass = t.TypeOf<typeof BoundaryClass>;

// Observation source type
export const SourceType = t.keyof({
  chat: null,
  tool: null,
  file: null,
  http: null,
  system: null,
});
export type SourceType = t.TypeOf<typeof SourceType>;

// Feedback signal
export const FeedbackSignal = t.keyof({
  helpful: null,
  harmful: null,
  outdated: null,
  duplicate: null,
});
export type FeedbackSignal = t.TypeOf<typeof FeedbackSignal>;

// Entity type (ANT vocabulary)
export const EntityType = t.keyof({
  Actor: null,
  Artifact: null,
  Event: null,
  Concept: null,
  Policy: null,
});
export type EntityType = t.TypeOf<typeof EntityType>;
```

### 1.3 Core Domain Types

```typescript
// Provenance (由来・トレーサビリティ)
export const Provenance = t.type({
  at: t.string, // ISO 8601 timestamp
  actor: t.union([t.string, t.undefined]),
  git: t.union([
    t.type({
      commit: t.string,
      repo: t.string,
      url: t.union([t.string, t.undefined]),
      files: t.union([t.array(t.string), t.undefined]),
    }),
    t.undefined,
  ]),
  url: t.union([t.string, t.undefined]),
  note: t.union([t.string, t.undefined]),
  signed: t.union([t.boolean, t.undefined]),
});
export type Provenance = t.TypeOf<typeof Provenance>;

// Observation (生観測)
export const Observation = t.type({
  id: ObservationId.codec,
  source_type: SourceType,
  source_id: t.union([t.string, t.undefined]),
  content: t.string,
  actor: t.union([t.string, t.undefined]),
  tags: t.union([t.array(t.string), t.undefined]),
  created_at: t.number, // UNIX epoch seconds (DuckDB TIMESTAMP 互換)
});
export type Observation = t.TypeOf<typeof Observation>;

// Claim (抽出主張・検索対象)
export const Claim = t.type({
  id: ClaimId.codec,
  text: t.string,
  kind: ClaimKind,
  scope: Scope,
  boundary_class: BoundaryClass,
  origin_observation_id: ObservationId.codec, // REQUIRED for Provenance
  quality: t.number, // [0.0, 1.0]
  confidence: t.number, // [0.0, 1.0]
  utility: t.number, // [-∞, +∞] (z-score or normalized)
  recency: t.number, // [0.0, 1.0] (computed from ts)
  content_hash: t.union([t.string, t.undefined]), // sha256:hex64
  created_at: t.number, // UNIX epoch seconds
  updated_at: t.number, // UNIX epoch seconds
});
export type Claim = t.TypeOf<typeof Claim>;

// DerivedClaim (派生主張 - Provenanceが間接的な場合)
export const DerivedClaim = t.type({
  id: ClaimId.codec,
  text: t.string,
  kind: ClaimKind,
  scope: Scope,
  boundary_class: BoundaryClass,
  origin_observation_id: t.union([ObservationId.codec, t.undefined]),
  derived_from: t.array(ClaimId.codec), // Track derivation chain
  quality: t.number,
  confidence: t.number,
  utility: t.number,
  recency: t.number,
  content_hash: t.union([t.string, t.undefined]),
  created_at: t.number,
  updated_at: t.number,
});
export type DerivedClaim = t.TypeOf<typeof DerivedClaim>;

// Evidence (由来鎖)
export const Evidence = t.type({
  id: EvidenceId.codec, // Branded type
  claim_id: ClaimId.codec,
  observation_id: t.union([ObservationId.codec, t.undefined]),
  method: t.keyof({ rule: null, llm: null, manual: null }),
  note: t.union([t.string, t.undefined]),
});
export type Evidence = t.TypeOf<typeof Evidence>;

// Entity (グラフノード)
export const Entity = t.type({
  id: EntityId.codec, // Branded type
  type: EntityType,
  name: t.string,
  canonical_key: t.union([t.string, t.undefined]),
  attrs: t.union([t.record(t.string, t.unknown), t.undefined]),
});
export type Entity = t.TypeOf<typeof Entity>;

// Relation (グラフエッジ)
export const Relation = t.type({
  id: RelationId.codec, // Branded type
  src_id: EntityId.codec, // Branded type
  dst_id: EntityId.codec, // Branded type
  type: t.string, // created|mentions|assigned_to|depends_on|...
  props: t.union([t.record(t.string, t.unknown), t.undefined]),
  evidence_claim_id: t.union([ClaimId.codec, t.undefined]),
});
export type Relation = t.TypeOf<typeof Relation>;

// Feedback (Critic 入力)
export const Feedback = t.type({
  id: FeedbackId.codec, // Branded type
  claim_id: ClaimId.codec,
  ts: t.number, // UNIX epoch seconds
  signal: FeedbackSignal,
  score: t.union([t.number, t.undefined]), // [-1.0, 1.0]
});
export type Feedback = t.TypeOf<typeof Feedback>;

// Active Context (短期・使い捨て)
export const ActiveContext = t.type({
  id: ActiveContextId.codec,
  window: t.union([t.string, t.undefined]),
  scope: Scope,
  provenance: t.union([t.array(Provenance), t.undefined]),
  expires_at: t.number, // UNIX epoch seconds
  policy_version: PolicyVersion.codec, // Branded type
});
export type ActiveContext = t.TypeOf<typeof ActiveContext>;

// Active Context Item (AC に含まれる Claim)
export const ActiveContextItem = t.type({
  ac_id: ActiveContextId.codec,
  claim_id: ClaimId.codec,
  rank: t.number,
  score: t.union([t.number, t.undefined]),
});
export type ActiveContextItem = t.TypeOf<typeof ActiveContextItem>;
```

### 1.4 Boundary & Policy Types

```typescript
// Invariant definition (from policy YAML)
export const InvariantDefinition = t.type({
  name: t.string,
  applies_to: t.array(t.string),
  rule: t.string,
});
export type InvariantDefinition = t.TypeOf<typeof InvariantDefinition>;

// Boundary (境界)
export const Boundary = t.type({
  scope: t.array(Scope),
  allow: t.array(t.string), // allow tags: "answer:task", "tool:*" など
  boundary_classes: t.array(BoundaryClass),
  invariants: t.array(InvariantDefinition),
});
export type Boundary = t.TypeOf<typeof Boundary>;

// Policy (運用ポリシー - YAML からロード)
export const Policy = t.type({
  version: PolicyVersion.codec, // Branded SemVer
  scopes: t.record(
    t.string,
    t.type({
      ttl: t.string,
      max_tokens: t.union([t.number, t.undefined]),
    })
  ),
  boundary_classes: t.record(
    t.string,
    t.type({
      allow: t.array(t.string),
      redact: t.union([t.array(t.string), t.undefined]),
      escalation: t.union([t.string, t.undefined]),
    })
  ),
  invariants: t.union([
    t.array(
      t.type({
        name: t.string,
        applies_to: t.array(t.string),
        rule: t.string,
      })
    ),
    t.undefined,
  ]),
  retrieval: t.union([
    t.type({
      hybrid: t.type({
        alpha: t.number, // [0.0, 1.0]
        k_txt: t.number,
        k_vec: t.number,
        k_final: t.number,
      }),
      rerank: t.union([
        t.type({
          use_quality: t.boolean,
          recency_half_life_days: t.number,
          recency: t.union([
            t.type({
              half_life_days_by_kind: t.record(t.string, t.number),
            }),
            t.undefined,
          ]),
        }),
        t.undefined,
      ]),
    }),
    t.undefined,
  ]),
});
export type Policy = t.TypeOf<typeof Policy>;
```

---

## 2. Error Types (エラー型階層)

### 2.1 Branded Error Types

```typescript
// Base error interface
export interface PCEError {
  readonly _tag: string;
  readonly message: string;
  readonly details?: Record<string, unknown>;
}

// Boundary errors
export interface BoundaryDeniedError extends PCEError {
  readonly _tag: 'BoundaryDeniedError';
  readonly boundary: Boundary;
  readonly reason: string;
}

export interface InvalidScopeError extends PCEError {
  readonly _tag: 'InvalidScopeError';
  readonly provided: string;
  readonly allowed: Scope[];
}

export interface PolicyMissingError extends PCEError {
  readonly _tag: 'PolicyMissingError';
  readonly policy_version?: string;
}

export interface InvalidPolicyError extends PCEError {
  readonly _tag: 'InvalidPolicyError';
  readonly validation_errors: string[];
}

// Data errors
export interface DuplicateClaimError extends PCEError {
  readonly _tag: 'DuplicateClaimError';
  readonly content_hash: string;
  readonly existing_id: ClaimId;
}

export interface UnknownClaimError extends PCEError {
  readonly _tag: 'UnknownClaimError';
  readonly claim_id: ClaimId;
}

export interface InvalidBoundaryError extends PCEError {
  readonly _tag: 'InvalidBoundaryError';
  readonly reason: string;
}

// ID validation errors
export interface InvalidIdError extends PCEError {
  readonly _tag: 'InvalidIdError';
  readonly id_type: string;
  readonly provided: string;
}

export interface InvalidPolicyVersionError extends PCEError {
  readonly _tag: 'InvalidPolicyVersionError';
  readonly provided: string;
}

// Search errors
export interface SearchFailedError extends PCEError {
  readonly _tag: 'SearchFailedError';
  readonly query: string;
  readonly reason: string;
}

export interface EmbeddingFailedError extends PCEError {
  readonly _tag: 'EmbeddingFailedError';
  readonly text: string;
  readonly provider: string;
}

// Database errors
export interface DatabaseError extends PCEError {
  readonly _tag: 'DatabaseError';
  readonly operation: string;
  readonly sql?: string;
}

// Union type for all errors
export type CoreError =
  | BoundaryDeniedError
  | InvalidScopeError
  | PolicyMissingError
  | InvalidPolicyError
  | DuplicateClaimError
  | UnknownClaimError
  | InvalidBoundaryError
  | InvalidIdError
  | InvalidPolicyVersionError
  | SearchFailedError
  | EmbeddingFailedError
  | DatabaseError;

// Error constructors
export const CoreError = {
  boundaryDenied: (boundary: Boundary, reason: string): BoundaryDeniedError => ({
    _tag: 'BoundaryDeniedError',
    message: `Boundary denied: ${reason}`,
    boundary,
    reason,
  }),

  invalidScope: (provided: string, allowed: Scope[]): InvalidScopeError => ({
    _tag: 'InvalidScopeError',
    message: `Invalid scope: ${provided}. Allowed: ${allowed.join(', ')}`,
    provided,
    allowed,
  }),

  policyMissing: (policy_version?: string): PolicyMissingError => ({
    _tag: 'PolicyMissingError',
    message: policy_version ? `Policy ${policy_version} not loaded` : 'No policy loaded',
    policy_version,
  }),

  duplicateClaim: (content_hash: string, existing_id: ClaimId): DuplicateClaimError => ({
    _tag: 'DuplicateClaimError',
    message: `Duplicate claim with hash ${content_hash}`,
    content_hash,
    existing_id,
  }),

  unknownClaim: (claim_id: ClaimId): UnknownClaimError => ({
    _tag: 'UnknownClaimError',
    message: `Claim ${claim_id} not found`,
    claim_id,
  }),

  searchFailed: (query: string, reason: string): SearchFailedError => ({
    _tag: 'SearchFailedError',
    message: `Search failed: ${reason}`,
    query,
    reason,
  }),

  embeddingFailed: (text: string, provider: string): EmbeddingFailedError => ({
    _tag: 'EmbeddingFailedError',
    message: `Embedding failed for provider ${provider}`,
    text,
    provider,
  }),

  database: (operation: string, sql?: string): DatabaseError => ({
    _tag: 'DatabaseError',
    message: `Database error during ${operation}`,
    operation,
    sql,
  }),

  invalidId: (id_type: string, provided: string): InvalidIdError => ({
    _tag: 'InvalidIdError',
    message: `Invalid ${id_type}: ${provided}`,
    id_type,
    provided,
  }),

  invalidPolicyVersion: (provided: string): InvalidPolicyVersionError => ({
    _tag: 'InvalidPolicyVersionError',
    message: `Invalid policy version: ${provided}. Must be valid SemVer`,
    provided,
  }),

  invalidPolicy: (validation_errors: string[]): InvalidPolicyError => ({
    _tag: 'InvalidPolicyError',
    message: `Invalid policy: ${validation_errors.join(', ')}`,
    validation_errors,
  }),

  invalidBoundary: (reason: string): InvalidBoundaryError => ({
    _tag: 'InvalidBoundaryError',
    message: `Invalid boundary: ${reason}`,
    reason,
  }),
};
```

---

## 3. Core Module Contracts (モジュール型定義)

### 3.1 Dependencies (Reader 環境型)

```typescript
// Database connection interface
export interface Database {
  readonly query: <T>(sql: string, params?: unknown[]) => TE.TaskEither<DatabaseError, T[]>;
  readonly execute: (sql: string, params?: unknown[]) => TE.TaskEither<DatabaseError, void>;
  readonly transaction: <T>(fn: () => TE.TaskEither<CoreError, T>) => TE.TaskEither<CoreError, T>;
}

// Embedding provider interface
export interface EmbeddingProvider {
  readonly embed: (text: string) => TE.TaskEither<EmbeddingFailedError, number[]>;
  readonly embedBatch: (texts: string[]) => TE.TaskEither<EmbeddingFailedError, number[][]>;
}

// Policy store interface
export interface PolicyStore {
  readonly getCurrent: () => TE.TaskEither<PolicyMissingError, Policy>;
  readonly getVersion: (version: PolicyVersion) => TE.TaskEither<PolicyMissingError, Policy>;
  readonly apply: (yaml: string) => TE.TaskEither<InvalidPolicyError, PolicyVersion>;
}

// Boundary invariant runtime evaluator
export interface BoundaryInvariant {
  readonly name: string;
  readonly appliesTo: Scope[];
  readonly evaluate: (claims: Claim[]) => TE.TaskEither<CoreError, boolean>;
}

export interface InvariantEvaluator {
  readonly compile: (def: InvariantDefinition) => E.Either<CoreError, BoundaryInvariant>;
  readonly evaluateAll: (
    invariants: BoundaryInvariant[],
    claims: Claim[]
  ) => TE.TaskEither<CoreError, boolean>;
}

// Core module dependencies
export interface CoreDeps {
  readonly db: Database;
  readonly embedding: EmbeddingProvider;
  readonly policyStore: PolicyStore;
  readonly invariantEvaluator: InvariantEvaluator;
}
```

### 3.2 Extractor (Observation → Claim[])

````typescript
/**
 * Extractor: Observation から Claim を抽出する
 *
 * 責務:
 * - Observation の content を解析し、意味のある断片（Claim）に分解
 * - Boundary に基づいて PII/Secret を事前に除去（Redact-before-Extract）
 * - Provenance を維持（origin_observation_id）
 * - 重複チェック（content_hash）
 *
 * @example
 * ```typescript
 * const extractClaims: Extractor = (obs, boundary) =>
 *   pipe(
 *     validateBoundary(obs, boundary),
 *     TE.chain(redactIfNeeded),
 *     TE.chain(parseContent),
 *     TE.chain(generateClaims),
 *     TE.chain(deduplicateByHash)
 *   )
 * ```
 */
export type Extractor = (
  observation: Observation,
  boundary: Boundary
) => RTE.ReaderTaskEither<CoreDeps, CoreError, Claim[]>;

// Extractor helper types
export interface ExtractionResult {
  readonly claims: Claim[];
  readonly evidences: Evidence[];
  readonly entities: Entity[];
  readonly relations: Relation[];
}

export type ExtractorWithGraph = (
  observation: Observation,
  boundary: Boundary
) => RTE.ReaderTaskEither<CoreDeps, CoreError, ExtractionResult>;
````

### 3.3 Integrator (Claim[] → LCP 統合)

````typescript
/**
 * Integrator: Claim を LCP (Latent Context Pool) に統合する
 *
 * 責務:
 * - Distillation: AC からの成果を LCP に昇格（promotion）
 * - Deduplication: content_hash による重複検出とマージ
 * - Boundary validation: 不変量 I(B) の検証
 * - Provenance 保持: evidence 鎖の維持
 * - Graph update: entities/relations の更新
 *
 * @example
 * ```typescript
 * const integrateClaims: Integrator = (claims, boundary, policy) =>
 *   pipe(
 *     validateInvariants(claims, boundary),
 *     TE.chain(deduplicateAndMerge),
 *     TE.chain(updateLCP),
 *     TE.chain(updateGraph),
 *     TE.chain(recordEvent('integrate'))
 *   )
 * ```
 */
export type Integrator = (
  claims: Claim[],
  boundary: Boundary,
  policy: Policy
) => RTE.ReaderTaskEither<CoreDeps, CoreError, void>;

// Integration options
export interface IntegrationOptions {
  readonly merge_strategy: 'replace' | 'merge' | 'keep_newest';
  readonly validate_invariants: boolean;
  readonly update_graph: boolean;
}

export type IntegratorWithOptions = (
  claims: Claim[],
  boundary: Boundary,
  policy: Policy,
  options: IntegrationOptions
) => RTE.ReaderTaskEither<CoreDeps, CoreError, void>;
````

### 3.4 Retriever (r function: Query → AC)

````typescript
/**
 * Query for retrieval
 */
export interface Query {
  readonly q: string; // テキストクエリ
  readonly scope?: Scope[]; // 検索対象スコープ
  readonly allow?: string[]; // allow tags
  readonly top_k?: number; // 最終結果数（既定 12）
  readonly include_meta?: boolean; // スコア詳細を含めるか
}

/**
 * Scored claim with ranking details
 */
export interface ScoredClaim {
  readonly claim: Claim;
  readonly score: number; // 最終スコア (S * g)
  readonly scores?: {
    // スコア内訳（include_meta=true 時）
    readonly text: number; // S_text
    readonly vector: number; // S_vec
    readonly combined: number; // S = α*S_vec + (1-α)*S_text
    readonly utility: number;
    readonly confidence: number;
    readonly quality: number;
    readonly recency: number;
    readonly g: number; // 再ランク係数
  };
  readonly evidences: Evidence[];
  readonly reason?: string; // ランク根拠（デバッグ用）
}

/**
 * Active Context result
 */
export interface ActivationResult {
  readonly active_context: ActiveContext;
  readonly items: ScoredClaim[];
  readonly scoring_params: {
    readonly alpha: number;
    readonly k_txt: number;
    readonly k_vec: number;
    readonly k_final: number;
    readonly recency_half_life_days: number;
  };
}

/**
 * Retriever: r(q, C^L, B, policy, critic) → AC
 *
 * 責務:
 * - Boundary 前置フィルタ (scope/allow/boundary_class/I(B))
 * - ハイブリッド検索 (FTS + Vector)
 * - スコア融合 (S = α*S_vec + (1-α)*S_text)
 * - 再ランク (g = f(utility, confidence, recency))
 * - AC 構成と保存
 * - Provenance 付与
 *
 * @example
 * ```typescript
 * const activate: Retriever = (query, boundary, policy) =>
 *   pipe(
 *     applyBoundaryFilter(query, boundary),
 *     TE.chain(hybridSearch(policy.retrieval)),
 *     TE.chain(rerank(policy.retrieval.rerank)),
 *     TE.chain(createActiveContext),
 *     TE.chain(saveAC)
 *   )
 * ```
 */
export type Retriever = (
  query: Query,
  boundary: Boundary,
  policy: Policy
) => RTE.ReaderTaskEither<CoreDeps, CoreError, ActivationResult>;

// Search function (internal to Retriever)
// Returns CoreError for consistent error handling in pipe composition
export type SearchFunction = (
  query: string,
  scope: Scope[],
  k: number
) => RTE.ReaderTaskEither<CoreDeps, CoreError, ScoredClaim[]>;
````

### 3.5 Critic (Feedback → 指標更新)

````typescript
/**
 * Critic update result
 */
export interface CriticUpdateResult {
  readonly claim_id: ClaimId;
  readonly previous: {
    readonly utility: number;
    readonly confidence: number;
    readonly recency: number;
  };
  readonly updated: {
    readonly utility: number;
    readonly confidence: number;
    readonly recency: number;
  };
}

/**
 * Critic: Feedback → utility/confidence/recency 更新
 *
 * 責務:
 * - Feedback signal に基づき指標を更新:
 *   - helpful: utility += 0.10, confidence += 0.05
 *   - harmful: utility -= 0.20, confidence -= 0.10
 *   - outdated: confidence -= 0.20
 *   - duplicate: 代表にマージ、旧の utility 減衰
 * - Decay 処理 (utility 30日半減、quality 120日半減)
 * - Events に記録
 *
 * @example
 * ```typescript
 * const processFeedback: Critic = (feedback, policy) =>
 *   pipe(
 *     getClaim(feedback.claim_id),
 *     TE.chain(applyFeedbackRules(feedback)),
 *     TE.chain(applyDecay(policy)),
 *     TE.chain(updateClaim),
 *     TE.chain(recordEvent('critic'))
 *   )
 * ```
 */
export type Critic = (
  feedback: Feedback,
  policy: Policy
) => RTE.ReaderTaskEither<CoreDeps, CoreError, CriticUpdateResult>;

// Batch critic for multiple feedbacks
export type BatchCritic = (
  feedbacks: Feedback[],
  policy: Policy
) => RTE.ReaderTaskEither<CoreDeps, CoreError, CriticUpdateResult[]>;

// Decay function (定期実行)
export type DecayFunction = (policy: Policy) => RTE.ReaderTaskEither<CoreDeps, CoreError, void>;
````

---

## 4. Utility Functions (補助関数型)

### 4.1 Boundary Validation

```typescript
/**
 * Boundary validation result
 */
export interface BoundaryValidationResult {
  readonly allowed: boolean;
  readonly reason?: string;
  readonly redacted?: string;
  readonly policy_version: PolicyVersion;
}

/**
 * Validate payload against boundary
 */
export type BoundaryValidator = (
  payload: string,
  boundary: Boundary,
  policy: Policy
) => TE.TaskEither<BoundaryDeniedError, BoundaryValidationResult>;
```

### 4.2 Content Hash

```typescript
/**
 * Generate content hash (sha256)
 *
 * Normalization:
 * - UTF-8 / NFC
 * - CRLF → LF
 * - Trim leading/trailing whitespace
 * - Compress consecutive whitespace
 */
export type ContentHasher = (text: string) => string;
```

### 4.3 Scoring Functions

```typescript
/**
 * Normalize text score
 */
export type TextScoreNormalizer = (bm25_scores: number[]) => number[];

/**
 * Normalize vector score (cos similarity to [0,1])
 */
export type VectorScoreNormalizer = (
  cos_sim: number // [-1, 1]
) => number; // [0, 1]

/**
 * Hybrid fusion (S = α*S_vec + (1-α)*S_text)
 */
export type HybridFusion = (s_text: number, s_vec: number, alpha: number) => number;

/**
 * Rerank function g(utility, confidence, recency)
 */
export type RerankFunction = (utility: number, confidence: number, recency: number) => number;

/**
 * Recency decay (exponential with half-life)
 */
export type RecencyDecay = (
  ts: number, // UNIX epoch seconds
  half_life_days: number
) => number; // [0, 1]
```

---

## 5. Module Interface (外部公開インターフェース)

```typescript
/**
 * Core module exports
 */
export interface CoreModule {
  readonly extractor: Extractor
  readonly integrator: Integrator
  readonly retriever: Retriever
  readonly critic: Critic

  // Utilities
  readonly boundary: {
    readonly validate: BoundaryValidator
    readonly redact: (text: string, policy: Policy) => string
  }
  readonly scoring: {
    readonly hybridFusion: HybridFusion
    readonly rerank: RerankFunction
    readonly recencyDecay: RecencyDecay
  }
  readonly hash: ContentHasher
}

/**
 * Create core module with dependencies
 */
export const createCoreModule = (deps: CoreDeps): CoreModule => ({
  // Implementation will be provided in separate files
  extractor: /* ... */,
  integrator: /* ... */,
  retriever: /* ... */,
  critic: /* ... */,
  boundary: /* ... */,
  scoring: /* ... */,
  hash: /* ... */
})
```

---

## 6. Property-Based Testing Invariants (検証すべき不変条件)

### 6.1 Extractor Invariants

```typescript
// Property 1: 出力 Claim の boundary_class は入力 Boundary に違反しない
∀ obs: Observation, boundary: Boundary.
  extractor(obs, boundary) = Right(claims) ⇒
    ∀ c ∈ claims. c.boundary_class ∈ boundary.boundary_classes

// Property 2: Provenance は必ず維持される
∀ obs: Observation, boundary: Boundary.
  extractor(obs, boundary) = Right(claims) ⇒
    ∀ c ∈ claims. c.origin_observation_id = Some(obs.id)

// Property 3: content_hash は一意
∀ obs: Observation, boundary: Boundary.
  extractor(obs, boundary) = Right(claims) ⇒
    |claims| = |{c.content_hash | c ∈ claims}|
```

### 6.2 Integrator Invariants

```typescript
// Property 1: 不変量 I(B) は常に満たされる
∀ claims: Claim[], boundary: Boundary, policy: Policy.
  integrator(claims, boundary, policy) = Right(_) ⇒
    ∀ inv ∈ boundary.invariants. inv.check(claims) = true

// Property 2: Duplicate は統合される
∀ c1, c2: Claim, boundary: Boundary, policy: Policy.
  c1.content_hash = c2.content_hash ∧
  integrator([c1, c2], boundary, policy) = Right(_) ⇒
    ∃! c_merged ∈ LCP. c_merged.content_hash = c1.content_hash

// Property 3: Boundary class は緩和されない
∀ claims: Claim[], boundary: Boundary, policy: Policy.
  integrator(claims, boundary, policy) = Right(_) ⇒
    ∀ c ∈ claims. LCP.lookup(c.id).boundary_class ≥ c.boundary_class
    (where: secret > pii > internal > public)
```

### 6.3 Retriever Invariants

```typescript
// Property 1: 結果は Boundary で制約される
∀ query: Query, boundary: Boundary, policy: Policy.
  retriever(query, boundary, policy) = Right(result) ⇒
    ∀ item ∈ result.items.
      item.claim.scope ∈ (boundary.scope ∪ query.scope) ∧
      item.claim.boundary_class ∈ boundary.boundary_classes

// Property 2: score は単調減少
∀ query: Query, boundary: Boundary, policy: Policy.
  retriever(query, boundary, policy) = Right(result) ⇒
    ∀ i, j. i < j ⇒ result.items[i].score ≥ result.items[j].score

// Property 3: 最終スコアは閾値以上
∀ query: Query, boundary: Boundary, policy: Policy.
  retriever(query, boundary, policy) = Right(result) ⇒
    ∀ item ∈ result.items. item.score ≥ 0.15
```

### 6.4 Critic Invariants

```typescript
// Property 1: helpful は指標を増加させる
∀ feedback: Feedback.
  feedback.signal = 'helpful' ∧
  critic(feedback, policy) = Right(result) ⇒
    result.updated.utility ≥ result.previous.utility ∧
    result.updated.confidence ≥ result.previous.confidence

// Property 2: harmful は指標を減少させる
∀ feedback: Feedback.
  feedback.signal = 'harmful' ∧
  critic(feedback, policy) = Right(result) ⇒
    result.updated.utility < result.previous.utility ∧
    result.updated.confidence < result.previous.confidence

// Property 3: 指標は範囲内に収まる
∀ feedback: Feedback.
  critic(feedback, policy) = Right(result) ⇒
    result.updated.confidence ∈ [0, 1] ∧
    result.updated.recency ∈ [0, 1]
```

---

## 7. Implementation Checklist

- [ ] 全ての domain types を io-ts codec で定義
- [ ] Branded types (ClaimId, ObservationId 等) の runtime validation
- [ ] Error 型階層のコンストラクタ実装
- [ ] CoreDeps (Database, EmbeddingProvider, PolicyStore) のインターフェース実装
- [ ] Extractor の実装と Property-based テスト
- [ ] Integrator の実装と Property-based テスト
- [ ] Retriever の実装と Property-based テスト
- [ ] Critic の実装と Property-based テスト
- [ ] Boundary validation の実装
- [ ] Content hash normalization の実装
- [ ] Scoring functions (fusion, rerank, decay) の実装
- [ ] Property-based テストで全ての不変条件を検証
- [ ] DuckDB integration (schema.md の DDL を適用)
- [ ] MCP tools から Core module を呼び出す統合テスト

---

## 8. 参考

- `docs/schema.md` - DuckDB スキーマ（TIMESTAMP, マクロ, AC/LCP）
- `docs/activation-ranking.md` - r/S/g の仕様
- `docs/boundary-policy.md` - Boundary/Policy/不変量
- `docs/mcp-tools.md` - MCP ツール JSON Schema
- `docs/pce-model.md` - PCE 概念モデル
- [fp-ts documentation](https://gcanti.github.io/fp-ts/)
- [io-ts documentation](https://gcanti.github.io/io-ts/)
