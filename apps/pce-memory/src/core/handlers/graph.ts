/**
 * Graph handlers: entity and relation upsert/query operations.
 */

import * as E from 'fp-ts/Either';
import { createToolResult, err, validateStringFields } from './shared.js';
import { upsertEntity, queryEntities } from '../../store/entities.js';
import type { EntityQueryFilters } from '../../store/entities.js';
import { upsertRelation, queryRelations } from '../../store/relations.js';
import type { RelationQueryFilters } from '../../store/relations.js';
import { appendLog } from '../../store/logs.js';
import { checkAndConsume } from '../../store/rate.js';
import { stateError } from '../../domain/stateMachine.js';
import { ENTITY_TYPES, isValidEntityType } from '../../domain/types.js';
import {
  canDoUpsert,
  canDoQuery,
  getPolicyVersion,
  getStateType,
} from '../../state/memoryState.js';

export async function handleUpsertEntity(args: Record<string, unknown>) {
  const { id, type, name, canonical_key, attrs } = args as {
    id?: string;
    type?: string;
    name?: string;
    canonical_key?: string;
    attrs?: Record<string, unknown>;
  };
  const reqId = crypto.randomUUID();
  const traceId = crypto.randomUUID();

  try {
    // 状態検証（PolicyApplied以降で利用可能）
    if (!canDoUpsert()) {
      const error = stateError('PolicyApplied or HasClaims or Ready', getStateType());
      return createToolResult(
        { ...err('STATE_ERROR', error.message, reqId), trace_id: traceId },
        { isError: true }
      );
    }

    // レート制限チェック
    if (!(await checkAndConsume('tool'))) {
      return createToolResult(
        { ...err('RATE_LIMIT', 'rate limit exceeded', reqId), trace_id: traceId },
        { isError: true }
      );
    }

    // バリデーション
    if (!id || !type || !name) {
      return createToolResult(
        { ...err('VALIDATION_ERROR', 'id, type, name are required', reqId), trace_id: traceId },
        { isError: true }
      );
    }

    if (!isValidEntityType(type)) {
      return createToolResult(
        {
          ...err('VALIDATION_ERROR', `type must be one of: ${ENTITY_TYPES.join(', ')}`, reqId),
          trace_id: traceId,
        },
        { isError: true }
      );
    }

    // 文字列長バリデーション
    const entityFieldsResult = validateStringFields([
      ['id', id, 256],
      ['name', name, 1024],
    ]);
    if (E.isLeft(entityFieldsResult)) {
      return createToolResult(
        { ...err('VALIDATION_ERROR', entityFieldsResult.left.message, reqId), trace_id: traceId },
        { isError: true }
      );
    }

    // Entity登録（exactOptionalPropertyTypes対応: undefinedを渡さない）
    const entity = await upsertEntity({
      id,
      type: type as 'Actor' | 'Artifact' | 'Event' | 'Concept',
      name,
      ...(canonical_key !== undefined && { canonical_key }),
      ...(attrs !== undefined && { attrs }),
    });

    await appendLog({
      id: `log_${reqId}`,
      op: 'upsert_entity',
      ok: true,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });

    return createToolResult({
      id: entity.id,
      type: entity.type,
      name: entity.name,
      canonical_key: entity.canonical_key,
      policy_version: getPolicyVersion(),
      state: getStateType(),
      request_id: reqId,
      trace_id: traceId,
    });
  } catch (e: unknown) {
    await appendLog({
      id: `log_${reqId}`,
      op: 'upsert_entity',
      ok: false,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });
    const msg = e instanceof Error ? e.message : String(e);
    return createToolResult(
      { ...err('UPSERT_ENTITY_FAILED', msg, reqId), trace_id: traceId },
      { isError: true }
    );
  }
}

export async function handleUpsertRelation(args: Record<string, unknown>) {
  const { id, src_id, dst_id, type, props, evidence_claim_id } = args as {
    id?: string;
    src_id?: string;
    dst_id?: string;
    type?: string;
    props?: Record<string, unknown>;
    evidence_claim_id?: string;
  };
  const reqId = crypto.randomUUID();
  const traceId = crypto.randomUUID();

  try {
    // 状態検証（PolicyApplied以降で利用可能）
    if (!canDoUpsert()) {
      const error = stateError('PolicyApplied or HasClaims or Ready', getStateType());
      return createToolResult(
        { ...err('STATE_ERROR', error.message, reqId), trace_id: traceId },
        { isError: true }
      );
    }

    // レート制限チェック
    if (!(await checkAndConsume('tool'))) {
      return createToolResult(
        { ...err('RATE_LIMIT', 'rate limit exceeded', reqId), trace_id: traceId },
        { isError: true }
      );
    }

    // バリデーション
    if (!id || !src_id || !dst_id || !type) {
      return createToolResult(
        {
          ...err('VALIDATION_ERROR', 'id, src_id, dst_id, type are required', reqId),
          trace_id: traceId,
        },
        { isError: true }
      );
    }

    // 文字列長バリデーション
    const relationFieldsResult = validateStringFields([
      ['id', id, 256],
      ['src_id', src_id, 256],
      ['dst_id', dst_id, 256],
      ['type', type, 256],
    ]);
    if (E.isLeft(relationFieldsResult)) {
      return createToolResult(
        { ...err('VALIDATION_ERROR', relationFieldsResult.left.message, reqId), trace_id: traceId },
        { isError: true }
      );
    }

    // Relation登録（exactOptionalPropertyTypes対応: undefinedを渡さない）
    const relation = await upsertRelation({
      id,
      src_id,
      dst_id,
      type,
      ...(props !== undefined && { props }),
      ...(evidence_claim_id !== undefined && { evidence_claim_id }),
    });

    await appendLog({
      id: `log_${reqId}`,
      op: 'upsert_relation',
      ok: true,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });

    return createToolResult({
      id: relation.id,
      src_id: relation.src_id,
      dst_id: relation.dst_id,
      type: relation.type,
      evidence_claim_id: relation.evidence_claim_id,
      policy_version: getPolicyVersion(),
      state: getStateType(),
      request_id: reqId,
      trace_id: traceId,
    });
  } catch (e: unknown) {
    await appendLog({
      id: `log_${reqId}`,
      op: 'upsert_relation',
      ok: false,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });
    const msg = e instanceof Error ? e.message : String(e);
    return createToolResult(
      { ...err('UPSERT_RELATION_FAILED', msg, reqId), trace_id: traceId },
      { isError: true }
    );
  }
}

export async function handleQueryEntity(args: Record<string, unknown>) {
  const { id, type, canonical_key, claim_id, limit } = args as {
    id?: string;
    type?: string;
    canonical_key?: string;
    claim_id?: string;
    limit?: number;
  };
  const reqId = crypto.randomUUID();
  const traceId = crypto.randomUUID();

  try {
    // 状態検証（PolicyApplied以降で利用可能）
    if (!canDoQuery()) {
      const error = stateError('PolicyApplied or HasClaims or Ready', getStateType());
      return createToolResult(
        { ...err('STATE_ERROR', error.message, reqId), trace_id: traceId },
        { isError: true }
      );
    }

    // レート制限チェック
    if (!(await checkAndConsume('tool'))) {
      return createToolResult(
        { ...err('RATE_LIMIT', 'rate limit exceeded', reqId), trace_id: traceId },
        { isError: true }
      );
    }

    // バリデーション: 少なくとも1つのフィルターが必要
    const hasFilter =
      id !== undefined ||
      type !== undefined ||
      canonical_key !== undefined ||
      claim_id !== undefined;
    if (!hasFilter) {
      return createToolResult(
        {
          ...err(
            'VALIDATION_ERROR',
            'at least one filter (id, type, canonical_key, claim_id) is required',
            reqId
          ),
          trace_id: traceId,
        },
        { isError: true }
      );
    }

    // typeのバリデーション
    if (type !== undefined && !isValidEntityType(type)) {
      return createToolResult(
        {
          ...err('VALIDATION_ERROR', `type must be one of: ${ENTITY_TYPES.join(', ')}`, reqId),
          trace_id: traceId,
        },
        { isError: true }
      );
    }

    // limitのバリデーション
    if (limit !== undefined) {
      if (typeof limit !== 'number' || !Number.isFinite(limit) || !Number.isInteger(limit) || limit < 1) {
        return createToolResult(
          {
            ...err('VALIDATION_ERROR', 'limit must be a positive integer', reqId),
            trace_id: traceId,
          },
          { isError: true }
        );
      }
    }

    // クエリ実行
    const filters: EntityQueryFilters = {
      ...(id !== undefined && { id }),
      ...(type !== undefined && { type: type as 'Actor' | 'Artifact' | 'Event' | 'Concept' }),
      ...(canonical_key !== undefined && { canonical_key }),
      ...(claim_id !== undefined && { claim_id }),
      ...(limit !== undefined && { limit }),
    };
    const entities = await queryEntities(filters);

    await appendLog({
      id: `log_${reqId}`,
      op: 'query_entity',
      ok: true,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });

    // safeJsonStringifyを使用してBigInt値を安全にシリアライズ
    return createToolResult(
      {
        entities,
        count: entities.length,
        policy_version: getPolicyVersion(),
        state: getStateType(),
        request_id: reqId,
        trace_id: traceId,
      },
      { useSafeStringify: true }
    );
  } catch (e: unknown) {
    await appendLog({
      id: `log_${reqId}`,
      op: 'query_entity',
      ok: false,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });
    const msg = e instanceof Error ? e.message : String(e);
    return createToolResult(
      { ...err('QUERY_ENTITY_FAILED', msg, reqId), trace_id: traceId },
      { isError: true, useSafeStringify: true }
    );
  }
}

export async function handleQueryRelation(args: Record<string, unknown>) {
  const { id, src_id, dst_id, type, evidence_claim_id, limit } = args as {
    id?: string;
    src_id?: string;
    dst_id?: string;
    type?: string;
    evidence_claim_id?: string;
    limit?: number;
  };
  const reqId = crypto.randomUUID();
  const traceId = crypto.randomUUID();

  try {
    // 状態検証（PolicyApplied以降で利用可能）
    if (!canDoQuery()) {
      const error = stateError('PolicyApplied or HasClaims or Ready', getStateType());
      return createToolResult(
        { ...err('STATE_ERROR', error.message, reqId), trace_id: traceId },
        { isError: true }
      );
    }

    // レート制限チェック
    if (!(await checkAndConsume('tool'))) {
      return createToolResult(
        { ...err('RATE_LIMIT', 'rate limit exceeded', reqId), trace_id: traceId },
        { isError: true }
      );
    }

    // バリデーション: 少なくとも1つのフィルターが必要
    const hasFilter =
      id !== undefined ||
      src_id !== undefined ||
      dst_id !== undefined ||
      type !== undefined ||
      evidence_claim_id !== undefined;
    if (!hasFilter) {
      return createToolResult(
        {
          ...err(
            'VALIDATION_ERROR',
            'at least one filter (id, src_id, dst_id, type, evidence_claim_id) is required',
            reqId
          ),
          trace_id: traceId,
        },
        { isError: true }
      );
    }

    // limitのバリデーション
    if (limit !== undefined) {
      if (typeof limit !== 'number' || !Number.isFinite(limit) || !Number.isInteger(limit) || limit < 1) {
        return createToolResult(
          {
            ...err('VALIDATION_ERROR', 'limit must be a positive integer', reqId),
            trace_id: traceId,
          },
          { isError: true }
        );
      }
    }

    // クエリ実行
    const filters: RelationQueryFilters = {
      ...(id !== undefined && { id }),
      ...(src_id !== undefined && { src_id }),
      ...(dst_id !== undefined && { dst_id }),
      ...(type !== undefined && { type }),
      ...(evidence_claim_id !== undefined && { evidence_claim_id }),
      ...(limit !== undefined && { limit }),
    };
    const relations = await queryRelations(filters);

    await appendLog({
      id: `log_${reqId}`,
      op: 'query_relation',
      ok: true,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });

    // safeJsonStringifyを使用してBigInt値を安全にシリアライズ
    return createToolResult(
      {
        relations,
        count: relations.length,
        policy_version: getPolicyVersion(),
        state: getStateType(),
        request_id: reqId,
        trace_id: traceId,
      },
      { useSafeStringify: true }
    );
  } catch (e: unknown) {
    await appendLog({
      id: `log_${reqId}`,
      op: 'query_relation',
      ok: false,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });
    const msg = e instanceof Error ? e.message : String(e);
    return createToolResult(
      { ...err('QUERY_RELATION_FAILED', msg, reqId), trace_id: traceId },
      { isError: true, useSafeStringify: true }
    );
  }
}
