/**
 * Cursor pagination utilities
 */

import type { ScoredClaim, PaginatedSearchResult } from './types.js';

/**
 * Apply cursor-based pagination to search results
 *
 * @param allResults Full search results
 * @param cursor Cursor (claim_id) to start after
 * @param limit Page size
 * @returns Paginated result with next_cursor and has_more
 */
export function paginateResults(
  allResults: ScoredClaim[],
  cursor: string | undefined,
  limit: number
): PaginatedSearchResult {
  // カーソル以降のデータをフィルタ
  let filteredResults = allResults;
  if (cursor) {
    const cursorIndex = allResults.findIndex((r) => r.claim.id === cursor);
    if (cursorIndex >= 0) {
      // カーソルの次から取得
      filteredResults = allResults.slice(cursorIndex + 1);
    }
  }

  // has_more判定とlimit適用
  const has_more = filteredResults.length > limit;
  const results = filteredResults.slice(0, limit);

  // 次カーソル（最後のclaim_id）
  const next_cursor =
    has_more && results.length > 0 ? results[results.length - 1]!.claim.id : undefined;

  return {
    results,
    next_cursor,
    has_more,
    total_in_page: results.length,
  };
}
