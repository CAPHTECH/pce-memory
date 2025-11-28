#!/usr/bin/env bash
# ADR-Spec Sync Checker
# Purpose: Verify that ADR documents reference current spec file versions
# Usage: ./scripts/check_adr_spec_sync.sh [--strict]
#
# Exit codes:
#   0 - All ADR-spec references are in sync
#   1 - Sync warnings found (non-strict mode) or errors (strict mode)

set -euo pipefail

SCRIPT_DIR=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$SCRIPT_DIR/.." && pwd)
ADR_DIR="$ROOT/docs/adr"
SPEC_DIR="$ROOT/docs/spec"

STRICT_MODE=false
if [[ "${1:-}" == "--strict" ]]; then
  STRICT_MODE=true
fi

# 色付き出力
RED='\033[0;31m'
YELLOW='\033[1;33m'
GREEN='\033[0;32m'
NC='\033[0m' # No Color

warnings=0
errors=0

echo "=========================================="
echo "ADR-Spec Sync Checker"
echo "=========================================="
echo ""

# ADRファイルを検査
for adr in "$ADR_DIR"/*.md; do
  if [[ ! -f "$adr" ]]; then
    continue
  fi

  adr_name=$(basename "$adr")
  echo "Checking: $adr_name"

  # ADR内で参照されている仕様ファイルを抽出
  # パターン: .tla, .als, .cfg
  referenced_specs=$(grep -oE '[a-zA-Z0-9_-]+\.(tla|als|cfg)' "$adr" | sort -u || true)

  if [[ -z "$referenced_specs" ]]; then
    echo "  (no spec files referenced)"
    continue
  fi

  for spec in $referenced_specs; do
    # 仕様ファイルの存在確認
    spec_path=$(find "$SPEC_DIR" -name "$spec" -type f 2>/dev/null | head -1)

    if [[ -z "$spec_path" ]]; then
      echo -e "  ${RED}ERROR${NC}: Referenced spec '$spec' not found"
      ((errors++))
      continue
    fi

    # 仕様ファイルの最終コミット時刻を取得（Gitタイムスタンプを使用）
    # CIではファイルmtimeがcheckout時刻に統一されるため、git logを使用
    spec_commit_time=$(git log -1 --format="%ct" -- "$spec_path" 2>/dev/null || echo "0")
    adr_commit_time=$(git log -1 --format="%ct" -- "$adr" 2>/dev/null || echo "0")

    # 日付表示用（人間可読形式）
    spec_date=$(git log -1 --format="%cs" -- "$spec_path" 2>/dev/null || echo "unknown")
    adr_date=$(git log -1 --format="%cs" -- "$adr" 2>/dev/null || echo "unknown")

    # ADRより仕様ファイルが新しい場合は警告
    if [[ "$spec_commit_time" -gt "$adr_commit_time" ]]; then
      echo -e "  ${YELLOW}WARN${NC}: $spec (committed: $spec_date) is newer than ADR (committed: $adr_date)"
      ((warnings++))
    else
      echo -e "  ${GREEN}OK${NC}: $spec (committed: $spec_date)"
    fi
  done

  echo ""
done

echo "=========================================="
echo "Summary"
echo "=========================================="
echo "  Errors:   $errors"
echo "  Warnings: $warnings"

if [[ $errors -gt 0 ]]; then
  echo -e "${RED}FAILED${NC}: Missing spec file references"
  exit 1
fi

if [[ $warnings -gt 0 ]]; then
  if [[ "$STRICT_MODE" == true ]]; then
    echo -e "${RED}FAILED${NC}: Spec files modified after ADR (strict mode)"
    exit 1
  else
    echo -e "${YELLOW}PASSED with warnings${NC}: Consider updating ADRs"
    exit 0
  fi
fi

echo -e "${GREEN}PASSED${NC}: All ADR-spec references are in sync"
exit 0
