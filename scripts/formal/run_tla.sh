#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$SCRIPT_DIR/../.." && pwd)
WORKDIR="$ROOT/docs/spec/tlaplus"
CACHE="$ROOT/.cache/formal"
JAR="$CACHE/tla2tools.jar"
IMG="eclipse-temurin:21-jre"

# 検証対象の.tlaファイルと対応する.cfgファイル
# 形式: "tlaファイル:cfgファイル"
TLA_SPECS=(
  "pce_memory.tla:${TLA_CFG:-pce_memory.small.cfg}"
  "pce_embedding.tla:pce_embedding.cfg"
  # embedding_failover_comparison は設計Cの問題を示すため、別途実行
)

mkdir -p "$CACHE"

if [[ ! -f $JAR ]]; then
  echo "[TLA+] downloading tla2tools.jar"
  curl -fsSL -o "$JAR" https://github.com/tlaplus/tlaplus/releases/latest/download/tla2tools.jar
fi

run_tla_spec() {
  local spec_cfg="$1"
  local tla_file="${spec_cfg%%:*}"
  local cfg_file="${spec_cfg##*:}"
  local tla_path="$WORKDIR/$tla_file"
  local cfg_path="$WORKDIR/$cfg_file"

  if [[ ! -f "$tla_path" ]]; then
    echo "[TLA+] SKIP: $tla_file (not found)" >&2
    return 0
  fi

  if [[ ! -f "$cfg_path" ]]; then
    echo "[TLA+] SKIP: $tla_file (config $cfg_file not found)" >&2
    return 0
  fi

  echo "[TLA+] checking: $tla_file with $cfg_file"

  if command -v java >/dev/null 2>&1; then
    java -jar "$JAR" -config "$cfg_path" "$tla_path"
  else
    docker run --rm \
      -v "$WORKDIR:/work" \
      -v "$CACHE:/cache" \
      "$IMG" sh -c "java -jar /cache/tla2tools.jar -config /work/$cfg_file /work/$tla_file"
  fi
}

# 全スペックを検証
failed=0
for spec in "${TLA_SPECS[@]}"; do
  if ! run_tla_spec "$spec"; then
    failed=1
  fi
done

if [[ $failed -ne 0 ]]; then
  echo "[TLA+] Some checks failed" >&2
  exit 1
fi

echo "[TLA+] All checks passed"
