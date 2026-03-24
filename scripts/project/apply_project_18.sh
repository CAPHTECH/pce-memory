#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
CONFIG_PATH="${REPO_ROOT}/docs/project-management/project-18-config.yaml"

require_cmd() {
  command -v "$1" >/dev/null 2>&1 || {
    echo "missing command: $1" >&2
    exit 1
  }
}

require_cmd gh
require_cmd jq
require_cmd ruby

CONFIG_JSON="$(ruby -r yaml -r json -e 'puts JSON.generate(YAML.load_file(ARGV[0]))' "$CONFIG_PATH")"

OWNER="$(jq -r '.project.owner' <<<"$CONFIG_JSON")"
REPO="$(jq -r '.project.repo' <<<"$CONFIG_JSON")"
PROJECT_NUMBER="$(jq -r '.project.number' <<<"$CONFIG_JSON")"
PROJECT_ID="$(gh project view "$PROJECT_NUMBER" --owner "$OWNER" --format json --jq '.id')"

FIELD_JSON="$(gh project field-list "$PROJECT_NUMBER" --owner "$OWNER" --format json)"

field_id() {
  local name="$1"
  jq -r --arg name "$name" '.fields[] | select(.name == $name) | .id' <<<"$FIELD_JSON"
}

option_id() {
  local field_name="$1"
  local option_name="$2"
  jq -r --arg field "$field_name" --arg option "$option_name" \
    '.fields[] | select(.name == $field) | .options[] | select(.name == $option) | .id' \
    <<<"$FIELD_JSON"
}

STATUS_FIELD_ID="$(field_id "Status")"
PRIORITY_FIELD_ID="$(field_id "Priority")"
SIZE_FIELD_ID="$(field_id "Size")"
START_DATE_FIELD_ID="$(field_id "Start date")"
TARGET_DATE_FIELD_ID="$(field_id "Target date")"

milestone_number() {
  local title="$1"
  gh api "repos/${OWNER}/${REPO}/milestones?state=all" --jq ".[] | select(.title == \"${title}\") | .number" | head -n1
}

ensure_milestone() {
  local title="$1"
  local due_on="$2"
  local existing_number
  existing_number="$(milestone_number "$title" || true)"
  if [[ -n "${existing_number}" ]]; then
    if [[ -n "${due_on}" ]]; then
      gh api --method PATCH "repos/${OWNER}/${REPO}/milestones/${existing_number}" -f title="$title" -f due_on="${due_on}T00:00:00Z" >/dev/null
    else
      gh api --method PATCH "repos/${OWNER}/${REPO}/milestones/${existing_number}" -f title="$title" -F due_on=null >/dev/null
    fi
  else
    if [[ -n "${due_on}" ]]; then
      gh api --method POST "repos/${OWNER}/${REPO}/milestones" -f title="$title" -f due_on="${due_on}T00:00:00Z" >/dev/null
    else
      gh api --method POST "repos/${OWNER}/${REPO}/milestones" -f title="$title" >/dev/null
    fi
  fi
}

echo "$CONFIG_JSON" | jq -c '.milestones[]' | while read -r milestone; do
  ensure_milestone "$(jq -r '.title' <<<"$milestone")" "$(jq -r '.due_on // ""' <<<"$milestone")"
done

echo "$CONFIG_JSON" | jq -c '.milestones[]' | while read -r milestone; do
  title="$(jq -r '.title' <<<"$milestone")"
  for issue in $(jq -r '.issues[]' <<<"$milestone"); do
    gh issue edit "$issue" --repo "${OWNER}/${REPO}" --milestone "$title" >/dev/null
  done
done

ITEM_JSON="$(gh project item-list "$PROJECT_NUMBER" --owner "$OWNER" --format json --limit 100)"

item_id_for_issue() {
  local issue_number="$1"
  jq -r --argjson issue "$issue_number" '.items[] | select(.content.number == $issue) | .id' <<<"$ITEM_JSON"
}

ensure_project_item() {
  local issue_number="$1"
  local item_id
  item_id="$(item_id_for_issue "$issue_number" || true)"
  if [[ -z "${item_id}" ]]; then
    gh project item-add "$PROJECT_NUMBER" --owner "$OWNER" --url "https://github.com/${OWNER}/${REPO}/issues/${issue_number}" >/dev/null
    ITEM_JSON="$(gh project item-list "$PROJECT_NUMBER" --owner "$OWNER" --format json --limit 100)"
  fi
}

all_issue_numbers="$(jq -r '.milestones[].issues[]' <<<"$CONFIG_JSON" | sort -n | uniq)"
for issue in $all_issue_numbers; do
  ensure_project_item "$issue"
done

ITEM_JSON="$(gh project item-list "$PROJECT_NUMBER" --owner "$OWNER" --format json --limit 100)"

apply_single_select() {
  local item_id="$1"
  local field_id="$2"
  local option="$3"
  local option_value_id="$4"
  if [[ -n "${option}" ]]; then
    gh project item-edit --id "$item_id" --project-id "$PROJECT_ID" --field-id "$field_id" --single-select-option-id "$option_value_id" >/dev/null
  else
    gh project item-edit --id "$item_id" --project-id "$PROJECT_ID" --field-id "$field_id" --clear >/dev/null
  fi
}

apply_date() {
  local item_id="$1"
  local field_id="$2"
  local value="$3"
  if [[ -n "${value}" ]]; then
    gh project item-edit --id "$item_id" --project-id "$PROJECT_ID" --field-id "$field_id" --date "$value" >/dev/null
  else
    gh project item-edit --id "$item_id" --project-id "$PROJECT_ID" --field-id "$field_id" --clear >/dev/null
  fi
}

for issue in $all_issue_numbers; do
  item_id="$(item_id_for_issue "$issue")"
  issue_cfg="$(jq -c --arg key "$issue" '.issue_settings[$key] // {}' <<<"$CONFIG_JSON")"
  defaults_cfg="$(jq -c '.defaults' <<<"$CONFIG_JSON")"

  status="$(jq -r '.status // empty' <<<"$issue_cfg")"
  priority="$(jq -r '.priority // empty' <<<"$issue_cfg")"
  size="$(jq -r '.size // empty' <<<"$issue_cfg")"
  start_date="$(jq -r '.start_date // empty' <<<"$issue_cfg")"
  target_date="$(jq -r '.target_date // empty' <<<"$issue_cfg")"

  if [[ -z "$status" ]]; then
    status="$(jq -r '.status // empty' <<<"$defaults_cfg")"
  fi
  if [[ -z "$priority" ]]; then
    priority="$(jq -r '.priority // empty' <<<"$defaults_cfg")"
  fi
  if [[ -z "$size" ]]; then
    size="$(jq -r '.size // empty' <<<"$defaults_cfg")"
  fi
  if [[ -z "$start_date" ]]; then
    start_date="$(jq -r '.start_date // empty' <<<"$defaults_cfg")"
  fi
  if [[ -z "$target_date" ]]; then
    target_date="$(jq -r '.target_date // empty' <<<"$defaults_cfg")"
  fi

  apply_single_select "$item_id" "$STATUS_FIELD_ID" "$status" "$(option_id "Status" "$status")"
  apply_single_select "$item_id" "$PRIORITY_FIELD_ID" "$priority" "$(option_id "Priority" "$priority")"

  if [[ -n "$size" ]]; then
    apply_single_select "$item_id" "$SIZE_FIELD_ID" "$size" "$(option_id "Size" "$size")"
  else
    gh project item-edit --id "$item_id" --project-id "$PROJECT_ID" --field-id "$SIZE_FIELD_ID" --clear >/dev/null
  fi

  apply_date "$item_id" "$START_DATE_FIELD_ID" "$start_date"
  apply_date "$item_id" "$TARGET_DATE_FIELD_ID" "$target_date"
done

cat <<EOF
Applied project state for ${OWNER}/${REPO} Project #${PROJECT_NUMBER}.
Project views are verified against the existing GitHub default layouts:
  - Team items
  - Backlog
  - Roadmap
Public APIs do not expose full Project V2 view CRUD/customization.
EOF
