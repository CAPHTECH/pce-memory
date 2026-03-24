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

MILESTONE_JSON="$(gh api "repos/${OWNER}/${REPO}/milestones?state=all")"
ITEM_JSON="$(gh project item-list "$PROJECT_NUMBER" --owner "$OWNER" --format json --limit 100)"
PROJECT_GRAPHQL_JSON="$(gh api graphql -F org="$OWNER" -F number="$PROJECT_NUMBER" -f query='
query($org: String!, $number: Int!) {
  organization(login: $org) {
    projectV2(number: $number) {
      views(first: 20) {
        nodes {
          name
          layout
          fields(first: 20) {
            nodes {
              ... on ProjectV2Field {
                name
              }
              ... on ProjectV2SingleSelectField {
                name
              }
              ... on ProjectV2IterationField {
                name
              }
            }
          }
          verticalGroupByFields(first: 10) {
            nodes {
              ... on ProjectV2Field {
                name
              }
              ... on ProjectV2SingleSelectField {
                name
              }
              ... on ProjectV2IterationField {
                name
              }
            }
          }
          sortByFields(first: 10) {
            nodes {
              direction
              field {
                ... on ProjectV2Field {
                  name
                }
                ... on ProjectV2SingleSelectField {
                  name
                }
                ... on ProjectV2IterationField {
                  name
                }
              }
            }
          }
        }
      }
      items(first: 100) {
        nodes {
          id
          fieldValues(first: 20) {
            nodes {
              __typename
              ... on ProjectV2ItemFieldSingleSelectValue {
                name
                field {
                  ... on ProjectV2FieldCommon {
                    name
                  }
                }
              }
              ... on ProjectV2ItemFieldDateValue {
                date
                field {
                  ... on ProjectV2FieldCommon {
                    name
                  }
                }
              }
            }
          }
          content {
            ... on Issue {
              number
            }
          }
        }
      }
    }
  }
}')"
ITEM_FIELD_JSON="$(jq '
  .data.organization.projectV2.items.nodes
  | map({
      number: .content.number,
      fields: (
        reduce (.fieldValues.nodes[]?) as $node ({};
          if ($node.field.name? // "") == "" then
            .
          elif $node.__typename == "ProjectV2ItemFieldDateValue" then
            . + {($node.field.name): ($node.date // "")}
          elif $node.__typename == "ProjectV2ItemFieldSingleSelectValue" then
            . + {($node.field.name): ($node.name // "")}
          else
            .
          end
        )
      )
    })
' <<<"$PROJECT_GRAPHQL_JSON")"
VIEW_JSON="$(jq '.data.organization.projectV2.views.nodes' <<<"$PROJECT_GRAPHQL_JSON")"

errors=0

check_eq() {
  local label="$1"
  local expected="$2"
  local actual="$3"
  if [[ "$expected" != "$actual" ]]; then
    echo "mismatch: ${label}: expected='${expected}' actual='${actual}'" >&2
    errors=$((errors + 1))
  fi
}

while read -r milestone; do
  title="$(jq -r '.title' <<<"$milestone")"
  due_on="$(jq -r '.due_on // ""' <<<"$milestone")"
  exists="$(jq -r --arg title "$title" '[.[] | select(.title == $title)] | length' <<<"$MILESTONE_JSON")"
  if [[ "$exists" == "0" ]]; then
    echo "missing milestone: ${title}" >&2
    errors=$((errors + 1))
    continue
  fi
  actual_due="$(jq -r --arg title "$title" '.[] | select(.title == $title) | (.due_on // "")' <<<"$MILESTONE_JSON" | head -n1)"
  if [[ -z "$actual_due" && -n "$due_on" ]]; then
    echo "missing milestone due date: ${title}" >&2
    errors=$((errors + 1))
  fi
  if [[ -n "$due_on" && -n "$actual_due" ]]; then
    check_eq "milestone due_on ${title}" "${due_on}T00:00:00Z" "$actual_due"
  fi
  if [[ -z "$due_on" ]]; then
    check_eq "milestone due_on ${title}" "" "$actual_due"
  fi
done < <(jq -c '.milestones[]' <<<"$CONFIG_JSON")

expected_issue_count="$(jq '[.milestones[].issues[]] | unique | length' <<<"$CONFIG_JSON")"
actual_issue_count="$(jq '.items | length' <<<"$ITEM_JSON")"
if [[ "$actual_issue_count" -lt "$expected_issue_count" ]]; then
  echo "project item count is lower than expected issue count: expected at least ${expected_issue_count}, actual ${actual_issue_count}" >&2
  errors=$((errors + 1))
fi

while read -r view; do
  name="$(jq -r '.name' <<<"$view")"
  layout="$(jq -r '.layout' <<<"$view")"
  actual_view="$(jq -c --arg name "$name" '.[] | select(.name == $name)' <<<"$VIEW_JSON")"
  if [[ -z "$actual_view" ]]; then
    echo "missing project view: ${name}" >&2
    errors=$((errors + 1))
    continue
  fi

  actual_layout="$(jq -r '.layout // ""' <<<"$actual_view")"
  check_eq "view ${name} layout" "$(tr '[:lower:]' '[:upper:]' <<<"${layout}")_LAYOUT" "$actual_layout"

  while read -r required_field; do
    if [[ -z "$required_field" ]]; then
      continue
    fi
    has_field="$(jq -r --arg field "$required_field" '[.fields.nodes[] | select(.name == $field)] | length' <<<"$actual_view")"
    if [[ "$has_field" == "0" ]]; then
      echo "view ${name} missing field: ${required_field}" >&2
      errors=$((errors + 1))
    fi
  done < <(jq -r '.required_fields[]? // empty' <<<"$view")

  vertical_group_by="$(jq -r '.vertical_group_by // ""' <<<"$view")"
  if [[ -n "$vertical_group_by" ]]; then
    has_vertical_group="$(jq -r --arg field "$vertical_group_by" '[.verticalGroupByFields.nodes[] | select(.name == $field)] | length' <<<"$actual_view")"
    if [[ "$has_vertical_group" == "0" ]]; then
      echo "view ${name} missing vertical group by: ${vertical_group_by}" >&2
      errors=$((errors + 1))
    fi
  fi

  while read -r sort_rule; do
    if [[ -z "$sort_rule" ]]; then
      continue
    fi
    field_name="${sort_rule% asc}"
    expected_direction="ASC"
    has_sort="$(jq -r --arg field "$field_name" --arg dir "$expected_direction" '[.sortByFields.nodes[] | select(.field.name == $field and .direction == $dir)] | length' <<<"$actual_view")"
    if [[ "$has_sort" == "0" ]]; then
      echo "view ${name} missing sort rule: ${sort_rule}" >&2
      errors=$((errors + 1))
    fi
  done < <(jq -r '.sort[]? // empty' <<<"$view")
done < <(jq -c '.views[]' <<<"$CONFIG_JSON")

while IFS=$'\t' read -r issue title status priority size start_date target_date; do
  actual_milestone="$(gh issue view "$issue" --repo "${OWNER}/${REPO}" --json milestone --jq '.milestone.title // ""')"
  check_eq "issue ${issue} milestone" "$title" "$actual_milestone"

  item="$(jq -c --argjson issue "$issue" '.items[] | select(.content.number == $issue)' <<<"$ITEM_JSON")"
  if [[ -z "$item" ]]; then
    echo "missing project item for issue ${issue}" >&2
    errors=$((errors + 1))
    continue
  fi

  actual_status="$(jq -r --argjson issue "$issue" '.[] | select(.number == $issue) | .fields["Status"] // ""' <<<"$ITEM_FIELD_JSON")"
  check_eq "issue ${issue} status" "$status" "$actual_status"

  actual_priority="$(jq -r --argjson issue "$issue" '.[] | select(.number == $issue) | .fields["Priority"] // ""' <<<"$ITEM_FIELD_JSON")"
  check_eq "issue ${issue} priority" "$priority" "$actual_priority"

  actual_size="$(jq -r --argjson issue "$issue" '.[] | select(.number == $issue) | .fields["Size"] // ""' <<<"$ITEM_FIELD_JSON")"
  check_eq "issue ${issue} size" "$size" "$actual_size"

  actual_start_date="$(jq -r --argjson issue "$issue" '.[] | select(.number == $issue) | .fields["Start date"] // ""' <<<"$ITEM_FIELD_JSON")"
  check_eq "issue ${issue} start_date" "$start_date" "$actual_start_date"

  actual_target_date="$(jq -r --argjson issue "$issue" '.[] | select(.number == $issue) | .fields["Target date"] // ""' <<<"$ITEM_FIELD_JSON")"
  check_eq "issue ${issue} target_date" "$target_date" "$actual_target_date"
done < <(
  jq -r '
    def issue_numbers:
      [ .milestones[].issues[] | tostring ] | unique | sort_by(tonumber);
    def milestone_for($issue):
      [ .milestones[] | select(.issues | index(($issue | tonumber))) | .title ][0];
    def merged_settings($issue):
      (.issue_settings[$issue] // {}) as $cfg
      | .defaults as $d
      | {
          status: ($cfg.status // $d.status // ""),
          priority: ($cfg.priority // $d.priority // ""),
          size: ($cfg.size // $d.size // ""),
          start_date: ($cfg.start_date // $d.start_date // ""),
          target_date: ($cfg.target_date // $d.target_date // "")
        };
    issue_numbers[] as $issue
    | merged_settings($issue) as $merged
    | [
        $issue,
        milestone_for($issue),
        $merged.status,
        $merged.priority,
        $merged.size,
        $merged.start_date,
        $merged.target_date
      ]
    | @tsv
  ' <<<"$CONFIG_JSON"
)

if [[ "$errors" -ne 0 ]]; then
  echo "verification failed with ${errors} error(s)" >&2
  exit 1
fi

echo "project verification passed for ${OWNER}/${REPO} Project #${PROJECT_NUMBER}"
