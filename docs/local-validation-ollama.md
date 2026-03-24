# Local Validation with Ollama

This guide defines a reproducible local validation track for pce-memory architecture experiments using:

- Mac Studio M4 / 128GB RAM
- Ollama
- `qwen3.5:122b-a10b`
- Codex CLI
- Claude Code

It was assembled on **March 24, 2026** using the locally installed CLI help for `ollama 0.17.7`, `codex`, and `claude`.

## Goal

Make architecture validation executable on a single local machine.

This workflow is for:

- checking that a local agent can connect to Ollama
- checking that it can inspect this repository and reason over the design
- running one fixed architecture validation task repeatedly
- storing results in a reusable layout

This workflow is not for:

- comparing Codex vs Claude Code
- claiming parity with frontier hosted models
- productionizing local-model support across every repository workflow

## Supported Setup

| Item        | Requirement                                      |
| ----------- | ------------------------------------------------ |
| Machine     | Mac Studio M4 with 128GB RAM                     |
| Ollama      | `0.17.7` or later                                |
| Local model | `qwen3.5:122b-a10b`                              |
| Codex       | CLI with `--oss --local-provider ollama` support |
| Claude Code | CLI launched through `ollama launch claude`      |

## Required Software

```bash
ollama --version
codex --help
claude --help
```

Ensure the Ollama daemon is running and the model is available:

```bash
ollama serve
ollama pull qwen3.5:122b-a10b
ollama show qwen3.5:122b-a10b
```

## Recommended Environment Variables

| Variable                       | Purpose                                                                                         | Default             |
| ------------------------------ | ----------------------------------------------------------------------------------------------- | ------------------- |
| `LOCAL_VALIDATION_MODEL`       | Model name used by helper scripts                                                               | `qwen3.5:122b-a10b` |
| `LOCAL_VALIDATION_OUTPUT_ROOT` | Root directory for result artifacts, resolved relative to the repository root when not absolute | `validation/local`  |
| `OLLAMA_HOST`                  | Optional alternate Ollama endpoint                                                              | Ollama CLI default  |

Example:

```bash
export LOCAL_VALIDATION_MODEL=qwen3.5:122b-a10b
export LOCAL_VALIDATION_OUTPUT_ROOT="$PWD/validation/local"
```

## Known-Good Launch Recipes

### Codex CLI directly against Ollama

Use Codex's local open-source provider mode:

```bash
codex --oss --local-provider ollama -m qwen3.5:122b-a10b -C "$PWD"
```

Repository wrapper:

```bash
pnpm local:codex
```

### Codex via Ollama launch integration

Ollama 0.17.7 advertises a dedicated Codex integration:

```bash
ollama launch codex --model qwen3.5:122b-a10b -- --sandbox workspace-write -C "$PWD"
```

Use this when you want Ollama-managed integration startup instead of invoking Codex directly.

### Claude Code via Ollama launch integration

Ollama 0.17.7 advertises a dedicated Claude Code integration:

```bash
ollama launch claude --model qwen3.5:122b-a10b
```

Repository wrapper:

```bash
pnpm local:claude
```

For a non-interactive smoke pass:

```bash
ollama launch claude --model qwen3.5:122b-a10b -- -p "Inspect docs/pce-memory-vision.md and summarize the memory layers."
```

## Minimal Validation Protocol

1. Run the preflight checks.

```bash
ollama show "${LOCAL_VALIDATION_MODEL:-qwen3.5:122b-a10b}"
```

2. Run the canonical smoke task with one agent.

```bash
pnpm local:validation:smoke
pnpm local:validation:smoke -- --agent claude
```

3. Inspect the generated artifact directory:

- `summary.md` for the agent answer
- `meta.json` for run metadata
- `prompt.md` for the exact task
- `run.log` for stdout/stderr details

4. If the smoke task succeeds, run one deeper task from `validation/tasks/`.

- `memory-architecture-smoke.md`
- `write-path-distill-check.md`

## Canonical Smoke Task

The canonical smoke task is stored at:

- `validation/tasks/memory-architecture-smoke.md`

It asks the local agent to:

- identify the current memory layers
- explain promotion risks
- explain retrieval risks
- propose concrete validation checks
- cite repository files it used

This is intentionally small enough to rerun multiple times in a day.

## Result Format

Runtime artifacts are written under:

```text
validation/local/<YYYY-MM-DD>/<run-id>/
├── meta.json
├── prompt.md
├── run.log
└── summary.md
```

Suggested metadata fields:

- `agent`
- `model`
- `ollama_version`
- `task_id`
- `run_id`
- `runtime_seconds`
- `success`
- `notes`

The repository includes a checked-in sample artifact at:

- `validation/local/2026-03-24/example-memory-architecture-smoke/`

## Known Limitations

- Tool calling is less reliable than with hosted frontier models. Prefer fixed, narrow prompts for local validation.
- End-to-end latency is high on large architecture prompts. Keep the smoke task small and evidence-oriented.
- Context windows and effective recall can differ from hosted models even with the same task framing.
- Long autonomous runs are more fragile. Favor short passes that emit artifacts after each run.
- A local success only proves the workflow is executable on this machine. It does not prove architectural correctness by itself.

## Troubleshooting

### `ollama show` fails

- Start the daemon with `ollama serve`
- Confirm `OLLAMA_HOST` is correct if you are not using the default endpoint
- Pull the model again with `ollama pull qwen3.5:122b-a10b`

### Codex does not use the local provider

- Ensure `--oss --local-provider ollama` is present
- Confirm the model name matches `ollama list`

### Claude Code launch fails

- Re-run `ollama launch claude --model qwen3.5:122b-a10b`
- Use the helper script so the repository root is the working directory
- Fall back to `--config` on `ollama launch` if you need to reconfigure the integration
