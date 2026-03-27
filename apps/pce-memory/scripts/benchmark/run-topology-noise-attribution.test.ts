import { describe, expect, it } from 'vitest';
import { existsSync, mkdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import {
  generateTopologyNoiseAttributionMarkdown,
  runTopologyNoiseAttributionBenchmark,
} from './topology-noise-attribution';

describe('Topology Noise Attribution Benchmark', () => {
  it('confirms forced graph-presence no longer adds noise beyond natural topology', async () => {
    const report = await runTopologyNoiseAttributionBenchmark();

    const repoRoot = join(import.meta.dirname, '../..');
    const resultsDir = join(repoRoot, 'var/benchmark');
    if (!existsSync(resultsDir)) {
      mkdirSync(resultsDir, { recursive: true });
    }

    const stamp = report.generated_at.replace(/[:.]/g, '-');
    const jsonPath = join(resultsDir, `topology-noise-attribution-${stamp}.json`);
    const mdPath = join(resultsDir, `topology-noise-attribution-${stamp}.md`);

    writeFileSync(jsonPath, JSON.stringify(report, null, 2));
    writeFileSync(mdPath, generateTopologyNoiseAttributionMarkdown(report));

    console.log(`\nTopology noise attribution report: ${mdPath}`);
    console.log(`Topology noise attribution data:   ${jsonPath}`);

    expect(report.summary.scenario_count).toBe(3);
    expect(report.summary.injection_only_noise_scenarios).toBe(0);
    expect(report.summary.natural_noise_scenarios).toBe(0);

    const related = report.scenarios.find(
      (scenario) => scenario.name === 'related injection attribution'
    );
    const hub = report.scenarios.find((scenario) => scenario.name === 'hub injection attribution');
    const twoHop = report.scenarios.find(
      (scenario) => scenario.name === 'two-hop path attribution'
    );

    expect(related).toBeDefined();
    expect(hub).toBeDefined();
    expect(twoHop).toBeDefined();

    expect(related!.topology_natural.precision_at_k).toBe(related!.baseline.precision_at_k);
    expect(related!.forced_noise_labels).toEqual([]);
    expect(related!.injected_only_path_evidence).toEqual([]);
    expect(related!.deltas.injected_vs_natural.precision_at_k).toBe(0);

    expect(hub!.topology_natural.precision_at_k).toBe(hub!.baseline.precision_at_k);
    expect(hub!.forced_noise_labels).toEqual([]);
    expect(hub!.injected_only_path_evidence).toEqual([]);
    expect(hub!.deltas.injected_vs_natural.precision_at_k).toBe(0);

    expect(twoHop!.topology_natural.precision_at_k).toBe(twoHop!.baseline.precision_at_k);
    expect(twoHop!.forced_noise_labels).toEqual([]);
    expect(twoHop!.injected_only_path_evidence).toEqual([]);
    expect(twoHop!.deltas.injected_vs_natural.precision_at_k).toBe(0);
  }, 60_000);
});
