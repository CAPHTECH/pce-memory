import { describe, expect, it } from 'vitest';
import { existsSync, mkdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import {
  generateTopologyNoiseBenchmarkMarkdown,
  runTopologyNoiseBenchmark,
} from './topology-noise';

describe('Topology Noise Benchmark', () => {
  it(
    'verifies that adversarial precision cliffs disappear after graph presence becomes fill-only',
    async () => {
      const report = await runTopologyNoiseBenchmark();

      const repoRoot = join(import.meta.dirname, '../..');
      const resultsDir = join(repoRoot, 'var/benchmark');
      if (!existsSync(resultsDir)) {
        mkdirSync(resultsDir, { recursive: true });
      }

      const stamp = report.generated_at.replace(/[:.]/g, '-');
      const jsonPath = join(resultsDir, `topology-noise-${stamp}.json`);
      const mdPath = join(resultsDir, `topology-noise-${stamp}.md`);

      writeFileSync(jsonPath, JSON.stringify(report, null, 2));
      writeFileSync(mdPath, generateTopologyNoiseBenchmarkMarkdown(report));

      console.log(`\nTopology noise report: ${mdPath}`);
      console.log(`Topology noise data:   ${jsonPath}`);

      expect(report.summary.scenario_count).toBe(3);
      expect(report.summary.sweep_count).toBe(3);
      expect(report.summary.sweep_case_count).toBe(51);
      expect(report.summary.precision_drop_scenarios).toBe(0);
      expect(report.summary.increased_noise_scenarios).toBe(0);
      expect(report.summary.injection_worsened_scenarios).toBe(0);
      expect(report.summary.precision_drop_sweep_cases).toBe(0);
      expect(report.summary.increased_noise_sweep_cases).toBe(0);
      expect(report.summary.injection_worsened_sweep_cases).toBe(0);

      const forced = report.scenarios.find(
        (scenario) => scenario.name === 'forced graph presence replacement risk'
      );
      const hub = report.scenarios.find(
        (scenario) => scenario.name === 'generic hub entity bridge risk'
      );
      const mitigated = report.scenarios.find(
        (scenario) => scenario.name === 'confidence mitigated graph selection'
      );

      expect(forced).toBeDefined();
      expect(hub).toBeDefined();
      expect(mitigated).toBeDefined();

      expect(forced!.deltas.precision_at_k).toBe(0);
      expect(forced!.natural_topology.graph_source_count).toBe(0);
      expect(forced!.injection_deltas.precision_at_k).toBe(0);
      expect(forced!.topology.noise_labels).toEqual([]);

      expect(hub!.deltas.precision_at_k).toBe(0);
      expect(hub!.diagnostics?.['generic_hub_detected']).toBe(true);
      expect(hub!.injection_deltas.precision_at_k).toBe(0);
      expect(hub!.topology.noise_labels).toEqual([]);

      expect(mitigated!.deltas.precision_at_k).toBe(0);
      expect(mitigated!.topology.top_claim_labels).toEqual(mitigated!.baseline.top_claim_labels);
      expect(mitigated!.topology.noise_labels).toEqual(mitigated!.baseline.noise_labels);

      const relatedSweep = report.sweeps.find((sweep) => sweep.name === 'related-star cliff sweep');
      const hubSweep = report.sweeps.find((sweep) => sweep.name === 'generic-hub fanout sweep');
      const twoHopSweep = report.sweeps.find((sweep) => sweep.name === 'two-hop contamination sweep');

      expect(relatedSweep).toBeDefined();
      expect(hubSweep).toBeDefined();
      expect(twoHopSweep).toBeDefined();

      const relatedTop1 = relatedSweep!.cases.find(
        (caseReport) =>
          caseReport.params.top_k === 1 &&
          caseReport.params.confidence === 0.9 &&
          caseReport.params.fanout === 1
      );
      const relatedTop2 = relatedSweep!.cases.find(
        (caseReport) =>
          caseReport.params.top_k === 2 &&
          caseReport.params.confidence === 0.9 &&
          caseReport.params.fanout === 1
      );

      expect(relatedTop1).toBeDefined();
      expect(relatedTop2).toBeDefined();
      expect(relatedTop1!.deltas.precision_at_k).toBeGreaterThanOrEqual(0);
      expect(relatedTop1!.natural_topology.graph_source_count).toBe(0);
      expect(relatedTop1!.topology.graph_source_count).toBe(0);
      expect(relatedTop1!.injection_deltas.precision_at_k).toBe(0);
      expect(relatedTop2!.deltas.precision_at_k).toBe(0);
      expect(relatedTop2!.natural_topology.graph_source_count).toBe(0);
      expect(relatedTop2!.topology.noise_count).toBe(0);
      expect(relatedTop2!.injection_deltas.precision_at_k).toBe(0);

      expect(hubSweep!.summary.increased_noise_cases).toBe(0);
      expect(hubSweep!.summary.injection_worsened_cases).toBe(0);
      expect(hubSweep!.cases.every((caseReport) => caseReport.topology.graph_source_count === 0)).toBe(
        true
      );

      expect(twoHopSweep!.cases.every((caseReport) => caseReport.deltas.precision_at_k === 0)).toBe(true);
      expect(
        twoHopSweep!.cases.every(
          (caseReport) => caseReport.topology.probe_graph_claim_details.length === 0
        )
      ).toBe(true);
    },
    120_000
  );
});
