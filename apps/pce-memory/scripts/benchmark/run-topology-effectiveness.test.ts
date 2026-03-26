import { describe, expect, it } from 'vitest';
import { existsSync, mkdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import {
  generateTopologyBenchmarkMarkdown,
  runTopologyEffectivenessBenchmark,
} from './topology-effectiveness';

describe('Topology Effectiveness Benchmark', () => {
  it(
    'measures the remaining topology gains under fill-only graph presence',
    async () => {
      const report = await runTopologyEffectivenessBenchmark();

      const repoRoot = join(import.meta.dirname, '../..');
      const resultsDir = join(repoRoot, 'var/benchmark');
      if (!existsSync(resultsDir)) {
        mkdirSync(resultsDir, { recursive: true });
      }

      const stamp = report.generated_at.replace(/[:.]/g, '-');
      const jsonPath = join(resultsDir, `topology-effectiveness-${stamp}.json`);
      const mdPath = join(resultsDir, `topology-effectiveness-${stamp}.md`);

      writeFileSync(jsonPath, JSON.stringify(report, null, 2));
      writeFileSync(mdPath, generateTopologyBenchmarkMarkdown(report));

      console.log(`\nTopology benchmark report: ${mdPath}`);
      console.log(`Topology benchmark data:   ${jsonPath}`);

      expect(report.summary.scenario_count).toBe(3);
      expect(report.summary.improved_recall_scenarios).toBeGreaterThanOrEqual(1);
      expect(report.summary.improved_precision_scenarios).toBeGreaterThanOrEqual(1);

      const claimLink = report.scenarios.find((scenario) => scenario.name === 'claim-link recall');
      const entityBridge = report.scenarios.find((scenario) => scenario.name === 'entity-bridge recall');
      const supersession = report.scenarios.find((scenario) => scenario.name === 'supersession refresh');

      expect(claimLink).toBeDefined();
      expect(entityBridge).toBeDefined();
      expect(supersession).toBeDefined();

      expect(claimLink!.deltas.recall_at_k).toBeGreaterThanOrEqual(0);
      expect(entityBridge!.deltas.recall_at_k).toBeGreaterThanOrEqual(0);
      expect(supersession!.deltas.precision_at_k).toBeGreaterThan(0);
      expect(supersession!.topology.top_claim_labels[0]).toBe('replacement-new');
    },
    120_000
  );
});
