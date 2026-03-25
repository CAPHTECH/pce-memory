/**
 * Deterministic synthetic claim generator for scalability benchmarks.
 *
 * Generates noise claims alongside the golden TEST_CLAIMS to measure
 * how search quality degrades as the corpus grows.
 */

import { TEST_CLAIMS } from '../../assay/test-data.ts';

export interface SyntheticClaim {
  id: string;
  text: string;
  kind: 'fact' | 'preference' | 'task' | 'policy_hint';
  scope: 'session' | 'project' | 'principle';
  boundary_class: 'public' | 'internal';
  content_hash: string;
  provenance: { at: string; actor: string; note: string };
}

const CATEGORIES: Array<{
  kind: SyntheticClaim['kind'];
  scope: SyntheticClaim['scope'];
  templates: string[];
}> = [
  {
    kind: 'fact',
    scope: 'project',
    templates: [
      '{tech}を使用してデータのシリアライゼーションを行う',
      '{tech}でAPIのバージョニングを管理する',
      '{tech}をCI/CDパイプラインのオーケストレーションに採用した',
      '{tech}でログの集約と分析を行う',
      '{tech}をメッセージキューとして使用する',
    ],
  },
  {
    kind: 'preference',
    scope: 'project',
    templates: [
      'コードフォーマッタとして{tech}を使用する',
      '{tech}スタイルのディレクトリ構成を好む',
      'デプロイ手法として{tech}ベースのアプローチを採用する',
      '{tech}のコーディング規約に従う',
      'ドキュメント生成に{tech}を使用する',
    ],
  },
  {
    kind: 'task',
    scope: 'session',
    templates: [
      '{tech}の設定ファイルを最適化する作業中',
      '{tech}へのマイグレーション計画を策定中',
      '{tech}のパフォーマンスチューニングを実施予定',
      '{tech}のセキュリティアップデートを適用する',
      '{tech}の統合テストを追加する',
    ],
  },
  {
    kind: 'policy_hint',
    scope: 'principle',
    templates: [
      '{tech}を使用する際は最新のセキュリティパッチを適用すること',
      '{tech}のAPIキーは環境変数で管理すること',
      '{tech}の本番デプロイは承認フローを経ること',
      '{tech}のバージョンはlockfileで固定すること',
      '{tech}のエラーログは構造化形式で出力すること',
    ],
  },
  {
    kind: 'fact',
    scope: 'principle',
    templates: [
      '{tech}はマイクロサービス間通信に適している',
      '{tech}はイベントソーシングパターンに適合する',
      '{tech}はCQRSアーキテクチャの読み取り側に使える',
      '{tech}はサーキットブレーカーパターンを実装できる',
      '{tech}はバルクヘッドパターンでリソースを分離する',
    ],
  },
];

const TECHNOLOGIES = [
  'Redis', 'PostgreSQL', 'MongoDB', 'Kafka', 'RabbitMQ',
  'GraphQL', 'gRPC', 'Terraform', 'Docker', 'Kubernetes',
  'Prometheus', 'Grafana', 'Elasticsearch', 'Nginx', 'Envoy',
  'Next.js', 'Remix', 'Astro', 'SvelteKit', 'Nuxt',
  'Prisma', 'Drizzle', 'TypeORM', 'Zod', 'tRPC',
  'Vite', 'esbuild', 'Turbopack', 'Biome', 'oxlint',
  'Playwright', 'Cypress', 'Storybook', 'Chromatic', 'Ladle',
  'OpenTelemetry', 'Jaeger', 'Datadog', 'PagerDuty', 'Sentry',
  'Auth0', 'Clerk', 'Supabase', 'Firebase', 'Neon',
  'Cloudflare', 'Vercel', 'Fly.io', 'Railway', 'Render',
];

/**
 * Generate `count` synthetic claims (deterministic).
 * The golden TEST_CLAIMS are always prepended.
 */
export function generateClaims(count: number): SyntheticClaim[] {
  const golden: SyntheticClaim[] = TEST_CLAIMS.map((c) => ({
    id: c.id,
    text: c.text,
    kind: c.kind as SyntheticClaim['kind'],
    scope: c.scope as SyntheticClaim['scope'],
    boundary_class: (c.boundary_class === 'pii' || c.boundary_class === 'secret'
      ? 'internal'
      : c.boundary_class) as 'public' | 'internal',
    content_hash: c.content_hash,
    provenance: c.provenance,
  }));

  if (count <= golden.length) return golden.slice(0, count);

  const syntheticCount = count - golden.length;
  const synthetic: SyntheticClaim[] = [];

  for (let i = 0; i < syntheticCount; i++) {
    const cat = CATEGORIES[i % CATEGORIES.length]!;
    const template = cat.templates[Math.floor(i / CATEGORIES.length) % cat.templates.length]!;
    const tech = TECHNOLOGIES[i % TECHNOLOGIES.length]!;
    const text = template.replace('{tech}', tech);

    synthetic.push({
      id: `synth-${String(i).padStart(5, '0')}`,
      text,
      kind: cat.kind,
      scope: cat.scope,
      boundary_class: 'internal',
      content_hash: `sha256:synth-${i}`,
      provenance: {
        at: new Date(Date.UTC(2024, 0, 15) + i * 3600_000).toISOString(),
        actor: '',
        note: '',
      },
    });
  }

  return [...golden, ...synthetic];
}
