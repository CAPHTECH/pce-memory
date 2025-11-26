/**
 * @pce/embeddings リモート埋め込みプロバイダー
 * ADR-0003: RemoteEmbeddingProvider (フォールバック用)
 *
 * OpenAI Embeddings API互換のエンドポイントをサポート
 */

import * as TE from "fp-ts/TaskEither";
import { pipe } from "fp-ts/function";
import type { EmbeddingProvider, ProviderStatus, RemoteProviderConfig } from "../types.js";
import { MAX_BATCH_SIZE } from "../types.js";
import type { EmbeddingError } from "../errors.js";
import {
  remoteApiError,
  batchSizeExceededError,
  providerUnavailableError,
} from "../errors.js";

// ========== 型定義 ==========

/**
 * OpenAI Embeddings API レスポンス形式
 */
interface EmbeddingsResponse {
  object: "list";
  data: Array<{
    object: "embedding";
    index: number;
    embedding: number[];
  }>;
  model: string;
  usage: {
    prompt_tokens: number;
    total_tokens: number;
  };
}

/**
 * リモートプロバイダー拡張設定
 */
export interface RemoteProviderOptions extends RemoteProviderConfig {
  /** タイムアウト（ミリ秒）。デフォルト: 30000 */
  readonly timeoutMs?: number;
  /** リトライ回数。デフォルト: 2 */
  readonly maxRetries?: number;
  /** リトライ間隔（ミリ秒）。デフォルト: 1000 */
  readonly retryDelayMs?: number;
}

// ========== セキュリティヘルパー ==========

/**
 * エンドポイントURLのセキュリティ検証
 * SSRF攻撃とAPIキー流出を防止
 *
 * @param endpoint 検証対象のエンドポイントURL
 * @throws エンドポイントが安全でない場合
 */
const validateEndpoint = (endpoint: string): void => {
  let url: URL;
  try {
    url = new URL(endpoint);
  } catch {
    throw new Error(`Invalid endpoint URL: ${endpoint}`);
  }

  // プロトコル検証: HTTPSのみ許可（開発時のlocalhost/127.0.0.1は例外）
  const isLocalhost = url.hostname === "localhost" || url.hostname === "127.0.0.1";
  if (url.protocol !== "https:" && !isLocalhost) {
    throw new Error(
      `Insecure endpoint protocol: ${url.protocol}. Only HTTPS is allowed (localhost exempt for development).`
    );
  }

  // 内部ネットワークアドレス検出（SSRF防止）
  // プライベートIP範囲: 10.x.x.x, 172.16-31.x.x, 192.168.x.x
  const hostname = url.hostname;
  const privateIpPatterns = [
    /^10\./,                          // 10.0.0.0/8
    /^172\.(1[6-9]|2[0-9]|3[01])\./,  // 172.16.0.0/12
    /^192\.168\./,                    // 192.168.0.0/16
    /^169\.254\./,                    // リンクローカル
    /^0\./,                           // 0.0.0.0/8
  ];

  // localhost以外でプライベートIPへのアクセスを禁止
  if (!isLocalhost) {
    for (const pattern of privateIpPatterns) {
      if (pattern.test(hostname)) {
        throw new Error(
          `Access to internal network address is not allowed: ${hostname}`
        );
      }
    }
  }
};

/**
 * 埋め込みベクトルの次元検証
 * 悪意あるエンドポイントからの不正データを防止
 *
 * @param embedding 検証対象の埋め込みベクトル
 * @throws 次元数が不正な場合
 */
const validateEmbeddingDimensions = (embedding: number[]): void => {
  if (!Array.isArray(embedding)) {
    throw new Error("Invalid embedding: expected array");
  }
  if (embedding.length === 0) {
    throw new Error("Invalid embedding: empty array");
  }
  // 極端に大きいベクトル（メモリ膨張攻撃防止）は拒否
  // MAX_ALLOWED_DIMENSIONS: OpenAI text-embedding-3-large の上限に合わせる
  const MAX_ALLOWED_DIMENSIONS = 4096;
  if (embedding.length > MAX_ALLOWED_DIMENSIONS) {
    throw new Error(
      `Invalid embedding dimensions: ${embedding.length} exceeds maximum allowed ${MAX_ALLOWED_DIMENSIONS}`
    );
  }
};

// ========== プロバイダー作成 ==========

/**
 * リモート埋め込みプロバイダーを作成
 *
 * OpenAI Embeddings API互換:
 * - POST /embeddings
 * - input: string | string[]
 * - model: string
 *
 * セキュリティ:
 * - HTTPSエンドポイントのみ許可（開発用localhost除く）
 * - 内部ネットワークへのSSRF攻撃を防止
 *
 * @param config プロバイダー設定
 * @returns EmbeddingProvider
 * @throws エンドポイントが安全でない場合
 */
export const createRemoteProvider = (
  config: RemoteProviderOptions
): EmbeddingProvider => {
  const {
    endpoint,
    apiKey,
    model,
    timeoutMs = 30000,
    maxRetries = 2,
    retryDelayMs = 1000,
  } = config;

  // エンドポイントのセキュリティ検証（SSRF/APIキー流出防止）
  validateEndpoint(endpoint);

  let status: ProviderStatus = "available";

  /**
   * API呼び出し
   */
  const callApi = async (
    input: string | readonly string[]
  ): Promise<EmbeddingsResponse> => {
    const controller = new AbortController();
    const timeoutId = setTimeout(() => controller.abort(), timeoutMs);

    try {
      const response = await fetch(`${endpoint}/embeddings`, {
        method: "POST",
        headers: {
          Authorization: `Bearer ${apiKey}`,
          "Content-Type": "application/json",
        },
        body: JSON.stringify({
          input,
          model,
          encoding_format: "float",
        }),
        signal: controller.signal,
      });

      clearTimeout(timeoutId);

      if (!response.ok) {
        // レート制限の場合はdegradedに
        if (response.status === 429) {
          status = "degraded";
        } else if (response.status >= 500) {
          status = "unavailable";
        }
        throw new Error(`API error: ${response.status} ${response.statusText}`);
      }

      status = "available";
      return (await response.json()) as EmbeddingsResponse;
    } catch (e) {
      clearTimeout(timeoutId);
      if (e instanceof Error && e.name === "AbortError") {
        throw new Error(`Request timed out after ${timeoutMs}ms`);
      }
      throw e;
    }
  };

  /**
   * リトライ付きAPI呼び出し
   */
  const callApiWithRetry = async (
    input: string | readonly string[]
  ): Promise<EmbeddingsResponse> => {
    let lastError: Error | null = null;

    for (let attempt = 0; attempt <= maxRetries; attempt++) {
      try {
        return await callApi(input);
      } catch (e) {
        lastError = e instanceof Error ? e : new Error(String(e));

        // 最後の試行でなければリトライ
        if (attempt < maxRetries) {
          await new Promise((resolve) => setTimeout(resolve, retryDelayMs));
        }
      }
    }

    throw lastError ?? new Error("Unknown error");
  };

  return {
    get modelVersion(): string {
      return model;
    },

    get status(): ProviderStatus {
      return status;
    },

    embed: (text: string): TE.TaskEither<EmbeddingError, readonly number[]> =>
      pipe(
        TE.tryCatch(
          async () => {
            const response = await callApiWithRetry(text);
            const first = response.data[0];
            if (!first) {
              throw new Error("Empty response from embedding API");
            }
            // 次元検証（メモリ膨張攻撃防止）
            validateEmbeddingDimensions(first.embedding);
            return first.embedding;
          },
          (e) =>
            remoteApiError(
              e instanceof Error ? e.message : String(e),
              e
            )
        )
      ),

    embedBatch: (
      texts: readonly string[]
    ): TE.TaskEither<EmbeddingError, readonly (readonly number[])[]> => {
      // バッチサイズ制限チェック
      if (texts.length > MAX_BATCH_SIZE) {
        return TE.left(batchSizeExceededError(texts.length, MAX_BATCH_SIZE));
      }

      // 空の配列は即座に空の結果を返す
      if (texts.length === 0) {
        return TE.right([]);
      }

      return pipe(
        TE.tryCatch(
          async () => {
            const response = await callApiWithRetry(texts);
            // indexでソートして元の順序を保持
            const sorted = response.data.sort((a, b) => a.index - b.index);
            // 全ての埋め込みベクトルを検証（メモリ膨張攻撃防止）
            sorted.forEach((d) => validateEmbeddingDimensions(d.embedding));
            return sorted.map((d) => d.embedding);
          },
          (e) =>
            remoteApiError(
              e instanceof Error ? e.message : String(e),
              e
            )
        )
      );
    },
  };
};

/**
 * OpenAI用のリモートプロバイダーを作成
 */
export const createOpenAIProvider = (
  apiKey: string,
  model = "text-embedding-3-small"
): EmbeddingProvider =>
  createRemoteProvider({
    endpoint: "https://api.openai.com/v1",
    apiKey,
    model,
  });

/**
 * Azure OpenAI用のリモートプロバイダーを作成
 */
export const createAzureOpenAIProvider = (
  endpoint: string,
  apiKey: string,
  deploymentName: string
): EmbeddingProvider =>
  createRemoteProvider({
    endpoint: `${endpoint}/openai/deployments/${deploymentName}`,
    apiKey,
    model: deploymentName,
  });

/**
 * 利用不可のスタブプロバイダー（テスト用）
 */
export const createUnavailableProvider = (): EmbeddingProvider => ({
  modelVersion: "unavailable",
  status: "unavailable",

  embed: (): TE.TaskEither<EmbeddingError, readonly number[]> =>
    TE.left(providerUnavailableError("Provider is unavailable")),

  embedBatch: (): TE.TaskEither<EmbeddingError, readonly (readonly number[])[]> =>
    TE.left(providerUnavailableError("Provider is unavailable")),
});
