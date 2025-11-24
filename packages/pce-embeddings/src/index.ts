/**
 * @pce/embeddings - Embedding provider abstraction for PCE
 *
 * このパッケージは埋め込みプロバイダーの抽象化を提供します：
 * - EmbeddingProvider interface (プロバイダーインターフェース)
 * - Local embedding support (ローカル埋め込み: BAAI/bge-small-en-v1.5)
 * - Remote embedding support (リモート埋め込み: OpenAI, Anthropic)
 * - Batch processing (バッチ処理)
 * - Caching strategies (キャッシング戦略)
 *
 * @see docs/core-types.md - EmbeddingProvider
 */

// TODO: Export EmbeddingProvider interface
// TODO: Implement LocalEmbeddingProvider (with ONNX runtime)
// TODO: Implement RemoteEmbeddingProvider
// TODO: Implement caching layer

export const PLACEHOLDER = 'pce-embeddings';
