/**
 * Daemon Socket Module Unit Tests
 *
 * JSON-RPCソケットサーバーのテスト:
 * - JSON-RPC型定義
 * - リクエスト/レスポンス構造
 */

import { describe, it, expect } from "vitest";

import type {
  JsonRpcRequest,
  JsonRpcResponse,
  SocketServerOptions,
} from "../src/daemon/socket.js";

describe("daemon socket types", () => {
  describe("JsonRpcRequest", () => {
    it("should accept valid request with all fields", () => {
      const request: JsonRpcRequest = {
        jsonrpc: "2.0",
        id: 1,
        method: "test",
        params: { foo: "bar" },
      };

      expect(request.jsonrpc).toBe("2.0");
      expect(request.id).toBe(1);
      expect(request.method).toBe("test");
      expect(request.params).toEqual({ foo: "bar" });
    });

    it("should accept request with string id", () => {
      const request: JsonRpcRequest = {
        jsonrpc: "2.0",
        id: "request-123",
        method: "ping",
      };

      expect(request.id).toBe("request-123");
    });

    it("should accept request without id (notification)", () => {
      const request: JsonRpcRequest = {
        jsonrpc: "2.0",
        method: "notify",
      };

      expect(request.id).toBeUndefined();
    });

    it("should accept request with null id", () => {
      const request: JsonRpcRequest = {
        jsonrpc: "2.0",
        id: null,
        method: "test",
      };

      expect(request.id).toBeNull();
    });
  });

  describe("JsonRpcResponse", () => {
    it("should accept success response", () => {
      const response: JsonRpcResponse = {
        jsonrpc: "2.0",
        id: 1,
        result: { status: "ok" },
      };

      expect(response.jsonrpc).toBe("2.0");
      expect(response.id).toBe(1);
      expect(response.result).toEqual({ status: "ok" });
      expect(response.error).toBeUndefined();
    });

    it("should accept error response", () => {
      const response: JsonRpcResponse = {
        jsonrpc: "2.0",
        id: 1,
        error: {
          code: -32600,
          message: "Invalid Request",
        },
      };

      expect(response.error?.code).toBe(-32600);
      expect(response.error?.message).toBe("Invalid Request");
      expect(response.result).toBeUndefined();
    });

    it("should accept error with data field", () => {
      const response: JsonRpcResponse = {
        jsonrpc: "2.0",
        id: 1,
        error: {
          code: -32603,
          message: "Internal error",
          data: { details: "stack trace" },
        },
      };

      expect(response.error?.data).toEqual({ details: "stack trace" });
    });

    it("should accept response with null id", () => {
      const response: JsonRpcResponse = {
        jsonrpc: "2.0",
        id: null,
        error: {
          code: -32700,
          message: "Parse error",
        },
      };

      expect(response.id).toBeNull();
    });
  });

  describe("JSON-RPC error codes", () => {
    it("should use standard error codes", () => {
      // JSON-RPC 2.0標準エラーコード
      const parseError: JsonRpcResponse = {
        jsonrpc: "2.0",
        id: null,
        error: { code: -32700, message: "Parse error" },
      };
      expect(parseError.error?.code).toBe(-32700);

      const invalidRequest: JsonRpcResponse = {
        jsonrpc: "2.0",
        id: null,
        error: { code: -32600, message: "Invalid Request" },
      };
      expect(invalidRequest.error?.code).toBe(-32600);

      const methodNotFound: JsonRpcResponse = {
        jsonrpc: "2.0",
        id: 1,
        error: { code: -32601, message: "Method not found" },
      };
      expect(methodNotFound.error?.code).toBe(-32601);

      const internalError: JsonRpcResponse = {
        jsonrpc: "2.0",
        id: 1,
        error: { code: -32603, message: "Internal error" },
      };
      expect(internalError.error?.code).toBe(-32603);
    });
  });

  describe("SocketServerOptions", () => {
    it("should define required properties", () => {
      const mockHandler = async () => null;
      const options: SocketServerOptions = {
        socketPath: "/tmp/test.sock",
        onRequest: mockHandler,
      };

      expect(options.socketPath).toBe("/tmp/test.sock");
      expect(typeof options.onRequest).toBe("function");
    });

    it("should allow optional error handler", () => {
      const mockHandler = async () => null;
      const mockErrorHandler = () => {};

      const options: SocketServerOptions = {
        socketPath: "/tmp/test.sock",
        onRequest: mockHandler,
        onError: mockErrorHandler,
      };

      expect(typeof options.onError).toBe("function");
    });
  });
});

describe("JSON-RPC message parsing", () => {
  it("should parse valid JSON-RPC request", () => {
    const json = '{"jsonrpc":"2.0","id":1,"method":"ping"}';
    const parsed = JSON.parse(json) as JsonRpcRequest;

    expect(parsed.jsonrpc).toBe("2.0");
    expect(parsed.id).toBe(1);
    expect(parsed.method).toBe("ping");
  });

  it("should parse request with params", () => {
    const json = '{"jsonrpc":"2.0","id":"abc","method":"tools/call","params":{"name":"test"}}';
    const parsed = JSON.parse(json) as JsonRpcRequest;

    expect(parsed.params).toEqual({ name: "test" });
  });

  it("should serialize response correctly", () => {
    const response: JsonRpcResponse = {
      jsonrpc: "2.0",
      id: 1,
      result: { status: "ok", data: [1, 2, 3] },
    };

    const json = JSON.stringify(response);
    const reparsed = JSON.parse(json);

    expect(reparsed.jsonrpc).toBe("2.0");
    expect(reparsed.id).toBe(1);
    expect(reparsed.result.status).toBe("ok");
    expect(reparsed.result.data).toEqual([1, 2, 3]);
  });
});
