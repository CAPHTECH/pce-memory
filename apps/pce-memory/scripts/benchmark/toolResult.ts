import { dispatchTool, type ToolResult } from '../../src/core/handlers.js';

interface ToolErrorShape {
  error?: {
    code?: string;
    message?: string;
  };
}

function getToolFailureMessage(result: ToolResult): string {
  const structured = result.structuredContent as ToolErrorShape | undefined;
  const code = structured?.error?.code ?? 'TOOL_ERROR';
  const message =
    structured?.error?.message ??
    result.content[0]?.text ??
    'tool failed without structuredContent';
  return `${code}: ${message}`;
}

export function unwrapToolResult<T extends Record<string, unknown>>(result: ToolResult): T {
  if (result.isError) {
    throw new Error(getToolFailureMessage(result));
  }
  if (!result.structuredContent) {
    throw new Error('TOOL_ERROR: missing structuredContent');
  }
  return result.structuredContent as T;
}

export async function dispatchToolOrThrow<T extends Record<string, unknown>>(
  name: string,
  args: Record<string, unknown>
): Promise<T> {
  return unwrapToolResult<T>(await dispatchTool(name, args));
}
