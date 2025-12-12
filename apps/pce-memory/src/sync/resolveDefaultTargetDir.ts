import { execFile } from 'node:child_process';
import * as path from 'node:path';
import { promisify } from 'node:util';
import { DEFAULT_TARGET_DIR } from './schemas.js';

const execFileAsync = promisify(execFile);

const gitRootCache = new Map<string, string>();
const gitRootInFlight = new Map<string, Promise<string | null>>();

async function tryGetGitRoot(cwd: string): Promise<string | null> {
  const resolvedCwd = path.resolve(cwd);

  const cached = gitRootCache.get(resolvedCwd);
  if (cached) {
    return cached;
  }

  const inFlight = gitRootInFlight.get(resolvedCwd);
  if (inFlight) {
    return await inFlight;
  }

  const promise = (async (): Promise<string | null> => {
    try {
      const { stdout } = await execFileAsync('git', ['rev-parse', '--show-toplevel'], {
        cwd: resolvedCwd,
        windowsHide: true,
      });

      const gitRoot = stdout.trim();
      return gitRoot.length > 0 ? gitRoot : null;
    } catch {
      return null;
    }
  })();

  gitRootInFlight.set(resolvedCwd, promise);
  const result = await promise;
  gitRootInFlight.delete(resolvedCwd);

  // 成功時のみキャッシュ（非Git→Gitに変わる可能性を潰さない）
  if (result) {
    gitRootCache.set(resolvedCwd, result);
  }

  return result;
}

export async function resolveDefaultTargetDir(
  basePath: string
): Promise<{ basePath: string; targetDir: string }> {
  const gitRoot = await tryGetGitRoot(basePath);
  if (gitRoot) {
    return { basePath: path.resolve(gitRoot), targetDir: DEFAULT_TARGET_DIR };
  }

  return { basePath, targetDir: DEFAULT_TARGET_DIR };
}
