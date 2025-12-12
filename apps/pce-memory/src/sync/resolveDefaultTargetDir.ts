import { execFile } from 'node:child_process';
import * as path from 'node:path';
import { promisify } from 'node:util';
import { DEFAULT_TARGET_DIR } from './schemas.js';

const execFileAsync = promisify(execFile);

async function tryGetGitRoot(cwd: string): Promise<string | null> {
  try {
    const { stdout } = await execFileAsync('git', ['rev-parse', '--show-toplevel'], {
      cwd,
      windowsHide: true,
    });

    const gitRoot = stdout.trim();
    return gitRoot.length > 0 ? gitRoot : null;
  } catch {
    return null;
  }
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
