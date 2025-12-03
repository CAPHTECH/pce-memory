/**
 * デーモンシャットダウン関連の定数
 *
 * タイムアウト値の関係:
 *   SOCKET_SHUTDOWN_TIMEOUT_MS < DAEMON_SHUTDOWN_WATCHDOG_MS
 *
 * ソケットシャットダウンが先にタイムアウトし、その後にウォッチドッグが発動する設計。
 */

/**
 * ソケットシャットダウンタイムアウト（ミリ秒）
 * この時間内に全接続がクローズしない場合、残存接続を強制切断する
 */
export const SOCKET_SHUTDOWN_TIMEOUT_MS = 5000;

/**
 * デーモン全体のシャットダウンウォッチドッグタイムアウト（ミリ秒）
 * シャットダウン処理全体がこの時間を超えた場合、強制終了する
 *
 * 必ず SOCKET_SHUTDOWN_TIMEOUT_MS より大きく設定すること
 */
export const DAEMON_SHUTDOWN_WATCHDOG_MS = 10000;

// 定数の関係性を静的に検証（ビルド時にチェック）
if (SOCKET_SHUTDOWN_TIMEOUT_MS >= DAEMON_SHUTDOWN_WATCHDOG_MS) {
  throw new Error(
    `Invalid timeout configuration: SOCKET_SHUTDOWN_TIMEOUT_MS (${SOCKET_SHUTDOWN_TIMEOUT_MS}) ` +
      `must be less than DAEMON_SHUTDOWN_WATCHDOG_MS (${DAEMON_SHUTDOWN_WATCHDOG_MS})`
  );
}
