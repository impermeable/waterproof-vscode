/**
 * The Lean LSP server configuration
 */
export type LeanLspServerConfig = Record<string, string | number | boolean>;

// TODO: Rewrite namespace to modern syntax
// eslint-disable-next-line @typescript-eslint/no-namespace
export namespace LeanLspServerConfig {
  export function create(): LeanLspServerConfig {
    return {
      // Without this, the server strips widgets (such as "Try this" suggestions) from the
      // interactive diagnostics returned by `Lean.Widget.getInteractiveDiagnostics`.
      hasWidgets: true,
    };
  }
}
