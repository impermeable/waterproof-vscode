/**
 * The Lean LSP server configuration
 */
export interface LeanLspServerConfig extends Record<string, string | number | boolean> {
}

// TODO: Rewrite namespace to modern syntax
// eslint-disable-next-line @typescript-eslint/no-namespace
export namespace LeanLspServerConfig {
    export function create(): LeanLspServerConfig {
        return {};
    }
}
