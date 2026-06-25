import {
  Code2ProtocolConverter,
  Protocol2CodeConverter,
} from "vscode-languageclient";
import { LeanDiagnostic, LeanTag } from "./requestTypes";
import { Diagnostic } from "vscode";
import * as code from "vscode";

import * as async from "vscode-languageclient/lib/common/utils/async";

/**
 * Preserve Lean-specific diagnostic fields (e.g. leanTags) during protocol<->code conversion.
 * Vscode does not preserve them on its own.
 * Inspired by the lean4 vscode extension's approach:
 * https://github.com/leanprover/vscode-lean4/blob/17d1d086d9cce16f885dde102adb056cad15cb50/vscode-lean4/src/utils/converters.ts
 */
export function patchDiagnosticConverters(
  p2c: Protocol2CodeConverter,
  c2p: Code2ProtocolConverter,
): void {
  const origP2c = p2c.asDiagnostic.bind(p2c);
  p2c.asDiagnostic = (protDiag: LeanDiagnostic) => {
    if (!protDiag.message) {
      // Fixes: Notification handler 'textDocument/publishDiagnostics' failed with message: message must be set
      protDiag.message = " ";
    }
    const diag = origP2c(protDiag) as LeanDiagnostic;
    diag.fullRange = p2c.asRange(protDiag.fullRange);
    diag.leanTags = protDiag.leanTags;
    diag.isSilent = protDiag.isSilent;
    return diag as Diagnostic;
  };
  p2c.asDiagnostics = async (diags, token) =>
    async.map(diags, (d) => p2c.asDiagnostic(d), token);

  const origC2p = c2p.asDiagnostic.bind(c2p);
  c2p.asDiagnostic = (
    diag: Diagnostic & {
      fullRange?: code.Range;
      isSilent?: boolean;
      leanTags?: LeanTag[];
    },
  ) => {
    const leanDiag = diag;
    const protDiag = origC2p(diag) as LeanDiagnostic;
    protDiag.fullRange = c2p.asRange(leanDiag.fullRange) ?? undefined;
    protDiag.leanTags = leanDiag.leanTags;
    protDiag.isSilent = leanDiag.isSilent;
    return protDiag;
  };
  c2p.asDiagnostics = async (diags: Diagnostic[]) =>
    async.map(diags, (d) => c2p.asDiagnostic(d));
}
