import { ServerStatus } from "@impermeable/waterproof-editor";
import {
    Position,
    Range,
    VersionedTextDocumentIdentifier,
} from "vscode-languageserver-types";

export interface Hyp<Pp> {
    names: Pp[];
    def?: Pp;
    ty: Pp;
}

export interface Goal<Pp> {
    ty: Pp;
    hyps: Hyp<Pp>[];
}

export interface GoalConfig<Pp> {
    goals: Goal<Pp>[];
    stack: [Goal<Pp>[], Goal<Pp>[]][];
    bullet?: Pp;
    shelf: Goal<Pp>[];
    given_up: Goal<Pp>[];
}

export interface Message<Pp> {
    range?: Range;
    level: number;
    text: Pp;
}

export type Id = ["Id", string];

export interface Loc {
    fname: unknown;
    line_nb: number;
    bol_pos: number;
    line_nb_last: number;
    bol_pos_last: number;
    bp: number;
    ep: number;
}

export interface Obl {
    name: Id;
    loc?: Loc;
    status: [boolean, unknown];
    solved: boolean;
}

export interface OblsView {
    opaque: boolean;
    remaining: number;
    obligations: Obl[];
}

export type ProgramInfo = [Id, OblsView][];

export interface GoalAnswer {
    textDocument: VersionedTextDocumentIdentifier;
    position: Position;
}

export interface CoqGoalAnswer<Pp> extends GoalAnswer {
    goals?: GoalConfig<Pp>;
    program?: ProgramInfo;
    messages: Pp[] | Message<Pp>[];
    error?: Pp;
}

export interface LeanGoalAnswer extends GoalAnswer {
    rendered: string;
    goals: string[];
}

export interface GoalRequest {
    textDocument: VersionedTextDocumentIdentifier;
    position: Position;
}

export interface CoqGoalRequest extends GoalRequest {
    pp_format?: "Pp" | "Str";
    command?: string;
    mode?: 'Prev' | 'After';
}

export type LeanGoalRequest = GoalRequest

export type Pp =
    | ["Pp_empty"]
    | ["Pp_string", string]
    | ["Pp_glue", Pp[]]
    | ["Pp_box", unknown, Pp]
    | ["Pp_tag", unknown, Pp]
    | ["Pp_print_break", number, number]
    | ["Pp_force_newline"]
    | ["Pp_comment", string[]];

export type PpString = Pp | string;

export function ppStringIsPp(obj: PpString): obj is Pp {
    return Array.isArray(obj);
}

export function isMessage(obj: Message<PpString> | PpString): obj is Message<PpString> {
    return (typeof obj === "object" && "level" in obj);
}

/**
 * Quick and dirty utility function to convert a pretty-printing object into a plain string.
 */
export function convertToString(pp: PpString): string {
    if (typeof pp === "string") return pp;
    switch (pp[0]) {
        case "Pp_empty":
        case "Pp_comment":
                return "";
        case "Pp_string":
            return pp[1];
        case "Pp_glue":
            return pp[1].map(convertToString).join("");
        case "Pp_box":
        case "Pp_tag":
            return convertToString(pp[2]);
        case "Pp_print_break":
            return " ";
        case "Pp_force_newline":
            return "\n";
    }
}

export interface FlecheDocumentParams {
    textDocument: VersionedTextDocumentIdentifier;
}

// Status of the document, Yes if fully checked, range contains the last seen lexical token
interface CompletionStatus {
    status: ["Yes" | "Stopped" | "Failed"];
    range: Range;
}

// Implementation-specific span information, for now the serialized Ast if present.
type SpanInfo = unknown;

interface RangedSpan {
    range: Range;
    span?: SpanInfo;
}

export interface FlecheDocument {
    spans: RangedSpan[];
    completed: CompletionStatus;
}

export interface FlecheSaveParams {
    textDocument: VersionedTextDocumentIdentifier;
}

export interface SentencePerfParams {
    loc: Loc;
    time: number;
    mem: number;
}

export interface DocumentPerfParams {
    summary: string;
    timings: SentencePerfParams[];
}

export interface CoqBusyStatus {
    status: "Busy";
    modname: string;
}

export interface CoqIdleStatus {
    status: "Idle" | "Stopped";
}

export type CoqServerStatus = CoqBusyStatus | CoqIdleStatus;

function isBusyStatus(status: CoqServerStatus): status is CoqBusyStatus {
    return status.status === "Busy";
}

export function CoqServerStatusToServerStatus(status: CoqServerStatus): ServerStatus {
    if (isBusyStatus(status)) {
        return { status: status.status, metadata: status.modname };
    }
    return status;
}

export enum HypVisibility {
  All = "all",
  Limited = "limited",
  None = "none"
}

