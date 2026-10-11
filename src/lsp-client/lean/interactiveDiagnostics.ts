import type {
  InteractiveDiagnostic,
  MsgEmbed,
  TaggedText,
} from "@leanprover/infoview-api";
import type { Range as LspRange, TextEdit } from "vscode-languageserver-types";
import type { MessageSegment, SegmentedDiagnostic } from "../clientTypes";

/**
 * Ids of the Lean widgets that render a clickable "Try this" suggestion inside a message.
 * Core Lean uses them in `Lean.Meta.Hint.mkSuggestionsMessage`, Verbose Lean's `help` uses
 * `textInsertionWidget` with the suggestion text as link text. Both carry the edit in their
 * props as `{ range, suggestion }`.
 */
const SUGGESTION_WIDGET_IDS: Set<string> = new Set([
  "Lean.Meta.Hint.textInsertionWidget",
  "Lean.Meta.Hint.tryThisDiffWidget",
]);

type Embed = MsgEmbed | { [key: string]: unknown };

function isText<T>(t: TaggedText<T>): t is { text: string } {
  return "text" in t;
}

function isAppend<T>(t: TaggedText<T>): t is { append: TaggedText<T>[] } {
  return "append" in t;
}

/** Flattens a tagged text by dropping all tags. Used for `expr` embeds. */
function flattenCode<T>(t: TaggedText<T>): string {
  if (isText(t)) return t.text;
  if (isAppend(t)) return t.append.map(flattenCode).join("");
  return flattenCode(t.tag[1]);
}

/**
 * The text of an embed. An `expr` embed stores its text inside the embed, not in the tagged
 * text it is attached to, and a widget is shown as its `alt` text in the plain message.
 */
function embedText(embed: Embed, inner: TaggedText<MsgEmbed>): string {
  if ("expr" in embed) return flattenCode(embed.expr as TaggedText<unknown>);
  if ("widget" in embed) {
    const widget = embed.widget as { alt: TaggedText<MsgEmbed> };
    return flattenMessage(widget.alt);
  }
  // Goals and traces do not occur in the messages we look at; fall back to the inner text.
  return flattenMessage(inner);
}

/** Flattens an interactive message to the text of the corresponding plain diagnostic. */
export function flattenMessage(t: TaggedText<MsgEmbed>): string {
  if (isText(t)) return t.text;
  if (isAppend(t)) return t.append.map(flattenMessage).join("");
  return embedText(t.tag[0], t.tag[1]);
}

/** Returns the edit of a suggestion widget embed, or `undefined` if the embed is not one. */
function suggestionEdit(embed: Embed): TextEdit | undefined {
  if (!("widget" in embed)) return undefined;
  const { wi } = embed.widget as {
    wi: { id?: string; props?: { range?: LspRange; suggestion?: unknown } };
  };
  if (!wi.id || !SUGGESTION_WIDGET_IDS.has(wi.id)) return undefined;
  const range = wi.props?.range;
  const suggestion = wi.props?.suggestion;
  if (!range || typeof suggestion !== "string") return undefined;
  return { range, newText: suggestion };
}

/**
 * Splits an interactive message into segments, where each suggestion widget becomes a segment
 * with an `edit`. Adjacent plain segments are merged, and empty plain segments are dropped.
 * Concatenating the segment texts gives `flattenMessage(t)`.
 */
export function toSegments(t: TaggedText<MsgEmbed>): MessageSegment[] {
  const segments: MessageSegment[] = [];
  const push = (segment: MessageSegment) => {
    const last = segments[segments.length - 1];
    if (!segment.edit && last && !last.edit) {
      last.text += segment.text;
    } else if (segment.edit || segment.text !== "") {
      segments.push(segment);
    }
  };
  const walk = (node: TaggedText<MsgEmbed>) => {
    if (isText(node)) return push({ text: node.text });
    if (isAppend(node)) return node.append.forEach(walk);
    const [embed, inner] = node.tag;
    const edit = suggestionEdit(embed);
    if (edit) {
      const { alt } = (embed as { widget: { alt: TaggedText<MsgEmbed> } })
        .widget;
      push({ text: flattenMessage(alt), edit });
    } else {
      push({ text: embedText(embed, inner) });
    }
  };
  walk(t);
  return segments;
}

/**
 * Splits the messages of interactive diagnostics into segments, skipping diagnostics without
 * suggestions. The message is flattened, so it equals that of the matching published diagnostic.
 */
export function toSegmentedDiagnostics(
  diagnostics: InteractiveDiagnostic[],
): SegmentedDiagnostic[] {
  const result: SegmentedDiagnostic[] = [];
  for (const d of diagnostics) {
    const segments = toSegments(d.message);
    if (!segments.some((s) => s.edit)) continue;
    result.push({
      range: d.range,
      message: segments.map((s) => s.text).join(""),
      segments,
    });
  }
  return result;
}

/**
 * Collects the RPC references (`{ p: string }`) in a response, so they can be released.
 * Expression embeds carry one per subexpression, and the server keeps them alive until the
 * client releases them or the session ends.
 */
export function collectRpcRefs(value: unknown): { p: string }[] {
  const refs: { p: string }[] = [];
  const walk = (v: unknown) => {
    if (Array.isArray(v)) return v.forEach(walk);
    if (v === null || typeof v !== "object") return;
    const keys = Object.keys(v);
    if (keys.length === 1 && keys[0] === "p") {
      if (typeof (v as { p: unknown }).p === "string")
        refs.push(v as { p: string });
      return;
    }
    Object.values(v).forEach(walk);
  };
  walk(value);
  return refs;
}
