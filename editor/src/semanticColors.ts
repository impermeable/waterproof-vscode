import { ThemeStyle } from "@impermeable/waterproof-editor";

export type SemanticColorMap = Record<string, string>;

const darkColors: SemanticColorMap = {
    "--wp-semanticKeyword":       "#7aa2f7",
    "--wp-semanticFunction":      "#e0af68",
    "--wp-semanticType":          "#2ac3de",
    "--wp-semanticVariable":      "#e8c574",
    "--wp-semanticProperty":      "#73daca",
    "--wp-semanticLiteral":       "#9ece6a",
    "--wp-semanticComment":       "#565f89",
    "--wp-semanticLeanSorryLike": "#f7768e",
};

const lightColors: SemanticColorMap = {
    "--wp-semanticKeyword":       "#0033b3",
    "--wp-semanticFunction":      "#795e26",
    "--wp-semanticType":          "#267f99",
    "--wp-semanticVariable":      "#9b6800",
    "--wp-semanticProperty":      "#0070c1",
    "--wp-semanticLiteral":       "#098658",
    "--wp-semanticComment":       "#6a9955",
    "--wp-semanticLeanSorryLike": "#cd3131",
};

export function getSemanticColors(theme: ThemeStyle): SemanticColorMap {
    return theme === ThemeStyle.Dark ? darkColors : lightColors;
}
