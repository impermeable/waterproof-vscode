import { TagConfiguration } from "@impermeable/waterproof-editor";

export const tagConfigurationV: TagConfiguration = {
  code: {
    openTag: "",
    closeTag: "",
    openRequiresNewline: true,
    closeRequiresNewline: true,
  },
  hint: {
    openTag: (title) => `(* begin details : ${title} *)\n`,
    closeTag: "\n(* end details *)",
    openRequiresNewline: true,
    closeRequiresNewline: true,
  },
  input: {
    openTag: "(* begin input *)\n",
    closeTag: "\n(* end input *)",
    openRequiresNewline: true,
    closeRequiresNewline: true,
  },
  markdown: {
    openTag: "(** ",
    closeTag: " *)",
    openRequiresNewline: true,
    closeRequiresNewline: true,
  },
  math: {
    openTag: "$",
    closeTag: "$",
    openRequiresNewline: false,
    closeRequiresNewline: false,
  },
  container: {
    openTag: (_name: string) => "",
    closeTag: "",
    openRequiresNewline: false,
    closeRequiresNewline: false,
  },
  // Rocq has no student-hidden syntax yet; placeholder tags for when it does.
  studentHidden: {
    openTag: "<student-hidden>",
    closeTag: "</student-hidden>",
    openRequiresNewline: false,
    closeRequiresNewline: false,
  },
};
