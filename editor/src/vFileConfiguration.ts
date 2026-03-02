import { TagConfiguration } from "@impermeable/waterproof-editor";

export const tagConfigurationV: TagConfiguration = {
	code: {
		openTag: "", closeTag: "",
		openRequiresNewline: false, closeRequiresNewline: false
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
		closeRequiresNewline: true
	},
	math: {
		openTag: "$", closeTag: "$",
		openRequiresNewline: false, closeRequiresNewline: false,
	}
}