import { TagConfiguration } from "@impermeable/waterproof-editor";

export const tagConfigurationLean: TagConfiguration = {
	code: {
		openTag: "```lean\n", closeTag: "\n```",
		openRequiresNewline: true, closeRequiresNewline: true
	},
	hint: {
		openTag: (title) => `:::hint ${title}\n`,
		closeTag: "\n:::",
		openRequiresNewline: true,
		closeRequiresNewline: true,
	},
	input: {
		openTag: "-- begin input\n",
		closeTag: "\n-- end input",
		openRequiresNewline: true,
		closeRequiresNewline: true,
	},
	markdown: {
		openTag: "",
		closeTag: "",
		openRequiresNewline: false,
		closeRequiresNewline: false
	},
	math: {
		openTag: "$$`", closeTag: "`",
		openRequiresNewline: false, closeRequiresNewline: false,
	}
}