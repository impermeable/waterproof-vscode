import { TagConfiguration } from "@impermeable/waterproof-editor";

export const tagConfigurationLean: TagConfiguration = {
	code: {
		openTag: "", closeTag: "",
		openRequiresNewline: false, closeRequiresNewline: false
	},
	hint: {
		openTag: (title) => `/- begin details : ${title} -/\n`,
		closeTag: "\n/- end -/",
		openRequiresNewline: true,
		closeRequiresNewline: true,
	},
	input: {
		openTag: "/- begin input -/\n",
		closeTag: "\n/- end -/",
		openRequiresNewline: true,
		closeRequiresNewline: true,
	},
	markdown: {
		openTag: "/-! ",
		closeTag: " -/",
		openRequiresNewline: true,
		closeRequiresNewline: true
	},
	math: {
		openTag: "$", closeTag: "$",
		openRequiresNewline: false, closeRequiresNewline: false,
	}
}