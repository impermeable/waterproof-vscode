let currentTheme: "light" | "dark" = "light";

export function setCurrentTheme(theme: "light" | "dark") {
	currentTheme = theme;
}

export function getCurrentTheme(): "light" | "dark" {
	return currentTheme;
}
