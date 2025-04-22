import { WaterproofEditor } from "../editor";

/**
 * Creates a context menu given the current editor.
 * @param editor The editor in use.
 * @returns HTMLDivElement storing the context menu element.
 */
export function createContextMenuHTML(editor: WaterproofEditor): HTMLDivElement {
    // Creating the container elements.
    const divContainer = document.createElement("div");
    const listContainer = document.createElement("ul");

    divContainer.classList.add("context-menu");
    divContainer.style.display = "none";
    listContainer.classList.add("menu");

    // Create a 'Help' button. On execution will send a command to coq-lsp to query for help,
    // this result is then displayed in a popup within the editor.
    listContainer.appendChild(contextMenuButton("?", "Help", () => {
        editor.executeCommand("Help.");
    }));

    listContainer.appendChild(contextMenuButton("X", "Close", () => {}));

    divContainer.appendChild(listContainer);
    return divContainer;
}

/**
 * Helper function for creating a context menu button.
 * @param buttonName The name of the button to display in the context menu.
 * @param buttonCallback The callback which will be called when the button is pressed.
 * @returns HTMLLiElement representing the button.
 */
function contextMenuButton(icon: string, buttonName: string, buttonCallback: () => unknown): HTMLLIElement {
    const element = document.createElement("li");
    // <i aria-hidden="true">?
    const a = document.createElement("a");
    a.onclick = buttonCallback;
    const i = document.createElement("i");
    i.ariaHidden = "true";
    i.innerText = icon;

    const textContent = document.createTextNode(` ${buttonName}`);
    a.appendChild(i);
    a.appendChild(textContent);
    element.appendChild(a);
    return element;
}

