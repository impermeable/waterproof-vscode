import { MessageType } from "../../../../shared";
import { Editor } from "../editor";

/**
 * Creates a context menu given the current editor.
 * @param editor The editor in use.
 * @returns HTMLDivElement storing the context menu element.
 */
export function createContextMenuHTML(editor: Editor): HTMLDivElement {
    // Creating the container elements.
    const divContainer = document.createElement("div");
    const listContainer = document.createElement("ul");

    // We need a time value for sending commands to coq-lsp.
    const date = new Date();

    divContainer.classList.add("context-menu");
    divContainer.style.display = "none";
    listContainer.classList.add("menu");

    // Create a 'Help' button. On execution will send a command to coq-lsp to query for help, 
    // this result is then displayed in a popup within the editor.
    listContainer.appendChild(contextMenuButton("Help", () => {
        editor.post({type: MessageType.command, body: "Help.", time: date.getTime()});
    }));
    
    divContainer.appendChild(listContainer);
    return divContainer;
}

/**
 * Helper function for creating a context menu button.
 * @param buttonName The name of the button to display in the context menu.
 * @param buttonCallback The callback which will be called when the button is pressed.
 * @returns HTMLLiElement representing the button.
 */
function contextMenuButton(buttonName: string, buttonCallback: () => any): HTMLLIElement {
    const element = document.createElement("li");
    element.onclick = buttonCallback;
    element.innerText = buttonName;
    return element;
}

