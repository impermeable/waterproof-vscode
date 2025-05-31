import { selectParentNode, wrapIn } from "prosemirror-commands";
import { Schema } from "prosemirror-model";
import { Command, PluginView, Plugin, PluginKey } from "prosemirror-state";
import { EditorView } from "prosemirror-view";
import { INPUT_AREA_PLUGIN_KEY } from "../inputArea";
import { cmdInsertCode, cmdInsertLatex, cmdInsertMarkdown, InsertionPlace, liftWrapper } from "../commands";
import { OS } from "../osType";
import { FileFormat } from "../../../../shared";

/** MenuEntry type contains the DOM, whether to only show it in teacher mode and the command to execute on click */
type MenuEntry = {
    dom: HTMLElement;
    teacherModeOnly: boolean;
    cmd: Command;
};

/**
 * Create a new `MenuButton` type.
 * @param displayedText The text displayed on the button (can be HTML).
 * @param tooltipText The tooltip to show when hovering over this button.
 * @param cmd The command to execute when this button is pressed.
 * @param teacherModeOnly [`false` by default] Whether this button should only be available in teacher mode.
 * @returns A new `MenuButton` object.
 */
function createMenuItem(displayedText: string, tooltipText: string, cmd: Command, teacherModeOnly: boolean = false): MenuEntry {
    // Create the DOM element.
    const menuItem = document.createElement("div");
    // Set the displayed text and the tooltip.
    menuItem.innerHTML = displayedText;
    menuItem.title = tooltipText;
    // Add the class for styling this menubar item
    menuItem.classList.add("menubar-item");
    // Return the new item.
    return {cmd, dom: menuItem, teacherModeOnly};
}

/**
 * Class implementing a prosemirror `PluginView`.
 * Shows menubar above the prosemirror editor.
 */
class MenuView implements PluginView {
    items: MenuEntry[];
    view: EditorView;
    public menubarDOM: HTMLElement;

    constructor(items: MenuEntry[], view: EditorView) {
        this.items = items;
        this.view = view;

        // Create menubar dom container.
        this.menubarDOM = document.createElement("div");
        this.menubarDOM.classList.add("menubar");

        for(const item of items) {
            // Append the menu item to the menubar DOM element.
            item.dom.style.width = "40px"
            this.menubarDOM.appendChild(item.dom);
        }

        // Update the view
        this.update(view);

        // Add event listeners to every menubar item
        this.menubarDOM.addEventListener("mousedown", (event) => {
            // Get the target DOM Node.
            const mouseTarget = event.target as Node;
            // Prevent default behaviour.
            event.preventDefault();

            view.focus();

            // Add the correct callback to all the items.
            for(const item of items) {
                if (item.dom.contains(mouseTarget)) {
                    // This item was clicked, execute the command and update this view.
                    item.cmd(view.state, view.dispatch, view);
                    this.update(view);
                }
            }
            this.update(view);
        });
    }

    update(view: EditorView) {
        // Whether we are currently in teacher mode.
        const inTeacherMode = MENU_PLUGIN_KEY.getState(view.state)?.teacher;

        for(const item of this.items) {
            const active = item.cmd(this.view.state, undefined, this.view);
            /* From https://prosemirror.net/examples/menu/
            "To update the menu for a new state, all commands are run without dispatch function,
            and the items for those that return false are hidden."
            */
            // Instead of hiding the item we set the opacity to something low
            item.dom.style.opacity = active ? "1" : "0.4";
            // And make it unclickable.
            item.dom.setAttribute("disabled", (!active).toString());

            // We hide the item (set display to none) if it should only be available in teacher mode
            // and the user is not in teacher mode.
            if (item.teacherModeOnly && !inTeacherMode) {
                item.dom.style.display = "none";
            }
        }
    }

    destroy() {
        // On destroy remove the dom node.
        this.menubarDOM.remove();
    }
}

/*
    LaTeX logo svg
    https://commons.wikimedia.org/wiki/File:LaTeX_logo.svg
*/
const LaTeX_SVG = `<svg viewBox="0 0 1200 500" xmlns="http://www.w3.org/2000/svg">
<path d="m5.46 4.23h-.25c-.1 1.02-.24 2.26-2 2.26h-.81c-.47 0-.49-.07-.49-.4v-5.31c0-.34 0-.48.94-.48h.33v-.3c-.36.03-1.26.03-1.67.03-.39 0-1.17 0-1.51-.03v.3h.23c.77 0 .79.11.79.47v5.25c0 .36-.02.47-.79.47h-.23v.31h5.19z" transform="matrix(45 0 0 45 40 47.65)"/>
<path d="m2.81.16c-.04-.12-.06-.16-.19-.16s-.16.04-.2.16l-1.61 4.08c-.07.17-.19.48-.81.48v.25h1.55v-.25c-.31 0-.5-.14-.5-.34 0-.05.01-.07.03-.14 0 0 .34-.86.34-.86h1.98l.4 1.02c.02.04.04.09.04.12 0 .2-.38.2-.57.2v.25h1.97v-.25h-.14c-.47 0-.52-.07-.59-.27 0 0-1.7-4.29-1.7-4.29zm-.4.71.89 2.26h-1.78z" transform="matrix(45 0 0 45 151.6 40)"/>
<path d="m6.27 0h-6.09s-.18 2.24-.18 2.24h.24c.14-1.61.29-1.94 1.8-1.94.18 0 .44 0 .54.02.21.04.21.15.21.38v5.25c0 .34 0 .48-1.05.48h-.4v.31c.41-.03 1.42-.03 1.88-.03s1.49 0 1.9.03v-.31h-.4c-1.05 0-1.05-.14-1.05-.48v-5.25c0-.2 0-.34.18-.38.11-.02.38-.02.57-.02 1.5 0 1.65.33 1.79 1.94h.25s-.19-2.24-.19-2.24z" transform="matrix(45 0 0 45 356.35 50.35)"/>
<path d="m6.16 4.2h-.25c-.25 1.53-.48 2.26-2.19 2.26h-1.32c-.47 0-.49-.07-.49-.4v-2.66h.89c.97 0 1.08.32 1.08 1.17h.25v-2.64h-.25c0 .85-.11 1.16-1.08 1.16h-.89v-2.39c0-.33.02-.4.49-.4h1.28c1.53 0 1.79.55 1.95 1.94h.25l-.28-2.24h-5.6v.3h.23c.77 0 .79.11.79.47v5.22c0 .36-.02.47-.79.47h-.23v.31h5.74z" transform="matrix(45 0 0 45 602.5 150.25)"/>
<path d="m3.76 2.95 1.37-2c.21-.32.55-.64 1.44-.65v-.3h-2.38v.3c.4.01.62.23.62.46 0 .1-.02.12-.09.23 0 0-1.14 1.68-1.14 1.68l-1.28-1.92c-.02-.03-.07-.11-.07-.15 0-.12.22-.29.64-.3v-.3c-.34.03-1.07.03-1.45.03-.31 0-.93-.01-1.3-.03v.3h.19c.55 0 .74.07.93.35 0 0 1.83 2.77 1.83 2.77l-1.63 2.41c-.14.2-.44.66-1.44.66v.31h2.38v-.31c-.46-.01-.63-.28-.63-.46 0-.09.03-.13.1-.24l1.41-2.09 1.58 2.38c.02.04.05.08.05.11 0 .12-.22.29-.65.3v.31c.35-.03 1.08-.03 1.45-.03.42 0 .88.01 1.3.03v-.31h-.19c-.52 0-.73-.05-.94-.36 0 0-2.1-3.18-2.1-3.18z" transform="matrix(45 0 0 45 845.95 47.65)"/>
</svg>`

/** If set to `true`, the menubar will display debug buttons.*/
const DEBUG = false;

/**
 * Creates the default menu bar.
 * @param schema The schema in use for the editor.
 * @param outerView The outer (prosemirror)editor.
 * @param filef The file format of the current file. Some commands will behave differently in `.mv` vs `.v` context.
 * @returns A new `MenuView` filled with default menu items.
 */
function createDefaultMenu(schema: Schema, outerView: EditorView, filef: FileFormat, os: OS): MenuView {

    // Platform specific keybinding string:
    const cmdOrCtrl = os == OS.MacOS ? "Cmd" : "Ctrl";
    const keyBinding = (key: string): string => `${cmdOrCtrl}-${key}`;

    // Create the list of menu entries.
    const items: MenuEntry[] = [
        // Insert Coq command
        createMenuItem("Math↓", `Insert new verified math block underneath (${keyBinding("q")})`, cmdInsertCode(filef, InsertionPlace.Underneath), false),
        createMenuItem("Math↑", `Insert new verified math block above (${keyBinding("Q")})`, cmdInsertCode(filef, InsertionPlace.Above), false),
        // Insert Markdown
        createMenuItem("Text↓", `Insert new text block underneath (${keyBinding("m")})`, cmdInsertMarkdown(filef, InsertionPlace.Underneath), false),
        createMenuItem("Text↑", `Insert new text block above (${keyBinding("M")})`, cmdInsertMarkdown(filef, InsertionPlace.Above), false),
        // Insert LaTeX
        createMenuItem(`${LaTeX_SVG} <div>↓</div>`, `Insert new LaTeX block underneath (${keyBinding("l")})`, cmdInsertLatex(schema, filef, InsertionPlace.Underneath), false),
        createMenuItem(`${LaTeX_SVG} <div>↑</div>`, `Insert new LaTeX block above (${keyBinding("L")})`, cmdInsertLatex(schema, filef, InsertionPlace.Above), false),
        // Select the parent node.
        createMenuItem("Parent", `Select the parent node (${keyBinding(".")})`, selectParentNode, false),
        // in teacher mode, display input area, hint and lift buttons.
        createMenuItem("ⵊ...", "Make selection an input area", wrapIn(schema.nodes["input"]), true),
        createMenuItem("<strong>?</strong>", "Make selection a hint element", wrapIn(schema.nodes["hint"]), true),
        createMenuItem("↑", "Lift selected node (Reverts the effect of making a 'hint' or 'input area')", liftWrapper, true)
    ]

    // If the DEBUG variable is set to `true` then we display a `dump` menu item, which outputs the current
    // document in the console as a JSON object.
    if (DEBUG) {
        items.push(createMenuItem("DUMP DOC", "", (state, dispatch) => {
            if (dispatch) console.log("\x1b[33m[DEBUG]\x1b[0m dumped doc", state.doc.toJSON());
            return true;
        }, false));
        items.push(createMenuItem("DUMP SELECTION", "", (state, dispatch) => {
            if (dispatch) console.log("\x1b[33m[DEBUG]\x1b[0m Selection", state.selection);
            return true;
        }, false));
    }

    // Return a new MenuView with the previously created items.
    return new MenuView(items, outerView);
}

/**
 * Interface describing the state of the menu plugin
 */
interface IMenuPluginState {
    teacher: boolean;
}

/**
 * The menu plugin key.
 */
export const MENU_PLUGIN_KEY = new PluginKey<IMenuPluginState>("prosemirror-menubar");

/**
 * Create a new menu plugin given the schema and file format.
 * @param schema The schema in use for the editor.
 * @param filef The file format of the currently opened file.
 * @returns A prosemirror `Plugin` type containing the menubar.
 */
export function menuPlugin(schema: Schema, filef: FileFormat, os: OS) {
    return new Plugin({
        // This plugin has an associated `view`. This allows it to add DOM elements.
        view(outerView) {
            // Create the default menu.
            const menuView = createDefaultMenu(schema, outerView, filef, os);
            // Get the parent node (the parent node of the outer prosemirror dom)
            const parentNode = outerView.dom.parentNode;
            if (parentNode == null) {
                throw Error("outerView.dom.parentNode cannot be null here");
            }
            // We insert the menubar before the prosemirror in the DOM tree.
            parentNode.insertBefore(menuView.menubarDOM, outerView.dom);

            // Return the plugin view.
            return menuView
        },
        // Set the key (uniquely associates this key to this plugin)
        key: MENU_PLUGIN_KEY,
        state: {
            init(_config, _instance): IMenuPluginState {
                // Initially teacher mode is set to true.
                return {
                    teacher: true
                }
            },
            apply(tr, value, _oldState, _newState) {
                // Upon recieving a transaction with meta information...
                let teacherState = !tr.getMeta(INPUT_AREA_PLUGIN_KEY);
                // we check if the teacherState variable is set and if so,
                //   we update the plugin state to reflect this
                if (teacherState === undefined) teacherState = value.teacher;
                return {
                    teacher: teacherState,
                };
            },
        }
    })
}
