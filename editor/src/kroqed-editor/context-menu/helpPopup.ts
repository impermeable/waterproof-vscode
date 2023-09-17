import { PpString, Message as GoalMessage, Pp } from "../../../../lib/types";
import { FormatPrettyPrint } from "../../../../lib/format-pprint/js/main";
import { HelpMessages } from "./types";
import { Command } from "prosemirror-state";
import { Editor } from "../editor";
import { MessageType } from "../../../../shared";

export class HelpPopup {
    private helpPopupDiv: HTMLDivElement;
    private closeButtonDiv: HTMLDivElement;
    private containerDiv: HTMLDivElement;

    private mouseY: number;

    private theEditor: Editor;

    constructor(editor: Editor) {
        this.theEditor = editor;
        this.helpPopupDiv = document.createElement("div");
        this.closeButtonDiv = document.createElement("div");
        this.containerDiv = document.createElement("div");

        this.helpPopupDiv.style.display = "none";
        
        this.closeButtonDiv.innerHTML = "&#10006;";
        
        this.helpPopupDiv.classList.add("help-popup");
		this.containerDiv.classList.add("content-container");
		this.closeButtonDiv.classList.add("close");
        
        const shadowThis = this;

        document.addEventListener("mousemove", (ev: MouseEvent) => this.handleMouse(ev, shadowThis));
        document.addEventListener("mouseenter", (ev: MouseEvent) => this.handleMouse(ev, shadowThis));
        
        this.helpPopupDiv.appendChild(this.closeButtonDiv);
        this.helpPopupDiv.appendChild(this.containerDiv);
        
        document.body.appendChild(this.helpPopupDiv);
        const shadow = this.helpPopupDiv;
        this.closeButtonDiv.onclick = () => {
            shadow.style.display = 'none';
        }
    }

    private handleMouse(ev: MouseEvent, popup: HelpPopup) {
        popup.mouseY = ev.pageY;
    }

    private show() {
        this.helpPopupDiv.style.top = `${this.mouseY}px`;
        this.helpPopupDiv.style.display = "block";
    }

    private hide() {
        this.helpPopupDiv.style.display = "none";
    }

    private setContent(renderedHTML: string) {
        this.containerDiv.innerHTML = renderedHTML;
    }

    private renderPP(ppIn: Pp): string {
        return FormatPrettyPrint.pp2DOM(ppIn, "horizontal").prop("outerHTML") as string;
    }

    private renderMessages(messages: HelpMessages): string {
        const first = messages[0];
        let helpBoxContent = "";
        if (isMessagePpString(first)) {
            // We are dealing with `Message<PpString>` type objects.
            const typed = messages as GoalMessage<PpString>[];
            for (let msg of typed) {
                const text = msg.text;
                if (text instanceof String) {
                    helpBoxContent += text as string;
                } else {
                    helpBoxContent += this.renderPP(text as Pp);
                }
            }
        } else {
            const typed = messages as PpString[];
            for (let msg of typed) {
                if (msg instanceof String) {
                    helpBoxContent += msg as string;
                } else {
                    helpBoxContent += this.renderPP(msg as Pp);
                }
            }
        }

        return helpBoxContent;
    }

    public setContentAndDisplay(messages: HelpMessages) {
        if (!messages || messages.length === 0) {
            console.error("Empty Messages array");
            return;
        }

        const renderOutput = this.renderMessages(messages);
        this.setContent(renderOutput);
        this.show();
    }

    public asCommand: Command = (state, dispatch, view) => {
        const date = new Date();
        this.theEditor.post({type: MessageType.command, body: "Help.", time: date.getTime()});
        return true;
    } 
}

/**
 * Type guard function, checks whether `sample` is a `Message<PpString>`
 * @param sample The sample to check.
 * @returns Whether `sample` is `Message<PpString>`.
 */
function isMessagePpString(sample: PpString | GoalMessage<PpString>): sample is GoalMessage<PpString> {
    return (sample as GoalMessage<PpString>).level !== undefined;
}