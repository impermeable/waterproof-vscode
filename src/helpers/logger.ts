import { OutputChannel, window } from "vscode";

const OUTPUT_CHANNEL_NAME = "Waterproof Debug";

export class WaterproofLogger {
    private static outputChannel: OutputChannel;

    static log(message: string) {
        console.log(message);
        if (!WaterproofLogger.outputChannel) {
            WaterproofLogger.outputChannel = window.createOutputChannel(OUTPUT_CHANNEL_NAME);
        }
        WaterproofLogger.outputChannel.appendLine(message);
    }

    static debug(message: string) {
        // this.log(message)
    }

    static show() {
        if (!WaterproofLogger.outputChannel) {
            WaterproofLogger.outputChannel = window.createOutputChannel(OUTPUT_CHANNEL_NAME);
        }
        WaterproofLogger.outputChannel.show();
    }
}