import { OutputChannel, window } from "vscode";
import { WaterproofConfigHelper, WaterproofSetting } from "./config-helper";

const OUTPUT_CHANNEL_NAME = "Waterproof Debug";

export class WaterproofLogger {
    private static outputChannel: OutputChannel;
    public static logDebug: boolean = WaterproofConfigHelper.get(WaterproofSetting.LogDebugStatements); 

    static log(message: string) {
        console.log(message);
        if (!WaterproofLogger.outputChannel) {
            WaterproofLogger.outputChannel = window.createOutputChannel(OUTPUT_CHANNEL_NAME);
        }
        WaterproofLogger.outputChannel.appendLine(message);
    }

    static debug(message: string) {
        if (WaterproofLogger.logDebug) this.log(message);
    }

    static show() {
        if (!WaterproofLogger.outputChannel) {
            WaterproofLogger.outputChannel = window.createOutputChannel(OUTPUT_CHANNEL_NAME);
        }
        WaterproofLogger.outputChannel.show();
    }
}