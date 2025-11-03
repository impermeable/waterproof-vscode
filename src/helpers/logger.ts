import { OutputChannel, window } from "vscode";
import { WaterproofConfigHelper, WaterproofSetting } from "./config-helper";

const OUTPUT_CHANNEL_NAME = "Waterproof Debug";

type StringConvertable = {
  toString(): string;
};

export class WaterproofLogger {
    private static outputChannel: OutputChannel;
    public static logDebug: boolean = WaterproofConfigHelper.get(WaterproofSetting.LogDebugStatements); 

    static log(message: StringConvertable) {
        console.log(message);
        if (!WaterproofLogger.outputChannel) {
            WaterproofLogger.outputChannel = window.createOutputChannel(OUTPUT_CHANNEL_NAME);
        }
        WaterproofLogger.outputChannel.appendLine(message.toString());
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