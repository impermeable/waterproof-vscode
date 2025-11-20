import { ExtensionContext } from "vscode"

export type WaterproofConfiguration = {
    requiredCoqLspVersion: string,
    requiredCoqWaterproofVersion: string,
    defaultCoqLspPathWindows: string,
    installerDownloadLinkWindows: string
}

const waterproofField = "waterproofConfiguration";
export class WaterproofPackageJSON {
    static getConfig(context: ExtensionContext): WaterproofConfiguration {
        const packageJSON = context.extension.packageJSON;
        const waterproofConfig = packageJSON[waterproofField];
        if (waterproofConfig === undefined) {
            throw new Error(`Field '${waterproofField}' not found in the package.json file`);
        }

        if (waterproofConfig["requiredCoqLspVersion"] === undefined ||
            waterproofConfig["requiredCoqWaterproofVersion"] === undefined ||
            waterproofConfig["defaultCoqLspPathWindows"] === undefined ||
            waterproofConfig["installerDownloadLinkWindows"] === undefined
        ) {
            throw new Error(`Missing option in field '${waterproofField}' of package.json file`);
        }

        return packageJSON[waterproofField] as WaterproofConfiguration;
    }

    static requiredCoqLspVersion(context: ExtensionContext): string {
        const packageJSON = context.extension.packageJSON;
        const waterproofConfig = packageJSON[waterproofField];
        if (waterproofConfig === undefined) {
            throw new Error(`Field '${waterproofField}' not found in the package.json file`);
        }

        if (waterproofConfig["requiredCoqLspVersion"] === undefined) {
            throw new Error(`Missing option 'requiredCoqLspVersion' in field '${waterproofField}' of package.json file`);
        }

        return waterproofConfig["requiredCoqLspVersion"] as string;
    }

    static requiredCoqWaterproofVersion(context: ExtensionContext): string {
        const packageJSON = context.extension.packageJSON;
        const waterproofConfig = packageJSON[waterproofField];
        if (waterproofConfig === undefined) {
            throw new Error(`Field '${waterproofField}' not found in the package.json file`);
        }

        if (waterproofConfig["requiredCoqWaterproofVersion"] === undefined) {
            throw new Error(`Missing option 'requiredCoqWaterproofVersion' in field '${waterproofField}' of package.json file`);
        }

        return waterproofConfig["requiredCoqWaterproofVersion"] as string;
    }
    
    static defaultCoqLspPathWindows(context: ExtensionContext): string {
        const packageJSON = context.extension.packageJSON;
        const waterproofConfig = packageJSON[waterproofField];
        if (waterproofConfig === undefined) {
            throw new Error(`Field '${waterproofField}' not found in the package.json file`);
        }

        if (waterproofConfig["defaultCoqLspPathWindows"] === undefined) {
            throw new Error(`Missing option 'defaultCoqLspPathWindows' in field '${waterproofField}' of package.json file`);
        }

        return waterproofConfig["defaultCoqLspPathWindows"] as string;
    }

    static installerDownloadLinkWindows(context: ExtensionContext): string {
        const packageJSON = context.extension.packageJSON;
        const waterproofConfig = packageJSON[waterproofField];
        if (waterproofConfig === undefined) {
            throw new Error(`Field '${waterproofField}' not found in the package.json file`);
        }

        if (waterproofConfig["installerDownloadLinkWindows"] === undefined) {
            throw new Error(`Missing option 'installerDownloadLinkWindows' in field '${waterproofField}' of package.json file`);
        }

        return waterproofConfig["installerDownloadLinkWindows"] as string;
    }
}