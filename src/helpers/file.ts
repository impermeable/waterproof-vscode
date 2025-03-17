import { Uri } from "vscode";


export class WaterproofFileUtil {
    public static getDirectory(filePath: string): string {
        const sep = process.platform === "win32" ? "\\" : "/";
        return new String(filePath).substring(0, filePath.lastIndexOf(sep)); 
    }

    public static getBasename(filePath: Uri): string {
        let base = new String(filePath.path).substring(filePath.path.lastIndexOf('/') + 1); 
        if(base.lastIndexOf(".") != -1)       
            base = base.substring(0, base.lastIndexOf("."));
        return base;
    }

    public static join(...paths: string[]): string {
        const sep = process.platform === "win32" ? "\\" : "/";
        return paths.join(sep);
    }
}