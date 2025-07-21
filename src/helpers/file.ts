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
        // We filter out empty path strings, maybe we could instead make this function
        // assume that arguments are non-empty and let the caller handle these?
        paths = paths.filter(v => v != "");
        const sep = process.platform === "win32" ? "\\" : "/";
        return paths.join(sep);
    }
}