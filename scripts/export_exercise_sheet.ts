import { window, workspace } from "vscode";
import path from 'path';

/**
 * Process Waterproof Rocq file content by removing solutions from input-area blocks.
 * This function:
 * - Finds input area blocks of the form
 *
 * <input-area>
 * ```coq
 *
 * ....code....
 *
 * ```
 * :::
 *
 * - Replaces the content with empty code blocks
 *
 * @param content - The raw content of a .mv file
 * @returns Processed content with solutions removed
 */
async function processWaterproofContentRocq(content: string): string {
    const pattern = /<input-area>\s*```coq[\s\S]*?```\s*<\/input-area>/g;
    const replacement = "<input-area>\n```coq\n\n```\n</input-area>";
    content = content.replace(pattern, replacement);
    return content;
}

/**
 * Process Waterproof Lean file content by removing solutions from input-area blocks.
 * This function:
 * - Finds input area blocks of the form
 *
 * :::input
 * ```lean
 *
 * ....code....
 *
 * ```
 * :::
 *
 * - Replaces the content with empty code blocks
 *
 * @param content - The raw content of a .lean file
 * @returns Processed content with solutions removed
 */
async function processWaterproofContentLean(content: string): string {
    const pattern = /:::input\s*```lean[\s\S]*?```\s*:::/g;
    const replacement = ':::input\n```lean\n\n```\n:::';
    content = content.replace(pattern, replacement);
    return content;
}

/**
 * Remove solutions from document and open save dialog for the solution-less file.
 */
export async function exportExerciseSheet(document: TextDocument) {
    try {
        if (document) {
            let content: string = document.getText();
            let fileExtension: string = path.extname(document.uri.fsPath);
            switch (fileExtension) {
                case '.lean':
                    content = await processWaterproofContentLean(content, fileExtension);
                    break;
                case '.mv':
                    content = await processWaterproofContentRocq(content, fileExtension);
                    break;
                default:
                    window.showInformationMessage(`Saving as exercise sheet is not supported for this file type: ${fileExtension}`);
                    return;
            } 
            const fileUri = await window.showSaveDialog();
            if (fileUri) {
                await workspace.fs.writeFile(fileUri, Buffer.from(content, 'utf8'));
                window.showInformationMessage(`Saved to: ${fileUri.fsPath}`);
            }
        }
    } catch (error) {
        console.error('Error while saving as exercise sheet:\n', error);
    }
}

async function processSingleFile(filePath: any): string {

}

async function processDirectory(inputFolder: any, outputFolder: any) {

}

async function runScript() {
    const { program } = require('commander');
    program
        .argument('[file]', 'Single .mv file to process (output goes to stdout)')
        .option('-i, --input-folder', 'Input folder containing .mv files to process')
        .option('-o --output-folder', 'Output folder for processed files (required with --input-folder)')
    program.parse(process.argv);
    
    try {
        if (program.file) {
            // Single file mode - output to stdout
            let processedContent = processSingleFile(args.file)
            process.stdout.write(processedContent);
        } else if (program.options.inputFolder) {
            if (!program.options.outputFolder) {
                throw new Error('--output-folder is required when using --input-folder');
            }
            processDirectory(program.options.inputFolder, program.options.outputFolder);
        } else {
            program.help();
        }
    } catch (error) {
        console.error('Error while saving as exercise sheet:\n', error);
    }
}
