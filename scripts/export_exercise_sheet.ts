import { window, workspace } from "vscode";
import path from 'path';
import fs from 'fs';

/**
 * Process Waterproof Rocq or Lean file content by removing solutions from input-area blocks.
 * Finds input area blocks of the form and replaces the content with empty code blocks.
 *
 * For rocq an input area has the following form:
 * <input-area>
 * ```coq
 *
 * ....code....
 *
 * ```
 * </input-area>
 *
 * For lean an input area has the following form:
 * :::input
 * ```lean
 *
 * ....code....
 *
 * ```
 * :::
 *
 * @param content - The raw content of a .mv or .lean file
 * @returns Processed content with solutions removed
 */
function processWaterproofContent(content: string, extension: string): string {
    switch (extension) {
        case '.lean':
            const pattern = /:::input\s*```lean[\s\S]*?```\s*:::/g;
            const replacement = ':::input\n```lean\n\n```\n:::';
            break;
        case '.mv':
            const pattern = /<input-area>\s*```coq[\s\S]*?```\s*<\/input-area>/g;
            const replacement = '<input-area>\n```coq\n\n```\n</input-area>';
            break;
        default:
            throw new Exception(`Only files with extension .lean and .mv are supported, found ${extension}`);
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
            content = processWaterproofContent(content, fileExtension);
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

function processSingleFile(filePath: any): string {
    if (!fs.existsSync(filePath)) {
        throw new Error(`File not found: ${filePath}`);
    }
    let fileExtension: string = path.extname(filePath);
    let content = fs.readFileSync(filePath, 'utf-8');

    return processWaterproofContent(content, fileExtension);
}

function processDirectory(inputFolder: any, outputFolder: any) {

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
