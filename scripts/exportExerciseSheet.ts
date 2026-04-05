/**
 * Waterproof Exercise Sheet Processor
 * A CLI tool to export exercise sheets from .mv or .lean files by removing 
 * solution content from input cells and substituting it with an empty code block.
 * Supports single-file processing via stdout or recursive directory batch processing.
 *
 * * Usage:
 * Process a single file (file.mv or file.lean) and output to terminal
 * npx tsx exportExerciseSheet.ts file.mv
 * or
 * npx tsx exportExerciseSheet.ts file.lean
 *
 * Process an entire directory (input_dir) with .mv and .lean files, and store processed files in another directory (output_dir) preserving the directory file structure.
 * npx tsx exportExerciseSheet.ts -i input_dir -o output_dir
 *
 * View help
 * npx tsx exportExerciseSheet.ts --help
 */

import * as path from 'path';
import * as fs from 'fs';
import { Command } from 'commander';
import { processWaterproofContent } from '../src/helpers/exerciseSheet.ts';


/**
 * Get paths of all .mv and .lean files inside a folder recursively.
 *
 * @param folder - Path to the folder
 */
function getAllFiles(folder: string): string[] {
    let allFilePaths: string[] = [];
    const fileNames = fs.readdirSync(folder);

    fileNames.forEach((fileName) => {
        const filePath = path.join(folder, fileName);
        if (fs.statSync(filePath).isDirectory()) {
            allFilePaths.push(...getAllFiles(filePath));    
        } else {
            let extension: string = path.extname(filePath);
            if (extension === '.mv' || extension === '.lean') {
                allFilePaths.push(filePath); 
            }
        }
    });

    return allFilePaths;
}

/**
 * Process a single .mv/.lean file and return processed content.
 *
 * @param filePath - Path to the .mv/.lean file
 * @return Processed content with solutions removed
 *
 * @throws {Error} If the file doesn't exist
 *
 */
function processSingleFile(filePath: string): string {
    if (!fs.existsSync(filePath)) {
        throw new Error(`File not found: ${filePath}`);
    }
    let fileExtension: string = path.extname(filePath);
    let content = fs.readFileSync(filePath, 'utf-8');

    return processWaterproofContent(content, fileExtension);
}

/**
 * Process all .mv and .lean files in inputFolder and save to outputFolder,
 * preserving directory structure.
 *
 * @param inputFolder - Source directory containing .mv files
 * @param outputFolder - Destination directory for processed files
 *
 * @throws {Error} If input folder is not a directory
 */
function processDirectory(inputFolder: any, outputFolder: any) {
    if (!fs.statSync(inputFolder).isDirectory()) {
        throw new Error(`Input folder is not a directory: ${inputFolder}`);
    }
    
    // Create output folder if it doesn't exist
    fs.mkdirSync(outputFolder, { recursive: true });
    
    // Find all .mv and .lean files recursively
    let files = getAllFiles(inputFolder);

    if (files.length === 0) {
        console.error(`No .mv or .lean files found in ${inputFolder}`);
    }

    let processedCount = 0;

    files.forEach((file) => {
        try {
            // Calculate relative path from input folder
            let relativePath = path.relative(inputFolder, file);
            let outputFile = path.join(outputFolder, relativePath);
            
            // Create ouptut directory if needed
            fs.mkdirSync(path.dirname(outputFile), { recursive: true });
            
            // Process the file
            let processedContent = processSingleFile(file)

            // Write to output file
            fs.writeFileSync(outputFile, processedContent);

            console.log(`Processed: ${relativePath}`);
            processedCount++;
        } catch (error) {
            console.error(`Error processing ${file}: ${error}`);    
        }
    });

    console.log(`successfully processed ${processedCount} files.`);
}


// Defining a parser for script arguments
const program = new Command();
program
    .argument('[file]', 'Single .mv file to process (output goes to stdout)')
    .description('Export exercise sheets from Waterproof (.mv) files by removing solutions')
    .option('-i, --input-folder <path>', 'Input folder containing .mv files to process')
    .option('-o, --output-folder <path>', 'Output folder for processed files (required with --input-folder)')
    .action((file, options) => {
        try {
            if (file) {
                // Single file mode - output to stdout
                let processedContent = processSingleFile(file)
                console.log(processedContent);
            } else if (options.inputFolder) {
                if (!options.outputFolder) {
                    throw new Error('--output-folder is required when using --input-folder');
                }
                processDirectory(options.inputFolder, options.outputFolder);
            } else {
                program.help();
            }
        } catch (error) {
            console.error('Error while saving as exercise sheet:\n', error);
        }
    });

// Executing the script
program.parse(process.argv);
