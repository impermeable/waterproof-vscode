import * as path from 'path';
import * as fs from 'fs';
import { Command } from 'commander';
import { processWaterproofContent } from '../src/helpers/exerciseSheet.ts';


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

function processSingleFile(filePath: string): string {
    if (!fs.existsSync(filePath)) {
        throw new Error(`File not found: ${filePath}`);
    }
    let fileExtension: string = path.extname(filePath);
    let content = fs.readFileSync(filePath, 'utf-8');

    return processWaterproofContent(content, fileExtension);
}

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

program.parse(process.argv);
