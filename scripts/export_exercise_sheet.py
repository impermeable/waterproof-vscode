#!/usr/bin/env python3
"""
Export Exercise Sheet Script

This script extracts the functionality from the exportExerciseSheet function
to remove solutions from Waterproof (.mv) files.

Usage:
    # Single file mode - output to stdout
    python export_exercise_sheet.py input.mv

    # Batch mode - process entire directory structure
    python export_exercise_sheet.py --input-folder /path/to/input --output-folder /path/to/output

The script removes content from <input-area> blocks, leaving empty code blocks
suitable for students to fill in as exercises.
"""

import argparse
import os
import re
import sys
from pathlib import Path
from typing import Optional


def process_waterproof_content(content: str) -> str:
    """
    Process Waterproof file content by removing solutions from input-area blocks.
    
    This function replicates the logic from the TypeScript exportExerciseSheet function:
    - Finds <input-area> blocks containing ```coq code ```
    - Replaces the content with empty code blocks
    
    Args:
        content: The raw content of a .mv file
        
    Returns:
        Processed content with solutions removed
    """
    # Pattern matches the same regex as in the TypeScript function:
    # <input-area>\s*```coq([\s\S]*?)\s*```\s</input-area>
    pattern = r'<input-area>\s*```coq([\s\S]*?)\s*```\s*</input-area>'
    replacement = '<input-area>\n```coq\n\n```\n</input-area>'
    
    return re.sub(pattern, replacement, content)


def process_single_file(file_path: Path) -> str:
    """
    Process a single .mv file and return the processed content.
    
    Args:
        file_path: Path to the .mv file
        
    Returns:
        Processed content with solutions removed
        
    Raises:
        FileNotFoundError: If the file doesn't exist
        ValueError: If the file is not a .mv file
    """
    if not file_path.exists():
        raise FileNotFoundError(f"File not found: {file_path}")
    
    if file_path.suffix != '.mv':
        raise ValueError(f"File must have .mv extension, got: {file_path.suffix}")
    
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        return process_waterproof_content(content)
    except UnicodeDecodeError as e:
        raise ValueError(f"Could not decode file as UTF-8: {e}")


def process_directory(input_folder: Path, output_folder: Path) -> None:
    """
    Process all .mv files in input_folder and save to output_folder,
    preserving directory structure.
    
    Args:
        input_folder: Source directory containing .mv files
        output_folder: Destination directory for processed files
        
    Raises:
        NotADirectoryError: If input_folder is not a directory
    """
    if not input_folder.is_dir():
        raise NotADirectoryError(f"Input folder is not a directory: {input_folder}")
    
    # Create output folder if it doesn't exist
    output_folder.mkdir(parents=True, exist_ok=True)
    
    # Find all .mv files recursively
    mv_files = list(input_folder.rglob("*.mv"))
    
    if not mv_files:
        print(f"No .mv files found in {input_folder}", file=sys.stderr)
        return
    
    processed_count = 0
    
    for mv_file in mv_files:
        try:
            # Calculate relative path from input folder
            relative_path = mv_file.relative_to(input_folder)
            output_file = output_folder / relative_path
            
            # Create output directory if needed
            output_file.parent.mkdir(parents=True, exist_ok=True)
            
            # Process the file
            processed_content = process_single_file(mv_file)
            
            # Write to output file
            with open(output_file, 'w', encoding='utf-8') as f:
                f.write(processed_content)
            
            print(f"Processed: {relative_path}")
            processed_count += 1
            
        except Exception as e:
            print(f"Error processing {mv_file}: {e}", file=sys.stderr)
    
    print(f"Successfully processed {processed_count} files.")


def main():
    """Main entry point for the script."""
    parser = argparse.ArgumentParser(
        description="Export exercise sheets from Waterproof (.mv) files by removing solutions",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Process single file to stdout
  python export_exercise_sheet.py exercise.mv

  # Process entire directory structure
  python export_exercise_sheet.py --input-folder ./lessons --output-folder ./exercises

  # Process directory with shorter flags
  python export_exercise_sheet.py -i ./src -o ./dest
        """
    )
    
    # Mutually exclusive group for single file vs directory mode
    group = parser.add_mutually_exclusive_group(required=True)
    
    group.add_argument(
        'file',
        nargs='?',
        type=Path,
        help='Single .mv file to process (output goes to stdout)'
    )
    
    group.add_argument(
        '--input-folder', '-i',
        type=Path,
        help='Input folder containing .mv files to process'
    )
    
    parser.add_argument(
        '--output-folder', '-o',
        type=Path,
        help='Output folder for processed files (required with --input-folder)'
    )
    
    args = parser.parse_args()
    
    try:
        if args.file:
            # Single file mode - output to stdout
            processed_content = process_single_file(args.file)
            print(processed_content, end='')
            
        elif args.input_folder:
            # Directory mode
            if not args.output_folder:
                parser.error("--output-folder is required when using --input-folder")
            
            process_directory(args.input_folder, args.output_folder)
            
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
