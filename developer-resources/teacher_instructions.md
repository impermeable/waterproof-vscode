# Teacher instructions

This documents presents the various options you have as a teacher and what is needed to use them in class.

If you run into issues, or have questions that are not answered here, ask in our [Zulip](https://waterproof.zulipchat.com).

## General

When creating exercise files, turn on `Teacher Mode` in the Waterproof extension settings in Visual Studio Code. This allows you to edit 
the whole file and shows you parts that are hidden from students.

Students will often not "Trust" the VScode workspace. This will disable the Waterproof extension.
Tell students to trust the workspace, and when troubleshooting, look for a purple-ish bar at the top of the screen with a message about trust before
trying anything else.

Especially mathematics students have wildly varying experience with computers. It helps to show, record or describe the instructions in more detail, with the details for your course woven in.

### Creating exercises

When creating exercises, we recommend looking at the source of the existing exercises, these will contain a lot of practical examples how things work.

## Waterproof (Rocq based)

This version is most in use, and should be the default choice, unless you have a specific reason to use the Lean version.

### Web-based (aquarium)

[The aquarium](https://impermeable.github.io/aquarium/) is a ready-to-use version of Waterproof with exercises provided.
You can offer this to students if you like the exercises that are available through the dropdown on the bottom-right.
Students do not need to install anything, but this version is slower than the installed version.

### Web-based (vscode.dev)

Going to [vscode.dev](https://vscode.dev), install the Waterproof extension and "Open a folder" containing `.mv` files, 
you and students can work with Waterproof without installing anything. You distribute the `.mv` files to students
through a channel of your choice.

### Installed

Installing Visual Studio Code, installing the Waterproof extension and following the prompts to install the dependencies 
should work for Windows. If it does not, doing a manual installation is described [here](https://github.com/impermeable/waterproof-vscode#manual-installation-on-windows-with-installer).
Alternatively, it is possible to install in [Windows Subsystem for Linux](https://github.com/impermeable/waterproof-vscode#manual-installation-on-windows-with-wsl).

Installing on [Mac](https://github.com/impermeable/waterproof-vscode#installation-on-mac) or [Linux](https://github.com/impermeable/waterproof-vscode#installation-on-linux).

### Exercises

Available exercises: [Analysis 1, TU/e](https://github.com/impermeable/waterproof-exercise-sheets), [Bewijzen in de Wiskunde, UU](https://github.com/impermeable/introduction-to-proof-sheets), [Analysis, RUG](https://github.com/impermeable/analysis-rug)

## Waterproof (Lean based)

The Lean version is backed by [Verbose Lean](https://github.com/PatrickMassot/verbose-lean4).

Installation instructions are: 

1. Install [Lean](https://lean-lang.org/install/) (along with VS Code).
2. Install the Waterproof extension in VSCode.
3. Disable the Lean extension, or follow the instructions to setup a separate profile in VS Code when these pop up.

A self-contained zip file for installation is in developement.


## Exercises

Available exercises: [Bewijzen in de Wiskunde, UU](https://github.com/impermeable/introduction-to-proof-sheets-lean)
