# Waterproof

The Waterproof vscode extension helps students learn how to write mathematical proofs.

1. [Automatic Installation](#quick-install-instructions-for-windows)
2. [Manual Installation](#more-extensive-installation-instructions)
3. [Getting Started](#getting-started)

# Quick install instructions for Windows

Install this extension and follow the installation instructions that pop up.

---

# More extensive installation instructions

## Installation on Windows

### Step 1: Dependencies installer
Download and execute the bundled installer `Waterproof-dependencies-wp-3.0.0+9.0-Windows-x86_64.exe` from the [release page](https://github.com/impermeable/waterproof-dependencies-installer/releases/tag/wp-3.0.0%2B9.0)
**Note:** do not change the default installation location, otherwise Waterproof will not work.

### Step 2: Install the vscode extension
Install this [Waterproof vscode extension](https://marketplace.visualstudio.com/items?itemName=waterproof-tue.waterproof)

### Step 3: Update the settings for Waterproof
Within vscode, go to the Extensions tab (Ctrl+Shift+X) and search for the installed Waterproof extension. Once the extension is found, click on the gear icon and enter the 'Extension Settings'.
Within the setting 'Waterproof: Path' enter the following line:

```
C:\cygwin_wp\home\runneradmin\.opam\wp\bin\coq-lsp
```

**Note:** This will only work if you have not changed the default installation for the dependencies.
In the case that a different file location was used for the installation, find the location of '.opam\wp\bin\coq-lsp' within this folder. Paste instead the absolute file address of this coq-lsp file into the 'Waterproof: Path' setting.



## Installation on Windows with WSL

If the above method did not work for Windows, it is possible to instead install the dependencies and run the Waterproof vscode extension using WSL

### Step 0: Install WSL

For the Waterproof extension to work on Windows, one needs to use WSL. If WSL is not yet set up on your Windows computer, open a Powershell window and run it as administrator (for instance by clicking on the magnifying glass, typing "Powershell", right clicking the Powershell app and pressing "Run as administrator"). In the Powershell window that appears, execute

```
wsl --install Ubuntu
```

This will specifically install the Ubuntu distribution
If necessary, you can find more information about WSL and how to install it [here](https://learn.microsoft.com/en-us/windows/wsl/install).

If this is your first time installing WSL and the Ubuntu Distribution you need to set up a username and password to use later. After setting this up, you will need to update the package lists on the system. To do this execute the following line:

```
sudo apt-get update
```

(Press enter to accept all requests)

### Step 1: Install the coq-lsp and coq-waterproof plugins

Within a WSL distribution, execute the following lines:

```
sudo apt-get install opam
opam init
eval $(opam env)
opam install coq-lsp.0.2.3+9.0
opam install coq-waterproof
```

The last two lines may take a while to install
(Press enter to accept all requests or 'y' to accept them one-by-one)

### Step 2: Install the [WSL vscode extension](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-wsl)

### Step 3: Connect to WSL from vscode

Press `Ctrl+Shift+P` and type "WSL: Connect to WSL using Distro..."

Alternatively, one navigate to a folder in WSL itself, and type `code .` to open the folder in WSL itself.

### Step 4: Install this [Waterproof vscode extension](https://marketplace.visualstudio.com/items?itemName=waterproof-tue.waterproof)

From this page in vscode, you can just click on the "Install" button.



## Installation on Linux

### Step 1: Install this [Waterproof vscode extension](https://marketplace.visualstudio.com/items?itemName=waterproof-tue.waterproof)

### Step 2: Install the coq-lsp and coq-waterproof plugins

In a terminal, execute the following lines

```
apt-get install opam
opam init
eval $(opam env)
opam install coq-lsp.0.2.3+9.0
opam install coq-waterproof
```

If vscode cannot detect the installation, set the coq-lsp path to the output of `which coq-lsp`. This can be done
using ctrl+shift+p and selecting "Waterproof: Change Waterproof path".
Alternatively, make sure that the `PATH` available to vscode contains the coq-lsp binary.

## Installation on Mac

### Step 1: Install this [Waterproof vscode extension](https://marketplace.visualstudio.com/items?itemName=waterproof-tue.waterproof)

### Step 2: Install the coq-lsp and coq-waterproof plugins

If you use homebrew, first install opam by executing the following lines in a terminal

```
brew install gpatch
brew install opam
```

If you prefer MacPorts, instead run
```
port install opam
```

Then execute

```
opam init
eval $(opam env)
opam install coq-lsp.0.2.3+9.0
opam install coq-waterproof
```

# Getting Started

### Tutorial
To get started with Waterproof, we recommend going through the tutorial. The tutorial can be accessed in VS Code by pressing `Ctrl-Shift-P` (this opens the command palette), typing `open tutorial` until you find the option `Waterproof: Open Tutorial`.

### Tactics
Waterproof makes use of 'tactics', information on the available tactics, together with explanations and examples can be accessed via the extension or through the repository:

* From the Waterproof extension: Navigate to the Waterproof sidebar (accessible via the droplet icon on the left) and click on the `Tactics` button. The panel that now opens shows all available tactics.
* From the repository: The repository contains a [Markdown](/docs/tactics-sheet.md) version of the tactics sheet.
