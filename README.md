# Waterproof

The Waterproof vscode extension helps students learn how to write mathematical proofs.


## Installation on Windows

### Step 1: Dependencies installer
Download and execute the bundled installer `Waterproof-dependencies-installer-v2.1.0+8.17.exe` from the [release page](https://github.com/impermeable/waterproof-dependencies-installer/releases/tag/v2.1.0%2B8.17)
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
opam install coq-lsp -v 8.17
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
opam install coq-lsp -v 8.17
opam install coq-waterproof
```



## Installation on Mac

### Step 1: Dependencies installer
Download and execute the bundled installer `Waterproof_Background.dmg` from the [release page](https://github.com/impermeable/waterproof-dependencies-installer/releases/tag/v2.1.0%2B8.17)

Open the `Waterproof_Background.dmg` and drag `Waterproof_Background.app` into the "Applications". You may need to provide administrative access to do this.


### Step 2: Install the vscode extension
Install this [Waterproof vscode extension](https://marketplace.visualstudio.com/items?itemName=waterproof-tue.waterproof)

### Step 3: Update the path settings for Waterproof
Within vscode, go to the Extensions tab (Shift+Command+X) and search for the installed Waterproof extension. Once the extension is found, click on the gear icon and enter the `Extension Settings`.
Within the setting `Waterproof: Path` enter the following line: 

```
/Applications/Waterproof_Background.app/Contents/Resources/bin/coq-lsp
```

### Step 4: Update the args settings for Waterproof
Still in the 'Extension Settings' within the setting `Waterproof: Args`. Click on the 'Add Item' button and   
For each of the following lines, click on the 'Add Item' button and enter the line. 
**Each of the lines should be added inividually.**

```
--ocamlpath=/Applications/Waterproof_Background.app/Contents/Resources/lib
```
```
--coqcorelib=/Applications/Waterproof_Background.app/Contents/Resources/lib/coq-core
```
```
--coqlib=/Applications/Waterproof_Background.app/Contents/Resources/lib/coq
```

You may have to restart vscode before these settings are implemented.

### Warning
Upon opening a .mv file for the first time, a pop-up about verifying the developer may appear.

To fix this issue, click 'Show in Finder', Control click on the Coq-Platform application and press open. Click 'open' again if a pop-up appears. You may close the application once it has opened. This will ensure that the application is now trusted when using the Waterproof extension in the future.

## Manual Installation on Mac

If the above method did not work for Mac, it is possible to instead install the dependencies manually using opam.

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
opam install coq-lsp -v 8.17
opam install coq-waterproof
```
