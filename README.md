# Waterproof

The Waterproof vscode extension helps students learn how to write mathematical proofs.

## Installation on Windows with WSL

### Step 0: Install WSL

For the Waterproof extension to work on Windows, one needs to use WSL. If WSL is not yet set up on your Windows computer, open a Powershell window (for instance by clicking on the magnifying glass, typing "Powershell" and selecting the Powershell app). In the Powershell window that appears, execute

```
wsl --install
```

If necessary, you can find more information about WSL and how to install it [here](https://learn.microsoft.com/en-us/windows/wsl/install).


### Step 1: Install this [Waterproof vscode extension](https://marketplace.visualstudio.com/items?itemName=waterproof-tue.waterproof)

From this page in vscode, you can just click on the "Install" button.

### Step 2: Install the coq-lsp and coq-waterproof plugins

Within a WSL distribution, execute the following lines:

```
apt-get install opam
opam init
eval $(opam env)
opam install coq-lsp
opam install coq-waterproof
```

### Step 3: Install the [WSL vscode extension](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-wsl)

### Step 4: Connect to WSL from vscode

Press `Ctrl+Shift+P` and type "WSL: Connect to WSL using Distro..."

Alternatively, one navigate to a folder in WSL itself, and type `code .` to open the folder in WSL itself.

## Installation on Linux

### Step 1: Install this [Waterproof vscode extension](https://marketplace.visualstudio.com/items?itemName=waterproof-tue.waterproof)

### Step 2: Install the coq-lsp and coq-waterproof plugins

In a terminal, execute the following lines

```
apt-get install opam
opam init
eval $(opam env)
opam install coq-lsp
opam install coq-waterproof
```

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
opam install coq-lsp
opam install coq-waterproof
```
