#!/bin/bash

OS=$(uname -s)
ARCH=$(uname -m)

VENV_NAME="batfish-venv"

install_for_linux() {
    echo "Detected Linux system (${ARCH})"

    # update apt
    sudo apt-get update

    # install OpenJDK 11
    sudo apt install openjdk-11-jdk openjdk-11-dbg -y

    # install Wget
    sudo apt install wget -y

    # install Bazel
    # wget -O- https://github.com/bazelbuild/bazelisk/releases/download/v1.12.2/bazelisk-linux-amd64 | sudo tee /usr/local/bin/bazelisk > /dev/null
    wget -O- https://github.com/bazelbuild/bazelisk/releases/download/v1.25.0/bazelisk-linux-amd64 | sudo tee /usr/local/bin/bazelisk > /dev/null
    sudo chmod +x /usr/local/bin/bazelisk
    sudo ln -s bazelisk /usr/local/bin/bazel

    # Z3 download URL and relevant local archive file and relevant directory
    Z3_VERSION="4.14.0"
    Z3_OS="x64-glibc-2.35"
    Z3_BASENAME="z3-${Z3_VERSION}-${Z3_OS}"
    Z3_URL="https://github.com/Z3Prover/z3/releases/download/z3-${Z3_VERSION}/${Z3_BASENAME}.zip"
    Z3_ARCHIVE="${Z3_BASENAME}.zip"
    Z3_DIR="${Z3_BASENAME}"
    # Z3 shared library directory
    Z3_BIN_DIR="/usr/bin"
    Z3_INCLUDE_DIR="/usr/include"
    Z3_LIB_DIR="/usr/lib"

    # install Z3
    wget "$Z3_URL"
    unzip "$Z3_ARCHIVE"
    sudo cp "$Z3_DIR/bin/z3" "$Z3_BIN_DIR/z3"
    sudo find "$Z3_DIR/include" -type f -exec cp {} "$Z3_INCLUDE_DIR" \;
    # sudo rsync -a "$Z3_DIR/include/" "$Z3_INCLUDE_DIR/" 
    sudo cp "$Z3_DIR/bin/libz3java.so" "$Z3_LIB_DIR/libz3java.so"
    sudo cp "$Z3_DIR/bin/libz3.so" "$Z3_LIB_DIR/libz3.so"
    sudo cp "$Z3_DIR/bin/com.microsoft.z3.jar" "$Z3_LIB_DIR/com.microsoft.z3.jar"
    sudo chmod 755 "$Z3_LIB_DIR/libz3java.so"
    sudo chmod 755 "$Z3_LIB_DIR/libz3.so"
    rm -r "$Z3_ARCHIVE"
    rm -r "$Z3_DIR" 

    if false; then
        # install Z3 via source code
        git clone https://github.com/Z3Prover/z3.git
        cd z3
        python3 scripts/mk_make.py --java
        cd build
        make examples
        sudo make install
    fi

    # Batfish Python3 venv `batfish-venv`
    VENV_NAME = "batfish-venv"

    # install Python3 pip and venv
    sudo apt-get install python3-pip -y
    sudo apt-get install python3-venv -y

    # create Python3 venv
    python3 -m venv $VENV_NAME

    # activate Python3 venv batfish-venv
    source $VENV_NAME/bin/activate
    
    # install Pybatfish
    python3 -m pip install --upgrade pip
    python3 -m pip install --upgrade setuptools
    # python3 -m pip install --upgrade pybatfish
    git clone --branch minesweeper-v2021 https://github.com/yongzheng2024/pybatfish.git
    cd pybatfish
    pip install .
    cd ..
    rm -r pybatfish

    # upgrade pandas and numpy version
    pip install "pandas==2.2.3"
    pip install "numpy==2.2.3"

    # exit Python3 venv batfish-venv
    deactivate
}

install_for_macos() {
    echo "TODO ..."
}

"""
install_for_macos() {
    echo "Detected macOS system (${ARCH})"

    # install or check Homebrew
    if ! command -v brew &>/dev/null; then
        echo "Homebrew not found, installing..."
        /bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"
    fi

    # update Homebrew
    brew update

    # install or check OpenJDK 11
    if ! brew list openjdk@11 &>/dev/null; then
        echo "Installing OpenJDK 11..."
        brew install openjdk@11
        echo 'export PATH="/opt/homebrew/opt/openjdk@11/bin:$PATH"' >> ~/.zshrc
        echo 'export PATH="/opt/homebrew/opt/openjdk@11/bin:$PATH"' >> ~/.bashrc
        export PATH="/opt/homebrew/opt/openjdk@11/bin:$PATH"
    else
        echo "OpenJDK 11 is already installed."
    fi
    
    # install or check Bazel
    if ! command -v bazel &>/dev/null; then
        echo "Installing Bazel..."
        brew install bazel
    else
        echo "Bazel is already installed."
    fi

    # install or check Wget
    # if ! command -v wget &>/dev/null; then
    #     echo "Installing wget..."
    #     brew install wget
    # fi

    # Z3 download URL and relevant local archive file and relevant directory
    Z3_VERSION="4.14.0"
    Z3_OS="arm64-osx-13.7.2"
    Z3_BASENAME="z3-${Z3_VERSION}-${Z3_OS}"
    Z3_URL="https://github.com/Z3Prover/z3/releases/download/z3-${Z3_VERSION}/${Z3_BASENAME}.zip"
    Z3_ARCHIVE="${Z3_BASENAME}.zip"
    Z3_DIR="${Z3_BASENAME}"

    # Z3 shared library directory
    Z3_BIN_DIR="/usr/local/bin"
    Z3_INCLUDE_DIR="/usr/local/include"
    Z3_LIB_DIR="/usr/local/lib"

    # download or check Z3
    if [[ ! -f "$Z3_ARCHIVE" && ! -d "$Z3_DIR" ]]; then
        echo "Downloading Z3 from $Z3_URL..."
        # wget "$Z3_URL"
        curl -L -O "$Z3_URL"
    else
        echo "Z3 archive already exists, skipping download."
    fi

    # unzip Z3
    if [[ -d "$Z3_DIR" ]]; then
        echo "Z3 directory already exists, skipping extraction."
    else
        echo "Extracting Z3..."
        unzip "$Z3_ARCHIVE"
    fi

    # install Z3 shared library to system lib directory
    echo "install Z3 to $Z3_BIN_DIR $Z3_INCLUDE_DIR $Z3_LIB_DIR..."
    sudo mkdir -p $Z3_BIN_DIR
    sudo mkdir -p $Z3_INCLUDE_DIR
    sudo mkdir -p $Z3_LIB_DIR
    sudo cp "$Z3_DIR/bin/z3" "$Z3_BIN_DIR/z3"
    sudo find "$Z3_DIR/include" -type f -exec cp {} "$Z3_INCLUDE_DIR" \;
    # sudo rsync -a "$Z3_DIR/include/" "$Z3_INCLUDE_DIR/" 
    sudo cp "$Z3_DIR/bin/libz3java.dylib" "$Z3_LIB_DIR/libz3java.dylib"
    sudo cp "$Z3_DIR/bin/libz3.dylib" "$Z3_LIB_DIR/libz3.dylib"
    sudo cp "$Z3_DIR/bin/com.microsoft.z3.jar" "$Z3_LIB_DIR/com.microsoft.z3.jar"

    # update shared library cache
    echo "Updating shared library cache..."
    sudo chmod 755 "$Z3_LIB_DIR/libz3java.dylib"
    sudo chmod 755 "$Z3_LIB_DIR/libz3.dylib"
    sudo chown root:wheel "$Z3_LIB_DIR/libz3java.dylib"
    sudo chown root:wheel "$Z3_LIB_DIR/libz3.dylib"

    # remove apple quarantine
    echo "Remove apple network quarantine..."
    sudo xattr -d com.apple.quarantine "$Z3_LIB_DIR/libz3java.dylib"
    sudo xattr -d com.apple.quarantine "$Z3_LIB_DIR/libz3.dylib"

    # clean up Z3 archive file and relevant directory
    echo "Cleaning up Z3 installation files..."
    rm -f "$Z3_ARCHIVE"
    rm -rf "$Z3_DIR"

    # install or check Python3
    if ! command -v python3 &>/dev/null; then
        echo "Python3 is not installed. Installing it now..."
        brew install python3
        brew install python3-pip
    fi

    # Batfish Python3 venv `batfish-venv`
    VENV_NAME = "batfish-venv"

    # create Python3 venv `batfish-venv`
    echo "Creating virtual environment: $VENV_NAME..."
    python3 -m venv "$VENV_NAME"

    # activate Python3 venv `batfish-venv`
    echo "Activating virtual environment: $VENV_NAME..."
    source "$VENV_NAME/bin/activate"

    # upgrade Python3 pip
    echo "Upgrading python3 pip in Python3 venv $VENV_NAME..."
    python3 -m pip install --upgrade pip

    # install setuptools (pkg_resources) in Python3 venv `batfish-venv`
    echo "Install setuptools in Python3 venv $VENV_NAME..."
    python3 -m pip install --upgrade setuptools

    # install Pybatfish in Python3 venv `batfish-venv`
    echo "Install Pybatfish in Python3 venv $VENV_NAME..."
    python3 -m pip install --upgrade pybatfish

    # exit Python3 venv `batfish-venv`
    echo "Deactivate virtual environment: $VENV_NAME..."
    deactivate

    echo 'export PATH="/usr/local/bin:$PATH"' >> ~/.zshrc
    echo 'export PATH="/usr/local/bin:$PATH"' >> ~/.bashrc
    echo 'export CPATH="/usr/local/include${CPATH:+:$CPATH}"' >> ~/.zshrc
    echo 'export CPATH="/usr/local/include${CPATH:+:$CPATH}"' >> ~/.bashrc
    echo 'export LIBRARY_PATH="/usr/local/lib${LIBRARY_PATH:+:$LIBRARY_PATH}"' >> ~/.zshrc
    echo 'export LIBRARY_PATH="/usr/local/lib${LIBRARY_PATH:+:$LIBRARY_PATH}"' >> ~/.bashrc
    echo 'export DYLD_LIBRARY_PATH="/usr/local/lib${DYLD_LIBRARY_PATH:+:$DYLD_LIBRARY_PATH}"' >> ~/.zshrc
    echo 'export DYLD_LIBRARY_PATH="/usr/local/lib${DYLD_LIBRARY_PATH:+:$DYLD_LIBRARY_PATH}"' >> ~/.bashrc
    export PATH="/usr/local/bin:$PATH"
    export CPATH="/usr/local/include${CPATH:+:$CPATH}"
    export LIBRARY_PATH="/usr/local/lib${LIBRARY_PATH:+:$LIBRARY_PATH}"
    export DYLD_LIBRARY_PATH="/usr/local/lib${DYLD_LIBRARY_PATH:+:$DYLD_LIBRARY_PATH}"
    
    # add DYLD_LIBRARY_PATH export command to ~/.zshrc
    # ZSH_CONFIG_FILE="$HOME/.zshrc"
    # BASH_CONFIG_FILE="$HOME/.bashrc"
    # EXPORT_CMD="export DYLD_LIBRARY_PATH=$Z3_LIB_DIR\${DYLD_LIBRARY_PATH:+:\$DYLD_LIBRARY_PATH}"

    # if ! grep -Fxq "$EXPORT_CMD" "$ZSH_CONFIG_FILE"; then
    #     echo "Add DYLD_LIBRARY_PATH to $ZSH_CONFIG_FILE..."
    #     echo "$EXPORT_CMD" | sudo tee -a "$ZSH_CONFIG_FILE" > /dev/null
    # else
    #     echo "DYLD_LIBRARY_PATH already exists in $ZSH_CONFIG_FILE, no need to add it again"
    # fi

    # if ! grep -Fxq "$EXPORT_CMD" "$BASH_CONFIG_FILE"; then
    #     echo "Add DYLD_LIBRARY_PATH to $BASH_CONFIG_FILE..."
    #     echo "$EXPORT_CMD" | sudo tee -a "$BASH_CONFIG_FILE" > /dev/null
    # else
    #     echo "DYLD_LIBRARY_PATH already exists in $BASH_CONFIG_FILE, no need to add it again"
    # fi
}
"""

# install batfish/minesweeper/pybatfish/z3 according to $OS and $ARCH
case "$OS" in
    "Linux")
        install_for_linux
        ;;
    "Darwin")
        if [[ "$ARCH" == "arm64" ]]; then
            install_for_macos
        else
            echo "Unsupported macOS architecture: $ARCH"
            exit 1
        fi
        ;;
    *)
        echo "Unsupported OS: $OS"
        exit 1
        ;;
esac

echo "Installation completed!"
