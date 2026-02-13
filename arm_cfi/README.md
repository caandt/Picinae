# ARMv7 CFI Binary Rewriter

Currently, it only uses a trivial policy (every address can go to every other address)

## Requirements

### Hardware / OS requirements

XXXX

### Software Package

#### nix-shell

First, you need to install [nix]().

- OCaml
    - Domainslib
    - Findlib
- Python
    - LIEF
- ARMv7 GCC Toolchain

You can get all of the dependencies with `nix-shell`

## Usage

```sh
./rewrite.sh <input binary> <output binary>
```

The input should be a static non-PIE binary
