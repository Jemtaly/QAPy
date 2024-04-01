# QAPy

A QAP compiler implemented in Python, used to compile the codes written in a Python-like programming laguage into its QAP form, and perform setup, proof and verification steps of [Groth16](https://eprint.iacr.org/2016/260.pdf).

## Requirements

- Python 3.9+
- [pymcl](https://github.com/Jemtaly/pymcl)
- dill

## Usage

QAPy provides a command-line tool, `main.py`, for compiling programs and performing Groth16 parameter setup, proof generation, and verification steps. The following is a brief introduction to the usage of the tool.

### Compile

```text
usage: main.py compile [-h] [-g GATES] [-f FUNCS] [-n NAMES] program

Compile a program and write the constraints, witness generation functions, and public entry names to files.

positional arguments:
  program     The program to compile.

options:
  -h, --help  show this help message and exit
  -g GATES    The file to write the constraints to. (Default: a.gates)
  -f FUNCS    The file to write the witness generation functions to. (Default: a.funcs)
  -n NAMES    The file to write the public entry names to. (Default: a.names)
```

### Setup

```text
usage: main.py setup [-h] [-g GATES] [-p PROVE] [-v VERIF]

Set up the parameters for proving and verifying and write them to files.

options:
  -h, --help  show this help message and exit
  -g GATES    The file to read the constraints from. (Default: a.gates)
  -p PROVE    The file to write the parameters for proving to. (Default: a.prove)
  -v VERIF    The file to write the parameters for verifying to. (Default: a.verif)
```

### Prove

```text
usage: main.py prove [-h] [-g GATES] [-f FUNCS] [-p PROVE] [-a [ARGS ...]] [-P PROOF]

Generate a proof and write it to a file.

options:
  -h, --help  show this help message and exit
  -g GATES    The file to read the constraints from. (Default: a.gates)
  -f FUNCS    The file to read the witness generation functions from. (Default: a.funcs)
  -p PROVE    The file to read the parameters for proving from. (Default: a.prove)
  -a [ARGS ...], --args [ARGS ...]
              The arguments to the program, in the form of key=value pairs.
  -P PROOF    The file to write the proof to. (Default: a.proof)
```

### Verify

```text
usage: main.py verify [-h] [-n NAMES] [-v VERIF] [-P PROOF]

Verify a proof.

options:
  -h, --help  show this help message and exit
  -n NAMES    The file to read the public entry names from. (Default: a.names)
  -v VERIF    The file to read the parameters for verifying from. (Default: a.verif)
  -P PROOF    The file to read the proof from. (Default: a.proof)
```

There are several sample codes in the `examples` directory. Take `examples/sha256.qapy` as an example, which performs a SHA-256 compression function without padding on one block of input data and outputs the hash value. You can compile, setup, prove, and verify it by running the following commands:

```bash
# Compile the program
./main.py compile examples/sha256.qapy -g sha256.gates -f sha256.funcs -n sha256.names

# Setup the parameters
./main.py setup -g sha256.gates -p sha256.prove -v sha256.verif

# Generate the proof (take the padded message "abc" as input)
./main.py prove -g sha256.gates -f sha256.funcs -p sha256.prove -a \
    W[0]=0x61626380 W[1]=0 W[2]=0 W[3]=0 W[4]=0 W[5]=0 W[6]=0 W[7]=0 \
    W[8]=0 W[9]=0 W[10]=0 W[11]=0 W[12]=0 W[13]=0 W[14]=0 W[15]=24 \
    -P sha256.proof

# Verify the proof
./main.py verify -n sha256.names -v sha256.verif -P sha256.proof
```

## Copyright Notice

This project is my ongoing undergraduate graduation project. It is currently completely experimental and cannot be used for production. Copying, modification, and redistribution of the code in this repository without permission is prohibited. If you have any needs, please submit an issue or contact me via email: [Jemtaly@outlook.com](mailto:Jemtaly@outlook.com).
