# QAPy

A QAP compiler implemented in Python, used to compile the codes written in a Python-like programming laguage into its QAP form, and perform setup, proof and verification steps of [Groth16](https://eprint.iacr.org/2016/260.pdf).

## Requirements

- Python 3.9+
- [pymcl](https://github.com/Jemtaly/pymcl)
- dill

## Usage

QAPy provides a command-line tool for compiling programs and performing Groth16 parameter setup, proof generation, and verification steps. The following is a brief introduction to the usage of the tool.

```sh
git clone https://github.com/Jemtaly/QAPy
cd QAPy
pip install -e .
qapy-test
```

### Compile

```text
usage: qapy compile [-h] [-g GATES] [-f FUNCS] [-n NAMES] program

Compile a program and write the constraints, witness generation functions, and public entry names to files.

positional arguments:
  program     path of the source code

options:
  -h, --help  show this help message and exit
  -g GATES    path to write the constraints to (default: a.gates)
  -f FUNCS    path to write the witness generation functions to (default: a.funcs)
  -n NAMES    path to write the public entry names to (default: a.names)
```

### Setup

```text
usage: qapy setup [-h] [-g GATES] [-p PROVE] [-v VERIF]

Set up the parameters for proving and verifying and write them to files.

options:
  -h, --help  show this help message and exit
  -g GATES    path to read the constraints from (default: a.gates)
  -p PROVE    path to write the parameters for proving to (default: a.prove)
  -v VERIF    path to write the parameters for verifying to (default: a.verif)
```

### Prove

```text
usage: qapy prove [-h] [-g GATES] [-f FUNCS] [-p PROVE] [-a [ARGS ...]] [-P PROOF]

Generate a proof and write it to a file.

options:
  -h, --help  show this help message and exit
  -g GATES    path to read the constraints from (default: a.gates)
  -f FUNCS    path to read the witness generation functions from (default: a.funcs)
  -p PROVE    path to read the parameters for proving from (default: a.prove)
  -a [ARGS ...], --args [ARGS ...]
              the arguments to the program as key=value pairs
  -P PROOF    path to write the proof to (default: a.proof)
```

### Verify

```text
usage: qapy verify [-h] [-n NAMES] [-v VERIF] [-P PROOF]

Verify a proof.

options:
  -h, --help  show this help message and exit
  -n NAMES    path to read the public entry names from (default: a.names)
  -v VERIF    path to read the parameters for verifying from (default: a.verif)
  -P PROOF    path to read the proof from (default: a.proof)
```

There are several sample codes in the `examples` directory. Take `examples/sha256.qapy` as an example, which performs a SHA-256 compression function without padding on one block of input data and outputs the hash value. You can compile, setup, prove, and verify it by running the following commands:

```bash
# Compile the program
qapy compile examples/sha256.qapy -g sha256.gates -f sha256.funcs -n sha256.names

# Setup the parameters
qapy setup -g sha256.gates -p sha256.pk -v sha256.vk

# Generate the proof (take the padded message "abc" as input)
qapy prove -g sha256.gates -f sha256.funcs -p sha256.pk -a \
    W[0]=0x61626380 W[1]=0 W[2]=0 W[3]=0 W[4]=0 W[5]=0 W[6]=0 W[7]=0 \
    W[8]=0 W[9]=0 W[10]=0 W[11]=0 W[12]=0 W[13]=0 W[14]=0 W[15]=24 \
    -P sha256.proof

# Verify the proof
qapy verify -n sha256.names -v sha256.vk -P sha256.proof
```

No compilation mode:

```bash
# Setup the parameters
qapy setup examples/sha256.qapy -p sha256.pk -v sha256.vk

# Generate the proof (take the padded message "abc" as input)
qapy prove examples/sha256.qapy -p sha256.pk -a \
    W[0]=0x61626380 W[1]=0 W[2]=0 W[3]=0 W[4]=0 W[5]=0 W[6]=0 W[7]=0 \
    W[8]=0 W[9]=0 W[10]=0 W[11]=0 W[12]=0 W[13]=0 W[14]=0 W[15]=24 \
    -P sha256.proof

# Verify the proof
qapy verify examples/sha256.qapy -v sha256.vk -P sha256.proof
```

## Copyright Notice

This project is my ongoing undergraduate graduation project. It is currently completely experimental and cannot be used for production. Copying, modification, and redistribution of the code in this repository without permission is prohibited. If you have any needs, please submit an issue or contact me via email: [Jemtaly@outlook.com](mailto:Jemtaly@outlook.com).
