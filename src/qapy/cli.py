import argparse
import dill

from pymcl import r as ρ

from .types import Witness
from .compiler import Compiler
from .groth16 import PKey, VKey, Proof, setup, prove, verify


class StoreKVPairs(argparse.Action):
    def __call__(self, parser, namespace, values, option_string=None):
        result = {}
        for value in values:
            k, _, v = value.rpartition("=")
            result[k] = int(v, 0) % ρ
        setattr(namespace, self.dest, result)


def main():
    parser = argparse.ArgumentParser(description="QAPy Compiler and Groth16 Prover/Verifier")

    subparsers = parser.add_subparsers(dest="command", required=True, help="sub-command")

    parser_compile = subparsers.add_parser("compile", help="compile the source code", description="Compile the source code and write the constraints, witness generation functions, and public entry names to files.")
    parser_compile.add_argument("file", type=str, help="path to the source code")
    parser_compile.add_argument("-g", "--gates", type=str, default=None, help="path to write the constraints to (default: a.gates)")
    parser_compile.add_argument("-f", "--funcs", type=str, default=None, help="path to write the witness generation functions to (default: a.funcs)")
    parser_compile.add_argument("-n", "--names", type=str, default=None, help="path to write the public entry names to (default: a.names)")

    parser_setup = subparsers.add_parser("setup", help="set up the parameters", description="Set up the parameters for proving and verifying and write them to files.")
    parser_setup.add_argument("file", type=str, nargs="?", help="path to the source code")
    parser_setup.add_argument("-g", "--gates", type=str, default=None, help="path to read the constraints from (default: a.gates)")
    parser_setup.add_argument("-p", "--pk", type=str, default="a.pk", help="path to write the parameters for proving to (default: a.pk)")
    parser_setup.add_argument("-v", "--vk", type=str, default="a.vk", help="path to write the parameters for verifying to (default: a.vk)")

    parser_prove = subparsers.add_parser("prove", help="generate a proof", description="Generate a proof and write it to a file")
    parser_prove.add_argument("file", type=str, nargs="?", help="path to the source code")
    parser_prove.add_argument("-g", "--gates", type=str, default=None, help="path to read the constraints from (default: a.gates)")
    parser_prove.add_argument("-f", "--funcs", type=str, default=None, help="path to read the witness generation functions from (default: a.funcs)")
    parser_prove.add_argument("-p", "--pk", type=str, default="a.pk", help="path to read the parameters for proving from (default: a.pk)")
    parser_prove.add_argument("-a", "--args", action=StoreKVPairs, nargs="*", default={}, help="the arguments to the program as key=value pairs")
    parser_prove.add_argument("-P", "--proof", type=str, default="a.proof", help="path to write the proof to (default: a.proof)")

    parser_verify = subparsers.add_parser("verify", help="verify a proof", description="Verify a proof")
    parser_verify.add_argument("file", type=str, nargs="?", help="path to the source code")
    parser_verify.add_argument("-n", "--names", type=str, default=None, help="path to read the public entry names from (default: a.names)")
    parser_verify.add_argument("-v", "--vk", type=str, default="a.vk", help="path to read the parameters for verifying from (default: a.vk)")
    parser_verify.add_argument("-P", "--proof", type=str, default="a.proof", help="path to read the proof from (default: a.proof)")

    args = parser.parse_args()

    if args.command == "compile":
        compiler = Compiler()
        with open(args.file, "r") as file:
            print("Compiling the source code...")
            compiler.compile(file.read())
        wire_count = compiler.wire_count
        skeys = compiler.stmts.keys()
        gates = compiler.gates
        funcs = compiler.funcs
        names = compiler.stmts.values()

        print("Dimension of the witness vector:", wire_count)
        print("Number of constraints:", len(gates))
        print("Number of public entries:", len(skeys))

        if args.gates is not None:
            with open(args.gates, "wb") as gates_file:
                print("Saving constraints to:", args.gates)
                gates_file.write(dill.dumps((wire_count, skeys, gates)))

        if args.funcs is not None:
            with open(args.funcs, "wb") as funcs_file:
                print("Saving witness generation functions to:", args.funcs)
                funcs_file.write(dill.dumps(funcs))

        if args.names is not None:
            with open(args.names, "wb") as names_file:
                print("Saving public entry names to:", args.names)
                names_file.write(dill.dumps(names))

    elif args.command == "setup":
        if args.file is not None:
            compiler = Compiler()
            with open(args.file, "r") as file:
                print("Compiling the source code...")
                compiler.compile(file.read())
            wire_count = compiler.wire_count
            skeys = compiler.stmts.keys()
            gates = compiler.gates
        elif args.gates is not None:
            with open(args.gates, "rb") as gates_file:
                print("Loading constraints from:", args.gates)
                wire_count, skeys, gates = dill.loads(gates_file.read())
        else:
            raise ValueError("--gates must be provided for setup if source code is not given.")

        print("Setting up parameters for proving and verifying...")
        key = setup(wire_count, skeys, gates)
        pk = key.get_pk()
        vk = key.get_vk()

        with open(args.pk, "wb") as pk_file:
            print("Saving parameters for proving to:", args.pk)
            pk.dumps(pk_file)

        with open(args.vk, "wb") as vk_file:
            print("Saving parameters for verifying to:", args.vk)
            vk.dumps(vk_file)

    elif args.command == "prove":
        if args.file is not None:
            compiler = Compiler()
            with open(args.file, "r") as file:
                print("Compiling the source code...")
                compiler.compile(file.read())
            wire_count = compiler.wire_count
            skeys = compiler.stmts.keys()
            gates = compiler.gates
            funcs = compiler.funcs
        elif args.gates is not None and args.funcs is not None:
            with open(args.gates, "rb") as gates_file:
                print("Loading constraints from:", args.gates)
                wire_count, skeys, gates = dill.loads(gates_file.read())
            with open(args.funcs, "rb") as funcs_file:
                print("Loading witness generation functions from:", args.funcs)
                funcs = dill.loads(funcs_file.read())
        else:
            raise ValueError("--gates and --funcs must be provided for proving if source code is not given.")

        with open(args.pk, "rb") as pk_file:
            print("Loading parameters for proving from:", args.pk)
            pk = PKey.loads(pk_file, wire_count, len(gates), len(skeys))

        print("Generating witness...")
        witness = Witness(funcs, args.args)

        print("Generating proof...")
        proof = prove(wire_count, skeys, gates, pk, witness)

        with open(args.proof, "wb") as proof_file:
            print("Saving proof to:", args.proof)
            proof.dumps(proof_file)

    elif args.command == "verify":
        if args.file is not None:
            compiler = Compiler()
            with open(args.file, "r") as file:
                print("Compiling the source code...")
                compiler.compile(file.read())
            names = list(compiler.stmts.values())
        elif args.names is not None:
            with open(args.names, "rb") as names_file:
                print("Loading public entry names from:", args.names)
                names = dill.loads(names_file.read())
        else:
            raise ValueError("--names must be provided for verifying if source code is not given.")

        with open(args.vk, "rb") as vk_file:
            print("Loading parameters for verifying from:", args.vk)
            vk = VKey.loads(vk_file, len(names))

        with open(args.proof, "rb") as proof_file:
            print("Loading proof from:", args.proof)
            proof = Proof.loads(proof_file, len(names))

        print("Verifying proof...")
        result = verify(names, vk, proof)

        if result.passed:
            print("Verification passed!")
            print("Public entries:", "{" + ", ".join(f"{k} = {u}" for k, u in result.values) + "}")
        else:
            print("Verification failed!")


if __name__ == "__main__":
    main()
