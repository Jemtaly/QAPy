#!/usr/bin/env python3

import argparse
import dill

import compiler
import groth16
from pymcl import G1, G2, g1, g2, r as ρ


L0 = ((ρ - 1).bit_length() + 7) // 8
L1 = len(g1.serialize())
L2 = len(g2.serialize())


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
    parser_compile.add_argument("-g", "--gates", type=str, default="a.gates", help="path to write the constraints to (default: a.gates)")
    parser_compile.add_argument("-f", "--funcs", type=str, default="a.funcs", help="path to write the witness generation functions to (default: a.funcs)")
    parser_compile.add_argument("-n", "--names", type=str, default="a.names", help="path to write the public entry names to (default: a.names)")

    parser_setup = subparsers.add_parser("setup", help="set up the parameters", description="Set up the parameters for proving and verifying and write them to files.")
    parser_setup.add_argument("-g", "--gates", type=str, default="a.gates", help="path to read the constraints from (default: a.gates)")
    parser_setup.add_argument("-p", "--prove", type=str, default="a.prove", help="path to write the parameters for proving to (default: a.prove)")
    parser_setup.add_argument("-v", "--verif", type=str, default="a.verif", help="path to write the parameters for verifying to (default: a.verif)")

    parser_prove = subparsers.add_parser("prove", help="generate a proof", description="Generate a proof and write it to a file")
    parser_prove.add_argument("-g", "--gates", type=str, default="a.gates", help="path to read the constraints from (default: a.gates)")
    parser_prove.add_argument("-f", "--funcs", type=str, default="a.funcs", help="path to read the witness generation functions from (default: a.funcs)")
    parser_prove.add_argument("-p", "--prove", type=str, default="a.prove", help="path to read the parameters for proving from (default: a.prove)")
    parser_prove.add_argument("-a", "--args", action=StoreKVPairs, nargs="*", default={}, help="the arguments to the program as key=value pairs")
    parser_prove.add_argument("-P", "--proof", type=str, default="a.proof", help="path to write the proof to (default: a.proof)")

    parser_verif = subparsers.add_parser("verify", help="verify a proof", description="Verify a proof")
    parser_verif.add_argument("-n", "--names", type=str, default="a.names", help="path to read the public entry names from (default: a.names)")
    parser_verif.add_argument("-v", "--verif", type=str, default="a.verif", help="path to read the parameters for verifying from (default: a.verif)")
    parser_verif.add_argument("-P", "--proof", type=str, default="a.proof", help="path to read the proof from (default: a.proof)")

    args = parser.parse_args()

    if args.command == "compile":
        test = compiler.Compiler()
        with open(args.file, "r") as file:
            print("Compiling the source code...")
            test.compile(file.read())
        print("Dimension of the witness vector:", test.wire_count)
        print("Number of constraints:", len(test.gates))
        print("Number of public entries:", len(test.stmts))
        with open(args.gates, "wb") as gates:
            print("Saving constraints to:", args.gates)
            gates.write(dill.dumps((test.wire_count, test.stmts.keys(), test.gates)))
        with open(args.funcs, "wb") as funcs:
            print("Saving witness generation functions to:", args.funcs)
            funcs.write(dill.dumps(test.funcs))
        with open(args.names, "wb") as names:
            print("Saving public entry names to:", args.names)
            names.write(dill.dumps(test.stmts.values()))
        # A malicious attacker can tamper with the above files, allowing them to execute arbitrary code when the user loads
        # the files, so it is recommended that the party executing the compilation sign the files before distributing them.

    elif args.command == "setup":
        with open(args.gates, "rb") as gates:
            print("Loading constraints from:", args.gates)
            wire_count, skeys, gates = dill.loads(gates.read())
        print("Setting up parameters for proving and verifying...")
        α1, β1, δ1, β2, γ2, δ2, u1U, v1V, x1I, x2I, y1I = groth16.setup(wire_count, skeys, gates)
        with open(args.prove, "wb") as prove:
            print("Saving parameters for proving to:", args.prove)
            prove.write(α1.serialize())
            prove.write(β1.serialize())
            prove.write(δ1.serialize())
            prove.write(β2.serialize())
            prove.write(δ2.serialize())
            for v1 in v1V:
                prove.write(v1.serialize())
            for x1 in x1I:
                prove.write(x1.serialize())
            for x2 in x2I:
                prove.write(x2.serialize())
            for y1 in y1I:
                prove.write(y1.serialize())
        with open(args.verif, "wb") as verif:
            print("Saving parameters for verifying to:", args.verif)
            verif.write(α1.serialize())
            verif.write(β2.serialize())
            verif.write(γ2.serialize())
            verif.write(δ2.serialize())
            for u1 in u1U:
                verif.write(u1.serialize())

    elif args.command == "prove":
        with open(args.gates, "rb") as gates:
            print("Loading constraints from:", args.gates)
            wire_count, skeys, gates = dill.loads(gates.read())
        with open(args.funcs, "rb") as funcs:
            print("Loading witness generation functions from:", args.funcs)
            funcs = dill.loads(funcs.read())
        N = len(gates)
        M = wire_count
        U = len(skeys)
        V = M - U
        I = 1 << (N - 1).bit_length()
        with open(args.prove, "rb") as prove:
            print("Loading parameters for proving from:", args.prove)
            α1 = G1.deserialize(prove.read(L1))
            β1 = G1.deserialize(prove.read(L1))
            δ1 = G1.deserialize(prove.read(L1))
            β2 = G2.deserialize(prove.read(L2))
            δ2 = G2.deserialize(prove.read(L2))
            v1V = [G1.deserialize(prove.read(L1)) for _ in range(V)]
            x1I = [G1.deserialize(prove.read(L1)) for _ in range(I)]
            x2I = [G2.deserialize(prove.read(L2)) for _ in range(I)]
            y1I = [G1.deserialize(prove.read(L1)) for _ in range(I)]
        print("Generating proof...")
        A1, B2, C1, uU = groth16.prove(wire_count, funcs, skeys, gates, α1, β1, δ1, β2, δ2, v1V, x1I, x2I, y1I, args.args)
        with open(args.proof, "wb") as proof:
            print("Saving proof to:", args.proof)
            proof.write(A1.serialize())
            proof.write(B2.serialize())
            proof.write(C1.serialize())
            for u in uU:
                proof.write(u.to_bytes(L0, "big"))

    elif args.command == "verify":
        with open(args.names, "rb") as names:
            print("Loading public entry names from:", args.names)
            names = dill.loads(names.read())
        U = len(names)
        with open(args.verif, "rb") as verif:
            print("Loading parameters for verifying from:", args.verif)
            α1 = G1.deserialize(verif.read(L1))
            β2 = G2.deserialize(verif.read(L2))
            γ2 = G2.deserialize(verif.read(L2))
            δ2 = G2.deserialize(verif.read(L2))
            u1U = [G1.deserialize(verif.read(L1)) for _ in range(U)]
        with open(args.proof, "rb") as proof:
            print("Loading proof from:", args.proof)
            A1 = G1.deserialize(proof.read(L1))
            B2 = G2.deserialize(proof.read(L2))
            C1 = G1.deserialize(proof.read(L1))
            uU = [int.from_bytes(proof.read(L0), "big") for _ in range(U)]
        print("Verifying proof...")
        passed, outs = groth16.verify(names, α1, β2, γ2, δ2, u1U, A1, B2, C1, uU)
        if passed:
            print("Verification passed!")
            print("Public entries:", "{{{}}}".format(", ".join("{} = {}".format(k, u) for k, u in outs)))
        else:
            print("Verification failed!")


if __name__ == "__main__":
    main()
