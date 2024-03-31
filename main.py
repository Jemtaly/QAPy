#!/usr/bin/python3
import compiler
import groth16
import argparse
import dill
import pymcl
ρ = pymcl.r
L0 = ((ρ - 1).bit_length() + 7) // 8
L1 = len(pymcl.g1.serialize())
L2 = len(pymcl.g2.serialize())
class StoreDictKeyPair(argparse.Action):
    def __call__(self, parser, namespace, values, option_string = None):
        result = {}
        for value in values:
            k, _, v = value.rpartition('=')
            result[k] = int(v, 0) % ρ
        setattr(namespace, self.dest, result)
def main():
    parser = argparse.ArgumentParser(description = 'QAPy Compiler and Groth16 Prover/Verifier')
    subparsers = parser.add_subparsers(dest = 'command', required = True, help = 'The command to run.')
    parser_compile = subparsers.add_parser('compile', help = 'Compile a program.', description = 'Compile a program and write the constraints, witness generation functions, and public variable names to files.')
    parser_compile.add_argument('program', type = str, help = 'The program to compile.')
    parser_compile.add_argument('-g', '--gates', type = str, default = 'a.gates', help = 'The file to write the constraints to. (Default: a.gates)')
    parser_compile.add_argument('-f', '--funcs', type = str, default = 'a.funcs', help = 'The file to write the witness generation functions to. (Default: a.funcs)')
    parser_compile.add_argument('-n', '--names', type = str, default = 'a.names', help = 'The file to write the public variable names to. (Default: a.names)')
    parser_setup = subparsers.add_parser('setup', help = 'Set up the parameters for proving and verifying.', description = 'Set up the parameters for proving and verifying and write them to files.')
    parser_setup.add_argument('-g', '--gates', type = str, default = 'a.gates', help = 'The file to read the constraints from. (Default: a.gates)')
    parser_setup.add_argument('-p', '--prove', type = str, default = 'a.prove', help = 'The file to write the parameters for proving to. (Default: a.prove)')
    parser_setup.add_argument('-v', '--verif', type = str, default = 'a.verif', help = 'The file to write the parameters for verifying to. (Default: a.verif)')
    parser_prove = subparsers.add_parser('prove', help = 'Generate a proof.', description = 'Generate a proof and write it to a file.')
    parser_prove.add_argument('-g', '--gates', type = str, default = 'a.gates', help = 'The file to read the constraints from. (Default: a.gates)')
    parser_prove.add_argument('-f', '--funcs', type = str, default = 'a.funcs', help = 'The file to read the witness generation functions from. (Default: a.funcs)')
    parser_prove.add_argument('-p', '--prove', type = str, default = 'a.prove', help = 'The file to read the parameters for proving from. (Default: a.prove)')
    parser_prove.add_argument('-a', '--args', action = StoreDictKeyPair, nargs = '*', default = {}, help = 'The arguments to the program, in the form of key=value pairs.')
    parser_prove.add_argument('-P', '--proof', type = str, default = 'a.proof', help = 'The file to write the proof to. (Default: a.proof)')
    parser_verif = subparsers.add_parser('verify', help = 'Verify a proof.', description = 'Verify a proof.')
    parser_verif.add_argument('-n', '--names', type = str, default = 'a.names', help = 'The file to read the public variable names from. (Default: a.names)')
    parser_verif.add_argument('-v', '--verif', type = str, default = 'a.verif', help = 'The file to read the parameters for verifying from. (Default: a.verif)')
    parser_verif.add_argument('-P', '--proof', type = str, default = 'a.proof', help = 'The file to read the proof from. (Default: a.proof)')
    args = parser.parse_args()
    if args.command == 'compile':
        test = compiler.Compiler()
        with open(args.program, 'r') as program:
            print('Compiling program...')
            test.compile(program.read())
        print('Length of the witness vector:', test.wire_count)
        print('Number of constraints:', len(test.gates))
        print('Number of public variables:', len(test.stmts))
        with open(args.gates, 'wb') as gates:
            print('Writing constraints to', args.gates)
            gates.write(dill.dumps((test.wire_count, test.stmts.keys(), test.gates)))
        with open(args.funcs, 'wb') as funcs:
            print('Writing witness generation functions to', args.funcs)
            funcs.write(dill.dumps(test.funcs))
        with open(args.names, 'wb') as names:
            print('Writing public variable names to', args.names)
            names.write(dill.dumps(test.stmts.values()))
        # A malicious attacker can tamper with the above files, allowing them to execute arbitrary code when the user loads
        # the files, so it is recommended that the party executing the compilation sign the files before distributing them.
    elif args.command == 'setup':
        with open(args.gates, 'rb') as gates:
            print('Loading constraints from', args.gates)
            wire_count, skeys, gates = dill.loads(gates.read())
        print('Setting up parameters for proving and verifying...')
        α1, β1, δ1, β2, γ2, δ2, u1U, v1V, x1I, x2I, y1I = groth16.setup(wire_count, skeys, gates)
        with open(args.prove, 'wb') as prove:
            print('Writing parameters for proving to', args.prove)
            prove.write(α1.serialize())
            prove.write(β1.serialize())
            prove.write(δ1.serialize())
            prove.write(β2.serialize())
            prove.write(δ2.serialize())
            for v1 in v1V: prove.write(v1.serialize())
            for x1 in x1I: prove.write(x1.serialize())
            for x2 in x2I: prove.write(x2.serialize())
            for y1 in y1I: prove.write(y1.serialize())
        with open(args.verif, 'wb') as verif:
            print('Writing parameters for verifying to', args.verif)
            verif.write(α1.serialize())
            verif.write(β2.serialize())
            verif.write(γ2.serialize())
            verif.write(δ2.serialize())
            for u1 in u1U: verif.write(u1.serialize())
    elif args.command == 'prove':
        with open(args.gates, 'rb') as gates:
            print('Loading constraints from', args.gates)
            wire_count, skeys, gates = dill.loads(gates.read())
        with open(args.funcs, 'rb') as funcs:
            print('Loading witness generation functions from', args.funcs)
            funcs = dill.loads(funcs.read())
        N = len(gates)
        M = wire_count
        U = len(skeys)
        V = M - U
        I = 1 << (N - 1).bit_length()
        with open(args.prove, 'rb') as prove:
            print('Loading parameters for proving from', args.prove)
            α1 = pymcl.G1.deserialize(prove.read(L1))
            β1 = pymcl.G1.deserialize(prove.read(L1))
            δ1 = pymcl.G1.deserialize(prove.read(L1))
            β2 = pymcl.G2.deserialize(prove.read(L2))
            δ2 = pymcl.G2.deserialize(prove.read(L2))
            v1V = [pymcl.G1.deserialize(prove.read(L1)) for _ in range(V)]
            x1I = [pymcl.G1.deserialize(prove.read(L1)) for _ in range(I)]
            x2I = [pymcl.G2.deserialize(prove.read(L2)) for _ in range(I)]
            y1I = [pymcl.G1.deserialize(prove.read(L1)) for _ in range(I)]
        print('Generating proof...')
        A1, B2, C1, uU = groth16.prove(wire_count, funcs, skeys, gates, α1, β1, δ1, β2, δ2, v1V, x1I, x2I, y1I, args.args)
        with open(args.proof, 'wb') as proof:
            print('Writing proof to', args.proof)
            proof.write(A1.serialize())
            proof.write(B2.serialize())
            proof.write(C1.serialize())
            for u in uU: proof.write(u.to_bytes(L0, 'big'))
    elif args.command == 'verify':
        with open(args.names, 'rb') as names:
            print('Loading public variable names from', args.names)
            names = dill.loads(names.read())
        U = len(names)
        with open(args.verif, 'rb') as verif:
            print('Loading parameters for verifying from', args.verif)
            α1 = pymcl.G1.deserialize(verif.read(L1))
            β2 = pymcl.G2.deserialize(verif.read(L2))
            γ2 = pymcl.G2.deserialize(verif.read(L2))
            δ2 = pymcl.G2.deserialize(verif.read(L2))
            u1U = [pymcl.G1.deserialize(verif.read(L1)) for _ in range(U)]
        with open(args.proof, 'rb') as proof:
            print('Loading proof from', args.proof)
            A1 = pymcl.G1.deserialize(proof.read(L1))
            B2 = pymcl.G2.deserialize(proof.read(L2))
            C1 = pymcl.G1.deserialize(proof.read(L1))
            uU = [int.from_bytes(proof.read(L0), 'big') for _ in range(U)]
        print('Verifying proof...')
        passed, outs = groth16.verify(names, α1, β2, γ2, δ2, u1U, A1, B2, C1, uU)
        if passed:
            print('Verification passed!')
            print('Public witness:', '{{{}}}'.format(', '.join('{} = {}'.format(k, u) for k, u in outs)))
        else:
            print('Verification failed!')
if __name__ == '__main__':
    main()
