#!/usr/bin/python3
import compiler
import groth16
import argparse
import sys
import dill
import pymcl
ρ = pymcl.r
class StoreDictKeyPair(argparse.Action):
    def __call__(self, parser, namespace, values, option_string = None):
        result = {}
        for value in values:
            k, v = value.split('=')
            result[k] = int(v, 0) % ρ
        setattr(namespace, self.dest, result)
def main():
    parser = argparse.ArgumentParser(description = 'zkSNARKs in Python.')
    subparsers = parser.add_subparsers(dest = 'command', help = 'The command to run.')
    parser_compile = subparsers.add_parser('compile', help = 'Compile a program.')
    parser_compile.add_argument('program', type = str, help = 'The program to compile.')
    parser_compile.add_argument('-g', '--gates', type = str, default = 'a.gates', help = 'The file to write the gates to. (Default: a.gates)')
    parser_compile.add_argument('-w', '--wires', type = str, default = 'a.wires', help = 'The file to write the wires to. (Default: a.wires)')
    parser_compile.add_argument('-n', '--names', type = str, default = 'a.names', help = 'The file to write the public names to. (Default: a.names)')
    parser_setup = subparsers.add_parser('setup', help = 'Set up the parameters for proving and verifying.')
    parser_setup.add_argument('-g', '--gates', type = str, default = 'a.gates', help = 'The file to read the gates from. (Default: a.gates)')
    parser_setup.add_argument('-p', '--prove', type = str, default = 'a.prove', help = 'The file to write the parameters for proving to. (Default: a.prove)')
    parser_setup.add_argument('-v', '--verif', type = str, default = 'a.verif', help = 'The file to write the parameters for verifying to. (Default: a.verif)')
    parser_prove = subparsers.add_parser('prove', help = 'Generate a proof.')
    parser_prove.add_argument('-g', '--gates', type = str, default = 'a.gates', help = 'The file to read the gates from. (Default: a.gates)')
    parser_prove.add_argument('-w', '--wires', type = str, default = 'a.wires', help = 'The file to read the wires from. (Default: a.wires)')
    parser_prove.add_argument('-p', '--prove', type = str, default = 'a.prove', help = 'The file to read the parameters for proving from. (Default: a.prove)')
    parser_prove.add_argument('-a', '--args', action = StoreDictKeyPair, nargs = '*', default = {}, help = 'The public witness.')
    parser_prove.add_argument('-P', '--proof', type = str, default = 'a.proof', help = 'The file to write the proof to. (Default: a.proof)')
    parser_verif = subparsers.add_parser('verify', help = 'Verify a proof.')
    parser_verif.add_argument('-n', '--names', type = str, default = 'a.names', help = 'The file to read the public names from. (Default: a.names)')
    parser_verif.add_argument('-v', '--verif', type = str, default = 'a.verif', help = 'The file to read the parameters for verifying from. (Default: a.verif)')
    parser_verif.add_argument('-P', '--proof', type = str, default = 'a.proof', help = 'The file to read the proof from. (Default: a.proof)')
    args = parser.parse_args()
    if args.command == 'compile':
        test = compiler.Compiler()
        with open(args.program, 'r') as program:
            test.compile(program.read())
        with open(args.gates, 'wb') as gates:
            gates.write(dill.dumps((test.gates, test.wire_count, test.stmts.keys())))
        with open(args.wires, 'wb') as wires:
            wires.write(dill.dumps(test.wires))
        with open(args.names, 'wb') as names:
            names.write(dill.dumps(test.stmts.values()))
    elif args.command == 'setup':
        with open(args.gates, 'rb') as gates:
            gates, wire_count, skeys = dill.loads(gates.read())
        α1, β1, δ1, β2, γ2, δ2, u1U, v1V, x1I, x2I, y1I = groth16.setup(gates, wire_count, skeys)
        α1, β1, δ1, β2, γ2, δ2 = α1.serialize(), β1.serialize(), δ1.serialize(), β2.serialize(), γ2.serialize(), δ2.serialize()
        u1U = [u1.serialize() for u1 in u1U]
        v1V = [v1.serialize() for v1 in v1V]
        x1I = [x1.serialize() for x1 in x1I]
        x2I = [x2.serialize() for x2 in x2I]
        y1I = [y1.serialize() for y1 in y1I]
        with open(args.prove, 'wb') as prove:
            prove.write(dill.dumps((α1, β1, δ1, β2, δ2, v1V, x1I, x2I, y1I)))
        with open(args.verif, 'wb') as verif:
            verif.write(dill.dumps((α1, β2, γ2, δ2, u1U)))
    elif args.command == 'prove':
        with open(args.gates, 'rb') as gates:
            gates, wire_count, skeys = dill.loads(gates.read())
        with open(args.wires, 'rb') as wires:
            wires = dill.loads(wires.read())
        with open(args.prove, 'rb') as prove:
            α1, β1, δ1, β2, δ2, v1V, x1I, x2I, y1I = dill.loads(prove.read())
            α1, β1, δ1, β2, δ2 = pymcl.G1.deserialize(α1), pymcl.G1.deserialize(β1), pymcl.G1.deserialize(δ1), pymcl.G2.deserialize(β2), pymcl.G2.deserialize(δ2)
            v1V = [pymcl.G1.deserialize(v1) for v1 in v1V]
            x1I = [pymcl.G1.deserialize(x1) for x1 in x1I]
            x2I = [pymcl.G2.deserialize(x2) for x2 in x2I]
            y1I = [pymcl.G1.deserialize(y1) for y1 in y1I]
        A1, B2, C1, uU = groth16.prove(gates, wires, wire_count, skeys, α1, β1, δ1, β2, δ2, v1V, x1I, x2I, y1I, args.args)
        A1, B2, C1 = A1.serialize(), B2.serialize(), C1.serialize()
        with open(args.proof, 'wb') as proof:
            proof.write(dill.dumps((A1, B2, C1, uU)))
    elif args.command == 'verify':
        with open(args.names, 'rb') as names:
            names = dill.loads(names.read())
        with open(args.verif, 'rb') as verif:
            α1, β2, γ2, δ2, u1U = dill.loads(verif.read())
            α1, β2, γ2, δ2 = pymcl.G1.deserialize(α1), pymcl.G2.deserialize(β2), pymcl.G2.deserialize(γ2), pymcl.G2.deserialize(δ2)
            u1U = [pymcl.G1.deserialize(u1) for u1 in u1U]
        with open(args.proof, 'rb') as proof:
            A1, B2, C1, uU = dill.loads(proof.read())
            A1, B2, C1 = pymcl.G1.deserialize(A1), pymcl.G2.deserialize(B2), pymcl.G1.deserialize(C1)
        passed, outs = groth16.verify(names, α1, β2, γ2, δ2, u1U, A1, B2, C1, uU)
        if passed:
            print('Verification passed!')
            print('Public witness:', '{{{}}}'.format(', '.join('{} = {}'.format(k, u) for k, u in outs)))
        else:
            print('Verification failed!')
    else:
        parser.print_help()
        sys.exit(1)
if __name__ == '__main__':
    main()
