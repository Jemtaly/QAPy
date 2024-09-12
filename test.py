#!/usr/bin/env python3


import time

import compiler
import groth16


class Timer:
    # This is used to measure the time of a block of code.
    def __init__(self, text):
        self.text = text

    def __enter__(self):
        print(self.text, end=" ", flush=True)
        self.beg = time.time()

    def __exit__(self, *info):
        self.end = time.time()
        print("{:.3f} sec".format(self.end - self.beg))


def main():
    with Timer("Compiling program..."):
        test = compiler.Compiler()
        test.compile(
            "ROR = lambda x, r: x >> r | x << 32 - r\n"
            "def MAJ(x, y, z):\n"
            "    t = x & y\n"
            "    return [t[i] + z[i] * (x[i] + y[i] - t[i] * 2) for i in range(32)]\n"
            "def CHO(x, y, z):\n"
            "    return [y[i] if x[i] else z[i] for i in range(32)]\n"
            "K = [\n"
            "    b32(0x428A2F98), b32(0x71374491), b32(0xB5C0FBCF), b32(0xE9B5DBA5),\n"
            "    b32(0x3956C25B), b32(0x59F111F1), b32(0x923F82A4), b32(0xAB1C5ED5),\n"
            "    b32(0xD807AA98), b32(0x12835B01), b32(0x243185BE), b32(0x550C7DC3),\n"
            "    b32(0x72BE5D74), b32(0x80DEB1FE), b32(0x9BDC06A7), b32(0xC19BF174),\n"
            "    b32(0xE49B69C1), b32(0xEFBE4786), b32(0x0FC19DC6), b32(0x240CA1CC),\n"
            "    b32(0x2DE92C6F), b32(0x4A7484AA), b32(0x5CB0A9DC), b32(0x76F988DA),\n"
            "    b32(0x983E5152), b32(0xA831C66D), b32(0xB00327C8), b32(0xBF597FC7),\n"
            "    b32(0xC6E00BF3), b32(0xD5A79147), b32(0x06CA6351), b32(0x14292967),\n"
            "    b32(0x27B70A85), b32(0x2E1B2138), b32(0x4D2C6DFC), b32(0x53380D13),\n"
            "    b32(0x650A7354), b32(0x766A0ABB), b32(0x81C2C92E), b32(0x92722C85),\n"
            "    b32(0xA2BFE8A1), b32(0xA81A664B), b32(0xC24B8B70), b32(0xC76C51A3),\n"
            "    b32(0xD192E819), b32(0xD6990624), b32(0xF40E3585), b32(0x106AA070),\n"
            "    b32(0x19A4C116), b32(0x1E376C08), b32(0x2748774C), b32(0x34B0BCB5),\n"
            "    b32(0x391C0CB3), b32(0x4ED8AA4A), b32(0x5B9CCA4F), b32(0x682e6ff3),\n"
            "    b32(0x748f82ee), b32(0x78a5636f), b32(0x84c87814), b32(0x8cc70208),\n"
            "    b32(0x90befffa), b32(0xa4506ceb), b32(0xbef9a3f7), b32(0xc67178f2),\n"
            "]\n"
            "V = [\n"
            "    b32(0x6A09E667), b32(0xBB67AE85), b32(0x3C6EF372), b32(0xA54FF53A),\n"
            "    b32(0x510E527F), b32(0x9B05688C), b32(0x1F83D9AB), b32(0x5BE0CD19),\n"
            "]\n"
            "def compress(V, W):\n"
            "    W = concat(W, repeat([b32(0)], 48))\n"
            "    for j in range(16, 64):\n"
            "        S0 = ROR(W[j - 15], 7) ^ ROR(W[j - 15], 18) ^ W[j - 15] >> 3\n"
            "        S1 = ROR(W[j - 2], 17) ^ ROR(W[j - 2], 19) ^ W[j - 2] >> 10\n"
            "        W[j] = {W[j - 16], S0, W[j - 7], S1}\n"
            "    A = V[0]\n"
            "    B = V[1]\n"
            "    C = V[2]\n"
            "    D = V[3]\n"
            "    E = V[4]\n"
            "    F = V[5]\n"
            "    G = V[6]\n"
            "    H = V[7]\n"
            "    for j in range(64):\n"
            "        S0 = ROR(A, 2) ^ ROR(A, 13) ^ ROR(A, 22)\n"
            "        MJ = MAJ(A, B, C)\n"
            "        S1 = ROR(E, 6) ^ ROR(E, 11) ^ ROR(E, 25)\n"
            "        CH = CHO(E, F, G)\n"
            "        A, B, C, D, E, F, G, H = {H, S1, CH, K[j], W[j], S0, MJ}, A, B, C, {H, S1, CH, K[j], W[j], D}, E, F, G\n"
            "    V[0] = A + V[0]\n"
            "    V[1] = B + V[1]\n"
            "    V[2] = C + V[2]\n"
            "    V[3] = D + V[3]\n"
            "    V[4] = E + V[4]\n"
            "    V[5] = F + V[5]\n"
            "    V[6] = G + V[6]\n"
            "    V[7] = H + V[7]\n"
            "    return V\n"
            "W = [b32(secret(fmt('W[{}]', i))) for i in range(16)]\n"
            "V = compress(V, W)\n"
            "for i in range(8):\n"
            "    reveal(fmt('V[{}]', i), V[i])\n"
        )
    print("Dimension of the witness vector:", test.wire_count)
    print("Number of constraints:", len(test.gates))
    print("Number of public entries:", len(test.stmts))
    with Timer("Setting up QAP..."):
        α1, β1, δ1, β2, γ2, δ2, u1U, v1V, x1I, x2I, y1I = groth16.setup(test.wire_count, test.stmts.keys(), test.gates)
    with Timer("Generating proof..."):
        args = {"W[{}]".format(i): v for i, v in enumerate([0x61626380] + [0x00000000] * 14 + [0x00000018])}
        A1, B2, C1, uU = groth16.prove(test.wire_count, test.funcs, test.stmts.keys(), test.gates, α1, β1, δ1, β2, δ2, v1V, x1I, x2I, y1I, args)
    with Timer("Verifying..."):
        passed, outs = groth16.verify(test.stmts.values(), α1, β2, γ2, δ2, u1U, A1, B2, C1, uU)
    if passed:
        print("Verification passed!")
        print("Public entries:", "{{{}}}".format(", ".join("{} = {:#010x}".format(k, u) for k, u in outs)))
    else:
        print("Verification failed!")


if __name__ == "__main__":
    main()
