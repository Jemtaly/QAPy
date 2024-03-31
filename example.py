#!/usr/bin/python3
import time
import compiler
import groth16
class Timer:
    # This is used to measure the time of a block of code.
    def __init__(self, text):
        self.text = text
    def __enter__(self):
        print(self.text, end = ' ', flush = True)
        self.beg = time.time()
    def __exit__(self, *info):
        self.end = time.time()
        print('{:.3f} sec'.format(self.end - self.beg))
if __name__ == '__main__':
    with Timer('Compiling program...'):
        test = compiler.Compiler()
        test.compile(
            "ROL = lambda x, r: x << r | x >> 32 - r\n"
            "P0 = lambda x: x ^ ROL(x, 9) ^ ROL(x, 17)\n"
            "P1 = lambda x: x ^ ROL(x, 15) ^ ROL(x, 23)\n"
            "F0 = lambda x, y, z: x ^ y ^ z\n"
            "G0 = lambda x, y, z: x ^ y ^ z\n"
            "def F1(x, y, z):\n"
            "    t = x & y\n"
            "    return [t[i] + z[i] * (x[i] + y[i] - t[i] * 2) for i in range(32)]\n"
            "def G1(x, y, z):\n"
            "    return [y[i] if x[i] else z[i] for i in range(32)]\n"
            "T0 = b32(0x79cc4519)\n"
            "T1 = b32(0x7a879d8a)\n"
            "def compress(V, I):\n"
            "    W = [b32(0) for _ in range(68)]\n"
            "    for j in range(0, 16):\n"
            "        W[j] = I[j]\n"
            "    for j in range(16, 68):\n"
            "        W[j] = P1(W[j - 16] ^ W[j - 9] ^ ROL(W[j - 3], 15)) ^ ROL(W[j - 13], 7) ^ W[j - 6]\n"
            "    A = V[0]\n"
            "    B = V[1]\n"
            "    C = V[2]\n"
            "    D = V[3]\n"
            "    E = V[4]\n"
            "    F = V[5]\n"
            "    G = V[6]\n"
            "    H = V[7]\n"
            "    for j in range(0, 64):\n"
            "        if j < 16:\n"
            "            SS1 = ROL({ROL(A, 12), E, ROL(T0, j)}, 7)\n"
            "            SS2 = SS1 ^ ROL(A, 12)\n"
            "            TT1 = {F0(A, B, C), D, SS2, W[j] ^ W[j + 4]}\n"
            "            TT2 = {G0(E, F, G), H, SS1, W[j]}\n"
            "        else:\n"
            "            SS1 = ROL({ROL(A, 12), E, ROL(T1, j)}, 7)\n"
            "            SS2 = SS1 ^ ROL(A, 12)\n"
            "            TT1 = {F1(A, B, C), D, SS2, W[j] ^ W[j + 4]}\n"
            "            TT2 = {G1(E, F, G), H, SS1, W[j]}\n"
            "        A, B, C, D, E, F, G, H = TT1, A, ROL(B, 9), C, P0(TT2), E, ROL(F, 19), G\n"
            "    V[0] = A ^ V[0]\n"
            "    V[1] = B ^ V[1]\n"
            "    V[2] = C ^ V[2]\n"
            "    V[3] = D ^ V[3]\n"
            "    V[4] = E ^ V[4]\n"
            "    V[5] = F ^ V[5]\n"
            "    V[6] = G ^ V[6]\n"
            "    V[7] = H ^ V[7]\n"
            "    return V\n"
            "V = [\n"
            "    b32(0x7380166f), b32(0x4914b2b9), b32(0x172442d7), b32(0xda8a0600),\n"
            "    b32(0xa96f30bc), b32(0x163138aa), b32(0xe38dee4d), b32(0xb0fb0e4e),\n"
            "]\n"
            "W = [b32(secret(fmt('W[{}]', i))) for i in range(16)]\n"
            "V = compress(V, W)\n"
            "for i in range(8):\n"
            "    reveal(fmt('V[{}]', i), V[i])\n"
        )
    print('Number of gates:', len(test.gates))
    print('Number of wires:', test.wire_count)
    with Timer('Setting up QAP...'):
        α1, β1, δ1, β2, γ2, δ2, u1U, v1V, x1I, x2I, y1I = groth16.setup(test.wire_count, test.stmts.keys(), test.gates)
    with Timer('Generating proof...'):
        args = {'W[{}]'.format(i): v for i, v in enumerate([0x61626380] + [0x00000000] * 14 + [0x00000018])}
        A1, B2, C1, uU = groth16.prove(test.wire_count, test.funcs, test.stmts.keys(), test.gates, α1, β1, δ1, β2, δ2, v1V, x1I, x2I, y1I, args)
    with Timer('Verifying...'):
        passed, outs = groth16.verify(test.stmts.values(), α1, β2, γ2, δ2, u1U, A1, B2, C1, uU)
    if passed:
        print('Verification passed!')
        print('Public witness:', '{{{}}}'.format(', '.join('{} = {:#010x}'.format(k, u) for k, u in outs)))
    else:
        print('Verification failed!')
