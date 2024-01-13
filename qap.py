#!/usr/bin/python3
import util
Q = util.genPrime(16)
def poly(n):
    # generate polynomial Z = (x - 1) * (x - 2) * ... * (x - n)
    Z = [1]
    for i in range(1, n + 1):
        Z = [(v - i * u) % Q for u, v in zip(Z + [0], [0] + Z)]
    return Z
def convert(mat):
    # convert matrix in R1CS form to list of polynomials in QAP form
    # input an n * m matrix, output a list of m polynomials of degree n - 1
    # time complexity: O(n * m ** 2)
    return [util.lagrange(list(enumerate(col, 1)), Q) for col in zip(*mat)]
def dot(polys, s):
    # calculate dot product of list of polynomials and vector
    return [sum(i * j for i, j in zip(u, s)) % Q for u in zip(*polys)]
class Program:
    def __init__(self):
        self.gates = []
        self.vars = []
        self.asserts = []
    def gate_count(self):
        return len(self.gates)
    def var_count(self):
        return len(self.vars)
    def R1CS(self):
        var_count = self.var_count()
        gate_count = self.gate_count()
        A = [[0 for _ in range(var_count)] for _ in range(gate_count)]
        B = [[0 for _ in range(var_count)] for _ in range(gate_count)]
        C = [[0 for _ in range(var_count)] for _ in range(gate_count)]
        for i, gate in enumerate(self.gates):
            xs, ys, zs = gate
            for x, m in xs:
                A[i][x] += m
            for y, n in ys:
                B[i][y] += n
            for z, o in zs:
                C[i][z] += o
        return A, B, C
    def witness(self, **kwargs):
        var_count = self.var_count()
        witness = [0 for _ in range(var_count)]
        for i, func in enumerate(self.vars):
            witness[i] = func(witness, **kwargs)
        for func in self.asserts:
            assert func(witness, **kwargs)
        return witness
    def __bind(self, func): # create a new variable bound to a function, return its index
        i = len(self.vars)
        self.vars.append(func)
        return i
    def VAR(self, name): # return a variable
        o = self.__bind(lambda witness, **kwargs: kwargs[name])
        return o
    def VMUL(self, xs, ys, zs = [], N = 1): # return (xs * ys - zs) / N (mod Q)
        o = self.__bind(lambda witness, **kwargs: (sum(witness[x] * m for x, m in xs) * pow(sum(witness[y] * n for y, n in ys), +1, Q) - sum(witness[z] * o for z, o in zs)) * pow(N, -1, Q) % Q)
        self.gates.append((xs, ys, zs + [(o, N)]))
        return o
    def VDIV(self, zs, ys, xs = [], N = 1): # return (xs / ys - zs) / N (mod Q)
        o = self.__bind(lambda witness, **kwargs: (sum(witness[z] * o for z, o in zs) * pow(sum(witness[y] * n for y, n in ys), -1, Q) - sum(witness[x] * m for x, m in xs)) * pow(N, -1, Q) % Q)
        self.gates.append((xs + [(o, N)], ys, zs))
        return o
    def MUL(self, a, b): # return a * b (mod Q)
        return self.VMUL([(a, 1)], [(b, 1)])
    def DIV(self, c, b): # return c / b (mod Q)
        return self.VDIV([(c, 1)], [(b, 1)])
    def POW(self, e, a, N): # return a ** N (mod Q)
        if N < 0:
            N = -N
            a = self.DIV(e, a)
        if N & 1:
            e = a
        N >>= 1
        while N:
            a = self.MUL(a, a)
            if N & 1:
                e = self.MUL(e, a)
            N >>= 1
        return e
    def BOOL(self, xs): # return if xs == 0 then 0 else 1
        i = self.__bind(lambda witness, **kwargs: pow(sum(witness[x] * m for x, m in xs), Q - 2, Q))
        o = self.__bind(lambda witness, **kwargs: pow(sum(witness[x] * m for x, m in xs), Q - 1, Q))
        self.gates.append((xs, [(o, 1)], xs))
        self.gates.append((xs, [(i, 1)], [(o, 1)]))
        return o
    def BIN(self, e, xs, L): # return binary representation of xs (L bits) (experiemental)
        bs = []
        closure = lambda I: lambda witness, **kwargs: sum(witness[x] * m for x, m in xs) % Q >> I & 1
        for I in range(L):
            i = self.__bind(closure(I))
            self.gates.append(([(i, 1)], [(i, 1)], [(i, 1)]))
            bs.append((i, 1 << I))
        self.asserts.append(lambda witness, **kwargs: sum(witness[x] * m for x, m in xs) % Q == sum(witness[i] * m for i, m in bs) * witness[e] % Q)
        self.gates.append((bs, [(e, 1)], xs))
        return bs
    def AND(self, e, a, b, a_flip = False, b_flip = False): # return (a ^ a_flip) & (b ^ b_flip)
        xs = [(a, -1), (e, 1)] if a_flip else [(a, 1)]
        ys = [(b, -1), (e, 1)] if b_flip else [(b, 1)]
        zs = [(0, 1)]
        (_, N), *zs = zs
        return self.VMUL(xs, ys, zs, N)
    def OR(self, e, a, b, a_flip = False, b_flip = False): # return (a ^ a_flip) | (b ^ b_flip)
        xs = [(a, 1)] if a_flip else [(a, -1), (e, 1)]
        ys = [(b, 1)] if b_flip else [(b, -1), (e, 1)]
        zs = [(0, -1), (e, 1)]
        (_, N), *zs = zs
        return self.VMUL(xs, ys, zs, N)
    def XOR(self, e, a, b, r_flip = False): # return (a ^ b) ^ r_flip
        xs = [(a, 2), (e, -1)]
        ys = [(b, 2), (e, -1)]
        zs = [(0, 2), (e, -1)] if r_flip else [(0, -2), (e, 1)]
        (_, N), *zs = zs
        return self.VMUL(xs, ys, zs, N)
    def COND(self, c, ts, fs): # return if c then ts else fs (c should be 0 or 1)
        ts = [(t, +n) for t, n in ts]
        fs = [(f, -n) for f, n in fs]
        return self.VMUL([(c, 1)], ts + fs, fs)
    def ASSERT_BOOL(self, x): # assert x == 0 or x == 1
        self.asserts.append(lambda witness, **kwargs: witness[x] ** 2 % Q == witness[x])
        self.gates.append(([(x, 1)], [(x, 1)], [(x, 1)]))
    def ASSERT_ZERO(self, e, xs): # assert xs == 0 (mod Q)
        self.asserts.append(lambda witness, **kwargs: (sum(witness[x] * m for x, m in xs) + witness[e]) * witness[e] % Q == witness[e])
        self.gates.append((xs + [(e, 1)], [(e, 1)], [(e, 1)]))
    def ASSERT_NONZ(self, e, xs): # assert xs != 0 (mod Q)
        i = self.__bind(lambda witness, **kwargs: pow(sum(witness[x] * m for x, m in xs), Q - 2, Q) * witness[e] % Q)
        self.asserts.append(lambda witness, **kwargs: pow(sum(witness[x] * m for x, m in xs), Q - 1, Q) * witness[e] % Q == witness[e])
        self.gates.append((xs, [(i, 1)], [(e, 1)]))
if __name__ == '__main__':
    print('GF({})'.format(Q))
    # Example Program
    qap = Program()
    e = qap.VAR('e') # 1
    x = qap.VAR('x') # x
    y = qap.VAR('y') # y
    xs = qap.BIN(e, [(x, 1)], 4) # xs = binary(x, 4)
    ys = qap.BIN(e, [(y, 1)], 4) # ys = binary(y, 4)
    zs = [(qap.XOR(e, a, b), 1 << i) for i, ((a, _), (b, _)) in enumerate(zip(xs, ys))] # zs = xs ^ ys
    z = qap.VMUL(zs, [(e, 1)]) # z = sum(zs) * e
    # Compile
    A, B, C = qap.R1CS()
    Z = poly(qap.gate_count())
    A_polys = convert(A)
    B_polys = convert(B)
    C_polys = convert(C)
    print('Z =', Z)
    # Prove
    s = qap.witness(e = 1, x = 3, y = 5)
    print('s =', s)
    a = dot(A_polys, s)
    b = dot(B_polys, s)
    c = dot(C_polys, s)
    t = util.polysub(util.polymul(a, b, Q), c, Q)
    print('A . s =', a)
    print('B . s =', b)
    print('C . s =', c)
    print('t =', t)
    H, r = util.polydm(t, Z, Q)
    print('H =', H)
    print('r =', r)
