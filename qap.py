#!/usr/bin/python3
import util
Q = util.genPrime(16)
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
    def DEC(self, xs, LIST): # return decoding of xs (LIST is a list of possible values) (experiemental)
        ds = []
        es = []
        closure = lambda V: lambda witness, **kwargs: sum(witness[x] * m for x, m in xs) % Q == V
        for V in LIST:
            i = self.__bind(closure(V))
            self.gates.append(([(i, 1)], [(i, 1)], [(i, 1)]))
            ds.append((i, V))
            es.append((i, 1))
        self.asserts.append(lambda witness, **kwargs: sum(witness[x] * m for x, m in xs) % Q == sum(witness[i] * m for i, m in ds) * witness[e] % Q)
        self.asserts.append(lambda witness, **kwargs: sum(witness[i] * m for i, m in es) * sum(witness[i] * m for i, m in es) % Q == witness[e] % Q)
        self.gates.append((ds, [(e, 1)], xs))
        self.gates.append((es, es, [(e, 1)]))
        return ds
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
    def XOR(self, e, a, b, r_flip = False): # return a ^ b ^ r_flip
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
        self.asserts.append(lambda witness, **kwargs: witness[x] * witness[x] % Q == witness[x] % Q)
        self.gates.append(([(x, 1)], [(x, 1)], [(x, 1)]))
    def ASSERT_ZERO(self, e, xs): # assert xs == 0 (mod Q)
        self.asserts.append(lambda witness, **kwargs: witness[e] * witness[e] % Q == (sum(witness[x] * m for x, m in xs) + witness[e]) % Q)
        self.gates.append(([(e, 1)], [(e, 1)], [(e, 1)] + xs))
    def ASSERT_NONZ(self, e, xs): # assert xs != 0 (mod Q)
        i = self.__bind(lambda witness, **kwargs: pow(sum(witness[x] * m for x, m in xs), Q - 2, Q) * witness[e] % Q)
        self.asserts.append(lambda witness, **kwargs: sum(witness[x] * m for x, m in xs) * witness[i] % Q == witness[e] % Q)
        self.gates.append((xs, [(i, 1)], [(e, 1)]))
def prod(s):
    # generate polynomial t(x) = prod(x - k) for k in s
    t = [1]
    for k in s:
        t = [(v - k * u) % Q for u, v in zip(t + [0], [0] + t)]
    return t
def convert(mat, s):
    # convert matrix in R1CS form to list of polynomials in QAP form
    # input an n * m matrix, output a list of m polynomials of degree n - 1
    # time complexity: O(n * m ** 2)
    return [util.lagrange(list(zip(s, col)), Q) for col in zip(*mat)]
def dot(polys, w):
    # calculate dot product of list of polynomials and vector
    return [sum(i * j for i, j in zip(u, w)) % Q for u in zip(*polys)]
if __name__ == '__main__':
    print('GF({})'.format(Q))
    # Example Program
    pro = Program()
    e = pro.VAR('e') # 1
    x = pro.VAR('x') # x
    y = pro.VAR('y') # y
    xs = pro.BIN(e, [(x, 1)], 4) # xs = binary(x, 4)
    ys = pro.BIN(e, [(y, 1)], 4) # ys = binary(y, 4)
    zs = [(pro.XOR(e, a, b), 1 << i) for i, ((a, _), (b, _)) in enumerate(zip(xs, ys))] # zs = xs ^ ys
    ILST = [0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xA, 0xB, 0xC, 0xD, 0xE, 0xF]
    OLST = [0x7, 0xC, 0xB, 0xD, 0xE, 0x4, 0x9, 0xF, 0x6, 0x3, 0x8, 0xA, 0x2, 0x5, 0x1, 0x0]
    os = [(k, o) for (k, i), o in zip(pro.DEC(zs, ILST), OLST)] # os = map(zs, ILST -> OLST)
    o = pro.VMUL(os, [(e, 1)]) # w = sum(ws)
    # Compile
    A, B, C = pro.R1CS() # A, B, C matrices
    s = util.sample(1, Q, pro.gate_count())
    t = prod(s)
    A = convert(A, s) # A polynomials set
    B = convert(B, s) # B polynomials set
    C = convert(C, s) # C polynomials set
    print('t(x) =', util.polyshow(t))
    # Prove
    w = pro.witness(e = 1, x = 3, y = 5)
    print('witness =', w)
    a = dot(A, w)
    b = dot(B, w)
    c = dot(C, w)
    print('a(x) =', util.polyshow(a))
    print('b(x) =', util.polyshow(b))
    print('c(x) =', util.polyshow(c))
    d = util.polysub(util.polymul(a, b, Q), c, Q)
    print('d(x) =', util.polyshow(d))
    q, r = util.polydm(d, t, Q)
    print('q(x) =', util.polyshow(q))
    print('r(x) =', util.polyshow(r))
