#!/usr/bin/python3
import time
import util
Q = util.genprime(16)
class Timer:
    def __init__(self, text):
        self.text = text
    def __enter__(self):
        print(self.text, end = ' ')
        self.beg = time.time()
    def __exit__(self, *args):
        self.end = time.time()
        print('{:.3f} sec'.format(self.end - self.beg))
class Program:
    def __init__(self):
        self.gates = []
        self.vars = []
        self.reveals = []
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
            al, bl, cl = gate
            for k, v in al:
                A[i][k] += v
            for k, v in bl:
                B[i][k] += v
            for k, v in cl:
                C[i][k] += v
        return A, B, C
    def witness(self, **kwargs):
        var_count = self.var_count()
        witness = [0 for _ in range(var_count)]
        get = lambda xl: sum(witness[k] * v for k, v in xl) % Q
        for i, func in enumerate(self.vars):
            witness[i] = func(get, **kwargs)
        for al, bl, cl in self.gates:
            assert get(al) * get(bl) % Q == get(cl)
        return witness
    def __bind(self, func, reveal = False): # create a new variable bound to a function, return its index
        i = len(self.vars)
        self.vars.append(func)
        if reveal:
            self.reveals.append(i)
        return i
    def VAR(self, name, reveal = False): # return a variable
        return [(self.__bind(lambda get, **kwargs: kwargs[name], reveal), 1)]
    def REVEAL(self, al): # reveal the value of a variable
        cl = [(self.__bind(lambda get, **kwargs: get(al), True), 1)]
        self.gates.append(([], [], self.SUB(cl, al)))
        return cl
    def MULN(self, al, N): # return a * N (mod Q)
        return [(i, m * N % Q) for i, m in al]
    def DIVN(self, al, N): # return a / N (mod Q)
        return [(i, m * util.modinv(N, Q) % Q) for i, m in al]
    def ADD(self, al, bl): # return a + b (mod Q)
        return al + bl
    def SUB(self, al, bl): # return a - b (mod Q)
        return al + [(i, -m % Q) for i, m in bl]
    def MUL(self, al, bl): # return a * b (mod Q)
        cl = [(self.__bind(lambda get, **kwargs: get(al) * get(bl) % Q), 1)]
        self.gates.append((al, bl, cl))
        return cl
    def DIV(self, cl, bl): # return c / b (mod Q)
        al = [(self.__bind(lambda get, **kwargs: get(cl) * util.modinv(get(bl), Q) % Q), 1)]
        self.gates.append((al, bl, cl))
        return al
    def POW(self, el, al, N): # return a ** N (mod Q)
        if N < 0:
            N = -N
            al = self.DIV(el, al)
        if N & 1:
            el = al
        N >>= 1
        while N:
            al = self.MUL(al, al)
            if N & 1:
                el = self.MUL(el, al)
            N >>= 1
        return el
    def BOOL(self, xl): # return if x == 0 then 0 else 1
        il = [(self.__bind(lambda get, **kwargs: pow(get(xl), Q - 2, Q)), 1)]
        ol = [(self.__bind(lambda get, **kwargs: pow(get(xl), Q - 1, Q)), 1)]
        self.gates.append((ol, xl, xl))
        self.gates.append((xl, il, ol))
        return ol
    def BIN(self, el, xl, L): # return binary representation of x (L bits) / assert 0 <= x < 2 ** L
        bl = []
        closure = lambda I: lambda get, **kwargs: get(xl) >> I & 1
        for I in range(L):
            iv = self.__bind(closure(I))
            il = [(iv, 1)]
            self.gates.append((il, il, il))
            bl.append((iv, 1 << I))
        self.gates.append((el, xl, bl))
        return bl
    def ABS(self, el, xl, L): # return absolute value of x (L bits) / assert abs(x) < 2 ** L
        bl = []
        closure = lambda I: lambda get, **kwargs: min(get(xl), Q - get(xl)) >> I & 1
        for I in range(L):
            iv = self.__bind(closure(I))
            il = [(iv, 1)]
            self.gates.append((il, il, il))
            bl.append((iv, 1 << I))
        sl = [(self.__bind(lambda get, **kwargs: int(get(xl) < Q - get(xl))), 1)]
        self.gates.append((sl, sl, el))
        self.gates.append((sl, xl, bl))
        return bl
    def DEC(self, el, xl, LIST): # return decoding of x (LIST is a list of possible values) / assert x in LIST
        dl = []
        fl = []
        closure = lambda V: lambda get, **kwargs: int(get(xl) == V)
        for V in LIST:
            iv = self.__bind(closure(V))
            il = [(iv, 1)]
            self.gates.append((il, il, il))
            dl.append((iv, V))
            fl.append((iv, 1))
        self.gates.append((el, xl, dl))
        self.gates.append((el, el, fl))
        return dl
    def NOT(self, el, xl): # return ~x
        return self.SUB(el, xl)
    def AND(self, el, al, bl): # return a & b
        return self.MUL(al, bl)
    def OR(self, el, al, bl): # return a | b
        return self.SUB(el, self.MUL(self.SUB(el, al), self.SUB(el, bl)))
    def XOR(self, el, al, bl): # return a ^ b
        return self.DIVN(self.SUB(el, self.MUL(self.SUB(el, self.MULN(al, 2)), self.SUB(el, self.MULN(bl, 2)))), 2)
    def IF(self, cl, tl, fl): # return if c then t else f (c should be 0 or 1)
        return self.ADD(self.MUL(cl, self.SUB(tl, fl)), fl)
    def ASSERT(self, xl, yl, zl): # assert x * y == z (mod Q)
        self.gates.append((xl, yl, zl))
    def ASSERT_BOOL(self, xl): # assert x == 0 or x == 1
        self.ASSERT(xl, xl, xl)
    def ASSERT_ZERO(self, xl): # assert x == 0 (mod Q)
        self.ASSERT([], [], xl)
    def ASSERT_NONZ(self, el, xl): # assert x != 0 (mod Q)
        self.DIV(el, xl)
def prod(s):
    # generate polynomial t(x) = prod(x - k) for k in s
    t = [1]
    for k in s:
        t = [(v - k * u) % Q for u, v in zip(t + [0], [0] + t)]
    return t
def convert(mat, s):
    # convert matrix in R1CS form to list of polynomials in QAP form
    # input an M * N matrix, output a list of N polynomials of degree M - 1
    # time complexity: O(M ** 2 * N)
    return [util.lagrange(list(zip(s, col)), Q) for col in zip(*mat)]
def dot(polys, w):
    # calculate dot product of list of polynomials and vector
    return [sum(i * j for i, j in zip(u, w)) % Q for u in zip(*polys)]
if __name__ == '__main__':
    print('GF({})'.format(Q))
    # Example Program
    pro = Program()
    el = pro.VAR('e', reveal = 1) # 1
    il = pro.VAR('i', reveal = 0) # x
    OP = [
        0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
        0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f,
        0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28, 0x29, 0x2a, 0x2b, 0x2c, 0x2d, 0x2e, 0x2f,
        0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x3a, 0x3b, 0x3c, 0x3d, 0x3e, 0x3f,
    ]
    FP = [
        0x39, 0x31, 0x29, 0x21, 0x19, 0x11, 0x09, 0x01, 0x3b, 0x33, 0x2b, 0x23, 0x1b, 0x13, 0x0b, 0x03,
        0x3d, 0x35, 0x2d, 0x25, 0x1d, 0x15, 0x0d, 0x05, 0x3f, 0x37, 0x2f, 0x27, 0x1f, 0x17, 0x0f, 0x07,
        0x38, 0x30, 0x28, 0x20, 0x18, 0x10, 0x08, 0x00, 0x3a, 0x32, 0x2a, 0x22, 0x1a, 0x12, 0x0a, 0x02,
        0x3c, 0x34, 0x2c, 0x24, 0x1c, 0x14, 0x0c, 0x04, 0x3e, 0x36, 0x2e, 0x26, 0x1e, 0x16, 0x0e, 0x06,
    ]
    GP = [
        0x27, 0x07, 0x2f, 0x0f, 0x37, 0x17, 0x3f, 0x1f, 0x26, 0x06, 0x2e, 0x0e, 0x36, 0x16, 0x3e, 0x1e,
        0x25, 0x05, 0x2d, 0x0d, 0x35, 0x15, 0x3d, 0x1d, 0x24, 0x04, 0x2c, 0x0c, 0x34, 0x14, 0x3c, 0x1c,
        0x23, 0x03, 0x2b, 0x0b, 0x33, 0x13, 0x3b, 0x1b, 0x22, 0x02, 0x2a, 0x0a, 0x32, 0x12, 0x3a, 0x1a,
        0x21, 0x01, 0x29, 0x09, 0x31, 0x11, 0x39, 0x19, 0x20, 0x00, 0x28, 0x08, 0x30, 0x10, 0x38, 0x18,
    ]
    fl = [(k, o) for (k, i), o in zip(pro.DEC(el, il, OP), FP)] # fl = map(il, OP -> FP)
    gl = [(k, o) for (k, i), o in zip(pro.DEC(el, il, OP), GP)] # gl = map(il, OP -> GP)
    fb = pro.BIN(el, fl, 6) # fb = binary(fs, 6)
    gb = pro.BIN(el, gl, 6) # gb = binary(gs, 6)
    ob = [pair for (a, i), (b, i) in zip(fb, gb) for pair in pro.MULN(pro.XOR(el, [(a, 1)], [(b, 1)]), i)] # ob = fb ^ gb
    ol = pro.REVEAL(ob) # ol = reveal(ob)
    print('Gates:', M := pro.gate_count())
    print('Vars:', N := pro.var_count())
    with Timer('Generating R1CS...'):
        A, B, C = pro.R1CS() # A, B, C matrices
    with Timer('Converting to QAP...'):
        s = util.sample(1, Q, M)
        t = prod(s)
        A = convert(A, s) # A polynomials set
        B = convert(B, s) # B polynomials set
        C = convert(C, s) # C polynomials set
    with Timer('Calculating witness...'):
        w = pro.witness(e = 1, i = 48)
    print('witness =', w)
    with Timer('Verifying witness...'):
        a = dot(A, w)
        b = dot(B, w)
        c = dot(C, w)
        d = util.polysub(util.polymul(a, b, Q), c, Q)
        q, r = util.polydm(d, t, Q)
    if any(r):
        print('Verification failed!')
        print('a(x) =', util.polyshow(a))
        print('b(x) =', util.polyshow(b))
        print('c(x) =', util.polyshow(c))
        print('d(x) =', util.polyshow(d))
        print('t(x) =', util.polyshow(t))
        print('q(x) =', util.polyshow(q))
        print('r(x) =', util.polyshow(r))
    else:
        print('Verification passed!')
