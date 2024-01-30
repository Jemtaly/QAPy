#!/usr/bin/python3
import time
import util
P = util.genprime(64)
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
        get = lambda xl: sum(witness[k] * v for k, v in xl) % P
        for i, func in enumerate(self.vars):
            witness[i] = func(get, **kwargs)
        for al, bl, cl in self.gates:
            assert get(al) * get(bl) % P == get(cl)
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
    def MULN(self, al, N): # return a * N (mod P)
        return [(i, m * N % P) for i, m in al]
    def DIVN(self, al, N): # return a / N (mod P)
        return [(i, m * util.modinv(N, P) % P) for i, m in al]
    def ADD(self, al, bl): # return a + b (mod P)
        return al + bl
    def SUB(self, al, bl): # return a - b (mod P)
        return al + [(i, -m % P) for i, m in bl]
    def MUL(self, al, bl): # return a * b (mod P)
        cl = [(self.__bind(lambda get, **kwargs: get(al) * get(bl) % P), 1)]
        self.gates.append((al, bl, cl))
        return cl
    def DIV(self, cl, bl): # return c / b (mod P)
        al = [(self.__bind(lambda get, **kwargs: get(cl) * util.modinv(get(bl), P) % P), 1)]
        self.gates.append((al, bl, cl))
        return al
    def POW(self, el, al, N): # return a ** N (mod P)
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
        il = [(self.__bind(lambda get, **kwargs: pow(get(xl), P - 2, P)), 1)]
        ol = [(self.__bind(lambda get, **kwargs: pow(get(xl), P - 1, P)), 1)]
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
        closure = lambda I: lambda get, **kwargs: min(get(xl), P - get(xl)) >> I & 1
        for I in range(L):
            iv = self.__bind(closure(I))
            il = [(iv, 1)]
            self.gates.append((il, il, il))
            bl.append((iv, 1 << I))
        sl = [(self.__bind(lambda get, **kwargs: int(get(xl) < P - get(xl))), 1)]
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
    def AND(self, el, al, bl): # return a & b
        return self.MUL(al, bl)
    def OR(self, el, al, bl): # return a | b
        return self.SUB(el, self.MUL(self.SUB(el, al), self.SUB(el, bl)))
    def XOR(self, el, al, bl): # return a ^ b
        return self.DIVN(self.SUB(el, self.MUL(self.SUB(el, self.MULN(al, 2)), self.SUB(el, self.MULN(bl, 2)))), 2)
    def COND(self, cl, tl, fl): # return if c then t else f (c should be 0 or 1)
        return self.ADD(self.MUL(cl, self.SUB(tl, fl)), fl)
    def ASSERT(self, xl, yl, zl): # assert x * y == z (mod P)
        self.gates.append((xl, yl, zl))
    def ASSERT_BOOL(self, xl): # assert x == 0 or x == 1
        self.ASSERT(xl, xl, xl)
    def ASSERT_ZERO(self, xl): # assert x == 0 (mod P)
        self.ASSERT([], [], xl)
    def ASSERT_NONZ(self, el, xl): # assert x != 0 (mod P)
        self.DIV(el, xl)
    def DIVMOD(self, el, xl, yl, Q, R): # return (x // y (Q bits), x % y (R bits))
        ql = [(self.__bind(lambda get, **kwargs: get(xl) // get(yl)), 1)]
        rl = [(self.__bind(lambda get, **kwargs: get(xl) % get(yl)), 1)]
        tl = self.ADD(self.SUB(rl, yl), self.MULN(el, 2 ** R))
        self.ASSERT(ql, yl, self.SUB(xl, rl)) # assert y * q == x - r
        self.BIN(el, ql, Q) # assert 0 <= q < 2 ** Q
        self.BIN(el, rl, R) # assert 0 <= r < 2 ** R
        self.BIN(el, tl, R) # assert y - 2 ** R <= r < y
        return ql, rl
def prod(s):
    # generate polynomial t(x) = prod(x - k) for k in s
    t = [1]
    for k in s:
        t = [(v - k * u) % P for u, v in zip(t + [0], [0] + t)]
    return t
def convert(mat, s):
    # convert matrix in R1CS form to list of polynomials in QAP form
    # input an M * N matrix, output a list of N polynomials of degree M - 1
    # time complexity: O(M ** 2 * N)
    return [util.lagrange(list(zip(s, col)), P) for col in zip(*mat)]
def dot(polys, w):
    # calculate dot product of list of polynomials and vector
    return [sum(i * j for i, j in zip(u, w)) % P for u in zip(*polys)]
if __name__ == '__main__':
    print('GF({})'.format(P))
    # Example Program
    pro = Program()
    el = pro.VAR('e', reveal = 1) # 1
    xl = pro.VAR('x', reveal = 0) # x
    yl = pro.VAR('y', reveal = 0) # y
    ql, rl = pro.DIVMOD(el, xl, yl, 16, 16) # x // y, x % y
    print('Gates:', M := pro.gate_count())
    print('Vars:', N := pro.var_count())
    with Timer('Generating R1CS...'):
        A, B, C = pro.R1CS() # A, B, C matrices
    with Timer('Converting to QAP...'):
        s = util.sample(1, P, M)
        t = prod(s)
        A = convert(A, s) # A polynomials set
        B = convert(B, s) # B polynomials set
        C = convert(C, s) # C polynomials set
    with Timer('Calculating witness...'):
        w = pro.witness(e = 1, x = 65535, y = 1234)
    print('witness =', w)
    with Timer('Verifying witness...'):
        a = dot(A, w)
        b = dot(B, w)
        c = dot(C, w)
        d = util.polysub(util.polymul(a, b, P), c, P)
        q, r = util.polydm(d, t, P)
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
