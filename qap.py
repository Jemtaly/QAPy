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
    def witness(self, **args):
        var_count = self.var_count()
        witness = [0 for _ in range(var_count)]
        getw = lambda xl: sum(witness[k] * v for k, v in xl) % P
        for i, func in enumerate(self.vars):
            witness[i] = func(getw, **args)
        for al, bl, cl in self.gates:
            assert getw(al) * getw(bl) % P == getw(cl)
        return witness
    def __bind(self, func, reveal = False): # create a new variable bound to a function, return its index
        i = len(self.vars)
        self.vars.append(func)
        if reveal:
            self.reveals.append(i)
        return i
    def VAR(self, name, reveal = False): # return a variable
        return [(self.__bind(lambda getw, **args: args[name], reveal), 1)]
    def REVEAL(self, al): # reveal the value of a variable
        cl = [(self.__bind(lambda getw, **args: getw(al), True), 1)]
        self.gates.append(([], [], self.SUB(cl, al)))
        return cl
    def ADD(self, al, bl): # return a + b (mod P)
        return al + bl
    def SUB(self, al, bl): # return a - b (mod P)
        return al + [(i, -m % P) for i, m in bl]
    def MUL_C(self, al, N): # return a * N (mod P)
        return [(i, m * N % P) for i, m in al]
    def DIV_C(self, al, N): # return a / N (mod P)
        return [(i, m * util.modinv(N, P) % P) for i, m in al]
    def MUL(self, al, bl): # return a * b (mod P)
        cl = [(self.__bind(lambda getw, **args: getw(al) * getw(bl) % P), 1)]
        self.gates.append((al, bl, cl))
        return cl
    def DIV(self, cl, bl): # return c / b (mod P)
        al = [(self.__bind(lambda getw, **args: getw(cl) * util.modinv(getw(bl), P) % P), 1)]
        self.gates.append((al, bl, cl))
        return al
    def SWITCH(self, el, xl, Set): # return a dictionary of {V: x == V} for V in Set / assert x in Set
        fl = []
        rd = {}
        closure = lambda V: lambda getw, **args: int((getw(xl) - V) % P == 0)
        for V in Set:
            il = [(self.__bind(closure(V)), 1)]
            self.gates.append((il, il, il))
            dl = self.ADD(dl, self.MUL_C(il, V))
            fl = self.ADD(fl, self.MUL_C(il, 1))
            rd[V] = il
        self.gates.append((el, xl, dl))
        self.gates.append((el, el, fl))
        return rd
    def BIN(self, el, xl, L): # return binary representation of x (L bits) / assert 0 <= x < 2 ** L
        rl = []
        rb = []
        closure = lambda I: lambda getw, **args: getw(xl) >> I & 1
        for I in range(L):
            il = [(self.__bind(closure(I)), 1)]
            self.gates.append((il, il, il))
            rl = self.ADD(rl, self.MUL_C(il, 1 << I))
            rb.append(il)
        self.gates.append((el, xl, rl))
        return rb
    def ABS(self, el, xl, L): # return binary representation of |x| (L bits) / assert |x| < 2 ** L
        rl = []
        rb = []
        closure = lambda I: lambda getw, **args: min(getw(xl), P - getw(xl)) >> I & 1
        for I in range(L):
            il = [(self.__bind(closure(I)), 1)]
            self.gates.append((il, il, il))
            rl = self.ADD(rl, self.MUL_C(il, 1 << I))
            rb.append(il)
        sl = [(self.__bind(lambda getw, **args: int(getw(xl) < P - getw(xl))), 1)]
        self.gates.append((sl, sl, el))
        self.gates.append((sl, xl, rl))
        return rb
    def SUM(self, ls): # return sum of list
        rl = []
        for il in ls:
            rl = self.ADD(rl, il)
        return rl
    def VAL(self, xb): # return value of binary representation
        return self.SUM(self.MUL_C(il, 1 << I) for I, il in enumerate(xb))
    def AND(self, el, al, bl): # return a & b
        return self.MUL(al, bl)
    def OR(self, el, al, bl): # return a | b
        return self.SUB(el, self.MUL(self.SUB(el, al), self.SUB(el, bl)))
    def XOR(self, el, al, bl): # return a ^ b
        return self.DIV_C(self.SUB(el, self.MUL(self.SUB(el, self.MUL_C(al, 2)), self.SUB(el, self.MUL_C(bl, 2)))), 2)
    def BOOL(self, xl): # return if x == 0 then 0 else 1
        il = [(self.__bind(lambda getw, **args: pow(getw(xl), P - 2, P)), 1)]
        ol = [(self.__bind(lambda getw, **args: pow(getw(xl), P - 1, P)), 1)]
        self.gates.append((ol, xl, xl))
        self.gates.append((xl, il, ol))
        return ol
    def COND(self, cl, tl, fl): # return if c then t else f (c should be 0 or 1)
        return self.ADD(self.MUL(cl, self.SUB(tl, fl)), fl)
    def AGET(self, kb, ls): # return ls[i] (i is binary representation)
        for il in kb:
            ls = [self.COND(il, rl, ll) for ll, rl in zip(ls[0::2], ls[1::2])]
        return ls[0]
    def COND_C(self, el, cl, T, F): # return if c then T else F (c should be 0 or 1)
        return self.ADD(self.MUL_C(cl, T - F), self.MUL_C(el, F))
    def AGET_C(self, el, kb, Arr): # return Arr[i] (i is binary representation)
        il, *kb = kb
        ls = [self.COND_C(el, il, R, L) for L, R in zip(Arr[0::2], Arr[1::2])]
        for il in kb:
            ls = [self.COND(il, rl, ll) for ll, rl in zip(ls[0::2], ls[1::2])]
        return ls[0]
    def ASSERT(self, xl, yl, zl): # assert x * y == z (mod P)
        self.gates.append((xl, yl, zl))
    def ASSERT_BOOL(self, xl): # assert x == 0 or x == 1
        self.ASSERT(xl, xl, xl)
    def ASSERT_ZERO(self, xl): # assert x == 0 (mod P)
        self.ASSERT([], [], xl)
    def ASSERT_NONZ(self, el, xl): # assert x != 0 (mod P)
        self.DIV(el, xl)
    def DIVMOD(self, el, xl, yl, Q, R): # return (x // y (Q bits), x % y (R bits)) (in binary representation)
        ql = [(self.__bind(lambda getw, **args: getw(xl) // getw(yl)), 1)]
        rl = [(self.__bind(lambda getw, **args: getw(xl) % getw(yl)), 1)]
        tl = self.ADD(self.SUB(rl, yl), self.MUL_C(el, 2 ** R))
        self.ASSERT(ql, yl, self.SUB(xl, rl)) # assert y * q == x - r
        qb = self.BIN(el, ql, Q) # assert 0 <= q < 2 ** Q
        rb = self.BIN(el, rl, R) # assert 0 <= r < 2 ** R
        tb = self.BIN(el, tl, R) # assert y - 2 ** R <= r < y
        return qb, rb
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
    zl = pro.VAR('z', reveal = 0) # z
    xb = pro.BIN(el, xl, 16) # binary representation of x
    yb = pro.BIN(el, yl, 16) # binary representation of y
    tb = [pro.XOR(el, a, b) for a, b in zip(xb, yb)] # binary representation of x ^ y
    tl = pro.VAL(tb) # x ^ y
    qb, rb = pro.DIVMOD(el, tl, zl, 16, 16) # x // y, x % y
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
        w = pro.witness(e = 1, x = 13, y = 12345, z = 17)
    print('witness = [{}]'.format(', '.join(('{} (reveal)' if i in pro.reveals else '{}').format(v) for i, v in enumerate(w))))
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
