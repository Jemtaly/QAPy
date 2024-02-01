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
        self.vars = [lambda getw, **args: 1]
        self.reveals = {0}
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
            a, b, c = gate
            for k, v in a:
                A[i][k] += v
            for k, v in b:
                B[i][k] += v
            for k, v in c:
                C[i][k] += v
        return A, B, C
    def witness(self, **args):
        var_count = self.var_count()
        witness = [0 for _ in range(var_count)]
        getw = lambda x: sum(witness[k] * v for k, v in x) % P
        for i, func in enumerate(self.vars):
            witness[i] = func(getw, **args)
        for a, b, c in self.gates:
            assert getw(a) * getw(b) % P == getw(c)
        return witness
    def __bind(self, func, reveal = False): # create a new variable bound to a function, return its index
        i = len(self.vars)
        self.vars.append(func)
        if reveal:
            self.reveals.append(i)
        return i
    def NEWVAR(self, name, reveal = False): # return a variable
        return [(self.__bind(lambda getw, **args: args[name], reveal), 1)]
    def REVEAL(self, a): # reveal the value of a variable
        r = [(self.__bind(lambda getw, **args: getw(a), True), 1)]
        self.ASSERT(1, a, r)
        return r
    def ADD(self, a, b): # return a + b (mod P)
        if isinstance(a, int) and isinstance(b, int):
            return (a + b) % P
        if isinstance(b, int):
            b = [(0, b)]
        if isinstance(a, int):
            a = [(0, a)]
        return a + b
    def SUB(self, a, b): # return a - b (mod P)
        if isinstance(a, int) and isinstance(b, int):
            return (a - b) % P
        if isinstance(b, int):
            b = [(0, b)]
        if isinstance(a, int):
            a = [(0, a)]
        return a + [(i, -m % P) for i, m in b]
    def MUL(self, a, b): # return a * b (mod P)
        if isinstance(a, int) and isinstance(b, int):
            return a * b % P
        if isinstance(b, int):
            return [(i, m * b % P) for i, m in a]
        if isinstance(a, int):
            return [(i, m * a % P) for i, m in b]
        c = [(self.__bind(lambda getw, **args: getw(a) * getw(b) % P), 1)]
        self.gates.append((a, b, c))
        return c
    def DIV(self, a, b): # return a / b (mod P)
        if isinstance(a, int) and isinstance(b, int):
            return a * util.modinv(b, P) % P
        if isinstance(b, int):
            return [(i, m * util.modinv(b, P) % P) for i, m in a]
        if isinstance(a, int):
            a = [(0, a)]
        c = [(self.__bind(lambda getw, **args: getw(a) * util.modinv(getw(b), P) % P), 1)]
        self.gates.append((c, b, a))
        return c
    def POW(self, a, Bin): # return a ** Bin (mod P)
        i, *Bin = Bin
        r = self.IF(i, a, 1)
        for i in Bin:
            a = self.MUL(a, a)
            r = self.MUL(r, self.IF(i, a, 1))
        return r
    def SUM(self, Lst): # return sum of list
        r = 0
        for i in Lst:
            r = self.ADD(r, i)
        return r
    def SWITCH(self, x, Set): # return a dictionary of {V: x == V} for V in Set / assert x in Set
        if isinstance(x, int):
            return {V: int((x - V) % P == 0) for V in Set}
        d = 0
        f = 0
        Dct = {}
        closure = lambda V: lambda getw, **args: int((getw(x) - V) % P == 0)
        for V in Set:
            i = [(self.__bind(closure(V)), 1)]
            self.ASSERT(i, i, i)
            d = self.ADD(d, self.MUL(i, V))
            f = self.ADD(f, self.MUL(i, 1))
            Dct[V] = i
        self.ASSERT(1, x, d)
        self.ASSERT(1, 1, f)
        return Dct
    def GETITEM(self, Map, Dct): # return Map @ Dct / assert x in Map
        return self.SUM(self.MUL(Map[k], Dct[k]) for k in Map)
    def SETITEM(self, Map, Dct, v): # Map[i] = Dct[i] ? v : Map[i] / assert x in Map
        for k in Map:
            Map[k] = self.ADD(Map[k], self.MUL(Dct[k], self.SUB(v, Map[k])))
    def BINARY(self, x, L): # return binary representation of x (L bits) / assert 0 <= x < 2 ** L
        if isinstance(x, int):
            return [x >> I & 1 for I in range(L)]
        r = 0
        Bin = []
        closure = lambda I: lambda getw, **args: getw(x) >> I & 1
        for I in range(L):
            i = [(self.__bind(closure(I)), 1)]
            self.ASSERT(i, i, i)
            r = self.ADD(r, self.MUL(i, 1 << I))
            Bin.append(i)
        self.ASSERT(1, x, r)
        return Bin
    def BINABS(self, x, L): # return binary representation of |x| (L bits) / assert |x| < 2 ** L
        if isinstance(x, int):
            return [min(x % P, -x % P) >> I & 1 for I in range(L)]
        r = 0
        Bin = []
        closure = lambda I: lambda getw, **args: min(getw(x), P - getw(x)) >> I & 1
        for I in range(L):
            i = [(self.__bind(closure(I)), 1)]
            self.ASSERT(i, i, i)
            r = self.ADD(r, self.MUL(i, 1 << I))
            Bin.append(i)
        s = [(self.__bind(lambda getw, **args: int(getw(x) < P - getw(x))), 1)]
        self.ASSERT(s, s, 1)
        self.ASSERT(s, x, r)
        return Bin
    def VAL(self, Bin): # return value of binary representation
        return self.SUM(self.MUL(i, 1 << I) for I, i in enumerate(Bin))
    def AND(self, a, b): # return a & b
        return self.MUL(a, b)
    def OR(self, a, b): # return a | b
        return self.SUB(1, self.MUL(self.SUB(1, a), self.SUB(1, b)))
    def XOR(self, a, b): # return a ^ b
        return self.DIV(self.SUB(1, self.MUL(self.SUB(1, self.MUL(a, 2)), self.SUB(1, self.MUL(b, 2)))), 2)
    def BOOL(self, x): # return x != 0
        v = [(self.__bind(lambda getw, **args: pow(getw(x), P - 2, P)), 1)]
        o = [(self.__bind(lambda getw, **args: pow(getw(x), P - 1, P)), 1)]
        self.ASSERT(o, x, x)
        self.ASSERT(x, v, o)
        return o
    def IF(self, c, t, f): # return if c then t else f (c should be 0 or 1)
        return self.ADD(self.MUL(c, self.SUB(t, f)), f)
    def INDEX(self, Arr, Bin): # return Arr[Bin]
        for i in Bin:
            Arr = [self.IF(i, r, l) for l, r in zip(Arr[0::2], Arr[1::2])]
        return Arr[0]
    def ASSERT(self, x, y, z): # assert x * y == z (mod P)
        if isinstance(x, int) and isinstance(y, int) and isinstance(z, int):
            assert x * y % P == z
            return
        if isinstance(x, int):
            x = [(0, x)]
        if isinstance(y, int):
            y = [(0, y)]
        if isinstance(z, int):
            z = [(0, z)]
        self.gates.append((x, y, z))
    def ASSERT_BOOL(self, x): # assert x == 0 or x == 1
        self.ASSERT(x, x, x)
    def ASSERT_ZERO(self, x): # assert x == 0 (mod P)
        self.ASSERT(0, 0, x)
    def ASSERT_NONZ(self, x): # assert x != 0 (mod P)
        self.DIV(1, x)
    def DIVMOD(self, x, y, Q, R): # return x // y (Q bits), x % y (R bits)
        if isinstance(x, int) and isinstance(y, int):
            return [x // y >> I & 1 for I in range(Q)], [x % y >> I & 1 for I in range(R)]
        if isinstance(x, int):
            x = [(0, x)]
        if isinstance(y, int):
            y = [(0, y)]
        q = [(self.__bind(lambda getw, **args: getw(x) // getw(y)), 1)]
        r = [(self.__bind(lambda getw, **args: getw(x) % getw(y)), 1)]
        self.ASSERT(q, y, self.SUB(x, r)) # assert y * q == x - r
        t = self.ADD(self.SUB(r, y), 2 ** R)
        qBin = self.BINARY(q, Q) # assert 0 <= q < 2 ** Q
        rBin = self.BINARY(r, R) # assert 0 <= r < 2 ** R
        tBin = self.BINARY(t, R) # assert y - 2 ** R <= r < y
        return qBin, rBin
    def DIVMSW(self, x, Y, Q): # return x // Y (Q bits), x % Y (from {0, 1, ..., Y - 1})
        if isinstance(x, int):
            return [x // Y >> I & 1 for I in range(Q)], {i: int(x % Y == i) for i in range(Y)}
        q = [(self.__bind(lambda getw, **args: getw(x) // Y), 1)]
        r = [(self.__bind(lambda getw, **args: getw(x) % Y), 1)]
        self.ASSERT(q, Y, self.SUB(x, r)) # assert y * q == x - r
        qBin = self.BINARY(q, Q) # assert 0 <= q < 2 ** Q
        rDct = self.SWITCH(r, range(Y)) # assert 0 <= r < y
        return qBin, rDct
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
    x = pro.NEWVAR('x', reveal = 0) # x
    y = pro.NEWVAR('y', reveal = 0) # y
    z = pro.NEWVAR('z', reveal = 0) # z
    xBin = pro.BINARY(x, 16) # binary representation of x
    yBin = pro.BINARY(y, 16) # binary representation of y
    tBin = [pro.XOR(a, b) for a, b in zip(xBin, yBin)] # binary representation of x ^ y
    t = pro.VAL(tBin) # x ^ y
    q, r = pro.DIVMOD(t, z, 16, 16) # x // y, x % y
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
        w = pro.witness(x = 65535, y = 12345, z = 17)
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
