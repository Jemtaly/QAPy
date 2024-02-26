#!/usr/bin/python3
import time
import util
import ast
import random
import pypbc
params = pypbc.Parameters(param_string =
    "type a\n"
    "q 8780710799663312522437781984754049815806883199414208211028653399266475630880222957078625179422662221423155858769582317459277713367317481324925129998224791\n"
    "h 12016012264891146079388821366740534204802954401251311822919615131047207289359704531102844802183906537786776\n"
    "r 730750818665451621361119245571504901405976559617\n"
    "exp2 159\n"
    "exp1 107\n"
    "sign1 1\n"
    "sign0 1\n"
)
pairing = pypbc.Pairing(params)
G1 = pypbc.Element.random(pairing, pypbc.G1)
G2 = pypbc.Element.random(pairing, pypbc.G2)
P = 730750818665451621361119245571504901405976559617
K = 1 # maxium exponent of 2 that divides P - 1 (the number of constraints should not exceed K, otherwise FFT cannot be applied)
while (P - 1) % (K * 2) == 0:
    K = K * 2
for Z in range(2, P):
    if pow(Z, (P - 1) // 2, P) != 1:
        break
T = pow(Z, (P - 1) // K, P) # primitive K-th root of unity
class Timer:
    def __init__(self, text):
        self.text = text
    def __enter__(self):
        print(self.text, end = ' ', flush = True)
        self.beg = time.time()
    def __exit__(self, *info):
        self.end = time.time()
        print('{:.3f} sec'.format(self.end - self.beg))
class Vector:
    def __init__(self, args):
        self.args = args
    def items(self):
        return self.args.items()
    def keys(self):
        return self.args.keys()
    def values(self):
        return self.args.values()
    def get(self, key, default):
        return self.args.get(key, default)
class Assembly:
    def __init__(self):
        self.cons = [] # constraints
        self.dims = [lambda getw, args: 1] # variables
        self.pubs = {0: 'unit'}
    def con_count(self):
        return len(self.cons)
    def dim_count(self):
        return len(self.dims)
    def setup(self, α, β, γ, δ, x):
        M = self.dim_count()
        N = self.con_count()
        I = 1
        while I < N:
            I = I * 2
        R = pow(T, K // I, P) # primitive I-th root of unity
        xI = [pow(x, i, P) for i in range(I)]
        XI = util.ifft(xI, R, P)
        AxM = [0 for _ in range(M)]
        BxM = [0 for _ in range(M)]
        CxM = [0 for _ in range(M)]
        for X, (aM, bM, cM, msg) in zip(XI, self.cons):
            for m, a in aM.items():
                AxM[m] += a * X
            for m, b in bM.items():
                BxM[m] += b * X
            for m, c in cM.items():
                CxM[m] += c * X
        Zx = pow(x, I, P) - 1
        Γ = util.modinv(γ, P)
        Δ = util.modinv(δ, P)
        α1 = G1 * α
        β1 = G1 * β
        δ1 = G1 * δ
        β2 = G2 * β
        γ2 = G2 * γ
        δ2 = G2 * δ
        u1U = [G1 * ((β * AxM[m] + α * BxM[m] + CxM[m]) * Γ % P) for m in                      self.pubs]
        v1V = [G1 * ((β * AxM[m] + α * BxM[m] + CxM[m]) * Δ % P) for m in range(M) if m not in self.pubs]
        x1I = [G1 * pow(x, i, P) for i in range(I)]
        x2I = [G2 * pow(x, i, P) for i in range(I)]
        y1I = [G1 * (pow(x, i, P) * Δ * Zx % P) for i in range(I - 1)]
        return α1, β1, δ1, β2, γ2, δ2, u1U, v1V, x1I, x2I, y1I
    def prove(self, α1, β1, δ1, β2, δ2, v1V, x1I, x2I, y1I, args, r, s):
        M = self.dim_count()
        N = self.con_count()
        I = 1
        while I < N:
            I = I * 2
        J = I * 2
        R = pow(T, K // I, P) # primitive I-th root of unity
        S = pow(T, K // J, P) # primitive J-th root of unity
        wM = []
        getw = lambda xM: sum(wM[m] * x for m, x in xM.items()) % P
        for func in self.dims:
            wM.append(func(getw, args))
        uU = [wM[m] for m in                      self.pubs]
        vV = [wM[m] for m in range(M) if m not in self.pubs]
        awN = []
        bwN = []
        cwN = []
        for aM, bM, cM, msg in self.cons:
            aw = getw(aM)
            bw = getw(bM)
            cw = getw(cM)
            assert aw * bw % P == cw, msg
            awN.append(aw)
            bwN.append(bw)
            cwN.append(cw)
        AwI = util.ifft(awN + [0] * (I - N), R, P)
        BwI = util.ifft(bwN + [0] * (I - N), R, P)
        CwI = util.ifft(cwN + [0] * (I - N), R, P)
        awI = util.fft([Aw * pow(S, i, P) % P for i, Aw in enumerate(AwI)], R, P) # FFT in coset
        bwI = util.fft([Bw * pow(S, i, P) % P for i, Bw in enumerate(BwI)], R, P) # FFT in coset
        cwI = util.fft([Cw * pow(S, i, P) % P for i, Cw in enumerate(CwI)], R, P) # FFT in coset
        hI = [(P - 1) // 2 * (aw * bw - cw) % P for aw, bw, cw in zip(awI, bwI, cwI)] # (A * B - C) / Z on coset
        HI = [H * pow(S, 0 - i, P) % P for i, H in enumerate(util.ifft(hI, R, P))] # IFFT in coset
        A1 = α1 + δ1 * r
        A1 = sum((x1 * Aw for x1, Aw in zip(x1I, AwI)), A1)
        B1 = β1 + δ1 * s
        B1 = sum((x1 * Bw for x1, Bw in zip(x1I, BwI)), B1)
        B2 = β2 + δ2 * s
        B2 = sum((x2 * Bw for x2, Bw in zip(x2I, BwI)), B2)
        C1 = A1 * s + B1 * r - δ1 * (r * s % P)
        C1 = sum((y1 * H for y1, H in zip(y1I, HI)), C1)
        C1 = sum((v1 * v for v1, v in zip(v1V, vV)), C1)
        return A1, B2, C1, uU
    @staticmethod
    def verify(α1, β2, γ2, δ2, u1U, A1, B2, C1, uU):
        D1 = G1 * 0
        D1 = sum((u1 * u for u1, u in zip(u1U, uU)), D1)
        return pairing.apply(B2, A1) == pairing.apply(β2, α1) + pairing.apply(γ2, D1) + pairing.apply(δ2, C1)
    def __bind(self, func, pubname = None):
        i = len(self.dims)
        self.dims.append(func)
        if pubname is not None:
            self.pubs[i] = pubname
        return Vector({i: 1})
    def VAR(self, name, public = False):
        return self.__bind(lambda getw, args: args[name], name if public else None)
    def REVEAL(self, name, x):
        if isinstance(x, int):
            x = Vector({0: x})
        return self.__bind(lambda getw, args: getw(x), name if name else 'unnamed')
    def ASSERT(self, x, y, z, *, msg = 'assertion error'):
        if isinstance(x, int) and isinstance(y, int) and isinstance(z, int):
            assert x * y % P == z, msg
            return
        if isinstance(x, int):
            x = Vector({0: x})
        if isinstance(y, int):
            y = Vector({0: y})
        if isinstance(z, int):
            z = Vector({0: z})
        self.cons.append((x, y, z, msg))
    def ADD(self, x, y):
        if isinstance(y, int):
            y = Vector({0: y})
        if isinstance(x, int):
            x = Vector({0: x})
        z = Vector({k: v for k in x.keys() | y.keys() if (v := (x.get(k, 0) + y.get(k, 0)) % P)})
        return z.get(0, 0) if z.keys() <= {0} else z
    def SUB(self, x, y):
        if isinstance(y, int):
            y = Vector({0: y})
        if isinstance(x, int):
            x = Vector({0: x})
        z = Vector({k: v for k in x.keys() | y.keys() if (v := (x.get(k, 0) - y.get(k, 0)) % P)})
        return z.get(0, 0) if z.keys() <= {0} else z
    def MUL(self, x, y, *, msg = 'multiplication error'):
        if x == 0 or y == 0:
            return 0
        if isinstance(x, int) and isinstance(y, int):
            return x * y % P
        if isinstance(y, int):
            return Vector({i: m * y % P for i, m in x.items()})
        if isinstance(x, int):
            return Vector({i: m * x % P for i, m in y.items()})
        z = self.__bind(lambda getw, args: getw(x) * getw(y) % P)
        self.ASSERT(x, y, z, msg = msg)
        return z
    def DIV(self, x, y, *, msg = 'division error'):
        if x == 0:
            return 0
        if y == 0:
            raise ZeroDivisionError
        if isinstance(x, int) and isinstance(y, int):
            return x * util.modinv(y, P) % P
        if isinstance(y, int):
            t = util.modinv(y, P)
            return Vector({i: m * t % P for i, m in x.items()})
        if isinstance(x, int):
            x = Vector({0: x})
        z = self.__bind(lambda getw, args: getw(x) * util.modinv(getw(y), P) % P)
        self.ASSERT(z, y, x, msg = msg)
        return z
    def ENUM(self, x, KEYS, *, msg = 'enumerization error'):
        if isinstance(x, int):
            xKey = {K: 1 - pow(x - K, P - 1, P) for K in KEYS}
            assert sum(xKey.values()) == 1, msg
            return xKey
        xKey = {K: 0 for K in KEYS}
        bind = lambda K: self.__bind(lambda getw, args: 1 - pow(getw(x) - K, P - 1, P))
        for K in KEYS:
            b = xKey[K] = bind(K)
            self.ASSERT_ISBOOL(b)
        t = self.SUM(self.MUL(b, K) for K, b in xKey.items())
        e = self.SUM(self.MUL(b, 1) for K, b in xKey.items())
        self.ASSERT_EQ(x, t, msg = msg)
        self.ASSERT_EQ(1, e, msg = msg)
        return xKey
    def BINARY(self, x, XLEN, *, msg = 'binarization error'):
        if isinstance(x, int):
            xBin = [x % P >> I & 1 for I in range(XLEN)]
            assert 0 <= x % P < 2 ** XLEN, msg
            return xBin
        bind = lambda I: self.__bind(lambda getw, args: getw(x) >> I & 1)
        xBin = [0 for _ in range(XLEN)]
        for I in range(XLEN):
            b = xBin[I] = bind(I)
            self.ASSERT_ISBOOL(b)
        t = self.SUM(self.MUL(b, 1 << I) for I, b in enumerate(xBin))
        self.ASSERT_EQ(x, t, msg = msg)
        return xBin
    def NEZ(self, x, *, msg = 'booleanization error'):
        if isinstance(x, int):
            return pow(x, P - 1, P)
        v = self.__bind(lambda getw, args: pow(getw(x), P - 2, P))
        o = self.__bind(lambda getw, args: pow(getw(x), P - 1, P))
        self.ASSERT(o, x, x, msg = msg)
        self.ASSERT(x, v, o, msg = msg)
        return o
    def NOT(self, x):
        return self.SUB(1, x)
    def AND(self, x, y):
        return self.MUL(x, y)
    def OR(self, x, y):
        return self.SUB(1, self.MUL(self.SUB(1, x), self.SUB(1, y)))
    def XOR(self, x, y):
        return self.DIV(self.SUB(1, self.MUL(self.SUB(1, self.MUL(x, 2)), self.SUB(1, self.MUL(y, 2)))), 2)
    def IF(self, b, t, f):
        if isinstance(t, dict) and isinstance(f, dict):
            return dict((k, self.IF(b, t[k], f[k])) for k in t.keys() | f.keys())
        if isinstance(t, list) and isinstance(f, list):
            return list(self.IF(b, t[k], f[k]) for k in range(max(len(t), len(f))))
        if isinstance(t, tuple) and isinstance(f, tuple):
            return tuple(self.IF(b, t[k], f[k]) for k in range(max(len(t), len(f))))
        # return self.ADD(self.MUL(b, t), self.MUL(self.NOT(b), f)) # generate more constraints but faster
        return self.ADD(self.MUL(b, self.SUB(t, f)), f)
    def POW(self, x, nBin):
        b, *nBin = nBin
        r = self.IF(b, x, 1)
        for b in nBin:
            x = self.MUL(x, x)
            k = self.IF(b, x, 1)
            r = self.MUL(r, k)
        return r
    def EXP(self, x, NEXP):
        NBIN = []
        while NEXP > 0:
            NBIN.append(NEXP & 1)
            NEXP = NEXP >> 1
        return self.POW(x, NBIN if NBIN else [0])
    def SUM(self, List):
        r = 0
        for i in List:
            r = self.ADD(r, i)
        return r
    def VAL(self, xBin):
        return self.SUM(self.MUL(b, 1 << I) for I, b in enumerate(xBin))
    def GETBYKEY(self, Value, iKey):
        if isinstance(Value, dict):
            if all(isinstance(V, dict) for V in Value.values()):
                return dict((k, self.GETBYKEY({K: V[k] for K, V in Value.items()}, iKey)) for k in set.union(*map(set, Value.values())))
            if all(isinstance(V, list) for V in Value.values()):
                return list(self.GETBYKEY({K: V[k] for K, V in Value.items()}, iKey) for k in range(max(map(len, Value.values()))))
            if all(isinstance(V, tuple) for V in Value.values()):
                return tuple(self.GETBYKEY({K: V[k] for K, V in Value.items()}, iKey) for k in range(max(map(len, Value.values()))))
        if isinstance(Value, list):
            if all(isinstance(V, dict) for V in Value):
                return dict((k, self.GETBYKEY([V[k] for V in Value], iKey)) for k in set.union(*map(set, Value)))
            if all(isinstance(V, list) for V in Value):
                return list(self.GETBYKEY([V[k] for V in Value], iKey) for k in range(max(map(len, Value))))
            if all(isinstance(V, tuple) for V in Value):
                return tuple(self.GETBYKEY([V[k] for V in Value], iKey) for k in range(max(map(len, Value))))
        return self.SUM(self.MUL(iKey[K], Value[K]) for K in iKey)
    def SETBYKEY(self, v, Value, *iKeys, c = 1):
        if len(iKeys) == 0:
            return self.IF(c, v, Value)
        iKey, *iKeys = iKeys
        if isinstance(Value, dict):
            return {K: self.SETBYKEY(v, V, *iKeys, c = self.AND(c, iKey[K])) for K, V in Value.items()}
        if isinstance(Value, list):
            return [self.SETBYKEY(v, V, *iKeys, c = self.AND(c, iKey[K])) for K, V in enumerate(Value)]
    def GE(self, x, y, BLEN): # 0 <= x - y < 2 ** BLEN
        return self.BINARY(self.ADD(2 ** BLEN, self.SUB(x, y)), BLEN + 1)[BLEN]
    def LE(self, x, y, BLEN): # 0 <= y - x < 2 ** BLEN
        return self.BINARY(self.ADD(2 ** BLEN, self.SUB(y, x)), BLEN + 1)[BLEN]
    def GT(self, x, y, BLEN): # 0 < x - y <= 2 ** BLEN
        return self.BINARY(self.ADD(2 ** BLEN, self.SUB(self.SUB(x, y), 1)), BLEN + 1)[BLEN]
    def LT(self, x, y, BLEN): # 0 < y - x <= 2 ** BLEN
        return self.BINARY(self.ADD(2 ** BLEN, self.SUB(self.SUB(y, x), 1)), BLEN + 1)[BLEN]
    def ASSERT_GE(self, x, y, BLEN, *, msg = 'GE check failed'): # assert 0 <= x - y < 2 ** BLEN
        return self.BINARY(self.SUB(x, y), BLEN, msg = msg)
    def ASSERT_LE(self, x, y, BLEN, *, msg = 'LE check failed'): # assert 0 <= y - x < 2 ** BLEN
        return self.BINARY(self.SUB(y, x), BLEN, msg = msg)
    def ASSERT_GT(self, x, y, BLEN, *, msg = 'GT check failed'): # assert 0 < x - y <= 2 ** BLEN
        return self.BINARY(self.SUB(self.SUB(x, y), 1), BLEN, msg = msg)
    def ASSERT_LT(self, x, y, BLEN, *, msg = 'LT check failed'): # assert 0 < y - x <= 2 ** BLEN
        return self.BINARY(self.SUB(self.SUB(y, x), 1), BLEN, msg = msg)
    def ASSERT_EQ(self, x, y, *, msg = 'EQ check failed'):
        self.ASSERT(1, x, y, msg = msg)
    def ASSERT_NE(self, x, y, *, msg = 'NE check failed'):
        self.DIV(1, self.SUB(x, y), msg = msg)
    def ASSERT_ISBOOL(self, x, *, msg = 'ISBOOL check failed'):
        self.ASSERT(x, x, x, msg = msg)
    def ROTL(self, xBin, NROT):
        NROT = -NROT % len(xBin)
        return xBin[NROT:] + xBin[:NROT]
    def ROTR(self, xBin, NROT):
        NROT = +NROT % len(xBin)
        return xBin[NROT:] + xBin[:NROT]
    def BITNOT(self, xBin):
        return [self.NOT(b) for b in xBin]
    def BITAND(self, xBin, yBin):
        # assert len(xBin) == len(yBin)
        return [self.AND(a, b) for a, b in zip(xBin, yBin)]
    def BITOR(self, xBin, yBin):
        # assert len(xBin) == len(yBin)
        return [self.OR(a, b) for a, b in zip(xBin, yBin)]
    def BITXOR(self, xBin, yBin):
        # assert len(xBin) == len(yBin)
        return [self.XOR(a, b) for a, b in zip(xBin, yBin)]
    def BINADD(self, xBin, yBin, c = 0):
        # assert len(xBin) == len(yBin)
        BLEN = max(len(xBin), len(yBin))
        zBin = self.BINARY(self.ADD(self.VAL(xBin), self.ADD(self.VAL(self.ADD(0, b) for b in yBin), self.ADD(0, c))), BLEN + 1)
        return zBin[:BLEN], self.ADD(0, zBin[BLEN])
    def BINSUB(self, xBin, yBin, c = 0):
        # assert len(xBin) == len(yBin)
        BLEN = max(len(xBin), len(yBin))
        zBin = self.BINARY(self.ADD(self.VAL(xBin), self.ADD(self.VAL(self.SUB(1, b) for b in yBin), self.SUB(1, c))), BLEN + 1)
        return zBin[:BLEN], self.SUB(1, zBin[BLEN])
    def BINMUL(self, xBin, yBin, cBin = [], dBin = []):
        # assert len(xBin) == len(yBin)
        BLEN = max(len(xBin), len(yBin))
        assert len(cBin) <= BLEN
        assert len(dBin) <= BLEN
        zBin = self.BINARY(self.ADD(self.MUL(self.VAL(xBin), self.VAL(yBin)), self.ADD(self.VAL(cBin), self.VAL(dBin))), BLEN * 2)
        return zBin[:BLEN], zBin[BLEN:]
    def BINDIVMOD(self, xBin, yBin, *, msg = 'binary divmod error'):
        QLEN = len(xBin)
        RLEN = len(yBin)
        x = self.VAL(xBin)
        y = self.VAL(yBin)
        if x == 0:
            return [0] * QLEN, [0] * RLEN
        if y == 0:
            raise ZeroDivisionError
        if isinstance(x, int) and isinstance(y, int):
            assert 0 <= x // y < 2 ** QLEN, msg
            assert 0 <= x % y < 2 ** RLEN, msg
            return [x // y >> I & 1 for I in range(QLEN)], [x % y >> I & 1 for I in range(RLEN)]
        if isinstance(x, int):
            x = Vector({0: x})
        if isinstance(y, int):
            y = Vector({0: y})
        q = self.__bind(lambda getw, args: getw(x) // getw(y))
        r = self.__bind(lambda getw, args: getw(x) % getw(y))
        self.ASSERT(q, y, self.SUB(x, r), msg = msg) # assert y * q == x - r
        qBin = self.ASSERT_GE(q, 0, QLEN, msg = msg)
        rBin = self.ASSERT_GE(r, 0, RLEN, msg = msg)
        _Bin = self.ASSERT_LT(r, y, RLEN, msg = msg)
        return qBin, rBin
    def BINPOW(self, xBin, nBin):
        BLEN = len(xBin)
        b, *nBin = nBin
        rBin = self.IF(b, xBin, self.BINARY(1, BLEN))
        for b in nBin:
            xBin = self.BINMUL(xBin, xBin)[0]
            kBin = self.IF(b, xBin, self.BINARY(1, BLEN))
            rBin = self.BINMUL(rBin, kBin)[0]
        return rBin
    def BINEXP(self, xBin, NEXP):
        NBIN = []
        while NEXP > 0:
            NBIN.append(NEXP & 1)
            NEXP = NEXP >> 1
        return self.BINPOW(xBin, NBIN if NBIN else [0])
    def BINGE(self, xBin, yBin):
        # assert len(xBin) == len(yBin)
        BLEN = max(len(xBin), len(yBin))
        return self.BINARY(self.ADD(2 ** BLEN, self.SUB(self.VAL(xBin), self.VAL(yBin))), BLEN + 1)[BLEN]
    def BINLE(self, xBin, yBin):
        # assert len(xBin) == len(yBin)
        BLEN = max(len(xBin), len(yBin))
        return self.BINARY(self.ADD(2 ** BLEN, self.SUB(self.VAL(yBin), self.VAL(xBin))), BLEN + 1)[BLEN]
    def BINGT(self, xBin, yBin):
        # assert len(xBin) == len(yBin)
        BLEN = max(len(xBin), len(yBin))
        return self.BINARY(self.ADD(2 ** BLEN, self.SUB(self.SUB(self.VAL(xBin), self.VAL(yBin)), 1)), BLEN + 1)[BLEN]
    def BINLT(self, xBin, yBin):
        # assert len(xBin) == len(yBin)
        BLEN = max(len(xBin), len(yBin))
        return self.BINARY(self.ADD(2 ** BLEN, self.SUB(self.SUB(self.VAL(yBin), self.VAL(xBin)), 1)), BLEN + 1)[BLEN]
    def ASSERT_BINGE(self, xBin, yBin, *, msg = 'BINGE check failed'):
        # assert len(xBin) == len(yBin)
        BLEN = max(len(xBin), len(yBin))
        self.BINARY(self.SUB(self.VAL(xBin), self.VAL(yBin)), BLEN, msg = msg)
    def ASSERT_BINLE(self, xBin, yBin, *, msg = 'BINLE check failed'):
        # assert len(xBin) == len(yBin)
        BLEN = max(len(xBin), len(yBin))
        self.BINARY(self.SUB(self.VAL(yBin), self.VAL(xBin)), BLEN, msg = msg)
    def ASSERT_BINGT(self, xBin, yBin, *, msg = 'BINGT check failed'):
        # assert len(xBin) == len(yBin)
        BLEN = max(len(xBin), len(yBin))
        self.BINARY(self.SUB(self.SUB(self.VAL(xBin), self.VAL(yBin)), 1), BLEN, msg = msg)
    def ASSERT_BINLT(self, xBin, yBin, *, msg = 'BINLT check failed'):
        # assert len(xBin) == len(yBin)
        BLEN = max(len(xBin), len(yBin))
        self.BINARY(self.SUB(self.SUB(self.VAL(yBin), self.VAL(xBin)), 1), BLEN, msg = msg)
def isint(x):
    return isinstance(x, int)
def isval(x):
    return isinstance(x, int | Vector)
def isbin(x):
    return isinstance(x, list) and all(isinstance(b, int | Vector) for b in x)
def asint(x):
    if isinstance(x, int):
        return x
    raise TypeError('expected a constant value')
def asval(x):
    if isinstance(x, int | Vector):
        return x
    raise TypeError('expected a value')
def asbin(x):
    if isinstance(x, list) and all(isinstance(b, int | Vector) for b in x):
        return x
    raise TypeError('expected a binary')
def shape(x):
    if isinstance(x, int | Vector):
        return (), None
    if isinstance(x, tuple):
        return (), tuple(shape(v) for v in x)
    if isinstance(x, list):
        shapes = {shape(v) for v in x}
        if len(shapes) == 1:
            outer, inner = shapes.pop()
            return (range(len(x)), *outer), inner
        raise TypeError('inconsistent shape of list elements')
    if isinstance(x, dict):
        shapes = {shape(v) for v in x.values()}
        if len(shapes) == 1:
            outer, inner = shapes.pop()
            return (frozenset(x), *outer), inner
        raise TypeError('inconsistent shape of dict values')
    raise TypeError('unsupported data type')
class Compiler(ast.NodeVisitor, Assembly):
    def __init__(self):
        ast.NodeVisitor.__init__(self)
        Assembly.__init__(self)
        self.stack = [{
            'range': lambda *args: range(*map(asint, args)),
            'log': lambda fmt, *args: print(fmt.format(*args)),
            'val': lambda x: self.VAL(x) if isbin(x) else asval(x),
            'b8':  lambda x: (x + [0] *  8)[: 8] if isbin(x) else self.BINARY(asval(x),  8),
            'b16': lambda x: (x + [0] * 16)[:16] if isbin(x) else self.BINARY(asval(x), 16),
            'b32': lambda x: (x + [0] * 32)[:32] if isbin(x) else self.BINARY(asval(x), 32),
            'b64': lambda x: (x + [0] * 64)[:64] if isbin(x) else self.BINARY(asval(x), 64),
            'bin': lambda x, n: (x + [0] * asint(n))[:n] if isbin(x) else self.BINARY(asval(x), asint(n)),
            'private': lambda fmt, *args: self.VAR(fmt.format(*args) if args else fmt),
            'public': lambda fmt, *args: self.VAR(fmt.format(*args) if args else fmt, public = True),
            'reveal': lambda x, fmt, *args: self.REVEAL(fmt.format(*args) if args else fmt, self.VAL(x) if isbin(x) else asval(x)),
        }]
    def visit_Module(self, node):
        for stmt in node.body:
            flag, result = self.visit(stmt)
            if flag == 'continue' or flag == 'break' or flag == 'return':
                raise SyntaxError('unexpected ' + flag)
    def visit_Continue(self, node):
        return 'continue', None
    def visit_Break(self, node):
        return 'break', None
    def visit_Return(self, node):
        return 'return', self.visit(node.value) if node.value else None
    def visit_If(self, node):
        if asint(self.visit(node.test)):
            for stmt in node.body:
                flag, result = self.visit(stmt)
                if flag == 'continue' or flag == 'break' or flag == 'return':
                    return flag, result
        else:
            for stmt in node.orelse:
                flag, result = self.visit(stmt)
                if flag == 'continue' or flag == 'break' or flag == 'return':
                    return flag, result
        return None, None
    def visit_While(self, node):
        while asint(self.visit(node.test)):
            for stmt in node.body:
                flag, result = self.visit(stmt)
                if flag == 'continue' or flag == 'break' or flag == 'return':
                    break
            else:
                continue
            if flag == 'continue':
                continue
            if flag == 'break':
                break
            if flag == 'return':
                return flag, result
        else:
            for stmt in node.orelse:
                flag, result = self.visit(stmt)
                if flag == 'continue' or flag == 'break' or flag == 'return':
                    return flag, result
        return None, None
    def visit_For(self, node):
        if not isinstance(node.target, ast.Name):
            raise SyntaxError('invalid iteration target')
        iter = self.visit(node.iter)
        if isinstance(iter, range):
            iter = iter
        elif isinstance(iter, list):
            iter = range(len(iter))
        elif isinstance(iter, dict):
            iter = iter.keys()
        else:
            raise TypeError('iteration can only be performed on range, list or dict')
        for value in iter:
            self.stack[-1][node.target.id] = value
            for stmt in node.body:
                flag, result = self.visit(stmt)
                if flag == 'continue' or flag == 'break' or flag == 'return':
                    break
            else:
                continue
            if flag == 'continue':
                continue
            if flag == 'break':
                break
            if flag == 'return':
                return flag, result
        else:
            for stmt in node.orelse:
                flag, result = self.visit(stmt)
                if flag == 'continue' or flag == 'break' or flag == 'return':
                    return flag, result
        return None, None
    def visit_ListComp(self, node):
        def visit(generators):
            if len(generators) == 0:
                yield self.visit(node.elt)
                return
            generator, *generators = generators
            if not isinstance(generator.target, ast.Name):
                raise SyntaxError('invalid iteration target')
            iter = self.visit(generator.iter)
            if isinstance(iter, range):
                iter = iter
            elif isinstance(iter, list):
                iter = range(len(iter))
            elif isinstance(iter, dict):
                iter = iter.keys()
            else:
                raise TypeError('iteration can only be performed on range, list or dict')
            call_stack = self.stack
            self.stack = self.stack + [{}]
            for value in iter:
                self.stack[-1][generator.target.id] = value
                if all(asint(self.visit(test)) for test in generator.ifs):
                    yield from visit(generators)
            self.stack = call_stack
        return list(visit(node.generators))
    def visit_DictComp(self, node):
        def visit(generators):
            if len(generators) == 0:
                yield asint(self.visit(node.key)), self.visit(node.value)
                return
            generator, *generators = generators
            if not isinstance(generator.target, ast.Name):
                raise SyntaxError('invalid iteration target')
            iter = self.visit(generator.iter)
            if isinstance(iter, range):
                iter = iter
            elif isinstance(iter, list):
                iter = range(len(iter))
            elif isinstance(iter, dict):
                iter = iter.keys()
            else:
                raise TypeError('iteration can only be performed on range, list or dict')
            call_stack = self.stack
            self.stack = self.stack + [{}]
            for value in iter:
                self.stack[-1][generator.target.id] = value
                if all(asint(self.visit(test)) for test in generator.ifs):
                    yield from visit(generators)
            self.stack = call_stack
        return dict(visit(node.generators))
    def visit_Tuple(self, node):
        return tuple(self.visit(elt) for elt in node.elts)
    def visit_List(self, node):
        return list(self.visit(elt) for elt in node.elts)
    def visit_Dict(self, node):
        return dict((asint(self.visit(key)), self.visit(value)) for key, value in zip(node.keys, node.values))
    def visit_Pass(self, node):
        return None, None
    def visit_Expr(self, node):
        self.visit(node.value)
        return None, None
    def visit_Assert(self, node):
        test = self.visit(node.test)
        if node.msg is None:
            self.ASSERT_NE(0, asval(test))
        else:
            self.ASSERT_NE(0, asval(test), msg = self.visit(node.msg))
        return None, None
    def visit_FunctionDef(self, node):
        def_stack = self.stack
        def func(*args):
            if len(args) != len(node.args.args):
                raise TypeError('mismatched number of arguments')
            call_stack = self.stack
            self.stack = def_stack + [{}]
            for target, arg in zip(node.args.args, args):
                self.stack[-1][target.arg] = arg
            for stmt in node.body:
                flag, result = self.visit(stmt)
                if flag == 'break' or flag == 'continue':
                    raise SyntaxError('unexpected ' + flag)
                if flag == 'return':
                    break
            else:
                result = None
            self.stack = call_stack
            return result
        self.stack[-1][node.name] = func
        return None, None
    def visit_Lambda(self, node):
        def_stack = self.stack
        def func(*args):
            if len(args) != len(node.args.args):
                raise TypeError('mismatched number of arguments')
            call_stack = self.stack
            self.stack = def_stack + [{}]
            for target, arg in zip(node.args.args, args):
                self.stack[-1][target.arg] = arg
            result = self.visit(node.body)
            self.stack = call_stack
            return result
        return func
    def visit_Assign(self, node):
        def assign(target, value):
            if isinstance(target, ast.Tuple):
                if not isinstance(value, tuple) or len(target.elts) != len(value):
                    raise TypeError('mismatched number of targets and values in assignment')
                for target, value in zip(target.elts, value):
                    assign(target, value)
                return
            if isinstance(target, ast.Name):
                self.stack[-1][target.id] = value
                return
            slices = []
            while not isinstance(target, ast.Name):
                if not isinstance(target, ast.Subscript):
                    raise SyntaxError('invalid assignment target')
                slices.append(self.visit(target.slice))
                target = target.value
            dest = self.visit(target)
            outer, inner = shape(dest)
            enums = []
            for slice in reversed(slices):
                if len(outer) == 0:
                    raise TypeError('cannot index a scalar')
                keys, *outer = outer
                enums.append(self.ENUM(self.VAL(slice) if isbin(slice) else asval(slice), keys))
            if (tuple(outer), inner) != shape(value):
                raise TypeError('inconsistent shape of target and value in indexed assignment')
            self.stack[-1][target.id] = self.SETBYKEY(value, dest, *enums)
        value = self.visit(node.value)
        for target in node.targets:
            assign(target, value)
        return None, None
    def visit_Delete(self, node):
        for target in node.targets:
            if not isinstance(target, ast.Name):
                raise SyntaxError('invalid deletion target')
            self.stack[-1].pop(target.id)
        return None, None
    def visit_Name(self, node):
        for scope in reversed(self.stack):
            if node.id in scope:
                return scope[node.id]
        raise NameError('undefined name: {}'.format(node.id))
    def visit_Subscript(self, node):
        slice = self.visit(node.slice)
        value = self.visit(node.value)
        outer, inner = shape(value)
        if len(outer) == 0:
            raise TypeError('cannot index a scalar')
        keys, *outer = outer
        return self.GETBYKEY(value, self.ENUM(self.VAL(slice) if isbin(slice) else asval(slice), keys))
    def visit_Call(self, node):
        return self.visit(node.func)(*map(self.visit, node.args))
    def visit_Constant(self, node):
        if isinstance(node.value, int):
            return node.value % P
        if isinstance(node.value, bool):
            return int(node.value)
        if isinstance(node.value, str):
            return node.value
        raise SyntaxError('invalid constant')
    def visit_BinOp(self, node):
        left = self.visit(node.left)
        right = self.visit(node.right)
        if isinstance(node.op, ast.Add):
            return self.BINADD(left, right)[0] if isbin(left) and isbin(right) else self.ADD(asval(left), asval(right))
        if isinstance(node.op, ast.Sub):
            return self.BINSUB(left, right)[0] if isbin(left) and isbin(right) else self.SUB(asval(left), asval(right))
        if isinstance(node.op, ast.Mult):
            return self.BINMUL(left, right)[0] if isbin(left) and isbin(right) else self.MUL(asval(left), asval(right))
        if isinstance(node.op, ast.Div):
            return self.DIV(asval(left), asval(right))
        if isinstance(node.op, ast.Pow):
            return (self.POW(left, right) if isbin(left) else self.BINPOW(asval(left), right)) if isbin(right) else (self.EXP(left, asint(right)) if isbin(left) else self.POW(asval(left), asint(right)))
        if isinstance(node.op, ast.FloorDiv):
            return self.BINDIVMOD(asbin(left), asbin(right))[0]
        if isinstance(node.op, ast.Mod):
            return self.BINDIVMOD(asbin(left), asbin(right))[1]
        if isinstance(node.op, ast.BitAnd):
            return self.BITAND(asbin(left), asbin(right))
        if isinstance(node.op, ast.BitOr):
            return self.BITOR(asbin(left), asbin(right))
        if isinstance(node.op, ast.BitXor):
            return self.BITXOR(asbin(left), asbin(right))
        if isinstance(node.op, ast.LShift):
            return self.ROTL(asbin(left), asint(right))
        if isinstance(node.op, ast.RShift):
            return self.ROTR(asbin(left), asint(right))
        raise SyntaxError('unsupported binary operation')
    def visit_UnaryOp(self, node):
        operand = self.visit(node.operand)
        if isinstance(node.op, ast.Invert):
            return self.BITNOT(asbin(operand))
        if isinstance(node.op, ast.Not):
            return self.NOT(asval(operand))
        raise SyntaxError('unsupported unary operation')
    def visit_BoolOp(self, node):
        if isinstance(node.op, ast.And):
            result = 1
            for value in node.values:
                result = self.AND(result, asval(self.visit(value)))
            return result
        if isinstance(node.op, ast.Or):
            result = 0
            for value in node.values:
                result = self.OR(result, asval(self.visit(value)))
            return result
        raise SyntaxError('unsupported boolean operation')
    def visit_Compare(self, node):
        result = 1
        left = self.visit(node.left)
        for op, right in zip(node.ops, map(self.visit, node.comparators)):
            if isinstance(op, ast.Eq):
                result = self.AND(result, self.NOT(self.NEZ(self.SUB(self.VAL(left) if isbin(left) else asval(left), self.VAL(right) if isbin(right) else asval(right)))))
            elif isinstance(op, ast.NotEq):
                result = self.AND(result, self.NEZ(self.SUB(self.VAL(left) if isbin(left) else asval(left), self.VAL(right) if isbin(right) else asval(right))))
            elif isinstance(op, ast.Lt):
                result = self.AND(result, self.BINLT(asbin(left), asbin(right)))
            elif isinstance(op, ast.LtE):
                result = self.AND(result, self.BINLE(asbin(left), asbin(right)))
            elif isinstance(op, ast.Gt):
                result = self.AND(result, self.BINGT(asbin(left), asbin(right)))
            elif isinstance(op, ast.GtE):
                result = self.AND(result, self.BINGE(asbin(left), asbin(right)))
            else:
                raise SyntaxError('unsupported comparison')
            left = right
        return result
    def visit_IfExp(self, node):
        left = self.visit(node.body)
        right = self.visit(node.orelse)
        if shape(left) != shape(right):
            raise TypeError('inconsistent shape of left and right values in conditional expression')
        return self.IF(asval(self.visit(node.test)), left, right)
    def generic_visit(self, node):
        raise SyntaxError('unsupported syntax')
if __name__ == '__main__':
    with Timer('Compiling program...'):
        asm = Compiler()
        asm.visit(ast.parse(
            "P0 = lambda x: x ^ (x << 9) ^ (x << 17)\n"
            "P1 = lambda x: x ^ (x << 15) ^ (x << 23)\n"
            "F0 = lambda x, y, z: x ^ y ^ z\n"
            "F1 = lambda x, y, z: (x & y) | (z & (x | y))\n"
            "G0 = lambda x, y, z: x ^ y ^ z\n"
            "G1 = lambda x, y, z: (x & y) | (z & ~x)\n"
            "T0 = b32(0x79cc4519)\n"
            "T1 = b32(0x7a879d8a)\n"
            "def compress(V, I):\n"
            "    W = [b32(0) for _ in range(68)]\n"
            "    for j in range(0, 16):\n"
            "        W[j] = I[j]\n"
            "    for j in range(16, 68):\n"
            "        W[j] = P1(W[j - 16] ^ W[j - 9] ^ (W[j - 3] << 15)) ^ (W[j - 13] << 7) ^ W[j - 6]\n"
            "    A = V[0]\n"
            "    B = V[1]\n"
            "    C = V[2]\n"
            "    D = V[3]\n"
            "    E = V[4]\n"
            "    F = V[5]\n"
            "    G = V[6]\n"
            "    H = V[7]\n"
            "    for j in range(0, 64):\n"
            "        if b8(j) < b8(16):\n"
            "            SS1 = ((A << 12) + E + (T0 << j)) << 7\n"
            "            SS2 = SS1 ^ (A << 12)\n"
            "            TT1 = F0(A, B, C) + D + SS2 + (W[j] ^ W[j + 4])\n"
            "            TT2 = G0(E, F, G) + H + SS1 + W[j]\n"
            "        else:\n"
            "            SS1 = ((A << 12) + E + (T1 << j)) << 7\n"
            "            SS2 = SS1 ^ (A << 12)\n"
            "            TT1 = F1(A, B, C) + D + SS2 + (W[j] ^ W[j + 4])\n"
            "            TT2 = G1(E, F, G) + H + SS1 + W[j]\n"
            "        A, B, C, D, E, F, G, H = TT1, A, B << 9, C, P0(TT2), E, F << 19, G\n"
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
            "W = [b32(private('W[{:#04x}]', i)) for i in range(16)]\n"
            "V = compress(V, W)\n"
            "for i in range(8):\n"
            "    reveal(V[i], 'V[{:#04x}]', i)\n"
        ))
    print('Number of constraints:', asm.con_count())
    print('Number of dimensions:', asm.dim_count())
    with Timer('Setting up QAP...'):
        α = random.randrange(1, P)
        β = random.randrange(1, P)
        γ = random.randrange(1, P)
        δ = random.randrange(1, P)
        x = random.randrange(1, P)
        α1, β1, δ1, β2, γ2, δ2, u1U, v1V, x1I, x2I, y1I = asm.setup(α, β, γ, δ, x)
    with Timer('Generating witness...'):
        args = {'W[{:#04x}]'.format(i): v for i, v in enumerate([0x61626380] + [0x00000000] * 14 + [0x00000018])}
        r = random.randrange(1, P)
        s = random.randrange(1, P)
        A1, B2, C1, uU = asm.prove(α1, β1, δ1, β2, δ2, v1V, x1I, x2I, y1I, args, r, s)
    with Timer('Verifying...'):
        passed = asm.verify(α1, β2, γ2, δ2, u1U, A1, B2, C1, uU)
    if passed:
        print('Verification passed!')
        print('Public witness:', '{{{}}}'.format(', '.join('{} = {:#010x}'.format(k, u) for k, u in zip(asm.pubs.values(), uU))))
    else:
        print('Verification failed!')
