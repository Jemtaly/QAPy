#!/usr/bin/python3
import time
import util
import ast
import random
import pymcl
import multiprocessing
import copy
# the BLS12-381 curve parameters
g1 = pymcl.g1
g2 = pymcl.g2
ρ = pymcl.r
# find the largest K such that P - 1 is divisible by 2 ** K, and Z is a primitive root of unity, they are used to perform FFT
K = 1
while (ρ - 1) % (K * 2) == 0:
    K = K * 2
for Z in range(2, ρ):
    if pow(Z, (ρ - 1) // 2, ρ) != 1:
        break
T = pow(Z, (ρ - 1) // K, ρ)
# scalar multiplication and dot product optimized for parallel execution
THREADS = None # automatically set to the number of CPU cores
def worker(Group, p, z):
    return str(Group(p) * pymcl.Fr(z))
def scalar_mult_parallel(P, Zs):
    Group = type(P)
    with multiprocessing.Pool(THREADS) as pool:
        return [Group(q) for q in pool.starmap(worker, ((Group, str(P), str(Z)) for Z in Zs))]
def dot_prod_parallel(O, Ps, Zs):
    Group = type(O)
    with multiprocessing.Pool(THREADS) as pool:
        return sum((Group(q) for q in pool.starmap(worker, ((Group, str(P), str(Z)) for P, Z in zip(Ps, Zs)))), O)
class Var:
    # All variables in a program are linear combinations of the variables in its witness vector, so they
    # can be represented by a dictionary that maps the indices of the variables in the witness vector to
    # their coefficients, for example, x = w0 + 5 * w2 + 7 * w3 can be represented as {0: 1, 2: 5, 3: 7},
    # note that the variables with coefficient 0 are always omitted.
    # Constants are represented by the integer itself.
    def __init__(self, data):
        self.data = data
class Assembly:
    # The Assembly class is used to construct the arithmetic circuits, it provides a set of methods to
    # create and manipulate the variables, and to perform arithmetic operations on them. The arithmetic
    # operations are represented as the constraints in the circuit. Besides, the Assembly class also
    # provides the setup, prove, and verify methods of the Groth16 zk-SNARK.
    def __init__(self):
        self.gates = [] # the constraints in the circuit
        self.wires = [lambda getw, args: 1] # the functions that represent the variables, used to generate the witness vector
        self.stmts = {0: 'unit'} # the public variables in the witness, keys are the indices of the variables in the witness vector
        self.enums = {} # memoization of the enum values
    def gate_count(self):
        return len(self.gates)
    def wire_count(self):
        return len(self.wires)
    # Groth16 zk-SNARK setup, prove, and verify methods
    def setup(self, α, β, γ, δ, x):
        M = self.wire_count()
        N = self.gate_count()
        I = 1
        while I < N:
            I = I * 2
        R = pow(T, K // I, ρ) # primitive I-th root of unity, used to perform FFT
        xI = [pow(x, i, ρ) for i in range(I)]
        XI = util.ifft(xI, R, ρ)
        AxM = [0x00 for _ in range(M)]
        BxM = [0x00 for _ in range(M)]
        CxM = [0x00 for _ in range(M)]
        for X, (aM, bM, cM, msg) in zip(XI, self.gates):
            for m, a in aM.data.items():
                AxM[m] += a * X
            for m, b in bM.data.items():
                BxM[m] += b * X
            for m, c in cM.data.items():
                CxM[m] += c * X
        Zx = pow(x, I, ρ) - 0x01
        Γ = pow(γ, -1, ρ)
        Δ = pow(δ, -1, ρ)
        α1 = g1 * pymcl.Fr(str(α))
        β1 = g1 * pymcl.Fr(str(β))
        δ1 = g1 * pymcl.Fr(str(δ))
        β2 = g2 * pymcl.Fr(str(β))
        γ2 = g2 * pymcl.Fr(str(γ))
        δ2 = g2 * pymcl.Fr(str(δ))
        u1U = scalar_mult_parallel(g1, [(β * AxM[m] + α * BxM[m] + CxM[m]) * Γ % ρ for m in                      self.stmts])
        v1V = scalar_mult_parallel(g1, [(β * AxM[m] + α * BxM[m] + CxM[m]) * Δ % ρ for m in range(M) if m not in self.stmts])
        x1I = scalar_mult_parallel(g1, [pow(x, i, ρ) for i in range(I)])
        x2I = scalar_mult_parallel(g2, [pow(x, i, ρ) for i in range(I)])
        y1I = scalar_mult_parallel(g1, [pow(x, i, ρ) * Δ * Zx % ρ for i in range(I - 1)])
        return α1, β1, δ1, β2, γ2, δ2, u1U, v1V, x1I, x2I, y1I
    def prove(self, α1, β1, δ1, β2, δ2, v1V, x1I, x2I, y1I, args, r, s):
        M = self.wire_count()
        N = self.gate_count()
        I = 1
        while I < N:
            I = I * 2
        J = I * 2
        R = pow(T, K // I, ρ) # primitive I-th root of unity, used to perform FFT
        S = pow(T, K // J, ρ) # primitive J-th root of unity, used to convert the FFT result to the coset
        wM = []
        getw = lambda xM: sum(wM[m] * x for m, x in xM.data.items()) % ρ
        for func in self.wires:
            wM.append(func(getw, args))
        uU = [wM[m] for m in                      self.stmts]
        vV = [wM[m] for m in range(M) if m not in self.stmts]
        awN = []
        bwN = []
        cwN = []
        for aM, bM, cM, msg in self.gates:
            aw = getw(aM)
            bw = getw(bM)
            cw = getw(cM)
            assert aw * bw % ρ == cw, msg
            awN.append(aw)
            bwN.append(bw)
            cwN.append(cw)
        AwI = util.ifft(awN + [0x00] * (I - N), R, ρ)
        BwI = util.ifft(bwN + [0x00] * (I - N), R, ρ)
        CwI = util.ifft(cwN + [0x00] * (I - N), R, ρ)
        awI = util.fft([Aw * pow(S, i, ρ) % ρ for i, Aw in enumerate(AwI)], R, ρ) # FFT in coset
        bwI = util.fft([Bw * pow(S, i, ρ) % ρ for i, Bw in enumerate(BwI)], R, ρ) # FFT in coset
        cwI = util.fft([Cw * pow(S, i, ρ) % ρ for i, Cw in enumerate(CwI)], R, ρ) # FFT in coset
        hI = [(ρ - 1) // 2 * (aw * bw - cw) % ρ for aw, bw, cw in zip(awI, bwI, cwI)] # (A * B - C) / Z on coset
        HI = [H * pow(S, 0 - i, ρ) % ρ for i, H in enumerate(util.ifft(hI, R, ρ))] # IFFT in coset
        A1 = α1 + δ1 * pymcl.Fr(str(r))
        A1 = dot_prod_parallel(A1, x1I, AwI)
        B1 = β1 + δ1 * pymcl.Fr(str(s))
        B1 = dot_prod_parallel(B1, x1I, BwI)
        B2 = β2 + δ2 * pymcl.Fr(str(s))
        B2 = dot_prod_parallel(B2, x2I, BwI)
        C1 = A1 * pymcl.Fr(str(s)) + B1 * pymcl.Fr(str(r)) - δ1 * pymcl.Fr(str(r * s % ρ))
        C1 = dot_prod_parallel(C1, y1I, HI)
        C1 = dot_prod_parallel(C1, v1V, vV)
        return A1, B2, C1, uU
    @staticmethod
    def verify(α1, β2, γ2, δ2, u1U, A1, B2, C1, uU):
        D1 = g1 * pymcl.Fr(str(0))
        D1 = dot_prod_parallel(D1, u1U, uU)
        return pymcl.pairing(A1, B2) == pymcl.pairing(α1, β2) * pymcl.pairing(D1, γ2) * pymcl.pairing(C1, δ2)
    # the following methods are used to construct the arithmetic circuits
    def MKWIRE(self, func, name = None):
        # Add a new variable that defined by the given function to the witness vector.
        # For example, x = MKWIRE(lambda getw, args: getw(y) * getw(z) % P) will add a new variable x
        # to the witness vector, and its value is the product of the values of y and z.
        i = len(self.wires)
        self.wires.append(func)
        # if name is specified, the variable is public
        if name is not None:
            self.stmts[i] = name
        return Var({i: 0x01})
    def MKGATE(self, xGal, yGal, zGal, *, msg = 'assertion error'):
        # Add a constraint to the circuit, the constraint is represented as a tuple (x, y, z, msg),
        # which means x * y = z, the msg is the error message when the constraint is not satisfied.
        if isinstance(xGal, int) and isinstance(yGal, int) and isinstance(zGal, int):
            assert xGal * yGal % ρ == zGal, msg
            return
        if isinstance(xGal, int):
            xGal = Var({0: xGal})
        if isinstance(yGal, int):
            yGal = Var({0: yGal})
        if isinstance(zGal, int):
            zGal = Var({0: zGal})
        self.gates.append((xGal, yGal, zGal, msg))
    # arithmetic operations on variables
    def ADD(self, xGal, yGal):
        if isinstance(yGal, int):
            yGal = Var({0: yGal})
        if isinstance(xGal, int):
            xGal = Var({0: xGal})
        zGal = Var({k: v for k in xGal.data.keys() | yGal.data.keys() if (v := (xGal.data.get(k, 0x00) + yGal.data.get(k, 0x00)) % ρ)})
        return zGal.data.get(0, 0x00) if zGal.data.keys() <= {0} else zGal # convert zGal to a constant if the only non-zero term is the 0-th (constant) term
    def SUB(self, xGal, yGal):
        if isinstance(yGal, int):
            yGal = Var({0: yGal})
        if isinstance(xGal, int):
            xGal = Var({0: xGal})
        zGal = Var({k: v for k in xGal.data.keys() | yGal.data.keys() if (v := (xGal.data.get(k, 0x00) - yGal.data.get(k, 0x00)) % ρ)})
        return zGal.data.get(0, 0x00) if zGal.data.keys() <= {0} else zGal # convert zGal to a constant if the only non-zero term is the 0-th (constant) term
    def MUL(self, xGal, yGal, *, msg = 'multiplication error'):
        if xGal == 0x00 or yGal == 0x00:
            return 0x00
        if isinstance(xGal, int) and isinstance(yGal, int):
            return xGal * yGal % ρ
        if isinstance(yGal, int):
            return Var({i: m * yGal % ρ for i, m in xGal.data.items()})
        if isinstance(xGal, int):
            return Var({i: m * xGal % ρ for i, m in yGal.data.items()})
        zGal = self.MKWIRE(lambda getw, args: getw(xGal) * getw(yGal) % ρ)
        self.MKGATE(xGal, yGal, zGal, msg = msg)
        return zGal
    def DIV(self, xGal, yGal, *, msg = 'division error'):
        # Note that this division is not the usual division, it is the division in the finite field GF(P).
        if xGal == 0x00:
            return 0x00
        if yGal == 0x00:
            raise ZeroDivisionError
        if isinstance(xGal, int) and isinstance(yGal, int):
            return xGal * pow(yGal, -1, ρ) % ρ
        if isinstance(yGal, int):
            return Var({i: m * pow(yGal, -1, ρ) % ρ for i, m in xGal.data.items()})
        if isinstance(xGal, int):
            xGal = Var({0: xGal})
        zGal = self.MKWIRE(lambda getw, args: getw(xGal) * pow(getw(yGal), -1, ρ) % ρ)
        self.MKGATE(zGal, yGal, xGal, msg = msg)
        return zGal
    def POW(self, xGal, nBin):
        nBit, *nBin = nBin
        rGal = self.IF(nBit, xGal, 0x01)
        for nBit in nBin:
            xGal = self.MUL(xGal, xGal)
            kGal = self.IF(nBit, xGal, 0x01)
            rGal = self.MUL(rGal, kGal)
        return rGal
    def SUM(self, iLst, rGal = 0x00):
        for iGal in iLst:
            rGal = self.ADD(rGal, iGal)
        return rGal
    # type conversion operations on variables
    def BINARY(self, xGal, xLen, *, msg = 'binarization error'):
        # Convert x to a binary list with the given bit length, for example, BINARY(5, 3) will return [1, 0, 1]
        # and BINARY(5, 2) will raise an error because 5 is too large for 2 bits. Note that the bit length
        # should be less than the bit length of the prime number P, since otherwise the binary representation
        # of x will be non-unique.
        if not 0 <= xLen < ρ.bit_length():
            raise ValueError('invalid bit length')
        if isinstance(xGal, int):
            xBin = [xGal % ρ >> iLen & 0x01 for iLen in range(xLen)]
            assert sum(xBit * 0x02 ** iLen for iLen, xBit in enumerate(xBin)) == xGal, msg
            return xBin
        bind = lambda iLen: self.MKWIRE(lambda getw, args: getw(xGal) >> iLen & 0x01)
        xBin = [0x00 for _ in range(xLen)]
        for iLen in range(xLen):
            xBit = xBin[iLen] = bind(iLen)
            self.ASSERT_ISBOOL(xBit)
        tGal = self.SUM(self.MUL(xBit, 0x02 ** iLen) for iLen, xBit in enumerate(xBin))
        self.ASSERT_EQ(xGal, tGal, msg = msg)
        return xBin
    def GALOIS(self, xBin):
        # Convert a binary list to an galios field element, for example, GALOIS([1, 0, 1]) will return 5.
        return self.SUM(self.MUL(bBit, 0x02 ** iLen) for iLen, bBit in enumerate(xBin))
    def ENUM(self, xGal, kSet, *, msg = 'enumerization error'):
        # Convert x to an enum value, for example, ENUM(3, {1, 3, 5, 7}) will return {1: 0, 3: 1, 5: 0, 7: 0}
        # and ENUM(2, {1, 3, 5, 7}) will raise an error because 2 is not in the enum set.
        if isinstance(xGal, int):
            xKey = {kInt: 0x01 - pow(xGal - kInt, ρ - 1, ρ) for kInt in kSet}
            assert sum(xBit * kInt for kInt, xBit in xKey.items()) == xGal, msg
            return xKey
        xFrz = tuple(sorted(xGal.data.items()))
        if (xKey := self.enums.get(kSet, {}).get(xFrz)) is not None:
            return xKey
        bind = lambda kInt: self.MKWIRE(lambda getw, args: 0x01 - pow(getw(xGal) - kInt, ρ - 1, ρ))
        xKey = {kInt: 0x00 for kInt in kSet}
        for kInt in kSet:
            xBit = xKey[kInt] = bind(kInt)
            self.ASSERT_ISBOOL(xBit)
        tGal = self.SUM(self.MUL(xBit, kInt) for kInt, xBit in xKey.items())
        eGal = self.SUM(self.MUL(xBit, 0x01) for kInt, xBit in xKey.items())
        self.ASSERT_EQ(xGal, tGal, msg = msg)
        self.ASSERT_EQ(0x01, eGal, msg = msg)
        self.enums.setdefault(kSet, {})[xFrz] = xKey # optimize by memoization
        return xKey
    # conditional expression and get/set operations on lists and dictionaries
    def IF(self, bBit, tItm, fItm):
        # Conditional expression, b is a boolean value, t and f are the true and false branches (can be scalars,
        # (multi-dimensional) lists, dictionaries, or tuples, but should have the same shape).
        # optimize when b is a constant
        if bBit == 0x01:
            return tItm
        if bBit == 0x00:
            return fItm
        if isinstance(tItm, dict):
            return dict((zInt, self.IF(bBit, tItm[zInt], fItm[zInt])) for zInt in tItm.keys())
        if isinstance(tItm, list):
            return list(self.IF(bBit, tItm[zInt], fItm[zInt]) for zInt in range(len(tItm)))
        if isinstance(tItm, tuple):
            return tuple(self.IF(bBit, tItm[zInt], fItm[zInt]) for zInt in range(len(tItm)))
        # return self.ADD(self.MUL(bBit, tItm), self.MUL(self.NOT(bBit), fItm)) # generate more constraints but faster to compile
        return self.ADD(self.MUL(bBit, self.SUB(tItm, fItm)), fItm)
    def GETBYBIN(self, lSpc, iBin, cBit = 0x01, *, msg = 'binary index out of range'):
        # Get the value of a (multi-dimensional) list by the given binary index.
        # For example, GETBYBIN([[1, 2], [3, 4], [5, 6]], [1, 0]) will return [5, 6]. The binary index can be any
        # length, however, the value it represents should be less than the length of the list.
        iLen = 2 ** len(iBin)
        if len(lSpc) >= iLen:
            lSpc = lSpc[:iLen]
            for iBit in iBin:
                lSpc = self.IF(iBit, lSpc[1::2], lSpc[0::2])
            return lSpc[0]
        *iBin, iBit = iBin
        iLen = 2 ** len(iBin)
        if len(lSpc) <= iLen:
            self.MKGATE(cBit, iBit, 0x00, msg = msg)
            return self.GETBYBIN(lSpc, iBin, cBit)
        return self.IF(iBit, self.GETBYBIN(lSpc[iLen:], iBin, self.AND(cBit, iBit)), self.GETBYBIN(lSpc[:iLen], iBin, self.AND(cBit, self.NOT(iBit))))
    def GETBYKEY(self, lSpc, iKey):
        # Get the value of a (multi-dimensional) list or dictionary by the given key, key should be an enum value.
        # For example, GETBYKEY({2: [1, 2], 3: [3, 4]}, {2: 1, 3: 0}) will return [1, 2].
        iItr = iter(iKey.items())
        kInt, iBit = next(iItr)
        vItm = lSpc[kInt]
        for kInt, iBit in iItr:
            vItm = self.IF(iBit, lSpc[kInt], vItm)
        return vItm
    def SETBYKEY(self, vItm, lSpc, *iKes, cBit = 0x01):
        # Set the value of a (multi-dimensional) list or dictionary by the given keys, it will return a new
        # (multi-dimensional) list or dictionary with the value set.
        # For example, SETBYKEY(5, {2: [1, 2], 3: [3, 4]}, {2: 1, 3: 0}, {0: 0, 1: 1}) means to set the value
        # of {2: [1, 2], 3: [3, 4]}[2][1] to 5, so the result will be {2: [1, 5], 3: [3, 4]}.
        if len(iKes) == 0:
            return self.IF(cBit, vItm, lSpc)
        iKey, *iKes = iKes
        if isinstance(lSpc, list):
            return [self.SETBYKEY(vItm, lSpc[kInt], *iKes, cBit = self.AND(cBit, iBit)) for kInt, iBit in iKey.items()]
        if isinstance(lSpc, dict):
            return {kInt: self.SETBYKEY(vItm, lSpc[kInt], *iKes, cBit = self.AND(cBit, iBit)) for kInt, iBit in iKey.items()}
    # logical operations on boolean values
    def NOT(self, xBit):
        return self.SUB(0x01, xBit)
    def AND(self, xBit, yBit):
        return self.MUL(xBit, yBit)
    def OR(self, xBit, yBit):
        return self.SUB(0x01, self.MUL(self.SUB(0x01, xBit), self.SUB(0x01, yBit)))
    def XOR(self, xBit, yBit):
        return self.DIV(self.SUB(0x01, self.MUL(self.SUB(0x01, self.MUL(xBit, 0x02)), self.SUB(0x01, self.MUL(yBit, 0x02)))), 0x02)
    # compare operations on galios field elements
    def NEZ(self, xGal, *, msg = 'booleanization error'):
        # Convert x to a boolean value, return 1 if x is non-zero and 0 if x is zero.
        if isinstance(xGal, int):
            return pow(xGal, ρ - 1, ρ)
        iGal = self.MKWIRE(lambda getw, args: pow(getw(xGal), ρ - 2, ρ))
        rBit = self.MKWIRE(lambda getw, args: pow(getw(xGal), ρ - 1, ρ))
        self.MKGATE(rBit, xGal, xGal, msg = msg) # the following constraint ensures that o has to be 1 if x is non-zero
        self.MKGATE(xGal, iGal, rBit, msg = msg) # the following constraint ensures that o has to be 0 if x is zero
        return rBit
    def GE(self, xGal, yGal, bLen, msg = 'GE compare failed'): # 0x00 <= xGal - yGal < 0x02 ** bLen
        return self.BINARY(self.ADD(0x02 ** bLen, self.SUB(xGal, yGal)), bLen + 1, msg = msg)[bLen]
    def LE(self, xGal, yGal, bLen, msg = 'LE compare failed'): # 0x00 <= yGal - xGal < 0x02 ** bLen
        return self.BINARY(self.ADD(0x02 ** bLen, self.SUB(yGal, xGal)), bLen + 1, msg = msg)[bLen]
    def GT(self, xGal, yGal, bLen, msg = 'GT compare failed'): # 0x00 < xGal - yGal <= 0x02 ** bLen
        return self.BINARY(self.ADD(0x02 ** bLen, self.SUB(self.SUB(xGal, yGal), 0x01)), bLen + 1, msg = msg)[bLen]
    def LT(self, xGal, yGal, bLen, msg = 'LT compare failed'): # 0x00 < yGal - xGal <= 0x02 ** bLen
        return self.BINARY(self.ADD(0x02 ** bLen, self.SUB(self.SUB(yGal, xGal), 0x01)), bLen + 1, msg = msg)[bLen]
    # assertion operations on galios field elements
    def ASSERT_GE(self, xGal, yGal, bLen, *, msg = 'GE assertion failed'): # assert 0x00 <= xGal - yGal < 0x02 ** bLen
        return self.BINARY(self.SUB(xGal, yGal), bLen, msg = msg)
    def ASSERT_LE(self, xGal, yGal, bLen, *, msg = 'LE assertion failed'): # assert 0x00 <= yGal - xGal < 0x02 ** bLen
        return self.BINARY(self.SUB(yGal, xGal), bLen, msg = msg)
    def ASSERT_GT(self, xGal, yGal, bLen, *, msg = 'GT assertion failed'): # assert 0x00 < xGal - yGal <= 0x02 ** bLen
        return self.BINARY(self.SUB(self.SUB(xGal, yGal), 0x01), bLen, msg = msg)
    def ASSERT_LT(self, xGal, yGal, bLen, *, msg = 'LT assertion failed'): # assert 0x00 < yGal - xGal <= 0x02 ** bLen
        return self.BINARY(self.SUB(self.SUB(yGal, xGal), 0x01), bLen, msg = msg)
    def ASSERT_EQ(self, xGal, yGal, *, msg = 'EQ assertion failed'):
        self.MKGATE(0x01, xGal, yGal, msg = msg)
    def ASSERT_NE(self, xGal, yGal, *, msg = 'NE assertion failed'):
        self.DIV(0x01, self.SUB(xGal, yGal), msg = msg)
    def ASSERT_ISBOOL(self, xGal, *, msg = 'ISBOOL assertion failed'):
        self.MKGATE(xGal, xGal, xGal, msg = msg)
    # bitwise operations on binary lists
    def ROTL(self, xBin, rLen):
        rLen = -rLen % len(xBin)
        return xBin[rLen:] + xBin[:rLen]
    def ROTR(self, xBin, rLen):
        rLen = +rLen % len(xBin)
        return xBin[rLen:] + xBin[:rLen]
    def BITNOT(self, xBin):
        return [self.NOT(xBit) for xBit in xBin]
    def BITAND(self, xBin, yBin):
        # assert len(xBin) == len(yBin)
        return [self.AND(xBit, yBit) for xBit, yBit in zip(xBin, yBin)]
    def BITOR(self, xBin, yBin):
        # assert len(xBin) == len(yBin)
        return [self.OR(xBit, yBit) for xBit, yBit in zip(xBin, yBin)]
    def BITXOR(self, xBin, yBin):
        # assert len(xBin) == len(yBin)
        return [self.XOR(xBit, yBit) for xBit, yBit in zip(xBin, yBin)]
    # arithmetic operations on binary lists
    def BINADD(self, xBin, yBin, cBit = 0x00):
        # assert len(xBin) == len(yBin)
        bLen = max(len(xBin), len(yBin))
        zBin = self.BINARY(self.ADD(self.GALOIS(xBin), self.ADD(self.GALOIS(self.ADD(0x00, bBit) for bBit in yBin), self.ADD(0x00, cBit))), bLen + 1)
        return zBin[:bLen], self.ADD(0x00, zBin[bLen])
    def BINSUB(self, xBin, yBin, cBit = 0x00):
        # assert len(xBin) == len(yBin)
        bLen = max(len(xBin), len(yBin))
        zBin = self.BINARY(self.ADD(self.GALOIS(xBin), self.ADD(self.GALOIS(self.SUB(0x01, bBit) for bBit in yBin), self.SUB(0x01, cBit))), bLen + 1)
        return zBin[:bLen], self.SUB(0x01, zBin[bLen])
    def BINMUL(self, xBin, yBin, cBin = [], dBin = []):
        # assert len(xBin) == len(yBin)
        bLen = max(len(xBin), len(yBin))
        assert len(cBin) <= bLen
        assert len(dBin) <= bLen
        zBin = self.BINARY(self.ADD(self.MUL(self.GALOIS(xBin), self.GALOIS(yBin)), self.ADD(self.GALOIS(cBin), self.GALOIS(dBin))), bLen * 2)
        return zBin[:bLen], zBin[bLen:]
    def BINDIVMOD(self, xBin, yBin, *, msg = 'binary divmod error'):
        # Division and modulo operations on binary lists.
        qLen = len(xBin)
        rLen = len(yBin)
        xGal = self.GALOIS(xBin)
        yGal = self.GALOIS(yBin)
        if xGal == 0x00:
            return [0x00] * qLen, [0x00] * rLen
        if yGal == 0x00:
            raise ZeroDivisionError
        if isinstance(xGal, int) and isinstance(yGal, int):
            qGal, rGal = divmod(xGal, yGal)
            return [qGal >> iLen & 0x01 for iLen in range(qLen)], [rGal >> iLen & 0x01 for iLen in range(rLen)]
        if isinstance(xGal, int):
            xGal = Var({0: xGal})
        if isinstance(yGal, int):
            yGal = Var({0: yGal})
        qGal = self.MKWIRE(lambda getw, args: getw(xGal) // getw(yGal))
        rGal = self.MKWIRE(lambda getw, args: getw(xGal) % getw(yGal))
        self.MKGATE(qGal, yGal, self.SUB(xGal, rGal), msg = msg) # assert y * q == x - r
        qBin = self.ASSERT_GE(qGal, 0x00, qLen, msg = msg)
        rBin = self.ASSERT_GE(rGal, 0x00, rLen, msg = msg)
        _Bin = self.ASSERT_LT(rGal, yGal, rLen, msg = msg)
        return qBin, rBin
    def BINPOW(self, xBin, nBin):
        bLen = len(xBin)
        nBit, *nBin = nBin
        rBin = self.IF(nBit, xBin, self.BINARY(0x01, bLen))
        for nBit in nBin:
            xBin = self.BINMUL(xBin, xBin)[0]
            kBin = self.IF(nBit, xBin, self.BINARY(0x01, bLen))
            rBin = self.BINMUL(rBin, kBin)[0]
        return rBin
    def BINSUM(self, List, cGal = 0x00): # c < len(List)
        # BINSUM generates less constraints than BINADD when their are lots of binary numbers to add.
        # assert len(set(map(len, List))) == 1
        bLen = max(map(len, List))
        return self.BINARY(self.SUM(map(self.GALOIS, List), cGal), bLen + (len(List) - 1).bit_length())[:bLen]
    # compare operations on binary lists
    def BINGE(self, xBin, yBin):
        # assert len(xBin) == len(yBin)
        bLen = max(len(xBin), len(yBin))
        return self.BINARY(self.ADD(0x02 ** bLen, self.SUB(self.GALOIS(xBin), self.GALOIS(yBin))), bLen + 1)[bLen]
    def BINLE(self, xBin, yBin):
        # assert len(xBin) == len(yBin)
        bLen = max(len(xBin), len(yBin))
        return self.BINARY(self.ADD(0x02 ** bLen, self.SUB(self.GALOIS(yBin), self.GALOIS(xBin))), bLen + 1)[bLen]
    def BINGT(self, xBin, yBin):
        # assert len(xBin) == len(yBin)
        bLen = max(len(xBin), len(yBin))
        return self.BINARY(self.ADD(0x02 ** bLen, self.SUB(self.SUB(self.GALOIS(xBin), self.GALOIS(yBin)), 0x01)), bLen + 1)[bLen]
    def BINLT(self, xBin, yBin):
        # assert len(xBin) == len(yBin)
        bLen = max(len(xBin), len(yBin))
        return self.BINARY(self.ADD(0x02 ** bLen, self.SUB(self.SUB(self.GALOIS(yBin), self.GALOIS(xBin)), 0x01)), bLen + 1)[bLen]
    # assertion operations on binary lists
    def ASSERT_BINGE(self, xBin, yBin, *, msg = 'BINGE assertion failed'):
        # assert len(xBin) == len(yBin)
        bLen = max(len(xBin), len(yBin))
        self.BINARY(self.SUB(self.GALOIS(xBin), self.GALOIS(yBin)), bLen, msg = msg)
    def ASSERT_BINLE(self, xBin, yBin, *, msg = 'BINLE assertion failed'):
        # assert len(xBin) == len(yBin)
        bLen = max(len(xBin), len(yBin))
        self.BINARY(self.SUB(self.GALOIS(yBin), self.GALOIS(xBin)), bLen, msg = msg)
    def ASSERT_BINGT(self, xBin, yBin, *, msg = 'BINGT assertion failed'):
        # assert len(xBin) == len(yBin)
        bLen = max(len(xBin), len(yBin))
        self.BINARY(self.SUB(self.SUB(self.GALOIS(xBin), self.GALOIS(yBin)), 0x01), bLen, msg = msg)
    def ASSERT_BINLT(self, xBin, yBin, *, msg = 'BINLT assertion failed'):
        # assert len(xBin) == len(yBin)
        bLen = max(len(xBin), len(yBin))
        self.BINARY(self.SUB(self.SUB(self.GALOIS(yBin), self.GALOIS(xBin)), 0x01), bLen, msg = msg)
    def PARAM(self, name, public = False):
        # Add an input parameter to the circuit, the value of the parameter can be set when calling the prove method.
        return self.MKWIRE(lambda getw, args: args[name], name if public else None)
    def REVEAL(self, name, xGal, *, msg = 'reveal error'):
        # Make a variable public.
        if isinstance(xGal, int):
            xGal = Var({0: xGal})
        rGal = self.MKWIRE(lambda getw, args: getw(xGal), name)
        self.ASSERT_EQ(xGal, rGal, msg = msg)
        return rGal
# check the type of a value
def isgal(x):
    return isinstance(x, (int, Var))
def isbin(x):
    return isinstance(x, list) and all(isinstance(b, (int, Var)) for b in x)
# assert the type of a value
def asint(x):
    if isinstance(x, int):
        return (x + (ρ - 1) // 2) % ρ - (ρ - 1) // 2
    raise TypeError('expected a constant value')
def asgal(x):
    if isinstance(x, (int, Var)):
        return x
    raise TypeError('expected a value')
def asbin(x):
    if isinstance(x, list) and all(isinstance(b, (int, Var)) for b in x):
        return x
    raise TypeError('expected a binary')
def asstr(x):
    if isinstance(x, str):
        return x
    raise TypeError('expected a string')
# get the shape of a value (binary list will be treated as a list of integers)
def shape(x):
    if isinstance(x, (int, Var)):
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
    # The Compiler class is a wrapper of the Assembly class, it compiles the given Python code to the arithmetic
    # circuits. The Python code should be written in a restricted subset of Python.
    def __init__(self):
        ast.NodeVisitor.__init__(self)
        Assembly.__init__(self)
        self.stack = [{
            'range': lambda *args: range(*map(asint, args)),
            'gal': lambda x: self.GALOIS(x) if isbin(x) else asgal(x),
            'b8':  lambda x: (x + [0x00] *  8)[: 8] if isbin(x) else self.BINARY(asgal(x),  8),
            'b16': lambda x: (x + [0x00] * 16)[:16] if isbin(x) else self.BINARY(asgal(x), 16),
            'b32': lambda x: (x + [0x00] * 32)[:32] if isbin(x) else self.BINARY(asgal(x), 32),
            'b64': lambda x: (x + [0x00] * 64)[:64] if isbin(x) else self.BINARY(asgal(x), 64),
            'bin': lambda x, n: (x + [0x00] * asint(n))[:n] if isbin(x) else self.BINARY(asgal(x), asint(n)),
            'fmt': lambda s, *args: asstr(s).format(*map(asint, args)),
            'log': lambda s: print(asstr(s)),
            'private': lambda s: self.PARAM(asstr(s)),
            'public': lambda s: self.PARAM(asstr(s), public = True),
            'reveal': lambda s, x: self.REVEAL(asstr(s), self.GALOIS(x) if isbin(x) else asgal(x)),
        }] # the stack is used to store the local variables
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
            self.ASSERT_NE(0x00, asgal(test))
        else:
            self.ASSERT_NE(0x00, asgal(test), msg = asstr(self.visit(node.msg)))
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
                enums.append(self.ENUM(self.GALOIS(slice) if isbin(slice) else asgal(slice), keys))
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
        if isinstance(value, list): # optimize for list
            return self.GETBYBIN(value, slice if isbin(slice) else self.BINARY(asgal(slice), (len(value) - 1).bit_length()))
        keys, *outer = outer
        return self.GETBYKEY(value, self.ENUM(self.GALOIS(slice) if isbin(slice) else asgal(slice), keys))
    def visit_Call(self, node):
        return self.visit(node.func)(*map(self.visit, node.args))
    def visit_Set(self, node):
        # this syntax is used for summing binary values
        # use * to represent negation (except for the first element)
        # e.g. {a, *b, c, *d, e} represents a - b + c - d + e
        elt, *elts = node.elts
        negs = 0x00
        args = [asbin(self.visit(elt))]
        for elt in elts:
            if isinstance(elt, ast.Starred):
                negs += 0x01
                args.append(self.BITNOT(asbin(self.visit(elt.value))))
            else:
                args.append(asbin(self.visit(elt)))
        return self.BINSUM(args, cGal = negs)
    def visit_Constant(self, node):
        if isinstance(node.value, int):
            return node.value % ρ
        if isinstance(node.value, str):
            return node.value
        raise SyntaxError('invalid constant')
    def visit_BinOp(self, node):
        left = self.visit(node.left)
        right = self.visit(node.right)
        if isinstance(node.op, ast.Add):
            return self.BINADD(left, right)[0] if isbin(left) and isbin(right) else self.ADD(asgal(left), asgal(right))
        if isinstance(node.op, ast.Sub):
            return self.BINSUB(left, right)[0] if isbin(left) and isbin(right) else self.SUB(asgal(left), asgal(right))
        if isinstance(node.op, ast.Mult):
            return self.BINMUL(left, right)[0] if isbin(left) and isbin(right) else self.MUL(asgal(left), asgal(right))
        if isinstance(node.op, ast.Div):
            return self.DIV(asgal(left), asgal(right))
        if isinstance(node.op, ast.Pow):
            return self.POW(left, asbin(right)) if isbin(left) else self.BINPOW(asgal(left), asbin(right))
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
            return self.NOT(asgal(operand))
        if isinstance(node.op, ast.UAdd):
            return self.ADD(0x00, asgal(operand))
        if isinstance(node.op, ast.USub):
            return self.SUB(0x00, asgal(operand))
        raise SyntaxError('unsupported unary operation')
    def visit_BoolOp(self, node):
        if isinstance(node.op, ast.And):
            result = 0x01
            for value in node.values:
                result = self.AND(result, asgal(self.visit(value)))
            return result
        if isinstance(node.op, ast.Or):
            result = 0x00
            for value in node.values:
                result = self.OR(result, asgal(self.visit(value)))
            return result
        raise SyntaxError('unsupported boolean operation')
    def visit_Compare(self, node):
        result = 0x01
        left = self.visit(node.left)
        for op, right in zip(node.ops, map(self.visit, node.comparators)):
            if isinstance(op, ast.Eq):
                result = self.AND(result, self.NOT(self.NEZ(self.SUB(self.GALOIS(left) if isbin(left) else asgal(left), self.GALOIS(right) if isbin(right) else asgal(right)))))
            elif isinstance(op, ast.NotEq):
                result = self.AND(result, self.NEZ(self.SUB(self.GALOIS(left) if isbin(left) else asgal(left), self.GALOIS(right) if isbin(right) else asgal(right))))
            elif isinstance(op, ast.Lt):
                result = self.AND(result, self.BINLT(left, right) if isbin(left) and isbin(right) else asint(left) < asint(right))
            elif isinstance(op, ast.LtE):
                result = self.AND(result, self.BINLE(left, right) if isbin(left) and isbin(right) else asint(left) <= asint(right))
            elif isinstance(op, ast.Gt):
                result = self.AND(result, self.BINGT(left, right) if isbin(left) and isbin(right) else asint(left) > asint(right))
            elif isinstance(op, ast.GtE):
                result = self.AND(result, self.BINGE(left, right) if isbin(left) and isbin(right) else asint(left) >= asint(right))
            else:
                raise SyntaxError('unsupported comparison')
            left = right
        return result
    def visit_IfExp(self, node):
        left = self.visit(node.body)
        right = self.visit(node.orelse)
        if shape(left) != shape(right):
            raise TypeError('inconsistent shape of left and right values in conditional expression')
        return self.IF(asgal(self.visit(node.test)), left, right)
    def generic_visit(self, node):
        raise SyntaxError('unsupported syntax')
    def visit_Index(self, node):
        # deprecated since Python 3.9
        return self.visit(node.value)
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
        asm = Compiler()
        asm.visit(ast.parse(
            "P0 = lambda x: x ^ x << 9 ^ x << 17\n"
            "P1 = lambda x: x ^ x << 15 ^ x << 23\n"
            "F0 = lambda x, y, z: x ^ y ^ z\n"
            "F1 = lambda x, y, z: x & y | z & (x | y)\n"
            "G0 = lambda x, y, z: x ^ y ^ z\n"
            "G1 = lambda x, y, z: x & y | z & ~x\n"
            "T0 = b32(0x79cc4519)\n"
            "T1 = b32(0x7a879d8a)\n"
            "def compress(V, I):\n"
            "    W = [b32(0) for _ in range(68)]\n"
            "    for j in range(0, 16):\n"
            "        W[j] = I[j]\n"
            "    for j in range(16, 68):\n"
            "        W[j] = P1(W[j - 16] ^ W[j - 9] ^ W[j - 3] << 15) ^ W[j - 13] << 7 ^ W[j - 6]\n"
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
            "            SS1 = {A << 12, E, T0 << j} << 7\n"
            "            SS2 = SS1 ^ A << 12\n"
            "            TT1 = {F0(A, B, C), D, SS2, W[j] ^ W[j + 4]}\n"
            "            TT2 = {G0(E, F, G), H, SS1, W[j]}\n"
            "        else:\n"
            "            SS1 = {A << 12, E, T1 << j} << 7\n"
            "            SS2 = SS1 ^ A << 12\n"
            "            TT1 = {F1(A, B, C), D, SS2, W[j] ^ W[j + 4]}\n"
            "            TT2 = {G1(E, F, G), H, SS1, W[j]}\n"
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
            "W = [b32(private(fmt('W[{:#04x}]', i))) for i in range(16)]\n"
            "V = compress(V, W)\n"
            "for i in range(8):\n"
            "    reveal(fmt('V[{:#04x}]', i), V[i])\n"
        ))
    print('Number of gates:', asm.gate_count())
    print('Number of wires:', asm.wire_count())
    with Timer('Setting up QAP...'):
        α = random.randrange(1, ρ)
        β = random.randrange(1, ρ)
        γ = random.randrange(1, ρ)
        δ = random.randrange(1, ρ)
        x = random.randrange(1, ρ)
        α1, β1, δ1, β2, γ2, δ2, u1U, v1V, x1I, x2I, y1I = asm.setup(α, β, γ, δ, x)
    with Timer('Generating proof...'):
        args = {'W[{:#04x}]'.format(i): v for i, v in enumerate([0x61626380] + [0x00000000] * 14 + [0x00000018])}
        r = random.randrange(1, ρ)
        s = random.randrange(1, ρ)
        A1, B2, C1, uU = asm.prove(α1, β1, δ1, β2, δ2, v1V, x1I, x2I, y1I, args, r, s)
    with Timer('Verifying...'):
        passed = asm.verify(α1, β2, γ2, δ2, u1U, A1, B2, C1, uU)
    if passed:
        print('Verification passed!')
        print('Public witness:', '{{{}}}'.format(', '.join('{} = {:#010x}'.format(k, u) for k, u in zip(asm.stmts.values(), uU))))
    else:
        print('Verification failed!')
