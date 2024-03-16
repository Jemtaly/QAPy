#!/usr/bin/python3
import time
import fft
import waksman
import ast
import random
import pymcl
import multiprocessing
# the BLS12-381 curve parameters
g1 = pymcl.g1
g2 = pymcl.g2
ρ = pymcl.r
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
    # their coefficients, for example, x = w₀ + 5w₂ + 7w₃ can be represented as {0: 1, 2: 5, 3: 7}, note
    # that the variables with coefficient 0 are always omitted.
    # Besides, constants are always represented by the integer itself.
    def __init__(self, data):
        self.data = data
class Circuit:
    # The Circuit class is used to construct the arithmetic circuits, it provides a set of methods to
    # create and manipulate the variables, and to perform arithmetic operations on them. The arithmetic
    # operations are represented as the constraints in the circuit. Besides, this class also implements
    # the setup, prove, and verify methods of the Groth16 zk-SNARK.
    def __init__(self):
        self.gates = [] # the constraints in the circuit, see the MKGATE method for details
        self.wires = [lambda getw, args: 1] # functions to generate the variables in the witness vector, the 0-th variable is always 1
        self.stmts = {0: '1'} # the public variables, keys are their indices in the witness vector, and values are their names
        self.enums = {} # memoization of the enum values
    def gate_count(self):
        return len(self.gates)
    def wire_count(self):
        return len(self.wires)
    # Groth16 zk-SNARK setup, prove, and verify methods
    def setup(self, α, β, γ, δ, τ):
        M = self.wire_count()
        N = self.gate_count()
        I = 1 << (N - 1).bit_length() # the smallest power of 2 that is not less than N
        p = fft.pru(I, ρ) # the primitive I-th root of unity in GF(P)
        # What we need is to calculate Aₘ(τ), Bₘ(τ), Cₘ(τ) for m in [0, M), where Aₘ, Bₘ and Cₘ are the
        # polynomials transformed from the m-th column of the three constraint matrices respectively.
        # The naivest way is to calculate the polynomials using Lagrange interpolation, which requires
        # O(I²M) time complexity for all the M columns. iFFT can reduce this to O(IMlogI), but this is
        # still too slow for large I and M. However, it's worth noting that the vast majority of values
        # in the constraint matrices are 0, and the number of non-zero values in the matrices is only
        # O(M). So we can make use of a property of DFT:
        #     Σᵢ₌₀ᴵ⁻¹ Xᵢyᵢ = Σᵢ₌₀ᴵ⁻¹ xᵢYᵢ
        # where xᵢ and Xᵢ, yᵢ and Yᵢ are two DFT pairs. So the three values required can be converted to
        #     Aₘ(τ) = Σᵢ₌₀ᴵ⁻¹ Xᵢaᵢₘ
        #     Bₘ(τ) = Σᵢ₌₀ᴵ⁻¹ Xᵢbᵢₘ
        #     Cₘ(τ) = Σᵢ₌₀ᴵ⁻¹ Xᵢcᵢₘ
        # where aᵢₘ, bᵢₘ, cᵢₘ are the elements in row i and column m of the three constraint matrices,
        # and X is the inverse DFTed form of the vector [τ⁰, τ¹, ..., τⁱ⁻¹]. All of these can be done in
        # O(IlogI) time.
        xI = list(fft.pows(τ, I, ρ))
        XI = fft.ifft(xI, p, ρ)
        AτM = [0x00 for _ in range(M)]
        BτM = [0x00 for _ in range(M)]
        CτM = [0x00 for _ in range(M)]
        for X, (aM, bM, cM, msg) in zip(XI, self.gates):
            for m, a in aM.data.items():
                AτM[m] += X * a
            for m, b in bM.data.items():
                BτM[m] += X * b
            for m, c in cM.data.items():
                CτM[m] += X * c
        Zτ = pow(τ, I, ρ) - 0x01 # Z(τ), where Z(X) = Πᵢ₌₀ᴵ⁻¹ (X - pⁱ)
        Γ = pow(γ, -1, ρ)
        Δ = pow(δ, -1, ρ)
        α1 = g1 * pymcl.Fr(str(α))
        β1 = g1 * pymcl.Fr(str(β))
        δ1 = g1 * pymcl.Fr(str(δ))
        β2 = g2 * pymcl.Fr(str(β))
        γ2 = g2 * pymcl.Fr(str(γ))
        δ2 = g2 * pymcl.Fr(str(δ))
        u1U = scalar_mult_parallel(g1, ((β * AτM[m] + α * BτM[m] + CτM[m]) * Γ % ρ for m in                      self.stmts))
        v1V = scalar_mult_parallel(g1, ((β * AτM[m] + α * BτM[m] + CτM[m]) * Δ % ρ for m in range(M) if m not in self.stmts))
        x1I = scalar_mult_parallel(g1, fft.pows(τ, I, ρ))
        x2I = scalar_mult_parallel(g2, fft.pows(τ, I, ρ))
        y1I = scalar_mult_parallel(g1, (x * Δ * Zτ % ρ for x in fft.pows(τ, I - 1, ρ)))
        return α1, β1, δ1, β2, γ2, δ2, u1U, v1V, x1I, x2I, y1I
    def prove(self, α1, β1, δ1, β2, δ2, v1V, x1I, x2I, y1I, args, r, s):
        M = self.wire_count()
        N = self.gate_count()
        I = 1 << (N - 1).bit_length()
        J = 1 << (N - 1).bit_length() + 1
        p = fft.pru(I, ρ)
        q = fft.pru(J, ρ)
        wM = []
        getw = lambda tM: sum(wM[m] * t for m, t in tM.data.items()) % ρ # <w, t> = Σₘ₌₀ᴹ⁻¹ wₘtₘ
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
        # Here we already have
        #     A(pⁱ) = Σₘ₌₀ᴹ⁻¹ wₘAₘ(pⁱ) = Σₘ₌₀ᴹ⁻¹ wₘaᵢₘ
        #     B(pⁱ) = Σₘ₌₀ᴹ⁻¹ wₘBₘ(pⁱ) = Σₘ₌₀ᴹ⁻¹ wₘbᵢₘ
        #     C(pⁱ) = Σₘ₌₀ᴹ⁻¹ wₘCₘ(pⁱ) = Σₘ₌₀ᴹ⁻¹ wₘcᵢₘ
        # for i in [0, I), thus we can simply obtain A(X), B(X), C(X) using iFFT. However, since Z(pⁱ)
        # always equals 0, it is not possible to calculate H(X) = (A(X) * B(X) - C(X)) / Z(X) in this
        # domain. Instead, we use coset FFT to calculate A(pⁱq), B(pⁱq), C(pⁱq) first, then calculate
        # corresponding H(pⁱq) (note that Z(pⁱq) = -2), and finally recover H(X) using the coset iFFT.
        AwI = fft.ifft(awN + [0x00] * (I - N), p, ρ)
        BwI = fft.ifft(bwN + [0x00] * (I - N), p, ρ)
        CwI = fft.ifft(cwN + [0x00] * (I - N), p, ρ)
        awI = fft.fft([Aw * k % ρ for k, Aw in zip(fft.pows(q, I, ρ), AwI)], p, ρ) # Coset FFT
        bwI = fft.fft([Bw * k % ρ for k, Bw in zip(fft.pows(q, I, ρ), BwI)], p, ρ) # Coset FFT
        cwI = fft.fft([Cw * k % ρ for k, Cw in zip(fft.pows(q, I, ρ), CwI)], p, ρ) # Coset FFT
        hI = [(ρ - 1) // 2 * (aw * bw - cw) % ρ for aw, bw, cw in zip(awI, bwI, cwI)] # (A * B - C) / Z on coset
        HI = [H * k % ρ for k, H in zip(fft.pows(pow(q, -1, ρ), I, ρ), fft.ifft(hI, p, ρ))] # Coset iFFT
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
        # For example, x = MKWIRE(lambda getw, args: getw(y) * getw(z) % ρ) will add a new variable x
        # that is defined by the product of the values of y and z in the witness vector, and then return
        # this variable. If name is specified, the variable is public.
        i = len(self.wires)
        self.wires.append(func)
        # if name is specified, the variable is public
        if name is not None:
            self.stmts[i] = name
        return Var({i: 0x01})
    def MKGATE(self, xGal, yGal, zGal, *, msg = 'assertion error'):
        # Add a constraint to the circuit, the constraint is represented as (x, y, z, msg), which means
        # x * y = z, msg is the error message when the constraint is not satisfied.
        if isinstance(zGal, int):
            if isinstance(xGal, int) and isinstance(yGal, int):
                assert xGal * yGal % ρ == zGal, msg
                return
            if xGal == 0x00 or yGal == 0x00:
                assert zGal == 0x00, msg
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
        xGal = Var({0: xGal}) if isinstance(xGal, int) else Var(xGal.data.copy())
        if isinstance(yGal, int):
            xGal.data[0] = (xGal.data.get(0, 0x00) + yGal) % ρ
        else:
            for k, v in yGal.data.items():
                xGal.data[k] = (xGal.data.get(k, 0x00) + v) % ρ
        return xGal.data.get(0, 0x00) if xGal.data.keys() <= {0} else xGal
    def SUB(self, xGal, yGal):
        xGal = Var({0: xGal}) if isinstance(xGal, int) else Var(xGal.data.copy())
        if isinstance(yGal, int):
            xGal.data[0] = (xGal.data.get(0, 0x00) - yGal) % ρ
        else:
            for k, v in yGal.data.items():
                xGal.data[k] = (xGal.data.get(k, 0x00) - v) % ρ
        return xGal.data.get(0, 0x00) if xGal.data.keys() <= {0} else xGal
    def MUL(self, xGal, yGal, *, msg = 'multiplication error'):
        if isinstance(xGal, int) and isinstance(yGal, int):
            return xGal * yGal % ρ
        if xGal == 0x00 or yGal == 0x00:
            return 0x00
        if isinstance(yGal, int):
            return Var({k: v * yGal % ρ for k, v in xGal.data.items()})
        if isinstance(xGal, int):
            return Var({k: v * xGal % ρ for k, v in yGal.data.items()})
        zGal = self.MKWIRE(lambda getw, args: getw(xGal) * getw(yGal) % ρ)
        self.MKGATE(xGal, yGal, zGal, msg = msg)
        return zGal
    def DIV(self, xGal, yGal, *, msg = 'division error'):
        # Division in the finite field GF(P).
        if isinstance(xGal, int) and isinstance(yGal, int):
            return xGal * pow(yGal, -1, ρ) % ρ
        if xGal == 0x00:
            return 0x00
        if isinstance(yGal, int):
            return Var({k: v * pow(yGal, -1, ρ) % ρ for k, v in xGal.data.items()})
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
        rGal = Var({0: rGal}) if isinstance(rGal, int) else Var(rGal.data.copy())
        for iGal in iLst:
            if isinstance(iGal, int):
                rGal.data[0] = (rGal.data.get(0, 0x00) + iGal) % ρ
            else:
                for k, v in iGal.data.items():
                    rGal.data[k] = (rGal.data.get(k, 0x00) + v) % ρ
        return rGal.data.get(0, 0x00) if rGal.data.keys() <= {0} else rGal
    # type conversion operations on variables
    def BINARY(self, xGal, xLen, *, msg = 'binarization error'):
        # Convert x to a binary list with the given bit length, for example, BINARY(5, 3) will return
        # [1, 0, 1] and BINARY(5, 2) will raise an error because 5 is too large for 2 bits. Notice that
        # the bit length should be less than the bit length of the prime number P, since otherwise the
        # binary representation of x will be non-unique.
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
        # Convert a binary list to a galios field element, for example, GALOIS([1, 0, 1]) will return 5.
        return self.SUM(self.MUL(bBit, 0x02 ** iLen) for iLen, bBit in enumerate(xBin))
    def ENUM(self, xGal, kSet, *, msg = 'enumerization error'):
        # Convert x to an enum value, for example, ENUM(3, {1, 3, 5}) will return {1: 0, 3: 1, 5: 0},
        # and ENUM(2, {1, 3, 5}) will raise an error because 2 is not in the set.
        if isinstance(xGal, int):
            xKey = {kInt: 0x01 if (xGal - kInt) % ρ == 0x00 else 0x00 for kInt in kSet}
            assert sum(xBit * kInt for kInt, xBit in xKey.items()) == xGal, msg
            return xKey
        xFrz = tuple(sorted(xGal.data.items()))
        if (xKey := self.enums.get(kSet, {}).get(xFrz)) is not None:
            return xKey
        bind = lambda kInt: self.MKWIRE(lambda getw, args: 0x01 if (getw(xGal) - kInt) % ρ == 0x00 else 0x00)
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
        # Conditional expression, b is a boolean value, t and f are the true and false branches, which
        # can be scalars, (multi-dimensional) lists, dictionaries, or tuples, but should have the same
        # shape.
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
        return self.ADD(self.MUL(bBit, self.SUB(tItm, fItm)), fItm)
    def GETBYBIN(self, lSpc, iBin, cBit = 0x01, *, msg = 'binary index out of range'):
        # Get the value of a (multi-dimensional) list by the given binary index.
        # For example, GETBYBIN([[1, 2], [3, 4], [5, 6]], [1, 0]) will return [5, 6]. The binary index
        # can be any length, but the value it represents should be less than the length of the list.
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
        return self.IF(iBit, self.GETBYBIN(lSpc[iLen:], iBin, self.AND(cBit, iBit)), self.GETBYBIN(lSpc[:iLen], iBin))
    def GETBYKEY(self, lSpc, iKey):
        # Get the value of a (multi-dimensional) list or dictionary by the given key, key should be an
        # enum value. For example, GETBYKEY({2: [1, 2], 3: [3, 4]}, {2: 1, 3: 0}) will return [1, 2].
        iItr = iter(iKey.items())
        kInt, iBit = next(iItr)
        vItm = lSpc[kInt]
        for kInt, iBit in iItr:
            vItm = self.IF(iBit, lSpc[kInt], vItm)
        return vItm
    def SETBYKEY(self, vItm, lSpc, *iKes, cBit = 0x01):
        # Set the value of a (multi-dimensional) list or dictionary by the given keys, it will return
        # a new (multi-dimensional) list or dictionary with the value set.
        # For example, SETBYKEY(5, {2: [1, 2], 3: [3, 4]}, {2: 1, 3: 0}, {0: 0, 1: 1}) means to set the
        # value of {2: [1, 2], 3: [3, 4]}[2][1] to 5, so the result will be {2: [1, 5], 3: [3, 4]}.
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
        self.MKGATE(rBit, xGal, xGal, msg = msg) # asserts that r has to be 1 if x is non-zero
        self.MKGATE(xGal, iGal, rBit, msg = msg) # asserts that r has to be 0 if x is zero
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
        self.MKGATE(0x00, 0x00, self.SUB(xGal, yGal), msg = msg)
    def ASSERT_NE(self, xGal, yGal, *, msg = 'NE assertion failed'):
        self.DIV(0x01, self.SUB(xGal, yGal), msg = msg)
    def ASSERT_ISBOOL(self, xGal, *, msg = 'ISBOOL assertion failed'):
        self.MKGATE(xGal, xGal, xGal, msg = msg)
    def ASSERT_ISPERM(self, lLst, rLst, *, msg = 'ISPERM assertion failed'):
        nLen = len(lLst)
        LLst = [Var({0: sGal}) if isinstance(sGal, int) else sGal for sGal in lLst]
        RLst = [Var({0: dGal}) if isinstance(dGal, int) else dGal for dGal in rLst]
        bind = lambda iLen: self.MKWIRE(lambda getw, args: waksman.genbits(list(map(getw, LLst)), list(map(getw, RLst)))[iLen] % ρ)
        if nLen == 0:
            return
        if nLen == 1:
            self.ASSERT_EQ(lLst[0], rLst[0], msg = msg)
            return
        if nLen == 2:
            cBit = bind(0)
            self.ASSERT_ISBOOL(cBit)
            self.MKGATE(cBit, self.SUB(lLst[1], lLst[0]), self.SUB(rLst[0], lLst[0]), msg = msg)
            self.MKGATE(cBit, self.SUB(lLst[0], lLst[1]), self.SUB(rLst[1], lLst[1]), msg = msg)
            return
        kLen = nLen // 2
        lLen = nLen // 2
        rLen = nLen // 2 + nLen % 2 - 1
        luLs, ldLs = lLst[:kLen], lLst[kLen:]
        ruLs, rdLs = rLst[:kLen], rLst[kLen:]
        for iLen in range(lLen):
            cBit = bind(iLen)
            self.ASSERT_ISBOOL(cBit)
            luLs[iLen], ldLs[iLen] = self.IF(cBit, (ldLs[iLen], luLs[iLen]), (luLs[iLen], ldLs[iLen]))
        for iLen in range(rLen):
            cBit = bind(iLen - rLen)
            self.ASSERT_ISBOOL(cBit)
            ruLs[iLen], rdLs[iLen] = self.IF(cBit, (rdLs[iLen], ruLs[iLen]), (ruLs[iLen], rdLs[iLen]))
        self.ASSERT_ISPERM(luLs, ruLs, msg = msg)
        self.ASSERT_ISPERM(ldLs, rdLs, msg = msg)
    def ASSERT_IN(self, xGal, kSet, *, msg = 'IN assertion failed'):
        # assert x is in the set
        return self.ENUM(xGal, kSet, msg = msg)
    # bitwise operations on binary lists
    def SHL(self, xBin, rLen):
        rLen = rLen % len(xBin)
        return [0x00] * rLen + xBin[:len(xBin) - rLen]
    def SHR(self, xBin, rLen):
        rLen = rLen % len(xBin)
        return xBin[rLen:] + [0x00] * rLen
    def ROL(self, xBin, rLen):
        rLen = len(xBin) - rLen % len(xBin)
        return xBin[rLen:] + xBin[:rLen]
    def ROR(self, xBin, rLen):
        rLen = rLen % len(xBin)
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
        # Add an input parameter to the circuit, the value of the parameter can be set when calling the
        # prove method.
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
class Compiler(ast.NodeVisitor, Circuit):
    # The Compiler class is a wrapper of the Circuit class, it compiles the given Python code to the
    # arithmetic circuits. The Python code should be written in a restricted subset of Python.
    def __init__(self):
        ast.NodeVisitor.__init__(self)
        Circuit.__init__(self)
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
            'isperm': lambda s, d, msg: self.ASSERT_ISPERM(list(map(asgal, s)), list(map(asgal, d)), msg = asstr(msg)),
            'mkgate': lambda x, y, z, msg: self.MKGATE(asgal(x), asgal(y), asgal(z), msg = asstr(msg)),
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
            return self.SHL(asbin(left), asint(right))
        if isinstance(node.op, ast.RShift):
            return self.SHR(asbin(left), asint(right))
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
            "ROR = lambda x, r: x >> r | x << 32 - r\n"
            "CHO = lambda x, y, z: [y[i] if x[i] else z[i] for i in range(32)]\n"
            "TMP = lambda x, y, z, t: [t[i] + z[i] * (x[i] + y[i] - t[i] * 2) for i in range(32)]\n"
            "MAJ = lambda x, y, z: TMP(x, y, z, x & y)\n"
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
            "def compress(V, I):\n"
            "    W = [b32(0) for _ in range(64)]\n"
            "    for j in range(16):\n"
            "        W[j] = I[j]\n"
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
