import waksman
import pymcl
ρ = pymcl.r
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