from dataclasses import dataclass, field
from typing import Callable, Iterable, TypeVar

from pymcl import r as ρ

from . import waksman


Fld = int


@dataclass
class Var:
    # All variables in a program are linear combinations of the entries in its witness vector, so they
    # can be represented by a dictionary that maps the indices of the entries in the witness vector to
    # their coefficients, for example, x = w₀ + 5w₂ + 7w₃ can be represented as {0: 1, 2: 5, 3: 7}, note
    # that the entries with coefficient 0 are always omitted.
    # Besides, constants are always represented by the integer itself.

    data: dict[int, Fld] = field(default_factory=lambda: {})


Gal = Var | Fld


Gate = tuple[Gal, Gal, Gal, str]
Getw = Callable[[Gal], Fld]
Args = dict[str, Fld]
S_Fn = Callable[[Getw, Args], Fld]
M_Fn = Callable[[Getw, Args], Iterable[Fld]]
Func = tuple[None, S_Fn] | tuple[int, M_Fn]


class Witness:
    def __init__(self, funcs: list[Func], args: Args) -> None:
        self.vec: list[Fld] = []
        for n, func in funcs:
            res = func(self.apply, args)
            if n is None:
                self.vec.append(res)
            else:
                assert len(res) == n
                self.vec.extend(res)

    def apply(self, xGal: Gal) -> Fld:
        return xGal if isinstance(xGal, Fld) else sum(self.vec[m] * a for m, a in xGal.data.items()) % ρ  # <w, t> = Σₘ₌₀ᴹ⁻¹ wₘtₘ


Bit = Gal
Bin = list[Bit]
Key = dict[Fld, Bit]
Any = Gal | list["Any"] | dict[Fld, "Any"] | tuple["Any", ...]
Spc = Any | list["Spc"] | dict[Fld, "Spc"]
ANY = TypeVar("ANY", bound=Any)
SPC = TypeVar("SPC", bound=Spc)
Set = frozenset[Fld] | range


class Circuit:
    # The Circuit class is used to construct the arithmetic circuits, it provides a set of methods to
    # create entries in the witness vector, add constraints to the circuit, and perform arithmetic and
    # other operations on the variables linearly combined by the entries in the witness vector.

    wire_count: int  # dimension of the witness vector
    funcs: list[Func]  # functions to generate the witness vector entries
    stmts: dict[int, str]  # the public entries, keys are their indices in the witness vector, and values are their names
    gates: list[Gate]  # the constraints in the circuit, see the MKGATE method for details
    enums: dict[Set, dict[tuple[tuple[int, Fld], ...], Key]]  # memoization of the enum values

    def __init__(self) -> None:
        self.wire_count = 0
        self.funcs = []
        self.stmts = {}
        self.gates = []
        self.enums = {}
        # add a constant 1 to the witness vector
        [self.one] = self.MKWIRE(lambda getw, args: 0x01, "ONE").data

    def MKWIRE(self, func: S_Fn, name: str | None = None) -> Var:
        # Add a new entry defined by the given function to the witness vector.
        # For example, x = MKWIRE(lambda getw, args: getw(y) * getw(z) % ρ) will add a new entry that is
        # defined by the product of the values of y and z to the witness vector, and assign a variable
        # corresponding to the entry to x.
        i = self.wire_count
        self.funcs.append((None, func))
        self.wire_count += 1
        # if name is specified, the entry will be treated as public
        if name is not None:
            self.stmts[i] = name
        return Var({i: 0x01})

    def MKWIRES(self, func: M_Fn, n: int) -> list[Var]:
        # Add n new entries defined by the given function to the witness vector, and return them as a
        # list of variables.
        i = self.wire_count
        self.funcs.append((n, func))
        self.wire_count += n
        return [Var({i + j: 0x01}) for j in range(n)]

    def MKGATE(self, xGal: Gal, yGal: Gal, zGal: Gal, *, msg="assertion error") -> None:
        # Add a constraint to the circuit, the constraint is represented as (x, y, z, msg), which means
        # x * y = z, msg is the error message when the constraint is not satisfied.
        if isinstance(xGal, Fld) or isinstance(yGal, Fld):
            zGal = self.SUB(zGal, self.MUL(xGal, yGal))
            if isinstance(zGal, Fld):
                assert zGal == 0x00, msg
                return
            xGal = 0x00
            yGal = 0x00
        self.gates.append((xGal, yGal, zGal, msg))

    def PARAM(self, name: str, public: bool = False) -> Var:
        # Add a new entry to the witness vector, whose value will be determined by the value correspond-
        # ing to the key named name in the args dictionary at runtime.
        return self.MKWIRE(lambda getw, args: args[name] % ρ, name if public else None)

    def REVEAL(self, name: str, xGal: Gal, *, msg="reveal error") -> Var:
        # Add a public entry to the witness vetor, whose value is equal to that of the given variable.
        rGal = self.MKWIRE(lambda getw, args: getw(xGal), name)
        self.ASSERT_EQZ(self.SUB(xGal, rGal), msg=msg)
        return rGal

    # basic arithmetic operations on variables

    def ADD(self, xGal: Gal, yGal: Gal) -> Gal:
        if isinstance(xGal, Fld):
            xGal = Var({self.one: xGal})
        if isinstance(yGal, Fld):
            yGal = Var({self.one: yGal})
        rGal = Var({k: v for k in xGal.data.keys() | yGal.data.keys() if (v := (xGal.data.get(k, 0x00) + yGal.data.get(k, 0x00)) % ρ)})
        return rGal.data.get(self.one, 0x00) if rGal.data.keys() <= {self.one} else rGal

    def SUB(self, xGal: Gal, yGal: Gal) -> Gal:
        if isinstance(xGal, Fld):
            xGal = Var({self.one: xGal})
        if isinstance(yGal, Fld):
            yGal = Var({self.one: yGal})
        rGal = Var({k: v for k in xGal.data.keys() | yGal.data.keys() if (v := (xGal.data.get(k, 0x00) - yGal.data.get(k, 0x00)) % ρ)})
        return rGal.data.get(self.one, 0x00) if rGal.data.keys() <= {self.one} else rGal

    def SUM(self, iLst: Iterable[Gal], rGal: Gal = 0x00) -> Gal:
        rGal = Var({self.one: rGal}) if isinstance(rGal, Fld) else Var(rGal.data.copy())
        for iGal in iLst:
            if isinstance(iGal, Fld):
                rGal.data[self.one] = rGal.data.get(self.one, 0x00) + iGal
            else:
                for k, v in iGal.data.items():
                    rGal.data[k] = rGal.data.get(k, 0x00) + v
        rGal = Var({k: t for k, v in rGal.data.items() if (t := v % ρ)})
        return rGal.data.get(self.one, 0x00) if rGal.data.keys() <= {self.one} else rGal

    def MUL(self, xGal: Gal, yGal: Gal, *, msg="multiplication error") -> Gal:
        if isinstance(xGal, Fld) and isinstance(yGal, Fld):
            return xGal * yGal % ρ
        if xGal == 0x00 or yGal == 0x00:
            return 0x00
        if isinstance(yGal, Fld) and isinstance(xGal, Var):
            return Var({k: v * yGal % ρ for k, v in xGal.data.items()})
        if isinstance(xGal, Fld) and isinstance(yGal, Var):
            return Var({k: v * xGal % ρ for k, v in yGal.data.items()})
        zGal = self.MKWIRE(lambda getw, args: getw(xGal) * getw(yGal) % ρ)
        self.MKGATE(xGal, yGal, zGal, msg=msg)
        return zGal

    def DIV(self, xGal: Gal, yGal: Gal, *, msg="division error") -> Gal:
        # Division in the finite field GF(P).
        if isinstance(xGal, Fld) and isinstance(yGal, Fld):
            return xGal * pow(yGal, -1, ρ) % ρ
        if xGal == 0x00:
            return 0x00
        if isinstance(yGal, Fld) and isinstance(xGal, Var):
            return Var({k: v * pow(yGal, -1, ρ) % ρ for k, v in xGal.data.items()})
        zGal = self.MKWIRE(lambda getw, args: getw(xGal) * pow(getw(yGal), -1, ρ) % ρ)
        self.MKGATE(zGal, yGal, xGal, msg=msg)
        return zGal

    # all other operations can be implemented using the above basic operations

    def POW(self, xGal: Gal, nBin: Bin) -> Gal:
        nBit, *nBin = nBin
        rGal = self.IF(nBit, xGal, 0x01)
        for nBit in nBin:
            xGal = self.MUL(xGal, xGal)
            kGal = self.IF(nBit, xGal, 0x01)
            rGal = self.MUL(rGal, kGal)
        return rGal

    # type conversion operations on variables

    def BINARY(self, xGal: Gal, xLen: int, *, msg="binarization error") -> Bin:
        # Convert x to a binary list with the given bit length, for example, BINARY(5, 3) will return
        # [1, 0, 1] and BINARY(5, 2) will raise an error because 5 is too large for 2 bits. Notice that
        # the bit length should be less than the bit length of the prime number P, since otherwise the
        # binary representation of x will be non-unique.
        if not 0 <= xLen < ρ.bit_length():
            raise ValueError("invalid bit length")
        if isinstance(xGal, Fld):
            xBin = [xGal >> iLen & 0x01 for iLen in range(xLen)]
            assert sum(xBit * 0x02**iLen for iLen, xBit in enumerate(xBin)) == xGal, msg
            return xBin
        xBin = self.MKWIRES(lambda getw, args: [getw(xGal) >> iLen & 0x01 for iLen in range(xLen)], xLen)
        for iLen, xBit in enumerate(xBin):
            self.ASSERT_IS_BOOL(xBit)
        tGal = self.SUM(self.MUL(xBit, 0x02**iLen) for iLen, xBit in enumerate(xBin))
        self.ASSERT_EQZ(self.SUB(xGal, tGal), msg=msg)
        return xBin

    def GALOIS(self, xBin: Bin) -> Gal:
        # Convert a binary list to a galios field element, for example, GALOIS([1, 0, 1]) will return 5.
        return self.SUM(self.MUL(bBit, 0x02**iLen) for iLen, bBit in enumerate(xBin))

    def ENUM(self, xGal: Gal, kSet: Set, *, msg="enumerization error") -> Key:
        # Convert x to an enum value, for example, ENUM(3, {1, 3, 5}) will return {1: 0, 3: 1, 5: 0},
        # and ENUM(2, {1, 3, 5}) will raise an error because 2 is not in the set.
        if isinstance(xGal, Fld):
            xKey = {kInt: 0x01 if xGal == kInt else 0x00 for kInt in kSet}
            assert sum(xBit * kInt for kInt, xBit in xKey.items()) == xGal, msg
            return xKey
        xFrz = tuple(sorted(xGal.data.items()))
        xKey = self.enums.get(kSet, {}).get(xFrz)
        if xKey is not None:
            return xKey
        xKey = dict(zip(kSet, self.MKWIRES(lambda getw, args: [0x01 if getw(xGal) == kInt else 0x00 for kInt in kSet], len(kSet))))
        for kInt, xBit in xKey.items():
            self.ASSERT_IS_BOOL(xBit)
        tGal = self.SUM(self.MUL(xBit, kInt) for kInt, xBit in xKey.items())
        eGal = self.SUM(self.MUL(xBit, 0x01) for kInt, xBit in xKey.items())
        self.ASSERT_EQZ(self.SUB(xGal, tGal), msg=msg)
        self.ASSERT_EQZ(self.SUB(0x01, eGal), msg=msg)
        self.enums.setdefault(kSet, {})[xFrz] = xKey  # optimize by memoization
        return xKey

    # conditional expression and get/set operations on lists and dictionaries

    def IF(self, bBit: Bit, tItm: ANY, fItm: ANY) -> ANY:
        # Conditional expression, b is a boolean value, t and f are the true and false branches, which
        # can be scalars, (multi-dimensional) lists, dictionaries, or tuples, but should have the same
        # shape.
        # optimize when b is a constant
        if bBit == 0x01:
            return tItm
        if bBit == 0x00:
            return fItm
        if isinstance(tItm, dict) and isinstance(fItm, dict):
            return dict((zInt, self.IF(bBit, tItm[zInt], fItm[zInt])) for zInt in frozenset(tItm))
        if isinstance(tItm, list) and isinstance(fItm, list):
            return list(self.IF(bBit, tItm[zInt], fItm[zInt]) for zInt in range(len(tItm)))
        if isinstance(tItm, tuple) and isinstance(fItm, tuple):
            return tuple(self.IF(bBit, tItm[zInt], fItm[zInt]) for zInt in range(len(tItm)))
        return self.ADD(self.MUL(bBit, self.SUB(tItm, fItm)), fItm)

    def GETBYBIN(self, lSpc: list[ANY], iBin: Bin, cBit: Bit = 0x01, *, msg="binary index out of range") -> ANY:
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
            self.MKGATE(cBit, iBit, 0x00, msg=msg)
            return self.GETBYBIN(lSpc, iBin, cBit)
        return self.IF(iBit, self.GETBYBIN(lSpc[iLen:], iBin, self.AND(cBit, iBit)), self.GETBYBIN(lSpc[:iLen], iBin))

    def GETBYKEY(self, lSpc: dict[Fld, ANY], iKey: Key) -> ANY:
        # Get the value of a (multi-dimensional) list or dictionary by the given key, key should be an
        # enum value. For example, GETBYKEY({2: [1, 2], 3: [3, 4]}, {2: 1, 3: 0}) will return [1, 2].
        iItr = iter(iKey.items())
        kInt, iBit = next(iItr)
        vItm = lSpc[kInt]
        for kInt, iBit in iItr:
            vItm = self.IF(iBit, lSpc[kInt], vItm)
        return vItm

    def SETBYKEY(self, vItm: ANY, lSpc: SPC, *iKes: Key, cBit: Bit = 0x01) -> SPC:
        # Set the value of a (multi-dimensional) list or dictionary by the given keys, it will return
        # a new (multi-dimensional) list or dictionary with the value set.
        # For example, SETBYKEY(5, {2: [1, 2], 3: [3, 4]}, {2: 1, 3: 0}, {0: 0, 1: 1}) means to set the
        # value of {2: [1, 2], 3: [3, 4]}[2][1] to 5, so the result will be {2: [1, 5], 3: [3, 4]}.
        if len(iKes) == 0:
            return self.IF(cBit, vItm, lSpc)
        iKey, *iKes = iKes
        if isinstance(lSpc, list):
            return [self.SETBYKEY(vItm, lSpc[kInt], *iKes, cBit=self.AND(cBit, iBit)) for kInt, iBit in iKey.items()]
        if isinstance(lSpc, dict):
            return {kInt: self.SETBYKEY(vItm, lSpc[kInt], *iKes, cBit=self.AND(cBit, iBit)) for kInt, iBit in iKey.items()}

    # logical operations on boolean values

    def NOT(self, xBit: Bit) -> Bit:
        return self.SUB(0x01, xBit)

    def AND(self, xBit: Bit, yBit: Bit) -> Bit:
        return self.MUL(xBit, yBit)

    def OR(self, xBit: Bit, yBit: Bit) -> Bit:
        return self.SUB(0x01, self.MUL(self.SUB(0x01, xBit), self.SUB(0x01, yBit)))

    def XOR(self, xBit: Bit, yBit: Bit) -> Bit:
        return self.DIV(self.SUB(0x01, self.MUL(self.SUB(0x01, self.MUL(xBit, 0x02)), self.SUB(0x01, self.MUL(yBit, 0x02)))), 0x02)

    # compare operations on galios field elements

    def GE(self, xGal: Gal, yGal: Gal, bLen: int, msg="GE compare failed") -> Bit:  # 0x00 <= xGal - yGal < 0x02 ** bLen
        return self.BINARY(self.ADD(0x02**bLen, self.SUB(xGal, yGal)), bLen + 1, msg=msg)[bLen]

    def LE(self, xGal: Gal, yGal: Gal, bLen: int, msg="LE compare failed") -> Bit:  # 0x00 <= yGal - xGal < 0x02 ** bLen
        return self.BINARY(self.ADD(0x02**bLen, self.SUB(yGal, xGal)), bLen + 1, msg=msg)[bLen]

    def GT(self, xGal: Gal, yGal: Gal, bLen: int, msg="GT compare failed") -> Bit:  # 0x00 < xGal - yGal <= 0x02 ** bLen
        return self.BINARY(self.ADD(0x02**bLen, self.SUB(self.SUB(xGal, yGal), 0x01)), bLen + 1, msg=msg)[bLen]

    def LT(self, xGal: Gal, yGal: Gal, bLen: int, msg="LT compare failed") -> Bit:  # 0x00 < yGal - xGal <= 0x02 ** bLen
        return self.BINARY(self.ADD(0x02**bLen, self.SUB(self.SUB(yGal, xGal), 0x01)), bLen + 1, msg=msg)[bLen]

    def NEZ(self, xGal: Gal, *, msg="booleanization error") -> Bit:
        # Convert x to a boolean value, return 1 if x is non-zero and 0 if x is zero.
        if isinstance(xGal, Fld):
            return pow(xGal, ρ - 1, ρ)
        iGal = self.MKWIRE(lambda getw, args: pow(getw(xGal), ρ - 2, ρ))
        rBit = self.MKWIRE(lambda getw, args: pow(getw(xGal), ρ - 1, ρ))
        self.MKGATE(rBit, xGal, xGal, msg=msg)  # asserts that r has to be 1 if x is non-zero
        self.MKGATE(xGal, iGal, rBit, msg=msg)  # asserts that r has to be 0 if x is zero
        return rBit

    # assertion operations on galios field elements

    def ASSERT_GE(self, xGal: Gal, yGal: Gal, bLen: int, *, msg="GE assertion failed") -> Bin:  # assert 0x00 <= xGal - yGal < 0x02 ** bLen
        return self.BINARY(self.SUB(xGal, yGal), bLen, msg=msg)

    def ASSERT_LE(self, xGal: Gal, yGal: Gal, bLen: int, *, msg="LE assertion failed") -> Bin:  # assert 0x00 <= yGal - xGal < 0x02 ** bLen
        return self.BINARY(self.SUB(yGal, xGal), bLen, msg=msg)

    def ASSERT_GT(self, xGal: Gal, yGal: Gal, bLen: int, *, msg="GT assertion failed") -> Bin:  # assert 0x00 < xGal - yGal <= 0x02 ** bLen
        return self.BINARY(self.SUB(self.SUB(xGal, yGal), 0x01), bLen, msg=msg)

    def ASSERT_LT(self, xGal: Gal, yGal: Gal, bLen: int, *, msg="LT assertion failed") -> Bin:  # assert 0x00 < yGal - xGal <= 0x02 ** bLen
        return self.BINARY(self.SUB(self.SUB(yGal, xGal), 0x01), bLen, msg=msg)

    def ASSERT_EQZ(self, xGal: Gal, *, msg="EQZ assertion failed") -> None:
        self.MKGATE(0x00, 0x00, xGal, msg=msg)

    def ASSERT_NEZ(self, xGal: Gal, *, msg="NEZ assertion failed") -> None:
        self.DIV(0x01, xGal, msg=msg)

    def ASSERT_IS_BOOL(self, xGal: Gal, *, msg="IS_BOOL assertion failed") -> None:
        # Assert x is a boolean value.
        self.MKGATE(xGal, xGal, xGal, msg=msg)

    def ASSERT_IS_PERM_IMPL(self, lLst: list[Gal], rLst: list[Gal], *, msg="IS_PERM assertion failed") -> None:
        # Assert that the two lists are permutations of each other using the Waksman network.
        nLen = max(len(lLst), len(rLst))
        if nLen == 0:
            return
        if nLen == 1:
            self.ASSERT_EQZ(self.SUB(lLst[0], rLst[0]), msg=msg)
            return
        kLen = nLen // 2
        lLen = nLen // 2
        rLen = nLen // 2 + nLen % 2 - 1
        wBin = self.MKWIRES(lambda getw, args: waksman.genbits(list(map(getw, lLst)), list(map(getw, rLst)), no_rec=True), lLen + rLen)
        if nLen == 2:
            cBit = wBin[0]
            self.ASSERT_IS_BOOL(cBit)
            self.MKGATE(cBit, self.SUB(lLst[1], lLst[0]), self.SUB(rLst[0], lLst[0]), msg=msg)
            self.MKGATE(cBit, self.SUB(lLst[0], lLst[1]), self.SUB(rLst[1], lLst[1]), msg=msg)
            return
        if nLen == 3:
            ldLs = lLst[1:]
            rdLs = rLst[1:]
            lBit = wBin[0]
            rBit = wBin[1]
            self.ASSERT_IS_BOOL(lBit)
            self.ASSERT_IS_BOOL(rBit)
            ldLs[0] = self.IF(lBit, ldLs[0], lLst[0])
            rdLs[0] = self.IF(rBit, rdLs[0], rLst[0])
            self.ASSERT_IS_PERM_IMPL(ldLs, rdLs, msg=msg)
            xGal = self.MKWIRE(lambda getw, args: max(getw(lLst[getw(lBit)]), getw(rLst[getw(rBit)])))
            self.MKGATE(lBit, self.SUB(lLst[1], lLst[0]), self.SUB(xGal, lLst[0]), msg=msg)
            self.MKGATE(rBit, self.SUB(rLst[1], rLst[0]), self.SUB(xGal, rLst[0]), msg=msg)
            return
        luLs, ldLs = lLst[:kLen], lLst[kLen:]
        ruLs, rdLs = rLst[:kLen], rLst[kLen:]
        for iLen in range(lLen):
            cBit = wBin[iLen]
            self.ASSERT_IS_BOOL(cBit)
            luLs[iLen], ldLs[iLen] = self.IF(cBit, (ldLs[iLen], luLs[iLen]), (luLs[iLen], ldLs[iLen]))
        for iLen in range(rLen):
            cBit = wBin[iLen - rLen]
            self.ASSERT_IS_BOOL(cBit)
            ruLs[iLen], rdLs[iLen] = self.IF(cBit, (rdLs[iLen], ruLs[iLen]), (ruLs[iLen], rdLs[iLen]))
        self.ASSERT_IS_PERM_IMPL(luLs, ruLs, msg=msg)
        self.ASSERT_IS_PERM_IMPL(ldLs, rdLs, msg=msg)

    def ASSERT_IS_PERM(self, lLst: list[Gal], rLst: list[Gal], *, msg="IS_PERM assertion failed") -> None:
        # Optimize the IS_PERM assertion by removing the common elements in the two lists before the assertion.
        lMap: dict[tuple[tuple[int, Gal], ...], list[int]] = {}
        rMap: dict[tuple[tuple[int, Gal], ...], list[int]] = {}
        for lLen, lGal in enumerate(lLst):
            lMap.setdefault(tuple(sorted((Var({self.one: lGal}) if isinstance(lGal, Fld) else lGal).data.items())), []).append(lLen)
        for rLen, rGal in enumerate(rLst):
            rMap.setdefault(tuple(sorted((Var({self.one: rGal}) if isinstance(rGal, Fld) else rGal).data.items())), []).append(rLen)
        lLst = lLst.copy()
        rLst = rLst.copy()
        for xGal in set(lMap) & set(rMap):
            for lLen, rLen in zip(lMap[xGal], rMap[xGal]):
                lLst[lLen] = None
                rLst[rLen] = None
        lLst = [lGal for lGal in lLst if lGal is not None]
        rLst = [rGal for rGal in rLst if rGal is not None]
        self.ASSERT_IS_PERM_IMPL(lLst, rLst, msg=msg)

    # bitwise operations on binary lists

    def SHL(self, xBin: Bin, rLen: int) -> Bin:
        rLen = rLen % len(xBin)
        return [0x00] * rLen + xBin[: len(xBin) - rLen]

    def SHR(self, xBin: Bin, rLen: int) -> Bin:
        rLen = rLen % len(xBin)
        return xBin[rLen:] + [0x00] * rLen

    def ROL(self, xBin: Bin, rLen: int) -> Bin:
        rLen = len(xBin) - rLen % len(xBin)
        return xBin[rLen:] + xBin[:rLen]

    def ROR(self, xBin: Bin, rLen: int) -> Bin:
        rLen = rLen % len(xBin)
        return xBin[rLen:] + xBin[:rLen]

    def BITNOT(self, xBin: Bin) -> Bin:
        return [self.NOT(xBit) for xBit in xBin]

    def BITAND(self, xBin: Bin, yBin: Bin) -> Bin:
        # assert len(xBin) == len(yBin)
        return [self.AND(xBit, yBit) for xBit, yBit in zip(xBin, yBin)]

    def BITOR(self, xBin: Bin, yBin: Bin) -> Bin:
        # assert len(xBin) == len(yBin)
        return [self.OR(xBit, yBit) for xBit, yBit in zip(xBin, yBin)]

    def BITXOR(self, xBin: Bin, yBin: Bin) -> Bin:
        # assert len(xBin) == len(yBin)
        return [self.XOR(xBit, yBit) for xBit, yBit in zip(xBin, yBin)]

    # arithmetic operations on binary lists

    def BINADD(self, xBin: Bin, yBin: Bin, cBit: Bit = 0x00) -> tuple[Bin, Bit]:
        # assert len(xBin) == len(yBin)
        bLen = max(len(xBin), len(yBin))
        zBin = self.BINARY(self.ADD(self.GALOIS(xBin), self.ADD(self.GALOIS(self.ADD(0x00, bBit) for bBit in yBin), self.ADD(0x00, cBit))), bLen + 1)
        return zBin[:bLen], self.ADD(0x00, zBin[bLen])

    def BINSUB(self, xBin: Bin, yBin: Bin, cBit: Bit = 0x00) -> tuple[Bin, Bit]:
        # assert len(xBin) == len(yBin)
        bLen = max(len(xBin), len(yBin))
        zBin = self.BINARY(self.ADD(self.GALOIS(xBin), self.ADD(self.GALOIS(self.SUB(0x01, bBit) for bBit in yBin), self.SUB(0x01, cBit))), bLen + 1)
        return zBin[:bLen], self.SUB(0x01, zBin[bLen])

    def BINSUM(self, List: Iterable[Bin], cGal=0x00) -> Bin:  # c < len(List)
        # BINSUM generates less constraints than BINADD/BINSUB when summing multiple binary lists.
        # assert len(set(map(len, List))) == 1
        bLen = max(map(len, List))
        return self.BINARY(self.SUM(map(self.GALOIS, List), cGal), bLen + (len(List) - 1).bit_length())[:bLen]

    def BINMUL(self, xBin: Bin, yBin: Bin, cBin: Bin = [], dBin: Bin = []) -> tuple[Bin, Bin]:
        # assert len(xBin) == len(yBin)
        bLen = max(len(xBin), len(yBin))
        assert len(cBin) <= bLen
        assert len(dBin) <= bLen
        zBin = self.BINARY(self.ADD(self.MUL(self.GALOIS(xBin), self.GALOIS(yBin)), self.ADD(self.GALOIS(cBin), self.GALOIS(dBin))), bLen * 2)
        return zBin[:bLen], zBin[bLen:]

    def BINDIVMOD(self, xBin: Bin, yBin: Bin, *, msg="binary divmod error") -> tuple[Bin, Bin]:
        # Division and modulo operations on binary lists.
        qLen = len(xBin)
        rLen = len(yBin)
        assert (0x02**rLen - 0x01) * (0x02**qLen) < ρ
        xGal = self.GALOIS(xBin)
        yGal = self.GALOIS(yBin)
        if xGal == 0x00:
            return [0x00] * qLen, [0x00] * rLen
        if yGal == 0x00:
            raise ZeroDivisionError
        if isinstance(xGal, Fld) and isinstance(yGal, Fld):
            qGal, rGal = divmod(xGal, yGal)
            return [qGal >> iLen & 0x01 for iLen in range(qLen)], [rGal >> iLen & 0x01 for iLen in range(rLen)]
        qGal = self.MKWIRE(lambda getw, args: getw(xGal) // getw(yGal))
        rGal = self.MKWIRE(lambda getw, args: getw(xGal) % getw(yGal))
        self.MKGATE(qGal, yGal, self.SUB(xGal, rGal), msg=msg)  # assert y * q == x - r
        qBin = self.ASSERT_GE(qGal, 0x00, qLen, msg=msg)
        rBin = self.ASSERT_GE(rGal, 0x00, rLen, msg=msg)
        _Bin = self.ASSERT_LT(rGal, yGal, rLen, msg=msg)
        return qBin, rBin

    def BINPOW(self, xBin: Bin, nBin: Bin) -> Bin:
        bLen = len(xBin)
        nBit, *nBin = nBin
        rBin = self.IF(nBit, xBin, self.BINARY(0x01, bLen))
        for nBit in nBin:
            xBin = self.BINMUL(xBin, xBin)[0]
            kBin = self.IF(nBit, xBin, self.BINARY(0x01, bLen))
            rBin = self.BINMUL(rBin, kBin)[0]
        return rBin

    # compare operations on binary lists

    def BINGE(self, xBin: Bin, yBin: Bin) -> Bit:
        # assert len(xBin) == len(yBin)
        bLen = max(len(xBin), len(yBin))
        return self.BINARY(self.ADD(0x02**bLen, self.SUB(self.GALOIS(xBin), self.GALOIS(yBin))), bLen + 1)[bLen]

    def BINLE(self, xBin: Bin, yBin: Bin) -> Bit:
        # assert len(xBin) == len(yBin)
        bLen = max(len(xBin), len(yBin))
        return self.BINARY(self.ADD(0x02**bLen, self.SUB(self.GALOIS(yBin), self.GALOIS(xBin))), bLen + 1)[bLen]

    def BINGT(self, xBin: Bin, yBin: Bin) -> Bit:
        # assert len(xBin) == len(yBin)
        bLen = max(len(xBin), len(yBin))
        return self.BINARY(self.ADD(0x02**bLen, self.SUB(self.SUB(self.GALOIS(xBin), self.GALOIS(yBin)), 0x01)), bLen + 1)[bLen]

    def BINLT(self, xBin: Bin, yBin: Bin) -> Bit:
        # assert len(xBin) == len(yBin)
        bLen = max(len(xBin), len(yBin))
        return self.BINARY(self.ADD(0x02**bLen, self.SUB(self.SUB(self.GALOIS(yBin), self.GALOIS(xBin)), 0x01)), bLen + 1)[bLen]

    # assertion operations on binary lists

    def ASSERT_BINGE(self, xBin: Bin, yBin: Bin, *, msg="BINGE assertion failed") -> None:
        # assert len(xBin) == len(yBin)
        bLen = max(len(xBin), len(yBin))
        assert bLen + 1 < ρ.bit_length()
        self.BINARY(self.SUB(self.GALOIS(xBin), self.GALOIS(yBin)), bLen, msg=msg)

    def ASSERT_BINLE(self, xBin: Bin, yBin: Bin, *, msg="BINLE assertion failed") -> None:
        # assert len(xBin) == len(yBin)
        bLen = max(len(xBin), len(yBin))
        assert bLen + 1 < ρ.bit_length()
        self.BINARY(self.SUB(self.GALOIS(yBin), self.GALOIS(xBin)), bLen, msg=msg)

    def ASSERT_BINGT(self, xBin: Bin, yBin: Bin, *, msg="BINGT assertion failed") -> None:
        # assert len(xBin) == len(yBin)
        bLen = max(len(xBin), len(yBin))
        assert bLen + 1 < ρ.bit_length()
        self.BINARY(self.SUB(self.SUB(self.GALOIS(xBin), self.GALOIS(yBin)), 0x01), bLen, msg=msg)

    def ASSERT_BINLT(self, xBin: Bin, yBin: Bin, *, msg="BINLT assertion failed") -> None:
        # assert len(xBin) == len(yBin)
        bLen = max(len(xBin), len(yBin))
        assert bLen + 1 < ρ.bit_length()
        self.BINARY(self.SUB(self.SUB(self.GALOIS(yBin), self.GALOIS(xBin)), 0x01), bLen, msg=msg)
