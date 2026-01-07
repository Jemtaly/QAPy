from dataclasses import dataclass, field
from typing import Callable, Iterable

from pymcl import r as ρ


Fld = int


@dataclass
class Var:
    # All variables in a program are linear combinations of the entries in its witness vector, so they
    # can be represented by a dictionary that maps the indices of the entries in the witness vector to
    # their coefficients, for example, x = w₀ + 5w₂ + 7w₃ can be represented as {0: 1, 2: 5, 3: 7}, note
    # that the entries with coefficient 0 are always omitted.

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
