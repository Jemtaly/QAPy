import multiprocessing
import random
from typing import TypeVar, Iterable

import fft

from pymcl import Fr, G1, G2, pairing, g1, g2, r as ρ

from circuit import Witness, Gate, Fld


Gn = TypeVar("Gn", G1, G2)
Fv = Fr | Fld


# scalar multiplication and dot product optimized for parallel execution


THREADS = None  # automatically set to the number of CPU cores


def worker(Group: type[Gn], p: str, z: str) -> str:
    return str(Group(p) * Fr(z))


def scalar_mult_parallel(P: Gn, Zs: Iterable[Fv]) -> list[Gn]:
    Group = type(P)
    with multiprocessing.Pool(THREADS) as pool:
        return [Group(q) for q in pool.starmap(worker, ((Group, str(P), str(Z)) for Z in Zs))]


def dot_prod_parallel(O: Gn, Ps: Iterable[Gn], Zs: Iterable[Fv]) -> Gn:
    Group = type(O)
    with multiprocessing.Pool(THREADS) as pool:
        return sum((Group(q) for q in pool.starmap(worker, ((Group, str(P), str(Z)) for P, Z in zip(Ps, Zs, strict=True)))), O)


# Groth16 zk-SNARK setup, prove, and verify methods


def setup(
    wire_count: int,
    skeys: Iterable[int],
    gates: list[Gate],
) -> tuple[
    G1,
    G1,
    G1,
    G2,
    G2,
    G2,
    list[G1],
    list[G1],
    list[G1],
    list[G2],
    list[G1],
]:
    α = random.randrange(1, ρ)
    β = random.randrange(1, ρ)
    γ = random.randrange(1, ρ)
    δ = random.randrange(1, ρ)
    τ = random.randrange(1, ρ)
    N = len(gates)
    M = wire_count
    I = 1 << (N - 1).bit_length()  # the smallest power of 2 that is not less than N
    p = fft.pru(I, ρ)  # the primitive I-th root of unity in GF(P)
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
    for X, (aM, bM, cM, msg) in zip(XI, gates):
        for m, a in [(0, aM)] if isinstance(aM, int) else aM.data.items():
            AτM[m] += X * a
        for m, b in [(0, bM)] if isinstance(bM, int) else bM.data.items():
            BτM[m] += X * b
        for m, c in [(0, cM)] if isinstance(cM, int) else cM.data.items():
            CτM[m] += X * c
    Zτ = pow(τ, I, ρ) - 0x01  # Z(τ), where Z(X) = Πᵢ₌₀ᴵ⁻¹ (X - pⁱ)
    Γ = pow(γ, -1, ρ)
    Δ = pow(δ, -1, ρ)
    α1 = g1 * Fr(str(α))
    β1 = g1 * Fr(str(β))
    δ1 = g1 * Fr(str(δ))
    β2 = g2 * Fr(str(β))
    γ2 = g2 * Fr(str(γ))
    δ2 = g2 * Fr(str(δ))
    u1U = scalar_mult_parallel(g1, ((β * AτM[m] + α * BτM[m] + CτM[m]) * Γ % ρ for m in skeys))
    v1V = scalar_mult_parallel(g1, ((β * AτM[m] + α * BτM[m] + CτM[m]) * Δ % ρ for m in range(M) if m not in skeys))
    x1I = scalar_mult_parallel(g1, fft.pows(τ, I, ρ))
    x2I = scalar_mult_parallel(g2, fft.pows(τ, I, ρ))
    y1I = scalar_mult_parallel(g1, (x * Δ * Zτ % ρ for x in fft.pows(τ, I, ρ)))
    return α1, β1, δ1, β2, γ2, δ2, u1U, v1V, x1I, x2I, y1I


def prove(
    wire_count: int,
    skeys: Iterable[int],
    gates: list[Gate],
    α1: G1,
    β1: G1,
    δ1: G1,
    β2: G2,
    δ2: G2,
    v1V: list[G1],
    x1I: list[G1],
    x2I: list[G2],
    y1I: list[G1],
    witness: Witness,
) -> tuple[
    G1,
    G2,
    G1,
    list[Fld],
]:
    r = random.randrange(1, ρ)
    s = random.randrange(1, ρ)
    N = len(gates)
    M = wire_count
    I = 1 << (N - 1).bit_length()
    J = 1 << (N - 1).bit_length() + 1
    p = fft.pru(I, ρ)
    q = fft.pru(J, ρ)
    wM = witness.vec
    uU = [wM[m] for m in skeys]
    vV = [wM[m] for m in range(M) if m not in skeys]
    awN = []
    bwN = []
    cwN = []
    for aM, bM, cM, msg in gates:
        aw = witness.apply(aM)
        bw = witness.apply(bM)
        cw = witness.apply(cM)
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
    awI = fft.fft([Aw * k % ρ for k, Aw in zip(fft.pows(q, I, ρ), AwI, strict=True)], p, ρ)  # Coset FFT
    bwI = fft.fft([Bw * k % ρ for k, Bw in zip(fft.pows(q, I, ρ), BwI, strict=True)], p, ρ)  # Coset FFT
    cwI = fft.fft([Cw * k % ρ for k, Cw in zip(fft.pows(q, I, ρ), CwI, strict=True)], p, ρ)  # Coset FFT
    hI = [(ρ - 1) // 2 * (aw * bw - cw) % ρ for aw, bw, cw in zip(awI, bwI, cwI, strict=True)]  # (A * B - C) / Z on coset
    HI = [H * k % ρ for k, H in zip(fft.pows(pow(q, -1, ρ), I, ρ), fft.ifft(hI, p, ρ), strict=True)]  # Coset iFFT
    A1 = α1 + δ1 * Fr(str(r))
    A1 = dot_prod_parallel(A1, x1I, AwI)
    B1 = β1 + δ1 * Fr(str(s))
    B1 = dot_prod_parallel(B1, x1I, BwI)
    B2 = β2 + δ2 * Fr(str(s))
    B2 = dot_prod_parallel(B2, x2I, BwI)
    C1 = A1 * Fr(str(s)) + B1 * Fr(str(r)) - δ1 * Fr(str(r * s % ρ))
    C1 = dot_prod_parallel(C1, y1I, HI)
    C1 = dot_prod_parallel(C1, v1V, vV)
    return A1, B2, C1, uU


def verify(
    names: Iterable[str],
    α1: G1,
    β2: G2,
    γ2: G2,
    δ2: G2,
    u1U: list[G1],
    A1: G1,
    B2: G2,
    C1: G1,
    uU: list[Fld],
) -> tuple[
    bool,
    list[tuple[str, Fld]],
]:
    D1 = g1 * Fr(str(0))
    D1 = dot_prod_parallel(D1, u1U, uU)
    return pairing(A1, B2) == pairing(α1, β2) * pairing(D1, γ2) * pairing(C1, δ2), list(zip(names, uU, strict=True))
