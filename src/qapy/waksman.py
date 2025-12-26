from typing import Literal, TypeVar


def network(n: int, j: int = 0) -> list[tuple[int, int]]:
    if n <= 1:
        return []
    k = n // 2
    lbitn = n // 2
    rbitn = n // 2 + n % 2 - 1
    net: list[tuple[int, int]] = []
    for i in range(lbitn):
        net.append((j + i, j + i + k))
    net += network(k, j)
    net += network(n - k, j + k)
    for i in range(rbitn):
        net.append((j + i, j + i + k))
    return net


T = TypeVar("T")


def genbits(lft: list[T], rgt: list[T], no_rec: bool = False) -> list[Literal[0, 1]]:
    idx = {t: i for i, t in enumerate(set(lft) | set(rgt))}
    n = len(idx)
    if n <= 1:
        return []
    k = n // 2
    lbitn = n // 2
    rbitn = n // 2 + n % 2 - 1
    # generate lookup tables
    ls: list[int] = [None] * n  # type: ignore
    rs: list[int] = [None] * n  # type: ignore
    for i, v in enumerate(lft):
        ls[idx[v]] = i
    for i, v in enumerate(rgt):
        rs[idx[v]] = i
    l2r: list[int] = [None] * n  # type: ignore
    r2l: list[int] = [None] * n  # type: ignore
    for l, r in zip(ls, rs):
        l2r[r] = l
        r2l[l] = r
    # left and right bits
    lbits: list[Literal[0, 1]] = [None] * lbitn  # type: ignore
    rbits: list[Literal[0, 1]] = [None] * rbitn  # type: ignore
    # generate bits
    if n % 2 == 0:
        l = n - 1
        r = l2r[l]
        while True:
            lbits[r % k] = 1 if r < k else 0
            r = r + k if r < k else r - k
            l = r2l[r]
            if l == k - 1:
                break
            rbits[l % k] = 0 if l < k else 1
            l = l + k if l < k else l - k
            r = l2r[l]
    else:
        l = n - 1
        r = l2r[l]
        while True:
            if r == n - 1:
                break
            lbits[r % k] = 1 if r < k else 0
            r = r + k if r < k else r - k
            l = r2l[r]
            rbits[l % k] = 0 if l < k else 1
            l = l + k if l < k else l - k
            r = l2r[l]
    # generate remaining bits
    i = rbitn
    while True:
        for i in reversed(range(i)):
            if rbits[i] is None:
                break
        else:
            break
        l = i + k
        r = l2r[l]
        while True:
            lbits[r % k] = 1 if r < k else 0
            r = r + k if r < k else r - k
            l = r2l[r]
            rbits[l % k] = 0 if l < k else 1
            l = l + k if l < k else l - k
            r = l2r[l]
            if l == i + k:
                break
    if no_rec:
        return lbits + rbits
    # apply swaps to the left and right inputs
    ulft, dlft = lft[:k], lft[k:]
    for i in range(lbitn):
        if lbits[i]:
            ulft[i], dlft[i] = dlft[i], ulft[i]
    urgt, drgt = rgt[:k], rgt[k:]
    for i in range(rbitn):
        if rbits[i]:
            urgt[i], drgt[i] = drgt[i], urgt[i]
    # generate bits for the upper and lower halves
    ubits = genbits(ulft, urgt)
    dbits = genbits(dlft, drgt)
    # concatenate and return the bits
    return lbits + ubits + dbits + rbits


def apply(src: list[T], net: list[tuple[int, int]], bits: list[Literal[0, 1]]) -> None:
    for bit, (i, j) in zip(bits, net):
        if bit:
            src[i], src[j] = src[j], src[i]


if __name__ == "__main__":
    import random

    keys = [chr(i) for i in range(ord("A"), ord("Z") + 1)]

    net = network(len(keys))

    reordered_src = random.sample(keys, len(keys))
    reordered_dst = random.sample(keys, len(keys))

    bits = genbits(reordered_src, reordered_dst)

    apply(reordered_src, net, bits)

    assert reordered_src == reordered_dst
