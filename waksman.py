def network(N, j = 0):
    if N == 1:
        return []
    if N == 2:
        return [(j, j + 1)]
    K = N // 2
    L = N // 2
    R = N // 2 + N % 2 - 1
    net = []
    for i in range(L):
        net.append((j + i, j + i + K))
    net += network(K, j)
    net += network(N - K, j + K)
    for i in range(R):
        net.append((j + i, j + i + K))
    return net
def genbits(lft, rgt):
    N = min(len(lft), len(rgt))
    if N == 1:
        return []
    if N == 2:
        return [lft[0] != rgt[0]]
    K = N // 2
    L = N // 2
    R = N // 2 + N % 2 - 1
    # generate lookup tables
    lidxs = sorted(range(len(lft)), key = lft.__getitem__)
    ridxs = sorted(range(len(rgt)), key = rgt.__getitem__)
    l2r = [None] * len(rgt)
    r2l = [None] * len(lft)
    for lidx, ridx in zip(lidxs, ridxs):
        l2r[ridx] = lidx
        r2l[lidx] = ridx
    # left and right bits
    lbits = [None] * L
    rbits = [None] * R
    # counter for the remaining bits to be generated
    c = L + R
    # generate bits
    if N % 2 == 0:
        l = N - 1
        r = l2r[l]
        while True:
            lbits[r % K] = r // K == 0
            r = r + K if r // K == 0 else r - K
            l = r2l[r]
            c -= 1
            if l == K - 1:
                break
            rbits[l % K] = l // K == 1
            l = l + K if l // K == 0 else l - K
            r = l2r[l]
            c -= 1
    else:
        l = N - 1
        r = l2r[l]
        while True:
            if r == N - 1:
                break
            lbits[r % K] = r // K == 0
            r = r + K if r // K == 0 else r - K
            l = r2l[r]
            c -= 1
            rbits[l % K] = l // K == 1
            l = l + K if l // K == 0 else l - K
            r = l2r[l]
            c -= 1
    # generate remaining bits
    t = R - 1
    while c > 0:
        while rbits[t] is not None:
            t -= 1
        l = K + t
        r = l2r[l]
        while True:
            lbits[r % K] = r // K == 0
            r = r + K if r // K == 0 else r - K
            l = r2l[r]
            c -= 1
            rbits[l % K] = l // K == 1
            l = l + K if l // K == 0 else l - K
            r = l2r[l]
            c -= 1
            if l == K + t:
                break
    # apply swaps to the left and right inputs
    ulft, urgt = lft[:K], rgt[:K]
    dlft, drgt = lft[K:], rgt[K:]
    for i in range(L):
        if lbits[i]:
            ulft[i], dlft[i] = dlft[i], ulft[i]
    for i in range(R):
        if rbits[i]:
            urgt[i], drgt[i] = drgt[i], urgt[i]
    # generate bits for the upper and lower halves
    ubits = genbits(ulft, urgt)
    dbits = genbits(dlft, drgt)
    # concatenate and return the bits
    return lbits + ubits + dbits + rbits
def apply(src, net, bits):
    for bit, (i, j) in zip(bits, net):
        if bit:
            src[i], src[j] = src[j], src[i]
