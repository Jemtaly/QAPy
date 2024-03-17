def network(n, j = 0):
    if n <= 1:
        return []
    k = n // 2
    lbitn = n // 2
    rbitn = n // 2 + n % 2 - 1
    net = []
    for i in range(lbitn):
        net.append((j + i, j + i + k))
    net += network(k, j)
    net += network(n - k, j + k)
    for i in range(rbitn):
        net.append((j + i, j + i + k))
    return net
def genbits(lft, rgt):
    n = min(len(lft), len(rgt))
    if n <= 1:
        return []
    k = n // 2
    lbitn = n // 2
    rbitn = n // 2 + n % 2 - 1
    # generate lookup tables
    ls = sorted(range(n), key = lft.__getitem__)
    rs = sorted(range(n), key = rgt.__getitem__)
    l2r = [None] * n
    r2l = [None] * n
    for l, r in zip(ls, rs):
        l2r[r] = l
        r2l[l] = r
    # left and right bits
    lbits = [None] * lbitn
    rbits = [None] * rbitn
    # generate bits
    if n % 2 == 0:
        l = n - 1
        r = l2r[l]
        while True:
            lbits[r % k] = r // k == 0
            r = r + k if r // k == 0 else r - k
            l = r2l[r]
            if l == k - 1:
                break
            rbits[l % k] = l // k == 1
            l = l + k if l // k == 0 else l - k
            r = l2r[l]
    else:
        l = n - 1
        r = l2r[l]
        while True:
            if r == n - 1:
                break
            lbits[r % k] = r // k == 0
            r = r + k if r // k == 0 else r - k
            l = r2l[r]
            rbits[l % k] = l // k == 1
            l = l + k if l // k == 0 else l - k
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
            lbits[r % k] = r // k == 0
            r = r + k if r // k == 0 else r - k
            l = r2l[r]
            rbits[l % k] = l // k == 1
            l = l + k if l // k == 0 else l - k
            r = l2r[l]
            if l == i + k:
                break
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
def apply(src, net, bits):
    for bit, (i, j) in zip(bits, net):
        if bit:
            src[i], src[j] = src[j], src[i]
if __name__ == '__main__':
    import random
    for _ in range(1000):
        n = random.randrange(1000, 10000)
        net = network(n)
        src = [random.randrange(n * n) for _ in range(n)]
        dst = src.copy()
        random.shuffle(dst)
        bits = genbits(src, dst)
        apply(src, net, bits)
        assert src == dst
        print(n, 'OK')
