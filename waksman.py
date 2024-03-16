def getperm(src, dst):
    srcidxs = sorted(range(len(src)), key = src.__getitem__)
    dstidxs = sorted(range(len(dst)), key = dst.__getitem__)
    res = [None] * len(src)
    for srcidx, dstidx in zip(srcidxs, dstidxs):
        res[dstidx] = srcidx
    return res
def genbits(i2o):
    n = len(i2o)
    if n == 1:
        return []
    if n == 2:
        return [i2o[0] != 0]
    o2i = [None] * n
    for i in range(n):
        o2i[i2o[i]] = i
    lbits = [None] * (n // 2)
    rbits = [None] * (n // 2 + n % 2 - 1)
    ui2o = [None] * (n // 2)
    di2o = [None] * (n // 2 + n % 2)
    c = n - 1
    if n % 2 == 0:
        i = n - 1
        o = i2o[i]
        while True:
            di2o[i // 2] = o // 2
            lbits[o // 2] = o % 2 == 0
            o = o + 1 if o % 2 == 0 else o - 1
            i = o2i[o]
            c -= 1
            ui2o[i // 2] = o // 2
            if i == n - 2:
                break
            rbits[i // 2] = i % 2 == 1
            i = i + 1 if i % 2 == 0 else i - 1
            o = i2o[i]
            c -= 1
    else:
        i = n - 1
        o = i2o[i]
        while True:
            di2o[i // 2] = o // 2
            if o == n - 1:
                break
            lbits[o // 2] = o % 2 == 0
            o = o + 1 if o % 2 == 0 else o - 1
            i = o2i[o]
            c -= 1
            ui2o[i // 2] = o // 2
            rbits[i // 2] = i % 2 == 1
            i = i + 1 if i % 2 == 0 else i - 1
            o = i2o[i]
            c -= 1
    t = len(rbits) - 1
    while c > 0:
        while rbits[t] is not None:
            t -= 1
        i = 2 * t
        o = i2o[i]
        while True:
            di2o[i // 2] = o // 2
            lbits[o // 2] = o % 2 == 0
            o = o + 1 if o % 2 == 0 else o - 1
            i = o2i[o]
            c -= 1
            ui2o[i // 2] = o // 2
            rbits[i // 2] = i % 2 == 1
            i = i + 1 if i % 2 == 0 else i - 1
            o = i2o[i]
            c -= 1
            if i == 2 * t:
                break
    ubits = genbits(ui2o)
    dbits = genbits(di2o)
    return lbits + ubits + dbits + rbits
def swap(list, bit, x, y):
    if bit:
        list[x], list[y] = list[y], list[x]
    return 1
def eval(list, bits, j = 0):
    n = len(list)
    if n == 1:
        return j
    if n == 2:
        j += swap(list, bits[j], 0, 1)
        return j
    for i in range(n // 2):
        j += swap(list, bits[j], 2 * i, 2 * i + 1)
    ulist = [None] * (n // 2)
    dlist = [None] * (n // 2 + n % 2)
    for i in range(n // 2):
        ulist[i] = list[2 * i]
        dlist[i] = list[2 * i + 1]
    if n % 2 == 1:
        dlist[-1] = list[-1]
    j = eval(ulist, bits, j)
    j = eval(dlist, bits, j)
    for i in range(n // 2):
        list[2 * i] = ulist[i]
        list[2 * i + 1] = dlist[i]
    if n % 2 == 1:
        list[-1] = dlist[-1]
    for i in range(n // 2 + n % 2 - 1):
        j += swap(list, bits[j], 2 * i, 2 * i + 1)
    return j
