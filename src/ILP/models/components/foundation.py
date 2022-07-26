from unicodedata import name


# def cumulative(s, d, r, c):
#     cnst_list = []
#     names = []
#     rhs = []
#     for u, i in zip(d, range(len(d))):
#         cu = [1 if s[i] < u < (s[i]+d[i]) else 0 for i in range(len(s))]
#         cnst_list.append(cu)
#         names.append(f'cumulative{i}')
#         rhs.append(c)
#     return cnst_list, rhs, names


def diffn_helper(c1, c2, k, size, CIRCUITS, n_circuits, axis=0):
    cffx = [0.0 for _ in CIRCUITS] 
    cffy = [0.0 for _ in CIRCUITS]
    cffd = [0.0 for i in CIRCUITS for _ in range(i+1, n_circuits) for _ in range(0, 4)]

    ### FIXME: not working bad computation of d indexes 
    idx = k + sum([(n_circuits - 1 - j)*4 for j in range(0, c1)])

    if axis == 0:
        cffx[c1] = 1.0
        cffx[c2] = -1.0
        cffd[idx] = -1.0
    elif axis == 1:
        cffy[c1] = 1.0
        cffy[c2] = -1.0
        cffd[idx] = -1.0
    else:
        raise Exception("axis must be 0 for x or 1 for y")
    
    return cffx + cffy + cffd, 1.0 - size


def diffn_or_helper(c1, c2, CIRCUITS, n_circuits):
    cffx = [0.0 for _ in CIRCUITS] 
    cffy = [0.0 for _ in CIRCUITS]
    cffd = [0.0 for i in CIRCUITS for _ in range(i+1, n_circuits) for _ in range(0, 4)]

    idx = sum([(n_circuits - j - 1)*4 for j in range(0, c1)])
    print('--->', idx, flush=True)

    cffd[idx]     = 1.0
    cffd[idx + 1] = 1.0
    cffd[idx + 2] = 1.0
    cffd[idx + 3] = 1.0

    return cffx + cffy + cffd, 1.0