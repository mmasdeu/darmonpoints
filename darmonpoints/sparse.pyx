from darmonpoints.util import update_progress

cimport cython


def compute_lift_sparse_cy(list big_system, list indeps, edge_to_eqs):
    cdef dict pivots = {}
    cdef int ncols = len(edge_to_eqs)
    cdef int nrows = len(big_system)
    cdef int niters = 0
    cdef int i = 0
    cdef int j = 0
    cdef int k = 0
    cdef int r = 0
    cdef int val = 0
    cdef int tmp = 0
    cdef int newval = 0
    cdef dict br0
    cdef int br1
    cdef int v

    for e01 in edge_to_eqs: # for each column...
        niters +=1
        update_progress(float(niters)/ncols,'Compute lift %s / %s'%(niters,ncols))
        # Find pivot row
        try:
            rws = [(r, len(big_system[r])) for r in edge_to_eqs[e01] if r not in pivots]
            r, _ = min(rws, key=lambda o:o[1])
        except (StopIteration, ValueError):
            continue
        try:
            tmp = big_system[r][e01]
            pivots[r] = e01
        except KeyError:
            continue
        assert tmp in [-1, 1]
        if tmp == -1:
            # rescale
            rw = big_system[r]
            indeps[r] = -indeps[r]
            for ky, v in rw.items():
                rw[ky] = -v
        for i in list(edge_to_eqs[e01]):
            if i == r:
                continue
            try:
                tmp = -big_system[i][e01]
            except KeyError:
                continue
            # add  (tmp * r) to (ith row)
            indeps[i] += tmp * indeps[r]
            for e01p, val in big_system[r].items() :
                newval = tmp * val
                if e01p in big_system[i] :
                    big_system[i][e01p] += newval
                    if big_system[i][e01p] == 0:
                        try:
                            edge_to_eqs[e01p].remove(int(i))
                        except ValueError:
                            pass
                        del big_system[i][e01p]
                else:
                    big_system[i][e01p] = newval
                    edge_to_eqs[e01p].append(int(i))
    ans = { e01 : int(0) for e01 in edge_to_eqs }
    for r, e01 in pivots.items():
        ans[e01] = indeps[r]
    return ans