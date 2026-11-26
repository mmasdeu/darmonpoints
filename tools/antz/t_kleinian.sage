load("tools/compare_magma.sage")
rk = compare_kleinian(magma)
print("@@SUMMARY kleinian: %s/%s agree" % (sum(rk), len(rk)))
print("@@DONE@@")
