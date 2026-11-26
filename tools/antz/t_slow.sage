load("tools/compare_magma.sage")
r = compare_group(13, 6, 5, magma=magma)[0]
print("@@SUMMARY slow: %s" % r)
print("@@DONE@@")
