load("tools/compare_magma.sage")
rb = []
for d in [-1, -2, -3, -7, -11]:
    F = QuadraticField(d, "a")
    rb.append(compare_arithgroup(F, (F(1), F(1)), F.ideal(1), magma=magma)[0])
print("@@SUMMARY bianchi: %s/%s agree" % (sum(rb), len(rb)))
print("@@DONE@@")
