load("tools/compare_magma.sage")
F = QuadraticField(5, "r"); r = F.gen()
ab = quaternion_algebra_invariants_from_ramification(F, F.ideal(3), F.real_places()[:1])
same, RES = compare_group(F.ideal(3 / 2 * r + 1 / 2), ab, F.ideal(1), base=F, magma=magma)
for b in RES:
    if "group" in RES[b]:
        GG = RES[b]["group"]
        print(b, "Gpn gens nrd:", [g.quaternion_rep.reduced_norm() for g in GG.Gpn.gens()])
        print(b, "Gn gens nrd:", [g.quaternion_rep.reduced_norm() for g in GG.Gn.gens()])
print("@@DONE@@")
