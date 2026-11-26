# Debug the "ti not found" failure of the Magma backend over QQ(sqrt5).
import time
from darmonpoints.sarithgroup import BigArithGroup
from darmonpoints.cohomology_arithmetic import ArithCoh
F = QuadraticField(5, "r"); r = F.gen()
ab = (1/2*r + 1/2, F(-3))
P = F.ideal(3/2*r + 1/2)
ell = 3/2*r - 1/2
def diag(G, label):
    GG = ArithCoh(G).group()
    print(label, "group is", "Gpn" if GG is G.Gpn else "Gn", flush=True)
    print(label, "gens nrd:", [g.quaternion_rep.reduced_norm() for g in GG.gens()], flush=True)
    g0 = GG.element_of_norm(ell, force_sign=True)
    print(label, "g0 nrd:", g0.reduced_norm(), "in order:", GG._is_in_order(g0), flush=True)
    reps = GG.get_hecke_reps(ell, g0=g0)
    dup = [(a, b) for a in range(len(reps)) for b in range(a + 1, len(reps)) if GG._is_in_order(reps[a]**-1 * reps[b])]
    print(label, "#reps", len(reps), "nrds", set(o.reduced_norm() for o in reps), "duplicates", dup, flush=True)
    bad = []
    for gamma in GG.gens():
        q = gamma.quaternion_rep
        for g in reps:
            if not any(GG._is_in_order(g**-1 * q * h) for h in reps):
                bad.append((g, q))
    print(label, "failing pairs:", len(bad), "of", len(reps) * len(GG.gens()), flush=True)
    for g, q in bad[:3]:
        print("   g nrd", g.reduced_norm(), "gamma", q, "nrd", q.reduced_norm(), "gamma in order", GG._is_in_order(q), flush=True)

t = time.time()
G = BigArithGroup(P, ab, F.ideal(1), base=F, use_shapiro=False, outfile="/dev/null", magma=magma, backend="magma")
print("magma group built in %.1f" % (time.time() - t), flush=True)
diag(G, "[magma]")
# Same with the old (no-op) _fix_sign
from darmonpoints.arithgroup import ArithGroup_fuchsian_generic
ArithGroup_fuchsian_generic._fix_sign = lambda self, x, N: x
G2 = BigArithGroup(P, ab, F.ideal(1), base=F, use_shapiro=False, outfile="/dev/null", magma=magma, backend="magma")
diag(G2, "[magma, old fix_sign]")
print("@@DONE@@")
