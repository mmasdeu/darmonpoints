# Seed sweep for the "ti not found" failure (PARI backend only).
# Usage inside Sage: SEED0, SEED1 = a, b; load("tools/antz/t_tisweep.sage")
import time
from darmonpoints.sarithgroup import BigArithGroup
from darmonpoints.cohomology_arithmetic import ArithCoh
from darmonpoints.util import quaternion_algebra_invariants_from_ramification
F = QuadraticField(5, "r"); r = F.gen()
ab = quaternion_algebra_invariants_from_ramification(F, F.ideal(3), F.real_places()[:1])
p = F.ideal(3/2*r + 1/2)
Pbad = F.ideal(p) * QuaternionAlgebra(F, *ab).discriminant()
primes = [P.gens_reduced()[0] for P in F.primes_of_degree_one_list(12) if P.is_coprime(Pbad) and P.is_principal()][:3]
for seed in range(SEED0, SEED1):
    set_random_seed(seed)
    G = BigArithGroup(p, ab, F.ideal(1), base=F, use_shapiro=False, outfile="/dev/null", backend="pari")
    H = ArithCoh(G)
    GG = H.group()
    for l in primes:
        try:
            M = H.hecke_matrix(l)
            print("@@SEED", seed, l, "ok", M.charpoly(), flush=True)
        except RuntimeError as e:
            print("@@SEED", seed, l, "FAIL", flush=True)
            reps = GG.get_hecke_reps(l)
            print("  #reps", len(reps), "norms", set(o.reduced_norm() for o in reps))
            dup = [(a, b) for a in range(len(reps)) for b in range(a + 1, len(reps)) if GG._is_in_order(reps[a]**-1 * reps[b])]
            print("  duplicate cosets", dup)
            for gamma in GG.gens():
                for g in reps:
                    if not any(GG._is_in_order(g**-1 * gamma.quaternion_rep * h) for h in reps):
                        print("  failing g =", g, "gamma =", gamma.quaternion_rep, "gamma in order", GG._is_in_order(gamma.quaternion_rep), "nrd", gamma.quaternion_rep.reduced_norm())
            save((seed, l, reps, [g.quaternion_rep for g in GG.gens()]), "logs/tifail_%s" % seed)
            break
print("@@DONE@@")
