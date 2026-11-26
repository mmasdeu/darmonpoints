import time
import darmonpoints.sarithgroup as SA
orig_wp = SA.BigArithGroup_class.wp
def wp_debug(self, **kwargs):
    t = time.time()
    if getattr(self.Gpn, "_backend", "magma") != "pari":
        print("magma backend: brute force wp search", flush=True)
        ans = orig_wp(self, **kwargs)
        print("magma wp found in %.1f s, nrd = %s" % (time.time() - t, ans.reduced_norm()), flush=True)
        return ans
    QA = self.Gpn._QA
    print("split place idx", QA.split_real_place_index(), "pgen", self.ideal_p.gens_reduced()[0], flush=True)
    w = QA.normalizer_element_of_norm(self.Gpn._O_mat, self.ideal_p.gens_reduced()[0], timeout=300)
    print("AL candidate", w, "time %.2f" % (time.time() - t), flush=True)
    if w is not None:
        try:
            self.set_wp(w)
            print("set_wp OK", flush=True)
        except TypeError as e:
            print("set_wp REJECTED", e, flush=True)
    return orig_wp(self, **kwargs)
SA.BigArithGroup_class.wp = wp_debug
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
