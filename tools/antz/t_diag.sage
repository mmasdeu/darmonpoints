import time
from darmonpoints.sarithgroup import BigArithGroup
from darmonpoints.util import quaternion_algebra_invariants_from_ramification
F = QuadraticField(5, "r"); r = F.gen()
ab = quaternion_algebra_invariants_from_ramification(F, F.ideal(3), F.real_places()[:1])
print("ab", ab, flush=True)
P = F.ideal(3/2*r + 1/2)
import darmonpoints.sarithgroup as SA
orig_wp = SA.BigArithGroup_class.wp
def wp_debug(self, **kwargs):
    t = time.time()
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
t = time.time()
G = BigArithGroup(P, ab, F.ideal(1), base=F, use_shapiro=False, outfile="/dev/null", backend="pari")
print("built in %.1f" % (time.time() - t), flush=True)
print("@@DONE@@")
