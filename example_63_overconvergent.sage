# # The plectic point of the curve 63.2-d1 over Q(sqrt(37)), with overconvergent cohomology
#
# This is the example of [FGM] (the curve of Section 7, beta = -21*w + 62),
# which was computed there to 7 digits by Riemann sums (see
# example_63_depth7.sage). Here the same group and the same class are used,
# but the measure is obtained from the overconvergent lift of the class to
# two-variable distributions, and the integral is a finite sum of moments.
#
# HOW TO RUN: Magma only works from the Sage REPL (the global ``magma`` is
# defined in ~/.sage/init.sage), so start the REPL of the conda environment
# darmonpoints-dev in this directory and type
#
#     sage: load("example_63_overconvergent.sage")
#
# Do not use ``from sage.all import *``, and do not run this file as a script.
#
# COST: the Magma part (Steps 2-3) took between 25 and 45 minutes, as in the
# Riemann sum computation. Step 4 (the lift) and Step 5 (the integral) take a
# few minutes for PREC = 6; PREC = 13 takes a few hours and gives 10 digits.

import time
from darmonpoints.plectic import *
from darmonpoints.plectic import get_overconvergent_class_plectic, plectic_integral
from darmonpoints.cohomology_arithmetic import ArithCoh, get_cocycle_from_elliptic_curve
from darmonpoints.util import quaternion_algebra_invariants_from_ramification

PREC = 13   # number of moments: the result is correct to about PREC - 3 digits
SEED = 271828   # for Magma: the running time depends on its random choices

# ## Step 1. The curve and the primes (as in example_63_depth7.sage)
x = polygen(QQ, 'x')
F = NumberField(x^2 - x - 9, 'w'); w = F.gen()
r = 2 * w - 1
assert r^2 == 37
E = EllipticCurve([1, 1/2 * r + 1/2, 1, 1/2 * r + 3/2, 2])
N = E.conductor()
p = 3
P1 = F.ideal(w - 3)
P2 = F.ideal(w + 2)
DB = N / (P1 * P2)
assert DB.norm() == 7
# E has split multiplicative reduction at P1 and non-split at P2, so that
# U_P1 U_P2 acts on the class of E as 1 * (-1) = -1.
red_types = [E.local_data(P).bad_reduction_type() for P in (P1, P2)]
assert red_types == [1, -1]
sign_ap = prod(red_types)

# ## Step 2. The plectic group (needs Magma)
t0 = cputime(); wt0 = walltime()
magma.eval('SetSeed(%s)' % SEED)
ramification_at_infinity = [0]
abtuple = quaternion_algebra_invariants_from_ramification(F, DB, ramification_at_infinity, optimize_through_magma=True, magma=magma)
set_verbose(1)
G = PlecticGroup(P1, P2, abtuple, 1, base=F, grouptype='PGL2', magma=magma)

# ## Step 3. The class of E in H^1(Gamma_S, Z) and the cycle
Coh = ArithCoh(G, trivial_action=True)
phiE = get_cocycle_from_elliptic_curve(Coh, E, sign=1)
beta = -21 * w + 62   # E_beta = F(sqrt(beta)), the field of the cycle
gammaquatrep, tau0, tau1 = get_cycle(G, beta, 10)
print('Magma part: %.0f s' % (walltime() - wt0))
set_verbose(0)

# ## Step 4. The overconvergent lift (no Magma)
# Applying U_P1 U_P2 repeatedly to phiE, viewed as a distribution of total mass
# phiE, gains one p-adic digit at each step.
wt0 = walltime()
Phi = get_overconvergent_class_plectic(G, phiE, PREC, sign_ap=sign_ap)
print('lift with %s moments: %.0f s' % (PREC, walltime() - wt0))

# ## Step 5. The integral
# Phi is not a harmonic measure, so X_1 X_2 cannot be integrated against it
# directly. Instead we integrate the function
#     F = X_1 X_2 - C_2/(2 C_1) X_1^2 - C_1/(2 C_2) X_2^2,    X_i o h = X_i + C_i,
# which differs from X_1 X_2 by functions of one variable and is invariant
# under h = u^(p+1): coboundaries then integrate to zero, and the integral only
# depends on the class of Phi. It is the sum over the (p+1)^2 residue polydiscs
# D_e of the integrals of F against the values Phi(g_e), g_e = gamma_e^-1 h gamma_e
# (the cycle and its fixed points are first conjugated by w_p, as in do_twist).
wt0 = walltime()
kL = plectic_integral(G, Phi, gammaquatrep, prec=60, M=PREC)
print('integral: %.0f s' % (walltime() - wt0))
print('k L =', kL)

# ## Step 6. Comparison with [FGM]
# Since h = u^(p+1), the integral is k L with k = p + 1, and L is the value of
# the plectic invariant, which is detsym_scaled (the value in the paper is
# -L modulo 3^10, up to the sign convention of the orientation of the cycle).
k = p + 1
L = kL / k
detsym_scaled = 3^2 + 2*3^3 + 2*3^4 + 2*3^5 + 3^6 + 2*3^8 + 3^9 + 2*3^10 + 3^11 + 3^12 + 3^13 + 2*3^15 + 2*3^17 + 2*3^18 + 2*3^20 + O(3^21)
minus_detsym_scaled = 2*3^2 + 3^6 + 2*3^7 + 3^9 + O(3^10)   # the value of [FGM]
print('L                  =', L)
print('detsym_scaled      =', detsym_scaled)
agreement = max((L - detsym_scaled).valuation(), (L + detsym_scaled).valuation())
print('L agrees with +-detsym_scaled modulo 3^%s, that is, to %s digits' % (agreement, agreement - 2))
