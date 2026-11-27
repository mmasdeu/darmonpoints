**Added:**

* PARI backend for quaternion algebras, orders and fundamental domains, replacing Magma: Rickards' algorithm for arithmetic Fuchsian groups (vendored in ``darmonpoints/fdom``, wrapped in ``afuch.pyx``) and a Python port of Page's algorithm for Kleinian groups (``kleinian.py``).
* Fast C (FLINT) computation of the matrices of the action on moments (``moments.pyx``).
* Integer arithmetic for the Darmon-Vonk iteration of ``U_p`` (``MeromorphicIntegerArithmetic``).

**Changed:**

* Magma is no longer needed: it is only used if a Magma session is passed explicitly.
* The package now compiles C extensions at install time (``pip install --no-build-isolation .``).
* ``darmon_point`` now returns, for a given curve, the point ``P`` or ``-P`` up to torsion (the sign of the period depends on the backend).

**Fixed:**

* Number field ``_is_in_order`` accepted elements that are not in the order.
* ``P1NFList`` looked up M-symbols with bisect on an unsorted list.
* Hecke operators for ``SL2`` and totally real fields of degree greater than 1 were not deterministic.
* CI workflows: Mambaforge no longer exists, ``build`` was renamed ``python-build`` on conda-forge.

**Performance:**

* Darmon points are 4-10 times faster (``U_p`` through a precomputed matrix, faster point recognition and searches for elements of given norm).
* Plectic points: Atkin-Lehner elements and cocycles with trivial action are computed much faster.
