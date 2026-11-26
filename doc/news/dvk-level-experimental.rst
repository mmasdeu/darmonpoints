**Added:**

* ``darmonpoints.arithgroup_io``: groups of rational quaternion algebras (``ArithGroup_rationalquaternion``) and the S-arithmetic groups over QQ built on them (``BigArithGroup_class``) can be exported to plain, JSON-compatible data (rationals as strings, reals as exact mantissa/exponent/precision, p-adic matrices as rational lifts) and rebuilt from it without Magma, with validation of the data (``StoredGroupMismatch``) and invariants to check a rebuilt group. Magma sessions of rebuilt groups are started lazily (``LazyMagma``); ``DARMONPOINTS_FORBID_MAGMA`` makes them raise instead.
* ``ArithGroup_rationalquaternion(..., stored_data=...)`` and ``BigArithGroup_class(..., padic_splitting=..., BT_reps=..., wp=...)`` to build groups from stored data (a stored p-adic splitting is Hensel-lifted when more precision is needed).
* Compiled kernel ``darmonpoints.sparse_padic`` (Cython and GMP) for the products with sparse integer matrices whose columns are only needed modulo powers of p, used by the Up iteration of the additive Darmon-Vonk lift. It only needs a C compiler and GMP; if it cannot be built, the installation continues and the pure python products are used, with the same results. ``DARMONPOINTS_INTEGER_MODE=python`` disables it at run time.
* ``meromorphic.LogSeriesOperator`` and ``meromorphic._IntegerOperator``: Up of the additive Darmon-Vonk lift as one integer matrix with precision tracking (from the refactor of ``theta_additive``; the names that moved from it are still importable from it).
* ``ArithCohOverconvergent.up_operator``: Up of the overconvergent quaternionic lift as one integer matrix modulo p^N, built once per cohomology group and shared by both signs at infinity.
* ``ArithCohElement.evaluate_many``: evaluation of a cocycle at many pairs with low memory.
* ``BigArithGroup_class.embedding_precision`` and ``util.discriminant_conductor``.

**Changed:**

* An integer D now stands for the quadratic order of discriminant D when D = d_K f^2 is one, and for the maximal order of Q(sqrt D) otherwise: ``prime_list_candidates`` and ``construct_conjectural_field`` take the conductor f into account. ``ArithGroup_rationalquaternion.embed_order`` accepts optimal embeddings of non-maximal orders; ``compute_quadratic_embedding`` raises ``NotImplementedError`` for f > 1 instead of silently embedding the maximal order. Fundamental discriminants and radicands give the same results as before.
* ``ArithCohOverconvergent.apply_Up`` uses ``up_operator`` when called with the default representatives (same results).
* ``integrate_H1`` pairs the divisor with the moments through power sums of the points instead of building the series of ``log(1 - x z)``, and keeps the values of the cocycle at the pairs it needs with the cocycle (same values).
* ``OCVn`` builds the matrices of the action on the moments with an integer recurrence modulo p^N (same matrices), and ``acting_matrix`` returns the cached immutable matrix instead of a copy.
* ``OneChainsElement.zero_degree_equivalent`` only builds the 1-boundaries when they are returned (``return_boundary=True``); the chain is unchanged.
* The points of divisors over unramified extensions of Qp are hashed by their value and precision instead of their printed form.
* ``setup.py`` lists the extensions explicitly; GMP is looked for in ``$GMP_PREFIX``, ``$SAGE_LOCAL`` and the prefix of the python environment.

**Deprecated:**

* <news item>

**Removed:**

* <news item>

**Fixed:**

* The overconvergent quaternionic lift computed its moments with 200-digit matrices when nothing had raised the precision of the embedding before it (``ArithGroupElement.matrix`` cached ``embed(-1)`` at the precision of its first call), so lifts above precision 200 were silently wrong beyond p^200. ``get_overconvergent_class_quaternionic`` now also raises the precision of the embedding to its working precision.
* ``get_hecke_reps`` and ``get_hecke_data`` were cached ignoring ``use_magma``, ``g0`` and ``hecke_reps``; ``OneChainsElement.act_by_hecke`` passes its Hecke representatives on to ``get_hecke_ti``.
* Groups reloaded with the legacy ``filename=`` path rebuild ``translate_inv`` (the word problem of a reloaded group failed).

**Performance:**

* Additive Darmon-Vonk lift: faster evaluation at cycles (power sums of the moved points), one Up operator shared by all embeddings, and much lower memory (e.g. 64 GB to 5.5 GB peak for p = 3, D = 14, N = 5 at precision 200); with the compiled kernel the lift is about 10 times faster.
* Quaternionic Darmon points: Up as one integer operator (one Up step 50-70 times faster), integer power matrices (27-64 times faster at 101-301 moments), divisor points hashed by value, ``zero_degree_equivalent`` without duplicated work, integration by power sums with cached cocycle values, and lower memory (each word-prefix matrix kept only until its last use). For example, for the curve 30a1 at precision 230 the lift goes from about 1150 s to about 65 s; for p = 7, D = 6, N = 5 at precision 100 a homology cycle goes from 105 s to 20 s and an integration from 336 s to 69 s.
