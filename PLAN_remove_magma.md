# Plan: removing the Magma dependency from darmonpoints

Goal: replace every Magma call by Sage + PARI (cypari2), reimplementing what PARI
does not provide. Magma stays available only as an optional comparison backend
until the end, and (temporarily) for Kleinian groups.

## Inventory of Magma usage

| # | What | Magma calls | Where | Replacement |
|---|------|-------------|-------|-------------|
| A1 | Algebra with prescribed ramification | `QuaternionAlgebra(I, places)` | `util.quaternion_algebra_invariants_from_ramification` | PARI `alginit` / existing Sage path |
| A2 | Maximal / Eichler orders, intersections, discriminants | `MaximalOrder`, `Order(Omax,N)`, `meet`, `Discriminant`, `ZBasis` | `_init_magma_objects` (QQ & nf), `arithgroup_generic._get_O_basis` | PARI `alginit` + own Eichler code |
| A3 | p-adic splitting adapted to the order | `pMatrixRing` | `arithgroup_generic._compute_padic_splitting` | own (core routine) |
| A4 | Archimedean splitting | `FuchsianMatrixRepresentation` | `_splitting_at_infinity` | closed formula |
| A5 | Element of given norm (Hecke, `wp`) | `ElementOfNorm` | `element_of_norm` (QQ & nf) | principalization by lattice enumeration |
| A6 | Optimal embedding of quadratic order | `Embed` | `compute_quadratic_embedding` (QQ & nf) | conic solving + principalization |
| G1 | Fuchsian groups (Voight): domain, presentation, side pairings, word problem | `FuchsianGroup`, `Group`, `ShimGroupSidepairs*`, `ShimFDArgs`, `WordProblem` | `ArithGroup_rationalquaternion`, `ArithGroup_nf_fuchsian`, `mixed_extension.get_word_rep_fast` | Rickards' PARI/C library + own Cython reduction |
| G2 | Kleinian groups (Page, ~3.9k lines Magma) | `NormalizedBasis`, `Presentation`, `ReduceGenerators`, `InfinitePlaces` | `ArithGroup_nf_kleinian`, `ArithGroup_nf_matrix*` | port (last phase) |
| L1 | Reduced binary quadratic forms | `ReducedForms` | `limits.find_optimal_embeddings` | `BinaryQF_reduced_representatives` |
| L2 | Ring class fields | `RayClassGroup` + `AbelianExtension` | `darmonvonk` | PARI `bnrclassfield(bnr,,2)` |
| L3 | Embeddability of K in B | `HasEmbedding` | `darmonvonk.admissible_discriminants` | local criterion |
| L4 | Kernel LLL | `KernelMatrix().LLL()` | `util` (`algorithm='magma'`) | drop option |

PARI 2.17.4 (shipped with Sage) has `alginit` (maximal order), `algbasis`,
`algnorm`, `algtrace`, `alglatinter`, `alglatadd`, `algramifiedplaces`,
`alghasse`, `qfminim`, `qfsolve` (QQ only), `rnfisnorm`, `bnrclassfield`.
It lacks Eichler orders (`algeichlerbasis` is only in 2.19-dev), elements of
given norm, optimal embeddings and Rickards' fundamental domains. The bundled
`Fdoms/libfdom.so` links against `libpari .so.7` and does not load with 2.17.

## Architecture

New `darmonpoints/quatorder.py` with a class `QuaternionOrderData` replacing
`_B_magma/_Omax_magma/_O_magma/_F_magma`:

- `F`, Sage `B = (a,b)`, PARI `alginit` object, Z-basis of Omax in (1,i,j,k);
- level `N`, Z-basis of `O` (replaces `_get_O_basis`, `_get_basis_invmat`);
- `local_splitting(P, prec)`, `eichler_suborder(N)`, `intersect(other)`,
  `discriminant()`, `element_of_norm(N, ...)`, `principal_generator(I)`,
  `optimal_embedding(D, conductor)`.

`info_magma` becomes `info` (shares Omax and parent order). Config option
`backend = 'pari' | 'magma'`; a thin Magma backend implementing the same
interface is kept for comparisons until cleanup.

Invariant to preserve: Gpn's order is built as `{x in O_n : iota_p(x) upper
triangular mod p}` with the *same* `iota_p` as `BigArithGroup.get_embedding`,
so the Bruhat-Tits code (`get_BT_reps`, `is_in_Gamma0loc`) stays consistent.

## Algorithms

- **Adapted local splitting (A3)**: any splitting of `B ⊗ F_P` (zero divisor
  mod P + `lift_padic_splitting`); the image of Omax is `End(Λ)`; find `Λ` by
  HNF and conjugate so that `ι(Omax) = M_2(O_P)`. Work modulo `P^e`.
- **Eichler orders (A2)**: for each `P^e || N`, kernel of
  `Omax → O_F/P^e`, `x ↦ ι_P(x)[1,0]`; HNF sublattice. Intersections are
  lattice intersections. Discriminant/level only in asserts (via index).
- **Archimedean splitting (A4)**: at the split real place one of `a,b` is
  positive; `i ↦ diag(√a,-√a)`, `j ↦ [[0,1],[b,0]]` (or swapped).
- **Principalization (A5/A6)**: for a left ideal `I`, find `x ∈ I` with
  `|N_{F/Q}(nrd x)| = N(nrd I)` by `qfminim` on the 4n-dim Z-lattice with a
  positive-definite majorant (Voight's absolute reduced norm; Page's analogue
  for Kleinian).
  - element of norm `n`: `I = O ∩ ι_p^{-1}(first row ≡ 0 mod p^k)`, then
    principalize; `_fix_sign` as now.
  - optimal embedding: find `φ: K → B` (solve `a x1² + b x2² − ab x3² = D`:
    `qfsolve` over QQ; over nf via two conics and `Conic(F,...).rational_point()`),
    then principalize `I = O·φ(O_K) = Oα`; `α φ α^{-1}` lands in `O`.
- **Fuchsian groups (G1)**: vendor Rickards' C library (GPL-3), compile as a
  Cython extension against Sage's libpari via cypari2. Use it for the domain,
  presentation and side pairings. Rewrite the word problem in Cython
  (isometric-circle reduction with exact side-pairing quaternions), aligning
  embeddings by a conjugating real matrix. Populate `Ugens`,
  `_relation_words`, `_fundamental_domain`, `translate`.
- **Kleinian groups (G2)**: first ship everything else Magma-free with Magma
  optional only for fields with a complex place; then port Page's algorithm.

## Phases and validation

Comparisons are run in the Sage REPL (Magma does not initialize from
`sage -c`) with a script `darmonpoints/tests/compare_magma.sage` that builds
the same group with both backends and compares invariants (never bases or
words).

| Phase | Content | Checks vs Magma |
|-------|---------|-----------------|
| 0 | backend layer + comparison script | identical results with `backend='magma'` |
| 1 | L1–L4, A1, A4 | equal form lists, isomorphic class fields, same `HasEmbedding` |
| 2 | A2, A3 | `disc(Omax)=D`, `disc(O)=D·N`, `O_pn ⊂ O_n`, `ι(i)²=a`, `ι(O) ⊆ M_2(O_P)` upper-triangular mod level; over QQ also vs Sage `maximal_order()`/`order_with_level()` |
| 3 | A5, A6 | output in `O` with correct nrd/trd; Hecke charpolys of `ArithCoh(G).hecke_matrix(ℓ)` equal |
| 4 | G1 | signature, covolume vs `util.covolume`, abelianization, Hecke charpolys for ~10 primes, `get_word_rep(g)` multiplies back; magma-marked doctests reproduce points/curves |
| 5 | cleanup | drop `# optional - magma` for QQ/totally real, seeds via `set_random_seed`/`setrand`, deprecate `magma=` argument, CI runs |
| 6 | G2 | as phase 4 for mixed-signature fields |

Test cases: QQ with D = 6, 10, 15, 22 and levels 1, 5, 7, 35; QQ(√5),
QQ(√13) with B ramified at one real place plus primes; one cubic field;
QQ(∛2) for phase 6.

## Risks

- Rickards' library must build against PARI 2.17.4 (checked first).
- Principalization can fail with non-trivial narrow class group (same
  limitation as Magma's `ElementOfNorm`).
- Precision: keep 800–1000 bits in the new word problem.

## Status

- [x] Phase 0: `backend='pari'|'magma'` keyword (default: `pari` unless a
  Magma session is passed); `tools/compare_magma.sage` for REPL comparisons.
- [x] Phase 1: L1 (`BinaryQF_reduced_representatives`), L2
  (`util.ray_class_field_polynomial` via `bnrclassfield`), L3
  (`util.quadratic_field_embeds_in_quaternion_algebra`), A1 (PARI `alginit`
  with local invariants + `algab`; now the default), A4. L4 untouched (only
  used when `algorithm='magma'` is requested explicitly).
- [x] Phase 2: `darmonpoints/quatorder.py` (`QuaternionAlgebraPari`):
  maximal order from `alginit`, Eichler orders with Aurel Page's GP code
  (vendored in `fdom/eichler.gp`), adapted p-adic splittings.
- [x] Phase 3: elements of given norm and quadratic embeddings by
  enumeration (`qfminim`) with a positive-definite majorant;
  `wp` from Rickards' `afuchfindoneelt` (Atkin-Lehner element).
- [x] Phase 4: Rickards' library vendored in `darmonpoints/fdom`
  (commit 79a12d3, plus `fdom_compat.h` for PARI < 2.18) and wrapped in
  `darmonpoints/afuch.pyx`. Change w.r.t. the plan: the word problem uses
  `afuchword` (C) directly instead of a new Cython reduction;
  `find_fundom_rep` reduces towards the centre of the Dirichlet domain.
- [x] Phase 5 (see the log below): all `# optional - magma` tags removed, Magma never started automatically, stale `Fdoms/` and dead helpers removed, CI/README/docs updated.
- [x] Phase 6 (see the log below): `darmonpoints/kleinian.py` (port of Page's KleinianGroups) used by `ArithGroup_nf_kleinian`; Darmon points and `find_curve` over fields with a complex place work without Magma.

Validated so far (without Magma): signatures and areas for many QQ and
QQ(sqrt5) orders; Hecke charpolys of the doctests in `cohomology_abstract`
(disc 6, p = 5) and `cohomology_arithmetic` (QQ(sqrt5)); `find_curve(5,6,30,20)`
returns the documented curve; `darmon_point(13, 78a1, 5, 20)` returns
`-14 * (22 : 48*alpha - 11 : 1)` (documented: `(22 : 48*alpha - 11 : 1)`;
the period corresponds to `±4 * P0`, the scalar comes from `recognize_J`).

Known weak spots: `element_with_minpoly` / `elements_of_norm` give up only
after many enlargements when no element exists (up to ~60 s); element of
norm over number fields takes a few seconds.

## Progress log

### 2026-11-25: Phases 0-4

See the status list above.

### 2026-11-26: comparison with Magma, Phases 5 and 6

**How the comparisons are run.** Magma only initializes inside an
interactive Sage REPL, so the REPL
(`~/miniforge3/envs/darmonpoints-dev/bin/sage --simple-prompt`) is driven
through a pseudo-terminal with `pexpect`, sending
`load("tools/compare_magma.sage")` and one comparison per cell
(Magma V2.24-3). Never `from sage.all import *` in a script.

**Comparison table (`tools/compare_magma.sage`, `compare_group`).** For each
`BigArithGroup(p, D, N)` built with both backends we compare the
abelianizations of `Gn` and `Gpn`, the characteristic polynomials of the
Hecke operators on `ArithCoh(G)` for four primes, and check that the local
splitting maps the order of `Gpn` into Eichler matrices.

| p | D | N | base | ab(Gn) | ab(Gpn) | Hecke charpolys | time pari / magma |
|---|---|---|------|--------|---------|-----------------|-------------------|
| 5 | 6 | 1 | QQ | (2, 6) equal | (2,2,2,2,0,0) equal | T7, T11, T13, T17 equal | 0.9 s / 6.5 s |
| 7 | 6 | 1 | QQ | (2, 6) equal | (3,3,6,0,0) equal | T5, T11, T13, T17 equal | 0.7 s / 8.7 s |
| 3 | 10 | 1 | QQ | (3,3,6) equal | (3,3,6,0,0) equal | T7, T11, T13, T17 equal | 5.3 s / 32.8 s |
| 3 | 22 | 1 | QQ | (3,6,6) equal | (3,3,6,0^6) equal | T5, T7, T13, T17 equal (3 newforms) | 7.8 s / 86.9 s |

(The first attempt used `p = 5, D = 10`, which is invalid since `p | D`; it
was replaced by `p = 3`.)

**Phase 5 so far.**

- All `# optional - magma` doctest tags removed (`magma=Magma()` arguments
  and `SetSeed` calls dropped from the examples).
- Removed the stale `darmonpoints/Fdoms/` (prebuilt `libfdom.so` linked to an
  old libpari) and the dead helpers `_get_O_pari`,
  `pari_ordmax_basis_to_sage`, `sage_order_basis_to_pari`; `MANIFEST.in`
  now ships `darmonpoints/fdom`.
- CI: `pip install --no-build-isolation` (the extension cimports cypari2 and
  needs the PARI headers of the conda env); `cython` added to
  `environment.yml`.
- README: Magma is optional; `config.ini` comments updated.
- `BigArithGroup`, `darmon_point`, `find_curve` never start Magma by
  themselves; Magma is used only when a session is passed.

**Phase 6 so far.** `darmonpoints/kleinian.py`: Python port of Page's
*KleinianGroups* (NormalizedBasis with "SmallBalls" enumeration and
"Reduction" pairing; NormOne and Units groups; non-maximal orders through the
coset enumeration `myIndex`; exterior domains, polyhedron volumes via the
Lobachevsky function, Presentation from edge cycles). Reals are `gmpy2.mpfr`
(default 60 digits), lattice enumeration is PARI's `qfminim`, and the
presentation is simplified with GAP (`IsomorphismSimplifiedFpGroup`, in place
of Magma's `ReduceGenerators`). `ArithGroup_nf_kleinian` uses it with the
PARI backend; the matrices, centres and radii it produces feed the existing
Python word problem (`get_word_rep`). `QuaternionAlgebraPari` gained a
majorant at complex places (elements of given norm for Kleinian orders).

First results: QQ(sqrt -7), B ramified at the two primes above 2, maximal
order: 16 faces, Vol/Covol = 1 - 5e-20, 3.7 s, presentation simplified by GAP
to 3 generators.

Bugs found and fixed along the way:

- `end_points` mistranslated Magma's 1-based `Interv[1+(2 mod #Interv)]`
  (both endpoints coincided, so all volumes were 0).
- Rickards' `afuchinit` segfaults on algebras that are not split at exactly
  one real place: `normalizer_element_of_norm` now returns `None` there.
- Sage bug: `coefficient_tuple()` of quaternions over number fields returns
  non-normalized zeros (with a denominator) when the common denominator is
  nontrivial; they compare `!= 0`. `ArithGroupElement.__hash__` now uses
  `is_zero()`, and the Kleinian code keys elements by rational coordinates.

### 2026-11-26 (cont.): tests on antz9, Hecke operators over real quadratic fields

**Test setup.** At the user's request the Magma comparisons now run on the
server antz9 (Magma V2.27-7) in the tmux session `dpnm`: the working tree is
copied to `~/darmonpoints-nomagma`, built with the `darmonpoints-dev` conda
env, and `tools/antz/run_window.sh <name> <file>` opens a window with an
interactive Sage REPL that loads a test file and logs to `logs/<name>.log`.
The test files are in `tools/antz/`.

**Results on antz9 (Magma V2.27-7).**

| Test | Result |
|------|--------|
| QQ: (p, D) = (5, 6), (7, 6), (3, 10), (3, 22) | agree (abelianizations, 4 Hecke charpolys each); pari 1.6-5.2 s, magma 18-86 s |
| Kleinian, QQ(sqrt -7), D = primes above 2, maximal order | agree, ab = (3, 3) |
| Kleinian, QQ(sqrt -7), level a prime above 11 | agree, ab = (15, 0) |
| Bianchi PSL2(Z[i]), PSL2(Z[sqrt -2]) | agree, ab = (2, 2) and (6, 0) |
| QQ(sqrt5), P above 11, D = (3) | PARI: Hecke eigenvalues -4, 4, 6 at the primes of norm 11, 19, 29 = a_q of the curve found by `find_curve`; Magma backend: "ti not found" (see below) |
| Darmon point 78a1, p = 13 | the periods J_psi differ (ratio a 13-adic unit, not 1); under investigation |

**Hecke operators over totally real fields (bug, both backends).**
`_fix_sign` did nothing for totally real fields of degree > 1, so the
element of norm `l` used for `T_l` had a random sign at the split real
place, and `T_l` was sometimes composed with the involution at infinity
(e.g. charpoly `x^2 - 16` instead of `(x + 4)^2`, depending on the random
seed). Now the element is chosen with totally positive reduced norm (as over
QQ), using an element of the order whose norm is a unit negative at the split
place (`_unit_negative_at_split_place`; exact-norm search
`QuaternionAlgebraPari.elements_of_norm(..., exact=True)` for PARI, brute
force for Magma). The Hecke operators are now deterministic and commute with
the involution at infinity; their eigenvalues are the `a_q` of the elliptic
curve (checked for 5 primes of QQ(sqrt5)). The doctest of
`cohomology_arithmetic` was updated accordingly (it showed the operators
composed with the involution at infinity).

**"ti not found" (Magma backend, pre-existing bug).** With the Magma backend
over QQ(sqrt5), `get_hecke_reps` returned 11 instead of 12 representatives
for the prime of norm 11 conjugate to `P`, because
`order_discriminant()` was wrong: `magma_F_elt_to_sage` read the coordinates
of elements of the ring of integers (returned by `TwoElement`) as if they
were power-basis coordinates (they are integral-basis coordinates), so the
Magma ideal D*P was converted to a different ideal. Fixed by coercing such
elements into the number field first. (A seed sweep of 550 Hecke operators
with the PARI backend on antz9 found no failure.)

**Speed.** `ArithGroupElement.__hash__` is now cached and equality first
compares hashes: a Hecke operator over the cubic field x^3 - 3 went from 39 s
to 14 s (shared code, so both backends benefit).

**Darmon point period mismatch (78a1, p = 13, D = 6, beta = 5).**

- The periods computed on antz9 satisfy, to the full 13-adic precision
  (21 digits), `(J_pari * J_magma)^(13^2 - 1) = 1`: the PARI period is the
  inverse of the Magma one up to a root of unity, i.e. the points agree up to
  sign and torsion. (Also `J * frob(J)` is torsion for both, as expected for a
  point in the minus part E(K)^-.)
- It is not the orientation of the optimal embedding: the new keyword
  `orientation=-1` of `embed_order` (passed through `darmon_point`) makes
  the PARI run use exactly Magma's embedding (`w_K -> 1/2 - 1/2*i + 1/2*j -
  1/2*k`, same `gamma_psi`), and the period is unchanged up to torsion. The
  sign comes from the cohomology class `phi_E`, which is only defined up to
  sign (an eigenvector of the Hecke operators whose sign depends on the
  presentation of the group); `J` is multiplicative in `phi_E`.
- The point `-14 * (22 : 48*alpha - 11 : 1)` returned by `darmon_point` was
  not a backend issue: fed with Magma's period, `recognize_J` also returns
  `-14 * P0`. Since commit 4bdee17 (July 2020) the list of multipliers tried
  by `recognize_J` is sorted increasingly, so `1/14` is tried before `1`; the
  documented `(22 : 48*alpha - 11 : 1)` predates that (2017). The list is now
  ordered by simplicity (1, then 1/2, 2, ...): PARI gives
  `(-2 : -12*alpha + 1 : 1) = P0 + (-10 : 5 : 1)` and Magma's period gives
  `(22 : -48*alpha - 11 : 1) = -P0`. The Stark-Heegner doctest
  (`-70*alpha + 449`) is unchanged. The doctests now check that the point is
  `±P0` plus torsion.

**Results after the fixes (antz9, Magma V2.27-7).**

| Test | Result | time pari / magma |
|------|--------|-------------------|
| QQ, D = 6, level 5, p = 13 (26-dim Hecke spaces) | agree | 110 s / 3278 s |
| QQ(sqrt5), P above 11, D = (3) | agree: ab(Gn) = (10), ab(Gpn) = (5,5,10,0,0), T charpolys (x+4)^2, (x-4)^2, (x-6)^2 | 5.5 s / 240 s |
| Magma ideal conversion (`order_discriminant`) | now `9/2*r + 3/2` = D*P as expected | |

**Other fixes found while working on the cubic Darmon point example**
(`darmon_point(P, E, beta, 20)` over `x^3 - x^2 - x + 2`, a Kleinian case):

- `util.module_generators` (pre-existing bug) converted PARI's relative basis
  assuming a base field of degree 2, so over cubic fields it returned a
  non-integral `w`. It now checks that `O_K = O_F[w]` (the discriminant of
  `(1, w)` generates the relative discriminant) and otherwise searches small
  integral combinations of a basis of `O_K`. Over quadratic fields the result
  is unchanged.
- `QuaternionAlgebraPari.element_with_minpoly` translates `w` by `c in O_F`
  (so that the trace is small) before searching, and `short_elements`
  detects when PARI's `qfminim` truncated its output and repeats with a
  larger count instead of silently missing vectors.
- `BigArithGroup.wp()` for the PARI backend: when Rickards' Atkin-Lehner
  shortcut is not available (Kleinian groups, or B = M_2), the short elements
  of the order of `Gpn` whose reduced norm generates `p` are tested in order
  (`QuaternionAlgebraPari.search_elements_of_norm`) before the old random
  search. For the cubic example `wp` is found in 2 s (61 candidates) instead
  of the random search not finishing in 8 minutes.

### 2026-11-26 (afternoon): Phases 5 and 6 without Magma comparisons

From now on results are checked for soundness (algebraicity of Darmon
points, Hecke eigenvalues vs a_p) instead of against Magma.

**Optimal embeddings (`QuaternionAlgebraPari.element_with_minpoly`).** The
cubic Darmon point example spent 40 minutes in this search and failed:
enumerating the whole order and filtering by trace finds almost nothing,
because the solutions form a conjugacy class (an element is short only if its
axis passes near the centre of the majorant), while the trace-zero lattice has
huge numbers of short vectors (6e3 / 3e6 / 2.6e9 vectors within 1.5 / 3 / 10
times the minimum in the example). New method:

1. a cheap search over the affine lattice of elements of the given trace
   (closest vectors to a projected point, PARI's `qfcvp`; it needs an exact
   Gram matrix, so a scaled and rounded one is used and candidates are
   checked exactly);
2. otherwise, as Magma's `Embed` presumably does: find a pure quaternion `z`
   with `z^2 = t^2 - 4n` by solving norm equations (PARI `rnfisnorm`, with a
   Hilbert symbol prefilter; fixing in turn the `k`, `i` or `j` coordinate,
   because e.g. with `Z` fixed a prime dividing `b` can obstruct every
   choice), so `x1 = (t + z)/2` has the right minimal polynomial; then
   principalize the left ideal `I = O + O x1` (whose right order contains
   `x1`): if `I = O alpha` then `alpha x1 alpha^-1` lies in `O`. Generators of
   `I` form a whole orbit under the unit group, so short-vector search finds
   one quickly. (Sage's conic solver over number fields fails here with a
   PARI type error, so the norm equations are solved directly.)

For the cubic example the embedding is now found in about 45 s.

**`B = M_2(F)` (Bianchi groups).** `compute_quadratic_embedding` writes the
embedding down directly: `[[s, (s(t-s)-n)/g], [g, t-s]]` with `s` a root of
`x^2 - t x + n` modulo the level `N = (g)` (Heegner condition), converted with
the matrix units of `_get_O_basis`.

**Phase 5 cleanup.** `plectic.py` no longer starts Magma; dead
`Magma()` branches removed from `darmon_point` and `find_curve`; the
`padicperiods` example no longer passes `magma=magma`; the new modules
(`quatorder`, `afuch`, `kleinian`) are added to the Sphinx documentation.

**Soundness checks of Darmon points (no Magma).**

| Example | Result | Checks |
|---------|--------|--------|
| 78a1, p = 13, beta = 5 (QQ, D = 6) | `P0 + T` (P0 = (22 : 48a - 11 : 1), T 2-torsion) | infinite order, minus part |
| 30a1, p = 5, beta = 53 (QQ, D = 6) | `(113/49 : -207/343*a - 81/49 : 1)`, recognized with multiplier 1 | infinite order, `Q + sigma(Q) = 0`, height 4.63, analytic rank of E/K = 1; 9 s |
| cubic `x^3 - x^2 - x + 2`, P = (r^2 - 2r - 1), beta = -3r^2 + 9r - 6 (Kleinian, D = (-r)) | `(-r^2 + r + 1 : (1/2*r^2 - 1)*a - 1/2*r^2 + r + 2 : 1)` | infinite order, `Q + sigma(Q) = 0`, height 0.40; 370 s (the embedding search, previously failing after 40 min, now 51 s) |

The cubic example is now a real doctest (it checks infinite order and the
minus part).

**Installation.** README: install with `pip install --no-build-isolation`,
since the extension must be compiled against Sage's cypari2/PARI.

**Full doctest run (`sage -t --long`, 2026-11-26).** All files pass except
the pre-existing failures in `my_p1list_nf.py` (2) and `ocmodule.py` (2),
which also fail on the original `HEAD`. The previously Magma-only examples now
run: `darmonpoints.py` (78a1 point; Darmon point over the cubic field
`x^3 - x^2 - x + 2`, 404 s), `findcurve.py` (QQ, QQ(sqrt5), and the cubic
field `x^3 - 3`, which takes 50 minutes), `darmonvonk.py` (the invariant is
defined up to sign, so the doctest accepts `7*x^2 +- 11*x + 7`).
`padicperiods.py`: its module example was already broken (`beta =` without
a value) and is now marked `# not tested`.

**Possible follow-ups.** The cubic `find_curve` example is slow (50 min);
Page's "Maximal" group type (normalizer) is not ported (darmonpoints does not
use it); the Magma backend and the `KleinianGroups-1.0` Magma package are
still shipped for comparisons (`backend='magma'`).

### 2026-11-26 (evening): performance of Darmon point computations

Profiled `darmon_point` on 78a1 (QQ, p = 13) and on the cubic field
`x^3 - x^2 - x + 2` (Kleinian). Timings (without profiler):

| Example | before | after |
|---------|--------|-------|
| 78a1, p = 13, beta = 5 | 56 s | 8.6 s |
| 30a1, p = 5, beta = 53 | 9 s | 2.0 s |
| cubic `x^3 - x^2 - x + 2` | 370 s | 75 s |
| Stark-Heegner 35a1 (unchanged code path) | 12 s | 15 s |

Changes (results unchanged; points checked: infinite order, `Q + sigma(Q) = 0`):

- `OCVn._get_powers` (action matrices on overconvergent distributions,
  the main cost of the overconvergent lift over QQ): computed with C-level
  polynomials over `Z/p^(depth-1)` (truncated inverse and products) instead
  of p-adic power series; identical matrices, 5-8x faster.
- Searches for elements of given norm (`elements_of_norm`,
  `search_elements_of_norm`, trace-slice search, principalization): the
  reduced norm is evaluated on the raw integer vectors inside PARI (integer
  quadratic forms, one matrix product per coordinate), and only matching
  vectors become quaternions.
- `element_with_minpoly`: principalization first (about 1.5 s), the
  trace-slice search only as a fallback.
- `ArithGroup_nf_generic._is_in_order`: now checks that the coordinates in the
  Z-basis of the order are integers (one rational matrix-vector product).
  The previous test grouped these coordinates into elements of F and tested
  their integrality, which is wrong for general Z-bases (PARI's, Magma's) and
  when `O_F != Z[r]`.
- `our_algdep`: LLL-reduced integral kernel with PARI's `matkerint`
  instead of Sage's kernel + saturation + LLL; the matrix of powers is read
  from the polynomial representation for unramified extensions (same results
  on tests, about 4x faster).
- `recognize_J`: candidates `J1` are first restricted to those compatible
  with `sigma(P) = +-P` (when the class number of K is 1): `frob(J1)` is `J1`
  or `J1^-1` up to a power of `qE`, tested before computing coordinates; and
  each multiplier is first tried without the torsion factor. A second pass
  runs the previous exhaustive search if the first finds nothing. For the
  cubic example this cut the number of algebraic recognitions from 20931 to a
  few hundred.

Remaining costs in the cubic example: integration (`log_pseries`,
`lift_to_locally_analytic`, ~24 s), cycle construction (Hecke
representatives and `zero_degree_equivalent`, ~27 s), fundamental domains
(~14 s).

### U_p lifting (2026-11-26)

Bottleneck for `darmon_point(13, EllipticCurve('78a1'), 5, prec)`: `improve`
applies U_p about prec+2 times, and each application re-evaluated the cocycle
at the (p+1)·n Hecke words through Fox gradients, forming matrix sums
Σ a_g M(g) each time (40 of the 47 s at prec 40).

Changes:
- `ArithCohOverconvergent._Up_local_matrix`: U_p is linear on the moments of
  the values at the generators, so its block matrix
  U_{j,i} = Σ_k P(s_k) ∂_i(t_{k,j}) is computed once (mod p^N, FLINT ZZ) and
  cached; `apply_Up` then is one matrix-vector product (used when the module
  is `OCVn`, no Shapiro, default representatives; otherwise the old code).
- `darmonpoints/moments.pyx` (new Cython/FLINT extension):
  `moebius_moment_matrix(a,b,c,d,N,depth)` computes the rows of
  ((b+az)/(d+cz))^i mod N via the recurrence
  y_i[j] = (b/d) y_{i-1}[j] + (a/d) y_{i-1}[j-1] − (c/d) y_i[j-1]
  (O(depth^2) per matrix instead of O(depth^3)); 6–14× faster than the NTL
  version, identical output. `OCVn._get_powers` uses it, falling back to NTL.
  `setup.py` passes Sage's directory to Cython's include path and adds
  `sage/libs/flint` (for `flint_wrap.h`) to the C include dirs.
- `_get_powers_reference` was missing its `return`.

Timings (whole `darmon_point` call; J_psi bit-for-bit identical to before):

| prec | before | after |
|---|---|---|
| 20 | 9.4 s | 2.8 s |
| 40 | 58.4 s | 6.8 s |
| 60 | 117.7 s | 14.1 s |

Remaining cost of the U_p build: the K·n² products P(s_k)·S (depth³ each),
already at the FLINT/hardware limit; applying them lazily costs the same over
~prec iterations.

### Other overconvergent modules (2026-11-26)

**Meromorphic functions / Darmon–Vonk** (`darmon_vonk_point(5, 1, 3, 13, 60, parity='+')`,
K = Q_5(√3), prec 60): `OverconvergentDVCocycle.improve` (59 applications of U_p,
multiplicative cocycle values) took 17.8 s of 19 s.
- `ArithGroupElement._act_on_` tried `matrix * x` first; for meromorphic
  functions the coercion model searched for an action (building pushouts of
  p-adic rings, and calling the action on test elements: 3× more actions than
  needed), failed with TypeError, and did not cache the failure. Failed
  (matrix parent, parent) pairs are now remembered (17.8 → 13 s).
- `MeromorphicIntegerArithmetic` (meromorphic.py): series over O_K (K = Q_p or
  unramified) as d FLINT integer polynomials mod p^N; actions as one product
  with a precomputed (d·n)×(d·n) integer matrix; products by d² truncated
  products; inverses by Newton. Results equal the p-adic ones (absolute
  precision N throughout).
- `OverconvergentDVCocycle._improve_integer` replays exactly the naive
  evaluation of `CohArbitrary.apply_hecke_operator` (same prefix group
  elements, action by g after the product of each word; normalization by
  the constant term done once at the end, which is exact) in integers;
  falls back to the p-adic loop on non-integral data / insufficient
  precision / non-units.
- Result: improve 17.8 → 2.4 s, whole example 19 → 4 s, J bit-for-bit identical.
- Note: `darmon_vonk_cocycle` fails intermittently (`assert found` in
  `ArithGroup.mat_list`, ~35% of tries, same rate before and after these
  changes); the retry loop in `darmon_vonk_point` absorbs it.

**theta_additive**: `_integer_moebius_matrix` uses the FLINT kernel (2.3× faster, same matrices).

**Bianchi** (ocbianchi.py): `BianchiDistributions._get_powers` is the Kronecker
product of two one-variable FLINT moment matrices, reduced mod p^N (the old
matrices had unreduced entries; congruent mod p^N); 4–18× faster, doctests pass.
The Bianchi lift itself (`get_overconvergent_class_bianchi`) is unreachable on
main and here: `BigArithGroup._hardcode_matrices` is forced to False since
80d00ea, and `get_Up_reps_bianchi` requires it. So no precomputed U_p there.

**PARI backend fixes for B = M_2(F), F imaginary quadratic** (found while trying
the Bianchi lift; group construction used to crash):
- `ArithGroup_generic._matrix_algebra_padic_splitting`: p-adic splitting in the
  matrix model of `_get_O_basis` ((1±i)/2, (j±k)/2 matrix units).
- `BigArithGroup._matrix_algebra_wp`: explicit Atkin–Lehner element
  [[πx, y], [n, π]] with det π (doctest over Q(i), p = 2+i, level 3).

### Further bottlenecks (2026-11-26, cubic-field Darmon point)

Cubic example (`x^3 - x^2 - x + 2`, p = 17): 78 s → 41 s; 78a1 prec 60: 14.1 → 9.4 s;
`darmonpoints.py` doctests 101 → 50 s. All points unchanged and sound; J for 78a1
bit-for-bit identical.
- `QuaternionAlgebraPari.elements_of_norm` / `search_elements_of_norm`: enumerate
  short vectors in batches (`_some_short_vectors`, qfminim with a count of 2000,
  enlarged ×4 only if nothing is found). One Hecke-representative search was
  enumerating and filtering 500000 vectors (20 s) to find one element.
- `recognize_J`: skip the (pnum, pden, i) whose valuation is not divisible by pden
  before computing powers (our_nroot returned [] for 20000 of 20544 calls);
  `_frobenius` (from `_flint_rep_abs`, cached Frob(g) powers; ~10× faster than
  `.frobenius()` for FLINT q-adic fields, which also reports fake precision).
- `our_nroot` (p ∤ n): residues of the roots from `nth_root(all=True)` in the
  residue field (sorted as the old search found them), one Newton refinement,
  the others by Teichmüller roots of unity; no quadratic dedup. Same roots, same order.
- `recognize_point`: factor the algdep polynomial over QQ and only compute roots
  over HCF of factors of degree dividing [HCF:QQ], and for degree = [HCF:QQ] only
  if disc(g)/disc(HCF) is a square (exact necessary conditions).
  recognize_J 25.6 → 7.9 s on the saved cubic instance.
- `integrate_H1`: pair `log c0 + Σ n_P log(1 - x_P z)` with the moments directly
  (power sums of the x_P, one division per degree, moments converted once per
  edge) instead of building a polynomial per point (`_locally_analytic_data`,
  `_pair_with_moments`; `lift_to_locally_analytic` kept).
- `divisors._hash`: key FLINT q-adic points by (valuation, precision, integer
  coefficients) instead of `hash(str(x))`; identifies exactly the same points
  (checked on ~1.6M pairs), 10–18× cheaper.

Remaining (cubic, 40 s): recognize_J ~13 s when the point is found late in the
multiplier list (~2500 algdep calls at ~2 ms), cycle construction ~12 s
(zero_degree_equivalent 6 s), integration 7 s, groups 4.7 s, Hecke matrices 3.7 s.
Not done: the non-cohomological SH integral `double_integral_zero_infty` (5 s in
the 35a1 example) could use the same closed form (the series is a Möbius
transform of r), but its subdivision test would need care to stay equivalent.

### Plectic points (2026-11-26, stopped here)

Example: 63.2-d1 over Q(√37), p = 3, beta = 27w + 50 (Dropbox `sample_usage.sage`,
without Magma). It did not run on the PARI backend; now depth 2 runs end to end
(~22 s, J = O(3^2)). Fixes:
- `quaternion_algebra_invariants_from_ramification`: an integer i in S means
  `F.real_places()[i]` (as the old Magma path accepted indices).
- `PlecticGroup_class`: w_{p_i} taken in the order of GS (level p0 p1) via
  `normalizer_element_of_norm`; otherwise `get_BT_reps` never finds
  representatives satisfying `local_condition` (it ran for hours).
- `_filter_by_norm(absolute=True)` accepts rational targets (the
  principalization in `get_cycle` uses N(nrd I) = 1/4).
- `_unit_negative_at_split_place`: places compared with a tolerance (they were
  compared at different precisions, so no unit qualified), and the PARI search
  looks directly for an element with unit norm negative at the split place
  (norms only matter up to squares of units). `ArithGroup_nf_generic.non_positive_unit`
  uses it on the PARI backend (20 s brute force → instant).
- Trivial action: cocycle values at words via cached letter counts, and Hecke
  operators via cached count matrices (`ArithCoh._trivial_hecke_counts`);
  identical Hecke matrices. Cocycle step 20–36 s → ~7 s.
Not finished: at depth 3 one run had a very slow Riemann sum (~1 min per term,
1296 terms), while profiling individual terms afterwards gave ~10 ms per term;
not resolved (possibly a random choice of cycle). The depth 3/4 timings were
not completed.
