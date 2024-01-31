# A package to compute Darmon points

## (or just p-adically construct elliptic curves, or p-adic Darmon-Vonk points,\...)

(for the full documentation, please see
<http://mmasdeu.github.io/darmonpoints/doc/html/>)

### What is this?

The **darmonpoints** package can compute many different types of what is
known as Darmon points. These are known as *Stark-Heegner* points in
some literature, and originated in [\[Darmon\]](#Darmon){.citation}.
Subsequent generalizations were introduced by
[\[Greenberg\]](#Greenberg){.citation} and
[\[Trifkovic\]](#Trifkovic){.citation}. This has been generalized by
[\[GMS1\]](#GMS1){.citation} to elliptic curves defined over number
fields of arbitrary signature. Darmon points are attached to triples
[(F,E,K)]{.title-ref}, where [F]{.title-ref} is a number field,
[E/F]{.title-ref} is an elliptic curve defined over [F]{.title-ref}, and
[K/F]{.title-ref} is a quadratic extension. These triples must satisfy
certain conditions for Darmon points to be attached to them. The article
[\[GMS1\]](#GMS1){.citation} contains an overview of all of this. We
include also a variation used in [\[KP\]](#KP){.citation}.

The **darmonpoints** package can also compute equations for some
elliptic curves [E/F]{.title-ref} defined over number fields
[F]{.title-ref}, as long as certain conditions are satisfied. Namely:

1)  [F]{.title-ref} has narrow class number [1]{.title-ref}.
2)  if [N]{.title-ref} is the conductor of the elliptic curve, it must
    admit a factorization of the form [N = PDM]{.title-ref}, where:
    a)  [P]{.title-ref}, [D]{.title-ref} and [M]{.title-ref} are
        relative coprime.
    b)  [P]{.title-ref} is a prime ideal of [F]{.title-ref} of prime
        norm.
    c)  [D]{.title-ref} is the discriminant of a quaternion algebra over
        [F]{.title-ref} which is split at only one infinite place.

Finally, we include the module *padicperiods*, which allows for the
computation of [p]{.title-ref}-adic periods attached to two-dimensional
components of the cohomology of the same arithmetic groups, and which
has allowed us to find the corresponding abelian surfaces in some cases
(see [\[GM\]](#GM){.citation}).

The full documentation can be found at
<http://mmasdeu.github.io/darmonpoints/doc/html/>

### Installation

Installation of the *darmonpoints* package has been greatly simplified,
thanks to Matthias Köppe \"Sample Sage\"
(<https://github.com/mkoeppe/sage_sample>). For most operations one
*does need* to have **Magma** (<https://magma.maths.usyd.edu.au/magma/>)
installed, although we do hope that in the future Sage will include the
required functionality.

We include for convenience the dependency Magma package *KleinianGroups*
by Aurel Page, the original of which can be found at
<http://www.normalesup.org/~page/Recherche/Logiciels/KleinianGroups/KleinianGroups-1.0.tar.gz>.

To install the package use the following command:

    sage -pip install --user --upgrade darmonpoints

If you rather install the cutting-edge version from the github
repository (which is likely to be broken), then use the following
command:

    sage -pip install --user --upgrade -v git+https://github.com/mmasdeu/darmonpoints.git

### Basic usage

The files `darmonpoints.py`, `findcurve.py` and `padicperiods.py`
contain the high level routines from which show how to use the package,
although one can use parts of the package in other ways if one feels
adventurous. Here are some sample calculations that one can try:

    sage: from darmonpoints.darmonpoints import darmon_point

1)  A classical Darmon (a.k.a. Stark-Heegner) point. The following will
    perform a [7]{.title-ref}-adic calculation to precision
    [7\^20]{.title-ref}, to find a point over the real quadratic field
    of discriminant [41]{.title-ref} for the elliptic curve `35a1`:

        sage: darmon_point(7,EllipticCurve('35a1'),41,20)

2)  A quaternionic Darmon (a.k.a. Greenberg) point:

        sage: darmon_point(13,EllipticCurve('78a1'),5,20)

3)  A Darmon point for a curve over a field of mixed signature:

        sage: F.<r> = NumberField(x^3 - x^2 - x + 2)
        sage: E = EllipticCurve([-r -1, -r, -r - 1,-r - 1, 0])
        sage: N = E.conductor()
        sage: P = F.ideal(r^2 - 2*r - 1)
        sage: beta = -3*r^2 + 9*r - 6
        sage: darmon_point(P,E,beta,30)

We can also *discover* equations of curves!

1)  We first find a curve over the rationals. The following command will
    find a curve of conductor [30]{.title-ref}, using a
    [5]{.title-ref}-adic calculation with precision of
    [5\^20]{.title-ref}, and the quaternion algebra of discriminant
    \`6\`:

        sage: from darmonpoints.findcurve import find_curve
        sage: find_curve(5,6,30,20)

    This constructs the curve with equation:

        y^2 + x*y + y = x^3 + x + 2

2)  Now for a curve defined over a real quadratic field. Note that here
    we must specify which place will ramify in the quaternion algebra:

        sage: from darmonpoints.findcurve import find_curve
        sage: F.<r> = QuadraticField(5)
        sage: P = F.ideal(3/2*r + 1/2)
        sage: D = F.ideal(3)
        sage: find_curve(P,D,P*D,30,ramification_at_infinity = F.real_places()[:1])

    This returns something like:

        y^2 + (1/2*r-1/2)*x*y = x^3 + (1/2*r+1/2)*x^2 + (285/2*r-793/2)*x + (3153/2*r-7689/2)

3)  A curve over a cubic field of mixed signature:

        sage: from darmonpoints.findcurve import find_curve
        sage: F.<r> = NumberField(x^3 -3)
        sage: P = F.ideal(r-2)
        sage: D = F.ideal(r-1)
        sage: find_curve(P,D,P*D,30)

    This should return an elliptic curve like this:

        y^2 + r*x*y + (r+1)*y = x^3 + (-575*r^2-829*r-1195)*x + (-13327*r^2-19221*r-27721)

Finally, there is also code to compute Darmon-Vonk quantities. Here are
a couple of examples.

1)  A Darmon-Vonk point for the matrix group:

        sage: from darmonpoints.darmonvonk import darmon_vonk_point
        sage: darmon_vonk_point(5, 1, 3, 13, 60, recognize_point='lindep')

2)  A quaternionic Darmon-Vonk point:

        sage: from darmonpoints.darmonvonk import darmon_vonk_point
        sage: darmon_vonk_point(5, 6, 53, 92, 120, scaling=12, recognize_point='algdep')

::: {#citations}

[Darmon]{#Darmon .citation-label}

:   H.Darmon. *Integration on Hp x H and arithmetic applications*.
    Annals of Math.

[DarmonVonk]{#DarmonVonk .citation-label}

:   H.Darmon, J.Vonk. *Singular moduli for real quadratic fields: a
    rigid analytic approach*. Duke Math.

[GM]{#GM .citation-label}

:   X.Guitart, M.Masdeu. *Periods of modular GL2-type abelian varieties
    and p-adic integration*. Experimental Mathematics.

[GMS1]{#GMS1 .citation-label}

:   X.Guitart, M.Masdeu, M.H.Sengun. *Darmon points on elliptic curves
    over number fields of arbitrary signature*. Proc. LMS.

[GMS2]{#GMS2 .citation-label}

:   X.Guitart, M.Masdeu, M.H.Sengun. *Uniformization of modular elliptic
    curves via p-adic methods*. Journal of Algebra.

[GMX]{#GMX .citation-label}

:   X.Guitart, M.Masdeu, X.Xarles *A quaternionic construction of p-adic
    singular moduli*. Res. Math. Sci.

[Greenberg]{#Greenberg .citation-label}

:   M.Greenberg. *Stark-Heegner points and the cohomology of
    quaternionic Shimura varieties*. Duke Math.

[KP]{#KP .citation-label}

:   A.Pacetti, D.Kohen (with an appendix by M.Masdeu) *On Heegner points
    for primes of additive reduction ramifying in the base field*.
    Transactions of the AMS.

[Trifkovic]{#Trifkovic .citation-label}

:   M.Trifkovic. *Stark-Heegner points on elliptic curves defined over
    imaginary quadratic fields*. Duke Math.
:::
