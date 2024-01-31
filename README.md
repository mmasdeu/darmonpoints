<p align="center">
    <img alt="logo" src="https://github.com/mmasdeu/darmonpoints/raw/main/doc/static/logo.svg?sanitize=true">
</p>

# A package to compute Darmon points

## (or just p-adically construct elliptic curves, or p-adic Darmon-Vonk points,...)

(for the full documentation, please see
<http://mmasdeu.github.io/darmonpoints/doc/html/>)


![doc](https://github.com/mmasdeu/darmonpoints/actions/workflows/doc.yml/badge.svg)

![test](https://github.com/mmasdeu/darmonpoints/actions/workflows/test.yml/badge.svg)

![lint](https://github.com/mmasdeu/darmonpoints/actions/workflows/lint.yml/badge.svg)


### What is this?

The **darmonpoints** package can compute many different types of what is
known as Darmon points. These are known as *Stark-Heegner* points in
some literature, and originated in
<a href="#Darmon" class="citation">[Darmon]</a>. Subsequent
generalizations were introduced by
<a href="#Greenberg" class="citation">[Greenberg]</a> and
<a href="#Trifkovic" class="citation">[Trifkovic]</a>. This has been
generalized by <a href="#GMS1" class="citation">[GMS1]</a> to elliptic
curves defined over number fields of arbitrary signature. Darmon points
are attached to triples <span class="title-ref">(F,E,K)</span>, where
<span class="title-ref">F</span> is a number field,
<span class="title-ref">E/F</span> is an elliptic curve defined over
<span class="title-ref">F</span>, and <span class="title-ref">K/F</span>
is a quadratic extension. These triples must satisfy certain conditions
for Darmon points to be attached to them. The article
<a href="#GMS1" class="citation">[GMS1]</a> contains an overview of all
of this. We include also a variation used in
<a href="#KP" class="citation">[KP]</a>.

The **darmonpoints** package can also compute equations for some
elliptic curves <span class="title-ref">E/F</span> defined over number
fields <span class="title-ref">F</span>, as long as certain conditions
are satisfied. Namely:

1)  <span class="title-ref">F</span> has narrow class number
    <span class="title-ref">1</span>.
2)  if <span class="title-ref">N</span> is the conductor of the elliptic
    curve, it must admit a factorization of the form
    <span class="title-ref">N = PDM</span>, where:
    1)  <span class="title-ref">P</span>,
        <span class="title-ref">D</span> and
        <span class="title-ref">M</span> are relative coprime.
    2)  <span class="title-ref">P</span> is a prime ideal of
        <span class="title-ref">F</span> of prime norm.
    3)  <span class="title-ref">D</span> is the discriminant of a
        quaternion algebra over <span class="title-ref">F</span> which
        is split at only one infinite place.

Finally, we include the module *padicperiods*, which allows for the
computation of <span class="title-ref">p</span>-adic periods attached to
two-dimensional components of the cohomology of the same arithmetic
groups, and which has allowed us to find the corresponding abelian
surfaces in some cases (see <a href="#GM" class="citation">[GM]</a>).

The full documentation can be found at
<http://mmasdeu.github.io/darmonpoints/doc/html/>

### Installation

Installation of the *darmonpoints* package has been greatly simplified,
thanks to Matthias Köppe "Sample Sage"
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
    perform a <span class="title-ref">7</span>-adic calculation to
    precision <span class="title-ref">7^20</span>, to find a point over
    the real quadratic field of discriminant
    <span class="title-ref">41</span> for the elliptic curve `35a1`:

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
    find a curve of conductor <span class="title-ref">30</span>, using a
    <span class="title-ref">5</span>-adic calculation with precision of
    <span class="title-ref">5^20</span>, and the quaternion algebra of
    discriminant \`6\`:

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

<div id="citations">

<span id="Darmon" class="citation-label">Darmon</span>  
H.Darmon. *Integration on Hp x H and arithmetic applications*. Annals of
Math.

<span id="DarmonVonk" class="citation-label">DarmonVonk</span>  
H.Darmon, J.Vonk. *Singular moduli for real quadratic fields: a rigid
analytic approach*. Duke Math.

<span id="GM" class="citation-label">GM</span>  
X.Guitart, M.Masdeu. *Periods of modular GL2-type abelian varieties and
p-adic integration*. Experimental Mathematics.

<span id="GMS1" class="citation-label">GMS1</span>  
X.Guitart, M.Masdeu, M.H.Sengun. *Darmon points on elliptic curves over
number fields of arbitrary signature*. Proc. LMS.

<span id="GMS2" class="citation-label">GMS2</span>  
X.Guitart, M.Masdeu, M.H.Sengun. *Uniformization of modular elliptic
curves via p-adic methods*. Journal of Algebra.

<span id="GMX" class="citation-label">GMX</span>  
X.Guitart, M.Masdeu, X.Xarles *A quaternionic construction of p-adic
singular moduli*. Res. Math. Sci.

<span id="Greenberg" class="citation-label">Greenberg</span>  
M.Greenberg. *Stark-Heegner points and the cohomology of quaternionic
Shimura varieties*. Duke Math.

<span id="KP" class="citation-label">KP</span>  
A.Pacetti, D.Kohen (with an appendix by M.Masdeu) *On Heegner points for
primes of additive reduction ramifying in the base field*. Transactions
of the AMS.

<span id="Trifkovic" class="citation-label">Trifkovic</span>  
M.Trifkovic. *Stark-Heegner points on elliptic curves defined over
imaginary quadratic fields*. Duke Math.

</div>
