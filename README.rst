==================================
A package to compute Darmon points
==================================
----------------------------------
(or just p-adically construct elliptic curves)
----------------------------------

What is this?
~~~~~~~~~~~~~
The **darmonpoints** package can compute many different types of what is known as Darmon points. These are known as *Stark-Heegner* points in some literature, and originated in [Darmon]_. Subsequent generalizations were introduced by [Greenberg]_ and [Trifkovic]_. This has been generalized by [GMS]_ to elliptic curves defined over number fields of arbitrary signature. Darmon points are attached to triples `(F,E,K)`, where `F` is a number field, `E/F` is an elliptic curve defined over `F`, and `K/F` is a quadratic extension. These triples must satisfy certain conditions for Darmon points to be attached to them. The article [GMS] contains an overview of all of this.

The **darmonpoints** package can also compute equations for some elliptic curves `E/F` defined over number fields `F`, as long as certain conditions are satisfied. Namely:

1) `F` has narrow class number `1`.
2) if `N` is the conductor of the elliptic curve, it must admit a factorization of the form `N = PDM`, where:
   a) `P`, `D` and `M` are relative coprime.
   b) `P` is a prime ideal of `F` of prime norm.
   c) `D` is the discriminant of a quaternion algebra over `F` which is split at only one infinite place.


Installation
~~~~~~~~~~~~

Installation of the *darmonpoints* package has been grealy simplified and is now essentially trivial. For most operations one does need to have **Magma** installed, although we do hope that in the future Sage will include the required functionality. We include for convenience the dependencies, which are currently:

1) The package *KleinianGroups*, the original of which can be found at http://www.normalesup.org/~page/Recherche/Logiciels/KleinianGroups/KleinianGroups-1.0.tar.gz.

2) The *overconvergent modular symbols* package (or rather some parts of it). This is currently on *Sage trac*, see  http://trac.sagemath.org/ticket/812 and please review it!


Basic usage
~~~~~~~~~~~

The file ``darmonpoints.sage`` contains the high level routines from which show how to use the package, although one can use parts of the package in other ways if one feels adventurous. Here are some sample calculations that one can try::

    sage: %runfile 'darmonpoints.sage'

1) A classical Darmon (a.k.a. Stark-Heegner) point. The following will perform a `7`-adic calculation to precision `7^20`, to find a point over the real quadratic field of discriminant `41` for the elliptic curve ``35a1``::

    sage: darmon_point(7,EllipticCurve('35a1'),41,20)

2) A quaternionic Darmon (a.k.a. Greenberg) point::

    sage: darmon_point(13,EllipticCurve('78a1'),5,20)

3) A Darmon point for a curve over a field of mixed signature::

    sage: F.<r> = NumberField(x^3 - x^2 - x + 2)
    sage: E = EllipticCurve([-r -1, -r, -r - 1,-r - 1, 0])
    sage: N = E.conductor()
    sage: P = F.ideal(r^2 - 2*r - 1)
    sage: beta = -3*r^2 + 9*r - 6
    sage: darmon_point(P,E,beta,20)

We can also *discover* equations of curves!

1) We first find a curve over the rationals. The following command will find a curve of conductor `30`, using a `5`-adic calculation with precision of `5^20`, and the quaternion algebra of discriminant `6`::

     sage: find_curve(5,6,30,20)

This constructs the curve with equation::

     y^2 + x*y + y = x^3 + x + 2


2) Now for a curve defined over a real quadratic field. Note that here we must specify which place will ramify in the quaternion algebra::

     sage: F.<r> = QuadraticField(5)
     sage: P = F.ideal(3/2*r + 1/2)
     sage: D = F.ideal(3)
     sage: find_curve(P,D,P*D,30,ramification_at_infinity=[-1,1])

This returns something like::

   y^2 + (1/2*r-1/2)*x*y = x^3 + (1/2*r+1/2)*x^2 + (285/2*r-793/2)*x + (3153/2*r-7689/2)


3) A curve over a cubic field of mixed signature::

     sage: F.<r> = NumberField(x^3-x^2-x+2)
     sage: N = F.ideal(r^2 + 2)
     sage: P = N.factor()[0][0]
     sage: D = N/P
     sage: find_curve(P,D,N,20)

which returns::

  y^2 + x*y + y = x^3 + (r^2-2)*x^2 + (r^2-2)*x + (-r^2-r)

4) Another (more spectacular) curve over a cubic field of mixed signature::

     sage: F.<r> = NumberField(x^3 -3)
     sage: P = F.ideal(r-2)
     sage: D = F.ideal(r-1)
     sage: find_curve(P,D,P*D,30)

This should return an elliptic curve like this::

   y^2 + r*x*y + (r+1)*y = x^3 + (-575*r^2-829*r-1195)*x + (-13327*r^2-19221*r-27721)

..   [Darmon] H.Darmon. *Integration on Hp x H and arithmetic applications*. Annals of Math.
..   [GMS] X.Guitart, M.Masdeu, M.H.Sengun. *Darmon points on elliptic curves over number fields of arbitrary signature*. Preprint.
..   [Greenberg] M.Greenberg. *Stark-Heegner points and the cohomology of quaternionic Shimura varieties*. Duke Math.
..   [Trifkovic] M.Trifkovic. *Stark-Heegner points on elliptic curves defined over imaginary quadratic fields*. Duke Math.
