====================
Darmon Points
====================
For installation and basic usage instructions please see the main Github repository (https://github.com/mmasdeu/darmonpoints).

The **darmonpoints** package can compute many different types of what is known as Darmon points. These are known as *Stark-Heegner* points in some literature, and originated in [Darmon]_. Subsequent generalizations were introduced by [Greenberg]_ and [Trifkovic]_. This has been generalized by [GMS1]_ to elliptic curves defined over number fields of arbitrary signature. Darmon points are attached to triples `(F,E,K)`, where `F` is a number field, `E/F` is an elliptic curve defined over `F`, and `K/F` is a quadratic extension. These triples must satisfy certain conditions for Darmon points to be attached to them. The article [GMS1]_ contains an overview of all of this. We include also a variation used in [KP]_.

The **darmonpoints** package can also compute equations for some elliptic curves `E/F` defined over number fields `F`, as long as certain conditions are satisfied. Namely:

1) `F` has narrow class number `1`.
2) if `N` is the conductor of the elliptic curve, it must admit a factorization of the form `N = PDM`, where:

   a) `P`, `D` and `M` are relative coprime.
   b) `P` is a prime ideal of `F` of prime norm.
   c) `D` is the discriminant of a quaternion algebra over `F` which is split at only one infinite place.

Finally, we include the module *padicperiods*, which allows for the computation of `p`-adic periods attached to two-dimensional components of the cohomology of the same arithmetic groups, and which has allowed us to find the corresponding abelian surfaces in some cases (see [GM]_).


..   [Darmon] H.Darmon. *Integration on Hp x H and arithmetic applications*. Annals of Math.
..   [Greenberg] M.Greenberg. *Stark-Heegner points and the cohomology of quaternionic Shimura varieties*. Duke Math.
..   [GM] X.Guitart, M.Masdeu. *Periods of modular GL2-type abelian varieties and p-adic integration*. Experimental Mathematics.
..   [GMS1] X.Guitart, M.Masdeu, M.H.Sengun. *Darmon points on elliptic curves over number fields of arbitrary signature*. Proc. LMS.
..   [GMS2] X.Guitart, M.Masdeu, M.H.Sengun. *Uniformization of modular elliptic curves via p-adic methods*. Journal of Algebra.
..   [KP] A.Pacetti, D.Kohen (with an appendix by M.Masdeu) *On Heegner points for primes of additive reduction ramifying in the base field*. Transactions of the AMS.
..   [Trifkovic] M.Trifkovic. *Stark-Heegner points on elliptic curves defined over imaginary quadratic fields*. Duke Math.

This work is licensed under a `Creative Commons Attribution-Share Alike
3.0 License`__.

__ https://creativecommons.org/licenses/by-sa/3.0/

.. toctree::
   :maxdepth: 2

Arithmetic Groups
------------------

.. toctree::

   arithmeticgroups

Cohomology and Homology
------------------------
.. toctree::

   cohomology

Integration pairing
--------------------
.. toctree::

   integration

Overconvergent distributions
------------------------------
.. toctree::

   distributions

Internals
-----------------
.. toctree::

   internals

Indices and Tables
==================

* :ref:`genindex`
* :ref:`modindex`
* :ref:`search`
