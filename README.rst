A package to compute Darmon points
==================================

Installation
~~~~~~~~~~~~

Currently Sage does not work with the Overconvergent modular symbols of Pollack-Stevens. This is why this package includes a frozen copy of the OMS package (the current version can be found in https://github.com/roed314/OMS ). Instructions for the installation of this package are included in ``OMS/README_ps.txt``.

Basic usage
~~~~~~~~~~~

Here there is simple example. Look at ``example.sage`` for a more detailed calculation::

    sage: load('darmonpoints.sage')
    sage: E = EllipticCurve('78a1')
    sage: p = 13 # Must divide the conductor of E
    sage: dK = 5 # The discriminant of the real quadratic field.
    sage: prec = 20 # Precision to which result is desired
    sage: outfile = 'point_quaternionic.txt' # Optional
    sage: darmon_point(p,E,dK,prec,outfile = outfile)

The package is capable of computing the classical Darmon (a.k.a. Stark-Heegner) points::

    sage: load('darmonpoints.sage')
    sage: E = EllipticCurve('35a1')
    sage: p = 7 # Must divide the conductor of E
    sage: dK = 41 # The discriminant of the real quadratic field.
    sage: prec = 20 # Precision to which result is desired
    sage: outfile = 'point_classical.txt' # Optional
    sage: darmon_point(p,E,dK,prec,outfile = outfile)
