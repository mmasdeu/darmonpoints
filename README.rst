A package to compute Darmon points
==================================

Installation
~~~~~~~~~~~~

Currently (as of version 5.10) Sage does not work with the "Overconvergent modular symbols" of Pollack-Stevens. This is why this package includes a frozen copy of the OMS package (the cutting-edge version can be found at https://github.com/roed314/OMS ). Here is how to install it.

  1. Patch the Sage library::

         sage -sh
         cd $SAGE_ROOT/devel/sage
         hg qimport -P /path/to/changes_to_sagelib-5.10.patch

  2. Copy files:

     - The following should work fine (notice the trailing slash after sage)::

         sage -sh
         cp -r /path/to/OMS/sage/ $SAGE_ROOT/devel/sage/

     - But if you're worried about overwriting things you can do the following instead::

         sage -sh
         cd $SAGE_ROOT/devel/sage/sage/modular
         cp -r /path/to/OMS/sage/modular/btquotients .
         cp -r /path/to/OMS/sage/modular/pollack_stevens .

  3. Build::

         sage -b

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
