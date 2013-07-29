A package to compute Darmon points
==================================

Installation
~~~~~~~~~~~~

Currently (as of version 5.10) Sage does not work with the "Overconvergent modular symbols" of Pollack-Stevens. This is why this package includes a frozen copy of the OMS package. The cutting-edge version can be found at https://github.com/roed314/OMS .

The following are the needed steps to install the *darmonpoints* package. The first 3 steps are needed in order to use the overconvergent modular symbols, and the last step allows the package to be run without having *Magma*, as long as the computations are done with elliptic curves of conductor `pD`, where:

a) `D = 6` and `p \leq 59`,
b) `D = 10` and `p \leq 47`,
c) `D = 22` and `p \leq 37`.

1. Patch the Sage library::

     sage -sh
     cd $SAGE_ROOT/devel/sage
     hg qimport -P /path/to/OMS/changes_to_sagelib-5.10.patch

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

4. (Optional) Copy precomputed groups to local database::

     cp -r /path/to/precomputed_groups/* $HOME/.sage/db/


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
