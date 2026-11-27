**Fixed:**

* ``darmonpoints.darmonpoints`` could not be imported with Sage 10.10, where ``is_fundamental_discriminant`` is a method of ``Integer``.
* CI runs the doctests with ``python -m sage.doctest`` (the ``sage`` launcher of recent versions has no ``-t`` option), on the installed package.
