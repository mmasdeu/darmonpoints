# Vendored: Fundamental domains for Shimura curves (James Rickards)

Upstream: https://github.com/JamesRickards-Canada/Fundamental-domains-for-Shimura-curves
Branch `klein`, commit `79a12d3f108edce3e78d30c4a59dfc0fb01012d8`.
License: GPL-3 (see `LICENSE`).

Files:

- `fdom.c`, `fdom.h`: the library (the `afuch*` functions). The only local
  change is `#include "fdom_compat.h"` after `#include "fdom.h"` in `fdom.c`.
- `fdom_compat.h`: re-adds `ZM_trace` and `FpM_trace` for PARI < 2.18
  (upstream removed them in commit `8cdce4c` once they entered PARI).
- `eichler.gp`: Aurel Page's GP code for Eichler orders (reference for
  `darmonpoints/quatorder.py`; not loaded at runtime).

`fdom_extra.c` (plotting, LaTeX output, tuning) is not vendored; `fdom.c`
links on its own against libpari.

The Python interface is `darmonpoints/afuch.pyx`.

If you cite the use of this code, please cite J. Rickards, *Improved
computation of fundamental domains for arithmetic Fuchsian groups*,
Math. Comp. 91 (2022), and the GitHub repository.
