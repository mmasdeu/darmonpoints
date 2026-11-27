**Performance:**

* The U_p operator used by ``darmon_point`` and ``darmon_vonk_point`` is much faster and uses much less memory at high p-adic precision: the local U_p matrix is built with C kernels that exploit the filtration of overconvergent distributions, and the iteration works on differences at decreasing precision.
* ``darmon_vonk_point`` lifts cocycles through logarithms, so that U_p acts linearly.
* For 150 or more moments, integration transforms the divisor points instead of caching a moment matrix per group element.
