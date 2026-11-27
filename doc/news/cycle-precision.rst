**Added:**

* A progress bar while the U_p matrix is built, in ``darmon_point`` (with ``progress_bar``) and ``darmon_vonk_point``.

**Fixed:**

* ``darmon_point`` failed to construct the homology cycle for ``prec >= 96`` (an assertion error), because group elements acted on the CM point with less precision than the point.
* Use ``revert`` instead of the deprecated ``reverse`` of power series.
