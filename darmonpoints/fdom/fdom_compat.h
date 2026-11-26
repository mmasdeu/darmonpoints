/* Compatibility shims for PARI < 2.18 (functions removed from fdom upstream
   in commit 8cdce4c because they became part of PARI). */
#ifndef FDOM_COMPAT_H
#define FDOM_COMPAT_H
#if PARI_VERSION_CODE < PARI_VERSION(2, 18, 0)
static GEN
FpM_trace(GEN x, GEN p)
{
  long i, lx = lg(x);
  GEN t;
  if (lx < 3) return lx == 1? gen_0: gcopy(gcoeff(x, 1, 1));
  t = gcoeff(x, 1, 1);
  for (i = 2; i < lx; i++) t = Fp_add(t, gcoeff(x, i, i), p);
  return t;
}

static GEN
ZM_trace(GEN x)
{
  long i, lx = lg(x);
  GEN t;
  if (lx < 3) return lx == 1? gen_0: gcopy(gcoeff(x, 1, 1));
  t = gcoeff(x, 1, 1);
  for (i = 2; i < lx; i++) t = addii(t, gcoeff(x, i, i));
  return t;
}
#endif
#endif
