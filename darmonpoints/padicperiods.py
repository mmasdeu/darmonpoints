from itertools import product
from sage.arith.all import algdep
from sage.rings.padics.precision_error import PrecisionError
from util import *
from cohomology_arithmetic import ArithCoh, get_overconvergent_class_quaternionic
from sarithgroup import BigArithGroup
from homology import lattice_homology_cycle
from itertools import product,chain,izip,groupby,islice,tee,starmap
from sage.modules.fg_pid.fgp_module import FGP_Module,FGP_Module_class
from sage.matrix.constructor import matrix,Matrix,block_diagonal_matrix,block_matrix
from util import tate_parameter,update_progress,get_C_and_C2,getcoords,recognize_point,fwrite
from sage.misc.persist import db
from sage.rings.padics.precision_error import PrecisionError
from util import enumerate_words, discover_equation,get_heegner_params,fwrite,quaternion_algebra_invariants_from_ramification, direct_sum_of_maps
from integrals import integrate_H1
from sage.misc.misc import alarm, cancel_alarm
from sage.rings.integer_ring import ZZ

import os, datetime, ConfigParser

# load('mixed_extension.spyx')

def precompute_powers(p,q,N):
    irange = range(-N, N+1)
    pdict = {0:1, 1:p, -1:p**-1}
    for i in range(2,N+2,2):
        tmp = pdict[i-2]*q
        tmpinv = tmp**-1
        pdict[i] = tmp
        pdict[-i] = tmpinv
        pdict[i+1] = p * tmp
        pdict[-i-1] = pdict[-1] * tmpinv
    for i in range(N/2,N+1):
        pdict[2*i] = q * pdict[2*i-2]
    for i in range(1, N + 2):
        idx = i**2-i
        if not pdict.has_key(idx):
            pdict[idx] = pdict[2*i - 2] * pdict[idx - 2*i + 2]
    return pdict

# Theta functions of (25) in Teitelbaum's
# and also the other theta functions that we need to compute the lambda's according to the formulas (23)
# We sum terms until we get the result to the accuracy prec. When deciding the set of indicies over which we sum, we have made several simplifications that probably cause that we sum more terms than strictly needed for that accuracy, but this probably won't be an issue...
def Thetas(p1, p2, p3, q1,q2,q3,prec=None):
    if prec is None:
        prec = 2 * p1.parent().precision_cap()
    imax = (RR(1)/2 + RR(2*prec + RR(1)/2).sqrt()).ceiling() # note the 2!
    if imax % 2 == 1:
        imax += 1
    a = QQ(1)/QQ(2)
    b = QQ(1)/QQ(2)
    c = 0
    # Define the different conditions and term forms
    resdict = {}
    resdict['1p1m'] = resdict['1p2m'] = 0
    resdict['2p2m'] = resdict['1m2p'] = 0
    resdict['3p3m'] = resdict['2m3p'] = 0
    resdict['2p3m'] = resdict['3m1p'] = resdict['3p1m'] = 0
    res = 0
    assert imax > 0
    jdict = {}
    p1dict = {}
    p3dict = {}
    p2dict = precompute_powers(p2,q2,imax)
    for i in xrange(-imax,imax+1):
        newjmax = RR(2*prec - .25 - i**2 + RR(i).abs())
        if newjmax >= 0:
            newjmax = (newjmax.sqrt()+.5).ceiling()
            jdict[i] = newjmax
            jrange = range(-newjmax,newjmax+1)
            jlist = list(set([j**2-j for j in jrange] + [j for j in jrange]).difference(set(p1dict.keys())))
            klist = list(set([(i-j)**2-(i-j) for j in jrange] + [(i-j) for j in jrange] + [(i-j)**2-(i-j) for j in jrange]).difference(set(p3dict.keys())))
            for j in jlist:
                tmp = q1**QQ(j/2).floor()
                if j % 2 == 1:
                    tmp *= p1
                p1dict[j] = tmp
            for k in klist:
                tmp = q3**QQ(k/2).floor()
                if k % 2 == 1:
                    tmp *= p3
                p3dict[k] = tmp
    for i,jmax in jdict.iteritems():
        for j in xrange(-jmax,jmax + 1):
            P = p1dict[j**2-j] * p2dict[i**2-i] * p3dict[(i-j)**2-(i-j)]
            p11 = p1dict[j]
            p22 = p2dict[i]
            p33 = p3dict[i-j]
            a = p33 * P
            p2l_inv_p1l_inv_term = a
            p22p11 = p22 * p11
            newterm = p22p11 * a
            b = p22p11 * P
            p2lp3l_term = p22 * p33**2 * b
            p1lp3l_inv_term = p11 * b

            resdict['1p2m'] += p2l_inv_p1l_inv_term
            resdict['2p3m'] += p2lp3l_term
            resdict['3p1m'] += p1lp3l_inv_term
            if j % 2 == 0:
                resdict['1p1m'] += newterm
                resdict['2m3p'] += p2lp3l_term
            else:
                resdict['1p1m'] -= newterm
                resdict['2m3p'] -= p2lp3l_term
            if i % 2 == 0:
                resdict['2p2m'] += newterm
                resdict['3m1p'] += p1lp3l_inv_term
            else:
                resdict['2p2m'] -= newterm
                resdict['3m1p'] -= p1lp3l_inv_term
            if (i-j) % 2 == 0:
                resdict['1m2p'] += p2l_inv_p1l_inv_term
                resdict['3p3m'] += newterm
            else:
                resdict['1m2p'] -= p2l_inv_p1l_inv_term
                resdict['3p3m'] -= newterm
    return resdict

def Theta(p1, p2, p3, version, prec=None):
    if prec is None:
        prec = 2 * p1.parent().precision_cap()
    imax = (RR(1)/2 + RR(2*prec + RR(1)/2).sqrt()).ceiling() # note the 2!
    a = QQ(1)/QQ(2)
    b = QQ(1)/QQ(2)
    c = 0
    # print 'Entering Theta %s %s %s'%(a,b,c)
    # Define the different conditions and term forms
    if version is None:
        condition = lambda i,j: b*(i**2-ZZ(i).abs()) + a*(j**2-ZZ(j).abs()) + c*((i-j)**2 - ZZ(i-j).abs())
        resdict = {}
        resdict['1p1m'] = resdict['1p2m'] = 0
        resdict['2p2m'] = resdict['1m2p'] = 0
        resdict['3p3m'] = resdict['2m3p'] = 0
        resdict['2p3m'] = resdict['3m1p'] = resdict['3p1m'] = 0
    elif version == '1p1m':
        condition = lambda i,j: b*i**2 + a*j**2 + c*(i-j)**2
        term = lambda i,j: (-1)**j
    elif version == '1p2m':
        condition = lambda i,j:  b*(i**2-i) + a*(j**2-j) + c*(i-j)**2
        term = lambda i,j: p2**(-i)*p1**(-j)
    elif version == '2p2m':
        condition = lambda i,j: b*i**2 + a*j**2 + c*(i-j)**2
        term = lambda i,j: (-1)**i
    elif version == '1m2p':
        condition = lambda i,j: b*(i**2-i) + a*(j**2-j) + c*(i-j)**2
        term = lambda i,j: p2**(-i)*p1**(-j)*(-1)**(i+j)
    elif version == '3p3m':
        condition = lambda i,j: b*i**2 + a*j**2 + c*(i-j)**2
        term = lambda i,j: (-1)**(i+j)
    elif version == '2m3p':
        condition = lambda i,j: b*(i**2+i) + a*j**2 + c*((i-j)**2+(i-j))
        term = lambda i,j: p2**(i)*p3**((i-j))*(-1)**j
    elif version == '2p3m':
        condition = lambda i,j: b*(i**2+i) + a*j**2 + c*((i-j)**2+(i-j))
        term = lambda i,j: p2**(i)*p3**((i-j))
    elif version == '3m1p':
        condition = lambda i,j: b*i**2 + a*(j**2+j) + c*((i-j)**2+(j-i))
        term = lambda i,j: p1**(j)*p3**((j-i))*(-1)**i
    elif version == '3p1m':
        condition = lambda i,j:  b*i**2 + a*(j**2+j) + c*((i-j)**2+(j-i))
        term = lambda i,j: p1**(j)*p3**((j-i))
    else:
        raise ValueError("Wrong version? version = %s"%version)
    res = 0
    assert imax > 0
    for i in xrange(-imax,imax + 1):
        jmax = RR(2*prec - .25 - i**2 + RR(i).abs())
        if jmax < 0:
            continue
        jmax = (jmax.sqrt()+.5).ceiling()
        for j in xrange(-jmax,jmax + 1):
            newterm = p2**(i**2) * p1**(j**2) * p3**((i-j)**2)
            if version is None:
                p1l = p1**j
                p2l = p2**i
                p3l = p3**(i-j)
                p2l_inv_p1l_inv_term = newterm * (p2l*p1l)**-1
                p2lp3l_term = newterm * p2l * p3l
                p1lp3l_inv_term = newterm * p1l * p3l**-1

                resdict['1p1m'] += newterm * (-1)**j
                resdict['1p2m'] += p2l_inv_p1l_inv_term
                resdict['2p2m'] += newterm * (-1)**i
                resdict['1m2p'] += p2l_inv_p1l_inv_term * (-1)**(i+j)
                resdict['3p3m'] += newterm * (-1)**(i+j)
                resdict['2m3p'] += p2lp3l_term * (-1)**j
                resdict['2p3m'] += p2lp3l_term
                resdict['3m1p'] += p1lp3l_inv_term * (-1)**i
                resdict['3p1m'] += p1lp3l_inv_term
            else:
                res += newterm * term(i,j)
    return res

def lambdavec(p1, p2, p3, prec = None, theta = None, prec_pseries = None):
    if theta is None:
        assert prec is not None
        th = Thetas(p1,p2,p3,prec = prec)
    else:
        th = theta

    num = th['3p3m'] * th['2m3p']
    den = th['2p2m'] * th['2p3m']
    if prec_pseries is not None:
        try:
            den.parent()._bg_ps_ring().set_default_prec(prec_pseries)
        except AttributeError:
            pass
    l1 = (num/den)**2
    num = th['1p1m'] * th['3m1p']
    den = th['3p3m'] * th['3p1m']
    l2 = (num/den)**2
    num = th['2p2m']
    num,rem = num.quo_rem(1-p3)
    assert rem == 0
    num *= th['1m2p']
    den = th['1p1m']
    den,rem = den.quo_rem(1+p3)
    assert rem == 0
    den *= th['1p2m']
    l3 = num/den
    l3 *= l3
    return matrix(3,1,[l1,l2,l3])

def lambdavec_padic(p1, p2, p3,q1,q2,q3,prec = None):
    th = Thetas(p1,p2,p3, q1,q2,q3,prec)
    num = th['3p3m'] * th['2m3p']
    den = th['2p2m'] * th['2p3m']
    l1 = (num/den)**2
    num = th['1p1m'] * th['3m1p']
    den = th['3p3m'] * th['3p1m']
    l2 = (num/den)**2
    num = th['2p2m'] * th['1m2p'] / (1-p3) # Watch
    den = th['1p1m'] * th['1p2m'] / (1+p3)
    l3 = (num/den)**2
    return matrix(3,1,[l1,l2,l3])

def xvec(p1, p2, p3, prec):
    if p1.valuation() < 0 or p2.valuation() < 0 or p3.valuation() < 0:
        raise RuntimeError('1')
    if sum(1 for u in [p1,p2,p3] if u.valuation() == 0) > 1:
        raise RuntimeError('2')
    if not ( p1.valuation() > 0 and p2.valuation() > 0 and p3.valuation() >= 0):
        raise RuntimeError('3')
    l1,l2,l3 = lambdavec(p1,p2,p3,prec).list()
    x3 = l3 * ((p3-1)/(p3+1))**2
    den = l2
    try:
        den.parent()._bg_ps_ring().set_default_prec(prec)
    except AttributeError:
        pass
    x2 = 1 - 1/den
    den = 1-l1
    try:
        den.parent()._bg_ps_ring().set_default_prec(prec)
    except AttributeError:
        pass
    x1 = 1/den
    return (x1,x2,x3)

def xvec_padic(p1, p2, p3,q1,q2,q3,prec = None):
    if p1.valuation() < 0 or p2.valuation() < 0 or p3.valuation() < 0:
        raise RuntimeError('1')
    if sum(1 for u in [p1,p2,p3] if u.valuation() == 0) > 1:
        raise RuntimeError('2')
    if not ( p1.valuation() > 0 and p2.valuation() > 0 and p3.valuation() >= 0):
        raise RuntimeError('3')
    l1,l2,l3 = lambdavec_padic(p1,p2,p3,q1,q2,q3,prec).list()
    return (1/(1-l1),1 - 1/l2,l3 * (1-(4*p3)/(q3+2*p3+1)) )

def igusa_clebsch_absolute_from_half_periods(p1, p2, p3, q1,q2,q3,prec = None, padic = True):
    I2, I4, I6, I10 = igusa_clebsch_from_half_periods(p1, p2, p3, q1,q2,q3,prec=prec, padic=padic)
    return I2**5/I10,I2**3*I4/I10,I2**2*I6/I10

def igusa_clebsch_from_half_periods(p1, p2, p3, q1, q2, q3, prec=None, padic=True):
    if padic or prec is None:
        return igusa_clebsch_from_xvec(xvec_padic(p1, p2, p3, q1, q2, q3, prec))
    else:
        return igusa_clebsch_from_xvec(xvec(p1, p2, p3, prec))

def igusa_clebsch_absolute_from_xvec(xvec):
    I2, I4, I6, I10 = igusa_clebsch_from_xvec(xvec)
    return I2**5/I10,I2**3*I4/I10,I2**2*I6/I10

def I2_inv_from_xvec(xvec):
    x1, x2, x3 = xvec
    x12, x22, x32 = x1 * x1, x2 * x2, x3 * x3
    return 6*((x12+1)*(x22+x32+1) + x22*x32 -1) + 12*x1*x2*x3 -\
        4*( x1*(x2*x3*(x1+x2+x3) + x1*(x2+x3) + x22 + x2) +  x3*(x22 + x3*(x1 + x2) + x1 + x2) )

def j1_inv_from_xvec(xvec):
    x1, x2, x3 = xvec
    x12, x22, x32 = x1 * x1, x2 * x2, x3 * x3
    I2 = 6*x12*x22 - 4*x12*x2*x3 - 4*x1*x22*x3 + 6*x12*x32 - 4*x1*x2*x32 + 6*x22*x32 - 4*x12*x2 - 4*x1*x22 - 4*x12*x3 + 12*x1*x2*x3 - 4*x22*x3 - 4*x1*x32 - 4*x2*x32 + 6*x12 - 4*x1*x2 + 6*x22 - 4*x1*x3 - 4*x2*x3 + 6*x32
    I10 = x12*x22*x32 * ((1-x1)*(1-x2)*(1-x3)*(x1-x2)*(x1-x3)*(x2-x3))**2
    return I2**5/I10

def igusa_clebsch_from_xvec(xvec):
    x1, x2, x3 = xvec
    x12, x22, x32 = x1 * x1, x2 * x2, x3 * x3
    x13, x23, x33 = x1 * x12, x2 * x22, x3 * x32
    x14, x24, x34 = x1 * x13, x2 * x23, x3 * x33
    x15, x25, x35 = x1 * x14, x2 * x24, x3 * x34
    x16, x26, x36 = x1 * x15, x2 * x25, x3 * x35
    x17, x27, x37 = x1 * x16, x2 * x26, x3 * x36
    x18, x28, x38 = x1 * x17, x2 * x27, x3 * x37

    I2 = 6*x12*x22 - 4*x12*x2*x3 - 4*x1*x22*x3 + 6*x12*x32 - 4*x1*x2*x32 + 6*x22*x32 - 4*x12*x2 - 4*x1*x22 - 4*x12*x3 + 12*x1*x2*x3 - 4*x22*x3 - 4*x1*x32 - 4*x2*x32 + 6*x12 - 4*x1*x2 + 6*x22 - 4*x1*x3 - 4*x2*x3 + 6*x32
    I4 = 4*x14*x22*x32 - 4*x13*x23*x32 + 4*x12*x24*x32 - 4*x13*x22*x33 - 4*x12*x23*x33 + 4*x12*x22*x34 - 4*x14*x22*x3 + 4*x13*x23*x3 - 4*x12*x24*x3 - 4*x14*x2*x32 + 4*x13*x22*x32 + 4*x12*x23*x32 - 4*x1*x24*x32 + 4*x13*x2*x33 + 4*x12*x22*x33 + 4*x1*x23*x33 - 4*x12*x2*x34 - 4*x1*x22*x34 + 4*x14*x22 - 4*x13*x23 + 4*x12*x24 - 4*x14*x2*x3 + 4*x13*x22*x3 + 4*x12*x23*x3 - 4*x1*x24*x3 + 4*x14*x32 + 4*x13*x2*x32 - 24*x12*x22*x32 + 4*x1*x23*x32 + 4*x24*x32 - 4*x13*x33 + 4*x12*x2*x33 + 4*x1*x22*x33 - 4*x23*x33 + 4*x12*x34 - 4*x1*x2*x34 + 4*x22*x34 - 4*x13*x22 - 4*x12*x23 + 4*x13*x2*x3 + 4*x12*x22*x3 + 4*x1*x23*x3 - 4*x13*x32 + 4*x12*x2*x32 + 4*x1*x22*x32 - 4*x23*x32 - 4*x12*x33 + 4*x1*x2*x33 - 4*x22*x33 + 4*x12*x22 - 4*x12*x2*x3 - 4*x1*x22*x3 + 4*x12*x32 - 4*x1*x2*x32 + 4*x22*x32
    I6 =8*x16*x24*x32 - 8*x15*x25*x32 + 8*x14*x26*x32 - 8*x16*x23*x33 - 4*x15*x24*x33 - 4*x14*x25*x33 - 8*x13*x26*x33 + 8*x16*x22*x34 - 4*x15*x23*x34 + 24*x14*x24*x34 - 4*x13*x25*x34 + 8*x12*x26*x34 - 8*x15*x22*x35 - 4*x14*x23*x35 - 4*x13*x24*x35 - 8*x12*x25*x35 + 8*x14*x22*x36 - 8*x13*x23*x36 + 8*x12*x24*x36 - 8*x16*x24*x3 + 8*x15*x25*x3 - 8*x14*x26*x3 - 4*x16*x23*x32 + 2*x15*x24*x32 + 2*x14*x25*x32 - 4*x13*x26*x32 - 4*x16*x22*x33 + 40*x15*x23*x33 - 28*x14*x24*x33 + 40*x13*x25*x33 - 4*x12*x26*x33 - 8*x16*x2*x34 + 2*x15*x22*x34 - 28*x14*x23*x34 - 28*x13*x24*x34 + 2*x12*x25*x34 - 8*x1*x26*x34 + 8*x15*x2*x35 + 2*x14*x22*x35 + 40*x13*x23*x35 + 2*x12*x24*x35 + 8*x1*x25*x35 - 8*x14*x2*x36 - 4*x13*x22*x36 - 4*x12*x23*x36 - 8*x1*x24*x36 + 8*x16*x24 - 8*x15*x25 + 8*x14*x26 - 4*x16*x23*x3 + 2*x15*x24*x3 + 2*x14*x25*x3 - 4*x13*x26*x3 + 24*x16*x22*x32 - 28*x15*x23*x32 + 32*x14*x24*x32 - 28*x13*x25*x32 + 24*x12*x26*x32 - 4*x16*x2*x33 - 28*x15*x22*x33 - 4*x14*x23*x33 - 4*x13*x24*x33 - 28*x12*x25*x33 - 4*x1*x26*x33 + 8*x16*x34 + 2*x15*x2*x34 + 32*x14*x22*x34 - 4*x13*x23*x34 + 32*x12*x24*x34 + 2*x1*x25*x34 + 8*x26*x34 - 8*x15*x35 + 2*x14*x2*x35 - 28*x13*x22*x35 - 28*x12*x23*x35 + 2*x1*x24*x35 - 8*x25*x35 + 8*x14*x36 - 4*x13*x2*x36 + 24*x12*x22*x36 - 4*x1*x23*x36 + 8*x24*x36 - 8*x16*x23 - 4*x15*x24 - 4*x14*x25 - 8*x13*x26 - 4*x16*x22*x3 + 40*x15*x23*x3 - 28*x14*x24*x3 + 40*x13*x25*x3 - 4*x12*x26*x3 - 4*x16*x2*x32 - 28*x15*x22*x32 - 4*x14*x23*x32 - 4*x13*x24*x32 - 28*x12*x25*x32 - 4*x1*x26*x32 - 8*x16*x33 + 40*x15*x2*x33 - 4*x14*x22*x33 + 48*x13*x23*x33 - 4*x12*x24*x33 + 40*x1*x25*x33 - 8*x26*x33 - 4*x15*x34 - 28*x14*x2*x34 - 4*x13*x22*x34 - 4*x12*x23*x34 - 28*x1*x24*x34 - 4*x25*x34 - 4*x14*x35 + 40*x13*x2*x35 - 28*x12*x22*x35 + 40*x1*x23*x35 - 4*x24*x35 - 8*x13*x36 - 4*x12*x2*x36 - 4*x1*x22*x36 - 8*x23*x36 + 8*x16*x22 - 4*x15*x23 + 24*x14*x24 - 4*x13*x25 + 8*x12*x26 - 8*x16*x2*x3 + 2*x15*x22*x3 - 28*x14*x23*x3 - 28*x13*x24*x3 + 2*x12*x25*x3 - 8*x1*x26*x3 + 8*x16*x32 + 2*x15*x2*x32 + 32*x14*x22*x32 - 4*x13*x23*x32 + 32*x12*x24*x32 + 2*x1*x25*x32 + 8*x26*x32 - 4*x15*x33 - 28*x14*x2*x33 - 4*x13*x22*x33 - 4*x12*x23*x33 - 28*x1*x24*x33 - 4*x25*x33 + 24*x14*x34 - 28*x13*x2*x34 + 32*x12*x22*x34 - 28*x1*x23*x34 + 24*x24*x34 - 4*x13*x35 + 2*x12*x2*x35 + 2*x1*x22*x35 - 4*x23*x35 + 8*x12*x36 - 8*x1*x2*x36 + 8*x22*x36 - 8*x15*x22 - 4*x14*x23 - 4*x13*x24 - 8*x12*x25 + 8*x15*x2*x3 + 2*x14*x22*x3 + 40*x13*x23*x3 + 2*x12*x24*x3 + 8*x1*x25*x3 - 8*x15*x32 + 2*x14*x2*x32 - 28*x13*x22*x32 - 28*x12*x23*x32 + 2*x1*x24*x32 - 8*x25*x32 - 4*x14*x33 + 40*x13*x2*x33 - 28*x12*x22*x33 + 40*x1*x23*x33 - 4*x24*x33 - 4*x13*x34 + 2*x12*x2*x34 + 2*x1*x22*x34 - 4*x23*x34 - 8*x12*x35 + 8*x1*x2*x35 - 8*x22*x35 + 8*x14*x22 - 8*x13*x23 + 8*x12*x24 - 8*x14*x2*x3 - 4*x13*x22*x3 - 4*x12*x23*x3 - 8*x1*x24*x3 + 8*x14*x32 - 4*x13*x2*x32 + 24*x12*x22*x32 - 4*x1*x23*x32 + 8*x24*x32 - 8*x13*x33 - 4*x12*x2*x33 - 4*x1*x22*x33 - 8*x23*x33 + 8*x12*x34 - 8*x1*x2*x34 + 8*x22*x34
    I10 = x12*x22*x32 * ((1-x1)*(1-x2)*(1-x3)*(x1-x2)*(x1-x3)*(x2-x3))**2
    return I2, I4, I6, I10

# computes the p-adic L-invariant
# A = <gamma_1,gamma_1>
# B = <gamma_1,gamma_2>
# D = <gamma_2,gamma_2>
# Tmatrix is the matrix of the T_ell operator with respect to the basis (gamma_1,gamma_2)
# the output is (a,b), where L_p = a + bT
def p_adic_l_invariant(A,B, Tmatrix):
    return p_adic_l_invariant_additive(A.log(0),B.log(0),A.ordp(),B.ordp(),Tmatrix)

def p_adic_l_invariant_additive(logA,logB, alpha, beta, Tmatrix):
    K = logA.parent()
    logA, logB = K(logA), K(logB)
    x,y,z,t = Tmatrix.change_ring(K).list()
    M = Matrix(K,2,2,[alpha,x*alpha+z*beta,beta, y*alpha+t*beta])
    n  = Matrix(K,2,1,[logA, logB])
    return M.solve_right(n).list()

def qlogs_from_Lp_and_ords(a,b,Tmatrix,q1ord, q2ord, q3ord):
    K = a.parent()
    ordA = q2ord + q3ord
    ordB = -q3ord
    ordD = q1ord + q3ord
    bord = matrix(K,2,2,[ordA,ordB,ordB,ordD]) * Tmatrix
    M = Matrix(K,3,2,[ordA, bord[0,0], ordB, bord[0,1],ordD,bord[1,1]])
    logA, logB, logD = (M * matrix(K,2,1,[a,b])).list()
    return logB + logD, logA + logB, -logB

def all_possible_qords(Tmatrix,N,initial = None):
    # Find linear equation from matrix
    x, y, z, t = [ZZ(o) for o in Tmatrix.list()]
    r = x+y-z-t
    ans = set([])
    # Note: since we assume that the minimal polynomial is irreducible,
    # we already know that z*y*r != 0

    # Know that q1^z = q2^y q3^r
    for ordq2, ordq3 in product(range(N+1),repeat = 2):
        ordq1 = ZZ(y * ordq2 + r * ordq3)
        if ordq1 % z != 0:
            continue
        ordq1 /= z
        ordtup = [ordq1,ordq2,ordq3]
        if all([o >= 0 for o in ordtup]) and len([o for o in ordtup if o == 0]) <= 1:
            ans = ans.union(ans,set([(ordq1, ordq2, ordq3)]))
    # Know that q2^y = q1^z q3^-r
    for ordq1, ordq3 in product(range(N+1),repeat = 2):
        ordq2 = ZZ(z * ordq1 - r * ordq3)
        if ordq2 % y != 0:
            continue
        ordq2 /= y
        ordtup = [ordq1,ordq2,ordq3]
        if all([o >= 0 for o in ordtup]) and len([o for o in ordtup if o == 0]) <= 1:
            ans = ans.union(ans,set([(ordq1, ordq2, ordq3)]))
    # Know that q3^r = q1^z q2^-y
    for ordq1, ordq2 in product(range(N+1),repeat = 2):
        ordq3 = ZZ(z * ordq1 - y * ordq2)
        if ordq3 % r != 0:
            continue
        ordq3 /= r
        ordtup = [ordq1,ordq2,ordq3]
        if all([o >= 0 for o in ordtup]) and len([o for o in ordtup if o == 0]) <= 1:
            ans = ans.union(ans,set([(ordq1, ordq2, ordq3)]))
    tmp = sorted(list(ans),key = lambda x: x[0]+x[1]+x[2])
    t0 = 0
    if initial is not None:
        try:
            t0 = tmp.index(initial)
        except ValueError:
            t0 = 0
    return tmp[t0:]

def recognize_invariant(j_invariant,base = None,threshold = None,prec = None, outfile = None, twopowlist = None, return_all = False):
    if threshold is None:
        threshold = .9
    if base is None:
        base = QQ
    if twopowlist is None:
        twopowlist = [0]
    deg = base.degree()
    Kp = j_invariant.parent()
    threshold = threshold * RR(Kp.prime()).log(10)
    for i in twopowlist:
        twopow = 2**i
        fx = algdep(j_invariant/twopow,deg)
        hfx = height_polynomial(fx)
        trash_height = threshold * j_invariant.precision_relative()
        if hfx < trash_height:
            ans = [twopow * o for o,_ in fx.change_ring(base).roots()]
            if len(ans) > 0:
                if return_all:
                    return ans
                else:
                    return ans[0]
    raise ValueError('Unrecognized')

def teichmuller_system(self):
    return [self.teichmuller(self(i).lift_to_precision(self.precision_cap())) for i in self.residue_field() if i != 0]

def take_to_Qp(x, tolerance = None):
    if hasattr(x,'trace'):
        ans = x.trace()/x.parent().degree()
    else:
        ans = x.trace_absolute()/x.parent().absolute_degree()
    ordp = (x.parent()(ans) - x).ordp()
    if tolerance is not None and ordp - x.ordp() < tolerance:
        raise ValueError('Input does not look p-adic')
    ans = ans.add_bigoh(ordp.floor())
    return ans

def j1_inv_padic_from_xvec(xvec, prec, threshold = None):
    if threshold is None:
        tol = None
    else:
        tol = threshold * prec
    j1 = j1_inv_from_xvec(xvec)
    try:
        return take_to_Qp(j1,tol)
    except ValueError:
        return None

def j1_inv_padic_from_half_periods(a, b, c, q1,q2,q3,prec, threshold=None):
    return j1_inv_padic_from_xvec(xvec_padic(a,b,c,q1,q2,q3,prec),prec,threshold)

def I2_inv_padic_from_xvec(xvec,prec,threshold=None):
    if threshold is None:
        tol = None
    else:
        tol = threshold * prec
    I2 = I2_inv(*xvec)
    try:
        return take_to_Qp(I2,tol)
    except ValueError:
        return None

def I2_inv_padic_from_half_periods(a, b, c, q1,q2,q3,prec,threshold=None):
    return I2_inv_padic_from_xvec(xvec_padic(a,b,c,q1,q2,q3,prec),prec,threshold)

def absolute_igusa_padic_from_xvec(xvec,prec, threshold = None):
    j1,j2,j3 = igusa_clebsch_absolute_from_xvec(xvec)
    if threshold is None:
        tol = None
    else:
        tol = threshold * prec
    try:
        j1 = take_to_Qp(j1,tol)
        j2 = take_to_Qp(j2,tol)
        j3 = take_to_Qp(j3,tol)
    except ValueError:
        return None, None, None
    return j1, j2, j3

def absolute_igusa_padic_from_half_periods(p1,p2,p3,q1,q2,q3,prec,threshold = None):
    xvec = xvec_padic(p1,p2,p3,q1,q2,q3,prec)
    j1,j2,j3 = igusa_clebsch_absolute_from_xvec(xvec)
    if threshold is None:
        tol = None
    else:
        tol = threshold * prec
    try:
        j1 = take_to_Qp(j1,tol)
        j2 = take_to_Qp(j2,tol)
        j3 = take_to_Qp(j3,tol)
    except ValueError:
        return None, None, None
    return j1, j2, j3

def multiplicative_scalar_product(b, v):
    ans = 1
    for bi,vi in zip(b,v):
        ans *= vi**ZZ(bi)
    return ans

def left_multiply_multiplicative(B, V): # V^B
    ans = V.parent()(0)
    for i, j in product(range(ans.nrows()),range(ans.ncols())):
        ans[i,j] = multiplicative_scalar_product(B.row(i).list(),V.column(j).list())
    return ans

def right_multiply_multiplicative(W, A):
    return left_multiply_multiplicative(A.transpose(),W.transpose()).transpose()

def generate_matlists(Lambdalist,mat_coeffs_range = 3):
    mlistX = []
    mlistY = []
    for a,b,c,d in product(range(-mat_coeffs_range,mat_coeffs_range+1),repeat = 4):
        m = matrix(ZZ,2,2,[a,b,c,d])
        if m.determinant() != 0:
            mlistY.append(m)
            if m.determinant().abs() in [1,2]:
                mlistX.append(m)
    mlistX = sorted(mlistX,key=lambda x:max([o.abs() for o in x.list()]))
    mlistY = sorted(mlistY,key=lambda x:max([o.abs() for o in x.list()]))
    mlistYYL = []
    for Y in mlistY:
        for Lambda in Lambdalist:
            YL = left_multiply_multiplicative(Y, Lambda)
            mlistYYL.append((Y,YL))
    for X,YYL in product(mlistX,mlistYYL):
        Y, YL = YYL
        delta = X.determinant()
        YLXinv = right_multiply_multiplicative(YL, X.adjoint())
        if YLXinv[0,1] != YLXinv[1,0]:
            continue
        yield (X,Y,YLXinv,delta)
    # return sorted(all_mats, key = lambda x: max([o.abs() for o in x[0].list() + x[1].list()]))

def build_Lambdalist_from_AB(A,B,T, scaling):
    # T is the matrix of Hecke acting on Homology
    try:
        x,y,z,t = T.list()
    except AttributeError:
        x,y,z,t = T
    alpha = ZZ(z)/ZZ(y)
    beta = ZZ(t-x)/ZZ(y)
    d = lcm(alpha.denominator(),beta.denominator())
    alpha, beta = ZZ(d*alpha), ZZ(d*beta)
    ans = []
    K = A.parent()
    for A0, B0 in product(our_nroot(A,scaling,return_all=True),our_nroot(B,scaling,return_all=True)):
        for B1 in our_nroot(B0, d,return_all=True):
            ans.append(Matrix(K,2,2,[A0,B0,B1**alpha,A0*B1**beta]))
    return ans

def find_igusa_invariants_from_AB(A,B,T,scaling, prec, **kwargs):
    global success_list
    Lambdalist = build_Lambdalist_from_AB(A,B,T, scaling)
    K0 = Lambdalist[0].parent().base_ring()
    p = K0.prime()
    phi = kwargs.get('phi',lambda x:Qp(p,prec)(x))
    mat_coeffs_range = kwargs.get('mat_coeffs_range',3)
    base = kwargs.setdefault('base',QQ)
    if kwargs.has_key('list_I10'):
        list_I10 = kwargs['list_I10']
        kwargs['list_I10_padic'] = [phi(o) for o in list_I10]
    # matlists = kwargs.get('matlists',generate_matlists(Lambdalist,mat_coeffs_range))
    outfile = kwargs.get('outfile')
    K = QuadExt(K0,p)
    total_tests = '?' #len(matlists)
    fwrite('# Starting search for Igusa invariants. Number of tests = %s'%(total_tests), outfile)
    ntests = 0
    success_list = []
    for X, Y, YLXinv, delta in generate_matlists(Lambdalist,mat_coeffs_range):
        data = 'X = %s, Y = %s'%(X.list(),Y.list())
        ntests += 1
        if ntests % 1000 == 0:
            fwrite('# num_tests = %s / %s (successes = %s)'%(ntests, total_tests, len(success_list)), outfile)
        Ag,Bg,_,Dg = YLXinv.list()
        q1inv = (Bg * Dg)**-1
        q2inv = (Bg * Ag)**-1
        q3inv = Bg
        try:
            p1, p2, p3 = K(q1inv).sqrt(), K(q2inv).sqrt(), K(q3inv).sqrt()
            xvec = xvec_padic(p1, p2, p3, q1inv, q2inv, q3inv, prec)
        except (ValueError,RuntimeError,PrecisionError):
            continue
        out_str = check_generic(xvec,prec,data,**kwargs)
        if out_str != '':
            success_list.append(out_str)
            fwrite('# Success! data = %s'%out_str, outfile)
    return success_list

def find_igusa_invariants(a, b, T, embedding, prec = None, outfile = None, list_I10 = None, Pgen = None, N = 6, cheatjs = None, parallelize = True):
    fwrite('# Trying to recognize invariants...',outfile)
    Pring = embedding.domain()
    if prec is None:
        prec = a.parent().precision_cap()
    Tlist = []
    fT = T.charpoly()
    fT_trace = -fT.list()[1]
    for x0,y,z in product(range(-N, N+1), range(-N, N+1), range(-N, N+1)):
        t = fT_trace - x0
        if x0*t - y*z == fT.list()[0]:
            M = matrix(ZZ,2,2,[x0,y,z,t])
            assert fT == M.charpoly()
            Tlist.append(M)
    Tlist = sorted(Tlist, key = lambda x: max(x[0,0].abs(), x[0,1].abs(), x[1,0].abs(), x[1,1].abs()))
    for ii, tt in enumerate(Tlist):
        fwrite('# Doing matrix %s / %s ( = %s)'%(ii,len(Tlist),tt.list()),outfile)
        Lp = a + b * tt
        inp_vec = [(Lp, ordmat, prec, Pring, cheatjs, embedding, 3, list_I10, Pgen, outfile) for ordmat in all_possible_ordmats(Lp,20)]

        num_inpts = len(inp_vec)
        jj = 0
        if parallelize:
            for inpt, outt in parallel(find_igusa_invariants_from_L_inv)(inp_vec):
                jj += 1
                if outt != 'Nope' and outt != '' and 'indistinguishable' not in outt and 'Error' not in outt:
                    fwrite('# (%s/%s) %s %s %s %s'%(jj, num_inpts, str(tt.list()), str(inpt[0][0].list()),str(inpt[0][1].list()),str(outt)), outfile)
                elif outt != 'Nope':
                    fwrite('# (%s/%s) (%s)...Out: %s'%(jj, num_inpts, inpt[0][1].list(),str(outt)), outfile)
        else:
            for inpt in inp_vec:
                outt = find_igusa_invariants_from_L_inv(*inpt)
                jj += 1
                if outt != 'Nope' and outt != '' and 'indistinguishable' not in outt and 'Error' not in outt:
                    fwrite('# (%s/%s) %s %s %s %s'%(jj, num_inpts, str(tt.list()), str(inpt[0][0].list()),str(inpt[0][1].list()),str(outt)), outfile)
                elif outt != 'Nope':
                    fwrite('# (%s/%s) (%s)...Out: %s'%(jj, num_inpts, inpt[0][1].list(),str(outt)), outfile)


def check_generic(xvec, prec, data,  **kwargs):
    if kwargs.has_key('cheatjs'):
        return check_cheatjs(xvec,prec,data, **kwargs)
    elif kwargs.has_key('list_I10'):
        return check_absoluteinvs(xvec,prec,data, **kwargs) + check_listI10(xvec,prec,data, **kwargs)
    else:
        return check_absoluteinvs(xvec,prec,data, **kwargs)

def check_cheatjs(xvec,prec,data, **kwargs):
    cheatjs = kwargs.get('cheatjs')
    minval = kwargs.get('minval',5)
    threshold = kwargs.get('threshold')
    try:
        j1 = j1_inv_padic_from_xvec(xvec, prec, threshold = 0.8)
        if j1 is None:
            return ''
    except (ValueError,RuntimeError,PrecisionError):
        return ''
    if (j1 - cheatjs[0]).valuation() > minval:
        j1, j2, j3 = absolute_igusa_padic_from_xvec(xvec,prec)
        vals = [(u-v).valuation() - u.valuation() for u,v in zip([j1,j2,j3],cheatjs)]
        if all([o > minval for o in vals]):
            out_str = '# Success !! -> %s, valuation=%s'%(data,min(vals))
            return out_str
    return ''

def check_absoluteinvs(xvec,prec,data, **kwargs):
    base = kwargs.get('base')
    threshold = kwargs.get('threshold')
    outfile = kwargs.get('outfile')
    try:
        j1 = j1_inv_padic_from_xvec(xvec, prec, threshold = .8)
        if j1 is None:
            return ''
    except (ValueError,RuntimeError,PrecisionError):
        return ''
    try:
        j1n = recognize_invariant(j1,base = base,threshold = threshold,prec = prec,  outfile = outfile)
        fwrite('# Possible j1 = %s'%(j1n),outfile)
        j1, j2, j3 = absolute_igusa_padic_from_xvec(xvec,prec)
        j2n = recognize_invariant(j2,base = base,threshold = threshold,prec = prec,  outfile = outfile)
        fwrite('# Possible j2 = %s'%(j2n),outfile)
        j3n = recognize_invariant(j3,base = base,threshold = threshold,prec = prec,  outfile = outfile)
        fwrite('# Possible j3 = %s'%(j3n),outfile)
        out_str = '# Candidate js = %s, %s, %s (%s) jpadic = (%s, %s, %s)'%(j1n,j2n,j3n,data, j1,j2,j3)
        return out_str
    except ValueError:
        return ''

def check_listI10(xvec, prec, data, **kwargs):
    list_I10 = kwargs.get('list_I10')
    list_I10_padic = kwargs.get('list_I10_padic')
    base = kwargs.get('base')
    threshold = kwargs.get('threshold')
    outfile = kwargs.get('outfile')
    try:
        j1 = j1_inv_padic_from_xvec(xvec, prec, threshold = .8)
        if j1 is None:
            return ''
    except (ValueError,RuntimeError,PrecisionError):
        return ''
    for I10new, I10p in zip(list_I10,list_I10_padic):
        I2c_list = our_nroot( j1 * I10p, 5, return_all = True)

        for I2c in I2c_list:
            try:
                I2new = recognize_invariant(I2c,base = base,threshold = threshold,prec = prec,  outfile = outfile, twopowlist = range(10))
                fwrite('# Possible I2 = %s'%(I2new),outfile)
                j1, j2, j3 = absolute_igusa_padic_from_xvec(xvec,prec)
                I4new = recognize_invariant(j2 * I10p / I2c**3,base = base,threshold = threshold,prec = prec,  outfile = outfile, twopowlist = range(12))
                fwrite('# Possible I4 = %s'%I4new,outfile)
                I6new = recognize_invariant(j3 * I10p / I2c**2,base = base,threshold = threshold,prec = prec,  outfile = outfile, twopowlist = range(20))
                fwrite('# Possible I6 = %s'%I6new,outfile)
                out_str = '# Candidate = %s, %s, %s, %s (%s)'%(I2new,I4new,I6new,I10new,data)
                return out_str
            except ValueError:
                pass
    return ''

def frobenius_polynomial(C):
    q = len(C.base_ring())
    N1, N2 = C.count_points(2)
    ap1 = q + 1 - N1
    ap2 = q*q +1 - N2
    r = (ap1*ap1 - ap2)/2
    print 'trace = %s'%ap1
    print 'norm = %s'%(r - 2*q)
    return QQ['x']([q*q, -ap1*q, r, -ap1, 1])

def euler_factor_twodim(p,T):
    return euler_factor_twodim_tn(p, T.trace(), T.determinant())

def euler_factor_twodim_tn(q,t,n):
    return QQ['x']([q*q,-q*t,2*q+n,-t,1])

def guess_equation(code,pol,Pgen,Dgen,Npgen, Sinf = None,  sign_ap = None, prec = -1, hecke_data_init = None, working_prec = None, recognize_invariants = True, return_all = True, compute_G = True, compute_cohomology = True, abtuple = None, logfile = None, **kwargs):

    config = ConfigParser.ConfigParser()
    config.read('config.ini')
    param_dict = config_section_map(config, 'General')
    param_dict.update(config_section_map(config, 'GuessEquation'))
    param_dict.update(kwargs)
    param = Bunch(**param_dict)

    # Get general parameters
    outfile = param.outfile
    use_ps_dists = param.use_ps_dists
    use_shapiro = param.use_shapiro
    use_sage_db = param.use_sage_db
    magma_seed = param.magma_seed
    parallelize = param.parallelize
    Up_method = param.up_method
    use_magma = param.use_magma
    progress_bar = param.progress_bar
    sign_at_infinity = param.sign_at_infinity

    # Get find_curve specific parameters
    grouptype = param.grouptype
    hecke_bound = param.hecke_bound
    timeout = param.timeout

    if Up_method == "bigmatrix" and use_shapiro == True:
        import warnings
        warnings.warn('Use of "bigmatrix" for Up iteration is incompatible with Shapiro Lemma trick. Using "naive" method for Up.')
        Up_method = 'naive'

    global G, Coh, flist, hecke_data, g0, g1, Alog, Aval, Amul, Blog, Bval, Bmul, Dlog, Dval, Dmul, a, b, T, xi10, xi20, xi11, xi21, Phif
    if pol is None or pol.degree() == 1:
        F = QQ
        P = Pgen
        Pnrm = Pgen
        Pring = QQ
        D = Dgen
        Np = Npgen
        Sinv_places = []
        if abtuple is None:
            abtuple = QuaternionAlgebra(D).invariants()
        else:
            abtuple = (QQ(abtuple[0]), QQ(abtuple[1]))

        if outfile is None:
            outfile = 'periods_%s_%s_%s_%s_%s.sage'%(code,1,P,D,(P*D*Np))
    else:
        F = NumberField(pol, name = 'r')
        r = F.gen()
        P = F.ideal(Pgen)
        Pnrm = P.norm()
        Pring = P.ring()
        D = F.ideal(Dgen)
        Np = F.ideal(Npgen)
        if Sinf is None:
            Sinf = [-1 for i in F.real_places()]
        Sinf_places = [v for v,o in zip(F.real_places(prec = Infinity),Sinf) if o == -1]
        if abtuple is None:
            abtuple = quaternion_algebra_invariants_from_ramification(F,D,Sinf_places)
        else:
            abtuple = (F(abtuple[0]), F(abtuple[1]))
        if outfile is None:
            outfile = 'periods_%s_%s_%s_%s_%s.sage'%(code,F.discriminant().abs(),Pnrm,D.norm(),(P*D*Np).norm())
    if os.path.isfile(outfile):
        return 'Skipping because outfile exists'

    if Pnrm > 31:
        return 'Giving up, prime norm is too large (Pnrm = %s)'%Pnrm
    fwrite('# Starting computation for candidate %s'%str((code,pol,Pgen,Dgen,Npgen,Sinf)),outfile)
    fwrite('p = %s'%Pnrm, outfile)
    if compute_G:
        G = BigArithGroup(P,abtuple,Np,base = F, use_shapiro = use_shapiro, seed = magma_seed, outfile = outfile, use_sage_db = use_sage_db, magma = None, timeout = timeout, grouptype = grouptype, logfile = logfile)
    if compute_cohomology:
        Coh = ArithCoh(G)
        fwrite('# Computed Cohomology group',outfile)
    fwrite('# dim H^1 = %s'%Coh.dimension(),outfile)
    if hecke_data_init is not None and return_all:
        fwrite('# Warning: setting return_all to False because user passed hecke_data_init value', outfile)
        return_all = False

    if return_all:
        all_twodim_cocycles = Coh.get_twodim_cocycle(sign_at_infinity, hecke_data = hecke_data_init, bound = hecke_bound, return_all = True, outfile = outfile)
    else:
        try:
            all_twodim_cocycles = [ Coh.get_twodim_cocycle(sign_at_infinity, hecke_data = hecke_data_init, bound = hecke_bound, return_all = False, outfile = outfile) ]
        except ValueError:
            all_twodim_cocycles = []
    if len(all_twodim_cocycles) == 0:
        fwrite('# Group not attached to surface',outfile)
        fwrite('# DONE WITH COMPUTATION',outfile)
        return 'DONE'
    fwrite('# Obtained cocycles',outfile)
    for flist, hecke_data in all_twodim_cocycles:
        fwrite('Hecke data: %s'%str(hecke_data),outfile)
        g0, g1, scaling = G.get_pseudo_orthonormal_homology(flist, hecke_data = hecke_data, outfile = outfile)
        g0_shapiro, g1_shapiro = G.inverse_shapiro(g0), G.inverse_shapiro(g1)
        fwrite('# Obtained homology generators',outfile)
        if working_prec is None:
            working_prec = max([2 * prec + 10, 30])
        found = False
        while not found:
            try:
                xi10,xi20 = lattice_homology_cycle(G, g0_shapiro, working_prec)
                xi11,xi21 = lattice_homology_cycle(G, g1_shapiro, working_prec)
                found = True
            except PrecisionError:
                working_prec *= 2
                fwrite('# Raising working precision to %s and trying again'%working_prec, outfile)
        fwrite('# Defined homology cycles', outfile)
        Phif = get_overconvergent_class_quaternionic(P, flist[0], G, prec, sign_at_infinity,sign_ap,use_ps_dists = use_ps_dists,use_sage_db = use_sage_db,parallelize = parallelize,method = Up_method, progress_bar = progress_bar)
        fwrite('# Overconvergent lift completed', outfile)

        from integrals import integrate_H1
        numadd, numval, numroot = integrate_H1(G, xi10, Phif, 1, method = 'moments', prec = working_prec, twist = False, progress_bar = progress_bar, multiplicative = False, return_valuation = True)
        denadd, denval, denroot = integrate_H1(G, xi20, Phif, 1, method = 'moments', prec = working_prec, twist = True, progress_bar = progress_bar, multiplicative = False, return_valuation = True)
        Alog = take_to_Qp(numadd - denadd)
        Aval = numval - denval
        Amul = numroot / denroot
        fwrite('# Finished computation of A period', outfile)
        # A = A.add_bigoh(prec + A.valuation())
        fwrite('A0 = p**(%s) * (%s) * (%s).exp()'%(Aval, Amul, Alog), outfile)

        numadd, numval, numroot = integrate_H1(G, xi11, Phif, 1, method = 'moments', prec = working_prec, twist = False, progress_bar = progress_bar, multiplicative = False, return_valuation = True)
        denadd, denval, denroot = integrate_H1(G, xi21,Phif, 1, method = 'moments', prec = working_prec, twist = True, progress_bar = progress_bar, multiplicative = False, return_valuation = True)
        Blog = take_to_Qp(numadd - denadd)
        Bval = numval - denval
        Bmul = numroot / denroot
        fwrite('# Finished computation of B period', outfile)
        # B = B.add_bigoh(prec + B.valuation())
        fwrite('B0 = p**(%s) * (%s) * (%s).exp()'%(Bval, Bmul, Blog), outfile)

        found = False
        for ell, T0 in hecke_data:
            fwrite('ell = %s'%ell, outfile)
            fwrite('T_ell = Matrix(ZZ,2,2,%s)'%str(T0.list()), outfile)
            if T0.charpoly().is_irreducible():
                found = True
                T = T0
                fwrite('# The above is the good T', outfile)
        if not found:
            fwrite('# Good T not found...', outfile)
            return('DONE WITH ERROR')

        Dlog = Alog + T.trace()*Blog
        Dval = Aval + T.trace()*Bval
        Dmul = Amul * Bmul**(ZZ(T.trace()))
        fwrite('D0 = p**(%s) * (%s) * (%s).exp()'%(Dval, Dmul, Dlog), outfile)

        Fp = Alog.parent()
        TFp = T.change_ring(Fp)
        a, b = p_adic_l_invariant_additive(Alog, Blog, Aval, Bval, TFp)
        a = take_to_Qp(a)
        b = take_to_Qp(b)
        Lp = a + b * T
        fwrite('a = %s'%a, outfile)
        fwrite('b = %s'%b, outfile)
        fwrite('Lp = Matrix(2,2,%s)'%str(Lp.list()), outfile)
        if recognize_invariants:
               K0 = Qq(Pnrm**2, prec,names = 's')
               A = K0(take_to_Qp(Pnrm**Aval * Alog.exp() * Amul))
               B = K0(take_to_Qp(Pnrm**Bval * Blog.exp() * Bmul))
               if not param_dict.has_key('list_I10'):
                   param_dict['list_I10'] = generate_listI10(G.F, G.ideal_p*G.discriminant*G.level)
               param_dict['outfile'] = outfile
               find_igusa_invariants_from_AB(A, B, T, scaling, prec = prec, phi = G._F_to_local, **param_dict)
    fwrite('# DONE WITH COMPUTATION', outfile)
    return('DONE')

def all_possible_ordmats(Lpmat, N):
    ans = []
    for x, y, t in product(range(N+1),range(-N,N+1),range(-N,N+1)):
        if x*t == y*y:
            continue
        M = matrix(ZZ,2,2,[x,y,y,t])
        logmat = M * Lpmat
        if logmat.is_symmetric():
            ans.append(M)
    return sorted(ans, key = lambda x: max([x[0,0].abs(),x[0,1].abs(),x[1,1].abs()]))

def jacobian_matrix(fvec):
    f1, f2, f3 = fvec.list()
    x, y, z = f1.variables()
    return Matrix(3,3,[f1.derivative(x), f1.derivative(y), f1.derivative(z),f2.derivative(x), f2.derivative(y), f2.derivative(z),f3.derivative(x), f3.derivative(y), f3.derivative(z)])

def compute_lvec_and_Mlist(prec):
    R = PowerSeriesRing(QQ,names = 'p', num_gens = 3)
    p1, p2, p3 = R.gens()
    R.set_default_prec(prec)
    R._bg_ps_ring().set_default_prec(prec)
    theta = Theta(p1,p2,p3,version=None, prec = prec)
    lvec = lambdavec(p1, p2, p3, theta = theta,prec_pseries = prec)
    Mlist = compute_twisted_jacobian_data(lvec)
    lvec = [o.polynomial() for o in lvec.list()]
    save((lvec,Mlist),'lvec_and_Mlist_%s.sobj'%prec)
    return (lvec,Mlist)

def load_lvec_and_Mlist(prec):
    try:
        lvec, Mlist = load('lvec_and_Mlist_%s.sobj'%prec)
    except:
        lvec, Mlist = compute_lvec_and_Mlist(prec)
    return (lvec, Mlist)

def evaluate_twisted_jacobian_matrix(p1,p2,p3,Mlist):
    retvec = []
    for i in range(6):
        retvec.append(Mlist[i](p1,p2,p3))
    h1 = Mlist[6](p1,p2,p3)
    h2 = Mlist[7](p1,p2,p3)
    h3 = Mlist[8](p1,p2,p3)
    ll = ((1-p3)/(1+p3))**2
    h1 = ll * h1
    h2 = ll * h2
    h3 = -4*(1-p3)/(1+p3)**3 * Mlist[9](p1,p2,p3) + ll * h3
    retvec.extend([h1,h2,h3])
    return Matrix(3,3,retvec)

def compute_twisted_jacobian_data(fvec):
    f1, f2, f3 = fvec.list()
    x, y, z = f1.variables()
    Mlist = [o.polynomial() for o in [f1.derivative(x), f1.derivative(y), f1.derivative(z),f2.derivative(x), f2.derivative(y), f2.derivative(z), f3.derivative(x), f3.derivative(y), f3.derivative(z)]] + [f3.polynomial()]
    return Mlist

def find_initial_approx(L1, L2, L3, lvec):
    # Evaluates a matrix M with entries in Z[[x,y,z]] at points x0,y0,z0
    def ev(x0,y0,z0):
        return [lvec[0](x0,y0,z0), lvec[1](x0,y0,z0), ((1-z0)/(1+z0))**2 * lvec[2](x0,y0,z0)]
    K = L1.parent()
    n_tries = 0
    for V in product(product(range(K.base().prime()), repeat = 3), repeat = 3):
        n_tries += 1
        if n_tries % 100 == 0:
            print 'n_tries = %s'%n_tries
        P = [a+b*K.gen()+c*K.base().gen() for a,b,c in V]
        FP = ev(*P)
        if min([(u-v).valuation() for u,v in zip(FP,[L1,L2,L3])]) > 1/2:
            good_P = P
            print P, [(u-v).valuation() for u,v in zip(FP,[L1,L2,L3])]
    return good_P

# given a triple of lambda's returns the corresponding half periods
def HalfPeriodsInTermsOfLambdas(L1, L2, L3, lvec_and_Mlist = None, HP0 = None, prec = None, max_iters = 20):
    K = L1.parent()
    L0 = Matrix(K, 3, 1, [L1, L2, L3])
    if lvec_and_Mlist is None:
        assert prec is not None
        lvec, Mlist = load_lvec_and_Mlist(prec)
    else:
        lvec, Mlist = lvec_and_Mlist
    # Evaluates a matrix M with entries in Z[[x,y,z]] at points x0,y0,z0
    def ev(x0,y0,z0):
        return [lvec[0](x0,y0,z0), lvec[1](x0,y0,z0), ((1-z0)/(1+z0))**2 * lvec[2](x0,y0,z0)]
    if HP0 is None:
        HP0 = [K(0),K(0),K(0)]
    Pn = Matrix(K,3,1,HP0) # 0th approximation
    n_iters = 0
    while n_iters < 20:
        n_iters += 1
        Jinv = evaluate_twisted_jacobian_matrix(*Pn.list(),Mlist = Mlist).inverse()
        FPn = matrix(3,1, ev(*Pn.list()))
        Pnn = Pn - Jinv * (FPn - L0)
        print '(%s)'%n_iters, [(u-v).valuation() for u,v in zip(Pn.list(), Pnn.list())]
        if all([u == v for u,v in zip(Pn.list(), Pnn.list())]):
            return Pn
        Pn = Pnn
    raise RuntimeError,"Does not converge"

def normalize_periods(A, B, alpha, T, a, b, outfile = None):
    r'''
    alpha = (phi1, theta1)
    beta = (phi2, theta2) = -n(T) * alpha, where T is the Hecke
    operator used when computing A and B.
    T is the new hecke operator.
    '''
    # fwrite('# The following are the canonical periods (using T_ell):', outfile)
    nm = T.determinant()
    newA = A**ZZ(-b*nm) * B**ZZ(-a)
    new_norm = ZZ((a+b*T).determinant())
    new_trace = 2*a + T.trace()
    newB = B**-new_norm
    newD = newA**ZZ(-new_norm) * newB**ZZ(new_trace)

    # fwrite('A = %s'%newA, outfile)
    # fwrite('B = %s'%newB, outfile)
    # fwrite('D = %s'%newD, outfile)
    # fwrite('final_scaling = %s * scaling'%-nm*b,outfile)
    return newA,newB,newD,-nm*b*alpha


def change_period_logs(Alog,Blog,T):
    x,y,z,t = T.list()
    c00,c01,c10,c11 = Matrix(2,2,[z, -x, x*(z-y), z*z-x*t]).list()
    Alog, Blog = c00*Alog + c01*Blog, c10*Alog + c11*Blog
    Dlog = Alog + T.trace()*Blog
    return Alog, Blog, Dlog

def compare_AB_periods(Alist, Blist, T, Ag, Bg, Dg, prec, base=QQ, matlist = None):
    F = Alist[0].parent().base().prime()
    x = QQ['x'].gen()
    K0 = Qq(p**2,prec,names='r')
    K = QuadExt(K0,p)
    deg = base.degree()
    L = NumberField(T.charpoly(),names='t')
    if matlist is None:
        matlist = []
        for b,d in product(range(-2,3),repeat = 2):
            m = matrix(ZZ,2,2,[1,b,0,d])
            if m.determinant() != 0:
                matlist.append(m)

    pairs = set([])
    print 'len(Alist) = %s, len(Blist) = %s'%(len(Alist),len(Blist))
    for u, pu in sorted([(u,u.charpoly().list()[:2]) for u in L.elements_of_bounded_height(5) if u.is_integral()],key = lambda x:max(x[1][0].abs(),x[1][1].abs())):
        if not u.charpoly().is_irreducible():
            continue
        n = ZZ(pu[0])
        t = -ZZ(pu[1])
        if (t,n) in pairs:
            continue
        pairs.add((t,n))
        for A0, B0, m in product(Alist,Blist,matlist):
            a,b,c,d = m.list()
            A1log = a* A0.log(0) + b*B0.log(0)
            B1log = c * A0.log(0) + d*B0.log(0)
            D1log = -n * A1log + t * B1log

            if (A1log-Ag.log(0)).valuation() > 2 and (B1log-Bg.log(0)).valuation() > 2 and (D1log-Dg.log(0)).valuation() > 2:
                print a,b,c,d, t,n

def generate_listI10(F,N):
    r'''
    Generates a list of possible I10's, of the form:

    (+-1) * 2^i * u^j * p^k * N^2

    where i is taken in a specific range(20,25)
    and j is taken in another range(-15,16)
    and p is taken in another range(3)
    '''
    from itertools import product
    range_twopows = range(12,25)
    range_units = range(-15,16)
    range_conductor = [2]
    range_smallprimes = range(3)

    factor_list = [F(2), F(-1)] + list(F.units()) + [o.gens_reduced()[0] for o,_ in N.factor()]
    exp_ranges = [range_twopows, [-1,1]] + [range_units for _ in F.units()] + [range_conductor for o in N.factor()]
    for ell in F.primes_of_bounded_norm(5):
        factor_list.append(ell.gens_reduced()[0])
        exp_ranges.append(range_smallprimes)
    ans = []
    for v in product(*exp_ranges):
        ans.append(prod([o**i for o,i in zip(factor_list,v)]))
    return ans

def find_kadziela_matrices(M,T):
    '''
    The matrix M describes the relation between periods (A,B,D)^t
    and the periods (A0,B0)^t, where (A,B,D) are the periods of
    the Teitelbaum periods, and (A0,B0) are the Darmon ones.
           (A,B,D)^t = M * (A0,B0)^t
    The matrix T describes the action of Hecke on homology.
    That is, the first column of T describes the image of T
    on the first basis vector.

    The output are matrices X and Y such that
         X * matrix(2,2,[A,B,B,D]) = matrix(2,2,[A0,B0,C0,D0]) * Y

    '''
    a, b, c, d, e, f = M.list()
    x, y, z, t = T.list()
    #     1,  2,  3,  4,  5,  6,  7,  8
    r1 = [a,  c,  0,  0, -1,  0,  0,  0]
    r2 = [b,  d,  0,  0,  0,  0, -1,  0]
    r3 = [c,  e,  0,  0,  0, -1,  0,  0]
    r4 = [d,  f,  0,  0,  0,  0,  0, -1]
    r5 = [0,  0,  a,  c,  0,  0, -1,  0]
    r6 = [0,  0,y*b,y*d, -z,  0,x-t,  0]
    r7 = [0,  0,  c,  e,  0,  0,  0, -1]
    r8 = [0,  0,y*d,y*f,  0, -z,  0,x-t]
    AA = matrix(ZZ,8,8,[r1,r2,r3,r4,r5,r6,r7,r8])
    if AA.rank() == 8:
        raise ValueError('Not isogenous')
    r = AA.right_kernel().matrix().rows()[0].list()
    X = matrix(ZZ,2,2,r[:4])
    Y = matrix(ZZ,2,2,r[4:])
    return X, Y

