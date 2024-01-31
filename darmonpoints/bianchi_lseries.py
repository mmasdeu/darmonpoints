from itertools import product

from sage.matrix.constructor import Matrix, matrix
from sage.modular.pollack_stevens.manin_map import unimod_matrices_to_infty
from sage.modular.pollack_stevens.padic_lseries import log_gamma_binomial
from sage.modular.pollack_stevens.sigma0 import Sigma0
from sage.rings.integer_ring import ZZ
from sage.rings.rational_field import QQ


def fundamental_integral(self, alpha, i, j):
    r"""
    Returns the integral

            int_{a + pZp, b + pZp} z_P^i z_Pbar^j d.Phi{0-->infty},

    where alpha = a mod P, b mod Pbar.

    self: overconvergent Bianchi cohomology class.

    From the theory, we can write this in terms of the moments of Phi{alpha/p --> \infty},
    and we know how to compute this in terms of the overconvergent cohomology class.

    We need to keep track of which is our distinguished prime; it is the prime used to define the arithmetic
    group. (The other prime is then in the `tame' level).

    Note that a, b MUST be coprime to p. (We obtain this in any case after multiplying by psi(a)psi(b)).

    This is essentially just the product of two copies of the theory for GL2/Q with single valued
    distributions.


    ::::REMARKS::::

     - CURRENTLY REQUIRES SQUARE-FREE LEVEL.

     - ALSO SOMETIMES FAILS IF i = j = 0. IN THIS CASE HAVE COMPLETE ANSWER IN BASE-CHANGE CASE USING ELLIPTIC
    MODULAR SYMBOLS. REQUIRES IMPLEMENTATION!!!!

     - THIS IS WHAT IN THE RATIONAL CODE WE WERE CALLING 'BI(phi,a,j)'.

    """

    if i == 0 and j == 0:
        raise NotImplementedError("We still need to implement constant terms!!")
    ## compute the a_p eigenvalues
    aP = self._aP
    aPbar = self._aPbar

    ## underlying primes : symbol --> overconvergent cohomology --> Gamma_0(n) --> p in ZZ
    G = self.parent().S_arithgroup()
    phi = G._F_to_local
    p = G.prime()  ## underlying rational prime
    F = G.base_field()  ## underlying quadratic field

    ## primes above p (as ideals) ## Do we need this?
    P = G.ideal_p
    Pbar = p / P  # F.ideal(pibar)

    ## Find the level: ideal in O_K
    level_away_from_P = G.level  ## Level outside of the prime P (but including Pbar)
    tame_level = level_away_from_P / Pbar
    level = P * level_away_from_P

    ## Generators
    pi = self.parent().P_gen
    pibar = self.parent().Pbar_gen

    ## Check this value is actually valid for computation
    if alpha in P or alpha in Pbar:
        raise ValueError("alpha must be prime to p.")

    ## Compute a, b
    a = F.residue_field(P)(alpha)
    b = F.residue_field(Pbar)(alpha)

    ## Initialise scaling factor
    main_scale = 1 / (aP * aPbar)

    ## RUN THROUGH ALL OTHER PRIMES DIVIDING N
    orders = []
    prime_unifs = []
    eigenvalues = []
    for q, _ in tame_level.factor():
        ## Compute uniformisers
        pi_q = q.gens_reduced()[0]  ## uniformiser at q
        prime_unifs.append(pi_q)

        ## Compute mult. order
        order_P = F.residue_field(P)(pi_q).multiplicative_order()
        order_Pbar = F.residue_field(Pbar)(pi_q).multiplicative_order()
        order_q = ZZ(order_P).lcm(
            ZZ(order_Pbar)
        )  ## Multiplicative order of pi_q in (O_F tensor Zp)*
        orders.append(order_q)

        ## Compute U_q eigenvalues
        lambda_q = self.ap_getter(q)
        # try:
        #         lambda_q = self.Tq_eigenvalue(q)
        # except AttributeError:
        #         lambda_q = self.get_hecke_eigenvalue(q)
        eigenvalues.append(lambda_q)

        ## Update global scaling factor
        main_scale /= lambda_q - lambda_q ** (1 - ZZ(order_q)) * pi_q ** (
            order_q * i
        ) * pi_q.conjugate() ** (order_q * j)

    ## Compute compatible generator for our level
    N = pi * pibar
    for pi_q in prime_unifs:
        N *= pi_q

    num_primes = len(prime_unifs)

    ## set up big sums, one for each prime, of length equal to the mult. order of that prime
    ranges = (range(ord_q) for ord_q in orders)
    exponents = product(*ranges)

    ## Initialise final answer
    ans = 0

    ## Range over big iterated outer sums
    for m in exponents:
        scalar_sum = 1
        scalar_mod_P = 1
        scalar_mod_Pbar = 1
        ## Set up lambda_q^(-m) * q^(mj) for each q|N
        ## Also set up q^m for each q|N to define the modulus condition on the inner sum
        for k in range(num_primes):
            scalar_sum *= (
                eigenvalues[k] ** (-m[k])
                * prime_unifs[k] ** (i * m[k])
                * prime_unifs[k].conjugate() ** (j * m[k])
            )
            scalar_mod_P *= prime_unifs[k] ** m[k]
            scalar_mod_Pbar *= prime_unifs[k].conjugate() ** m[k]

        ## Create the inner sum for this set of exponents
        new_ans = 0

        ## Run over all beta modulo the level ideal
        for beta in F.ideal(level).residues():
            ## if beta does not satisfy the required congruence conditions modulo p, then continue
            if (scalar_mod_P * beta - alpha) not in P:
                continue
            if (scalar_mod_Pbar * beta - alpha) not in Pbar:
                continue

            ## If beta is not coprime to the level, then continue
            g = ZZ(beta.norm()).gcd(level.norm())
            if g != 1:
                continue

            ## Create the matrix gamma such that gamma.infty = beta/level Need to do CRT on beta, N, level = (N)
            I_beta = F.ideal(beta)
            C = I_beta.element_1_mod(level)

            ## Now E*beta - D*p = 1
            D = (C - 1) / N
            E = C / beta
            assert E * beta - D * N == 1
            ## ... so the matrix we want is [[beta, D], [N,E]]. This returns Phi(beta/N --> infty)
            o = matrix(F.ring_of_integers(), 2, 2, [beta, D, N, E])
            B = G.Gpn.B
            quaternion = G.Gpn(
                B(
                    [
                        (o[0, 0] + o[1, 1]) / 2,
                        (o[0, 0] - o[1, 1]) / 2,
                        (-o[0, 1] - o[1, 0]) / 2,
                        (-o[0, 1] + o[1, 0]) / 2,
                    ]
                )
            ).quaternion_rep

            distribution_beta = self.evaluate(quaternion)

            ## Update inner sum for this beta; simple binomial sum repr. Phi{beta/N --> infty}[(beta + Nx)^j]
            tmp = sum(
                ZZ(j).binomial(r)
                * phi(beta) ** (j - r)
                * phi(N) ** r
                * distribution_beta.moment(r)
                for r in range(j + 1)
            )
            # print 'tmp = %s'%tmp
            new_ans += tmp
        ans += phi(scalar_sum) * new_ans

    ## Return scaled answer
    return phi(main_scale) * ans


def basic_integral(self, alpha, i, j):
    r"""
    Returns the integral

            int_{a + pZp, b + pZp} (z_P - {a})^i (z_Pbar - {b})^j d.Phi{0-->infty},

    where alpha = a mod P, b mod Pbar.

    self: overconvergent Bianchi cohomology class.

    From the theory, we can write this in terms of the moments of Phi{alpha/p --> \infty},
    and we know how to compute this in terms of the overconvergent cohomology class.

    We need to keep track of which is our distinguished prime; it is the prime used to define the arithmetic
    group. (The other prime is then in the `tame' level).

    Note that a, b MUST be coprime to p. (We obtain this in any case after multiplying by psi(a)psi(b)).

    This is essentially just the product of two copies of the theory for GL2/Q with single valued
    distributions.

    REQUIRES SQUARE-FREE LEVEL.
    ALSO SOMETIMES FAILS IF i = j = 0. IN THIS CASE HAVE COMPLETE ANSWER IN BASE-CHANGE CASE USING ELLIPTIC
    MODULAR SYMBOLS. REQUIRES IMPLEMENTATION!!!!
    """
    p = phi.parent().coefficient_module().base_ring().prime()
    M = phi.precision_relative()
    K = pAdicField(p, M)
    aa = K.teichmuller(a)
    p = K.prime()

    ## primes above p (as ideals) ## Do we need this?
    P = self.parent().S_arithgroup().ideal_p
    Pbar = p / P  # F.ideal(pibar)

    ## Check this value is actually valid for computation
    if alpha.mod(P) == 0 or alpha.mod(Pbar) == 0:
        raise ValueError("alpha must be prime to p.")

    ## Compute a, b
    a = F.residue_field(P)(alpha)
    b = F.residue_field(Pbar)(alpha)

    return sum(
        ZZ(j).binomial(r)
        * ZZ(j).binomial(s)
        * (-1) ** (i + j - r - s)
        * ZZ(K.teichmuller(a)) ** (i - r)
        * ZZ(K.teichmuller(b)) ** (j - s)
        * self.fundamental_integral(alpha, r, s)
        for r in range(i)
        for s in range(j)
    )


def basic_integral_one_prime(self, alpha, i, j):
    r"""
    Returns the integral

            int_{a + pZp, b + pZp} (z_P - {a})^i (z_Pbar - {b})^j d.Phi{0-->infty},

    where alpha = a mod P, b mod Pbar.

    From the theory, we can write this in terms of the moments of Phi{alpha/p --> \infty},
    and we know how to compute this in terms of the overconvergent cohomology class.

    We need to keep track of which is our distinguished prime; it is the prime used to define the arithmetic
    group. (The other prime is then in the `tame' level).

    Note that a, b MUST be coprime to p. (We obtain this in any case after multiplying by psi(a)psi(b)).

    This is essentially just the product of two copies of the theory for GL2/Q with single valued
    distributions.

    NOTE: THIS IS OLD CODE FOR COMPUTING WHEN THE LEVEL IS A PRIME IDEAL IN IQF F.
    """
    ## compute the a_p eigenvalues
    aP = self._aP
    aPbar = self._aPbar

    ## underlying primes : symbol --> overconvergent cohomology --> Gamma_0(n) --> p in ZZ
    p = self.parent().S_arithgroup().prime()  ## underlying rational prime
    F = self.parent().S_arithgroup().base_field()  ## underlying quadratic field

    ## Distinguished prime
    # pi = self.parent().P_gen
    # pibar = self.parent().Pbar_gen

    ## primes above p (as ideals)
    P = self.parent().S_arithgroup().ideal_p
    Pbar = p / P  # F.ideal(pibar)

    ## Compute a, b
    a = F.residue_field(P)(alpha)
    b = F.residue_field(Pbar)(alpha)

    if alpha.mod(pi) == 0 or alpha.mod(pibar) == 0:
        raise ValueError("alpha must be prime to p.")

    ## Compute a matrix that sends 0 to alpha/p. Need to do CRT on alpha, p
    I_alpha = F.ideal(alpha)
    C = I_alpha.element_1_mod(F.ideal(p))

    ## Now E*alpha - D*p = 1
    D = (Cprime - 1) / p
    E = Cprime / alpha
    assert E * alpha - D * p == 1
    ## ... so the matrix we want is [[alpha, D], [p,E]]
    distribution_alpha = self.evaluate(
        matrix(F.ring_of_integers(), 2, 2, [alpha, D, p, E])
    )

    ## symbol --> overconvergent class --> distributions --> base ring Zp
    K = self.parent().coefficient_module().base_ring()

    ## return the formula
    return sum(
        sum(
            ZZ(i).binomial(r)
            * ZZ(j).binomial(s)
            * ((alpha - ZZ(K.teichmuller(a))) ** (i - r))
            * (
                (alpha.conjugate - ZZ(K.teichmuller(b)) ** (j - r))
                * (p ** (r + s))
                * (-1) ** (r + 1)
                * (-1) ** (s + 1)
                * distribution_alpha.moment((r, s))
                for r in range(i + 1)
            )
            for s in range(j + 1)
        )
        / (aP * aPbar)
    )


def get_Lseries_term(self, m, n):
    r"""
    Return the `(m,n)`-th coefficient of the `p`-adic `L`-series, i.e. coeff of X^m * Y^n.

    See the paper for the exact formula for this coefficient. It is given in terms of
    a Mahler expansion for the measure combined with a choice of the p-adic logarithm.
    """

    ## check to see if we've already computed this, and if so, return this
    if (m, n) in self._Lseries_coefficients:
        return self._Lseries_coefficients[(m, n)]

    ## we haven't computed this yet. Go ahead and compute it
    else:
        ## Initialise p and a_p
        p = self.parent().S_arithgroup().prime()
        F = self.parent().S_arithgroup().base_field()
        ap = self._ap

        ## Primes above p
        P = self.parent().S_arithgroup().ideal_p
        Pbar = p / P

        ## Choose a topological generator
        if p == 2:
            gamma = 1 + 4
        else:
            gamma = 1 + p

        ## modular symbol --> space of symbols --> distributions --> base-ring Zp
        K = self.parent().coefficient_module().base_ring()
        precision = K.precision_cap()

        ## Initialise space in which our power series representation lives
        S = QQ[["z"]]
        z = S.gen()
        M = precision

        ## Initialise the (m,n)th coefficient, which will be given by a triple sum
        dmn = 0

        ## Compute representatives for (O_F/p)*
        residues = []
        for alpha in F.ideal(p).residues():
            if alpha.mod(P) != 0 and alpha.mod(Pbar) != 0:
                residues.append(alpha)

        ## Compute the coefficients c_j^(m)
        if m == 0:
            precision = M
            log_binom_m = [1] + [0 for a in range(M - 1)]
        else:
            ## compute the binomial polynomial (log_gamma(<z>), m) used to compute c_j^(n)
            log_binom_m = log_gamma_binomial(
                p, gamma, z, m, 2 * M
            )  ## p, top gen, power series gen, target term, twice precision
            if precision is None:
                precision = min(
                    [j + log_binom_m[j].valuation(p) for j in range(M, len(lb))]
                )
            log_binom_m = [log_binom_m[a] for a in range(M)]

        ## Compute the coefficients c_j^(n)
        if n == 0:
            precision = M
            log_binom_n = [1] + [0 for a in range(M - 1)]
        else:
            ## compute the binomial polynomial (log_gamma(<z>), n) used to compute c_j^(n)
            log_binom_n = log_gamma_binomial(
                p, gamma, z, n, 2 * M
            )  ## p, top gen, power series gen, target term, twice precision
            if precision is None:
                precision = min(
                    [j + log_binom_n[j].valuation(p) for j in range(M, len(lb))]
                )
            log_binom_n = [log_binom_n[a] for a in range(M)]

        ## Range over (O_F/p)*
        for alpha in residues:
            ## Compute alpha mod P, mod Pbar for Teichmuller lifts
            a = F.residue_field(P)(alpha)
            b = F.residue_field(Pbar)(alpha)

            ## range over i and j, from the series expansion for log_p
            for i in range(len(lb)):
                cim = log_binom_m[i]
                for j in range(len(lb)):
                    cjn = log_binom_n[j]

                    ## update the (triple) sum with the term corresponding to (i,j,alpha)
                    dmn += (
                        cjn
                        * cin
                        * ZZ(K.teichmuller(a)) ** (-i)
                        * ZZ(K.teichmuller(b)) ** (-j)
                        * self.basic_integral(alpha, i, j)
                    )

        ## We've computed the coefficient!

        ## Now cache the coefficient
        self._Lseries_coefficients[(m, n)] = dn.add_bigoh(precision)
        # self._Lseries_coefficients[n] /= self._cinf # DEBUG
        return self._Lseries_coefficients[(m, n)]
