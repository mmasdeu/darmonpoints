print("\n\nType '?fdom' for help.\n\n");
addhelp(fdom, "This package can be used to compute fundamental domains for Shimura curves (the PARI code can be easily adapted to compute fundamental domains for any discrete subgroup of PSL(2, R)).\n For each subtopic ``P (p)'', call ?p to access a basic description and list of methods. Subtopics:\n Geometry (geo)\n Visualizing fundamental domains with Python (vfd)\n Quaternion methods (quat)");

\\GEOMETRY
	addhelp(geo,"These methods deal with geometry. Available methods:\n hdiscrandom, hdist, mat_eval");

	install("hdiscrandom","Gp","hdiscrandom","libfdom.so");
	addhelp(hdiscrandom,"Input R, a positive real number.\n Returns a random point in the ball of radius R centred at 0 in the unit disc model of the hyperbolic plane.");
	install("hdist","GGD0,L,p","hdist","libfdom.so");
	addhelp(hdist,"Inputs z1, z2, {flag=0}: complex numbers in the upper half plane z1 and z2, and flag=0, 1.\n Returns the hyperbolic distance between z1 and z2. If flag=0 we use the upper half plane model, and if flag=1 we use the unit disc model.");
	install("mat_eval","GG","mat_eval","libfdom.so");
	addhelp(mat_eval, "Inputs M, x; M a matrix, and x number.\n Returns Mx with M acting via Mobius transformation. x=+/-oo is allowed.");
	\\install("mobius_gp","GGp","mobius","libfdom.so");
	\\addhelp(mobius,"Inputs M, c: a 2x2 matrix M, and a circle/line/arc/segment c.\n This returns M(c), where M acts as a Mobius map.");

\\Visualization
	addhelp(vfd,"These methods allow one to save fundamental domains and geodesics, and view them with a Python program. Available methods:\n python_plotviewer, python_printarcs, python_printfdom.");
	
	install("python_plotviewer","vr","python_plotviewer","libfdom.so");
	addhelp(python_plotviewer,"Input S: string denoting the file names of data fundamental domains/geodesics.\n Launches the python file fdviewer.py to view the domain/geodesics. Enter the files separated by spaces (they must be stored in the sub-folder 'fdoms').");
	install("python_printarcs","vGrD0,L,Drp","python_printarcs","libfdom.so");
	addhelp(python_printarcs,"Inputs arcs, filename, {view=0}, {extrainput=NULL}: a set of arcs arcs, string filename, view=0, 1, and extrainput=NULL or a string.\n Prints the arcs specified by arcs to the file fdoms/filename.dat, ready for plotviewer. If view=1, calls plotviewer with the additional input of extrainput if you want to include other arcs/fundamental domains.");
	install("python_printfdom","vGrp","python_printfdom","libfdom.so");
	addhelp(python_printfdom,"Input U, filename: fundamental domain U, string filename.\n Prints the fundamental domain U to the file fdoms/filename.dat, ready for the plot viewer. The filename must start with 'fd' to work properly.")


\\Quaternion methods
	addhelp(quat,"These methods allow for the computation of fundamental domains for Eichler orders in quaternion algebras split at one real place. Available methods:\n algalgto1ijk, algbasisto1ijk, algeichler1, algeichler2, algeichler_conj, algelttype, algfdom, algfdomalg, algfdomarea, algfdomminimalcycles, algfdomorder, algfdompresentation, algfdomrootgeodesic, algfdomsignature, algfdomword, algisorder, algmulvec, algnormdisc, algorderconj, algorderdisc, algorderlevel, algreduceddisc, algshimura, algshimura_ab, algswapab, smallalgebras, smallalgebras_area.");

	install("algelttype","iGG",,"libfdom.so");
	addhelp(algelttype,"Inputs A, g: quaternion algebra A over a totally real number field and split at exactly one real place, and g, an element of norm 1 in A.\n Returns the type of g, i.e. -1 if g is elliptic (|trace|<2), 0 if g is parabolic (|trace|=2), and 1 if g is hyperbolic (|trace|>2). Does not check that g has norm 1.");
	install("algfdom","GDGD0,G,D0,L,D0,L,D0,G,D0,G,p","algfdom","libfdom.so");
	addhelp(algfdom,"Inputs A, {O=NULL}, {p=I/2}, {dispprogress=0}, {dumppartial=0}, {partialset=0}, {constants=0}: quaternion algebra A split at one real place, O an Eichler order (4n x 4x Z-matrix written in the basis of the stored maximal order, columns spanning the order), upper half plane point p, dispprogress=0,1, dumppartial=0,1, partialset=0 or a set of norm 1 elements of A, constants=0 or [C, R, passes, type].\n Computes and returns the fundamental domain for the group of units of norm 1 in O, where O is set to the pre-computed maximal order in A if not supplied. We use the unit disc model, which the upper half plane is mapped to via p->0. p need to NOT be a fixed point of this group under the standard embedding into PSL(2, R) (p=I/2 is safe for quaternion algebras over Q). If dispprogress=1, displays partial progress. If dumppartial=1, this dumps generating sets of partial results to 'algfdom_partialdata_log.txt', where i is a number. This is useful in case of error, for example running out of memory, lack of precision, segmentation fault, etc. partialset is either 0 or a vector of norm 1 elements of A that can be used as a starting base for the fundamental domain. If any of C, R, passes, or type is 0, it is auto-set. C is the constant used in solving Q_{z_1, z_2}(x)<=C, R is the radius we choose random points from, passes is used to specify the estimated number of passes (larger=less points per pass). If type=1, we enumerate using qfminim. If type=2, we enumerate using the `improved' Fincke-Pohst method. If type=0, we automatically choose type 1 if n>=2 and type 2 if n=1 (which seems to be the optimal choice).");
	install("algfdomalg","G","algfdomalg","libfdom.so");
	addhelp(algfdomalg,"Input U, a fundamental domain.\n Returns the algebra associated to the fundamental domain. If the computation increased the precision, then this algebra has been recomputed to the new precision, and should be used for all future computations involving U.");
	install("algfdomarea","GDGD0,L,p","algfdomarea","libfdom.so");
	addhelp(algfdomarea,"Input A, {Order=NULL}, {lp=0}: a quaternion algebra A split at one real place, Eichler order Order, and lp=0 or 1.\n Returns the area of the fundamental domain associated to the group of units of norm 1 in Order. Requires the computation of the zeta_K(2) (Dedekind zeta function for the centre), which may require some calls to allocatemem() if K is ``large''. To compute the answer to less precision, input lp as 1 (this can be significantly faster for large K).");
	install("algfdomminimalcycles","Gp","algfdomminimalcycles","libfdom.so");
	addhelp(algfdomminimalcycles,"Input U, a fundamental domain.\n Returns the set of minimal cycles of the side pairing. The format is [cycles, types], where an element of cycle is a vecsmall [i1,i2,...,in] so that the cycle is v_i1, v_i2, ..., v_in. cycle[i] has type types[i], where type 0=parabolic, 1=accidental, m>=2=elliptic of order m. The vecsmall types is sorted from small to large.");
	install("algfdomorder","G","algfdomorder","libfdom.so");
	addhelp(algfdomorder,"Input U, a fundamental domain.\n Returns the order associated to the fundamental domain.");
	install("algfdompresentation","Gp","algfdompresentation","libfdom.so");
	addhelp(algfdompresentation,"Inputs U, a fundamental domain.\n Returns the group presentation of the fundamental domain U. The return is a vector V, where V[1] is the vector of generators (a subset of U[1]), V[2] is the vector of relations, and V[3] is the representation of U[1][i] as a word in V[1]. A word/relation is listed as Vecsmall([i1, i2, ..., ik]), which corresponds to the equation V[1][|i1|]^{sign(i1)}*...*V[1][|ik|]^{sign(ik)} (i.e. g_1^2g_2^-1->[1, 1, -2]).");
	install("algfdomrootgeodesic","GGp","algfdomrootgeodesic","libfdom.so");
	addhelp(algfdomrootgeodesic,"Inputs g, U: a hyperbolic element g of norm 1 in an order in an algebra, U the fundamental domain of this order.\n Returns the root geodesic of g in the fundamental domain. The format is [g's, circle arcs, vecsmall(sides hit), vecsmall(sides emenating from)].");
	install("algfdomsignature","Gp","algfdomsignature","libfdom.so");
	addhelp(algfdomsignature,"Input U, a fundamental domain.\n Returns the signature of the algebra A. The format is [g, V, s], where g is the genus, V=[m1,m2,...,mt] (vecsmall) are the orders of the elliptic cycles (all >=2), and s is the number of parabolic cycles. The signature is normally written as (g;m1,m2,...,mt;s), and the group is generated by elements a_1, ..., a_g, b_1, ..., b_g, g_1, ..., g_{t+s} satisfying the relations g_i^m_i=1 for 1<=i<=t and [a_1,b_1]*...*[a_g,b_g]*g_1*...*g_{t+s}=1, where [x, y]=x*y*y^(-1)*x^(-1) is the commutator.");
	install("algfdomword","GGGp","algfdomword","libfdom.so");
	addhelp(algfdomword, "Inputs: g, P, U: an element g of norm 1 in an order in an algebra, fundamental domain of this order U, and group presentation of this order P.\n This writes g as a word in P[1], and returns the word. The format is Vecsmall([i1, i2, ..., ik]) corresponds to the equation V[1][|i1|]^{sign(i1)}*...*V[1][|ik|]^{sign(ik)} (i.e. g_1^2g_2^-1->[1, 1, -2]).");
	install("algisorder","iGG", ,"libfdom.so");
	addhelp(algisorder,"Input A, O: algebra A, lattice O.\n Returns 1 if O is an order, and 0 if O is not.");
	install("algmulvec","GGG","algmulvec","libfdom.so");
	addhelp(algmulvec,"Inputs A, G, L: algebra A, G=vector of elements of A, L a vecsmall or vector of indices.\n Returns G[L[1]]*G[L[2]]*...*G[L[n]]. If an index is negative, we take the inverse of that element.");
	install("algnormdisc","G","algnormdisc","libfdom.so");
	addhelp(algnormdisc,"Input A, an algebra.\n Returns the norm to Q of the discriminant of A.");
	install("algorderdisc","GGD1,L,D1,L,","algorderdisc","libfdom.so");
	addhelp(algorderdisc,"Inputs A, O, {reduced=1}, {factored=1}: quaternion algebra A, order O.\n Returns the discriminant of the order O as an ideal in the centre of A. If reduced=1 we use the reduced discriminant, and if factored=1 we return the factorization matrix.");
	install("algorderlevel","GGD1,L,","algorderlevel","libfdom.so");
	addhelp(algorderlevel,"Inputs A, O, {factored=1}: quaternion algebra A, order O.\n Returns the level of the order O, in factored form if factored=1.");
	
	\\install("algfdom_bestC","GDGp","algfdom_bestC","libfdom.so");
	\\addhelp(algfdom_bestC,"Input A, {O=NULL}: a quaternion algebra corresponding to a Shimura curve.\n Returns the (theoretically) optimal value of C to input into algsmallnorm1elts to minimize expected time to find a new element.");
	\\install("algnormalizedbasis","GDGGGp","algnormalizedbasis","libfdom.so");
	\\addhelp(algnormalizedbasis, "Inputs A, {O=NULL}, G, p: quaternion algebra A split at one real place, Eichler order O, set G of elements of norm 1 in the order in A, upper half plane point p.\n Returns the normalized basis associated to G.");
	\\install("algnormalizedboundary","GDGGGp","algnormalizedboundary","libfdom.so");
	\\addhelp(algnormalizedboundary, "Inputs A, {O=NULL}, G, p: quaternion algebra A split at one real place, Eichler order O, set G of elements of norm 1 in the order in A, upper half plane point p.\n Returns the normalized boundary associated to G. The format of the output is [elements, icircs, vertices, vertex angles, matrices, area, 0, mats]. The circle corresponding to elements[i] is icircs[i], and the vertices are vertices[i-1] and vertices[i]. matrices[i] is the image in PSU(1,1) of elements[i]. The element 1 corresponds to a section on the unit circle, which also corresponds to a circle of 0. Vertex angles stores the radial angle to the ith vertex (with base angle being the first one). The area is the area, and the 0 stores the side pairing when we have a fundamental domain (so a priori stores nothing).");
	\\install("algfdomreduce","GGD0,G,p","algfdomreduce","libfdom.so");
	\\addhelp(algfdomreduce,"Inputs g, U, {z=0}: an element g of norm 1 in an order in an algebra, normalized boundary of a subset of this order, and a point z in the unit disc.\n Returns the triple [gammabar, delta, decomp], where gammabar=delta*g is (G,z)-reduced (i.e. distance between gammabar*z and 0 is less than or equal to the distance between g'*gammabar*z for all g' in G), and decomp is the vecsmall [i1, i2, ..., in] with delta=G[i1]*G[i2]*...*G[in], with G=U[1]. If z=0 and we have the full fundamental domain, then gammabar=+/-1.");
	\\install("algramifiedplacesf","G","algramifiedplacesf","libfdom.so");
	\\addhelp(algramifiedplacesf,"Input A, an algebra.\n Returns the vector of finite places that ramify.");
	\\install("algabsrednorm","GGD0,G,D0,G,p","algabsrednorm","libfdom.so");
	\\addhelp(algabsrednorm,"Inputs A, p, {z1=0}, {z2=0}: quaternion algebra A split at one real place, upper half plane point p, unit disc points z1, z2.\n Returns the quadratic form q that satisfies Q_{z1, z2}(g)=cosh(d(g(z_1), z_2))+n-1 for g of norm 1 in the order of A. If g is written in the basis representation, g~*q*g gives the value of Q_{z1, z2}(g). Finding small vectors with respect to q allows one to determine if z1 and z2 are close on the quotient, and to find which element makes them close.");
	\\install("algsmallnorm1elts","GDGGGD0,G,D0,G,D0,L,p","algsmallnorm1elts","libfdom.so");
	\\addhelp(algsmallnorm1elts,"Inputs A, {O=NULL}, p, C, {z1=0}, {z2=0}, {type=0}: quaternion algebra A split at one real place, Eichler order O, upper half plane point p, positive real number C, unit disc points z1 and z2, type=0, 1, 2.\n Computes small norm 1 elements O, i.e. such that Q_{z_1,z_2}(g)<=C. The point p is the base for the mapping from the upper half plane model to the unit disc model, and z1, z2 are basepoints: if g has norm 1, then Q_{z_1, z_2)(g)=cosh(d(gz_1, z_2))+n-1 is satisfied (n=degree of the centre of A). If type=1 we use qfminim, and type=2 we use the ``improved Fincke-Pohst''. If type=0, we take qfminim if n>=2 and improved F-P if n=1. Note that the improved F-P method may return some elements with Q(g)>C, and is generally faster if n=1, or possibly if C is really large.");
	
	\\fdom_extra
	install("algsmallelts","GDGGGGD0,G,D0,G,p","algsmallelts","libfdom.so");\\Still working on this.
	
	install("alg1ijktoalg","GG","alg1ijktoalg","libfdom.so");
	addhelp(alg1ijktoalg,"Inputs: quaternion algebra A, element x=[e, f, g, h].\n Returns what e+fi+gj+hk is in the algebraic representation.");
	install("alg1ijktobasis","GG","alg1ijktobasis","libfdom.so");
	addhelp(alg1ijktobasis,"Inputs: quaternion algebra A, element x=[e, f, g, h].\n Returns what e+fi+gj+hk is in the basis representation.");
	install("algalgto1ijk","GG","algalgto1ijk","libfdom.so");
	addhelp(algalgto1ijk,"Inputs: quaternion algebra A, element x in algebraic form.\n Returns [e, f, g, h], where x=e+fi+gj+hk.");
	install("algbasisto1ijk","GG","algbasisto1ijk","libfdom.so");
	addhelp(algbasisto1ijk,"Inputs: quaternion algebra A, element x in basis form.\n Returns [e, f, g, h], where x=e+fi+gj+hk.");
	install("algeichler_conj","GG","algeichler_conj","libfdom.so");
	install("algeichler1", "vGG", , "libfdom.so");
	addhelp(algeichler1,"Input A, ideal: algebra A, ideal of the centre.\n Prints code that you can copy-paste into Magma to generate an Eichler order of level ideal in the maximal order of A. Copy the result back into the second input of algeichler2 to generate the order.");
	install("algeichler2","GG", , "libfdom.so");
	addhelp(algeichler2,"Input A, magma-order: algebra A, final output of the Magma code generated with algeichler1.\n Returns the corresponding Eichler order.");
	addhelp(algeichler_conj,"Inputs A, x: quaternion algebra A, invertible element x.\n Returns the Eichler order O intersect xOx^(-1).");
	install("algorderconj","GGDG","algorderconj","libfdom.so");
	addhelp(algorderconj,"Inputs: A, x, {O=NULL}: algebra A, invertible element x, order O (in terms of the stored order).\n Returns xOx^{-1}, where the columns generate this new order over Z (with respect to the stored order in O).");
	install("algreduceddisc","G","algreduceddisc","libfdom.so");
	addhelp(algreduceddisc,"Input A, a quaternion algebra.\n Returns the reduced discriminant of the maximal order, as an ideal in the centre of the field.");
	install("algshimura","GGD1,L,D20,L,D1,L,","algshimura","libfdom.so");
	addhelp(algshimura,"Inputs F, D, {place=1}, {maxcomptime=20}, {allowswap=1}: totally real number field F, positive integer D, integer place between 1 and deg(F),maxcomptime= nonnegative integer, allowswap=0 or 1.\n Returns a quaternion algebra over F that is split at the infinite place place only, and has discriminant D, where |N_{F/Q}(disc)|=D, if it exists. If it does not exist, returns 0. This also guarantees that a>0 at the split infinite place, hence the output is suitable for fundamental domain methods. If maxcomptime!=0, we stop after that many seconds. If allowswap=0, then we do NOT allow the swapping of a, b in output of alginit (we require a>0 at the split real place, and may need to swap), and instead return 0. This is recommended if deg(F)>=6, as the swapped algebra is typically far to massive (e.g. sometimes run out of memory, even with 4GB).");
	install("algshimura_ab","GGD1,L,D1,L,","algshimura_ab","libfdom.so");
	addhelp(algshimura_ab,"Inputs F, D, {place=1}, {maxcomptime=20}, {allowswap=1}: totally real number field F, positive integer D, integer place between 1 and deg(F), maxcomptime= nonnegative integer, allowswap=0, 1.\n Returns [a, b] such that B=(a, b/F) is a quaternion algebra over F that is split at the infinite place place only, and has discriminant D, where |N_{F/Q}(disc)|=D, if it exists. If it does not exist, returns 0. This also guarantees that a>0 at the split infinite place, hence the output is suitable for fundamental domain methods. If maxcomptime!=0, we stop after that many seconds. If allowswap=0, then we do NOT allow the swapping of a, b in output of alginit (we require a>0 at the split real place, and may need to swap), and instead return 0. This is recommended if deg(F)>=6, as the swapped algebra is typically far to massive (e.g. sometimes run out of memory, even with 4GB).");
	install("algswapab","G","algswapab","libfdom.so");
	addhelp(algswapab,"Input A, a quaternion algebra=(a, b/F).\n Returns (b, a/F), i.e. swapping a and b.");
	install("smallalgebras","GLD2,G,D0,G,D20,L,D0,L,","smallalgebras","libfdom.so");
	addhelp(smallalgebras,"Inputs F, nwant, {Dmin=2}, {Dmax=oo}, {maxcomptime=20}, {allowswap=0}: totally real number field F, positive integer nwant, Dmin>=2 integer, maxcomptime= nonnegative integer, allowswap=0 or 1.\n Finds and returns nwant pairs [a, b] corresponding to quaternion algebras over F split at exactly one real place. The return format is [{Nm_F/Q(disc(A)}, {[a,b]}]. We search for algebras starting at Nm_F/Q(disc(A))=Dmin. If Dmax is non-zero, we stop searching at Dmax (and possibly return less than nwant algebras). If maxcomptime!=0, we allow that many seconds for each search (recommended if deg(F)>=6). If allowswap=0, we do NOT allow the swapping of a, b, in the found algebra (the method will find fewer algebras, but the coefficients will be better). This is recommended if deg(F)>=6.");
	install("smallalgebras_area","GGGD0,L,D20,L,D1,L,p","smallalgebras_area","libfdom.so");
	addhelp(smallalgebras_area,"Inputs F, Amin, Amax, {retD=0}, {maxcomptime=20}, {allowswap=1}: totally real number field F, positive reals Amin<Amax, retD=0 or 1, maxcomptime= nonnegative integer, allowswap=0 or 1.\n Finds and returns pairs [a, b] corresponding to quaternion algebras over F split at exactly one real place, which have area between Amin and Amax. If retD=1, we only return the discriminants. Otherwise, the return format is [{Nm_F/Q(disc(A)}, {[a,b]}]. If maxcomptime!=0, we allow that many seconds for each search (recommended if deg(F)>=6). If allowswap=0, we do NOT allow the swapping of a, b, in the found algebra (the method will find fewer algebras, but the coefficients will be better). This is recommended if deg(F)>=6.");

\\PAPER METHODS

	\\OPTIMIZING THE VALUE OF C FOR ENUMERATION
	install("enum_bestC","GGGLD300,L,p","enum_bestC","libfdom.so");
	addhelp(enum_bestC,"Inputs A, p, scale, ntrials, {mintesttime=300}: quaternion algebra A corresponding to a Shimura curve, upper half plane point p, scale>1 real, mintesttime positive integer.\n Computes the optimal C value for A based on heuristics. We use ntrials values of C in a range [Cmin, Cmin*scale^(1/2n)] to compute a, b, where the total time taken is a+b*C^{2n}. We solve for the optimal C based on this. We return [a, b, C, R^2], with the R^2 value for the a, b regression.");
	install("enum_bestC_range","GGGLLsD0,L,D1,L,D1,L,p","enum_bestC_range","libfdom.so");
	addhelp(enum_bestC_range,"Inputs Aset, p, scale, ntrials, mintesttime, fname, {isArange=0}, {compile=1}, {WSL=1}: set of quaternion algebras corresponding to Shimura curves Aset, upper half plane point p, scale>1, ntrials>=2, mintesttime positive integer, fname a string, and isArange/compile/WSL 0 or 1.\n Computes the optimal C for all algebras A in Aset using the data p, scale, ntrials, mintesttime. If isArange=1, we assume they all have the same base number field, and we are changing the algebra discriminant. Otherwise, we assume that n=[F:Q] is constant, and we are varying disc(F). We save the data to plots/build/fname.dat, and perform regression on the data. If compile=1 we compile a plot, and display it if WSL=1. The return value is [trend, R^2].");
	install("enum_successrate","GGGLD0,G,p","enum_successrate","libfdom.so");
	addhelp(enum_successrate,"Inputs A, p, C, Ntests, {R=0}: quaternion algebra A corresponding to a Shimura curve, upper half plane point p, positive real number C, positive integer Ntests, positive real R.\n Computes the small norm 1 elements of A (<=C) Ntests times, where we pick z_1=0 and z_2 a random point in the hyperbolic disc of radius R. If R=0, we auto-set R to be the same R as the algfdom method. We output the pair [obs, exp], of the number of found norm 1 elements, and the expected number.");
	install("enum_successrate_range","GGGGLLD0,G,DsD1,L,D1,L,p","enum_successrate_range","libfdom.so");
	addhelp(enum_successrate_range,"Inputs A, p, Cmin, Cmax, ntrials, Ntests, {R=0}, {fname=NULL}, {compile=1}, {WSL=1}: q-alg A corresp. to a Shimura curve, upper half plane point p, 0<Cmin<Cmax, ntrials>1 and Ntests>0 integers, R>=0, fname=file name, compile and WSL=0, 1.\n Runs enum_successrate on ntrials trials of C between Cmin and Cmax. This prints the results to the file pltos/build/fname.dat, and returns [A, B, R^2], where the expected trend line is A+B*C, and R^2 is the R^2 value of this trendline with the data. If compile=1, we create and compile a LaTeX (pgfplots) of the curve. If WSL=1, we also display said plot, assuming we are using Windows Subsystem for Linux.");
	install("enum_time","GGGD300,L,p","enum_time","libfdom.so");
	addhelp(enum_time,"Inputs A, p, Cset, {mintesttime=300}: quaternion algebra A corresponding to a Shimura curve, upper half plane point p, vector of positive real numbers, mintesttime positive integer.\n This computes how long the call to algsmallnorm1elts(A, p, C, z1, z2) takes for all C in Cset, and returns a column vector of the timings. This does NOT take into account time spent initializing things related to the algebra (e.g. cholesky of the norm form), since this can be computed once and reused many times. If the time taken is <mintesttime (in milliseconds), we repeat the test K times until we have taken at least mintesttime, and divide the final result by K. A larger value of mintesttime will produce more accurate results, but will take longer.");
	install("enum_time_range","GGGGLD300,L,DsD1,L,D1,L,p","enum_time_range","libfdom.so");
	addhelp(enum_time_range,"Inputs: A, p, Cmin, Cmax, ntrials, {mintesttime=300}, {fdata=NULL}, {compile=1}, {WSL=1}: quaternion algebra A corresponding to a Shimura curve, upper half plane point p, positive real numbers Cmin and Cmax, positive integer ntrials>=2, positive integer mintesttime, file name fdata, compile and WSL=0, 1.\n This takes the interval [Cmin, Cmax], chops it up into ntrials pieces, and runs enum_time on this. We run the linear regression on this, and return [[A,B]~, R^2], where we fit to the curve t=A+B*C^(2n), n=degree of the number field F. If fdata!=NULL, we also write the pairs (C, t) to the file plots/build/fdata.dat (the first line is 'x y', so that it can be used to create a LaTeX (pgfplots) if desired). If compile=1, we compile the plot. If WSL=1 we assume we are on Windows Subsystem for Linux and also view the plot, and otherwise we just compile it assuming we are in Linux.");
	install("enum_timeforNelts","lGGGLD0,G,D1,L,p","enum_timeforNelts","libfdom.so");
	addhelp(enum_timeforNelts,"Inputs: A, p, C, nelts, {R=0}, {type=1}: quaternion algebra A corresponding to a Shimura curve, upper half plane point p, positive real number C, nelts positive integer, R>=0, type=1 or 2.\n Computes the time to find nelts non-trivial elements using the given inputs. If type=1, we use qfminim, and otherwise we use the condition method.");
	install("enum_timeforNelts_range","vGGGGLLsD1,L,D1,L,D1,L,p","enum_timeforNelts_range","libfdom.so");
	addhelp(enum_timeforNelts_range,"Inputs: A, p, Cmin, Cmax, ntrials, nelts, fname, {type=1}, {compile=1}, {WSL=1}: quaternion algebra A corresponding to a Shimura curve, upper half plane point p, positive real numbers Cmin<Cmax, ntrials>=2, nelts positive integer, string fname, type=1 or 2, compile and WSL=0, 1.\n Computes the time to find nelts non-trivial elements using the given inputs for ntrials between Cmin and Cmax. If type=1, we use qfminim, and otherwise we use the condition method. We write the results to the file plots/build/fname.dat. If compile=1 we make and compile a plot of the results. If WSL=1, we also view it, assuming we are on the Windows Subsystem for Linux.");

	\\NUMBER OF ELEMENTS REQUIRED TO GENERATE ALGEBRA
	install("algfdom_nelts","GGD0,G,D0,L,p","algfdom_nelts","libfdom.so");
	addhelp(algfdom_nelts,"Inputs: A, p, {CNRdata=0}, {type=0}: same as algfdom.\n This computes the fundamental domain with algfdom, but instead returns [nelts, sides, area], where nelts is the number of elements found before generating the domain.");

	\\REGRESSIONS & PLOTS
	install("OLS","GGD1,L,","OLS","libfdom.so");
	addhelp(OLS,"Inputs X, y, {retrsqr=1}:  m*n matrix X with top row being all 1's, length n column vector y, retrsqr=0, 1.\n Performs ordinary least squares regression on the data, where the n inputs are the columns of X, and the outputs are the entries of y. We must include a constant term, hence why the first row of X must be all 1's. If retrsqr=1, returns [params, R^2], and otherwise returns params, where params is the length m column vector of best fit parameters.");
	install("OLS_nointercept","GGD1,L,","OLS_nointercept","libfdom.so");
	addhelp(OLS_nointercept,"Inputs X, y, {retrsqr=1}: vector X, column vector y (of same length), retrsqr=0, 1.\n Performs ordinary least squares regression on the data assuming that y[i]=c*X[i], i.e. the y-intercept is 0. Returns c if retrsqr=0, or [c, R^2] otherwise.");
	install("OLS_single","GGD1,L,","OLS_single","libfdom.so");
	addhelp(OLS_single,"Inputs x, y, {retrsqr=1}: vector x, column vector y, retrsqr=0, 1. Performs linear regression for a single variable (essentially a macro for OLS with y=mx+b.");
	install("rsquared","GGG","rsquared","libfdom.so");
	addhelp(rsquared,"Inputs X, y, fit: X and y data supplied to OLS, and fit the proposed fit (a column vector of parameters). This returns the R^2 value for this proposal.");
	install("plot_compile","vsD1,L,","plot_compile","libfdom.so");
	addhelp(plot_compile,"Inputs: string fname, {WSL=1 or 0}.\n Compiles the plot plots/build/fname_plotter.tex and moves the output to plots/fname.pdf. If WSL=1, also opens the output plot, assuming Windows Subsystem for Linux is being run.");

default(parisize, "4096M");\\Must come at the end