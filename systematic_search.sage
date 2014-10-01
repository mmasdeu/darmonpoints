# load('darmonpoints.sage')
from sage.parallel.decorate import parallel,fork
from util import fwrite

######################
# Parameters         #
######################
Nrange = range(1,200) # Conductors to explore
max_P_norm = 200 # Maximum allowed norm for the chosen prime
max_P_norm_integrate = 23 # Maximum allowed norm for the chosen prime to integrate
max_F_disc = None # Maximum size of discriminant of base field
max_waiting_time_aurel = 2 * 60 * 60 # Amount of patience (in seconds)
max_waiting_time = 10 * 60 * 60 # Amount of patience (in seconds)
decimal_prec = 50

@parallel
def find_all_curves(pol,Nrange,max_P_norm,max_P_norm_integrate,max_waiting_time_aurel,max_waiting_time,decimal_prec,log_file):
    load('darmonpoints.sage')
    from sarithgroup import BigArithGroup
    from homology import construct_homology_cycle,lattice_homology_cycle
    from cohomology import CohomologyGroup, get_overconvergent_class_quaternionic
    from util import enumerate_words, quaternion_algebra_from_discriminant
    from itertools import product,chain,izip,groupby,islice,tee,starmap
    from sage.modules.fg_pid.fgp_module import FGP_Module,FGP_Module_class
    from sage.matrix.constructor import matrix,Matrix,block_diagonal_matrix,block_matrix
    from util import tate_parameter,update_progress,get_C_and_C2,getcoords,recognize_point,fwrite
    import os,datetime
    from sage.misc.persist import db
    from sage.rings.padics.precision_error import PrecisionError
    from util import discover_equation,get_heegner_params,fwrite,quaternion_algebra_from_discriminant, discover_equation_from_L_invariant,direct_sum_of_maps
    from integrals import integrate_H1,double_integral_zero_infty,indef_integral
    from sage.interfaces.magma import Magma

    out_str_vec = []

    try:
        page_path = ROOT + '/KleinianGroups-1.0/klngpspec'
    except NameError:
        ROOT = os.getcwd()
        page_path = ROOT + '/KleinianGroups-1.0/klngpspec'

    F = NumberField(pol,names='r')
    r = F.gen()

    if len(F.narrow_class_group()) > 1:
        return out_str_vec

    magma = Magma()
    magma.attach_spec(page_path)
    sys.setrecursionlimit(10**6)
    x = pol.parent().gen()
    no_rational_line = False
    for N in Nrange:
        # if gcd(F.discriminant(),N) != 1:
        #     continue
        for a in F.elements_of_norm(N):
            facts = F.ideal(a).factor()
            nfactors = len(facts)
            no_rational_line = False
            for j,Pe in enumerate(facts):
                if no_rational_line:
                    break
                P,e = Pe
                if e > 1:
                    continue
                if P.ramification_index() > 1:
                    verbose('ramified P')
                    continue
                if not ZZ(P.norm()).is_prime():
                    verbose('f > 1')
                    continue
                if ZZ(P.norm()).abs() > max_P_norm:
                    verbose('large P')
                    continue
                for v in enumerate_words([0,1],[0 for o in facts],nfactors):
                    try:
                        if no_rational_line:
                            break
                        if v[j] == 0:
                            continue
                        if any([v[k] == 1 and facts[k][1] > 1 for k in range(nfactors)]):
                            continue
                        D = F.ideal(1)
                        Np = F.ideal(1)
                        n_ramified_places = F.signature()[0] + F.signature()[1] - 1
                        for i in range(nfactors):
                            if i == j:
                                continue
                            if v[i] == 1:
                                assert facts[i][1] == 1
                                n_ramified_places +=1
                                D *= facts[i][0]
                            else:
                                Np *= facts[i][0]**facts[i][1]
                        if n_ramified_places % 2 != 0:
                            continue
                        NE = P * D * Np
                        assert NE == F.ideal(a)
                        Pnorm = P.norm()
                        assert N == NE.norm().abs()
                        prec = (RR(decimal_prec) * RR(10).log(Pnorm)).ceil()
                        out_str = '[%s, %s, %s, %s, %s, %s, {curve}, %s],\\'%(N,F.discriminant(),pol,P.gens_reduced()[0],D.gens_reduced()[0],Np.gens_reduced()[0],prec)
                        ram_at_inf = [-1 for o in F.real_embeddings()]
                        if F.signature()[1] == 0:
                            ram_at_inf[0] = 1
                        try:
                            G = fork(BigArithGroup,timeout = max_waiting_time_aurel)(P,quaternion_algebra_from_discriminant(F,D,ram_at_inf).invariants(),Np,base = F,use_sage_db = False,grouptype = None,magma = magma)
                        except Exception as e:
                            out_str_vec.append(out_str.format(curve = '\'Err G (%s)\''%e.message))
                            continue
                        if not hasattr(G,'embed'): # Not very elegant but works
                            if 'timed out' in G:
                                out_str_vec.append(out_str.format(curve = '\'Timed Out\''))
                            else:
                                out_str_vec.append(out_str.format(curve = '\'Err G (%s)\''%str(G)))
                            continue
                        try:
                            Coh = CohomologyGroup(G.Gpn)
                            phiElist = Coh.get_rational_cocycle(sign = 1,bound = 5,return_all =True)
                        except Exception as e:
                            out_str_vec.append(out_str.format(curve = '\'Err coh (%s)\''%e.message))
                            no_rational_line = True
                            continue
                        if Pnorm > max_P_norm_integrate:
                            out_str_vec.append(out_str.format(curve = '\'Prime too large to integrate (Pnorm = %s)\''%Pnorm))
                            continue
                        for phiE in phiElist:
                            try:
                                curve = fork(find_curve,timeout = max_waiting_time)(P,D,P*D*Np,prec,outfile=log_file,ramification_at_infinity = ram_at_inf,magma = magma,return_all = False,Up_method='bigmatrix',initial_data = [G,phiE])
                                curve = str(curve) # just in case
                            except Exception as e:
                                out_str_vec.append(out_str.format(curve = '\'Err (%s)\''%e.message))
                                continue
                            if 'timed out' in curve:
                                out_str_vec.append(out_str.format(curve = '\'Timed Out in find_curve\''))
                                continue
                            if curve == 'None':
                                new_out_str = out_str.format(curve = '\'Unrecognized\'')
                            else:
                                new_out_str = out_str.format(curve = curve)
                            out_str_vec.append(new_out_str)
                    except Exception as e:
                        out_str_vec.append(out_str.format(curve = '\'Unknown exception (%s)\''%e.message))
    return out_str_vec

# outfile='atest.txt'
# # Testing
# data = [[x^3-x^2+x-2]]
# Nrange = [10]
# for inp,out_str_vec in find_all_curves([(data[0][0],Nrange,max_P_norm,max_waiting_time)]):
#     for out_str in out_str_vec:
#         fwrite(out_str,outfile)

def compute_table(input_file,output_trail = None):
    global Nrange, max_P_norm, max_P_norm_integrate, max_waiting_time_aurel, max_waiting_time, max_F_disc, decimal_prec
    x = QQ['x'].gen()
    if output_trail is None:
        output_trail = '_computed.txt'
    load(input_file) # Initializes ``all_fields`` vector
    output_file = input_file.replace('.sage',output_trail)
    log_file = input_file.replace('.sage','.log')
    input_vec = [(datum[0],Nrange,max_P_norm,max_P_norm_integrate,max_waiting_time_aurel,max_waiting_time,decimal_prec,log_file) for datum in all_fields]

    # # DEBUG
    # for inp in input_vec:
    #     out_str_vec = find_all_curves(*inp)
    #     if out_str_vec == 'NO DATA':
    #         fwrite('NO DATA',output_file)
    #     else:
    #         for out_str in out_str_vec:
    #             fwrite(out_str,output_file)

    # REGULAR
    for inp,out_str_vec in find_all_curves(input_vec):
        if out_str_vec == 'NO DATA':
            fwrite('NO DATA',output_file)
        else:
            for out_str in out_str_vec:
                fwrite(out_str,output_file)
