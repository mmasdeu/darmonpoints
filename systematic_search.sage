# load('darmonpoints.sage')
from sage.parallel.decorate import parallel,fork
from sage.misc.misc import alarm, cancel_alarm
from util import fwrite

######################
# Parameters         #
######################
Nrange = range(1,200) # Conductors to explore
max_P_norm = 200 # Maximum allowed norm for the chosen prime
max_P_norm_integrate = 23 # Maximum allowed norm for the chosen prime to integrate
max_F_disc = None # Maximum size of discriminant of base field
max_waiting_time_aurel = 30 * 60 # Amount of patience (in seconds)
max_waiting_time = 2 * 60 * 60 # Amount of patience (in seconds)
decimal_prec = 50

def find_num_classes(P,abtuple,Np,F,out_str):
    load('darmonpoints.sage')
    from sarithgroup import BigArithGroup
    from homology import construct_homology_cycle,lattice_homology_cycle
    from cohomology import CohomologyGroup, get_overconvergent_class_quaternionic
    from itertools import product,chain,izip,groupby,islice,tee,starmap
    from sage.modules.fg_pid.fgp_module import FGP_Module,FGP_Module_class
    from sage.matrix.constructor import matrix,Matrix,block_diagonal_matrix,block_matrix
    from util import tate_parameter,update_progress,get_C_and_C2,getcoords,recognize_point,fwrite
    import os,datetime
    from sage.misc.persist import db
    from sage.rings.padics.precision_error import PrecisionError
    from util import enumerate_words, discover_equation,get_heegner_params,fwrite,quaternion_algebra_invariants_from_ramification, direct_sum_of_maps
    from integrals import integrate_H1,double_integral_zero_infty,indef_integral
    from sage.ext.c_lib import AlarmInterrupt
    from sage.misc.misc import alarm, cancel_alarm
    from sage.rings.integer_ring import ZZ

    try:
        G = BigArithGroup(P,abtuple,Np,base = F,use_sage_db = False,grouptype = "PGL2", magma = None,seed = 12345)
    except Exception as e:
        return out_str.format(curve = '\'Err G (%s)\''%e.message)
    try:
        Coh = CohomologyGroup(G.Gpn)
        phiElist = Coh.get_rational_cocycle(sign = 1,bound = 5,return_all =True)
    except Exception as e:
        return out_str.format(curve = '\'Err coh (%s)\''%e.message)
    except (AlarmInterrupt,KeyboardInterrupt):
        return out_str.format(curve = '\'Timed out in get_rational_cocycle\'')
    return len(phiElist)


@parallel
def find_all_curves(pol,Nrange,max_P_norm,max_P_norm_integrate,max_waiting_time_aurel,max_waiting_time,decimal_prec,log_file):
    load('darmonpoints.sage')
    from homology import construct_homology_cycle,lattice_homology_cycle
    from cohomology import CohomologyGroup, get_overconvergent_class_quaternionic
    from itertools import product,chain,izip,groupby,islice,tee,starmap
    from sage.modules.fg_pid.fgp_module import FGP_Module,FGP_Module_class
    from sage.matrix.constructor import matrix,Matrix,block_diagonal_matrix,block_matrix
    from util import tate_parameter,update_progress,get_C_and_C2,getcoords,recognize_point,fwrite
    import os,datetime
    from sage.misc.persist import db
    from sage.rings.padics.precision_error import PrecisionError
    from util import enumerate_words,discover_equation,get_heegner_params,fwrite,quaternion_algebra_invariants_from_ramification, direct_sum_of_maps
    from integrals import integrate_H1,double_integral_zero_infty,indef_integral
    from sage.ext.c_lib import AlarmInterrupt
    from sage.misc.misc import alarm, cancel_alarm
    from sage.rings.integer_ring import ZZ

    out_str_vec = []

    F = NumberField(pol,names='r')
    r = F.gen()

    if len(F.narrow_class_group()) > 1:
        return out_str_vec
    sys.setrecursionlimit(10**6)
    x = pol.parent().gen()
    no_rational_line = False
    try:
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
                        ram_at_inf = F.real_places(prec = Infinity)
                        if F.signature()[1] == 0:
                            ram_at_inf = ram_at_inf[1:]
                        for phiE in phiElist:
                            try:
                                alarm(max_waiting_time)
                                curve = find_curve(P,D,P*D*Np,prec,outfile=log_file,ramification_at_infinity = ram_at_inf, grouptype = "PGL2", magma = G.magma, magma_seed = 12345, return_all = False,Up_method='bigmatrix',initial_data = [G,phiE])
                                cancel_alarm()
                                curve = str(curve) # just in case
                            except Exception as e:
                                new_out_str = out_str.format(curve = '\'Err (%s)\''%e.message)
                                cancel_alarm()
                            except (AlarmInterrupt,KeyboardInterrupt):
                                new_out_str = out_str.format(curve = '\'Timed Out in find_curve\'')
                            except:
                                new_out_str = out_str.format(curve = '\'Probably Timed Out in find_curve\'')
                            else:
                                new_out_str = out_str.format(curve = curve)
                            out_str_vec.append(new_out_str)
    except:
        out_str_vec.append('Unknown exception field of discriminant %s (%s results preced)'%(F.discriminant(),len(out_str_vec)))
    return out_str_vec

def compute_table(input_file,output_trail = None):
    global Nrange, max_P_norm, max_P_norm_integrate, max_waiting_time_aurel, max_waiting_time, max_F_disc, decimal_prec
    x = QQ['x'].gen()
    if output_trail is None:
        output_trail = '_computed.txt'
    load(input_file) # Initializes ``all_fields`` vector
    output_file = input_file.replace('.sage',output_trail)
    log_file = input_file.replace('.sage','.log')
    input_vec = [(datum[0],Nrange,max_P_norm,max_P_norm_integrate,max_waiting_time_aurel,max_waiting_time,decimal_prec,log_file) for datum in all_fields]

    for inp,out_str_vec in find_all_curves(input_vec):
        if out_str_vec == 'NO DATA':
            fwrite('NO DATA',output_file)
        else:
            for out_str in out_str_vec:
                fwrite(out_str,output_file)

@parallel
def find_few_curves(F,P,D,Np,ram_at_inf,max_P_norm_integrate,max_waiting_time_aurel,max_waiting_time,decimal_prec,log_file,covol):
    load('darmonpoints.sage')
    from homology import construct_homology_cycle,lattice_homology_cycle
    from cohomology import CohomologyGroup, get_overconvergent_class_quaternionic
    from itertools import product,chain,izip,groupby,islice,tee,starmap
    from sage.modules.fg_pid.fgp_module import FGP_Module,FGP_Module_class
    from sage.matrix.constructor import matrix,Matrix,block_diagonal_matrix,block_matrix
    from util import tate_parameter,update_progress,get_C_and_C2,getcoords,recognize_point,fwrite
    import os,datetime
    from sage.misc.persist import db
    from sage.rings.padics.precision_error import PrecisionError
    from util import enumerate_words, discover_equation,get_heegner_params,fwrite,quaternion_algebra_invariants_from_ramification, direct_sum_of_maps
    from integrals import integrate_H1,double_integral_zero_infty,indef_integral
    from sage.ext.c_lib import AlarmInterrupt
    from sage.misc.misc import alarm, cancel_alarm
    from sage.rings.integer_ring import ZZ

    out_str_vec = []
    pol = F.polynomial()
    # F = NumberField(pol,names='r')
    # r = F.gen()
    P = F.ideal(P)
    D = F.ideal(D)
    Np = F.ideal(Np)
    sys.setrecursionlimit(10**6)
    # x = pol.parent().gen()
    try:
        try:
            NE = P * D * Np
            Pnorm = P.norm()
            prec = (RR(decimal_prec) * RR(10).log(Pnorm)).ceil()
            out_str = '[%s, %s, %s, %s, %s, %s, {curve}, %s, %s],\\'%(NE,F.discriminant(),pol,P.gens_reduced()[0],D.gens_reduced()[0],Np.gens_reduced()[0],prec,covol)
            abtuple = quaternion_algebra_invariants_from_ramification(F,D,ram_at_inf)
        except:
            out_str_vec.append(out_str.format(curve = '\'Err G (initialization)\''))
            return out_str_vec
        num_classes = ZZ(-1)
        try:
            num_classes = fork(find_num_classes,timeout = max_waiting_time_aurel)(P,abtuple,Np,F,out_str)
            num_classes = ZZ(num_classes)
        except TypeError as e:
            if hasattr(num_classes,'startswith'):
                if num_classes.startswith('NO DATA'):
                    if 'imed out' in num_classes:
                        out_str_vec.append(out_str.format(curve = '\'Err G (Timed out)\''))
                    else:
                        out_str_vec.append(out_str.format(curve = '\'Err G (%s)\''%num_classes[7:]))
                else:
                    out_str_vec.append(str(num_classes))
                return out_str_vec
            else:
                out_str_vec.append(out_str.format(curve = '\'Err G(%s)\''%str(e.message)))
                return out_str_vec
        except:
            out_str_vec.append('\'Err G(unhandled: %s)\''%num_classes)
            return out_str_vec
        if num_classes <= 0:
            out_str_vec.append(out_str.format(curve = '\'Err G (No rational classes)\''))
            return out_str_vec
        if Pnorm > max_P_norm_integrate:
            out_str_vec.append( out_str.format(curve = '\'Prime too large to integrate (Pnorm = %s)\''%Pnorm))
            return out_str_vec
        try:
            curve = fork(find_curve,timeout = num_classes * max_waiting_time)(P,D,P*D*Np,prec,outfile=log_file,ramification_at_infinity = ram_at_inf, magma_seed = 1123, grouptype = "PGL2", return_all = True,Up_method='bigmatrix')
            if hasattr(curve,'startswith'):
                out_str_vec.append( out_str.format(curve = str(curve)))
            else:
                out_str_vec.extend( out_str.format(curve = str(o)) for o in curve) # Success
        except Exception as e:
            out_str_vec.append( out_str.format(curve = '\'Err (%s)\''%str(e.message)))
        except (AlarmInterrupt,KeyboardInterrupt):
            out_str_vec.append( out_str.format(curve = '\'Timed Out in find_curve\''))
        except:
            out_str_vec.append( out_str.format(curve = '\'Probably Timed Out in find_curve\''))
    except Exception as e:
        try:
            out_str_vec.append(out_str.format(curve = 'unhandled exception: %s'%str(e.message)))
        except:
            out_str_vec.append('Unknown exception (%s), field of discriminant %s (%s results preced)'%(str(e.message),F.discriminant(),len(out_str_vec)))
    return out_str_vec


def compute_table_in_order(candidates,output_file,c0 = 0, c1 = 200,step = 50):
    global Nrange, max_P_norm, max_P_norm_integrate, max_waiting_time_aurel, max_waiting_time, max_F_disc, decimal_prec
    log_file = output_file.replace('.txt','.log')
    for cov in range(c0,c1,step):
        good_candidates = filter(lambda x:x[-1] >= cov and x[-1] < cov + step,candidates)
        input_vec = [(datum[0],datum[1],datum[2],datum[3],datum[4],max_P_norm_integrate,max_waiting_time_aurel,max_waiting_time,decimal_prec,log_file,datum[-1]) for datum in good_candidates]
        fwrite('# Starting range %s..%s'%(cov,cov+step),output_file)
        for inp,out_str_vec in find_few_curves(input_vec):
            if out_str_vec == 'NO DATA':
                fwrite('NO DATA',output_file)
            else:
                for out_str in out_str_vec:
                    fwrite(out_str,output_file)

def dry_run(input_file,covolume_bound):
    from homology import construct_homology_cycle,lattice_homology_cycle
    from cohomology import CohomologyGroup, get_overconvergent_class_quaternionic
    from util import enumerate_words, quaternion_algebra_invariants_from_ramification,covolume
    from itertools import product,chain,izip,groupby,islice,tee,starmap
    from sage.modules.fg_pid.fgp_module import FGP_Module,FGP_Module_class
    from sage.matrix.constructor import matrix,Matrix,block_diagonal_matrix,block_matrix
    from util import tate_parameter,update_progress,get_C_and_C2,getcoords,recognize_point,fwrite
    import os,datetime
    from sage.misc.persist import db
    from sage.rings.padics.precision_error import PrecisionError
    from util import discover_equation,get_heegner_params,fwrite, direct_sum_of_maps
    from integrals import integrate_H1,double_integral_zero_infty,indef_integral
    from sage.ext.c_lib import AlarmInterrupt
    from sage.misc.misc import alarm, cancel_alarm

    load('darmonpoints.sage')
    global Nrange, max_P_norm, max_P_norm_integrate, max_waiting_time_aurel, max_waiting_time, max_F_disc, decimal_prec, candidates

    x = QQ['x'].gen()
    load(input_file) # Initializes ``all_fields`` vector
    candidates = []
    for datum in all_fields:
        pol = datum[0]
        F = NumberField(pol,names='r')
        zeta = F.zeta_function(53)(2)
        print F.discriminant()
        r = F.gen()
        if F.class_number(proof = False) > 1:
            continue
        if len(F.narrow_class_group(proof = False)) > 1:
            continue
        x = pol.parent().gen()
        for N in Nrange:
            for a in F.elements_of_norm(N):
                facts = F.ideal(a).factor()
                nfactors = len(facts)
                for j,Pe in enumerate(facts):
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
                        ram_at_inf = F.real_places(prec = Infinity)
                        if F.signature()[1] == 0:
                            ram_at_inf = ram_at_inf[1:]
                        covol = covolume(F,D,P * Np,prec = 53, zeta = zeta)
                        verbose('Estimated Covolume = %s'%covol)
                        difficulty = covol**2
                        verbose('Estimated Difficulty = %s'%difficulty)
                        if covol < covolume_bound:
                            candidates.append([F,P,D,Np,ram_at_inf,covol])
    return candidates
