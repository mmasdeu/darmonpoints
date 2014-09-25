load('darmonpoints.sage')
from sage.misc.misc import alarm,cancel_alarm
from sage.parallel.decorate import parallel,fork
######################
# Parameters         #
######################

x = QQ['x'].gen()

Nrange = range(1,200) # Conductors to explore
max_P_norm = 200 # Maximum allowed conductor
max_F_disc = None # Maximum size of discriminant of base field
max_waiting_time = 5 * 60 * 60 # Amount of patience (in seconds)
chunk_length = 20
decimal_prec = 40

@parallel
def find_all_curves(pol,Nrange,max_P_norm,max_waiting_time):
    load('darmonpoints.sage')
    from sarithgroup import BigArithGroup
    from homology import construct_homology_cycle,lattice_homology_cycle
    from cohomology import CohomologyGroup, get_overconvergent_class_quaternionic
    from util import enumerate_words, quaternion_algebra_from_discriminant

    try:
        page_path = ROOT + '/KleinianGroups-1.0/klngpspec'
    except NameError:
        ROOT = os.getcwd()
        page_path = ROOT + '/KleinianGroups-1.0/klngpspec'

    from sage.interfaces.magma import Magma
    magma = Magma()
    magma.attach_spec(page_path)

    sys.setrecursionlimit(10**6)
    x = pol.parent().gen()
    # r = QQ['r'].gen()
    out_str_vec = []
    for N in Nrange:
        print 'N = %s'%N
        F.<r> = NumberField(pol)
        # if gcd(F.discriminant(),N) != 1:
        #     continue
        if len(F.narrow_class_group()) > 1:
            continue
        for a in F.elements_of_norm(N):
            print 'pol = %s'%pol
            facts = F.ideal(a).factor()
            # if any([e > 1 for f,e in facts]):
            #     verbose('e > 1')
            #     continue
            nfactors = len(facts)
            for j,Pe in enumerate(facts):
                P,e = Pe
                if e > 1:
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
                    assert N == NE.norm()
                    prec = (RR(decimal_prec) * RR(10).log(Pnorm)).ceil()
                    out_str = '[%s, %s, %s, %s, %s, %s, {curve}, {right_conductor}, %s],\\'%(N,F.discriminant(),pol,P.gens_reduced()[0],D.gens_reduced()[0],Np.gens_reduced()[0],prec)
                    ram_at_inf = [-1 for o in F.real_embeddings()]
                    if F.signature()[1] == 0:
                        ram_at_inf[0] = 1
                    try:
                        G = BigArithGroup(P,quaternion_algebra_from_discriminant(F,D,ram_at_inf).invariants(),Np,base = F,use_sage_db = False,grouptype = None,magma = magma)
                    except Exception as e:
                        out_str_vec.append('Error when computing G: ' + e.message)
                        continue
                    try:
                        Coh = CohomologyGroup(G.Gpn)
                        phiElist = Coh.get_rational_cocycle(sign = 1,bound = 5,return_all =True)
                    except Exception as e:
                        out_str_vec.append('Error when finding cohomology class: ' + e.message)
                        continue
                    for phiE in phiElist:
                        # curve = 'P,D,N = %s'%(P.reduced_gens()[0],D.reduced_gens()[0],(P*D*Np).reduced_gens()[0])
                        curve = fork(find_curve,timeout = max_waiting_time)(P,D,P*D*Np,prec,outfile='tmp.txt',ramification_at_infinity = ram_at_inf,magma = magma,return_all = False,Up_method='bigmatrix',initial_data = [G,phiE])
                        if curve is None:
                            new_out_str = out_str.format(curve = 'Not recognized',right_conductor = 'False')
                        else:
                            try:
                                curve_conductor = curve.conductor()
                                new_out_str = out_str.format(curve = curve.a_invariants(),right_conductor = (curve_conductor == P*D*Np))
                            except AttributeError:
                                if 'timed out' in curve:
                                    new_out_str = out_str.format(curve = '\'Timed out\'',right_conductor = '\'False\'')
                                else:
                                    new_out_str = out_str.format(curve = '\'Error '+ curve + ' \'',right_conductor = '\'False\'')
                        out_str_vec.append(new_out_str)
    return out_str_vec

# # Testing
# data = [[x^3-x^2-x+2]]
# Nrange = [34]
# for inp,out_str_vec in find_all_curves([(data[0][0],Nrange,max_P_norm,max_waiting_time)]):
#     for out_str in out_str_vec:
#         fwrite(out_str,outfile)



def compute_table(input_file,output_trail = None):
    if output_trail is None:
        output_trail = '_computed.txt'
    load(input_file) # Initializes ``all_fields`` vector
    input_vec = [(datum[0],Nrange,max_P_norm,max_waiting_time) for datum in all_fields]
    output_file = input_file + output_trail
    for inp,out_str_vec in find_all_curves(input_vec):
        for out_str in out_str_vec:
            fwrite(out_str,output_file)
