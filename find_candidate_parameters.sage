load('darmonpoints.sage')
from sage.misc.misc import alarm,cancel_alarm
######################
# Parameters         #
######################
use_ps_dists = False
x = QQ['x'].gen()
Nrange = range(5,120) # Conductors to explore
max_P_norm = 20 # Maximum allowed conductor
max_F_disc = 3000 # Maximum size of discriminant of base field
max_waiting_time = 100 # Amount of patience (in seconds)

load('imquad_fields.sage')

outfile = 'field_data.txt'
from sarithgroup import ArithGroup
set_verbose(0)
with open(outfile,'a') as fout:
    for N in Nrange:
        print 'N = %s'%N
        for datum in data:
            if ZZ(datum[1]).abs() > max_F_disc:
                break
            pol = datum[0]
            F.<r> = NumberField(pol)
            if gcd(F.discriminant(),N) != 1:
                continue
            if len(F.narrow_class_group()) > 1:
                continue
            for a in F.elements_of_norm(N):
                print 'pol = %s'%pol
                facts = F.ideal(a).factor()
                if any([e > 1 for f,e in facts]):
                    continue
                nfactors = len(facts)
                for j,Pe in enumerate(facts):
                    P,_ = Pe
                    if not ZZ(P.norm()).is_prime():
                        continue
                    if ZZ(P.norm()).abs() > max_P_norm:
                        continue
                    for v in enumerate_words([0,1],[0 for o in facts],nfactors):
                        if v[j] == 0:
                            continue
                        D = F.ideal(1)
                        Np = F.ideal(1)
                        n_factors_in_discriminant = 0
                        for i in range(nfactors):
                            if i == j:
                                continue
                            if v[i] == 1:
                                n_factors_in_discriminant +=1
                                D *= facts[i][0]
                            else:
                                Np *= facts[i][0]
                        if n_factors_in_discriminant % 2 != 0:
                            continue
                        NE = P * D * Np
                        assert NE == F.ideal(a)
                        try:
                            alarm(max_waiting_time)
                            abtuple = quaternion_algebra_from_discriminant(F,D,[-1 for o in F.real_embeddings()]).invariants()
                            G = ArithGroup(F,D,abtuple,level = P * Np)
                            ngens = len(G.abelianization().free_gens())
                            cancel_alarm()
                            if ngens > 0:
                                print 'Found, p = %s, F = %s, length %s'%(P.norm(),F,ngens)
                                fout.write('%s %s %s %s %s %s %s\n'%(F,P,D,Np,P.norm(),(P*D*Np).norm(),ngens))
                                fout.flush()
                        except KeyboardInterrupt:
                            print 'Skipping, Magma takes too long (p = %s, F = %s, NE = %s)'%(P.norm(),F,NE.norm())
                        except RuntimeError:
                            print 'Skipping, might be a bug'

