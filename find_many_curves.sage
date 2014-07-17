load('darmonpoints.sage')
from sage.misc.misc import alarm,cancel_alarm
from sage.parallel.decorate import parallel,fork
######################
# Parameters         #
######################

x = QQ['x'].gen()
max_waiting_time = 60 * 60 # Amount of patience (in seconds)
decimal_prec = 60
outfile = 'curve_table'

@parallel
def find_one_curve(inp):
    pol,P,D,Np,Pnorm,Nnorm = inp
    F.<r> = NumberField(pol)
    P = F.ideal(P)
    D = F.ideal(D)
    Np = F.ideal(Np)
    Pnorm = ZZ(Pnorm)
    NEnorm = (P*D*Np).norm()
    prec = (RR(decimal_prec) * RR(10).log(Pnorm)).ceil()
    working_prec = 2 * prec
    out_str = '[%s, %s, %s, %s, %s, %s, {curve}, {right_conductor}],\\'%(NEnorm,F.discriminant(),pol,P.gens_reduced()[0],D.gens_reduced()[0],Np.gens_reduced()[0])
    curve = fork(find_curve,timeout = max_waiting_time)(P,D,P*D*Np,prec,working_prec)
    try:
        curve_conductor = curve.conductor()
        out_str.format(curve = curve.a_invariants(),right_conductor = (curve_conductor == P*D*Np))
    except AttributeError:
        if 'timed out' in curve:
            out_str.format(curve = 'Timed out',right_conductor = 'False')
        else:
            out_str.format(curve = 'Error',right_conductor = 'False')
    return out_str


r = QQ['r'].gen()
load('all_candidates.sage')
data = sorted(data,key = lambda x:x[-1])

for inp,out_str in find_one_curve(data):
    fwrite(out_str,outfile)

