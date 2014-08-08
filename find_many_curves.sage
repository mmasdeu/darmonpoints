load('darmonpoints.sage')
from sage.misc.misc import alarm,cancel_alarm
from sage.parallel.decorate import parallel,fork
######################
# Parameters         #
######################

x = QQ['x'].gen()
max_waiting_time = 10 * 60 * 60 # Amount of patience (in seconds)
decimal_prec = 60
outfile = 'curve_table_real_new.sage'

@parallel
def find_one_curve(inp):
    x = QQ['x'].gen()
    # pol,P,D,Np,Pnorm,Nnorm = inp
    Nnorm, _, pol, P, D, Np, curve_message, matching_conductor = inp
    pol = x.parent()(pol)
    F.<r> = NumberField(pol)
    P = F.ideal(P)
    Pnorm = P.norm()
    D = F.ideal(D)
    Np = F.ideal(Np)
    NEnorm = (P*D*Np).norm()
    if NEnorm != Nnorm:
        return 'NE norms do not coincide'
    prec = (RR(decimal_prec) * RR(10).log(Pnorm)).ceil()
    working_prec = min([2 * prec,200])
    out_str = '[%s, %s, %s, %s, %s, %s, {curve}, {right_conductor}],\\'%(NEnorm,F.discriminant(),pol,P.gens_reduced()[0],D.gens_reduced()[0],Np.gens_reduced()[0])
    if matching_conductor == True:
        return out_str.format(curve = curve_message, right_conductor = 1)
    ram_at_inf = [-1 for a in F.real_embeddings()]
    ram_at_inf[0] = 1
    curve = fork(find_curve,timeout = max_waiting_time)(P,D,P*D*Np,prec,working_prec,outfile='tmp.txt',ramification_at_infinity = ram_at_inf)

    if curve is None:
        out_str = out_str.format(curve = 'Not recognized',right_conductor = 'False')
    else:
        try:
            curve_conductor = curve.conductor()
            out_str = out_str.format(curve = curve.a_invariants(),right_conductor = (curve_conductor == P*D*Np))
        except AttributeError:
            if 'timed out' in curve:
                out_str = out_str.format(curve = '\'Timed out\'',right_conductor = '\'False\'')
            else:
                out_str = out_str.format(curve = '\'Error '+ curve + ' \'',right_conductor = '\'False\'')
    return out_str


x = QQ['x'].gen()
r = QQ['r'].gen()
load('curve_table_real.sage')
data = sorted(data,key = lambda x:x[0])

for inp,out_str in find_one_curve(data):
    fwrite(out_str,outfile)
