# used to verify dataset correctness

import random
import math

random.seed(42)
USE_MONT = False

N = 8
InSize = 256
BaseSize = 64

# N = 1024
# InSize = 16
# BaseSize = 16
# modulus = 4007 # 12b
# mu = 33495 # 16b

# N = 1024
# InSize = 64
# BaseSize = 32
# # Barrett
# # modulus = 1152921504606846577 # 60b
# # mu = 9223372036854779000 # 64b
# # Mont.
# modulus = 17748036510181812557 # 64b
# mu = 11769938695513732997 # n', not mu for Barrett

# modulus = 3589109125839004175685800359 # 92b
# mu = 54654072181485643485796443864 # 96b

# N: 116 begin
'''
modulus = 41538374868278621028243970639921153 # 116b
mu = 1329227995784915872903807060083212256 # 120b 
# N: 116 end
'''

# N: 124 begin
'''
modulus = 21267647932558653966460912964485512497 # 124b
mu = 170141183460469231731687303715884111480 # 120b
# N: 124 end
'''

# Mont.
# modulus = 314893916791000603291454862963448458853 # 128b
# mu = 305817041278684739420340247558975148909 # n'

# N: 188 begin
'''
modulus = 391413006540853979723254332574612578537769751856289269811 # 188b
mu = 3145814454453517081702688962989576880651878088595387813283 # 192b
# N: 188 end
'''

# N: 244 begin
'''
modulus = 28269553036454149273332760011886696253239742350009903329945699220681913911 # 244b
mu = 226156424291633194186662080095093570025917938800079226639565593765455351368 # 248b
# N: 244 end
'''

# N: 252 begin
'''
modulus = 7027743565212848765676440327064703729222336898800080028220957462729896510181 # 252b
mu = 59619989534722887712477344028792269975066441801303261207817810644565192805376 # 256b
# N: 252 end
'''

# Mont.
# modulus = 104146878628309814226799871866525301758308907631144890574422957796423820812107 # 256b
# mu = 86398029835697469927966954678945403612729729935567251940217767921728922022499 # n'

# N: 316 begin
'''
modulus = 104697188298103731621607350869699042902700326113874073006597172226733221273613717195210620215611 # 316b
mu = 1361796545048917348133953997861052814124725982276501067562442850783901336700175227734691838785447 # 320b
# N: 316 end
'''

# N: 380 begin
'''
modulus = 2259584370240099908975171503226189253872885147750231543606272001246412298168889942514222823011807517309066056668089 # 380b
mu = 21471289597936942511848496444561653187196642388373155638611222610176022847257685796372957864896654204870319040524420 # 384b
# N: 380 end
'''

# N: 444 begin
'''
modulus = 42163756158208564869210873866135436009797329503556370460403748014227965831316503111570865057326349518689251099109329708282090179525507 # 444b
mu = 391549653120159177786080043702201452437411663841180806996458717684128330192196195464490840893924853319937882930373399650106601680105465 # 448b
# N: 444 end
'''

# N: 500 begin
'''
modulus = 2675836088189059019350300012489651245496945814395327594323156934120849692225327707334743369258251562552542007137026274542030631040301454349803725586033 # 500b
mu = 32035104449508739955324740738809466172586387011098367985411527728879034055202326761576813789927093277415781556771084265090178350879935590529204851033592 # 504b
# N: 500 end
'''

# N: 508 begin
'''
modulus = 525669482416392445595578695168562329288901870852618638836095804624065437137517238230800982769582208949054025331121980355411872810977153611848548469077481 # 508b
mu = 10686926356502433995531402994014829878643756356697675919264012157336623957677412790541200610675718507596618184568538671331767150719306702030298127962948952 # 512b
# N: 508 end
'''

# Mont.
# modulus = 7910290865926089532771781508648172187620341152008858217395718462979608689497031993972101713091929873152872996166199520499022506468214371404938331348183743 # 512b
# mu = 2777466859286970676964790370777993004276558734174245633201636868951957853535311574784851188106497049824199251325769147719990375122187765569015419541505343 # n'
# modulus = 38360757622011453780003512891597534923499674404368741080796406645436897699804662542709814031933028469621708729858001 # 384b
# mu = 9847749543419990163333897213655525536300188915551036916230113851640864374270029131732242346728657567900702330454321 # n'

# N: 572 begin
'''
modulus = 10310613998726579983810417288706406221065097301753360973923320151571407590076856145259747051717628956648372310131346962400862708152895695563970199535555443347028879022839503 # 572b
mu = 185404597086804805807385897593228686392512478118021040306208198195694342367175981175675791552992492022819813064207565671695181348823809353204033886610449388484175526942334336 # 576b
# N: 572 end
'''

# N: 636 begin
'''
modulus = 221443360051800973751253691786504451062089544815726239257544417494896381129077083855684431472731615524278078971278306397673523693741277994458562634344255235355311364359593759903256419374374333 # 636b
mu = 2937526607320075905373414482411051537331113023738806669643310249861944922030436227014258799845630112857705874098456349342307198132942982868449315850910264546594954774927394461768171390756291839 # 640b
# N: 636 end
'''

# N: 700 begin
'''
modulus = 3638264411458009147301369002987409584150317170832113616040416227774226315096118904347058293454624334021009403392274841712766162203831632046048332019486095984560671731052152306103113952413184667881092000701347041 # 700b
mu = 60840063444800481707436100366740743776492285069376634406019383885237466514183767398071716573657806345266347992106439511995248061875698158855256956671638131660361791284102344611799485552585375964990442223372070750 # 704b
# N: 700 end
'''

# N: 764 begin
'''
modulus = 94004047165710635085568527505291103125901631844201943057313092767874706285240686026932769775672480815776017257417135862807586451931789256888179308390478609379808522384091608522316677544231474881340610403421759418465284727313758623 # 764b
mu = 801266175364811066068690412438859509532526366721391781302522049725988544507282148228200253099488308109971919118424746048416696444899286524934379085954829687859916057983757959241187867247419673679212099027007909630819405377403923400 # 768b
# N: 764 end
'''

# N: 828 begin
'''
modulus = 1782533739463890241508622479786463592878156283030403290610592184634089913991990855499374953551701646281455432871960593420911919908521697031444720167967221828243062559348366975952937636636621383847239707038147310033380347287256274813571350691907316017 # 828b
mu = 14378879616226744132875097719586225340682120115538651857534349151595342419272089391612934576508411952752439866641834712588154971339210621792238770645708846949167807429966434174235396813983749312488438356171494173247805529124003125114478354943287251392 # 832b
# N: 828 end
'''

# N: 892 begin
'''
modulus = 16829171446954606962320984378329040883217164590087967185691880514652756749818279075469066842232018184086088896954912328947967615622572329072404194175354474937929186126616526238698175904550033318768021633377519357068043372861653455178503810120841971578133273051790284847 # 892b
mu = 518250245762910832604671454292748487853990937890310938909190391989837417734051793277552231413687067927551843899766468044057475382328280249080241910491915353446009389677388514321330409404342249594178722970349410333553987751127890986564147749920552982774783291210874614935 # 896b
# N: 892 end
'''

# N: 956 begin
'''
modulus = 380635091449667311019174571552539546051049263368871990747471527434415368598530957028662739138952855360661354069127397616987441196256208632374888380866417707737912507770873091321814649045516484969068330113465442126069526080183334972296766722988726859708264075754071470288785711174523422759 # 956b
mu = 7797095836845903285904964596477116971170151336694302275863218789689759378454529582800883972635675154803619703992788845597859607088614236716141127368440366282982981870982085209975575742978531009710660044584742074902586785639340570181198955856954001764448724371852320046440996504644001712379 # 960b
# N: 956 end
'''

# N: 1012 begin
'''
modulus = 26219665417856637699286108407326698164192891346198812700226860689076004405200297767491441243098781415061414859422335539046464937654735993482704198241986343246532772287564327613468290572521362305467250631822104125099608988613769574143020423906653427459573339639845143927922583771129933560654085504231743669 # 1012b
mu = 587724865710234727853389717540142332585764121200421761236975617229398994434532706551636346482332753870255294905055824408015706665976549365704775166032123161989918598445540209466361489422495319902848864120366572372020458617838825467902788239757810994495168264622932239113113822293332270032360073870067819948 # 1016b
# N: 1012 end
'''

# N: 1020 begin
'''
modulus = 8770938812795625299677713467977347754203906613835205724674307155547578599276263714758787329109134060705609979043413214426031844734738762024263874659216440550046999533064414055125793056504429494586635083121536248226070570040532464305972294495146873210292088382249748148652291770561273775370573819107685154043 # 1020b
mu = 115142342374473153204121999964739270811321469857866869354500092527176039814455303526531457366024615400118535178998880845812020784374203729572517663762227699036122571497164464748369880503598089280563380023041140447479007300334205744755093361762546745492205441691956086586153750746744465964358753347296264105003 # 1020b
# N: 1020 end
'''

# Mont.
# modulus = 148735191028630373711846539597472811322460065450223988969420531648331628062718493991213660679833782456273030831710666100777181497398980685132340925872672524919230145363353771924477873794358536811867172701931293948182750346348621065941421844938839694297301127299957089217914118382249339147576109679875731468929 # 1024b
# mu = 96164927394059612931017430862079807317370986030650841058432758410859577236053286291356732458852197927199445364691395925768463688537154547276142444691898619266869864266290748720835531812068659538273881725297973859303236232096618681876020591876927053479623843994331623963668826971922784369685563249489587375489 # n'

file_out = "data.txt"

def barrett(a, mu, modulus):
    MBITS=modulus.bit_length()
    t = a
    a = a >> (MBITS - 2)
    a = a * mu
    a >>= (MBITS + 5)
    t -= a * modulus
    if t > modulus:
        t -= modulus
    return t

def mont_mul(a, b, modulus):
    return redc(a * b, modulus, r, n_prime)

# Montgomery reduction
def redc(T, modulus, r, n_prime):
    
    # print(T)
    # r = 2^k > modulus
    # this requires modulus to be entire word so that we can just drop/keep a word
    # mod 2^k: keep only right-most k bits
    # / 2^k: get rid of right-most k bits (by shifting right k bit)
    
    # mullo to compute T
    t1 = T % r # Tr < r # keep Tl of T = [Th, Tl]
    t2 = t1 * n_prime # 2b = b * b # mullo
    m = t2 % r # m < r # keep last word
    t3 = m * modulus # 2b = b * b # mulhi
    
    # subhi
    # take Th, t3h
    # if Th < t3h, Th += modulus
    # t = Th - t3h
    t = (T - t3) // r # keep the high part
    # print(t)
    if t < 0:
        t += modulus
        # print(t)
    return t

# every element after to_mont is < modulus
def to_mont(x, modulus, r):
    return (x * r) % modulus

def from_mont(x, modulus, r, n_prime):
    return redc(x, modulus, r, n_prime)

def compute_mu(modulus):
    # ((input >> (2*Mbits+3)) * mu ) = a / mod
    print("mod bit: ", modulus.bit_length())
    mu = math.floor((2**(2*modulus.bit_length()+3)) // modulus)
    print("mu bit: ", mu.bit_length())
    return mu

def generate_integers(length, min_digits, modulus):
    result = []
    while len(result) < length:
        num = random.randint(0, modulus - 1)
        binary_str = bin(num)[2:]  # Convert to binary string, remove '0b' prefix
        if len(binary_str) >= min_digits:
            result.append(num)
    return result[:length]

def breakdown_large_integers(insize, basesize, integers):
    # Calculate the number of smaller integers needed to represent the large integer
    num_chunks = insize // basesize
    
    # Mask to extract chunks of 'basesize' bits
    mask = (1 << basesize) - 1
    
    # List to store smaller integers
    smaller_integers = []
    
    for large_integer in integers:
        # Break down the large integer into smaller integers
        chunks = [(large_integer >> i * basesize) & mask for i in range(num_chunks)]
        
        # Reverse the order of chunks to maintain consistency
        chunks.reverse()
        
        # Append the smaller integers to the result list
        smaller_integers.extend(chunks)
    
    return smaller_integers

# compute
if USE_MONT:
    # Montgomery multiplication is just any kind of mult. in Mont. space with redc
    def mulmod(a, b, modulus, mu):
        return mont_mul(a, b, modulus)
else:                         
    def mulmod(a, b, modulus, mu):
        return (a * b) % modulus

def addmod(a, b, modulus, mu):
    return (a + b) % modulus

def submod(a, b, modulus, mu):
    return (a - b) % modulus

# ----------------- BEGIN of SPIRAL-generated code -----------------  

# This code was generated by Spiral 8.5.1, www.spiral.net

def nttmp(Y, X, modulus, twiddles, mu): 
    s73 = mulmod(twiddles[1], X[4], modulus, mu)
    t87 = addmod(X[0], s73, modulus, mu)
    t88 = submod(X[0], s73, modulus, mu)
    s74 = mulmod(twiddles[1], X[5], modulus, mu)
    t89 = addmod(X[1], s74, modulus, mu)
    t90 = submod(X[1], s74, modulus, mu)
    s75 = mulmod(twiddles[1], X[6], modulus, mu)
    s76 = mulmod(twiddles[1], X[7], modulus, mu)
    s77 = mulmod(twiddles[2], addmod(X[2], s75, modulus, mu), modulus, mu)
    t91 = addmod(t87, s77, modulus, mu)
    t92 = submod(t87, s77, modulus, mu)
    s78 = mulmod(twiddles[2], addmod(X[3], s76, modulus, mu), modulus, mu)
    s79 = mulmod(twiddles[4], addmod(t89, s78, modulus, mu), modulus, mu)
    Y[0] = addmod(t91, s79, modulus, mu)
    Y[1] = submod(t91, s79, modulus, mu)
    s80 = mulmod(twiddles[5], submod(t89, s78, modulus, mu), modulus, mu)
    Y[2] = addmod(t92, s80, modulus, mu)
    Y[3] = submod(t92, s80, modulus, mu)
    s81 = mulmod(twiddles[3], submod(X[2], s75, modulus, mu), modulus, mu)
    t93 = addmod(t88, s81, modulus, mu)
    t94 = submod(t88, s81, modulus, mu)
    s82 = mulmod(twiddles[3], submod(X[3], s76, modulus, mu), modulus, mu)
    s83 = mulmod(twiddles[6], addmod(t90, s82, modulus, mu), modulus, mu)
    Y[4] = addmod(t93, s83, modulus, mu)
    Y[5] = submod(t93, s83, modulus, mu)
    s84 = mulmod(twiddles[7], submod(t90, s82, modulus, mu), modulus, mu)
    Y[6] = addmod(t94, s84, modulus, mu)
    Y[7] = submod(t94, s84, modulus, mu)

# ----------------- END of SPIRAL-generated code -----------------

min_digits = modulus.bit_length() - 2
# Mont.
r = 1 << modulus.bit_length()
n_prime = pow(modulus, -1, r)

X = generate_integers(N, min_digits, modulus)
twiddles = generate_integers(N, min_digits, modulus)
# print(X)
if USE_MONT:
    X = [to_mont(e, modulus, r) for e in X]
    twiddles = [to_mont(e, modulus, r) for e in twiddles]
# print(X)

# init. Y
Y = [0] * len(X)

nttmp(Y, X, modulus, twiddles, mu)

# transform back to check correctness against data.txt without Mont.
# if USE_MONT:
#     # don't need this as testing data
#     Y = [from_mont(e, modulus, r, n_prime) for e in Y]
#     X = [from_mont(e, modulus, r, n_prime) for e in X] 
#     twiddles = [from_mont(e, modulus, r, n_prime) for e in twiddles] 

# print("Result of NTT:", Y)

# with open(file_out, 'w') as file:
#         file.write("InInt mu = " + str(mu) + ";\n")
#         file.write("InInt modulus = " + str(modulus) + ";\n")
#         file.write("InInt _twd[N] = {" + ', '.join(map(str, twiddles)) + "};\n")
#         file.write("InInt _x[N] = {" + ', '.join(map(str, X)) + "};\n")
#         file.write("InInt _y[N] = {" + ', '.join(map(str, Y)) + "};\n")

# unpacked version
upmu = breakdown_large_integers(InSize, BaseSize, [mu])
upmod = breakdown_large_integers(InSize, BaseSize, [modulus])
uptwd = breakdown_large_integers(InSize, BaseSize, twiddles)
upx = breakdown_large_integers(InSize, BaseSize, X)
upy = breakdown_large_integers(InSize, BaseSize, Y)

with open(file_out, 'w') as file:
        file.write("\n")
        file.write("BaseInt upmu[N*InRatio] = {" + ', '.join(map(str, upmu)) + "};\n")
        file.write("BaseInt upmodulus[N*InRatio] = {" + ', '.join(map(str, upmod)) + "};\n")
        file.write("BaseInt uptwd[N*InRatio] = {" + ', '.join(map(str, uptwd)) + "};\n")
        file.write("BaseInt upx[N*InRatio] = {" + ', '.join(map(str, upx)) + "};\n")
        file.write("BaseInt upy[N*InRatio] = {" + ', '.join(map(str, upy)) + "};\n")
