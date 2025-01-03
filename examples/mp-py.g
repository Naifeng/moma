# PALISDADE Multi-Precision example

Load(fftx);
ImportAll(fftx);
Load(nttx);
ImportAll(nttx);

# NTT size
n := 8;

# forward or inverse 
fwd := true;
# fwd := false; 

# mixed precision
# mxp := true;
mxp := false; # always

# using macro for arithmetic operations or not
useMacro := true; # always
# useMacro := false;

# insize: [input data bit-length]
# basesize: [system data bit-length]

# insize := 32; mbits := 28; basesize := 16;
insize := 64; mbits := 60; basesize := 32; 
# insize := 128; mbits := 124; basesize := 64; 

# name := When(fwd, "ntt", "intt")::StringInt(n)::"mp";
name := When(fwd, "ntt", "intt")::"mp"; # easier for testing
conf := LocalConfig.nttx.mpPyConf();

p := var("modulus", conf.type());
if not fwd then cyclo := var("cyclo", conf.type()); fi;
mu := var("mu", conf.type());
twiddles := var("twiddles", TPtr(conf.type()));

ntt := When(fwd, NTT, iNTT);
twrec := CopyFields(rec(n := n, modulus := p, twiddles := twiddles, mu := mu, 
                        mxp := mxp, useMacro := useMacro, insize := insize,
                        basesize := basesize, mbits := mbits), 
    When(fwd, rec(), rec( cyclo := cyclo)));
funcrec := CopyFields(rec(abstractType := conf.type(), fname := name, params := [p, twiddles]::When(fwd, [], [cyclo])::[mu]), twrec);

t := TFCall(ntt(n, twrec), funcrec);
opts := conf.getOpts(t);
tt := opts.tagIt(t);

rt := opts.search(tt);
spl := SPLRuleTree(rt);
ss := opts.sumsRuleTree(rt);
c := opts.codeSums(ss);

# c := opts.genNttx(tt);
opts.prettyPrint(c);

# print to ntt.cpp for testing
PrintTo("../namespaces/packages/nttx/cuda/cuda-test/ntt.py", 
        PrintCode(name, c, opts)
);
