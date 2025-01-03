TableRootsOfUnity := [ 
    rec(
       modulus := 268435009,
       mu := 2147487224,
       roots := [1, 110070314, 49163687, 51684000, 5454002, 221964181, 190475310, 231112073]
   ),
   rec(
       modulus := 268435361,
       mu := 2147484408,
       roots := [1, 106416730, 210605896, 90281519, 18125476, 56427457, 86117821, 123453994]
   ),
   rec(
       modulus := 268435313,
       mu := 2147484792,
       roots := [1, 95610582, 75277247, 94670791, 29475028, 202971815, 175741954, 213751763]
   ),
   rec(
       modulus := 268435121,
       mu := 2147486328,
       roots := [1, 184774930, 15282554, 62348410, 51958, 222145496, 19852814, 23646552]
   )
];


TableRootsOfUnityInv := [ 
    rec(
       modulus := 268435009,
       mu := 2147487224,
       roots := [1, 158364695, 216751009, 219271322, 37322936, 77959699, 46470828, 262981007],
       cyclo := 234880633
   ),
   rec(
       modulus := 268435361,
       mu := 2147484408,
       roots := [1, 162018631, 178153842, 57829465, 144981367, 182317540, 212007904, 250309885],
       cyclo := 234880941
   ),
   rec(
       modulus := 268435313,
       mu := 2147484792,
       roots := [1, 172824731, 173764522, 193158066, 54683550, 92693359, 65463498, 238960285],
       cyclo := 234880899
   ),
   rec(
       modulus := 268435121,
       mu := 2147486328,
       roots := [1, 83660191, 206086711, 253152567, 244788569, 248582307, 46289625, 268383163],
       cyclo := 234880731
   )
];



iT_N_mn_n := (N, mn, n, l) -> Flat(Zip2(Replicate(n, 1), l{[n+1..2*n]}));


# N, n, g, p
# n -> N, i -> g^i mod p
Class(iTwIntMod, DiagFunc, rec(
    checkParams := (self, params) >> Checked(Length(params) = 4, params),
    lambda := self >> When(IsRec(self.params[4]), 
        let(mn := self.params[2],
            i := Ind(mn),
            Lambda(i, cond(eq(imod(i, 2), V(0)), V(1), nth(self.params[4].twiddles, self.params[3] + idiv(i, V(2)))))), # take params
        let(t := _T_IntMod(self.params[4]), 
            l := List(Filtered(TableRootsOfUnity, r->r.modulus = self.params[4])[1].roots, v->Value(t, v)),
            FData(iT_N_mn_n(self.params[1], self.params[2], self.params[3], l)).lambda())
    ),
    range := self >> _T_IntMod(self.params[1]),
    domain := self >> self.params[2]

    # for N = 16:
    # range = 16
    # domain = {2, 4, 8, 16}
));

# N, n, g, p
# n -> N, i -> g^i mod p
# work on the lambda line to make sure the indexing is correct
# change this: self.params[3] + idiv(i, V(2))
# 1. track t positions for n = 16
# 2. try to let the Pease to access the correct t's by finding which t at 2 -> 2, which t at 4 -> 4 

# Iter:
# for stage j, j in [1, n] 
# i: index var, i in [0, 2^(n-j+1)-1]
# if i even, 
# V(1)
# if i odd, 
# nth(twds, 2^(n-j) + i/2 )

# Still Iter:
# N = 16, n = 4
# j = 1, i in [0, 15], params[2] = 16, [3] = 8
# if i odd,
# nth(twds, 8 + {0, 1, 2, 3, 4, 5, 6, 7})

# j = 2, i in [0, 7], params[2] = 8, [3] = 4
# if i odd,
# nth(twds, 4 + {0, 1, 2, 3})

# j = 3, i in [0, 3], params[2] = 4, [3] = 2
# if i odd,
# nth(twds, 2 + {0, 1})

# j = 4, i in [0, 1], params[2] = 2, [3] = 1
# if i odd,
# nth(twds, 1)

# Q: i is the index in each butterfly?
# So the access sequence(i) is
# 8 9 10 11 12 13 14 15, 4 5 6 7, 2 3, 1
# that corresponds to t_
# 8 12 10 14 9 13 11 15, 4 6 5 7, 2 3, 1
# => access pattern is bit-reversed in iter
# For some reason, Pease has the same pattern as Iter, e.g., 4 6 5 7 
#   but in Pease we need to specifically perform bit-reversal, namely, _digitRev in the following lines,
#   to make sure Pease and Iter access the same twiddle factor at the same point

# PeaseBR:
# i always in [0, 15]
# Lambda(i, cond(eq(self.params[2], V(2)), cond(eq(imod(i, 2), V(0)), V(1), nth(self.params[4].twiddles, V(1) + idiv(i, V(16)) )), # {0} 
#                eq(self.params[2], V(4)), cond(eq(imod(i, 2), V(0)), V(1), nth(self.params[4].twiddles, V(2) + idiv(i, V(8)) )), # {0, 1}
#                eq(self.params[2], V(8)), cond(eq(imod(i, 2), V(0)), V(1), nth(self.params[4].twiddles, V(4) + idiv(i, V(4)) )), # {1, 3, 5, 7, 9, 11, 13, 15} -> {0, 1, 2, 3} -> {0, 2, 1, 3}
#                eq(self.params[2], V(16)), cond(eq(imod(i, 2), V(0)), V(1), nth(self.params[4].twiddles, V(8) + idiv(i, V(2)) )) # {1, 3, 5, 7, 9, 11, 13, 15} -> {0, 1, 2, 3, 4, 5, 6, 7} -> {0, 4, 2, 6, 1, 5, 3, 7}
#               )
#       )
# which is equivalent to
# Lambda(i, cond(eq(imod(i, 2), V(0)), V(1), nth(self.params[4].twiddles, self.params[3] + idiv(i, self.params[1]/self.params[3]) ) )) 
# but still need to bit-reverse the idiv()

Class(iTwIntModPeaseBR, DiagFunc, rec(
    checkParams := (self, params) >> Checked(Length(params) = 4, params),
    lambda := self >> 
        let(# the following two lines change the frequency of each twds
            mn := self.params[1], # only way to make the freq correct
            i := Ind(mn),
            Lambda(i, cond(eq(imod(i, 2), V(0)), V(1), nth(self.params[4].twiddles, self.params[3] + _digitRev(idiv(i, self.params[1]/self.params[3]), self.params[3], 2) ) )) # hardcoded: base = 2 in _digitRev
           ),
    range := self >> _T_IntMod(self.params[1]), 
    domain := self >> self.params[1] # changed here to make the dimension correct
));

# KL:

# params[1] = N = 8, n = 3

# j = 1, i in [0, 7], params[2] = 8, [3] = 4
# if i in {4, 5, 6, 7}
# nth(twds, 4 + mod(4)) # want {4, 5, 6, 7}                   # if N = 16, this would be {4, 5, 6, 7, 4, 5, 6, 7}

# j = 2, i in [0, 7], params[2] = 4, [3] = 2
# if i in {4, 5, 6, 7}
# nth(twds, 2 + mod(2)) # want {2, 3, 2, 3}                   # if N = 16, this would be {2, 3, 2, 3, 2, 3, 2, 3}

# j = 3, i in [0, 7], params[2] = 2, [3] = 1
# if i in {4, 5, 6, 7}
# nth(twds, 1 + mod(1)) # want {1, 1, 1, 1} 

# TIP: cond(eq()) really dictates the position of twds (on the graph). 
# For example, if twds are all at the last four indices, then use idiv(i, self.params[1]/2) to get rid of first four indices

Class(iTwIntModKL, DiagFunc, rec(
    checkParams := (self, params) >> Checked(Length(params) = 4, params),
    lambda := self >> 
        let(
            mn := self.params[1], # give the right frequency of twds
            i := Ind(mn),
            Lambda(i, cond(eq(idiv(i, self.params[1]/2), V(0)), V(1), nth(self.params[4].twiddles, self.params[3] + imod(i, self.params[3]) ) ))
           ),
    range := self >> _T_IntMod(self.params[1]), # Q: change this to params[2]?
    domain := self >> self.params[1] # need to be [1] to make the dimension align
));

# N, n, g, p
# n -> N, i -> g^i mod p
# Exactly the same as iTwIntMod
Class(iTwIntModInv, DiagFunc, rec(
    checkParams := (self, params) >> Checked(Length(params) = 4, params),
    lambda := self >> When(IsRec(self.params[4]), 
        let(mn := self.params[2],
            i := Ind(mn),
            Lambda(i, cond(eq(imod(i, 2), V(0)), V(1), nth(self.params[4].twiddles, self.params[3] + idiv(i, V(2)))))),
        let(
            t := _T_IntMod(self.params[4]), 
            l := List(Filtered(TableRootsOfUnityInv, r->r.modulus = self.params[4])[1].roots, v->Value(t, v)),
            FData(iT_N_mn_n(self.params[1], self.params[2], self.params[3], l)).lambda())
    ),
    range := self >> _T_IntMod(self.params[1]),
    domain := self >> self.params[2]
));



# N, n, g, p
# fConst()
Class(iNTTRescale, DiagFunc, rec(
    checkParams := (self, params) >> Checked(Length(params) = 2, params),
    lambda := self >> When(IsRec(self.params[2]),
        fConst(self.params[2].cyclo.t, self.params[1], self.params[2].cyclo).lambda(),
        let(
            t := _T_IntMod(self.params[2]), 
            v := Value(t, Filtered(TableRootsOfUnityInv, r->r.modulus = self.params[2])[1].cyclo),
            fConst(t, self.params[1], v).lambda())
    ),
    range := self >> _T_IntMod(self.params[2]),
    domain := self >> self.params[1]
));
