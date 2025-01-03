NewRulesFor(SkewNTT, rec(
    SkewNTT_CT := rec(
        maxSize       := false,
        
        maxKernelSize := 8,
        filter := (self, lst) >> Filtered(lst, a-> When(a[1] * a[2] > self.maxKernelSize, a[1] = self.maxKernelSize, true)),
        
        forcePrimeFactor := false,

        applicable := (self, nt) >> nt.params[1] > 2 and not IsPrime(nt.params[1]),
        
        children  := (self, nt) >> Map2(self.filter(DivisorPairs(nt.params[1])),
            (m,n) -> let(ii := Ind(n), [ SkewNTT(m, fTensor(nt.params[2], fBase(ii)), nt.params[3]), SkewNTT(n, nt.params[2], nt.params[3]), InfoNt(ii) ])
        ),

        apply := (nt, C, cnt) -> let(mn := nt.params[1], m := Rows(C[1]), n := Rows(C[2]), ii := cnt[3].params[1],
            IDirSum(ii, C[1]) *
            Tensor(C[2], I(m)) 
        )
    ),
    
    SkewNTT_Base := rec(
        forTransposition := false,
        applicable       := (self, nt) >> nt.params[1] = 2,
        apply            := (nt, c, cnt) -> let(
            mn := Product(List(nt.free(), i->i.range)),
            df := iTwIntMod(nt.params[3].n, 2 * mn, mn, nt.params[3]),
            f := RulesFuncSimp(fTensor(nt.params[2], fId(2))), 
            F(2) * Diag(fCompose(df, f)))
    )
));


NewRulesFor(NTT, rec(
    NTT_SkewNTT := rec(
        forTransposition := false,
        applicable       := (self, nt) >> true,
        children  := nt -> [[ SkewNTT(nt.params[1], fId(1), nt.params[2]) ]],
        apply            := (nt, C, cnt) -> C[1] 
    ),

    NTT_Base := rec(
        forTransposition := false,
        applicable       := (self, nt) >> nt.params[1] = 2,
        apply            := (nt, c, cnt) -> F(2),
    ),

    NTT_iter := rec(
        maxSize       := false,
        forcePrimeFactor := false,

        applicable := (self, nt) >> nt.params[1] > 2 and nt.params[1] = 2^LogInt(nt.params[1], 2),
        
        children  := nt -> [[ NTT(2, nt.params[2]) ]],
        
        apply := (nt, C, cnt) -> 
            Compose(List([1..LogInt(nt.params[1], 2)], 
                i -> Tensor(
                    Tensor(I(nt.params[1]/2^(i)), C[1]) * Diag(iTwIntMod(nt.params[1], nt.params[1]/2^(i-1), nt.params[1]/2^i, nt.params[2])), 
                    I(2^(i-1)))))
    ),

    # NTT_Pease_BR := rec(
    #     maxSize       := false,
    #     forcePrimeFactor := false,

    #     applicable := (self, nt) >> nt.params[1] > 2 and nt.params[1] = 2^LogInt(nt.params[1], 2),
        
    #     children  := nt -> [[ NTT(2, nt.params[2]) ]],
        
    #     # add BR to force the inputs and outputs align with NTT_iter
    #     apply := (nt, C, cnt) -> 
    #         BR(nt.params[1]) * # BR is required to pass nttx-test
    #         Compose(List([1..LogInt(nt.params[1], 2)], # [1, n], stage i
    #             i -> Tensor(C[1], I(nt.params[1]/2)) * L(nt.params[1], 2) * # nt.params[1] = N, N = 2^n
    #                  # ^ same as: 
    #                  # L(nt.params[1], 2) * Tensor(I(nt.params[1]/2), C[1]) *  
    #                  # L(nt.params[1], nt.params[1]/2) * Tensor(C[1], I(nt.params[1]/2)) *  
    #                  Diag(iTwIntModPeaseBR(nt.params[1], nt.params[1]/2^(i-1), nt.params[1]/2^i, nt.params[2]))
    #         )) 
    #         * BR(nt.params[1])

    #         # For N = 16, BR_16 * NTT_2 x I_8 * L^16_2 * Diag * BR_16
    #         # NTT_2 x I_8 * L^16_2 * Diag = L^16_2 * I_8 x NTT_2 * Diag'
    # ),

    NTT_KL := rec(
        maxSize       := false,
        forcePrimeFactor := false,

        applicable := (self, nt) >> nt.params[1] > 2 and nt.params[1] = 2^LogInt(nt.params[1], 2),
        
        children  := nt -> [[ NTT(2, nt.params[2]) ]],
        
        apply := (nt, C, cnt) -> 
            Compose(List([1..LogInt(nt.params[1], 2)], # [1, n], stage i
                i -> L(nt.params[1], nt.params[1]/2) * 
                     Tensor(C[1], I(nt.params[1]/2)) *  
                     Diag(iTwIntModKL(nt.params[1], nt.params[1]/2^(i-1), nt.params[1]/2^i, nt.params[2]))
            )) 

        # For N = 16, L^16_8 * NTT_2 x I_8 * Diag
        # Diag(iTwIntModKL(2^n, 2^(n-j+1), 2^(n-j), nt.params[2]))

    )

));

NewRulesFor(iSkewNTT, rec(
    iSkewNTT_CT := rec(
        maxSize       := false,
        forcePrimeFactor := false,
        maxKernelSize := 8,
        filter := (self, lst) >> Filtered(lst, a-> When(a[1] * a[2] > self.maxKernelSize, a[1] = self.maxKernelSize, true)),

        applicable := (self, nt) >> nt.params[1] > 2 and not IsPrime(nt.params[1]),
        
        children  := (self, nt) >> Map2(self.filter(DivisorPairs(nt.params[1])),
            (m,n) -> let(ii := Ind(n), [ iSkewNTT(n, nt.params[2], nt.params[3]), iSkewNTT(m, fTensor(nt.params[2], fBase(ii)), nt.params[3]), InfoNt(ii) ])
        ),

        apply := (nt, C, cnt) -> let(mn := nt.params[1], m := Rows(C[2]), n := Rows(C[1]), ii := cnt[3].params[1],
            Tensor(C[1], I(m)) *
            IDirSum(ii, C[2])
        )
    ),
    
    iSkewNTT_Base := rec(
        forTransposition := false,
        applicable       := (self, nt) >> nt.params[1] = 2,
        apply            := (nt, c, cnt) -> let(
            mn := Product(List(nt.free(), i->i.range)),
            df := iTwIntModInv(nt.params[3].n, 2 * mn, mn, nt.params[3]),
            f := RulesFuncSimp(fTensor(nt.params[2], fId(2))), 
            Diag(fCompose(df, f))) * F(2)
    )
));

NewRulesFor(iNTT, rec(
    iNTT_iSkewNTT := rec(
        forTransposition := false,
        applicable       := (self, nt) >> true,
        children  := nt -> [[ iSkewNTT(nt.params[1], fId(1), nt.params[2]) ]],
        apply            := (nt, C, cnt) -> Diag(iNTTRescale(nt.params[1], nt.params[2])) * C[1] 
    ),

    iNTT_Base := rec(
        forTransposition := false,
        applicable       := (self, nt) >> nt.params[1] = 2,
        apply            := (nt, c, cnt) -> F(2),
    ),

    iNTT_iter := rec(
        maxSize       := false,
        forcePrimeFactor := false,

        applicable := (self, nt) >> nt.params[1] > 2 and nt.params[1] = 2^LogInt(nt.params[1], 2),
        
        children  := nt -> [[ NTT(2, nt.params[2]) ]],
        
        apply := (nt, C, cnt) -> 
            Compose([Diag(iNTTRescale(nt.params[1], nt.params[2]))]::
                List(Reversed([1..LogInt(nt.params[1], 2)]), i -> 
                    Tensor(
                        Diag(iTwIntModInv(nt.params[1], nt.params[1]/2^(i-1), nt.params[1]/2^i, nt.params[2])) * 
                        Tensor(
                            I(nt.params[1]/2^(i)), 
                            C[1]
                        ),  
                        I(2^(i-1))
                    )
                ))
    ),

    # based on NTT_KL
    iNTT_Pease := rec(
        maxSize       := false,
        forcePrimeFactor := false,

        applicable := (self, nt) >> nt.params[1] > 2 and nt.params[1] = 2^LogInt(nt.params[1], 2),
        
        children  := nt -> [[ NTT(2, nt.params[2]) ]],
        
        apply := (nt, C, cnt) ->  

            Compose([Diag(iNTTRescale(nt.params[1], nt.params[2]))]::
                List(Reversed([1..LogInt(nt.params[1], 2)]), i -> 
                    Diag(iTwIntModKL(nt.params[1], nt.params[1]/2^(i-1), nt.params[1]/2^i, nt.params[2])) * 
                    Tensor(C[1], I(nt.params[1]/2)) * 
                    L(nt.params[1], 2)
                ))

        # For N = 16, D * NTT_2 x I_8 * L^16_2
    )
));

NewRulesFor(ModSwitch, rec(
    ModSwitch_Base := rec(
        forTransposition := false,
        # applicable       := nt -> nt.params[1] = 2, # Q: what should be the true base case?
        applicable := (self, nt) >> nt.params[1] = 2^LogInt(nt.params[1], 2),
        
        children := nt -> let(

            N := nt.params[1],
            alpha := nt.params[2].alpha,
            beta := nt.params[2].beta,
            p := nt.params[2].p,
            q := nt.params[2].q,

            i := Ind(alpha),
            j := Ind(beta),
            k := Ind(N),

            # Q: using conf.type() gives an error: Can't add non-integer to a pointer in
            # Workaround: f := Lambda(k, Lambda(t, cond(gt(k, nth(p, i)/2), t, t + (deref(p + i) - deref(q + i))))), 
            t := var("pencil", TPtr(TInt)), # TArray(TInt, N))

            f := Lambda(k, Lambda(t, cond(gt(k, nth(p, i)/2), t, t + (nth(p, i) - nth(q, j))))),
            [[Pointwise(f)]] # ISum * PW(1) * Scat: loop of pw of size 1 with gather and scat
        ),
        
        apply := (nt, c, cnt) -> let(

            N := nt.params[1],
            alpha := nt.params[2].alpha,
            beta := nt.params[2].beta,

            i := Ind(alpha),
            j := Ind(beta),

            switch_modulus := c[1],

            # j -> N * len(i) + j 
            g := Gath(fTensor(fBase(i), fId(N))),
            s := ScatAcc(fTensor(fBase(j), fId(N))), 

            ISum(i, alpha, ISum(j, beta, s * switch_modulus * g))

        )
    )
));






