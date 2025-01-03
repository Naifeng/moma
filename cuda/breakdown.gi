NewRulesFor(NTT, rec(
    NTT_KL_CUDA := rec(
        forTransposition := false,
        minSize          := 2, 
        applicable       := (self, nt) >> nt.hasTags()
                                          and nt.params[1] >= self.minSize
                                          and nt.params[1] = 2^LogInt(nt.params[1], 2),
        radices          := [2], # should be extended to 4, 8, ...
        children  := (self, nt) >> let(
                                # Error(),
                                N := nt.params[1], # 512 # nt.params[2]: rec(n := 512, modulus := modulus, twiddles := twiddles)
                                ap := Filtered(self.radices, n -> IsInt(N/n)),
                                j := var.fresh_t("j", TInt),
                                tags := nt.getTags(),

                                List(ap, rdx -> [
                                    TICompose(j, LogInt(N, rdx), 
                                    # TICompose(j, (1), # for testing purpose
                                        TCompose([
                                            # Error(),
                                            TTensorI(NTT(2, nt.params[2]), N/rdx, APar, AVec),
                                            TDiag(iTwIntModKL(nt.params[1], nt.params[1]/bin_shl(1, j), nt.params[1]/bin_shl(1, j+1), nt.params[2]))
                                        ])
                                    
                                    ).withTags(tags)
                                ])
                               ),

        apply := (nt, C, cnt) -> C[1]
    )
));
