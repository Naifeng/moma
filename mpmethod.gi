# general native mod for QBaseInt
MakeGNativeMod := function(cm, c0, c1, c2, c3, opts) 
    local cc, c;
    
    c := var.fresh_t("c_", TReal); # TReal <-> QBaseInt

    cc := chain(
        assign(c, bin_or(bin_shl(tcast(TReal, c0), opts.basesize * 3),
                  bin_or(bin_shl(tcast(TReal, c1), opts.basesize * 2), 
                  bin_or(bin_shl(tcast(TReal, c2), opts.basesize), 
                  c3)))), 
        assign(cm, imod(c, opts.modulus))
    );

    return cc;
end;

# native mod for DBaseInt
MakeNativeMod := function(cm, c0, c1, blen, opts) 
    local cc, c;
    
    c := var.fresh_t("c_", T_UInt(blen*2)); 

    cc := chain(
        assign(c, bin_or(bin_shl(tcast(T_UInt(blen*2), c0), blen), c1)), 
        assign(cm, imod(c, opts.modulus))
    );

    return cc;
end;

MakeMPAdd := function(c0, c1, c2, c3, a0, a1, a2, a3, b0, b1, b2, b3, blen, opts)
    
    local cc;

    cc := chain(
        assign(c0, a0 + b0),
        assign(c1, a1 + b1),
        assign(c2, a2 + b2),
        assign(c3, a3 + b3),
        assign(c2, cond(lt(c3, a3), c2 + 1, c2)),
        assign(c1, cond(lt(tcast(T_UInt(blen), a2 + b2), a2), c1 + 1, c1)), 
        assign(c0, cond(lt(tcast(T_UInt(blen), a1 + b1), a1), c0 + 1, c0)) 
    );
    
    return cc;
end;

MakeMPSub := function(c0, c1, c2, c3, a0, a1, a2, a3, b0, b1, b2, b3, blen)
    
    local cc;

    cc := chain(
        assign(c0, a0 - b0),
        assign(c1, a1 - b1),
        assign(c2, a2 - b2),
        assign(c3, a3 - b3),
        assign(c0, cond(lt(a1, b1), c0 - 1, c0)),
        assign(c1, cond(lt(a2, b2), c1 - 1, c1)),
        assign(c2, cond(lt(a3, b3), c2 - 1, c2))
    );
    
    return cc;
end;

# Karatsuba Helper
MakeKaratsubaH := function(c0, c1, c2, c3, a0, a1, b0, b1, blen, opts)
    
    local cc, r0, c10, c11, r1, c20, c21, r2, ad0, ad1, r3, bd0, bd1, r4,
        c30, c31, c32, c33, pc10, pc11, pc12, pc13, pc20, pc21, pc22, pc23,
        rsub0, rsub1, rsub2, rsub3, shc10, shc11, shc12, shc13, shc30, shc31, shc32, shc33,
        radd0, radd1, radd2, radd3;

    r0 := var.fresh_t("r0_", T_UInt(blen*2));
    c10 := var.fresh_t("c10_", T_UInt(blen));
    c11 := var.fresh_t("c11_", T_UInt(blen));
    r1 := var.fresh_t("r1_", T_UInt(blen*2));
    c20 := var.fresh_t("c20_", T_UInt(blen));
    c21 := var.fresh_t("c21_", T_UInt(blen));
    r2 := var.fresh_t("r2_", T_UInt(blen*2));
    ad0 := var.fresh_t("ad0_", T_UInt(blen));
    ad1 := var.fresh_t("ad1_", T_UInt(blen));
    r3 := var.fresh_t("r3_", T_UInt(blen*2));
    bd0 := var.fresh_t("bd0_", T_UInt(blen));
    bd1 := var.fresh_t("bd1_", T_UInt(blen));
    r4 := var.fresh_t("r4_", T_UInt(blen*2));
    c30 := var.fresh_t("c30_", T_UInt(blen));
    c31 := var.fresh_t("c31_", T_UInt(blen));
    c32 := var.fresh_t("c32_", T_UInt(blen));
    c33 := var.fresh_t("c33_", T_UInt(blen));
    pc10 := var.fresh_t("pc10_", T_UInt(blen));
    pc11 := var.fresh_t("pc11_", T_UInt(blen));
    pc12 := var.fresh_t("pc12_", T_UInt(blen));
    pc13 := var.fresh_t("pc13_", T_UInt(blen));
    pc20 := var.fresh_t("pc20_", T_UInt(blen));
    pc21 := var.fresh_t("pc21_", T_UInt(blen));
    pc22 := var.fresh_t("pc22_", T_UInt(blen));
    pc23 := var.fresh_t("pc23_", T_UInt(blen));
    rsub0 := var.fresh_t("rsub0_", T_UInt(blen));
    rsub1 := var.fresh_t("rsub1_", T_UInt(blen));
    rsub2 := var.fresh_t("rsub2_", T_UInt(blen));
    rsub3 := var.fresh_t("rsub3_", T_UInt(blen));
    shc10 := var.fresh_t("shc10_", T_UInt(blen));
    shc11 := var.fresh_t("shc11_", T_UInt(blen));
    shc12 := var.fresh_t("shc12_", T_UInt(blen));
    shc13 := var.fresh_t("shc13_", T_UInt(blen));
    shc30 := var.fresh_t("shc30_", T_UInt(blen));
    shc31 := var.fresh_t("shc31_", T_UInt(blen));
    shc32 := var.fresh_t("shc32_", T_UInt(blen));
    shc33 := var.fresh_t("shc33_", T_UInt(blen));
    radd0 := var.fresh_t("radd0_", T_UInt(blen));
    radd1 := var.fresh_t("radd1_", T_UInt(blen));
    radd2 := var.fresh_t("radd2_", T_UInt(blen));
    radd3 := var.fresh_t("radd3_", T_UInt(blen));

    cc := chain(
        assign(r0, tcast(T_UInt(blen*2), a0) * tcast(T_UInt(blen*2), b0)),
        assign(c10, tcast(T_UInt(blen), bin_shr(r0, blen))),
        assign(c11, tcast(T_UInt(blen), r0)),
        assign(r1, tcast(T_UInt(blen*2), a1) * tcast(T_UInt(blen*2), b1)),
        assign(c20, tcast(T_UInt(blen), bin_shr(r1, blen))),
        assign(c21, tcast(T_UInt(blen), r1)),
        assign(r2, tcast(T_UInt(blen*2), a0) + tcast(T_UInt(blen*2), a1)),
        assign(ad0, tcast(T_UInt(blen), bin_shr(r2, blen))),
        assign(ad1, tcast(T_UInt(blen), r2)),
        assign(r3, tcast(T_UInt(blen*2), b0) + tcast(T_UInt(blen*2), b1)),
        assign(bd0, tcast(T_UInt(blen), bin_shr(r3, blen))),
        assign(bd1, tcast(T_UInt(blen), r3)),
        assign(r4, r2 * r3),
        assign(c30, 0),
        assign(c31, 0),
        assign(c32, tcast(T_UInt(blen), bin_shr(r4, blen))),
        assign(c33, tcast(T_UInt(blen), r4)),
        assign(pc10, 0),
        assign(pc11, 0),
        assign(pc12, c10),
        assign(pc13, c11),
        assign(pc20, 0),
        assign(pc21, 0),
        assign(pc22, c20),
        assign(pc23, c21),
        MakeMPSub(rsub0, rsub1, rsub2, rsub3, c30, c31, c32, c33, pc20, pc21, pc22, pc23, blen),
        MakeMPSub(c30, c31, c32, c33, rsub0, rsub1, rsub2, rsub3, pc10, pc11, pc12, pc13, blen),
        assign(shc10, c10),
        assign(shc11, c11),
        assign(shc12, 0),
        assign(shc13, 0),
        assign(shc30, c31),
        assign(shc31, c32),
        assign(shc32, c33),
        assign(shc33, 0),
        MakeMPAdd(radd0, radd1, radd2, radd3, shc10, shc11, shc12, shc13, pc20, pc21, pc22, pc23, blen, opts),
        MakeMPAdd(c0, c1, c2, c3, radd0, radd1, radd2, radd3, shc30, shc31, shc32, shc33, blen, opts)
    );

    return cc;
end;


MakeKaratsuba := function(c0, c1, c2, c3, a0, a1, b0, b1, blen, opts)
    
    local cc, r0, c10, c11, r1, c20, c21, r2, ad0, ad1, r3, bd0, bd1, 
        e_c30, e_c31, e_c32, e_c33, pc10, pc11, pc12, pc13, pc20, pc21, pc22, pc23,
        rsub0, rsub1, rsub2, rsub3, shc10, shc11, shc12, shc13, shc30, shc31, shc32, shc33,
        radd0, radd1, radd2, radd3;

    r0 := var.fresh_t("r0_", T_UInt(blen*2));
    c10 := var.fresh_t("c10_", T_UInt(blen));
    c11 := var.fresh_t("c11_", T_UInt(blen));
    r1 := var.fresh_t("r1_", T_UInt(blen*2));
    c20 := var.fresh_t("c20_", T_UInt(blen));
    c21 := var.fresh_t("c21_", T_UInt(blen));
    r2 := var.fresh_t("r2_", T_UInt(blen*2));
    ad0 := var.fresh_t("ad0_", T_UInt(blen));
    ad1 := var.fresh_t("ad1_", T_UInt(blen));
    r3 := var.fresh_t("r3_", T_UInt(blen*2));
    bd0 := var.fresh_t("bd0_", T_UInt(blen));
    bd1 := var.fresh_t("bd1_", T_UInt(blen));
    e_c30 := var.fresh_t("e_c30_", T_UInt(blen));
    e_c31 := var.fresh_t("e_c31_", T_UInt(blen));
    e_c32 := var.fresh_t("e_c32_", T_UInt(blen));
    e_c33 := var.fresh_t("e_c33_", T_UInt(blen));
    pc10 := var.fresh_t("pc10_", T_UInt(blen));
    pc11 := var.fresh_t("pc11_", T_UInt(blen));
    pc12 := var.fresh_t("pc12_", T_UInt(blen));
    pc13 := var.fresh_t("pc13_", T_UInt(blen));
    pc20 := var.fresh_t("pc20_", T_UInt(blen));
    pc21 := var.fresh_t("pc21_", T_UInt(blen));
    pc22 := var.fresh_t("pc22_", T_UInt(blen));
    pc23 := var.fresh_t("pc23_", T_UInt(blen));
    rsub0 := var.fresh_t("rsub0_", T_UInt(blen));
    rsub1 := var.fresh_t("rsub1_", T_UInt(blen));
    rsub2 := var.fresh_t("rsub2_", T_UInt(blen));
    rsub3 := var.fresh_t("rsub3_", T_UInt(blen));
    shc10 := var.fresh_t("shc10_", T_UInt(blen));
    shc11 := var.fresh_t("shc11_", T_UInt(blen));
    shc12 := var.fresh_t("shc12_", T_UInt(blen));
    shc13 := var.fresh_t("shc13_", T_UInt(blen));
    shc30 := var.fresh_t("shc30_", T_UInt(blen));
    shc31 := var.fresh_t("shc31_", T_UInt(blen));
    shc32 := var.fresh_t("shc32_", T_UInt(blen));
    shc33 := var.fresh_t("shc33_", T_UInt(blen));
    radd0 := var.fresh_t("radd0_", T_UInt(blen));
    radd1 := var.fresh_t("radd1_", T_UInt(blen));
    radd2 := var.fresh_t("radd2_", T_UInt(blen));
    radd3 := var.fresh_t("radd3_", T_UInt(blen));

    cc := chain(
        # 32b = 16b * 16b
        assign(r0, tcast(T_UInt(blen*2), a0) * tcast(T_UInt(blen*2), b0)), # r0 = a0 * b0
        assign(c10, tcast(T_UInt(blen), bin_shr(r0, blen))),
        assign(c11, tcast(T_UInt(blen), r0)),
        assign(r1, tcast(T_UInt(blen*2), a1) * tcast(T_UInt(blen*2), b1)), # r1 = a1 * b1
        assign(c20, tcast(T_UInt(blen), bin_shr(r1, blen))),
        assign(c21, tcast(T_UInt(blen), r1)),
        assign(r2, tcast(T_UInt(blen*2), a0) + tcast(T_UInt(blen*2), a1)), # r2 = a0 + a1
        assign(ad0, tcast(T_UInt(blen), bin_shr(r2, blen))),
        assign(ad1, tcast(T_UInt(blen), r2)),
        assign(r3, tcast(T_UInt(blen*2), b0) + tcast(T_UInt(blen*2), b1)), # r3 = b0 + b1
        assign(bd0, tcast(T_UInt(blen), bin_shr(r3, blen))),
        assign(bd1, tcast(T_UInt(blen), r3)),
        MakeKaratsubaH(e_c30, e_c31, e_c32, e_c33, ad0, ad1, bd0, bd1, blen, opts), # 4b = 2b * 2b
        assign(pc10, 0),
        assign(pc11, 0),
        assign(pc12, c10),
        assign(pc13, c11),
        assign(pc20, 0),
        assign(pc21, 0),
        assign(pc22, c20),
        assign(pc23, c21),
        MakeMPSub(rsub0, rsub1, rsub2, rsub3, e_c30, e_c31, e_c32, e_c33, pc20, pc21, pc22, pc23, blen),
        MakeMPSub(e_c30, e_c31, e_c32, e_c33, rsub0, rsub1, rsub2, rsub3, pc10, pc11, pc12, pc13, blen),
        assign(shc10, c10),
        assign(shc11, c11),
        assign(shc12, 0),
        assign(shc13, 0),
        assign(shc30, e_c31),
        assign(shc31, e_c32),
        assign(shc32, e_c33),
        assign(shc33, 0),
        MakeMPAdd(radd0, radd1, radd2, radd3, shc10, shc11, shc12, shc13, pc20, pc21, pc22, pc23, blen, opts),
        MakeMPAdd(c0, c1, c2, c3, radd0, radd1, radd2, radd3, shc30, shc31, shc32, shc33, blen, opts)
    );

    return cc;
end;

MakeMPMod := function(cm, c0, c1, c2, c3, mod0, mod1, mu0, mu1, blen, opts)

    local cc, t0, t1, t2, t3, high, low, p1, mask, p2, p3, e_low, p,
        tmp0, tmp1, tmp2, tmp3, s0, s1, s2, s3, ts0, ts1, ts2, ts3,
        q1, q2;

    t0 := var.fresh_t("t0_", T_UInt(blen));
    t1 := var.fresh_t("t1_", T_UInt(blen));
    t2 := var.fresh_t("t2_", T_UInt(blen));
    t3 := var.fresh_t("t3_", T_UInt(blen));
    high := var.fresh_t("high_", T_UInt(blen*2));
    low := var.fresh_t("low_", T_UInt(blen*2));
    p1 := var.fresh_t("p1_", T_UInt(blen));
    mask := var.fresh_t("mask_", T_UInt(blen*2));
    p2 := var.fresh_t("p2_", T_UInt(blen*2));
    p3 := var.fresh_t("p3_", T_UInt(blen));
    e_low := var.fresh_t("e_low_", T_UInt(blen*2));
    p := var.fresh_t("p_", T_UInt(blen*2));
    tmp0 := var.fresh_t("tmp0_", T_UInt(blen));
    tmp1 := var.fresh_t("tmp1_", T_UInt(blen));
    tmp2 := var.fresh_t("tmp2_", T_UInt(blen));
    tmp3 := var.fresh_t("tmp3_", T_UInt(blen));
    s0 := var.fresh_t("s0_", T_UInt(blen));
    s1 := var.fresh_t("s1_", T_UInt(blen));
    s2 := var.fresh_t("s2_", T_UInt(blen));
    s3 := var.fresh_t("s3_", T_UInt(blen));
    ts0 := var.fresh_t("ts0_", T_UInt(blen));
    ts1 := var.fresh_t("ts1_", T_UInt(blen));
    ts2 := var.fresh_t("ts2_", T_UInt(blen));
    ts3 := var.fresh_t("ts3_", T_UInt(blen));
    q1 := var.fresh_t("q1_", T_UInt(blen*2));
    q2 := var.fresh_t("q2_", T_UInt(blen*2));

    cc := chain(
        assign(t0, c0),
        assign(t1, c1),
        assign(t2, c2),
        assign(t3, c3),
        assign(high, bin_or(bin_shl(tcast(T_UInt(blen*2), c0), blen), c1)),
        assign(low, bin_or(bin_shl(tcast(T_UInt(blen*2), c2), blen), c3)),
        assign(p1, bin_shr(low, opts.mbits - 2)),
        assign(mask, bin_shl(tcast(T_UInt(blen*2), 1), (opts.mbits - 2)) - 1),
        assign(p2, bin_and(high, mask)),
        assign(p3, bin_shr(high, (opts.mbits - 2))),
        assign(e_low, bin_or(bin_shl(tcast(T_UInt(blen*2), p2), blen * 2 - (opts.mbits - 2)), p1)),
        assign(c0, 0),
        assign(c1, tcast(T_UInt(blen), p3)),
        assign(c2, tcast(T_UInt(blen), (bin_shr(e_low, blen)))),
        assign(c3, tcast(T_UInt(blen), e_low)),
        MakeKaratsuba(c0, c1, c2, c3, c2, c3, mu0, mu1, blen, opts),
        assign(high, bin_or(bin_shl(tcast(T_UInt(blen*2), c0), blen), c1)),
        assign(p, bin_shr(high, (opts.mbits + 5 - (blen * 2)))),
        # assign(c0, 0),
        # assign(c1, 0),
        assign(c2, tcast(T_UInt(blen), (bin_shr(p, blen)))),
        assign(c3, tcast(T_UInt(blen), p)),
        MakeKaratsuba(tmp0, tmp1, tmp2, tmp3, c2, c3, mod0, mod1, blen, opts),
        MakeMPSub(s0, s1, s2, s3, t0, t1, t2, t3, tmp0, tmp1, tmp2, tmp3, blen),
        MakeMPSub(ts0, ts1, ts2, ts3, s0, s1, s2, s3, 0, 0, mod0, mod1, blen),
        assign(q1, bin_or(bin_shl(tcast(T_UInt(blen*2), ts2), blen), ts3)),
        assign(q2, bin_or(bin_shl(tcast(T_UInt(blen*2), s2), blen), s3)),
        assign(cm, cond(logic_or(logic_or(neq(s1, 0), gt(s2, mod0)), logic_and(eq(s2, mod0), gt(s3, mod1))),
            q1, q2))
    );

    return cc;

end;

MakeModMulMP := function(c, a, b, blen, opts)

    local cc, a0, a1, b0, b1, mod0, mod1, mu0, mu1, c0, c1, c2, c3, f, rc1, rc2;

    a0 := var.fresh_t("a0_", T_UInt(blen));
    a1 := var.fresh_t("a1_", T_UInt(blen));
    b0 := var.fresh_t("b0_", T_UInt(blen));
    b1 := var.fresh_t("b1_", T_UInt(blen));
    mod0 := var.fresh_t("mod0_", T_UInt(blen));
    mod1 := var.fresh_t("mod1_", T_UInt(blen));
    mu0 := var.fresh_t("mu0_", T_UInt(blen));
    mu1 := var.fresh_t("mu1_", T_UInt(blen));
    c0 := var.fresh_t("c0_", T_UInt(blen));
    c1 := var.fresh_t("c1_", T_UInt(blen));
    c2 := var.fresh_t("c2_", T_UInt(blen));
    c3 := var.fresh_t("c3_", T_UInt(blen));
    f := var.fresh_t("f_", T_UInt(blen));
    rc1 := var.fresh_t("rc1_", T_UInt(blen*2));
    rc2 := var.fresh_t("rc2_", T_UInt(blen*2));

    cc := chain(
        assign(a0, tcast(T_UInt(blen), bin_shr(a, blen))),
        assign(a1, tcast(T_UInt(blen), a)),
        assign(b0, tcast(T_UInt(blen), bin_shr(b, blen))),
        assign(b1, tcast(T_UInt(blen), b)),
        assign(mod0, tcast(T_UInt(blen), bin_shr(opts.modulus, blen))),
        assign(mod1, tcast(T_UInt(blen), opts.modulus)),
        assign(mu0, tcast(T_UInt(blen), bin_shr(opts.barrettMu, blen))),
        assign(mu1, tcast(T_UInt(blen), opts.barrettMu)),
        MakeKaratsuba(c0, c1, c2, c3, a0, a1, b0, b1, blen, opts),
        # Option 1
        # MakeGNativeMod(c, c0, c1, c2, c3, opts)
        # Option 2
        # assign(f, logic_and(eq(c0, 0), eq(c1, 0))),
        # MakeNativeMod(rc1, c2, c3, opts),
        # MakeMPMod(rc2, c0, c1, c2, c3, mod0, mod1, mu0, mu1, blen, opts),
        # assign(c, cond(f, rc1, rc2))
        # Option 3
        MakeMPMod(c, c0, c1, c2, c3, mod0, mod1, mu0, mu1, blen, opts)
    );

    return cc;
end;



# DBaseInt sum;
# int carry;

# sum = (DBaseInt) a[1] + (DBaseInt) b[1]; # 32b = 16b + 16b
# c[3] = (BaseInt) sum;
# carry = (sum >> BaseSize);


# sum = (DBaseInt) a[0] + (DBaseInt) b[0];
# sum = sum + carry; # 32b = 32b + 1
# c[2] = (BaseInt) sum;
# carry = (sum >> BaseSize);

# c[1] = carry;
# c[0] = 0;


# c_{blen*2} = a_{blen*2} + b_{blen*2}
# Should be
# [c0, c1] = [a0, a1] + [b0, b1]
# consumes two blen*2 and produces two blen
# should be: MakeAddMP := function(c0, c1, a, b, blen, opts)
MakeAddMP := function(c, a, b, blen, opts)

    local cc, a0, a1, b0, b1, c0, c1, s1, cr1;

    a0 := var.fresh_t("a0_", T_UInt(blen));
    a1 := var.fresh_t("a1_", T_UInt(blen));
    b0 := var.fresh_t("b0_", T_UInt(blen));
    b1 := var.fresh_t("b1_", T_UInt(blen));
    c0 := var.fresh_t("c0_", T_UInt(blen));
    c1 := var.fresh_t("c1_", T_UInt(blen));
    s1 := var.fresh_t("s1_", T_UInt(blen*2)); # sum
    cr1 := var.fresh_t("cr1_", T_UInt(blen)); # carry

    cc := chain(
        assign(a0, tcast(T_UInt(blen), bin_shr(a, blen))),
        assign(a1, tcast(T_UInt(blen), a)),
        assign(b0, tcast(T_UInt(blen), bin_shr(b, blen))),
        assign(b1, tcast(T_UInt(blen), b)),
        assign(s1, tcast(T_UInt(blen*2), a1) + b1),
        assign(c1, tcast(T_UInt(blen), s1)),
        assign(cr1, bin_shr(s1, blen)),
        assign(s1, tcast(T_UInt(blen*2), a0) + b0 + cr1),
        assign(c0, tcast(T_UInt(blen), s1)),
        assign(c, bin_or(bin_shl(tcast(T_UInt(blen*2), c0), blen), c1))
    );

    return cc;
end;

# _ModAddMP(a, b, mod, mu) in mp_int.h
# TODO: change this according to ap_int.h
MakeModAddMP := function(c, a, b, blen, opts)

    local cc, a0, a1, b0, b1, mod0, mod1, mu0, mu1, c0, c1, c2, c3, f, rc1, rc2;

    a0 := var.fresh_t("a0_", T_UInt(blen));
    a1 := var.fresh_t("a1_", T_UInt(blen));
    b0 := var.fresh_t("b0_", T_UInt(blen));
    b1 := var.fresh_t("b1_", T_UInt(blen));
    mod0 := var.fresh_t("mod0_", T_UInt(blen));
    mod1 := var.fresh_t("mod1_", T_UInt(blen));
    mu0 := var.fresh_t("mu0_", T_UInt(blen));
    mu1 := var.fresh_t("mu1_", T_UInt(blen));
    c0 := var.fresh_t("c0_", T_UInt(blen));
    c1 := var.fresh_t("c1_", T_UInt(blen));
    c2 := var.fresh_t("c2_", T_UInt(blen));
    c3 := var.fresh_t("c3_", T_UInt(blen));
    f := var.fresh_t("f_", T_UInt(blen));
    rc1 := var.fresh_t("rc1_", T_UInt(blen*2));
    rc2 := var.fresh_t("rc2_", T_UInt(blen*2));

    cc := chain(
        assign(a0, tcast(T_UInt(blen), bin_shr(a, blen))),
        assign(a1, tcast(T_UInt(blen), a)),
        assign(b0, tcast(T_UInt(blen), bin_shr(b, blen))),
        assign(b1, tcast(T_UInt(blen), b)),
        assign(mod0, tcast(T_UInt(blen), bin_shr(opts.modulus, blen))),
        assign(mod1, tcast(T_UInt(blen), opts.modulus)),
        assign(mu0, tcast(T_UInt(blen), bin_shr(opts.barrettMu, blen))),
        assign(mu1, tcast(T_UInt(blen), opts.barrettMu)),
        
        assign(c0, 0),
        assign(c1, 0),
        assign(c2, a0 + b0),
        assign(c3, a1 + b1),
        assign(c2, cond(lt(c3, a1), c2 + 1, c2)), 
        assign(c1, cond(lt(tcast(T_UInt(blen), a0 + b0), a0), c1 + 1, c1)), 
        
        
        # Option 1
        # MakeGNativeMod(c, c0, c1, c2, c3, opts)
        MakeNativeMod(c, c2, c3, blen, opts)
        # Option 2
        # assign(f, logic_and(eq(c0, 0), eq(c1, 0))),
        # MakeNativeMod(rc1, c2, c3, opts),
        # MakeMPMod(rc2, c0, c1, c2, c3, mod0, mod1, mu0, mu1, blen, opts),
        # assign(c, cond(f, rc1, rc2))
        # Option 3
        # MakeMPMod(c, c0, c1, c2, c3, mod0, mod1, mu0, mu1, blen, opts)
    );

    return cc;
end;


MakeModSubMP := function(c, a, b, blen, opts)

    local cc, a0, a1, b0, b1, mod0, mod1, mu0, mu1, c0, c1, c2, c3, tmp2, tmp3, f, rc1, rc2;

    a0 := var.fresh_t("a0_", T_UInt(blen));
    a1 := var.fresh_t("a1_", T_UInt(blen));
    b0 := var.fresh_t("b0_", T_UInt(blen));
    b1 := var.fresh_t("b1_", T_UInt(blen));
    mod0 := var.fresh_t("mod0_", T_UInt(blen));
    mod1 := var.fresh_t("mod1_", T_UInt(blen));
    mu0 := var.fresh_t("mu0_", T_UInt(blen));
    mu1 := var.fresh_t("mu1_", T_UInt(blen));
    c0 := var.fresh_t("c0_", T_UInt(blen));
    c1 := var.fresh_t("c1_", T_UInt(blen));
    c2 := var.fresh_t("c2_", T_UInt(blen));
    c3 := var.fresh_t("c3_", T_UInt(blen));
    tmp2 := var.fresh_t("tmp2_", T_UInt(blen));
    tmp3 := var.fresh_t("tmp3_", T_UInt(blen));
    f := var.fresh_t("f_", T_UInt(blen));
    rc1 := var.fresh_t("rc1_", T_UInt(blen*2));
    rc2 := var.fresh_t("rc2_", T_UInt(blen*2));

    cc := chain(
        assign(a0, tcast(T_UInt(blen), bin_shr(a, blen))),
        assign(a1, tcast(T_UInt(blen), a)),
        assign(b0, tcast(T_UInt(blen), bin_shr(b, blen))),
        assign(b1, tcast(T_UInt(blen), b)),
        assign(mod0, tcast(T_UInt(blen), bin_shr(opts.modulus, blen))),
        assign(mod1, tcast(T_UInt(blen), opts.modulus)),
        assign(mu0, tcast(T_UInt(blen), bin_shr(opts.barrettMu, blen))),
        assign(mu1, tcast(T_UInt(blen), opts.barrettMu)),
        assign(c0, 0),
        assign(c1, 0),
        assign(c2, cond(lt(a, b), a0 + mod0, a0)),
        assign(c3, cond(lt(a, b), a1 + mod1, a1)),
        assign(c2, cond(logic_and(lt(a, b), lt(c3, a1)), c2 + 1, c2)), 
        assign(c1, cond(logic_and(lt(a, b), lt(tcast(T_UInt(blen), a0 + mod0), a0)), c1 + 1, c1)), 
        assign(tmp2, c2),
        assign(tmp3, c3),
        assign(c2, tcast(T_UInt(blen), c2 - b0)), # in case this is negative and compiler do some inline optimizations
        assign(c3, tcast(T_UInt(blen), c3 - b1)),
        assign(c1, cond(lt(tmp2, b0), c1 - 1, c1)),
        assign(c2, cond(lt(tmp3, b1), c2 - 1, c2)),
        # Option 1
        # MakeGNativeMod(c, c0, c1, c2, c3, opts)
        MakeNativeMod(c, c2, c3, blen, opts)
        # Option 2
        # assign(f, logic_and(eq(c0, 0), eq(c1, 0))),
        # MakeNativeMod(rc1, c2, c3, opts),
        # MakeMPMod(rc2, c0, c1, c2, c3, mod0, mod1, mu0, mu1, blen, opts),
        # assign(c, cond(f, rc1, rc2))
        # Option 3
        # MakeMPMod(c, c0, c1, c2, c3, mod0, mod1, mu0, mu1, blen, opts)
    );

    return cc;
end;






# n = 2
# for (int i = 0; i < n; i++) {
#     if (a[i] > b[i]) return 1;
#     else if (a[i] < b[i]) return 0;
# }


# assign(c, cond(gt(a0, b0), 1, a0)),

# set c to V(true) if a < b
# set c to V(false) if a >= b
# a0, a1; b0, b1
# a0 < b0 -> c := true
# c := true iff (a0 < b0) or (a0 = b0 and a1 < b1)
MakeLessThanMP := function(c, a, b, blen, opts)

    local cc, a0, a1, b0, b1;

    a0 := var.fresh_t("a0_", T_UInt(blen));
    a1 := var.fresh_t("a1_", T_UInt(blen));
    b0 := var.fresh_t("b0_", T_UInt(blen));
    b1 := var.fresh_t("b1_", T_UInt(blen));

    cc := chain(
        assign(a0, tcast(T_UInt(blen), bin_shr(a, blen))),
        assign(a1, tcast(T_UInt(blen), a)),
        assign(b0, tcast(T_UInt(blen), bin_shr(b, blen))),
        assign(b1, tcast(T_UInt(blen), b)),
        assign(c, cond(logic_or(lt(a0, b0), logic_and(eq(a0, b0), lt(a1, b1))), V(true), V(false)))
    );


end;