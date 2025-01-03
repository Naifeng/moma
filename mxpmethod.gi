# Example:
# 4b: 64b
# 2b: 32b
# b: 16b

# Code Opt. Rule
ForceCopyPropagate := function(c, opts)

    local vars, cmds, cmd;
    
    # Rule: X, Y, twds cannot be standalone, i.e., assign(a217, nth(twiddles, V(2))), need to be copypropagated
    # Collect all TArray/TPtr of TArray
    vars := Set(Collect(c, @(1, var, e->IsPtrT(e.t) or (IsArrayT(e.t) and IsBound(e.t.t) and IsArrayT(e.t.t)))));
    # force copypropagate X, Y, twds into usage 
    cmds := Collect(c, [assign, @(1), [@(2, nth), @(3, var, e->e in vars), @(4)]]);
    for cmd in cmds do
        cmd.exp.t := cmd.exp.computeType(); # sometimes cmd.exp.t does not match the actual object type
        vars := Collect(c, @(1, var, e->e=cmd.loc));
        c := SubstBottomUp(c, @(1, var, e->e in vars), e->cmd.exp);
    od;
    # Collect(c, @(1, assign, e->e in cmds));
    c := SubstBottomUp(c, @(1, assign, e->e in cmds), e->skip());
    c := FlattenCode(c);

    return c;

end;

# Rule 2: 2b = (2b) 4b 
MPExtractLow := function(c, a, blen, opts)
    local cc;

    cc := chain(
        comment("MPExtractLow "::StringInt(blen)),
        assign(nth(c, 0), nth(a, 2)),
        assign(nth(c, 1), nth(a, 3))
    );

    return cc;

end;

# Rule 14: 2b = (2b) 2b
MPEqualTypeCastD := function(c, a, blen, opts)
    local cc;

    cc := chain(
        comment("MPEqualTypeCastD "::StringInt(blen)),
        assign(nth(c, 0), nth(a, 0)),
        assign(nth(c, 1), nth(a, 1))
    );

    return cc;

end;

# Rule 16: 2b = (2b) 1
# Rule 32: 2b = TInt or 0/1
MPTypeCastDI := function(c, a, blen, opts)
    local cc;

    cc := chain(
        comment("MPTypeCastDI "::StringInt(blen)),
        assign(nth(c, 0), 0),
        assign(nth(c, 1), a)
    );

    return cc;

end;

# Rule 3: int = 4b >> blen*2
MPExtractCarry := function(c, a, blen, opts)
    local cc;

    cc := chain(
        comment("MPExtractCarry "::StringInt(blen)),
        assign(c, nth(a, 1))
    );

    return cc;

end;

# Rule 4: 4b = 4b + 0/1
# a[0-3]
# b = 0/1
# [could be optimized further]
MPPropagateCarry := function(c, a, b, blen, opts)
    
    # c[3] = a[3] + b
    # if c[3] = 0 c[2] = a[2] + b else c[2] = a[2] // c[2] := c[3] = 0 ? a[2] + b : a[2]
    # if c[2] = 0 and c[3] = 0 c[1] = a[1] + b else c[1] = a[1] 
    # if c[1] = 0 and c[2] = 0 and c[3] = 0 c[0] = a[0] + b else c[0] = a[0]
    
    local cc;

    cc := chain(
        comment("MPPropagateCarry "::StringInt(blen)),
        assign(nth(c, 3), nth(a, 3) + b),
        assign(nth(c, 2), cond(eq(nth(c, 3), 0), nth(a, 2) + b, nth(a, 2))),
        assign(nth(c, 1), cond(logic_and(eq(nth(c, 2), 0), eq(nth(c, 3), 0)), nth(a, 1) + b, nth(a, 1))),
        assign(nth(c, 0), cond(logic_and(eq(nth(c, 1), 0), eq(nth(c, 2), 0), eq(nth(c, 3), 0)), nth(a, 0) + b, nth(a, 0)))
    );

    return cc;

end;

# Rule 5: int = 2b == 2b
MPEqualD := function(c, a, b, blen, opts)
    local cc;

    cc := chain(
        comment("MPEqual "::StringInt(blen)),
        # assign(c, logic_and(eq(nth(a, 0), nth(b, 0)), eq(nth(a, 1), nth(b, 1))))
        # force to return int
        assign(c, cond(
                    logic_and(eq(nth(a, 0), nth(b, 0)), eq(nth(a, 1), nth(b, 1))),
                    1,
                    0
                    ))
    );

    return cc;
end;

# Rule 34: TBool = 2b == int
MPEqualDI := function(c, a, b, blen, opts)
    local cc;

    cc := chain(
        comment("MPEqualDI "::StringInt(blen)),
        # assign(c, logic_and(eq(nth(a, 0), 0), eq(nth(a, 1), b)))
        # force to return int
        assign(c, cond(
                    logic_and(eq(nth(a, 0), 0), eq(nth(a, 1), b)),
                    1,
                    0
                    ))
    );

    return cc;
end;

# Rule 24: TBool = 2b <> int
MPNotEqualDI := function(c, a, b, blen, opts)
    local cc;

    cc := chain(
        comment("MPNotEqualDI "::StringInt(blen)),
        # assign(c, logic_or(neq(nth(a, 0), 0), neq(nth(a, 1), b)))
        # force to return int
        assign(c, cond(
                    logic_or(neq(nth(a, 0), 0), neq(nth(a, 1), b)),
                    1,
                    0
                    ))
    );

    return cc;
end;

# Rule 10: 2b = 4b >> blen*2
MPExtractHigh := function(c, a, blen, opts)
    local cc;

    cc := chain(
        comment("MPExtractHigh "::StringInt(blen)),
        assign(nth(c, 0), nth(a, 0)),
        assign(nth(c, 1), nth(a, 1))
    );

    return cc;

end;

# Rule 11: 2b = 2b
# same impl. as MPExtractHigh
MPAssignDD := function(c, a, blen, opts)
    local cc;

    cc := chain(
        comment("MPAssignDD "::StringInt(blen)),
        assign(nth(c, 0), nth(a, 0)),
        assign(nth(c, 1), nth(a, 1))
    );

    return cc;

end;

# Rule 12: int = 2b (0/1) && 2b (0/1)
MPLogicAndDD := function(c, a, b, blen, opts)
    local cc;

    cc := chain(
        comment("MPLogicAndDD "::StringInt(blen)),
        # assign(c, logic_and(nth(a, 1), nth(b, 1)))
        assign(c, cond(
                    logic_and(nth(a, 1), nth(b, 1)),
                    1,
                    0
                    ))
    );

    return cc;

end;

# Rule 17: 2b = 0/1 ? 2b : 2b
MPCondD := function(c, d, a, b, blen, opts)
    
    local cc;

    # break into 2 cond for each b in 2b

    cc := chain(
        comment("MPCondD "::StringInt(blen)),
        assign(nth(c, 0), cond(d, nth(a, 0), nth(b, 0))), # b = cond : b ? b
        assign(nth(c, 1), cond(d, nth(a, 1), nth(b, 1))) # b = cond : b ? b
    );

    return cc;

end;

# Rule 41: 2b = 0/1 ? 2b : int
MPCondDDI := function(c, d, a, b, blen, opts)
    
    local cc;

    # break into 2 cond for each b in 2b

    cc := chain(
        comment("MPCondDDI "::StringInt(blen)),
        assign(nth(c, 0), cond(d, nth(a, 0), 0)), # b = cond : b ? int
        assign(nth(c, 1), cond(d, nth(a, 1), b)) # b = cond : b ? int
    );

    return cc;

end;

# Rule 18: 2b = 2b & 2b
MPBinAndD := function(c, a, b, blen, opts)
    local cc;

    cc := chain(
        comment("MPBinAndD "::StringInt(blen)),
        assign(nth(c, 0), bin_and(nth(a, 0), nth(b, 0))), # b = b & b
        assign(nth(c, 1), bin_and(nth(a, 1), nth(b, 1))) # b = b & b
    );

    return cc;

end;

# Rule 19: 2b = 2b | 2b
MPBinOrD := function(c, a, b, blen, opts)
    local cc;

    cc := chain(
        comment("MPBinOrD "::StringInt(blen)),
        assign(nth(c, 0), bin_or(nth(a, 0), nth(b, 0))), # b = b | b
        assign(nth(c, 1), bin_or(nth(a, 1), nth(b, 1))) # b = b | b
    );

    return cc;

end;

# a[0] a[1]
# b[0] b[1]
# Rule 6: TBool/TInt = 2b < 2b
# also used for Rule 25: TBool/TInt = 2b > 2b
MPLessThanD := function(c, a, b, blen, opts)
    
    # if a[0] < b[0] return true
    # if a[0] = b[0] and a[1] < b[1] return true
    # else return false
    
    local cc;

    cc := chain(
        comment("MPLessThan "::StringInt(blen)),
        assign(c, cond(
                    logic_or(lt(nth(a, 0), nth(b, 0)), 
                             logic_and(eq(nth(a, 0), nth(b, 0)), lt(nth(a, 1), nth(b, 1)))),
                    1,
                    0
                    )
        )
    );

    return cc;
end;

# Rule 26: TBool/TInt = 2b < TInt
# Rule 42: TBool/TInt = 2b < 1
# Rule 43: TBool/TInt = 2b < TInt
MPLessThanDI := function(c, a, b, blen, opts)
    
    # if a[0] = 0 and a[1] < b return true
    # else return false
    
    local cc;

    cc := chain(
        comment("MPLessThanDI "::StringInt(blen)),
        assign(c, cond(
                    logic_and(eq(nth(a, 0), 0), lt(nth(a, 1), b)),
                    1,
                    0
                    )
        )
    );

    return cc;
end;

# Rule 33: TInt = int < 2b
MPLessThanID := function(c, a, b, blen, opts)
    
    # if b[0] > 0 or (b[0] = 0 and b[1] > a) return true
    # else return false
    
    local cc;

    cc := chain(
        comment("MPLessThanID "::StringInt(blen)),
        assign(c, cond(
                    logic_or(lt(0, nth(b, 0)), logic_and(eq(nth(b, 0), 0), lt(a, nth(b, 1)))),
                    1,
                    0
                    )
        )
    );

    return cc;
end;

# two parts shift
# assumption: 2*blen < int < 3*blen
# 2b = 4b >> int
# should be named MPShiftRight2Q
MPShiftRight2 := function(c, a, b, blen, opts)
        
    local cc, in0;

    in0 := var.fresh_t("in_", TInt); 

    cc := chain(
        comment("Begin of MPShiftRight2"),
        assign(in0, b - (blen * 2)), # 1 # int = 1
        assign(nth(c, 0), bin_shr(nth(a, 0), in0)), # b = b >> int TODO
        # b = (b << int) | (b >> int) TODO
        assign(nth(c, 1), bin_or(bin_shl(nth(a, 0), blen - in0), # b << blen - int TODO
                                 bin_shr(nth(a, 1), in0))), # b >> int TODO
        comment("End of MPShiftRight2")
    );

    return cc;
end;

# three parts shift
# assumption: blen < int < 2*blen
# 2b = 4b >> int
# should be named MPShiftRight3Q
# [could be optimized further]
MPShiftRight3 := function(c, a, b, blen, opts)
        
    local cc, in1, in2, p1, p2, mask;

    in1 := var.fresh_t("in_", TInt); 
    in2 := var.fresh_t("in_", TInt);
    p1 := var.fresh_t("p_", T_UInt(blen)); 
    p2 := var.fresh_t("p_", T_UInt(blen)); 
    mask := var.fresh_t("m_", T_UInt(blen)); 

    cc := chain(
        comment("Begin of MPShiftRight3"),
        assign(in1, b - blen), # int = int
        assign(in2, blen*2 - (b)), # int = int
        assign(p1, bin_shr(nth(a, 2), in1)), # b = b >> int
        # b = ((b) 1 << int) - 1 TODO
        assign(mask, bin_shl(tcast(T_UInt(blen), 1), in1) - 1), # 111...111, len: 10  
        assign(p2, bin_and(nth(a, 0), mask)), # b = b & 11..11 TODO
        # b = (b << int) | (b >> int) TODO
        assign(nth(c, 0), bin_or(bin_shl(p2, in2), # b << int TODO
                                 bin_shr(nth(a, 1), in1))), # b >> int TODO
        assign(nth(c, 1), bin_or(bin_shl(nth(a, 1), in2), p1)), # b = (b << int) | b TODO
        comment("End of MPShiftRight3")
    );

    return cc;
end;

# two parts shift
# assumption: int < blen
# Rule 20: 2b = 2b >> int
MPShiftRight2D := function(c, a, b, blen, opts)
        
    local cc;

    cc := chain(
        comment("Begin of MPShiftRight2D"),
        assign(nth(c, 0), bin_shr(nth(a, 0), b)), # b = b >> int
        # b = (b << int) | (b >> int)
        assign(nth(c, 1), bin_or(bin_shl(nth(a, 0), blen - b), # b = b << (blen - int)
                                 bin_shr(nth(a, 1), b))), # b = b >> int
        comment("End of MPShiftRight2D")
    );

    return cc;
end;

# one part shift
# assumption: blen < int < 2*blen
# Rule 21: 2b = 2b >> int
MPShiftRight1D := function(c, a, b, blen, opts)
        
    local cc;

    cc := chain(
        comment("Begin of MPShiftRight1D"),
        assign(nth(c, 0), 0), # b = 0
        assign(nth(c, 1), bin_shr(nth(a, 0), b - blen)), # b >> int
        comment("End of MPShiftRight1D")
    );

    return cc;
end;

# two parts shift
# assumption: int < blen
# Rule 22: 2b = 2b << int
MPShiftLeft2D := function(c, a, b, blen, opts)
        
    local cc;

    cc := chain(
        comment("Begin of MPShiftLeft2D"),
        # b = (b << int) | (b >> int)
        assign(nth(c, 0), bin_or(bin_shl(nth(a, 0), b), # b = b << int
                                 bin_shr(nth(a, 1), blen - b))), # b = b >> (blen - int)
        assign(nth(c, 1), bin_shl(nth(a, 1), b)), # b = b << int
        comment("End of MPShiftLeft2D")
    );

    return cc;
end;

# two parts shift
# assumption: blen < int < 2*blen
# Rule 23: 2b = 2b << int
MPShiftLeft1D := function(c, a, b, blen, opts)
        
    local cc;

    cc := chain(
        comment("Begin of MPShiftLeft1D"),
        assign(nth(c, 0), bin_shl(nth(a, 1), b - blen)), # b = b >> (int - blen)
        assign(nth(c, 1), 0), # b = 0
        comment("End of MPShiftLeft1D")
    );

    return cc;
end;

# one part shift
# assumption: len(TInt) < blen
# assumption: blen < int < 2*blen
# Rule 28: 2b = TInt >> int
MPShiftRight1I := function(c, a, b, blen, opts)
        
    local cc;

    cc := chain(
        comment("Begin of MPShiftRight1I "),
        assign(nth(c, 0), 0), # b = 0
        assign(nth(c, 1), 0), # b = 0
        comment("End of MPShiftRight1I ")
    );

    return cc;
end;

# two parts shift
# assumption: len(TInt) < blen
# assumption: int < blen
# assumption: int+len(TInt) < blen
# Rule 29: 2b = TInt << int
MPShiftLeft2I := function(c, a, b, blen, opts)
        
    local cc;

    cc := chain(
        comment("Begin of MPShiftLeft2I"),
        assign(nth(c, 0), 0), # b = 0
        assign(nth(c, 1), bin_shl(a, b)), # b = TInt << int
        comment("End of MPShiftLeft2I")
    );

    return cc;
end;

# Debug Rule
MPCallD := function(t, a, blen, opts)
        
    local cc;

    cc := chain(
        comment("Begin of MPCallD"),
        call(var("apprint"), t, nth(a, 0)),
        call(var("apprint"), t, nth(a, 1)),
        comment("End of MPCallD")
    );

    return cc;
end;

# Rule 40: 2b = 0/1 + 0/1
MPAddDII := function(c, a, b, blen, opts)
    
    # c[1] = 0/1 + 0/1;
    # c[0] = 0;

    local cc;

    cc := chain(
        comment("MPAddDII "::StringInt(blen)),
        assign(nth(c, 1), a + b), # b = int + int
        assign(nth(c, 0), 0)
    );

    return cc;

end;

# Rule 38: 2b = 2b + 0/1
# Rule 39: 2b = 0/1 + 2b
MPAddDDI := function(c, a, b, blen, opts)
    
    # DBaseInt sum;
    # int carry;
    # sum = (DBaseInt) a[1] + 0/1;
    # c[1] = (BaseInt) sum;
    
    # carry = (sum >> BaseSize);
    # sum = (DBaseInt) a[0] + carry;
    # c[0] = (BaseInt) sum;
    
    local cc, s1, cr1;

    s1 := var.fresh_t("s1_", T_UInt(blen*2)); # sum
    cr1 := var.fresh_t("cr1_", TInt); # carry

    cc := chain(
        comment("MPAddDDI "::StringInt(blen)),
        assign(s1, nth(a, 1) + b), # 2b = b + 0/1
        assign(nth(c, 1), tcast(T_UInt(blen), s1)), # b = (b) 2b -> c[3] = sum[1]
        assign(cr1, bin_shr(s1, blen)), # b = 2b >> blen -> carry = sum[0]
        assign(s1, nth(a, 0) + cr1), # 2b = b + 0/1
        assign(nth(c, 0), tcast(T_UInt(blen), s1)) # b = (b) 2b -> c[2] = sum[1]
    );

    return cc;

end;

# Rule 15: 4b = 0/1 + 2b
MPAddQID := function(c, a, b, blen, opts)
    
    # DBaseInt sum;
    # int carry;
    # sum = 0/1 + (DBaseInt) b[1];
    # c[3] = (BaseInt) sum;
    
    # carry = (sum >> BaseSize);
    # sum = (DBaseInt) b[0] + carry;
    # c[2] = (BaseInt) sum;
    
    # carry = (sum >> BaseSize);
    # c[1] = carry;
    
    # c[0] = 0;

    local cc, s1, cr1;

    s1 := var.fresh_t("s1_", T_UInt(blen*2)); # sum
    cr1 := var.fresh_t("cr1_", TInt); # carry

    cc := chain(
        comment("MPAddQID "::StringInt(blen)),
        assign(s1, nth(b, 1) + a), # 2b = b + 0/1
        assign(nth(c, 3), tcast(T_UInt(blen), s1)), # b = (b) 2b -> c[3] = sum[1]
        assign(cr1, bin_shr(s1, blen)), # b = 2b >> blen -> carry = sum[0]
        assign(s1, nth(b, 0) + cr1), # 2b = b + 0/1
        assign(nth(c, 2), tcast(T_UInt(blen), s1)), # b = (b) 2b -> c[2] = sum[1]
        assign(cr1, bin_shr(s1, blen)), # b = 2b >> b -> carry = sum[0]
        assign(nth(c, 1), cr1), # b = b
        assign(nth(c, 0), 0) # b = b
    );

    return cc;

end;

# |add(c_2b, a_2b, b_2b)|_2b
# |cc|_2b
# consumes: a[0], a[1], b[0], b[1]
# produces: c[0], c[1]
# [can be broken down]
# [could be optimized further]
MPAddDDD := function(c, a, b, blen, opts)
    
    # DBaseInt sum;
    # int carry;
    # sum = (DBaseInt) a[1] + (DBaseInt) b[1]; # 32b = 16b + 16b
    # c[1] = (BaseInt) sum;
    
    # carry = (sum >> BaseSize);
    # sum = (DBaseInt) a[0] + (DBaseInt) b[0];
    # sum = sum + carry; # 32b = 32b + 1
    # c[0] = (BaseInt) sum;

    local cc, s1, cr1;

    s1 := var.fresh_t("s1_", T_UInt(blen*2)); # sum
    # cr1 := var.fresh_t("cr1_", T_UInt(blen)); # carry
    cr1 := var.fresh_t("cr1_", TInt); # carry

    cc := chain(
        comment("MPAddDDD "::StringInt(blen)),
        # assign(s1, tcast(T_UInt(blen*2), nth(a, 1)) + tcast(T_UInt(blen*2), nth(b, 1))), # 2b = b + b -> MPAddQDD
        assign(s1, nth(a, 1) + nth(b, 1)), # see above
        assign(nth(c, 1), tcast(T_UInt(blen), s1)), # b = (b) 2b -> c[3] = sum[1]
        assign(cr1, bin_shr(s1, blen)), # b = 2b >> blen -> carry = sum[0]
        # assign(s1, tcast(T_UInt(blen*2), nth(a, 0)) + tcast(T_UInt(blen*2), nth(b, 0))), # 2b = b + b -> MPAddQDD
        assign(s1, nth(a, 0) + nth(b, 0)), # see above
        assign(s1, s1 + cr1), # 2b = 2b + 0/1, guaranteed no overflow -> PropagateCarry
        assign(nth(c, 0), tcast(T_UInt(blen), s1)) # b = (b) 2b -> c[2] = sum[1]
    );

    return cc;

end;

# |add(c_4b, a_2b, b_2b)|_4b
# |cc|_2b
# consumes: a[0], a[1], b[0], b[1]
# produces: c[0], c[1], c[2], c[3]
# [can be broken down]
# [could be optimized further]
MPAddQDD := function(c, a, b, blen, opts)
    
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

    local cc, s1, cr1;

    s1 := var.fresh_t("s1_", T_UInt(blen*2)); # sum
    # cr1 := var.fresh_t("cr1_", T_UInt(blen)); # carry
    cr1 := var.fresh_t("cr1_", TInt); # carry

    cc := chain(
        comment("MPAddQDD "::StringInt(blen)),
        # assign(s1, tcast(T_UInt(blen*2), nth(a, 1)) + tcast(T_UInt(blen*2), nth(b, 1))), # 2b = b + b -> MPAddQDD
        assign(s1, nth(a, 1) + nth(b, 1)), # see above
        assign(nth(c, 3), tcast(T_UInt(blen), s1)), # b = (b) 2b -> c[3] = sum[1]
        assign(cr1, bin_shr(s1, blen)), # b = 2b >> blen -> carry = sum[0]
        # assign(s1, tcast(T_UInt(blen*2), nth(a, 0)) + tcast(T_UInt(blen*2), nth(b, 0))), # 2b = b + b -> MPAddQDD
        assign(s1, nth(a, 0) + nth(b, 0)), # see above
        assign(s1, s1 + cr1), # 2b = 2b + 0/1, guaranteed no overflow -> PropagateCarry
        assign(nth(c, 2), tcast(T_UInt(blen), s1)), # b = (b) 2b -> c[2] = sum[1]
        assign(cr1, bin_shr(s1, blen)), # b = 2b >> b -> carry = sum[0]
        assign(nth(c, 1), cr1), # b = b
        assign(nth(c, 0), 0) # b = b
    );

    return cc;

end;

# |add(c_4b, a_4b, b_2b)|_4b
# |cc|_2b
# consumes: a[0], a[1], a[2], a[3], b[0], b[1]
# produces: c[0], c[1], c[2], c[3]
# [could be optimized further]
MPAddQQD := function(c, a, b, blen, opts)
    
    # DBaseInt sum;
    # int carry;

    # sum = a[3] + b[1]; # 2b = b + b
    # c[3] = (BaseInt) sum;
    
    # carry = (sum >> BaseSize);
    # sum = a[2] + b[0];
    # sum = sum + carry; # 2b = 2b + 0/1
    # c[2] = (BaseInt) sum;
    
    # carry = (sum >> BaseSize);
    # sum = a[1] + carry; # 2b = 2b + 0/1
    # c[1] = (BaseInt) sum;
    
    # carry = (sum >> BaseSize);
    # sum = a[0] + carry; # 2b = 2b + 0/1
    # c[0] = (BaseInt) sum;

    local cc, s1, cr1;

    s1 := var.fresh_t("s1_", T_UInt(blen*2)); # sum 
    cr1 := var.fresh_t("cr1_", TInt); # carry

    cc := chain(
        comment("Begin of MPAddQQD "::StringInt(blen)),

        assign(s1, nth(a, 3) + nth(b, 1)), # 2b = b + b -> MPAddQDD
        assign(nth(c, 3), tcast(T_UInt(blen), s1)), # b = (b) 2b -> c[3] = sum[1]
        
        assign(cr1, bin_shr(s1, blen)), # b = 2b >> b -> carry = sum[0]
        assign(s1, nth(a, 2) + nth(b, 0)),  # 2b = b + b -> MPAddQDD
        assign(s1, s1 + cr1), # 2b = 2b + 0/1, guaranteed no overflow -> PropagateCarry
        assign(nth(c, 2), tcast(T_UInt(blen), s1)), # b = (b) 2b -> c[2] = sum[1]
        
        assign(cr1, bin_shr(s1, blen)), # b = 2b >> b -> carry = sum[0]
        assign(s1, nth(a, 1) + cr1), # 2b = 2b + 0/1, guaranteed no overflow -> PropagateCarry
        assign(nth(c, 1), tcast(T_UInt(blen), s1)), # b = (b) 2b -> c[1] = sum[1]
        
        assign(cr1, bin_shr(s1, blen)), # b = 2b >> b -> carry = sum[0]
        assign(s1, nth(a, 0) + cr1), # 2b = 2b + 0/1, guaranteed no overflow -> PropagateCarry
        assign(nth(c, 0), tcast(T_UInt(blen), s1)), # b = (b) 2b -> c[0] = sum[1]

        comment("End of MPAddQQD "::StringInt(blen))

    );

    return cc;

end;

# |add(c_4b, a_4b, b_4b)|_4b
# |cc|_2b
# consumes: a[0], a[1], a[2], a[3], b[0], b[1], b[2], b[3]
# produces: c[0], c[1], c[2], c[3]
# [could be optimized further]
MPAddQQQ := function(c, a, b, blen, opts)
    
    # DBaseInt sum;
    # int carry;

    # sum = a[3] + b[3]; # 2b = b + b
    # c[3] = (BaseInt) sum;
    
    # carry = (sum >> BaseSize);
    # sum = a[2] + b[2];
    # sum = sum + carry; # 2b = 2b + 0/1
    # c[2] = (BaseInt) sum;
    
    # carry = (sum >> BaseSize);
    # sum = a[1] + b[1];
    # sum = sum + carry; # 2b = 2b + 0/1
    # c[1] = (BaseInt) sum;
    
    # carry = (sum >> BaseSize);
    # sum = a[0] + b[0];
    # sum = sum + carry; # 2b = 2b + 0/1
    # c[0] = (BaseInt) sum;

    local cc, s1, cr1, k0, k1, k2;

    s1 := var.fresh_t("s1_", T_UInt(blen*2)); # sum 
    cr1 := var.fresh_t("cr1_", TInt); # carry

    k0 := var.fresh_t("k_", TReal); 
    k1 := var.fresh_t("k_", TReal); 
    k2 := var.fresh_t("k_", TReal); 

    cc := chain(
        comment("Begin of MPAddQQQ "::StringInt(blen)),

        # assign(k0, bin_or(
        #                 bin_shl(tcast(TReal, nth(a, 0)), blen * 3), 
        #                 bin_shl(tcast(TReal, nth(a, 1)), blen * 2), 
        #                 bin_shl(tcast(TReal, nth(a, 2)), blen), 
        #                 nth(a, 3)
        #                 )), 
        # call(var("apprint"), var("\"MakeMPAddQQQ input a: \""), k0),


        # assign(k1, bin_or(
        #                 bin_shl(tcast(TReal, nth(b, 0)), blen * 3), 
        #                 bin_shl(tcast(TReal, nth(b, 1)), blen * 2), 
        #                 bin_shl(tcast(TReal, nth(b, 2)), blen), 
        #                 nth(b, 3)
        #                 )), 
        # call(var("apprint"), var("\"MakeMPAddQQQ input b: \""), k1),


        assign(s1, nth(a, 3) + nth(b, 3)), # 2b = b + b -> MPAddQDD
        assign(nth(c, 3), tcast(T_UInt(blen), s1)), # b = (b) 2b -> c[3] = sum[1]
        
        assign(cr1, bin_shr(s1, blen)), # b = 2b >> b -> carry = sum[0]
        assign(s1, nth(a, 2) + nth(b, 2)),  # 2b = b + b -> MPAddQDD
        assign(s1, s1 + cr1), # 2b = 2b + 0/1, guaranteed no overflow -> PropagateCarry
        assign(nth(c, 2), tcast(T_UInt(blen), s1)), # b = (b) 2b -> c[2] = sum[1]
        
        assign(cr1, bin_shr(s1, blen)), # b = 2b >> b -> carry = sum[0]
        assign(s1, nth(a, 1) + nth(b, 1)),  # 2b = b + b -> MPAddQDD
        assign(s1, s1 + cr1), # 2b = 2b + 0/1, guaranteed no overflow -> PropagateCarry
        assign(nth(c, 1), tcast(T_UInt(blen), s1)), # b = (b) 2b -> c[1] = sum[1]
        
        assign(cr1, bin_shr(s1, blen)), # b = 2b >> b -> carry = sum[0]
        assign(s1, nth(a, 0) + nth(b, 0)),  # 2b = b + b -> MPAddQDD
        assign(s1, s1 + cr1), # 2b = 2b + 0/1, guaranteed no overflow -> PropagateCarry
        assign(nth(c, 0), tcast(T_UInt(blen), s1)), # b = (b) 2b -> c[0] = sum[1]

        # assign(k2, bin_or(
        #                 bin_shl(tcast(TReal, nth(c, 0)), blen * 3), 
        #                 bin_shl(tcast(TReal, nth(c, 1)), blen * 2), 
        #                 bin_shl(tcast(TReal, nth(c, 2)), blen), 
        #                 nth(c, 3)
        #                 )), 
        # call(var("apprint"), var("\"MakeMPAddQQQ output c: \""), k2),
        comment("End of MPAddQQQ "::StringInt(blen))

    );

    return cc;

end;

# |sub(c_2b, a_2b, b_2b)|_2b
# |cc|_2b
# consumes: a[0], a[1], b[0], b[1]
# produces: c[0], c[1]
# will wrap around if a < b
# [can be broken down]
# [could be optimized further]
MPSubDDD := function(c, a, b, blen, opts)

    # d1 = a1 - b1
    # if (a1 < b1) borrow = 1 else borrow = 0
    # c1 = d1
    # d0 = a0 - b0
    # d0 = d0 - borrow  
    # c0 = d0

    # 2b + (2b) 1 << #b
    # a - b = a + (1 << #b) - b

    local cc, br, d1, d0, k0, k1, k2, k3, k4, k5;

    br := var.fresh_t("br_", TInt); # borrow
    d1 := var.fresh_t("d1_", T_UInt(blen)); # diff
    d0 := var.fresh_t("d0_", T_UInt(blen)); # diff

    # debug
    k0 := var.fresh_t("k_", T_UInt(blen*2)); 
    k1 := var.fresh_t("k_", T_UInt(blen*2)); 
    k2 := var.fresh_t("k_", T_UInt(blen*2)); 
    k3 := var.fresh_t("k_", T_UInt(blen*2)); 
    k4 := var.fresh_t("k_", T_UInt(blen*2)); 
    k5 := var.fresh_t("k_", TReal); 

    cc := chain(
        comment("Begin of MPSubDDD "::StringInt(blen)),

        # assign(k0, bin_or(
        #                 bin_shl(tcast(T_UInt(blen*2), nth(a, 0)), blen), 
        #                 nth(a, 1)
        #                 )),
        # call(var("apprint"), var("\"MPSubDDD input a: \""), k0),
        # assign(k1, bin_or(
        #                 bin_shl(tcast(T_UInt(blen*2), nth(b, 0)), blen), 
        #                 nth(b, 1)
        #                 )),
        # call(var("apprint"), var("\"MPSubDDD input b: \""), k1),

        assign(d1, nth(a, 1) - nth(b, 1)), # b = b - b, expected to be wrapped around
        # assign(br, cond(lt(nth(a, 1), nth(b, 1)), 1, 0)), # b = b < b ? 1 : 0
        assign(br, tcast(TInt, lt(nth(a, 1), nth(b, 1)))), # b = b < b ? 1 : 0
        assign(nth(c, 1), d1), # b = b
        assign(d0, nth(a, 0) - nth(b, 0)), # b = b - b
        assign(d0, d0 - br), # b = b - b
        assign(nth(c, 0), d0), # b = b

        # assign(k2, bin_or(
        #                 bin_shl(tcast(T_UInt(blen*2), nth(c, 0)), blen), 
        #                 nth(c, 1)
        #                 )),
        # call(var("apprint"), var("\"MPSubDDD output c: \""), k2),

        comment("End of MPSubDDD "::StringInt(blen))

    );

    return cc;

end;

# consumes: a, b[0], b[1]
# produces: c[0], c[1]
# will wrap around if a < b
# [can be broken down]
MPSubDID := function(c, a, b, blen, opts)

    # d1 = a - b[1]
    # if (a < b[1]) borrow = 1 else borrow = 0
    # c1 = d1
    # d0 = 0 - b0
    # d0 = d0 - borrow  
    # c0 = d0

    local cc, br, d1, d0;

    br := var.fresh_t("br_", TInt); # borrow
    d1 := var.fresh_t("d1_", T_UInt(blen)); # diff
    d0 := var.fresh_t("d0_", T_UInt(blen)); # diff

    cc := chain(
        comment("Begin of MPSubDID "::StringInt(blen)),

        assign(d1, a - nth(b, 1)), # b = TInt - b, expected to be wrapped around
        assign(br, tcast(TInt, lt(a, nth(b, 1)))), # b = TInt < b ? 1 : 0
        assign(nth(c, 1), d1), # b = b
        assign(d0, 0 - nth(b, 0)), # b = 0 - b
        assign(d0, d0 - br), # b = b - b
        assign(nth(c, 0), d0), # b = b

        comment("End of MPSubDID "::StringInt(blen))

    );

    return cc;

end;

# |sub(c_2b, a_2b, b_int)|_2b
# |cc|_2b
# consumes: a[0], a[1], b
# produces: c[0], c[1]
MPSubDDI := function(c, a, b, blen, opts)

    # d1 = a[1] - b
    # if (a[1] < b) borrow = 1 else borrow = 0
    # c[1] = d1
    # c[0] = a[0] - borrow

    local cc, br, d1;

    br := var.fresh_t("br_", TInt); # borrow
    d1 := var.fresh_t("d1_", T_UInt(blen)); # diff

    cc := chain(
        comment("MPSubDDI "::StringInt(blen)),
        
        assign(d1, nth(a, 1) - b), # b = b - int, expected to be wrapped around
        assign(br, tcast(TInt, lt(nth(a, 1), b))), # b = b < int ? 1 : 0
        assign(nth(c, 1), d1), # b = b
        assign(nth(c, 0), nth(a, 0) - br) # b = b - int

    );

    return cc;

end;

# consumes: a, b
# produces: c[0], c[1]
MPSubDII := function(c, a, b, blen, opts)

    # d1 = a - b
    # if (a < b) borrow = 1 else borrow = 0
    # c[1] = d1
    # c[0] = 0 - borrow

    local cc, br, d1;

    br := var.fresh_t("br_", TInt); # borrow
    d1 := var.fresh_t("d1_", T_UInt(blen)); # diff

    cc := chain(
        comment("MPSubDII "::StringInt(blen)),
        
        assign(d1, a - b), 
        assign(br, tcast(TInt, lt(a, b))), 
        assign(nth(c, 1), d1), 
        assign(nth(c, 0), 0 - br) 

    );

    return cc;

end;

# |sub(c_4b, a_4b, b_2b)|_4b
# |cc|_2b
# consumes: a[0], a[1], a[2], a[3], b[0], b[1]
# produces: c[0], c[1], c[2], c[3]
# assumes: a > b
# [can be broken down]
# [could be optimized further]
MPSubQQD := function(c, a, b, blen, opts)

    # int borrow = 0;
    # BaseInt d3, d2;

    # d3 = a3 - b1 # 1 - 2 = 1 + 256 - 2
    # if (a3 < b1) borrow = 1 else borrow = 0
    # c3 = d3
    # d2 = a2 - b0
    # d2 = d2 - borrow  
    # if (a2 < b0 or (a2 = b0 and borrow = 1)) borrow = 1 else borrow = 0
        # if (a2 < (b0+borrow)) borrow = 1 # hard part
        # borrow = 1 in 2 cases
        # 1. a2 < b0
        # 2. a2 = b0 and borrow = 1
    # c2 = d2
    # c1 = a1 - borrow
    # c0 = a0

    # 2b + (2b) 1 << #b
    # a - b = a + (1 << #b) - b

    local cc, br, d3, d2, k0, k1, k2, k3, k4, k5;

    br := var.fresh_t("br_", TInt); # borrow
    d3 := var.fresh_t("d1_", T_UInt(blen)); # diff_3
    d2 := var.fresh_t("d0_", T_UInt(blen)); # diff_2

    # debug
    k0 := var.fresh_t("k_", TReal); 
    k1 := var.fresh_t("k_", T_UInt(blen*2)); 
    k2 := var.fresh_t("k_", TReal); 


    cc := chain(
        comment("Begin of MPSubQQD "::StringInt(blen)),

        # assign(k0, bin_or(
        #                 bin_shl(tcast(TReal, nth(a, 0)), blen * 3), 
        #                 bin_shl(tcast(TReal, nth(a, 1)), blen * 2), 
        #                 bin_shl(tcast(TReal, nth(a, 2)), blen), 
        #                 nth(a, 3)
        #                 )), 
        # call(var("apprint"), var("\"MPSubQQD input a: \""), k0),
        # assign(k1, bin_or(
        #                 bin_shl(tcast(T_UInt(blen*2), nth(b, 0)), blen), 
        #                 nth(b, 1)
        #                 )),
        # call(var("apprint"), var("\"MPSubQQD input b: \""), k1),


        assign(d3, nth(a, 3) - nth(b, 1)), # b = b - b, expected to be wrapped around
        assign(br, tcast(TInt, lt(nth(a, 3), nth(b, 1)))), # b = b < b ? 1 : 0
        assign(nth(c, 3), d3), # b = b
        assign(d2, nth(a, 2) - nth(b, 0)), # b = b - b
        assign(d2, d2 - br), # b = b - b
        # b = b < b or (b == b and b == 1) ? 1 : 0
        # assign(br, cond(logic_or(lt(nth(a, 2), nth(b, 0)), logic_and(eq(nth(a, 2), nth(b, 0)), eq(br, 1))), 1, 0)),
        assign(br, tcast(TInt, logic_or(lt(nth(a, 2), nth(b, 0)), logic_and(eq(nth(a, 2), nth(b, 0)), eq(br, 1))))),
        assign(nth(c, 2), d2), # b = b
        assign(nth(c, 1), nth(a, 1) - br), # b = b - 1
        assign(nth(c, 0), nth(a, 0)), # b = b

        # assign(k2, bin_or(
        #                 bin_shl(tcast(TReal, nth(c, 0)), blen * 3), 
        #                 bin_shl(tcast(TReal, nth(c, 1)), blen * 2), 
        #                 bin_shl(tcast(TReal, nth(c, 2)), blen), 
        #                 nth(c, 3)
        #                 )), 
        # call(var("apprint"), var("\"MPSubQQD output c: \""), k2),

        comment("End of MPSubQQD "::StringInt(blen))
    );

    return cc;

end;

# |sub(c_4b, a_4b, b_4b)|_4b
# |cc|_2b
# consumes: a[0], a[1], a[2], a[3], b[0], b[1], b[2], b[3]
# produces: c[0], c[1], c[2], c[3]
# assumes: a > b
# [can be broken down]
# [could be optimized further]
MPSubQQQ := function(c, a, b, blen, opts)

    # int br;
    # BaseInt d0, d1, d2, d3;

    # d3 = a3 - b3
    # if (a3 < b3) br = 1 else br = 0
    # c3 = d3
    
    # d2 = a2 - b2
    # d2 = d2 - br
    # if (a2 < b2 or (a2 = b2 and br = 1)) br = 1 else br = 0
    # c2 = d2
    
    # d1 = a1 - b1
    # d1 = d1 - br
    # if (a1 < b1 or (a1 = b1 and br = 1)) br = 1 else br = 0
    # c1 = d1

    # d0 = a0 - b0
    # d0 = d0 - br
    # c0 = d0

    local cc, br, d3, d2, d1, d0;

    br := var.fresh_t("br_", TInt); # borrow
    d3 := var.fresh_t("d_", T_UInt(blen)); 
    d2 := var.fresh_t("d_", T_UInt(blen)); 
    d1 := var.fresh_t("d_", T_UInt(blen)); 
    d0 := var.fresh_t("d_", T_UInt(blen)); 

    cc := chain(
        comment("MPSubQQQ "::StringInt(blen)),
        assign(d3, nth(a, 3) - nth(b, 3)), # b = b - b, expected to be wrapped around
        assign(br, tcast(TInt, lt(nth(a, 3), nth(b, 3)))), # b = b < b ? 1 : 0
        assign(nth(c, 3), d3), # b = b
        
        assign(d2, nth(a, 2) - nth(b, 2)), # b = b - b
        assign(d2, d2 - br), # b = b - b
        # b = b < b or (b == b and b == 1) ? 1 : 0
        assign(br, tcast(TInt, logic_or(lt(nth(a, 2), nth(b, 2)), logic_and(eq(nth(a, 2), nth(b, 2)), eq(br, 1))))),
        assign(nth(c, 2), d2), # b = b

        assign(d1, nth(a, 1) - nth(b, 1)), # b = b - b
        assign(d1, d1 - br), # b = b - b
        # b = b < b or (b == b and b == 1) ? 1 : 0
        assign(br, tcast(TInt, logic_or(lt(nth(a, 1), nth(b, 1)), logic_and(eq(nth(a, 1), nth(b, 1)), eq(br, 1))))),
        assign(nth(c, 1), d1), # b = b
        
        assign(d0, nth(a, 0) - nth(b, 0)), # b = b - b
        assign(d0, d0 - br), # b = b - b
        # b = b < b or (b == b and b == 1) ? 1 : 0
        assign(nth(c, 0), d0) # b = b
    );

    return cc;

end;

# |mul(c_4b, a_{b+1}, b_{b+1})|_4b
# |cc|_2b
# consumes: a[0], a[1], b[0], b[1]
# produces: c[0], c[1], c[2], c[3]
# base case of Karatsuba algorithm
# a & b = b + b, thus a[0] & b[0] in {0, 1}
# [can be broken down]
MPMulQDD_Base := function(c, a, b, blen, opts)

    local cc, in0, r1, t1, t2, t3, s1, s2, s0, m1, m2, k0, k1, k2, k3, k4, k5;

    in0 := var.fresh_t("in_", TInt);
    
    r1 := var.fresh_t("r_", TArray(T_UInt(blen), 2)); 
    t1 := var.fresh_t("t_", TArray(T_UInt(blen), 2)); 
    t2 := var.fresh_t("t_", TArray(T_UInt(blen), 2)); 
    t3 := var.fresh_t("t_", TArray(T_UInt(blen), 2)); 
    
    s1 := var.fresh_t("s_", TArray(T_UInt(blen), 4)); 
    s2 := var.fresh_t("s_", TArray(T_UInt(blen), 4)); 

    s0 := var.fresh_t("s_", T_UInt(blen*2)); # sum/prod

    m1 := var.fresh_t("p_", T_UInt(blen)); # sum
    m2 := var.fresh_t("p_", T_UInt(blen)); # sum

    # debug
    k0 := var.fresh_t("k_", T_UInt(blen*2)); 
    k1 := var.fresh_t("k_", T_UInt(blen*2)); 
    k2 := var.fresh_t("k_", T_UInt(blen*2)); 
    k3 := var.fresh_t("k_", T_UInt(blen*2)); 
    k4 := var.fresh_t("k_", T_UInt(blen*2)); 
    k5 := var.fresh_t("k_", TReal); 

    cc := chain(
        comment("Begin of MPMulQDD_Base "::StringInt(blen)),
        
        # assign(k0, bin_or(
        #                 bin_shl(tcast(T_UInt(blen*2), nth(a, 0)), blen), 
        #                 nth(a, 1)
        #                 )),
        # call(var("apprint"), var("\"MPMulQDD_Base input a: \""), k0),
        # assign(k1, bin_or(
        #                 bin_shl(tcast(T_UInt(blen*2), nth(b, 0)), blen), 
        #                 nth(b, 1)
        #                 )),
        # call(var("apprint"), var("\"MPMulQDD_Base input b: \""), k1),
        
        # assign(in0, cond(logic_or(eq(nth(a, 0), 0), eq(nth(b, 0), 0)), 0, 1)), # int = 0/1 * 0/1
        assign(in0, tcast(TInt, logic_and(nth(a, 0), nth(b, 0)))), # int = 0/1 * 0/1
        assign(s0, nth(a, 1) * nth(b, 1)), # 2b = b * b
        assign(nth(r1, 0), bin_shr(s0, blen)), # b = 2b >> b
        assign(nth(r1, 1), tcast(T_UInt(blen), s0)), # b = (b) 2b
        assign(m1, nth(a, 0) + nth(a, 1)), # b = 0/1 + b, guaranteed no overflow (e.g., 1111 + 1111 = 1 1110)
        assign(m2, nth(b, 0) + nth(b, 1)), # b = 0/1 + b, guaranteed no overflow (e.g., 1111 + 1111 = 1 1110)
        assign(s0, m1 * m2), # 2b = b * b
        assign(nth(t1, 0), bin_shr(s0, blen)), # b = 2b >> b
        assign(nth(t1, 1), tcast(T_UInt(blen), s0)), # b = (b) 2b
        MPSubDDD(t2, t1, r1, blen, opts), # 2b = 2b - 2b
        MPSubDDI(t3, t2, in0, blen, opts), # 2b = 2b - 0/1
        assign(nth(s1, 0), 0), # b = 0
        assign(nth(s1, 1), in0), # b = 0/1
        assign(nth(s1, 2), nth(r1, 0)), # b = b
        assign(nth(s1, 3), nth(r1, 1)), # b = b
        assign(nth(s2, 0), 0), # b = 0
        assign(nth(s2, 1), nth(t3, 0)), # b = b
        assign(nth(s2, 2), nth(t3, 1)), # b = b
        assign(nth(s2, 3), 0), # b = 0
        MPAddQQQ(c, s1, s2, blen, opts), # assign(c, s1 + s2) # 4b = 4b + 4b

        # assign(k5, bin_or(
        #                 bin_shl(tcast(TReal, nth(c, 0)), blen * 3), 
        #                 bin_shl(tcast(TReal, nth(c, 1)), blen * 2), 
        #                 bin_shl(tcast(TReal, nth(c, 2)), blen), 
        #                 nth(c, 3)
        #                 )), 
        # call(var("apprint"), var("\"MPMulQDD_Base output c: \""), k5),


        comment("End of MPMulQDD_Base "::StringInt(blen))

    );

    return cc;

end;

# |mul(c_4b, a_2b, b_2b)|_4b
# |cc|_2b
# consumes: a[0], a[1], b[0], b[1]
# produces: c[0], c[1], c[2], c[3]
# implemented using Karatsuba algorithm
MPMulQDD_Karatsuba_uo := function(c, a, b, blen, opts)

    local cc, r0, r1, r2, r3, r4, r5, t1, t2, t3, t4, 
    t5, t6, s1, s2, s0, testq, sign1, sign2, 
    abs1, abs2, p1, p2, a0, a1, b0, b1;

    r0 := var.fresh_t("r0_", TArray(T_UInt(blen), 2)); 
    r1 := var.fresh_t("r1_", TArray(T_UInt(blen), 2)); 
    r2 := var.fresh_t("r2_", TArray(T_UInt(blen), 2)); 
    r3 := var.fresh_t("r3_", TArray(T_UInt(blen), 2)); 
    
    t1 := var.fresh_t("t1_", TArray(T_UInt(blen), 4)); 
    t2 := var.fresh_t("t2_", TArray(T_UInt(blen), 4)); 
    t3 := var.fresh_t("t3_", TArray(T_UInt(blen), 4)); 
    
    s1 := var.fresh_t("s1_", TArray(T_UInt(blen), 4)); 
    s2 := var.fresh_t("s2_", TArray(T_UInt(blen), 4)); 

    s0 := var.fresh_t("s0_", T_UInt(blen*2)); # sum/prod

    # for optimized karatsuba
    sign1 := var.fresh_t("sign1_", TInt);
    sign2 := var.fresh_t("sign2_", TInt);
    
    abs1 := var.fresh_t("abs1_", T_UInt(blen)); 
    abs2 := var.fresh_t("abs2_", T_UInt(blen)); 
    
    p1 := var.fresh_t("p1_", T_UInt(blen)); 
    p2 := var.fresh_t("p2_", T_UInt(blen)); 
    
    a0 := var.fresh_t("a0_", T_UInt(blen)); 
    a1 := var.fresh_t("a1_", T_UInt(blen)); 
    b0 := var.fresh_t("b0_", T_UInt(blen)); 
    b1 := var.fresh_t("b1_", T_UInt(blen)); 
    
    r4 := var.fresh_t("r4_", TArray(T_UInt(blen), 2)); 
    r5 := var.fresh_t("r5_", TArray(T_UInt(blen), 2)); 

    t4 := var.fresh_t("t4_", TArray(T_UInt(blen), 4)); 
    t5 := var.fresh_t("t5_", TArray(T_UInt(blen), 4)); 
    t6 := var.fresh_t("t6_", TArray(T_UInt(blen), 4)); 

    testq := var.fresh_t("k_", T_UInt(blen*4)); 

    cc := chain(
        comment("Begin of MPMulQDD_Karatsuba_uo"),
        # load inputs just once
        assign(a0, nth(a, 0)),
        assign(a1, nth(a, 1)),
        assign(b0, nth(b, 0)),
        assign(b1, nth(b, 1)),

        assign(s0, a0 * b0), # 2b = b * b
        assign(nth(r0, 0), bin_shr(s0, blen)), # b = 2b >> b
        assign(nth(r0, 1), tcast(T_UInt(blen), s0)), # b = (b) 2b
        assign(s0, a1 * b1), # 2b = b * b
        assign(nth(r1, 0), bin_shr(s0, blen)), # b = 2b >> b
        assign(nth(r1, 1), tcast(T_UInt(blen), s0)), # b = (b) 2b
        assign(s0, a0 + a1), # 2b = b + b
        assign(nth(r2, 0), bin_shr(s0, blen)), # b = 2b >> b
        assign(nth(r2, 1), tcast(T_UInt(blen), s0)), # b = (b) 2b
        assign(s0, b0 + b1), # 2b = b + b
        assign(nth(r3, 0), bin_shr(s0, blen)), # b = 2b >> b
        assign(nth(r3, 1), tcast(T_UInt(blen), s0)), # b = (b) 2b
        
        # normal breakdown to obtain a1b0 + a0b1
        # seems to be slightly faster than opt. breakdown for 128b
        # z1 = (a0 + a1) * (b0 + b1)
        # MPMulQDD_Base(t1, r2, r3, blen, opts),  # 4b = 2b({b+1}) * 2b({b+1})
        # # t2 = z1 - a1b1
        # MPSubQQD(t2, t1, r1, blen, opts), # 4b = 4b - 2b
        # # t3 = z1 - a0b0 = (a0b1 + a1b0)
        # MPSubQQD(t3, t2, r0, blen, opts), # 4b = 4b - 2b
        
        comment("Begin of breakdown in MPMulQDD"),
        # optimized breakdown to obtain a1b0 + a0b1
        # z0 = r1
        # z2 = r0
        # want: z1 = (a1 - a0) * (b0 - b1) + z2 + z0 # a1b0 - a1b1 - a0b0 + a0b1 + a0b0 + a1b1 = a1b0 + a0b1
        # record the sign: sign1 = a1 > a0, sign2 = b0 > b1
        assign(sign1, gt(a1, a0)),
        assign(sign2, gt(b0, b1)),
        # evaluate sign here

        # abs1 = sign1 ? a1 - a0 : a0 - a1
        assign(p1, a1 - a0), # b = b - b
        assign(p2, a0 - a1), # b = b - b
        assign(abs1, cond(sign1, p1, p2)), # b = cond : b ? b
        # abs2 = sign2 ? b0 - b1 : b1 - b0
        assign(p1, b1 - b0), # b = b - b
        assign(p2, b0 - b1), # b = b - b
        assign(abs2, cond(sign2, p2, p1)), # b = cond : b ? b
        # r4 = abs1 * abs2 
        # r4 is 2b, need to convert to nth types so that following code can consume it
        assign(s0, abs1 * abs2), # 2b = b * b
        assign(nth(r4, 0), bin_shr(s0, blen)), # b = 2b >> b
        assign(nth(r4, 1), tcast(T_UInt(blen), s0)), # b = (b) 2b
        
        # t1 = z2 + z0 # 4b = 2b + 2b
        MPAddQDD(t1, r0, r1, blen, opts),
        
        # t3 = sign1 = sign2 ? t1 + r4 : t1 - r4 = a1b0 + a0b1
        # t4 = t1 + r4 # 4b = 4b + 2b
        assign(nth(t6, 0), 0),
        assign(nth(t6, 1), 0),
        assign(nth(t6, 2), nth(r4, 0)),
        assign(nth(t6, 3), nth(r4, 1)),
        MPAddQQQ(t4, t1, t6, blen, opts),
        
        # t5 = t1 - r4 # 4b = 4b - 2b
        MPSubQQD(t5, t1, r4, blen, opts),
        # manually assign 4b = 4b
        assign(nth(t3, 0), cond(eq(sign1, sign2), nth(t4, 0), nth(t5, 0))),
        assign(nth(t3, 1), cond(eq(sign1, sign2), nth(t4, 1), nth(t5, 1))),
        assign(nth(t3, 2), cond(eq(sign1, sign2), nth(t4, 2), nth(t5, 2))),
        assign(nth(t3, 3), cond(eq(sign1, sign2), nth(t4, 3), nth(t5, 3))),
        comment("End of breakdown in MPMulQDD"),

        # optimize here
        # shift a0b0 << b^2 + a1b1
        assign(nth(s1, 0), nth(r0, 0)), # b = b
        assign(nth(s1, 1), nth(r0, 1)), # b = b
        assign(nth(s1, 2), nth(r1, 0)), # b = b
        assign(nth(s1, 3), nth(r1, 1)), # b = b
        # shift (a0b1 + a1b0) << b
        assign(nth(s2, 0), nth(t3, 1)), # b = b
        assign(nth(s2, 1), nth(t3, 2)), # b = b
        assign(nth(s2, 2), nth(t3, 3)), # b = b
        assign(nth(s2, 3), 0), # b = 0
        # final: a0b0 << b^2 + (a0b1 + a1b0) << b + a1b1
        MPAddQQQ(c, s1, s2, blen, opts), # 4b = 4b + 4b
        # call(var("apprint"), var("\"MPMulQDD[0]: \""), nth(c, 0)),
        # call(var("apprint"), var("\"MPMulQDD[1]: \""), nth(c, 1)),
        # call(var("apprint"), var("\"MPMulQDD[2]: \""), nth(c, 2)),
        # call(var("apprint"), var("\"MPMulQDD[3]: \""), nth(c, 3)),
        comment("End of MPMulQDD_Karatsuba_uo")
    );

    return cc;

end;

# consumes: a[0], a[1], b[0], b[1]
# produces: c[0], c[1], c[2], c[3]
# implemented using Karatsuba algorithm
# aggressively opt. based on MPMulQDD
MPMulQDD_Karatsuba := function(c, a, b, blen, opts)

    local cc, r0, r1, r4, t1, t3, t4, 
    t5, t6, s1, s2, s0, sign1, sign2, in0,
    abs1, abs2, p1, p2, a0, a1, b0, b1;

    r0 := var.fresh_t("r0_", TArray(T_UInt(blen), 2)); 
    r1 := var.fresh_t("r1_", TArray(T_UInt(blen), 2));
    r4 := var.fresh_t("r4_", TArray(T_UInt(blen), 2)); 
    
    t1 := var.fresh_t("t1_", TArray(T_UInt(blen), 4)); 
    t3 := var.fresh_t("t3_", TArray(T_UInt(blen), 4)); 
    t4 := var.fresh_t("t4_", TArray(T_UInt(blen), 4)); 
    t5 := var.fresh_t("t5_", TArray(T_UInt(blen), 4)); 
    t6 := var.fresh_t("t6_", TArray(T_UInt(blen), 4)); 
    s1 := var.fresh_t("s1_", TArray(T_UInt(blen), 4)); 
    s2 := var.fresh_t("s2_", TArray(T_UInt(blen), 4)); 

    s0 := var.fresh_t("s0_", T_UInt(blen*2)); # sum/prod

    sign1 := var.fresh_t("sign1_", TInt);
    sign2 := var.fresh_t("sign2_", TInt);
    in0 := var.fresh_t("in_", TInt);
    
    abs1 := var.fresh_t("abs1_", T_UInt(blen)); 
    abs2 := var.fresh_t("abs2_", T_UInt(blen)); 
    p1 := var.fresh_t("p1_", T_UInt(blen)); 
    p2 := var.fresh_t("p2_", T_UInt(blen)); 
    a0 := var.fresh_t("a0_", T_UInt(blen)); 
    a1 := var.fresh_t("a1_", T_UInt(blen)); 
    b0 := var.fresh_t("b0_", T_UInt(blen)); 
    b1 := var.fresh_t("b1_", T_UInt(blen)); 
    
    cc := chain(
        comment("Begin of MPMulQDD_Karatsuba"),
        # load inputs just once
        assign(a0, nth(a, 0)),
        assign(a1, nth(a, 1)),
        assign(b0, nth(b, 0)),
        assign(b1, nth(b, 1)),

        assign(s0, a0 * b0), # 2b = b * b
        assign(nth(r0, 0), bin_shr(s0, blen)), # b = 2b >> b
        assign(nth(r0, 1), tcast(T_UInt(blen), s0)), # b = (b) 2b
        assign(s0, a1 * b1), # 2b = b * b
        assign(nth(r1, 0), bin_shr(s0, blen)), # b = 2b >> b
        assign(nth(r1, 1), tcast(T_UInt(blen), s0)), # b = (b) 2b
        
        # to obtain a1b0 + a0b1
        # z0 = r1
        # z2 = r0
        # want: z1 = (a1 - a0) * (b0 - b1) + z2 + z0 # a1b0 - a1b1 - a0b0 + a0b1 + a0b0 + a1b1 = a1b0 + a0b1
        # record the sign: sign1 = a1 > a0, sign2 = b0 > b1
        assign(sign1, tcast(TInt, gt(a1, a0))),
        assign(sign2, tcast(TInt, gt(b0, b1))),
        assign(in0, tcast(TInt, eq(sign1, sign2))),
        # abs1 = sign1 ? a1 - a0 : a0 - a1
        assign(p1, a1 - a0), # b = b - b
        assign(p2, a0 - a1), # b = b - b
        assign(abs1, cond(sign1, p1, p2)), # b = cond : b ? b
        # abs2 = sign2 ? b0 - b1 : b1 - b0
        assign(p1, b1 - b0), # b = b - b
        assign(p2, b0 - b1), # b = b - b
        assign(abs2, cond(sign2, p2, p1)), # b = cond : b ? b
        # r4 = abs1 * abs2 
        # r4 is 2b, need to convert to nth types so that following code can consume it
        assign(s0, abs1 * abs2), # 2b = b * b
        assign(nth(r4, 0), bin_shr(s0, blen)), # b = 2b >> b
        assign(nth(r4, 1), tcast(T_UInt(blen), s0)), # b = (b) 2b
        
        # t1 = z2 + z0 # 4b = 2b + 2b
        MPAddQDD(t1, r0, r1, blen, opts),
        
        # t3 = sign1 = sign2 ? t1 + r4 : t1 - r4 = a1b0 + a0b1
        # t4 = t1 + r4 # 4b = 4b + 2b
        assign(nth(t6, 0), 0), # should be reduced by strengthreduction
        assign(nth(t6, 1), 0),
        assign(nth(t6, 2), nth(r4, 0)),
        assign(nth(t6, 3), nth(r4, 1)),
        MPAddQQQ(t4, t1, t6, blen, opts),
        # t5 = t1 - r4 # 4b = 4b - 2b
        MPSubQQD(t5, t1, r4, blen, opts),
        # manually assign 4b = 4b
        assign(nth(t3, 0), cond(in0, nth(t4, 0), nth(t5, 0))),
        assign(nth(t3, 1), cond(in0, nth(t4, 1), nth(t5, 1))),
        assign(nth(t3, 2), cond(in0, nth(t4, 2), nth(t5, 2))),
        assign(nth(t3, 3), cond(in0, nth(t4, 3), nth(t5, 3))),

        # shift a0b0 << b^2 + a1b1
        assign(nth(s1, 0), nth(r0, 0)), # b = b
        assign(nth(s1, 1), nth(r0, 1)), # b = b
        assign(nth(s1, 2), nth(r1, 0)), # b = b
        assign(nth(s1, 3), nth(r1, 1)), # b = b
        # shift (a0b1 + a1b0) << b
        assign(nth(s2, 0), nth(t3, 1)), # b = b
        assign(nth(s2, 1), nth(t3, 2)), # b = b
        assign(nth(s2, 2), nth(t3, 3)), # b = b
        assign(nth(s2, 3), 0), # b = 0
        # final: a0b0 << b^2 + (a0b1 + a1b0) << b + a1b1
        MPAddQQQ(c, s1, s2, blen, opts), # 4b = 4b + 4b
        comment("End of MPMulQDD_Karatsuba")
    );

    return cc;

end;

# consumes: a[0], a[1], b[0], b[1]
# produces: c[0], c[1], c[2], c[3]
# implemented using the schoolbook algorithm
# DOES NOT WORK FOR l2 recursion
# should only use this for the first recursion or just l1 recursion
# works for partial bit-width
MPMulQDD_Schoolbook_P := function(c, a, b, blen, opts)

    local cc, a0, a1, b0, b1, t0, t1,
    albl, albh, ahbl, ahbh, cx, cx2, chx;

    a0 := var.fresh_t("a0_", T_UInt(blen)); 
    a1 := var.fresh_t("a1_", T_UInt(blen)); 
    b0 := var.fresh_t("b0_", T_UInt(blen)); 
    b1 := var.fresh_t("b1_", T_UInt(blen)); 
    t0 := var.fresh_t("t0_", T_UInt(blen)); 
    t1 := var.fresh_t("t1_", T_UInt(blen)); 

    albl := var.fresh_t("albl_", T_UInt(blen*2));
    albh := var.fresh_t("albh_", T_UInt(blen*2));
    ahbl := var.fresh_t("ahbl_", T_UInt(blen*2));
    ahbh := var.fresh_t("ahbh_", T_UInt(blen*2));
    cx := var.fresh_t("cx_", T_UInt(blen*2));
    cx2 := var.fresh_t("cx2_", T_UInt(blen*2));
    chx := var.fresh_t("chx_", T_UInt(blen*2));

    cc := chain(
        comment("Begin of MPMulQDD_Schoolbook_Partial"),
        # load inputs just once
        assign(a0, nth(a, 0)),
        assign(a1, nth(a, 1)),
        assign(b0, nth(b, 0)),
        assign(b1, nth(b, 1)),

        assign(albl, a1 * b1), # 2b = b * b
        assign(albh, a1 * b0), # 2b = b * b
        assign(ahbl, a0 * b1), # 2b = b * b
        assign(ahbh, a0 * b0), # 2b = b * b
        
        assign(cx, albh + ahbl), # 2b = 2b + 2b

        assign(t0, bin_shr(albl, blen)), # b = 2b >> b
        assign(cx2, cx + t0), # 2b = 2b + b
        assign(t1, bin_shr(cx2, blen)), # b = 2b >> b
        assign(chx, ahbh + t1), # 2b = 2b + b
        assign(nth(c, 0), bin_shr(chx, blen)), # b = 2b >> b
        assign(nth(c, 1), tcast(T_UInt(blen), chx)), # b = (b) 2b
        assign(nth(c, 2), tcast(T_UInt(blen), cx2)), # b = (b) 2b
        assign(nth(c, 3), tcast(T_UInt(blen), albl)), # b = (b) 2b
        comment("End of MPMulQDD_Schoolbook_Partial")
    );

    return cc;

end;

# consumes: a[0], a[1], b[0], b[1]
# produces: c[0], c[1], c[2], c[3]
# implemented using the schoolbook algorithm
# works for full bit-width
MPMulQDD_Schoolbook_F := function(c, a, b, blen, opts)

    local cc, a0, a1, b0, b1, albl, albh, ahbl, ahbh, 
    r0, r1, r2, r3, s0, s1, s2;

    a0 := var.fresh_t("a0_", T_UInt(blen)); 
    a1 := var.fresh_t("a1_", T_UInt(blen)); 
    b0 := var.fresh_t("b0_", T_UInt(blen)); 
    b1 := var.fresh_t("b1_", T_UInt(blen)); 

    albl := var.fresh_t("albl_", T_UInt(blen*2));
    albh := var.fresh_t("albh_", T_UInt(blen*2));
    ahbl := var.fresh_t("ahbl_", T_UInt(blen*2));
    ahbh := var.fresh_t("ahbh_", T_UInt(blen*2));

    r0 := var.fresh_t("r0_", TArray(T_UInt(blen), 2));
    r1 := var.fresh_t("r1_", TArray(T_UInt(blen), 2));
    r2 := var.fresh_t("r2_", TArray(T_UInt(blen), 2)); 
    r3 := var.fresh_t("r3_", TArray(T_UInt(blen), 2));

    s0 := var.fresh_t("s0_", TArray(T_UInt(blen), 4));
    s1 := var.fresh_t("s1_", TArray(T_UInt(blen), 4));
    s2 := var.fresh_t("s2_", TArray(T_UInt(blen), 4));

    cc := chain(
        comment("Begin of MPMulQDD_Schoolbook_Full"),
        # load inputs just once
        assign(a0, nth(a, 0)),
        assign(a1, nth(a, 1)),
        assign(b0, nth(b, 0)),
        assign(b1, nth(b, 1)),

        # need to break it down for 4b arithmetic
        assign(albl, a1 * b1), # 2b = b * b
        assign(nth(r2, 0), bin_shr(albl, blen)), # b = 2b >> b
        assign(nth(r2, 1), tcast(T_UInt(blen), albl)), # b = (b) 2b
        assign(ahbh, a0 * b0), # 2b = b * b
        assign(nth(r3, 0), bin_shr(ahbh, blen)), # b = 2b >> b
        assign(nth(r3, 1), tcast(T_UInt(blen), ahbh)), # b = (b) 2b
        assign(ahbl, a0 * b1), # 2b = b * b
        assign(nth(r0, 0), bin_shr(ahbl, blen)), # b = 2b >> b
        assign(nth(r0, 1), tcast(T_UInt(blen), ahbl)), # b = (b) 2b
        assign(albh, a1 * b0), # 2b = b * b
        assign(nth(r1, 0), bin_shr(albh, blen)), # b = 2b >> b
        assign(nth(r1, 1), tcast(T_UInt(blen), albh)), # b = (b) 2b
        # assign(cx, albh + ahbl), # 2b = 2b + 2b
        # 4b({2b+1}) = 2b + 2b
        MPAddQDD(s0, r0, r1, blen, opts),

        # glue ahbh and albl
        assign(nth(s1, 0), nth(r3, 0)), # b = b
        assign(nth(s1, 1), nth(r3, 1)), # b = b
        assign(nth(s1, 2), nth(r2, 0)), # b = b
        assign(nth(s1, 3), nth(r2, 1)), # b = b
        # shift (albh + ahbl)
        assign(nth(s2, 0), nth(s0, 1)), # b = b
        assign(nth(s2, 1), nth(s0, 2)), # b = b
        assign(nth(s2, 2), nth(s0, 3)), # b = b
        assign(nth(s2, 3), 0), # b = 0

        MPAddQQQ(c, s1, s2, blen, opts), # 4b = 4b + 4b
        
        comment("End of MPMulQDD_Schoolbook_Full")
    );

    return cc;

end;

# special mod for add
# Optimization Rule 1
# works for full bit-width: c = a + b where c can be (2b + 1)
MPModDQ_Add := function(cm, c, blen, opts)
    
    # c = a + b
    # if c > mod, cm = c - mod
    # else, cm = c
        
    local cc, t, r, in0, in1;

    t := var.fresh_t("t_", TArray(T_UInt(blen), 4)); 
    r := var.fresh_t("r_", TArray(T_UInt(blen), 2));
    in0 := var.fresh_t("in_", TInt);
    in1 := var.fresh_t("in_", TInt); 

    # fix X & Y datatype
    if IsBound(cm.computeType) then cm.t := cm.computeType(); fi;

    cc := chain(
        comment("Begin of MPModDQ_Add"),
        
        # in0 = c > m
        MPExtractLow(r, c, blen, opts), 
        MPLessThanD(in1, opts.modulus, r, blen, opts), # mod < r
        assign(in0, tcast(TInt, logic_or(lt(0, nth(c, 1)), logic_and(eq(nth(c, 1), 0), in1)))), # in0 = 1 if c > mod
        
        MPSubQQD(t, c, opts.modulus, blen, opts), # t = c - m
        
        assign(nth(cm, 0), cond(in0, nth(t, 2), nth(c, 2))), # b = cond : b ? b
        assign(nth(cm, 1), cond(in0, nth(t, 3), nth(c, 3))), # b = cond : b ? b
        comment("End of MPModDQ_Add")
    );

    return cc;

end;

# special mod for add
# Optimization Rule 1
# works for partial bit-width: c = a + b where c <= 2*blen
MPModDD := function(cm, c, blen, opts)
    
    # c <= 2*blen
    # if c > mod, cm = c - mod
    # else, cm = c

    local cc, t, in0;

    t := var.fresh_t("t_", TArray(T_UInt(blen), 2)); 
    in0 := var.fresh_t("in_", TInt); 

    # fix X & Y datatype
    if IsBound(cm.computeType) then cm.t := cm.computeType(); fi;

    cc := chain(
        comment("Begin of MPModDD"),
        
        # determine if c > m
        MPLessThanD(in0, opts.modulus, c, blen, opts), # mod < r
        
        MPSubDDD(t, c, opts.modulus, blen, opts), # t = c - m
        
        assign(nth(cm, 0), cond(in0, nth(t, 0), nth(c, 0))), # b = cond : b ? b
        assign(nth(cm, 1), cond(in0, nth(t, 1), nth(c, 1))), # b = cond : b ? b
        comment("End of MPModDD")
    );

    return cc;

end;

# mod(cm_2b, c_4b)
# consumes: c[0], c[1], c[2], c[3]
# produces: cm[0], cm[1]
# native implementation
MPModDQ_Native := function(cm, c, blen, opts)

    local cc, r, m, t;

    r := var.fresh_t("r_", T_UInt(blen*4)); 
    m := var.fresh_t("m_", T_UInt(blen*2)); 
    t := var.fresh_t("t_", T_UInt(blen*2)); 
    
    # r0 := var.fresh_t("r_", TArray(T_UInt(blen), 2)); 

    # Debug(true); Error();

    # fix X & Y datatype
    if IsBound(cm.computeType) then cm.t := cm.computeType(); fi;

    cc := chain(
        comment("MPModDQ_Native"),
        assign(r, bin_or(
                        bin_shl(tcast(T_UInt(blen*4), nth(c, 0)), blen * 3), 
                        bin_shl(tcast(T_UInt(blen*4), nth(c, 1)), blen * 2), 
                        bin_shl(tcast(T_UInt(blen*4), nth(c, 2)), blen), 
                        nth(c, 3)
                        )), 
        assign(m, bin_or(
                        bin_shl(tcast(T_UInt(blen*2), nth(opts.modulus, 0)), blen), 
                        nth(opts.modulus, 1)
                        )),
        assign(t, imod(r, m)),
        assign(nth(cm, 0), bin_shr(t, blen)), # b = 2b >> b
        assign(nth(cm, 1), tcast(T_UInt(blen), t)) # b = (b) 2b
    );



    return cc;

end;

# mod(cm_2b, c_4b)
# consumes: c[0], c[1], c[2], c[3]
# produces: cm[0], cm[1]
# implemented using Barrett reduction
# based on mpmod in mp_int.h
# built for recursion
MPModDQ := function(cm, c, blen, opts)

    # this is based on the assumption that mbits is insize*2-4
    # t = c,
    # c >>= (MBITS-2);
    # c *= mu64; // (c >> bits-2) * mu
    # c >>= (MBITS + 5); // (c >> 2*bits+3) * mu
    # t -= c * mod64;
    # cm = t > mod64 ? t - mod64 : t;

    local cc, t, t1, t2, t3, t4, r, r1, r2, r3, r4, r5, 
    p1, p2, p3, p4, p5, in0, in1, in2, mask;
    
    t := var.fresh_t("t_", TArray(T_UInt(blen), 4)); 
    t1 := var.fresh_t("t_", TArray(T_UInt(blen), 4));
    t2 := var.fresh_t("t_", TArray(T_UInt(blen), 4));
    t3 := var.fresh_t("t_", TArray(T_UInt(blen), 4));
    t4 := var.fresh_t("t_", TArray(T_UInt(blen), 4));
    
    r := var.fresh_t("r_", TArray(T_UInt(blen), 2));
    r1 := var.fresh_t("r_", TArray(T_UInt(blen), 2));
    r2 := var.fresh_t("r_", TArray(T_UInt(blen), 2));
    r3 := var.fresh_t("r_", TArray(T_UInt(blen), 2));
    r4 := var.fresh_t("r_", TArray(T_UInt(blen), 2));
    r5 := var.fresh_t("r_", TArray(T_UInt(blen), 2));

    p1 := var.fresh_t("p_", TArray(T_UInt(blen), 2));
    p2 := var.fresh_t("p_", TArray(T_UInt(blen), 2));
    p3 := var.fresh_t("p_", TArray(T_UInt(blen), 2));
    p4 := var.fresh_t("p_", TArray(T_UInt(blen), 2));
    p5 := var.fresh_t("p_", TArray(T_UInt(blen), 2));
    
    mask := var.fresh_t("m_", T_UInt(blen)); 
    
    in0 := var.fresh_t("in_", TInt); 
    in1 := var.fresh_t("in_", TInt); 
    in2 := var.fresh_t("in_", TInt);

    # debug
    # k0 := var.fresh_t("k_", T_UInt(blen*2)); 
    # testq := var.fresh_t("k_", T_UInt(blen*4)); 

    # fix X & Y datatype
    if IsBound(cm.computeType) then cm.t := cm.computeType(); fi;

    cc := chain(
        comment("Begin of MPModDQ"),
        # t = c
        assign(nth(t, 0), nth(c, 0)), # b = b 
        assign(nth(t, 1), nth(c, 1)), # b = b 
        assign(nth(t, 2), nth(c, 2)), # b = b 
        assign(nth(t, 3), nth(c, 3)), # b = b 

        assign(nth(p1, 0), nth(c, 2)), # b = b 
        assign(nth(p1, 1), nth(c, 3)), # b = b 

        # 4b >>= MBITS - 2 -> will be 2b for OpenFHE data
        # 3 part shift
        MPShiftRight3(r, t, opts.mbits - 2, blen, opts), 
        
        # r * mu
        # 4b = 2b * 2b
        assign(nth(r2, 0), nth(opts.barrettMu, 0)), # b = b
        assign(nth(r2, 1), nth(opts.barrettMu, 1)), # b = b
        When(opts.useMacro,
            When(opts.useArray,
                fmulqdd(t2, r, r2),
                fmulqdd_l1(nth(t2, 0), nth(t2, 1), nth(t2, 2), nth(t2, 3), nth(r, 0), nth(r, 1), nth(r2, 0), nth(r2, 1))
            ),
            opts.mulqdd(t2, r, r2, blen, opts)
            # MPMulQDD_Karatsuba(t2, r, r2, blen, opts)
            # MPMulQDD_Schoolbook(t2, r, r2, blen, opts)
        ),
        
        # 4b >>= MBITS + 5 -> 2b
        # 2 part shift
        When((opts.insize - opts.mbits) <= 4, 
            MPShiftRight2(r3, t2, opts.mbits + 5, blen, opts), 
            MPShiftRight3(r3, t2, opts.mbits + 5, blen, opts)
        ),

        # r * mod
        # 4b = 2b * 2b
        assign(nth(r4, 0), nth(opts.modulus, 0)), # b = b
        assign(nth(r4, 1), nth(opts.modulus, 1)), # b = b
        When(opts.useMacro,
            When(opts.useArray,
                fmulqdd(t1, r3, r4),
                fmulqdd_l1(nth(t1, 0), nth(t1, 1), nth(t1, 2), nth(t1, 3), nth(r3, 0), nth(r3, 1), nth(r4, 0), nth(r4, 1))
            ),
            opts.mulqdd(t1, r3, r4, blen, opts)
            # MPMulQDD_Karatsuba(t1, r3, r4, blen, opts)
            # MPMulQDD_Schoolbook(t1, r3, r4, blen, opts)
        ),
        
        # t - r * mod
        # {2b+1} = 4b - 4b, results < modulus*2 (2b + 2b)
        # 0 0/1 t3[2] t3[3]
        # MPSubQQQ(t3, t, t1, blen, opts), # non-opt.
        assign(nth(p2, 0), nth(t1, 2)), # b = b 
        assign(nth(p2, 1), nth(t1, 3)), # b = b 
        MPSubDDD(p3, p1, p2, blen, opts),
        
        # t - r * mod - mod
        # 4b = 4b - 2b
        # 0 0 t4[2] t4[3]
        # MPSubQQD(t4, t3, r4, blen, opts), # non-opt.
        MPSubDDD(p5, p3, r4, blen, opts), # right now only works for MK -> code gen problem
        
        # cm = 4b > 2b ? 2b : 2b;
        # 0 0/1 t3[2] t3[3] > mod[0] mod[1]
        # 3 cases: 
        # 1. 0/1 is 1 
        # 2. t3[2] > mod[0]
        # 3. t3[2] = mod[0] and t[3] > mod[1]
        # assign(in0, logic_or(neq(nth(t3, 1), 0), # b != 0 # non-opt.
        #                     gt(nth(t3, 2), nth(r4, 0)), # b > b
        #                     # b == b and b > b
        #                     logic_and(eq(nth(t3, 2), nth(r4, 0)), gt(nth(t3, 3), nth(r4, 1))))),
        MPLessThanD(in0, p3, r4, blen, opts),

        # assign(nth(cm, 0), cond(in0, nth(t4, 2), nth(t3, 2))), # b = cond : b ? b # non-opt.
        # assign(nth(cm, 1), cond(in0, nth(t4, 3), nth(t3, 3))), # b = cond : b ? b
        assign(nth(cm, 0), cond(in0, nth(p3, 0), nth(p5, 0))), # b = cond : b ? b
        assign(nth(cm, 1), cond(in0, nth(p3, 1), nth(p5, 1))), # b = cond : b ? b

        comment("End of MPModDQ")
    );

    return cc;

end;

# mod(cm_2b, c_4b)
# consumes: c[0], c[1], c[2], c[3]
# produces: cm[0], cm[1]
# implemented using Montgomery reduction
MPREDCDQ := function(cm, c, blen, opts)

    # this is based on the assumption that mbits is a multiple of word size

    local cc, t, t1, t2, t3, t4, r, r1, r2, r3, r4, r5, 
    p1, p2, p3, p4, p5, in0, in1, in2, mask;
    
    t := var.fresh_t("t_", TArray(T_UInt(blen), 4)); 
    t1 := var.fresh_t("t_", TArray(T_UInt(blen), 4));
    t2 := var.fresh_t("t_", TArray(T_UInt(blen), 4));
    t3 := var.fresh_t("t_", TArray(T_UInt(blen), 4));
    t4 := var.fresh_t("t_", TArray(T_UInt(blen), 4));
    
    r := var.fresh_t("r_", TArray(T_UInt(blen), 2));
    r1 := var.fresh_t("r_", TArray(T_UInt(blen), 2));
    r2 := var.fresh_t("r_", TArray(T_UInt(blen), 2));
    r3 := var.fresh_t("r_", TArray(T_UInt(blen), 2));
    r4 := var.fresh_t("r_", TArray(T_UInt(blen), 2));
    r5 := var.fresh_t("r_", TArray(T_UInt(blen), 2));

    p1 := var.fresh_t("p_", TArray(T_UInt(blen), 2));
    p2 := var.fresh_t("p_", TArray(T_UInt(blen), 2));
    p3 := var.fresh_t("p_", TArray(T_UInt(blen), 2));
    p4 := var.fresh_t("p_", TArray(T_UInt(blen), 2));
    p5 := var.fresh_t("p_", TArray(T_UInt(blen), 2));
    
    mask := var.fresh_t("m_", T_UInt(blen)); 
    
    in0 := var.fresh_t("in_", TInt); 
    in1 := var.fresh_t("in_", TInt); 
    in2 := var.fresh_t("in_", TInt);

    # debug
    # k0 := var.fresh_t("k_", T_UInt(blen*2)); 
    # testq := var.fresh_t("k_", T_UInt(blen*4)); 

    # fix X & Y datatype
    if IsBound(cm.computeType) then cm.t := cm.computeType(); fi;

    cc := chain(
        comment("Begin of MPREDCDQ"),

        # p1 = Th
        assign(nth(p1, 0), nth(c, 0)), # b = b 
        assign(nth(p1, 1), nth(c, 1)), # b = b 

        # r = Tl
        assign(nth(r, 0), nth(c, 2)), # b = b 
        assign(nth(r, 1), nth(c, 3)), # b = b 

        # t2 = Tl * mu (n')
        # 4b = 2b * 2b
        assign(nth(r2, 0), nth(opts.barrettMu, 0)), # b = b
        assign(nth(r2, 1), nth(opts.barrettMu, 1)), # b = b
        
        When(opts.useMacro,
            When(opts.useArray,
                fmulqdd(t2, r, r2),
                fmulqdd_l1(nth(t2, 0), nth(t2, 1), nth(t2, 2), nth(t2, 3), nth(r, 0), nth(r, 1), nth(r2, 0), nth(r2, 1))
            ),
            opts.mulqdd(t2, r, r2, blen, opts)
        ),

        # r3 = t2l
        assign(nth(r3, 0), nth(t2, 2)), # b = b 
        assign(nth(r3, 1), nth(t2, 3)), # b = b 
        
        # t2l * mod
        # 4b = 2b * 2b
        assign(nth(r4, 0), nth(opts.modulus, 0)), # b = b
        assign(nth(r4, 1), nth(opts.modulus, 1)), # b = b
        
        
        When(opts.useMacro,
            When(opts.useArray,
                fmulqdd(t1, r3, r4),
                fmulqdd_l1(nth(t1, 0), nth(t1, 1), nth(t1, 2), nth(t1, 3), nth(r3, 0), nth(r3, 1), nth(r4, 0), nth(r4, 1))
            ),
            opts.mulqdd(t1, r3, r4, blen, opts)
        ),
        # future: # mulhi
        # MPMulQDD_Schoolbook_F(t1, r3, r4, blen, opts),
        
        # subhi
        # p2 = t3h
        assign(nth(p2, 0), nth(t1, 0)), # b = b 
        assign(nth(p2, 1), nth(t1, 1)), # b = b 

        # Th - t3h
        MPSubDDD(p3, p1, p2, blen, opts),

        # if Th < t3h, p3 will wrap around (being negative)
        # add modulus to p3
        MPAddDDD(p4, p3, r4, blen, opts),

        # Th < t3h
        MPLessThanD(in0, p1, p2, blen, opts),

        assign(nth(cm, 0), cond(in0, nth(p4, 0), nth(p3, 0))), # b = cond : b ? b
        assign(nth(cm, 1), cond(in0, nth(p4, 1), nth(p3, 1))), # b = cond : b ? b

        comment("End of MPREDCDQ")
    );

    return cc;

end;

# mod(cm_2b, c_4b)
# consumes: c[0], c[1], c[2], c[3]
# produces: cm[0], cm[1]
# implemented using Barrett reduction
# alternative for MPModDQ, based on mpmod in mpmethod.gi
# updated for general mbits
MPModDQ_Alt := function(cm, c, blen, opts)

    # t = c,
    # c >>= (MBITS-2);
    # c *= mu64; // (c >> bits-2) * mu
    # c >>= (MBITS + 5); // (c >> 2*bits+3) * mu
    # t -= c * mod64;
    # cm = t > mod64 ? t - mod64 : t;

    local cc, m, t, t1, t2, t3, t4, r, r2, r3, r4, p1, p2, p3, p4, in0, in1, in2, high, low, mask, e_low, p,
    k0, k1, k2, mod0, mu0, testq, testd;
    
    t := var.fresh_t("t_", TArray(T_UInt(blen), 4)); 
    t1 := var.fresh_t("t_", TArray(T_UInt(blen), 4));
    t2 := var.fresh_t("t_", TArray(T_UInt(blen), 4));
    t3 := var.fresh_t("t_", TArray(T_UInt(blen), 4));
    t4 := var.fresh_t("t_", TArray(T_UInt(blen), 4));
    
    r := var.fresh_t("r_", TArray(T_UInt(blen), 2));
    r2 := var.fresh_t("r_", TArray(T_UInt(blen), 2));
    r3 := var.fresh_t("r_", TArray(T_UInt(blen), 2));
    r4 := var.fresh_t("r_", TArray(T_UInt(blen), 2));

    p1 := var.fresh_t("p_", T_UInt(blen)); 
    p2 := var.fresh_t("p_", T_UInt(blen*2)); 
    p3 := var.fresh_t("p_", T_UInt(blen)); 
    p4 := var.fresh_t("p_", T_UInt(blen)); 
    
    m := var.fresh_t("m_", T_UInt(blen)); 
    
    in0 := var.fresh_t("in_", TInt);
    in1 := var.fresh_t("in_", TInt); 
    in2 := var.fresh_t("in_", TInt);

    high := var.fresh_t("high_", T_UInt(blen*2));
    low := var.fresh_t("low_", T_UInt(blen*2));
    mask := var.fresh_t("mask_", T_UInt(blen*2));
    e_low := var.fresh_t("e_low_", T_UInt(blen*2));
    p := var.fresh_t("p_", T_UInt(blen*2));

    # debug
    k0 := var.fresh_t("k_", T_UInt(blen*2)); 
    k1 := var.fresh_t("k_", T_UInt(blen*4)); 
    k2 := var.fresh_t("k_", T_UInt(blen*2)); 
    mod0 := var.fresh_t("m_", T_UInt(blen*2)); 
    mu0 := var.fresh_t("m_", T_UInt(blen*2)); 
    testq := var.fresh_t("k_", T_UInt(blen*4)); 
    testd := var.fresh_t("k_", T_UInt(blen*2)); 

    # fix X & Y datatype
    if IsBound(cm.computeType) then cm.t := cm.computeType(); fi;

    cc := chain(
        comment("Begin of MPModDQ_Alt"),
        # t = c
        assign(nth(t, 0), nth(c, 0)),
        assign(nth(t, 1), nth(c, 1)),
        assign(nth(t, 2), nth(c, 2)),
        assign(nth(t, 3), nth(c, 3)),
        # 4b >>= MBITS - 2 -> will be 2b for OpenFHE data
        assign(high, bin_or(bin_shl(tcast(T_UInt(blen*2), nth(c, 0)), blen), nth(c, 1))),
        assign(low, bin_or(bin_shl(tcast(T_UInt(blen*2), nth(c, 2)), blen), nth(c, 3))),
        assign(p1, bin_shr(low, opts.mbits - 2)), # 16b >> 10b = 6b
        assign(mask, bin_shl(tcast(T_UInt(blen*2), 1), (opts.mbits - 2)) - 1),
        assign(p2, bin_and(high, mask)),
        assign(p3, bin_shr(high, (opts.mbits - 2))),
        assign(e_low, bin_or(bin_shl(tcast(T_UInt(blen*2), p2), blen * 2 - (opts.mbits - 2)), p1)),
        assign(nth(r, 0), tcast(T_UInt(blen), (bin_shr(e_low, blen)))),
        assign(nth(r, 1), tcast(T_UInt(blen), e_low)),
        # 4b = 2b * 2b
        assign(nth(r2, 0), nth(opts.barrettMu, 0)),
        assign(nth(r2, 1), nth(opts.barrettMu, 1)),
        opts.mulqdd(t2, r, r2, blen, opts),
        # 4b >>= MBITS + 5 -> 2b
        # only works for mbits+5 > 2*blen
        # assign(high, bin_or(bin_shl(tcast(T_UInt(blen*2), nth(t2, 0)), blen), nth(t2, 1))),
        # assign(p, bin_shr(high, (opts.mbits + 5 - (blen * 2)))),
        # assign(nth(r3, 0), tcast(T_UInt(blen), (bin_shr(p, blen)))),
        # assign(nth(r3, 1), tcast(T_UInt(blen), p)),
        # general shift
        assign(high, bin_or(bin_shl(tcast(T_UInt(blen*2), nth(t2, 0)), blen), nth(t2, 1))),
        assign(low, bin_or(bin_shl(tcast(T_UInt(blen*2), nth(t2, 2)), blen), nth(t2, 3))),
        assign(p1, bin_shr(low, opts.mbits + 5)),
        assign(mask, bin_shl(tcast(T_UInt(blen*2), 1), (opts.mbits + 5)) - 1),
        assign(p2, bin_and(high, mask)),
        assign(p3, bin_shr(high, (opts.mbits + 5))),
        assign(e_low, bin_or(bin_shl(tcast(T_UInt(blen*2), p2), blen * 2 - (opts.mbits + 5)), p1)),
        assign(nth(r3, 0), tcast(T_UInt(blen), (bin_shr(e_low, blen)))),
        assign(nth(r3, 1), tcast(T_UInt(blen), e_low)),
        # 4b = 2b * 2b
        assign(nth(r4, 0), nth(opts.modulus, 0)),
        assign(nth(r4, 1), nth(opts.modulus, 1)),
        # call(var("apprint"), var("\"p: \""), p),
        opts.mulqdd(t1, r3, r4, blen, opts),
        # assign(testq, bin_or(
        #                 bin_shl(tcast(T_UInt(blen*4), nth(t1, 0)), blen * 3), 
        #                 bin_shl(tcast(T_UInt(blen*4), nth(t1, 1)), blen * 2), 
        #                 bin_shl(tcast(T_UInt(blen*4), nth(t1, 2)), blen), 
        #                 nth(t1, 3)
        #                 )), 
        # call(var("apprint"), var("\"barrett: \""), testq),
        # {2b+1} = 4b - 4b, results < modulus*2 (2b + 2b)
        # 0 0/1 t3[2] t3[3]
        MPSubQQQ(t3, t, t1, blen, opts), # t - q
        # 4b = 4b - 2b
        # 0 0 t4[2] t4[3]
        MPSubQQD(t4, t3, r4, blen, opts), # t - q - mod
        # cm = 4b > 2b ? 2b : 2b;
        # 0 0/1 t3[2] t3[3] > mod[0] mod[1]
        # 3 cases: 
        # 1. 0/1 is 1 
        # 2. t3[2] > mod[0]
        # 3. t3[2] = mod[0] and t[3] > mod[1]
        assign(in0, tcast(TInt, logic_or(neq(nth(t3, 1), 0), 
                            gt(nth(t3, 2), nth(r4, 0)), 
                            logic_and(eq(nth(t3, 2), nth(r4, 0)), gt(nth(t3, 3), nth(r4, 1)))))),
        assign(nth(cm, 0), cond(in0, nth(t4, 2), nth(t3, 2))),
        assign(nth(cm, 1), cond(in0, nth(t4, 3), nth(t3, 3))),
        
        # debug
        # assign(k0, bin_or(
        #                 bin_shl(tcast(T_UInt(blen*2), nth(cm, 0)), blen), 
        #                 nth(cm, 1)
        #                 )),
        # call(var("apprint"), var("\"Result barrett: \""), k0),
        # assign(k1, bin_or(
        #                 bin_shl(tcast(T_UInt(blen*4), nth(c, 0)), blen * 3), 
        #                 bin_shl(tcast(T_UInt(blen*4), nth(c, 1)), blen * 2), 
        #                 bin_shl(tcast(T_UInt(blen*4), nth(c, 2)), blen), 
        #                 nth(c, 3)
        #                 )), 
        # assign(mod0, bin_or(
        #                 bin_shl(tcast(T_UInt(blen*2), nth(opts.modulus, 0)), blen), 
        #                 nth(opts.modulus, 1)
        #                 )),
        # assign(k2, k1),
        # assign(k1, bin_shr(k1, opts.mbits - 2)), # c >>= (MBITS-2);
        
        # # call(var("mpprintb"), var("\"native barrett: \""), k1),
        # assign(mu0, bin_or(
        #                 bin_shl(tcast(T_UInt(blen*2), nth(opts.barrettMu, 0)), blen), 
        #                 nth(opts.barrettMu, 1)
        #                 )),
        # assign(k1, k1 * mu0),
        
        # assign(k1, bin_shr(k1, opts.mbits + 5)),
        # call(var("apprint"), var("\"native barrett: \""), k1 * mod0),
        # assign(k2, k2 - k1 * mod0),
        # assign(k2, cond(gt(k2, mod0), k2 - mod0, k2)),
        # assign(t2, tcast(T_UInt(blen*2), k2)),
        # # assign(k2, imod(k1, mod0)),
        # call(var("apprint"), var("\"Result native barrett: \""), k2),
        comment("End of MPModDQ_Alt")
    );

    return cc;

end;

# mod(cm_2b, c_4b)
# consumes: c[0], c[1], c[2], c[3]
# produces: cm[0], cm[1]
# implemented using Barrett reduction
# based on mpmod in mp_int.h and mpmethod.gi
MPModDQ_Native_Barrett := function(cm, c, blen, opts)

    # t = c,
    # c >>= (MBITS-2);
    # c *= mu64; // (c >> bits-2) * mu
    # c >>= (MBITS + 5); // (c >> 2*bits+3) * mu
    # t -= c * mod64;
    # cm = t > mod64 ? t - mod64 : t;

    local cc, r, t, mu0, mod0, t1, t2;
        
    r := var.fresh_t("r_", T_UInt(blen*4)); 
    t := var.fresh_t("t_", T_UInt(blen*4)); 
    t1 := var.fresh_t("t_", T_UInt(blen*4)); 
    
    t2 := var.fresh_t("t_", T_UInt(blen*2)); 
    mu0 := var.fresh_t("m_", T_UInt(blen*2)); 
    mod0 := var.fresh_t("m_", T_UInt(blen*2)); 

    # Debug(true);
    # Error();

    # fix X & Y datatype
    if IsBound(cm.computeType) then cm.t := cm.computeType(); fi;

    cc := chain(
        comment("Begin of MPModDQ_Barrett"),
        assign(r, bin_or(
                        bin_shl(tcast(T_UInt(blen*4), nth(c, 0)), blen * 3), 
                        bin_shl(tcast(T_UInt(blen*4), nth(c, 1)), blen * 2), 
                        bin_shl(tcast(T_UInt(blen*4), nth(c, 2)), blen), 
                        nth(c, 3)
                        )), 
        assign(mod0, bin_or(
                        bin_shl(tcast(T_UInt(blen*2), nth(opts.modulus, 0)), blen), 
                        nth(opts.modulus, 1)
                        )),
        # assign(t1, imod(r, mod0)), # debug
        assign(t, r),
        assign(r, bin_shr(r, opts.mbits - 2)), # c >>= (MBITS-2);
        assign(mu0, bin_or(
                        bin_shl(tcast(T_UInt(blen*2), nth(opts.barrettMu, 0)), blen), 
                        nth(opts.barrettMu, 1)
                        )),
        assign(r, r * mu0),
        assign(r, bin_shr(r, opts.mbits + 5)),
        assign(t, t - r * mod0),
        assign(t, cond(gt(t, mod0), t - mod0, t)),
        assign(t2, tcast(T_UInt(blen*2), t)),
        assign(nth(cm, 0), bin_shr(t2, blen)), # b = 2b >> b
        assign(nth(cm, 1), tcast(T_UInt(blen), t2)), # b = (b) 2b
        # debug
        # call(var("apprint"), var("\"barrett: \""), t2),
        # call(var("apprint"), var("\"native: \""), t1),
        comment("End of MPModDQ_Barrett")
    );

    return cc;

end;

# addmod(c_2b, a_2b, b_2b, mod_2b)
MPModAdd := function(cm, a, b, blen, opts)

    local cc, c, t, k0, k1, k2, k3, k4;
    
    c := var.fresh_t("c_", TArray(T_UInt(blen), 4));
    
    t := var.fresh_t("t_", TArray(T_UInt(blen), 2));

    # Debug(true);
    # Error();

    # debug
    k0 := var.fresh_t("k_", T_UInt(blen*2)); 
    k1 := var.fresh_t("k_", T_UInt(blen*2)); 
    k2 := var.fresh_t("k_", T_UInt(blen*2)); 
    k3 := var.fresh_t("k_", T_UInt(blen*2)); 
    k4 := var.fresh_t("k_", T_UInt(blen*2)); 

    cc := chain(
        comment("Begin of MPModAdd "::StringInt(blen)),
        
        When(opts.useMont,
            MPAddQDD(c, a, b, blen, opts), # works for full bit-width
            MPAddDDD(t, a, b, blen, opts) # assumes that mbits < blen
        ),

        When(opts.useMont,
            MPModDQ_Add(cm, c, blen, opts), # works for full bit-width
            MPModDD(cm, t, blen, opts) # assumes that mbits < blen
        ),

        comment("End of MPModAdd "::StringInt(blen))
    );

    return cc;

end;

# submod(c_2b, a_2b, b_2b, mod_2b)
MPModSub := function(cm, a, b, blen, opts)

    local cc, c, t, r0, r1, in0;
    
    c := var.fresh_t("c_", TArray(T_UInt(blen), 4));
    t := var.fresh_t("t_", TArray(T_UInt(blen), 4));
    # if a < b
    # t = a + mod # 64b = 32b + 32b

    r0 := var.fresh_t("r0_", TArray(T_UInt(blen), 2)); 
    r1 := var.fresh_t("r1_", TArray(T_UInt(blen), 2)); 
    in0 := var.fresh_t("in_", TInt);

    # Debug(true); Error();

    # fix X & Y datatype
    if IsBound(cm.computeType) then cm.t := cm.computeType(); fi;

    cc := chain(
        comment("Begin of MPModSub "::StringInt(blen)),

        # option 1
        # works much better than option 2 for 256b MK on H100
        # MPAddQDD(t, a, opts.modulus, blen, opts), # t = a + mod
        # MPSubQQD(c, t, b, blen, opts), # 64b = 64b - 32b
        # # MPModDQ_Native(cm, c, blen, opts),
        # # MPModDQ_Native_Barrett(cm, c, blen, opts),
        # # MPModDQ_Alt(cm, c, blen, opts),
        # # MPModDQ(cm, c, blen, opts),
        # MPModDQ_Add(cm, c, blen, opts),

        # option 2 (optimized)
        # r0 = a - b
        MPSubDDD(r0, a, b, blen, opts), # r0 < mod if a > b # r0 < 0 -> overflow if a < b
        MPAddDDD(r1, r0, opts.modulus, blen, opts), # r1 = a - b + mod
        # in0 = 1 if a < b
        MPLessThanD(in0, a, b, blen, opts),
        assign(nth(cm, 0), cond(in0, nth(r1, 0), nth(r0, 0))), # b = cond : b ? b
        assign(nth(cm, 1), cond(in0, nth(r1, 1), nth(r0, 1))), # b = cond : b ? b

        comment("End of MPModSub "::StringInt(blen))
    );

    return cc;

end;

# mulmod(c_2b, a_2b, b_2b, mod_2b)
MPModMul := function(cm, a, b, blen, opts)

    local cc, c, k0, k1, k2, k3, k4, k5;
    
    c := var.fresh_t("c_", TArray(T_UInt(blen), 4));

    # debug
    k0 := var.fresh_t("k_", T_UInt(blen*2)); 
    k1 := var.fresh_t("k_", T_UInt(blen*2)); 
    k2 := var.fresh_t("k_", T_UInt(blen*2)); 
    k3 := var.fresh_t("k_", T_UInt(blen*2)); 
    k4 := var.fresh_t("k_", T_UInt(blen*2)); 
    k5 := var.fresh_t("k_", TReal); 

    # Error();

    cc := chain(
        comment("Begin of MPModMul "::StringInt(blen)),
        
        # assign(k0, bin_or(
        #                 bin_shl(tcast(T_UInt(blen*2), nth(a, 0)), blen), 
        #                 nth(a, 1)
        #                 )),
        # call(var("apprint"), var("\"input a: \""), k0),
        # assign(k1, bin_or(
        #                 bin_shl(tcast(T_UInt(blen*2), nth(b, 0)), blen), 
        #                 nth(b, 1)
        #                 )),
        # call(var("apprint"), var("\"input b: \""), k1),
        When(opts.useMacro,
            When(opts.useArray,
                fmulqdd(c, a, b),
                fmulqdd_l1(nth(c, 0), nth(c, 1), nth(c, 2), nth(c, 3), nth(a, 0), nth(a, 1), nth(b, 0), nth(b, 1))
            ),
            opts.mulqdd(c, a, b, blen, opts)
            # MPMulQDD_Karatsuba(c, a, b, blen, opts)
            # MPMulQDD_Schoolbook(c, a, b, blen, opts)
        ),
        
        # assign(k3, bin_or(
        #                 bin_shl(tcast(T_UInt(blen*2), nth(c, 0)), blen), 
        #                 nth(c, 1)
        #                 )),
        # call(var("apprint"), var("\"output c[0]: \""), k3),
        # assign(k4, bin_or(
        #                 bin_shl(tcast(T_UInt(blen*2), nth(c, 2)), blen), 
        #                 nth(c, 3)
        #                 )),
        # call(var("apprint"), var("\"output c[1]: \""), k4),
        
        # assign(k5, bin_or(
        #                 bin_shl(tcast(TReal, nth(c, 0)), blen * 3), 
        #                 bin_shl(tcast(TReal, nth(c, 1)), blen * 2), 
        #                 bin_shl(tcast(TReal, nth(c, 2)), blen), 
        #                 nth(c, 3)
        #                 )), 
        # call(var("apprint"), var("\"output c: \""), k5),
        
        When(opts.useMont,
            MPREDCDQ(cm, c, blen, opts),
            # using Barrett
            # MPModDQ_Native(cm, c, blen, opts),
            # MPModDQ_Native_Barrett(cm, c, blen, opts),
            # MPModDQ_Alt(cm, c, blen, opts),
            MPModDQ(cm, c, blen, opts)
        ),
        
        
        # assign(k2, bin_or(
        #                 bin_shl(tcast(T_UInt(blen*2), nth(cm, 0)), blen), 
        #                 nth(cm, 1)
        #                 )),
        # call(var("apprint"), var("\"output cm: \""), k2),
        
        comment("End of MPModMul "::StringInt(blen))
    );

    return cc; 

end;

