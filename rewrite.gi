CleanVars := (c, opts) -> let(vars := Set(Filtered(List(Collect(c, assign), v->v.loc), IsVar)),
    SubstTopDown(c, @(1,decl), e->decl(Filtered(e.vars, v->v in vars or ObjId(v.t) = TArray), e.cmd)));

UnusedVars := c -> let(vars := Set(Filtered(List(Collect(c, assign), v->v.loc), IsVar)),
    Filtered(Set(Flat(List(Collect(c, decl), d->d .vars or ObjId(v.t) = TArray))), v->not v in vars));

# eliminate variable assignments that are not used in the following lines of code
EliminateDeadCode := function(c, opts)

    local used_vars, assign_list, item, declared_vars, unused_vars, ret_vars, func_vars;

    # all the vars that are returned from func calls
    func_vars := Set(Filtered(Flat(List(Collect(c, @(1, fmulqdd_l1)), v->v.op_out())), IsVar));

    repeat
        # Debug(true); Error();
        # collect all used vars
        # Q: any way to collect all commands? # Collect(c, @(1).cond(IsCommand));
        used_vars := [];
        assign_list := Collect(c, @(1, [assign, fmulqdd_l1]));
        for item in assign_list do
            Append(used_vars, Difference(Set(Collect(item, var)), item.op_out()));
        od;
         
        # collect all defined vars
        declared_vars := Set(Filtered(Flat(List(Collect(c, @(1, [assign, fmulqdd_l1])), v->v.op_out())), IsVar));

        # obtain unused vars (defined - used)
        unused_vars := declared_vars;
        SubtractSet(unused_vars, Set(used_vars));
        
        # need to substract function return arguments from func definition
        ret_vars := Flat(List(Collect(c, func), d->d.params));
        SubtractSet(unused_vars, Set(ret_vars));
        
        # Option 2
        # a7004
        # all_vars := Collect(c, var); # can I collect all var from a cmd?
        # used_vars := Set(ListDifference(all_vars, Set(all_vars)));
        # unused_vars := Set(all_vars);
        # SubtractSet(unused_vars, used_vars);

        # remove dead code
        SubstBottomUp(c, @(1, [assign, fmulqdd_l1], e->IsSubset(unused_vars, e.op_out())), e->skip());
        c := FlattenCode(c);

        # check
        PrintLine(unused_vars);
    until Length(unused_vars) = 0 or IsSubset(func_vars, unused_vars);

    return c;
end;

SCopyPropagate := function(c, opts)
    
    local cmds, vars, tmps;
    
    repeat
        # Debug(true); Error();
        # 1. subst (a35 = t444)
        # 2. assign(t444 = t444) -> skip()
        cmds := Collect(c, [assign, @(1, var), [@(2, var)]]);
        vars := List(cmds, e->e.exp);
        tmps := List(cmds, e->e.loc);
        c := SubstVars(c, FoldR(Zip2(tmps, vars), (a,b) -> CopyFields(a, rec((b[1].id) := b[2])), rec())); 
        SubstBottomUp(c, @(1, assign, e->e.loc = e.exp), e->skip());
        PrintLine("Length(cmds): ", Length(cmds));
    until Length(cmds) = 0;
    
    c := FlattenCode(c);
    
    return c;
end;

MakeBarrettMult := function(c, a, b, opts)
    local cc, mod64, q64, q64a, q64b, tmp64, c64;
    mod64 := tcast(opts.machineMulType, opts.modulus);
    q64a := var.fresh_t("q", opts.machineMulType);
    q64b := var.fresh_t("q", opts.machineMulType);
    tmp64 := var.fresh_t("q", opts.machineMulType);
   
    cc := chain(
        assign(q64a, tcast(opts.machineMulType, a) * tcast(opts.machineMulType, b)),
        assign(q64b, bin_shr(tcast(opts.machineMulType, opts.barrettMu) * bin_shr(q64a, opts.mbits - 2), opts.mbits + 5)),
        assign(tmp64, q64a - q64b * mod64),
        assign(c, tcast(opts.machineType, cond(gt(tmp64, mod64), tmp64-mod64, tmp64)))
    );
    return cc;
end; 

MakeAddMod := function(c, a, b, opts)
    local cc, tmp;
    tmp := var.fresh_t("q", opts.machineMulType);

    cc := chain(
        assign(tmp, tcast(opts.machineMulType, a) + tcast(opts.machineMulType, b)),
        assign(c, cond(gt(tmp, tcast(opts.machineMulType, opts.modulus)), 
                    tmp - tcast(opts.machineMulType, opts.modulus), 
                    tmp))
    );
    return cc;

end;

NTTXFixBigIntOps := function(c, opts)
    local r, s, N;

    c := SubstTopDown(c, @(1, mul, e->ObjId(e.t) = T_UInt), e->ApplyFunc(mulmod, @(1).val.args::[opts.modulus]::
        When(IsBound(opts.nttxConf[1].useBarrettMult) and opts.nttxConf[1].useBarrettMult, [opts.barrettMu], []))); 
    c := SubstBottomUp(c, @(1, add, e->ObjId(e.t) = T_UInt), e->ApplyFunc(addmod, @(1).val.args::[opts.modulus])); 
    c := SubstBottomUp(c, @(1, sub, e->ObjId(e.t) = T_UInt), e->ApplyFunc(submod, @(1).val.args::[opts.modulus])); 
    
    c := Rewrite(c, RulesStrengthReduce, opts);
    c := BinSplit(c, opts);
    c := CSE(c);
    c := CopyPropagate(c, opts);
    c := CopyPropagate.initial(c, opts);
    c := MarkDefUse(c);
    c := CopyPropagate(c, CopyFields(opts, rec(autoinline := true )));
    c := SubstBottomUp(c, @(1, func, e->e.id = "transform"),
        e -> func(@(1).val.ret, @(1).val.id, @(1).val.params, Compile.declareVars(@(1).val.cmd)));
    c := CleanVars(c, opts);

    # twiddle generation via baby step giant step
    if Length(Collect(c, loop)) > 0 then
        # loop code
        N := Length(Collect(c, loop)[1].range)*2;
    else
        N := Length(Collect(c, @(1, nth, e->e.loc = Y)));
    fi; 

    if opts.useTwiddleGen then
        if IsInt(Sqrt(N)) then
            r := Sqrt(N);
            s := r; 
        else
            r := Sqrt(N*2);
            s := N/r;
        fi;

        SubstBottomUp(c, @(1, nth, e->e.loc=opts.twiddles), 
            e->ApplyFunc(mulmod, [nth(opts.twiddles, imod(@(1).val.idx, r)), 
                                nth(opts.twiddles, idiv(@(1).val.idx, r)+r), 
                                opts.modulus]));
    fi;
    
    return c;
end;

NTTXFixMod := function(c, opts)
    local p, vars, v;
    
    p := Value(opts.machineType, opts.abstractType.params[1]);
    c := SubstBottomUp(c, @(1, [add, sub, mul], e->e.t = opts.abstractType),
       e-> imod(@(1).val, p));
    vars := Set(Collect(c, @(1, var, e->e.t = opts.abstractType)));   
    for v in vars do
        v.t := opts.machineType;
    od;
    vars := Set(Collect(c, @(1, var, e->e.t = TPtr(opts.abstractType))));   
    for v in vars do
        v.t := TPtr(opts.machineType);
    od;

    c := SubstBottomUp(c, @(1, mul, e->ObjId(e.t) = T_UInt),
        e->ApplyFunc(mul, List(@(1).val.args, a -> When(IsValue(a), a, tcast(opts.machineMulType, a)))));

    c := SubstBottomUp(c, [@(4, imod), [@(1, sub, e->ObjId(e.t) = T_UInt), @(2), @(3)], @(5)],
        e->(tcast(opts.machineSignedType, @(2).val) - tcast(opts.machineSignedType, @(3).val)) +
            cond(lt(@(2).val, @(3).val), p, V(0))); 
    
    #    c := SubstBottomUp(c, @(1, nth, e->e.loc.id = "X"), 
    #        e->tcast(opts.machineSignedType, @(1).val));
    #    c := SubstBottomUp(c, [@(1, assign), @(2, nth, e->e.loc.id = "Y"), @(3)], 
    #        e->assign(@(2).val, tcast(opts.machineType, @(3).val)));
    
    c := Rewrite(c, RulesStrengthReduce, opts);
    c := CleanVars(c, opts);
    
    return(c);
end;

# FUTURE: these need better guards to ensure all the mods are the same
RewriteRules(RulesStrengthReduce, rec(
    mul_1 :=  ARule(mul, [ @(1, Value, e->ObjId(e.t) = T_UInt and e.v = 1) ],  e -> [ ]),

    # require 1 bit headroom here
    drop_mod := Rule([@(1, imod), @@(2, mul, (e, cx)-> IsBound(cx.opts.machineBitwidth) and IsBound(cx.opts.modulusBitwidth) and
        cx.opts.machineBitwidth > (cx.opts.modulusBitwidth + 1) and ForAll(e.args, i-> ObjId(i) in [Value, imod])), @(3)],
        e -> imod(ApplyFunc(mul, List(@@(2).val.args, i -> When(ObjId(i) = Value, i, i.args[1]))), @(3).val)),

    # the following rules are added for MP
    # a < a <-> False
    lt_self := Rule([lt, @(1), @(2, var, e -> IsBound(e.id) and IsBound(@(1).val.id) and e.id = @(1).val.id)], e -> V_false),

    # unsigned int < 0 <-> False
    lt_0 := Rule([lt, @(1), @(2, Value, e -> e.v = 0)], e -> V_false),

    # a - 0 <-> a
    sub_0 := Rule([sub, @(1), @(2, Value, e -> e.v = 0)], e -> @(1).val),

    # a + 0 <-> a
    add_0 := Rule([add, @(1), @(2, Value, e -> e.v = 0)], e -> @(1).val),

    # (a comp b) ? 1 : 0 <-> (a comp b)
    cond_1_0 := Rule([cond, @(1), @(2, Value, e -> e.v = 1), @(3, Value, e -> e.v = 0)], e -> @(1).val),

    # (a comp b) ? -1 : 0 <-> (!(a comp b) - 1)
    cond_neg1_0 := Rule([cond, @(1), @(2, Value, e -> e.v = -1), @(3, Value, e -> e.v = 0)], e -> (logic_neg(@(1).val) - 1)),

    # cond(bool, a +/- 1, a) <-> a +/- (int) bool
    cond_self_1 := Rule([cond, @(1), @(2, [add, sub], e -> e.args[2] = 1), @(3, var, e -> IsBound(e.id) and IsBound(@(2).val.args[1].id) and e.id = @(2).val.args[1].id)], 
                            e -> @(2).val.__bases__[1](@(2).val.args[1], tcast(TInt, @(1).val))),
    
    # (type) False <-> 0
    tcast_false := Rule([tcast, @(1), @(2, Value, e -> e.v = false)], e -> V(0))

    # Q: worth it?
    # c578 = ((a4759) ? ((a4758 + m7)) : (a4758)); // a4758 + a4759 * m7

));

NTTXFixModNativeBarrett := function(c, opts)
    local p, vars, v, rt;
    
    rt := When(IsBound(c.ruletree), c.ruletree, rec());
    p := opts.modulus;
    
    # fix up subtractions
    # c := SubstBottomUp(c, [@(1, sub, e->e.t = opts.abstractType), @(2), @(3)],
    # e -> cond(lt(@(2).val, @(3).val), (@(2).val + p) - @(3).val, @(2).val - @(3).val)); 

    c := SubstBottomUp(c, [@(1, sub, e->ObjId(e.t) = T_UInt), @(2), @(3)],
        e->tcast(opts.machineType, (tcast(opts.machineSignedType, @(2).val) - tcast(opts.machineSignedType, @(3).val)) +
            cond(lt(@(2).val, @(3).val), tcast(opts.machineSignedType, p), V(0)))); 

    # fix up additions
    c := SubstBottomUp(c, [@(1, add, e->IsBound(e.t) and e.t = opts.abstractType), @(2), @(3)],
        e -> cond(gt(@(2).val + @(3).val, opts.modulus), (@(2).val + @(3).val) - p, @(2).val + @(3).val)); 

    # fix up multiplications
    c := BinSplit(c, opts);
    c := CSE(c);
    c := CopyPropagate(c, opts);

    c := SubstBottomUp(c, [assign, @(1), [@(2, mul, e->IsBound(e.t) and e.t = opts.abstractType), @(3), @(4) ]],
        e -> MakeBarrettMult(@(1).val, @(3).val, @(4).val, opts)); 
   
    c := SubstVars(c, FoldR(Flat(List(List(Collect(c, @(1,cond)), e->e.args[1]), v->Collect(c, @(1, assign, e->e.loc = v)))), 
        (a,b) -> CopyFields(a, rec((b.loc.id) := b.exp)), rec()));
        
    c := FlattenCode(SubstTopDown(c, [@(1, assign), @(2, [lt, gt]), @(3)], e->skip()));


    c := CopyPropagate.initial(c, opts);
    c := MarkDefUse(c);
    c := CopyPropagate(c, CopyFields(opts, rec(autoinline := true )));

    c := SubstBottomUp(c, @(1, func, e->e.id = "transform"),
        e -> func(@(1).val.ret, @(1).val.id, @(1).val.params, Compile.declareVars(@(1).val.cmd)));
    # c := Compile(c, opts);

    # fix up data types
    vars := Set(Collect(c, @(1, var, e->e.t = opts.abstractType)));   
    for v in vars do
        v.t := opts.machineType;
    od;
    vars := Set(Collect(c, @(1, var, e->e.t = TPtr(opts.abstractType))));   
    for v in vars do
        v.t := TPtr(opts.machineType);
    od;
    vars := Set(Collect(c, @(1, var, e->ObjId(e.t) = TPtr and e.t.t = TPtr(opts.abstractType))));   
    for v in vars do
        v.t.t := TPtr(opts.machineType);
    od;


    vars := Set(Collect(c, @(1, var, e->ObjId(e.t) = TArray and e.t.t = opts.abstractType)));   
    for v in vars do
        v.t.t := opts.machineType;
    od;

    c := CleanVars(c, opts);

    c.ruletree := rt;
    return c;

    ##========================
    #
    #    c := SubstBottomUp(c, @(1, [add, sub, mul], e->e.t = opts.abstractType),
    #       e-> imod(@(1).val, p));
    #
    #
    #
    #    c := SubstBottomUp(c, @(1, mul, e->ObjId(e.t) = T_UInt),
    #        e->ApplyFunc(mul, List(@(1).val.args, a -> When(IsValue(a), a, tcast(opts.machineMulType, a)))));
    #
    #    c := SubstBottomUp(c, [@(4, imod), [@(1, sub, e->ObjId(e.t) = T_UInt), @(2), @(3)], @(5)],
    #        e->(tcast(opts.machineSignedType, @(2).val) - tcast(opts.machineSignedType, @(3).val)) +
    #            cond(lt(@(2).val, @(3).val), p, V(0))); 
    #    
    ##    c := SubstBottomUp(c, @(1, nth, e->e.loc.id = "X"), 
    ##        e->tcast(opts.machineSignedType, @(1).val));
    ##    c := SubstBottomUp(c, [@(1, assign), @(2, nth, e->e.loc.id = "Y"), @(3)], 
    ##        e->assign(@(2).val, tcast(opts.machineType, @(3).val)));
    #    
    #    c := Rewrite(c, RulesStrengthReduce, opts);
    #    
    #    return(c);
end;

# used by mp.g without mxp flag
NTTXFixMPOps := function(c, opts)
    local p, vars, v, rt, currsize;
    
    rt := When(IsBound(c.ruletree), c.ruletree, rec());
    p := opts.modulus;
    currsize := opts.insize;

    c := BinSplit(c, opts);
    c := CSE(c);
    c := CopyPropagate(c, opts);

    currsize := currsize/2;

    if IsBound(opts.useMacro) and opts.useMacro then
        # use macros from the library
        c := SubstBottomUp(c, @(1, mul, e->ObjId(e.t) = T_UInt), e->ApplyFunc(mulmod, @(1).val.args::[opts.modulus, opts.barrettMu])); 
        c := SubstBottomUp(c, @(1, add, e->ObjId(e.t) = T_UInt), e->ApplyFunc(addmod, @(1).val.args::[opts.modulus, opts.barrettMu])); 
        c := SubstBottomUp(c, @(1, sub, e->ObjId(e.t) = T_UInt), e->ApplyFunc(submod, @(1).val.args::[opts.modulus, opts.barrettMu])); 
    else
        # @(1).val: output
        # @(2).val: operand
        # @(3).val: op first param
        # @(4).val: op second param
        c := SubstBottomUp(c, [assign, @(1), [@(2, mul, e->IsBound(e.t) and e.t = opts.abstractType), @(3), @(4)]],
            e -> MakeModMulMP(@(1).val, @(3).val, @(4).val, currsize, opts)); 
        c := SubstBottomUp(c, [assign, @(1), [@(2, add, e->IsBound(e.t) and e.t = opts.abstractType), @(3), @(4)]],
            e -> MakeModAddMP(@(1).val, @(3).val, @(4).val, currsize, opts)); 
        c := SubstBottomUp(c, [assign, @(1), [@(2, sub, e->IsBound(e.t) and e.t = opts.abstractType), @(3), @(4)]],
            e -> MakeModSubMP(@(1).val, @(3).val, @(4).val, currsize, opts)); 
    fi;

    c := FlattenCode(c);
    # PrintCode("", c, opts);

    c := Rewrite(c, RulesStrengthReduce, opts); 
    c := BinSplit(c, opts); 
    # c := CSE(c); # not working for MPMod
    c := CopyPropagate(c, opts); 
    # c := CopyPropagate.initial(c, opts); # not working for MPMod
    c := MarkDefUse(c);
    c := CopyPropagate(c, CopyFields(opts, rec(autoinline := true)));
    
    # Error();

    c := SubstBottomUp(c, @(1, func, e->e.id = "transform"),
        e -> func(@(1).val.ret, @(1).val.id, @(1).val.params, Compile.declareVars(@(1).val.cmd)));


    #     # fix up data types Q: do I need this?
    #     vars := Set(Collect(c, @(1, var, e->e.t = opts.abstractType)));   
    #     for v in vars do
    #         v.t := opts.machineType;
    #     od;
    #     vars := Set(Collect(c, @(1, var, e->e.t = TPtr(opts.abstractType))));   
    #     for v in vars do
    #         v.t := TPtr(opts.machineType);
    #     od;
    #     vars := Set(Collect(c, @(1, var, e->ObjId(e.t) = TPtr and e.t.t = TPtr(opts.abstractType))));   
    #     for v in vars do
    #         v.t.t := TPtr(opts.machineType);
    #     od;


    #     vars := Set(Collect(c, @(1, var, e->ObjId(e.t) = TArray and e.t.t = opts.abstractType)));   
    #     for v in vars do
    #         v.t.t := opts.machineType;
    #     od;

    c := CleanVars(c, opts);

    c.ruletree := rt;
    return c;
end;

# used by mp-py.g
NTTXFixMPPyOps := function(c, opts)
    local p, vars, v, rt, currsize, ins, j, vectorlength, recurlevel;
    
    rt := When(IsBound(c.ruletree), c.ruletree, rec());
    p := opts.modulus;
    currsize := opts.insize;

    c := BinSplit(c, opts);
    c := CSE(c);
    c := CopyPropagate(c, opts);

    currsize := currsize/2;

    genBLAS := false;
    if genBLAS then

        # Debug(true); Error();
        recurlevel := 3;
        vectorlength := 1024/pow(2, recurlevel-1).v;
        j := Ind(vectorlength);
    
        # vvmul: Y[i] = X[i] * twd[i]
        # ins := [loop(j, vectorlength, assign(nth(Y, j), mul(nth(X, j), nth(opts.twiddles, j))))];
        
        # vvadd: Y[i] = X[i] + twd[i]
         #ins := [loop(j, vectorlength, assign(nth(Y, j), add(nth(X, j), nth(opts.twiddles, j))))];
        
        # vvsub: Y[i] = X[i] - twd[i]
        # ins := [loop(j, vectorlength, assign(nth(Y, j), sub(nth(X, j), nth(opts.twiddles, j))))];
        
        # axpy: Y[i] = twd[0] * X[i] + twd[i]
         #ins := [loop(j, vectorlength, assign(nth(Y, j), add(mul(nth(X, j), nth(opts.twiddles, 0)), nth(opts.twiddles, j))))];

        c.cmds[1].cmds[1].cmds[2].cmd.cmds[1].cmd.cmds := ins;
        
    fi;

    if IsBound(opts.useMacro) and opts.useMacro then
        # use macros from the library
        c := SubstBottomUp(c, @(1, mul, e->ObjId(e.t) = T_UInt), e->ApplyFunc(mulmod, @(1).val.args::[opts.modulus, opts.barrettMu])); 
        c := SubstBottomUp(c, @(1, add, e->ObjId(e.t) = T_UInt), e->ApplyFunc(addmod, @(1).val.args::[opts.modulus, opts.barrettMu])); 
        c := SubstBottomUp(c, @(1, sub, e->ObjId(e.t) = T_UInt), e->ApplyFunc(submod, @(1).val.args::[opts.modulus, opts.barrettMu])); 
    else
        # @(1).val: output
        # @(2).val: operand
        # @(3).val: op first param
        # @(4).val: op second param
        c := SubstBottomUp(c, [assign, @(1), [@(2, mul, e->IsBound(e.t) and e.t = opts.abstractType), @(3), @(4)]],
            e -> MakeModMulMP(@(1).val, @(3).val, @(4).val, currsize, opts)); 
        c := SubstBottomUp(c, [assign, @(1), [@(2, add, e->IsBound(e.t) and e.t = opts.abstractType), @(3), @(4)]],
            e -> MakeModAddMP(@(1).val, @(3).val, @(4).val, currsize, opts)); 
        c := SubstBottomUp(c, [assign, @(1), [@(2, sub, e->IsBound(e.t) and e.t = opts.abstractType), @(3), @(4)]],
            e -> MakeModSubMP(@(1).val, @(3).val, @(4).val, currsize, opts)); 
    fi;

    # remove init and destroy
    c := SubstTopDown(c, @(1, func, e-> e.id = "init"), e -> skip());
    c := SubstTopDown(c, @(1, func, e-> e.id = "destroy"), e -> skip());

    c := FlattenCode(c);
    # PrintCode("", c, opts);

    c := Rewrite(c, RulesStrengthReduce, opts); 
    c := BinSplit(c, opts); 
    # c := CSE(c); # not working for MPMod
    c := CopyPropagate(c, opts); 
    # c := CopyPropagate.initial(c, opts); # not working for MPMod
    c := MarkDefUse(c);
    c := CopyPropagate(c, CopyFields(opts, rec(autoinline := true)));

    c := SubstBottomUp(c, @(1, func, e->e.id = "transform"),
        e -> func(@(1).val.ret, @(1).val.id, @(1).val.params, Compile.declareVars(@(1).val.cmd)));

    c := CleanVars(c, opts);

    c.ruletree := rt;
    return c;
end;

# used by mp.g with mxp flag, mixed precision
# assuming useMacro = false
# right now it is assuming that InInt = 2 * BaseInt
# basesize = blen(BaseInt)
# need: insize, basesize (carried by opts)
NTTXFixMxPOps := function(c, opts)
    local p, vars, v, rt, currsize, ins, nths, tmps, cmds, cmd,
    muls, mul_vars, add_vars, sub_vars, array_vars, loop_vars,
    main_decl, useVerbose, time_stamp, fa, fb, fc, mulqdd_func,
    funcs, list, func_list;

    rt := When(IsBound(c.ruletree), c.ruletree, rec());
    p := opts.modulus;

    # print more info for debugging
    useVerbose := true;
    if useVerbose then 
        PrintLine("Entering rewrite.gi"); 
        time_stamp := Runtime();
        PrintLine("0\% Done. Time spent: ", StringTime(Runtime()-time_stamp));
    fi;

    # pre-compile
    c := BinSplit(c, opts);
    c := CSE(c);
    c := CopyPropagate(c, opts);

    # Original code

    # Debug(true); Error();
    # only testing for one ins
    # ins := c.cmds[1].cmds[1].cmds[2].cmd.cmds[1].cmd.cmds;
    # ins := [assign(nth(Y, V(0)), mul(nth(twiddles, V(1)), nth(X, V(2))))];
    # # ins := [ins[1], 
    # #         assign(nth(Y, V(0)), add(nth(X, V(0)), var.table.s17)),
    # #         assign(nth(Y, V(1)), sub(nth(X, V(0)), var.table.s17))
    # #         ];
    # c.cmds[1].cmds[1].cmds[2].cmd.cmds[1].cmd.cmds := ins;

    
    # -------------------------------- First Pass --------------------------------
    # Example: 64b InInt 32b BaseInt
    # 64b -> 64b & 32b, with 32b Base

    currsize := opts.insize/2;

    c := BinSplit(c, opts); 

    # now everything is 64b
    # inspect datatype
    # vars := Set(Collect(c, var));
    # for v in vars do
    #     PrintLine(v, ": ", v.t);
    # od;

    # modify datatype
    # Y datatype error
    # c := SubstBottomUp(c, [assign, @(1, nth, e->e.loc = Y), [@(2), @(3), @(4)]],
    #     e -> let(tmp_y := var.fresh_t("tmp_y", T_UInt(currsize*2)), 
    #              chain(assign(tmp_y, @(2).val), assign(@(1).val, tmp_y))));
    # c := FlattenCode(c);

    # type: T_UInt(2b) -> TArray(T_UInt(b), 2)
    vars := Collect(c, @(1, var, e->e.t=T_UInt(currsize*2))); 
    for v in vars do
        v.t := TArray(T_UInt(currsize), 2);
    od;

    # Debug(true);
    # Error();
    
    # type: TPtr(T_UInt(2b), Value) -> TPtr(TArray(T_UInt(b), 2), Value)
    # TPtr(T_UInt(64)).aligned([ 16, 0 ]) -> TPtr(TArray(T_UInt(32), 2)).aligned([ 16, 0 ])
    # target X, Y, twiddles
    vars := Collect(c, @(1, var, e->IsBound(e.t.t) and e.t.t=T_UInt(currsize*2)));
    for v in vars do
        v.t.t := TArray(T_UInt(currsize), 2);
    od;
    opts.modulus.t := TArray(T_UInt(currsize), 2);
    opts.barrettMu.t := TArray(T_UInt(currsize), 2);

    # inspect datatype
    # all datatypes should be TArray(T_UInt(currsize), 2) or TInt
    # vars := Set(Collect(c, var));
    # for v in vars do
    #     PrintLine(v, ": ", v.t);
    # od;

    # initial mul, add & sub
    # used for SubstBottomUp
    muls := Collect(c, [assign, @(1), [@(2, mul), @(3), @(4)]]);
    mul_vars := List(muls, e->e.loc);
    adds := Collect(c, [assign, @(1), [@(2, add, e->IsBound(e.t) and e.t = opts.abstractType), @(3), @(4)]]);
    add_vars := List(adds, e->e.loc);
    subs := Collect(c, [assign, @(1), [@(2, sub, e->IsBound(e.t) and e.t = opts.abstractType), @(3), @(4)]]);
    sub_vars := List(subs, e->e.loc);

    # @(1).val: output
    # @(2).val: operand
    # @(3).val: op first param
    # @(4).val: op second param
    # 2b = 2b * 2b
    c := SubstBottomUp(c, [assign, @(1, [var, nth], e->e in mul_vars), [@(2, mul, e->IsBound(e.t) and e.t = opts.abstractType), @(3), @(4)]],
        e -> MPModMul(@(1).val, @(3).val, @(4).val, currsize, opts)); 
    c := SubstBottomUp(c, [assign, @(1, [var, nth], e->e in add_vars), [@(2, add, e->IsBound(e.t) and e.t = opts.abstractType), @(3), @(4)]],
        e -> MPModAdd(@(1).val, @(3).val, @(4).val, currsize, opts));
    c := SubstBottomUp(c, [assign, @(1, [var, nth], e->e in sub_vars), [@(2, sub, e->IsBound(e.t) and e.t = opts.abstractType), @(3), @(4)]],
        e -> MPModSub(@(1).val, @(3).val, @(4).val, currsize, opts)); 

    if opts.useMacro then
        # add function implementation
        # append mpmulqdd to the main body
        # func(TVoid, "MPMulQDD", [c0, c1, c2, c3, a0, a1, b0, b1, mod0, mod1, mu0, mu1],
        # chain(MPMulQDD())
        # then I need to a function that takes 12 inputs?
        #)
        # c.cmds[1].cmds[1].cmds
        # 
        if not opts.useArray then
            fa := var.fresh_t("fa_", TArray(T_UInt(currsize), 2)); 
            fb := var.fresh_t("fb_", TArray(T_UInt(currsize), 2)); 
            fc := var.fresh_t("fc_", TArray(T_UInt(currsize), 4)); 

            mulqdd_func := func(TVoid, "MPMulQDD_L1", [nth(fc, 0), nth(fc, 1), nth(fc, 2), nth(fc, 3),
                                                    nth(fa, 0), nth(fa, 1), nth(fb, 0), nth(fb, 1)],
                                chain(MPMulQDD(fc, fa, fb, currsize, opts))
                            );
            funcs := [mulqdd_func];
            Append(funcs, c.cmds[1].cmds[1].cmds);
            c.cmds[1].cmds[1].cmds := funcs;
        else
            # maybe this should de deprecated?
            fa := var.fresh_t("fa_", TArray(T_UInt(currsize), 2)); 
            fb := var.fresh_t("fb_", TArray(T_UInt(currsize), 2)); 
            fc := var.fresh_t("fc_", TArray(T_UInt(currsize), 4)); 

            mulqdd_func := func(TVoid, "MPMulQDD", [fc, fa, fb],
                                chain(MPMulQDD(fc, fa, fb, currsize, opts))
                            );
            funcs := [mulqdd_func];
            Append(funcs, c.cmds[1].cmds[1].cmds);
            c.cmds[1].cmds[1].cmds := funcs;

            # Debug(true); Error();
        fi;
    fi;

    if useVerbose then PrintLine("10\% Done. Time spent: ", StringTime(Runtime()-time_stamp)); fi;

    c := FlattenCode(c);
    c := Rewrite(c, RulesStrengthReduce, opts); 
        
    # put X, Y in nth
    # otherwise cannot tell which nth needs to be removed/scalarized
    
    c := CopyPropagate(c, opts);
    c := ForceCopyPropagate(c, opts);

    # X/Y/twds[i][j] -> X[i*R+j]
    # Collect(c, @(1, nth, e->IsBound(e.loc.loc))); # nth(nth(...))
    # Debug(true); Error();
    c := SubstBottomUp(c, @(1, nth, e->IsBound(e.loc.loc)), e->nth(e.loc.loc, e.loc.idx*2+e.idx));

    if useVerbose then PrintLine("20\% Done. Time spent: ", StringTime(Runtime()-time_stamp)); fi;
    
    # Pass to remove intermediates nths
    # Assumes that any generated nth will be consumed
        # only allow 32b and 16b
        # does not allow arrays
        # Collect(c, @(1, var, e->e.t=TArray(T_UInt(currsize), 2)));
        # Debug(true); Error();

        # x := c.cmds[1].cmds[1].cmds[3].cmd.cmds[1].cmd.cmds[2];
        
        c := BinSplit(c, opts);
        c := MarkDefUse(c);

        # vars that can be nth'ed (will exclude them in the following lines)
        # array_vars = loop_vars::{inputs}
        array_vars := Set([X, Y, opts.twiddles, opts.barrettMu, opts.modulus]::Collect(c, @(1, var, e->IsPtrT(e.t) or (IsArrayT(e.t) and IsBound(e.t.t) and IsArrayT(e.t.t)))));
        loop_vars := Copy(array_vars); SubtractSet(loop_vars, Set([X, Y, opts.twiddles, opts.barrettMu, opts.modulus]));

        nths := Set(Collect(c, @(1, nth, e->not e.loc in array_vars)));
        tmps := [];
        for i in [1..Length(nths)] do
            Append(tmps, [var.fresh_t("t", nths[i].t)]);
        od;
        vars := Collect(c, @(1, nth, e->not e.loc in array_vars));
        c := SubstBottomUp(c, @(1, nth, e->not e.loc in array_vars), e->tmps[Position(nths, e)]);
        
        
        c := FlattenCode(c);
        # c := CopyPropagate(c, opts); # does not work
        # run copypropagation only on the main function
        # SubstBottomUp(c, @(1, func, e->e.id = "MPMulQDD_L1"), e -> CopyPropagate(e, opts)); # wrong
        # SubstBottomUp(c, @(1, func, e->e.id = "transform"), e -> CopyPropagate(e, opts));
        # using own copyprapagation
        c := SCopyPropagate(c, opts);
        c := ForceCopyPropagate(c, opts);

    if useVerbose then PrintLine("30\% Done. Time spent: ", StringTime(Runtime()-time_stamp)); fi;

    # should be no TArray(T_UInt(currsize), 2)
    # vars := Set(Collect(c, var)); # some vars are not in the actual code
    # for v in vars do
    #     PrintLine(v, ": ", v.t);
    # od;

    # remove vars in decl, only keep T*
    list := Collect(c, decl);
    for v in list do
        v.vars := Filtered(v.vars, e->IsArray(e.t) and IsBound(e.t.t) and IsArray(e.t.t));
    od;

    # Strength Reduction
    # b >> blen -> 0
    # Collect(c, [assign, @(1), [@(2, bin_shr), @(3, var, e->e.t = T_UInt(currsize)), @(4, Value, e->e = currsize)]]);
    c := SubstBottomUp(c, [assign, @(1), [@(2, bin_shr), @(3, var, e->e.t = T_UInt(currsize)), @(4, Value, e->e = currsize)]],
        e -> assign(@(1).val, V(0))); 

    # X, Y, twds' datatype now is splitted for correct function inputs' datatype
    # TPtr(TArray(T_UInt(16), 2)) -> TPtr(T_UInt(16))
    X.t := TPtr(T_UInt(currsize)).aligned([ 16, 0 ]); opts.XType := X.t;
    Y.t := TPtr(T_UInt(currsize)).aligned([ 16, 0 ]); opts.YType := Y.t;
    opts.twiddles.t := TPtr(T_UInt(currsize)).aligned([ 16, 0 ]);
    for v in loop_vars do
        v.t := TArray(T_UInt(currsize), v.t.size*(insize/currsize));
    od;
    # Debug(true); Error();

    # needed for l2 recursion
    c := EliminateDeadCode(c, opts);

    if useVerbose then PrintLine("40\% Done. Time spent: ", StringTime(Runtime()-time_stamp)); fi;


    if opts.recursionLevel = 2 then

        # -------------------------------- Second Pass --------------------------------
        # 64b & 32b -> 32b & 16b, with 16b Base
        
        currsize := currsize/2; # TODO: change name to currlen
        # currtype := T_UInt(currsize);
        # TArray(T_UInt(current), 4)

        # Y datatype error
        # Y.t := TPtr(TArray(T_UInt(currsize), 2)).aligned([ 16, 0 ]);
        
        # BinSplit is not working for all X, and twiddles related
        c := BinSplit(c, opts);
        # fix BinSplit
        vars := Set(Collect(c, @(1, var, e->IsArray(e.t))));
        for v in vars do
            if not v in [opts.modulus, opts.barrettMu] then
                v.t := v.t.t;
            fi;
        od;

        # now everything is binsplitted, continue here

        # now everything is 64b & 32b
        # inspect datatype
        # vars := Set(Collect(c, var));
        # for v in vars do
        #     PrintLine(v, ": ", v.t);
        # od;

        # type: T_UInt(2b) -> TArray(T_UInt(b), 2)
        vars := Collect(c, @(1, var, e->e.t=T_UInt(currsize*2))); 
        for v in vars do
            v.t := TArray(T_UInt(currsize), 2);
        od;

        # type: T_UInt(4b) -> TArray(T_UInt(b), 4)
        vars := Collect(c, @(1, var, e->e.t=T_UInt(currsize*4))); 
        for v in vars do
            v.t := TArray(T_UInt(currsize), 4);
        od;

        # type: TArray(T_UInt(2b), Value) -> TArray(TArray(T_UInt(b), 2), Value)
        # change X, Y, twiddles datatype
        vars := Collect(c, @(1, var, e->IsBound(e.t.t) and e.t.t=T_UInt(currsize*2)));
        for v in vars do
            v.t.t := TArray(T_UInt(currsize), 2);
        od;
        opts.modulus.t := TArray(T_UInt(currsize), opts.modulus.t.size*2);
        opts.barrettMu.t := TArray(T_UInt(currsize), opts.barrettMu.t.size*2);
        # Debug(true); Error();
        
        # inspect datatype
        # all datatypes should be TArray(T_UInt(currsize), 2/4) or TInt
        # vars := Set(Collect(c, var));
        # for v in vars do
        #     PrintLine(v, ": ", v.t);
        # od;

        # plan: 
        # edit add, make code gen go through and verify s7 correctness
        # if correct, just define own add here that makes copypropagation go through

        # note that in mxpmethod.gi all rules are in the form of b + b -> 2b
        # here b becomes 2b and 2b becomes 4b
        # now the goal is to remove any 4b (reduce to 2b & b)
        # we can also reduce 2b to b but it is not required

        # fix datatype of nth()
        vars := Collect(c, @(1, nth, e->e.t <> e.computeType()));
        for v in vars do
            v.t := v.computeType();
        od;

        # Debug(true); Error();

        if useVerbose then PrintLine("50\% Done. Time spent: ", StringTime(Runtime()-time_stamp)); fi;

        # Rule 1: 4b = 2b + 2b -> MPAddQDD
        c := SubstBottomUp(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 4)), [@(2, add), @(3, var, e->e.t = TArray(T_UInt(currsize), 2)), @(4, var, e->e.t = TArray(T_UInt(currsize), 2))]],
            e -> MPAddQDD(@(1).val, @(3).val, @(4).val, currsize, opts));

        # Rule 2: 2b = (2b) 4b 
        c := SubstBottomUp(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 2)), [@(2, tcast, e->e.args[1] = T_UInt(currsize*2)), @(3), @(4, var, e->e.t = TArray(T_UInt(currsize), 4))]],
            e -> MPExtractLow(@(1).val, @(4).val, currsize, opts));

        # Rule 3: int = 4b >> blen*2
        c := SubstBottomUp(c, [assign, @(1, var, e->e.t = TInt), [@(2, bin_shr), @(3, var, e->e.t = TArray(T_UInt(currsize), 4)), @(4, Value, e->e.v = currsize*2)]],
            e -> MPExtractCarry(@(1).val, @(3).val, currsize, opts));

        # Rule 4: 4b = 4b + 0/1
        c := SubstBottomUp(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 4)), [@(2, add), @(3, var, e->e.t = TArray(T_UInt(currsize), 4)), @(4, var, e->e.t = TInt)]],
            e -> MPPropagateCarry(@(1).val, @(3).val, @(4).val, currsize, opts));
        
        # Rule 5: int = 2b == 2b
        c := SubstBottomUp(c, [assign, @(1, var, e->e.t = TBool), [@(2, eq), @(3, var, e->e.t = TArray(T_UInt(currsize), 2)), @(4, var, e->e.t = TArray(T_UInt(currsize), 2))]],
            e -> MPEqualD(@(1).val, @(3).val, @(4).val, currsize, opts));

        # Rule 6: TBool/int = 2b < 2b
        c := SubstBottomUp(c, [assign, @(1, var, e->e.t in [TBool, TInt]), [@(2, lt), @(3, var, e->e.t = TArray(T_UInt(currsize), 2)), @(4, var, e->e.t = TArray(T_UInt(currsize), 2))]],
            e -> MPLessThanD(@(1).val, @(3).val, @(4).val, currsize, opts));

        # Rule 7: 2b = 2b - 2b (can wrap around)
        c := SubstBottomUp(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 2)), [@(2, sub), @(3, var, e->e.t = TArray(T_UInt(currsize), 2)), @(4, var, e->e.t = TArray(T_UInt(currsize), 2))]],
            e -> MPSubDDD(@(1).val, @(3).val, @(4).val, currsize, opts));
        
        # Rule 8: 2b = 2b - 0/1
        c := SubstBottomUp(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 2)), [@(2, sub), @(3, var, e->e.t = TArray(T_UInt(currsize), 2)), @(4, [var, Value], e->e.t = TInt)]],
            e -> MPSubDDI(@(1).val, @(3).val, @(4).val, currsize, opts));

        # Rule 9: 4b = 2b * 2b -> MPMulQDD
        # Debug(true); Error();
        c := SubstBottomUp(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 4)), [@(2, mul), @(3, var, e->e.t = TArray(T_UInt(currsize), 2)), @(4, var, e->e.t = TArray(T_UInt(currsize), 2))]],
            e -> MPMulQDD(@(1).val, @(3).val, @(4).val, currsize, opts));
        
        # Rule 10: 2b = 4b >> blen*2
        c := SubstBottomUp(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 2)), [@(2, bin_shr), @(3, var, e->e.t = TArray(T_UInt(currsize), 4)), @(4, Value, e->e.v = currsize*2)]],
            e -> MPExtractHigh(@(1).val, @(3).val, currsize, opts));
        
        # Rule 11: 2b = 2b
        # Collect(c, @(1, assign, e->e.loc.t = TArray(T_UInt(currsize), 2) and e.exp.t = TArray(T_UInt(currsize), 2)));
        c := SubstBottomUp(c, @(1, assign, e->e.loc.t = TArray(T_UInt(currsize), 2) and e.exp.t = TArray(T_UInt(currsize), 2)),
            e -> MPAssignDD(@(1).val.loc, @(1).val.exp, currsize, opts));

        # assumption: the only logic_and in mxpmethods acts on 2b and 2b is where both 2b = 0/1
        # Rule 12: int = 2b (0/1) && 2b (0/1)
        # Collect(c, [assign, @(1, var, e->e.t = TInt), [@(2, logic_and), @(3, var, e->e.t = TArray(T_UInt(currsize), 2)), @(4, var, e->e.t = TArray(T_UInt(currsize), 2))]]);
        c := SubstBottomUp(c, [assign, @(1, var, e->e.t = TInt), [@(2, logic_and), @(3, var, e->e.t = TArray(T_UInt(currsize), 2)), @(4, var, e->e.t = TArray(T_UInt(currsize), 2))]],
            e -> MPLogicAndDD(@(1).val, @(3).val, @(4).val, currsize, opts));

        # Rule 13: 2b = 2b + 2b
        c := SubstBottomUp(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 2)), [@(2, add), @(3, var, e->e.t = TArray(T_UInt(currsize), 2)), @(4, var, e->e.t = TArray(T_UInt(currsize), 2))]],
            e -> MPAddDDD(@(1).val, @(3).val, @(4).val, currsize, opts));

        # Rule 14: 2b = (2b) 2b
        c := SubstBottomUp(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 2)), [@(2, tcast, e->e.args[1] = T_UInt(currsize*2)), @(3), @(4, var, e->e.t = TArray(T_UInt(currsize), 2))]],
            e -> MPEqualTypeCastD(@(1).val, @(4).val, currsize, opts));

        # assumption: all TInt (involved in computation, not shift) is actually 0/1
        # Rule 15: 4b = 0/1 + 2b
        # Collect(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 4)), [@(2, add), @(3, var, e->e.t = TInt), @(4, var, e->e.t = TArray(T_UInt(currsize), 2))]]);
        c := SubstBottomUp(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 4)), [@(2, add), @(3, var, e->e.t = TInt), @(4, var, e->e.t = TArray(T_UInt(currsize), 2))]],
            e -> MPAddQID(@(1).val, @(3).val, @(4).val, currsize, opts));
        
        # starting here, rules are for Mod
        # Debug(true); Error();
        # Rule 16: 2b = (2b) 1
        # assign(a313, tcast(T_UInt(32), V(1)))
        # Collect(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 2)), [@(2, tcast, e->e.args[1] = T_UInt(currsize*2)), @(3), @(4, Value, e->e.v = 1)]]);
        c := SubstBottomUp(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 2)), [@(2, tcast, e->e.args[1] = T_UInt(currsize*2)), @(3), @(4, Value, e->e.v = 1)]],
            e -> MPTypeCastDI(@(1).val, @(4).val, currsize, opts));

        # assumption: @(1) must be 2b; does not explicitly check because of nth(Y, *)
        # Rule 17: 2b = 0/1 ? 2b : 2b
        # Collect(c, [assign, @(1), [@(2, cond), @(3, var, e->e.t = TInt), @(4, var, e->e.t = TArray(T_UInt(currsize), 2)), @(5, var, e->e.t = TArray(T_UInt(currsize), 2))]]);
        c := SubstBottomUp(c, [assign, @(1), [@(2, cond), @(3, var, e->e.t = TInt), @(4, var, e->e.t = TArray(T_UInt(currsize), 2)), @(5, var, e->e.t = TArray(T_UInt(currsize), 2))]],
            e -> MPCondD(@(1).val, @(3).val, @(4).val, @(5).val, currsize, opts));

        # Rule 18: 2b = 2b & 2b
        # Collect(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 2)), [@(2, bin_and), @(3, var, e->e.t = TArray(T_UInt(currsize), 2)), @(4, var, e->e.t = TArray(T_UInt(currsize), 2))]]);
        c := SubstBottomUp(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 2)), [@(2, bin_and), @(3, var, e->e.t = TArray(T_UInt(currsize), 2)), @(4, var, e->e.t = TArray(T_UInt(currsize), 2))]],
            e -> MPBinAndD(@(1).val, @(3).val, @(4).val, currsize, opts));

        # Rule 19: 2b = 2b | 2b
        # Collect(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 2)), [@(2, bin_or), @(3, var, e->e.t = TArray(T_UInt(currsize), 2)), @(4, var, e->e.t = TArray(T_UInt(currsize), 2))]]);
        c := SubstBottomUp(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 2)), [@(2, bin_or), @(3, var, e->e.t = TArray(T_UInt(currsize), 2)), @(4, var, e->e.t = TArray(T_UInt(currsize), 2))]],
            e -> MPBinOrD(@(1).val, @(3).val, @(4).val, currsize, opts));

        # assumption: int < blen
        # Rule 20: 2b = 2b >> int
        # Collect(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 2)), [@(2, bin_shr), @(3, var, e->e.t = TArray(T_UInt(currsize), 2)), @(4, Value, e->e.v < currsize)]]);
        c := SubstBottomUp(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 2)), [@(2, bin_shr), @(3, var, e->e.t = TArray(T_UInt(currsize), 2)), @(4, Value, e->e.v < currsize)]],
            e -> MPShiftRight2D(@(1).val, @(3).val, @(4).val, currsize, opts));
        
        # assumption: blen < int < 2*blen
        # Rule 21: 2b = 2b >> int
        # Collect(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 2)), [@(2, bin_shr), @(3, var, e->e.t = TArray(T_UInt(currsize), 2)), @(4, Value, e->e.v > currsize and e.v < 2*currsize)]]);
        c := SubstBottomUp(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 2)), [@(2, bin_shr), @(3, var, e->e.t = TArray(T_UInt(currsize), 2)), @(4, Value, e->e.v > currsize and e.v < 2*currsize)]],
            e -> MPShiftRight1D(@(1).val, @(3).val, @(4).val, currsize, opts));

        # assumption: int < blen
        # Rule 22: 2b = 2b << int
        # Collect(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 2)), [@(2, bin_shl), @(3, var, e->e.t = TArray(T_UInt(currsize), 2)), @(4, Value, e->e.v < currsize)]]);
        c := SubstBottomUp(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 2)), [@(2, bin_shl), @(3, var, e->e.t = TArray(T_UInt(currsize), 2)), @(4, Value, e->e.v < currsize)]],
            e -> MPShiftLeft2D(@(1).val, @(3).val, @(4).val, currsize, opts));
        
        # assumption: blen < int < 2*blen
        # Rule 23: 2b = 2b << int
        # Collect(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 2)), [@(2, bin_shl), @(3, var, e->e.t = TArray(T_UInt(currsize), 2)), @(4, Value, e->e.v > currsize and e.v < 2*currsize)]]);
        c := SubstBottomUp(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 2)), [@(2, bin_shl), @(3, var, e->e.t = TArray(T_UInt(currsize), 2)), @(4, Value, e->e.v > currsize and e.v < 2*currsize)]],
            e -> MPShiftLeft1D(@(1).val, @(3).val, @(4).val, currsize, opts));

        # Rule 24: TBool = 2b <> int
        # Collect(c, [assign, @(1, var, e->e.t = TBool), [@(2, neq), @(3, var, e->e.t = TArray(T_UInt(currsize), 2)), @(4, Value)]]);
        c := SubstBottomUp(c, [assign, @(1, var, e->e.t = TBool), [@(2, neq), @(3, var, e->e.t = TArray(T_UInt(currsize), 2)), @(4, Value)]],
            e -> MPNotEqualDI(@(1).val, @(3).val, @(4).val, currsize, opts));
        
        # Rule 25: TBool/TInt = 2b > 2b
        c := SubstBottomUp(c, [assign, @(1, var, e->e.t in [TBool, TInt]), [@(2, gt), @(3, var, e->e.t = TArray(T_UInt(currsize), 2)), @(4, var, e->e.t = TArray(T_UInt(currsize), 2))]],
            e -> MPLessThanD(@(1).val, @(4).val, @(3).val, currsize, opts));

        # Rule 26: TInt = 2b < TInt
        c := SubstBottomUp(c, [assign, @(1, var, e->e.t = TInt), [@(2, lt), @(3, var, e->e.t = TArray(T_UInt(currsize), 2)), @(4, var, e->e.t = TInt)]],
            e -> MPLessThanDI(@(1).val, @(3).val, @(4).val, currsize, opts));
        
        # Rule 27: 2b = 0 | 2b
        # Collect(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 2)), [@(2, bin_or), @(3, Value, e->e.v = 0), @(4, var, e->e.t = TArray(T_UInt(currsize), 2))]]);
        c := SubstBottomUp(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 2)), [@(2, bin_or), @(3, Value, e->e.v = 0), @(4, var, e->e.t = TArray(T_UInt(currsize), 2))]],
            e -> MPEqualTypeCastD(@(1).val, @(4).val, currsize, opts));
        
        # assumption: len(TInt) < blen
        # assumption: blen < int < 2*blen
        # Rule 28: 2b = TInt >> int
        # Collect(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 2)), [@(2, bin_shr), @(3, var, e->e.t = TInt), @(4, Value, e->e.v > currsize and e.v < 2*currsize)]]);
        c := SubstBottomUp(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 2)), [@(2, bin_shr), @(3, var, e->e.t = TInt), @(4, Value, e->e.v > currsize and e.v < 2*currsize)]],
            e -> MPShiftRight1I(@(1).val, @(3).val, @(4).val, currsize, opts));

        # assumption: len(TInt) < blen
        # assumption: int < blen
        # assumption: int+len(TInt) < blen
        # Rule 29: 2b = TInt << int
        # Collect(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 2)), [@(2, bin_shl), @(3, var, e->e.t = TInt), @(4, Value, e->e.v < currsize)]]);
        c := SubstBottomUp(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 2)), [@(2, bin_shl), @(3, var, e->e.t = TInt), @(4, Value, e->e.v < currsize)]],
            e -> MPShiftLeft2I(@(1).val, @(3).val, @(4).val, currsize, opts));

        # assumption: len(TInt) < blen
        # Rule 30: 2b = TInt - 2b
        # Collect(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 2)), [@(2, sub), @(3, var, e->e.t = TInt), @(4, var, e->e.t = TArray(T_UInt(currsize), 2))]]);
        c := SubstBottomUp(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 2)), [@(2, sub), @(3, var, e->e.t = TInt), @(4, var, e->e.t = TArray(T_UInt(currsize), 2))]],
            e -> MPSubDID(@(1).val, @(3).val, @(4).val, currsize, opts));

        # assumption: len(TInt) < blen
        # Rule 31: 2b = TInt - TInt
        Collect(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 2)), [@(2, sub), @(3, var, e->e.t = TInt), @(4, var, e->e.t = TInt)]]);
        c := SubstBottomUp(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 2)), [@(2, sub), @(3, var, e->e.t = TInt), @(4, var, e->e.t = TInt)]],
            e -> MPSubDII(@(1).val, @(3).val, @(4).val, currsize, opts));
        
        # Rule 32: 2b = TInt or 0/1
        c := SubstBottomUp(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 2)), [@(2, [var, Value], e->e.t = TInt)]],
            e -> MPTypeCastDI(@(1).val, @(2).val, currsize, opts));

        if useVerbose then PrintLine("60\% Done. Time spent: ", StringTime(Runtime()-time_stamp)); fi;
        
        # find assign cmds that need to be reduced
        # for dev use
        # Debug(true); Error();
        # then subst fmulqdd_l1 to fmulqddl2?
        # if opts.useMacro then
        #     cmds := c.cmds[1].cmds[1].cmds[3].cmd.cmds[1].cmd.cmds;
        #     # cmds := c.cmds[1].cmds[1].cmds[1].cmd.cmds; # for macro itself
        # else
        #     cmds := c.cmds[1].cmds[1].cmds[2].cmd.cmds[1].cmd.cmds;
        # fi;
        # list := Filtered(cmds, e->e.__bases__[1] = assign);
        # filtered_list := [];
        # for v in list do
        #     if not v.loc.t in [TInt, TBool] then Append(filtered_list, [v]);
        #     else
        #         if IsBound(v.exp.args) then
        #             flag := 0;
        #             for arg in v.exp.args do
        #                 if not arg.t in [TInt, TBool] then flag := 1; fi;
        #             od;
        #             if flag = 1 then Append(filtered_list, [v]); fi;
        #         else
        #             if not v.exp.t in [TInt, TBool] then Append(filtered_list, [v]); fi;
        #         fi;
        #     fi;
        # od;
        # list := Filtered(filtered_list, e->(not IsBound(e.exp.loc)) or (IsBound(e.exp.loc) and not e.exp.loc in [opts.barrettMu, opts.modulus]));

        # Debug Rule for printing
        c := SubstBottomUp(c, @(1, call, e->not IsNth(e.args[3])), e -> MPCallD(@(1).val.args[2], @(1).val.args[3], currsize, opts));

        if opts.useMacro then
            # duplicate l1 for l1 inside l2: TODO: this should happen before l2 breakdown -> tells l2 not to break down these
            # func_l1 := Collect(c, @(1, func, e->e.id = "MPMulQDD_L1"));
            # Append(func_l1, c.cmds[1].cmds[1].cmds);
            # c.cmds[1].cmds[1].cmds := func_l1;

            # Debug(true); Error();


            # add function implementation
            # append mpmulqdd to the main body
            # func(TVoid, "MPMulQDD", [c0, c1, c2, c3, a0, a1, b0, b1, mod0, mod1, mu0, mu1],
            # chain(MPMulQDD())
            # then I need to a function that takes 12 inputs?
            #)
            # c.cmds[1].cmds[1].cmds
            # Debug(true); Error();
            # fa := var.fresh_t("fa_", TArray(T_UInt(currsize), 2)); 
            # fb := var.fresh_t("fb_", TArray(T_UInt(currsize), 2)); 
            # fc := var.fresh_t("fc_", TArray(T_UInt(currsize), 4)); 

            # mulqdd_func := func(TVoid, "MPMulQDD", [nth(fc, 0), nth(fc, 1), nth(fc, 2), nth(fc, 3),
            #                                         nth(fa, 0), nth(fa, 1), nth(fb, 0), nth(fb, 1)],
            #                     chain(MPMulQDD(fc, fa, fb, currsize, opts))
            #                 );
            # funcs := [mulqdd_func];
            # Append(funcs, c.cmds[1].cmds[1].cmds);
            # c.cmds[1].cmds[1].cmds := funcs;
            # Collect(c, @(1, fmulqdd));
            
            # Debug(true); Error();
            # change function calls in main body
            # TODO: fix up mod and mu datatype -> I think this works now after being binsplitted -> mu and mod should not be in function arguments
            # maybe for l3 recursion I need turn off the flag in code.gi
            # then this should just work for l2 recursion
            # this is bc binsplit does not work on fmulqdd
            SubstBottomUp(c, @(1, fmulqdd_l1), e->fmulqdd_l2(nth(@(1).val.args[1], 0), nth(@(1).val.args[1], 1), nth(@(1).val.args[2], 0), nth(@(1).val.args[2], 1),
                                                             nth(@(1).val.args[3], 0), nth(@(1).val.args[3], 1), nth(@(1).val.args[4], 0), nth(@(1).val.args[4], 1),
                                                             nth(@(1).val.args[5], 0), nth(@(1).val.args[5], 1), nth(@(1).val.args[6], 0), nth(@(1).val.args[6], 1),
                                                             nth(@(1).val.args[7], 0), nth(@(1).val.args[7], 1), nth(@(1).val.args[8], 0), nth(@(1).val.args[8], 1)));
            
            # change func definition
            # func_l1 := Collect(c, @(1, func, e->e.id = "MPMulQDD_L1"))[1];
            # TODO: create func_l2's params based on func_l1
            # func_l2_params := [nth(@(1).val.args[1], 0), nth(@(1).val.args[1], 1), nth(@(1).val.args[2], 0), nth(@(1).val.args[2], 1),
            #                    nth(@(1).val.args[3], 0), nth(@(1).val.args[3], 1), nth(@(1).val.args[4], 0), nth(@(1).val.args[4], 1),
            #                    nth(@(1).val.args[5], 0), nth(@(1).val.args[5], 1), nth(@(1).val.args[6], 0), nth(@(1).val.args[6], 1),
            #                    nth(@(1).val.args[7], 0), nth(@(1).val.args[7], 1), nth(@(1).val.args[8], 0), nth(@(1).val.args[8], 1)]

           
            c := SubstBottomUp(c, @(1, func, e->e.id = "MPMulQDD_L1"), e -> func(@(1).val.ret, "MPMulQDD_L2", 
                                [nth(@(1).val.params[1], 0), nth(@(1).val.params[1], 1), nth(@(1).val.params[2], 0), nth(@(1).val.params[2], 1),
                                 nth(@(1).val.params[3], 0), nth(@(1).val.params[3], 1), nth(@(1).val.params[4], 0), nth(@(1).val.params[4], 1),
                                 nth(@(1).val.params[5], 0), nth(@(1).val.params[5], 1), nth(@(1).val.params[6], 0), nth(@(1).val.params[6], 1),
                                 nth(@(1).val.params[7], 0), nth(@(1).val.params[7], 1), nth(@(1).val.params[8], 0), nth(@(1).val.params[8], 1)], 
                                 @(1).val.cmd));

        fi;

        if useVerbose then PrintLine("70\% Done. Time spent: ", StringTime(Runtime()-time_stamp)); fi;
        
        #   1. collect via accurate conditions
        #   2. subst to function in mxpmethod.gi
        #   3. need to make sure the function is also reducible
        
        # there are two design choices
        # break down 2b or delay till 4b for reduction
        # breaking down 2b to b might hinder performance since machine already supports 2b arithmetic (by assumption)
        # but implementation-wise, 2b breakdown (i.e., reduction) might be easier
        
        # to-be-implemented list
        
        # easy
        # 4b == 1
        # 4b != 0
        # int = 4b > 4b
        
        c := FlattenCode(c);
        c := Rewrite(c, RulesStrengthReduce, opts); 

        # put X, Y in nth
        # otherwise cannot tell which nth needs to be removed/scalarized
        # Debug(true); Error();
        # cc := Collect(c, @(1, func, e->e.id = "MPMulQDD_L2"));
        c := CopyPropagate(c, opts);
        c := ForceCopyPropagate(c, opts);

        
        # X/Y/twds[i][j] -> X[i*R+j]
        # Collect(c, @(1, nth, e->IsBound(e.loc.loc))); # nth(nth(...))
        c := SubstBottomUp(c, @(1, nth, e->IsBound(e.loc.loc)), e->nth(e.loc.loc, e.loc.idx*2+e.idx));

        if useVerbose then PrintLine("80\% Done. Time spent: ", StringTime(Runtime()-time_stamp)); fi;

        # Pass to remove intermediates nths
        # Assumes that any generated nth will be consumed
            # only allow 32b and 16b
            # does not allow arrays
            # Collect(c, @(1, var, e->e.t=TArray(T_UInt(currsize), 2)));
            # Debug(true); Error();
            c := BinSplit(c, opts); 
            c := MarkDefUse(c);
        
        if useVerbose then PrintLine("83\% Done. Time spent: ", StringTime(Runtime()-time_stamp)); fi;

            # vars that can be nth'ed (will exclude them in the following lines)
            # array_vars = loop_vars::{inputs}
            # Debug(true); Error();
            array_vars := Set([X, Y, opts.twiddles, opts.barrettMu, opts.modulus]::Collect(c, @(1, var, e->IsPtrT(e.t) or (IsArrayT(e.t) and IsBound(e.t.t) and IsArrayT(e.t.t)))));
            loop_vars := Copy(array_vars); SubtractSet(loop_vars, Set([X, Y, opts.twiddles, opts.barrettMu, opts.modulus]));

            nths := Set(Collect(c, @(1, nth, e->not e.loc in array_vars)));
            tmps := [];
            for i in [1..Length(nths)] do
                Append(tmps, [var.fresh_t("t", nths[i].t)]);
            od;
            vars := Collect(c, @(1, nth, e->not e.loc in array_vars));
            c := SubstBottomUp(c, @(1, nth, e->not e.loc in array_vars), e->tmps[Position(nths, e)]);
        
        if useVerbose then PrintLine("86\% Done. Time spent: ", StringTime(Runtime()-time_stamp)); fi;

            # Debug(true); Error();
            c := FlattenCode(c);
            c := SCopyPropagate(c, opts); 
            # c := ForceCopyPropagate(c, opts); # don't need this to get correctness

        # Debug(true); Error();
        # should be no TArray(T_UInt(currsize), 2)
        # vars := Set(Collect(c, var)); # some vars are not in the actual code
        # for v in vars do
        #     PrintLine(v, ": ", v.t);
        # od;

        if useVerbose then PrintLine("90\% Done. Time spent: ", StringTime(Runtime()-time_stamp)); fi;

        # Debug(true); Error();
        # Set(Collect(c, @(1, var, e->IsArray(e.t))));

        # remove decl of arrays (not used in code)
        # not needed after first time -> move the code above to outside of loop
        # main_decl := Collect(c, @(1, decl))[1];
        # main_decl.vars := Filtered(main_decl.vars, e->not IsArray(e.t));

        # Strength Reduction
        # b >> blen -> 0
        # Collect(c, [assign, @(1), [@(2, bin_shr), @(3, var, e->e.t = T_UInt(currsize)), @(4, Value, e->e = currsize)]]);
        # c := SubstBottomUp(c, [assign, @(1), [@(2, bin_shr), @(3, var, e->e.t = T_UInt(currsize)), @(4, Value, e->e = currsize)]],
        #     e -> assign(@(1).val, V(0))); 

        # X, Y, twds' datatype now is splitted for correct function inputs' datatype
        # TPtr(TArray(T_UInt(16), 2)) -> TPtr(T_UInt(16))
        X.t := TPtr(T_UInt(currsize)).aligned([ 16, 0 ]); opts.XType := X.t;
        Y.t := TPtr(T_UInt(currsize)).aligned([ 16, 0 ]); opts.YType := Y.t;
        opts.twiddles.t := TPtr(T_UInt(currsize)).aligned([ 16, 0 ]);
        for v in loop_vars do
            v.t := TArray(T_UInt(currsize), v.t.size*(insize/currsize));
        od;

        # Debug(true); Error();

        # TODO: takes a long time
        # not compatible with debug call(apprint)
        # DIFF 2
        # c := EliminateDeadCode(c, opts);

        # Debug(true); Error();

    fi;

    # Final pass to add tcast for safe arithmetic
    # 2b = b +/* b -> 2b = (2b) b +/* (2b)
        # Debug(true);
        # Error();
        # Collect(c, [assign, @(1, var, e->e.t = T_UInt(currsize*2)), [@(2, add), @(3, var, e->e.t = T_UInt(currsize)), @(4, var, e->e.t = T_UInt(currsize))]]);
        # Collect(c, [assign, @(1, var, e->e.t = T_UInt(currsize*2)), [@(2, add), @(3), @(4)]]);
        # + 
        c := SubstBottomUp(c, [assign, @(1, var, e->e.t = T_UInt(currsize*2)), [@(2, add), @(3), @(4)]],
            e -> assign(@(1).val, add(tcast(T_UInt(currsize*2), @(2).val.args[1]), tcast(T_UInt(currsize*2), @(2).val.args[2])))); 
        # * 
        c := SubstBottomUp(c, [assign, @(1, var, e->e.t = T_UInt(currsize*2)), [@(2, mul), @(3), @(4)]],
            e -> assign(@(1).val, mul(tcast(T_UInt(currsize*2), @(2).val.args[1]), tcast(T_UInt(currsize*2), @(2).val.args[2])))); 
        # bin_shl
        # not needed as of now
        # c := SubstBottomUp(c, [assign, @(1, var, e->e.t = T_UInt(currsize*2)), [@(2, bin_shl), @(3, var, e->e.t = T_UInt(currsize)), @(4)]],
        #     e -> assign(@(1).val, mul(tcast(T_UInt(currsize*2), @(2).val.args[1]), tcast(T_UInt(currsize*2), @(2).val.args[2])))); 

   
    c := SubstBottomUp(c, @(1, func), e -> func(@(1).val.ret, @(1).val.id, @(1).val.params, Compile.declareVars(@(1).val.cmd)));
    # Debug(true); Error();

    # fix decl in mpmulqdd
    # remove extra declared vars what are function inputs
    func_list := Collect(c, @(1, func));
    for v in func_list do
        if IsBound(v.cmd.vars) then
            v.cmd.vars := Difference(v.cmd.vars, v.params);
        fi;
    od;

    if useVerbose then PrintLine("100\% Done. Time spent: ", StringTime(Runtime()-time_stamp)); fi;
    
    # Debug(true);
    c.ruletree := rt;
    return c;
end;

# made for Hybrid Key Switching
NTTXFixBigIntHKSOps := function(c, opts)
    # c := SubstTopDown(c, @(1, mul, e->ObjId(e.t) = T_UInt), e->ApplyFunc(mulmod, @(1).val.args::[opts.modulus]::
    #     When(IsBound(opts.nttxConf[1].useBarrettMult) and opts.nttxConf[1].useBarrettMult, [opts.barrettMu], []))); 
    # c := SubstBottomUp(c, @(1, add, e->ObjId(e.t) = T_UInt), e->ApplyFunc(addmod, @(1).val.args::[opts.modulus])); 
    # c := SubstBottomUp(c, @(1, sub, e->ObjId(e.t) = T_UInt), e->ApplyFunc(submod, @(1).val.args::[opts.modulus])); 

    # ReduceTempStages(c, opts);

    # FUTURE: move to rewrite.gi
    # c := SubstBottomUp(c, @(1, func, e->e.id = "transform"),
    #         e -> func(@(1).val.ret, "SwitchModulus", [X, Y, p, q], @(1).val.cmd));


    # Debug(true);
    # Error("here");

    return c;
end;
