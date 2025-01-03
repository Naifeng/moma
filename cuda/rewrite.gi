ReduceTempStages := function(c, opts)
    local vars, tmps, sfunc, main_decl, N, ins_curr, global_decl;

    # reduce temporary vectors between stages (__shared__ BigInt T*[ntt_size])
    # T{odd} -> T1
    # T{even} -> T2

    # Debug(true); Error();
    
    # HACK: grab N (dimension)
    if IsBound(opts.mxp) and opts.mxp then
        # # mxp code is binsplitted
        # ins_curr := Collect(c, [assign, @(1), mul])[1]; 
        # # assign(a2327, mul(V(8), i1))
        # N := ins_curr.exp.args[1].v;
        N := t.params[2].n;
    else
        ins_curr := Collect(c, [assign, @(1), @(2, [add, [@(3, mul), @(4), @(5, mul)]])])[1];
        #             assign( a25, add(mul(V(4096), i1), i49, mul(V(1024), i25)))
        N := ins_curr.exp.args[1].args[1].v;
    fi;

    # stage1 -> T1 -> stage2 -> T2 -> stage3 -> T1 -> ...
    # collect T*
    if IsBound(opts.mxp) and opts.mxp then
        # vars := Set(Collect(c, @(1, var, e -> e.t = TArray(T_UInt(opts.basesize), When(N<=4096, N*(opts.insize/opts.basesize), 2*N*(opts.insize/opts.basesize)))))); # Q: why 2n? special case for >= 8K
        vars := Set(Collect(c, @(1, var, e -> e.id[1] = 'T' or e.id[1] = 'P')));
    else
        # vars := Set(Collect(c, @(1, var, e -> e.t = TArray(T_UInt(1), When(N<=4096, N, 2*N))))); # Q: why 2n? special case for >= 8K
        vars := Set(Collect(c, @(1, var, e -> IsArray(e.t))));
    fi;

    tmps := []; 
    for i in [1..Length(vars)] do 
        tmps[i] := vars[imod(i+1,2).v+1]; # T1, T2
        # tmps[i] := When(imod(i,2) = 0, Y, vars[1]); # T1, Y
    od;
    c := SubstVars(c, FoldR(Zip2(vars, tmps), (a,b) -> CopyFields(a, rec((b[1].id) := b[2])), rec())); 

    # remove extra T* and Y in the main declaration
    sfunc := Collect(c, @(1, specifiers_func))[1];

    # for n <= 4K, decl is in sfunc
    # not sure why since for larger bit-width we need decl outside of sfunc for 2K or even 1K
    # otherwise outside of kernel to become __device__ memory since __shared__ memory cannot hold it anymore
    if IsBound(opts.basesize) then
    # MP/MxP
    # l1
    # if 32b, <= 4K uses shared -> nothing needs to change
    # if 64b, <= 2K uses shared -> when N = 4K, need to move
    # if 128b, <= 1K uses shared -> when N = 2K & 4K, need to move

    # l2 
    # if 64b, <= 1K uses shared -> when N = 2K, need to move
    # Debug(true); Error();
        if N <= 131072/(opts.insize * pow(2, opts.recursionLevel - 1).v) then
            # remove extra decl of T1 & T2
            main_decl := Collect(c, @(1, decl))[1]; 
            main_decl.vars := Intersection(vars, main_decl.vars); # only keep T1 & T2
        else
            global_decl := Collect(c, @(1, decl))[1];
            global_decl.vars := Set(global_decl.vars);
            
            # remove extra decl of T1 & T2
            # sfunc_decl := Collect(c, @(1, decl))[1];
            # vars := Set(sfunc_decl.vars);
            # sfunc_decl.vars := []; # remove shared memory decl

            # # # move declartion of T1 & T2 from shared memory to global memory
            # pr := Collect(c, @(1, program))[1];
            # c := program(decl(vars, pr.cmds[1]));
        fi;
    else
    # BigInt
    # FUTURE: need to merge this in to MP/MxP (above case) by adding basesize to the bigint-cuda-batch.g
        # remove extra decl of T1 & T2
        if IsBound(sfunc.cmd.vars) then 
            main_decl := Collect(c, @(1, decl))[1];
            main_decl.vars := Intersection(vars, main_decl.vars); # only keep T1 & T2
        else
            # >= 8K
            global_decl := Collect(c, @(1, decl))[1];
            global_decl.vars := Set(global_decl.vars);
        fi;
    fi;

    # Debug(true);
    # Error();

    return c;
end;

# eliminate variable assignments that are not used in the following lines of code
EliminateDeadCode := function(c, opts)

    local used_vars, assign_list, item, declared_vars, unused_vars, ret_vars, func_vars;
    
    # all the vars that are returned from func calls
    func_vars := Set(Filtered(Flat(List(Collect(c, @(1).cond(e->IsCommand(e) and IsBound(e.isMacro) and e.isMacro)), v->v.op_out())), IsVar));

    repeat
        # Debug(true); Error();
        # collect all used vars
        used_vars := [];
        assign_list := Collect(c, @(1).cond(e->IsCommand(e) and ((IsBound(e.isMacro) and e.isMacro) or (IsBound(e.__bases__[1]) and e.__bases__[1] = assign))));
        for item in assign_list do
            Append(used_vars, Difference(Set(Collect(item, var)), item.op_out()));
        od;
        
        # collect all defined vars
        declared_vars := Set(Filtered(Flat(List(assign_list, v->v.op_out())), IsVar));

        # obtain unused vars (defined - used)
        unused_vars := declared_vars;
        SubtractSet(unused_vars, Set(used_vars));
        
        # need to substract function return arguments from func definition
        ret_vars := Flat(List(Collect(c, specifiers_func), d->d.params));
        SubtractSet(unused_vars, Set(ret_vars));
        
        # Option 2
        # a7004
        # all_vars := Collect(c, var); # can I collect all var from a cmd?
        # used_vars := Set(ListDifference(all_vars, Set(all_vars)));
        # unused_vars := Set(all_vars);
        # SubtractSet(unused_vars, used_vars);

        # Debug(true); Error();
        # remove dead code
        # SubstBottomUp(c, @(1, [assign, fmulqdd_l1], e->IsSubset(unused_vars, e.op_out())), e->skip());
        SubstBottomUp(c, @(1).cond(e->IsCommand(e) and ((IsBound(e.isMacro) and e.isMacro) or (IsBound(e.__bases__[1]) and e.__bases__[1] = assign))
                            and IsSubset(unused_vars, e.op_out())), e->skip());
        c := FlattenCode(c);

        # check
        PrintLine(unused_vars);
    until Length(unused_vars) = 0 or IsSubset(func_vars, unused_vars);

    return c;
end;

EliminateDuplicateLoad := function(c, cmds, opts)
    local i, def, vars, tmps;
    
    def := cmds[1];
    vars := List(cmds, e->e.loc);
    # subvars
    # find all nth(mod, 0) to var
    tmps := [];
    for i in [1..Length(vars)] do Append(tmps, [def.loc]); od;
    for i in [1..Length(vars)] do c := SubstVars(c, rec((vars[i].id) := tmps[i])); od;

    # Collect(c, @(1, assign, e->e in Sublist(cmds, 2, Length(cmds))));
    c := SubstBottomUp(c, @(1, assign, e->e in Sublist(cmds, 2, Length(cmds))), e->skip());
    
    return c;
end;

EliminateZeroAssignment := function(c, currsize, opts)

    local cmds, vars, tmps;

    repeat 
        # Opt Rule 4: remove a = 0 and propagate to later commands
        cmds := Collect(c, @(1, assign, e->e.exp = 0));
        vars := List(cmds, e->e.exp);
        tmps := List(cmds, e->e.loc);
        c := SubstVars(c, FoldR(Zip2(tmps, vars), (a,b) -> CopyFields(a, rec((b[1].id) := b[2])), rec())); 
        c := SubstBottomUp(c, @(1, assign, e->e.loc = e.exp), e->skip());

        # Opt Rule 5: remove 0 in command add(a, 0) = a
        cmds := Collect(c, [assign, @(1, var), [@(2, add), @(3, var), @(4, Value, e->e = 0)]]);
        vars := List(cmds, e->e.exp.args[1]);
        tmps := List(cmds, e->e.loc);
        c := SubstVars(c, FoldR(Zip2(tmps, vars), (a,b) -> CopyFields(a, rec((b[1].id) := b[2])), rec())); 
        c := SubstBottomUp(c, [assign, @(1, var), [@(2, add), @(3, var), @(4, Value, e->e = 0)]], e->skip());

        # Strength Reduction
        # b >> blen -> 0
        Collect(c, [assign, @(1), [@(2, bin_shr), @(3, var, e->e.t = T_UInt(currsize)), @(4, Value, e->e = currsize)]]);
        c := SubstBottomUp(c, [assign, @(1), [@(2, bin_shr), @(3, var, e->e.t = T_UInt(currsize)), @(4, Value, e->e = currsize)]], e -> assign(@(1).val, V(0))); 

    until Length(cmds) = 0;

    return c;

end;

NCopyPropagate := function(c, opts)
    local spfunc, spfuncs;
    
    spfuncs := Collect(c, specifiers_func);
    for spfunc in spfuncs do
        SubstBottomUp(c, @(1, specifiers_func, e->e = spfunc), e -> CopyPropagate(spfunc, opts));
    od;

    return c;
end;

# scalar
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

# scalar & eval
SECopyPropagate := function(c, opts)
    
    local cmds, vars, tmps;

    repeat
        # Debug(true); Error();
        # 1. subst (a35 = t444) and (a35 = V(0))
        # 2. assign(t444 = t444) -> skip()
        cmds := Collect(c, [assign, @(1, var), [@(2, [var, Value])]]);
        vars := List(cmds, e->e.exp);
        tmps := List(cmds, e->e.loc);
        c := SubstVars(c, FoldR(Zip2(tmps, vars), (a,b) -> CopyFields(a, rec((b[1].id) := b[2])), rec())); 
        SubstBottomUp(c, @(1, assign, e->e.loc = e.exp), e->skip());
        # evaluate add/sub/mul/imod(Value, Value)
        # Debug(true); Error();
        SubstBottomUp(c, @(1, [add, sub, mul, imod], e->IsValue(e.args[1]) and IsValue(e.args[2])), e->@(1).val(@(1).val.args[1], @(1).val.args[2]));
        PrintLine("Length(cmds): ", Length(cmds));
    until Length(cmds) = 0;
    
    c := FlattenCode(c);

    return c;
end;

NSCopyPropagate := function(c, opts)
    local spfunc, spfuncs;
    
    spfuncs := Collect(c, specifiers_func);
    for spfunc in spfuncs do
        SubstBottomUp(c, @(1, specifiers_func, e->e = spfunc), e -> SCopyPropagate(spfunc, opts));
    od;

    return c;
end;

NTTXFixCUDAOps := function(c, opts)
    c := SubstTopDown(c, @(1, mul, e->ObjId(e.t) = T_UInt), e->ApplyFunc(mulmod, @(1).val.args::[opts.modulus]::
        When(IsBound(opts.nttxConf[1].useBarrettMult) and opts.nttxConf[1].useBarrettMult, [opts.barrettMu], []))); 
    c := SubstBottomUp(c, @(1, add, e->ObjId(e.t) = T_UInt), e->ApplyFunc(addmod, @(1).val.args::[opts.modulus])); 
    c := SubstBottomUp(c, @(1, sub, e->ObjId(e.t) = T_UInt), e->ApplyFunc(submod, @(1).val.args::[opts.modulus])); 

    ReduceTempStages(c, opts);

    return c;
end;

NTTXFixCUDANativeOps := function(c, opts)
    local p, vars, v, rt, declared_vars, basesize, dbasesize;

    declared_vars := Set(Filtered(List(Collect(c, assign), v->v.loc), IsVar));

    rt := When(IsBound(c.ruletree), c.ruletree, rec());
    p := opts.modulus;

    # InInt = BaseInt = 64
    # DBaseInt = 128
    basesize := opts.insize;
    dbasesize := opts.insize*2;
    
    # fix up subtractions
    # (2b) a - (2b) b + a < b ? (2b) mod : 0
    c := SubstBottomUp(c, [@(1, sub, e->ObjId(e.t) = T_UInt), @(2), @(3)],
        e -> tcast(T_Int(dbasesize), @(2).val) - tcast(T_Int(dbasesize), @(3).val) +
            cond(lt(@(2).val, @(3).val), tcast(T_Int(dbasesize), p), V(0))); 

    # Debug(true); Error();
    # fix up additions
    # c := SubstBottomUp(c, [@(1, add, e->IsBound(e.t) and e.t = opts.abstractType), @(2), @(3)],
    #     e -> cond(gt(tcast(T_Int(dbasesize), @(2).val) + tcast(T_Int(dbasesize), @(3).val), tcast(T_Int(dbasesize), opts.modulus)), 
    #                 tcast(T_Int(dbasesize), @(2).val) + tcast(T_Int(dbasesize), @(3).val) - p, 
    #                 tcast(T_Int(dbasesize), @(2).val) + tcast(T_Int(dbasesize), @(3).val))); 
    c := SubstBottomUp(c, [assign, @(1), [@(2, add, e->IsBound(e.t) and e.t = opts.abstractType), @(3), @(4) ]],
        e -> MakeAddMod(@(1).val, @(3).val, @(4).val, opts)); 

    # fix up multiplications
    c := SubstBottomUp(c, [assign, @(1), [@(2, mul, e->IsBound(e.t) and e.t = opts.abstractType), @(3), @(4) ]],
        e -> MakeBarrettMult(@(1).val, @(3).val, @(4).val, opts)); 

    # c := BinSplit(c, opts);
    # c := CSE(c);
    # c := CopyPropagate(c, opts);
   
    c := SubstVars(c, FoldR(Flat(List(List(Collect(c, @(1,cond)), e->e.args[1]), v->Collect(c, @(1, assign, e->e.loc = v)))), 
        (a,b) -> CopyFields(a, rec((b.loc.id) := b.exp)), rec()));
        
    c := FlattenCode(SubstTopDown(c, [@(1, assign), @(2, [lt, gt]), @(3)], e->skip()));

    # c := CopyPropagate.initial(c, opts);
    # c := MarkDefUse(c);
    # c := CopyPropagate(c, CopyFields(opts, rec(autoinline := true )));

    c := SubstBottomUp(c, @(1, func, e->e.id = "transform"),
        e -> func(@(1).val.ret, @(1).val.id, @(1).val.params, Compile.declareVars(@(1).val.cmd)));

    ReduceTempStages(c, opts);
    
    # declare newly added vars (q*) for each kernel code
    c := SubstBottomUp(c, @(1, specifiers_func),
        e -> specifiers_func(@(1).val.decl_specs, @(1).val.ret, @(1).val.id, @(1).val.params, 
                let(    
                        code := @(1).val.cmd,
                        _vars := Filtered(Set(ConcatList(Collect(code, @.cond(e->IsCommand(e) and IsBound(e.op_out))), e->e.op_out())), IsVar),
                        SubtractSet(_vars, declared_vars),
                        decl(_vars, code)
                    )
            ));
    
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

    

    return c;
end;

# used by mp-cuda-batch.g
NTTXFixMPCUDAOps := function(c, opts)
    local N, ins_curr, currsize;

    # Debug(true);
    # Error();

    # added for flatten code
    # c := BinSplit(c, opts); # Q: Worked but give this error: Error, IsBound: <record> must be a record
    # c := FlattenCode(c);

    currsize := opts.insize;
    currsize := currsize/2;

    # test on CPU first?

    # derived from NTTXFixMPOps

    # FUTURE: here useMacro works but not useMacro does not
    if IsBound(opts.useMacro) and opts.useMacro then
        # use macros from the library
        c := SubstBottomUp(c, @(1, mul, e->ObjId(e.t) = T_UInt), e->ApplyFunc(mulmod, @(1).val.args::[opts.modulus, opts.barrettMu])); 
        c := SubstBottomUp(c, @(1, add, e->ObjId(e.t) = T_UInt), e->ApplyFunc(addmod, @(1).val.args::[opts.modulus, opts.barrettMu])); 
        c := SubstBottomUp(c, @(1, sub, e->ObjId(e.t) = T_UInt), e->ApplyFunc(submod, @(1).val.args::[opts.modulus, opts.barrettMu])); 
    else
        # uses mpmethods defined in nttx/mpmethods.gi
        c := SubstBottomUp(c, [assign, @(1), [@(2, mul, e->IsBound(e.t) and e.t = opts.abstractType), @(3), @(4)]],
            e -> MakeModMulMP(@(1).val, @(3).val, @(4).val, currsize, opts)); 
        c := SubstBottomUp(c, [assign, @(1), [@(2, add, e->IsBound(e.t) and e.t = opts.abstractType), @(3), @(4)]],
            e -> MakeModAddMP(@(1).val, @(3).val, @(4).val, currsize, opts)); 
        c := SubstBottomUp(c, [assign, @(1), [@(2, sub, e->IsBound(e.t) and e.t = opts.abstractType), @(3), @(4)]],
            e -> MakeModSubMP(@(1).val, @(3).val, @(4).val, currsize, opts)); 
    fi;

    c := FlattenCode(c);
    # # PrintCode("", c, opts);

    # HACK: grab N (dimension)
    ins_curr := Collect(c, [assign, @(1), @(2, [add, [@(3, mul), @(4), @(5, mul)]])])[1]; # assign( a25, add(mul(V(4096), i1), i49, mul(V(1024), i25)))
    N := ins_curr.exp.args[1].args[1].v;
    
    c := ReduceTempStages(c, opts);

    # Debug(true);
    # Error();

    # remove double declared vars
    SubstBottomUp(c, @(1, decl, e -> e.vars[1].t = TInt), e -> decl([], @(1).val.cmd));

    c := Rewrite(c, RulesStrengthReduce, opts); 
    # c := BinSplit(c, opts); # not work for CUDA code Q: why?
    # c := CSE(c); # not working for MPMod
    
    # copypropate is wrong if multiple specifiers_func exists
    # using NCopyPropagate that works for multiple specifiers_func
    # Debug(true); Error();
    c := NCopyPropagate(c, opts); 
    # # c := CopyPropagate.initial(c, opts); # not working for MPMod
    c := MarkDefUse(c);
    c := NCopyPropagate(c, CopyFields(opts, rec(autoinline := true)));

    # decl vars
    SubstBottomUp(c, @(1, specifiers_func), 
        e -> specifiers_func(@(1).val.decl_specs, @(1).val.ret, @(1).val.id, @(1).val.params, Compile.declareVars(@(1).val.cmd)));    

    return c;
end;

# used by mp-cuda-batch.g
# copy from NTTXFixMxPOps (CPU) with few modifications
NTTXFixMxPCUDAOps := function(c, opts)
    local N, ins_curr, p, vars, v, rt, currsize, ins, nths, tmps, cmds, cmd,
    muls, mul_vars, add_vars, sub_vars, array_vars, loop_vars, twd_decl,
    main_func, spfunc, useVerbose, time_stamp, fa, fb, fc, mulqdd_func,
    useOptm, spfuncs, ret_vars, func_list, tmp1, tmp2, j, loop1, genBLAS,
    currRecur, cc, exps, cutsize, n_elm, n_off;

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
    # Collect by cond, BinSplit
    spfunc := Collect(c, specifiers_func);
    spfunc := BinSplit(spfunc, opts);
    # Debug(true); Error();
    c := NCopyPropagate(c, opts);

    # modular BLAS: only testing for one ins
    # set n := 4 in mp-cuda-batch.g
    genBLAS := false;
    if genBLAS then

        # Debug(true); Error();
    
        ins := c.cmds[1].cmds[2].cmds[1].cmds[1].cmd.cmds[1].cmd.cmds[1].cmd.cmds;
        ins := Sublist(ins, 1, 2);
        c.cmds[1].cmds[2].cmds[1].cmds[1].cmd.cmds[1].cmd.cmds[1].cmd.cmds := ins;
        ins := c.cmds[1].cmds[2].cmds[1].cmds[1].cmd.cmds[1].cmd.cmds[1].cmd.cmds[1].cmd.cmds[1].cmd.cmds;
        
        # vvmul: Y[i] = X[i] * twd[i]
        # ins := Sublist(ins, 1, 2)::[assign(nth(Y, var.table.a54), mul(nth(X, var.table.a54), nth(opts.twiddles, var.table.a54)))];
        
        # vvadd: Y[i] = X[i] + twd[i]
         #ins := Sublist(ins, 1, 2)::[assign(nth(Y, var.table.a54), add(nth(X, var.table.a54), nth(opts.twiddles, var.table.a54)))];
        
        # vvsub: Y[i] = X[i] - twd[i]
        # ins := Sublist(ins, 1, 2)::[assign(nth(Y, var.table.a54), sub(nth(X, var.table.a54), nth(opts.twiddles, var.table.a54)))];
        
        # axpy: Y[i] = twd[0] * X[i] + twd[i]
         #ins := Sublist(ins, 1, 2)::[assign(nth(Y, var.table.a54), add(mul(nth(X, var.table.a54), nth(opts.twiddles, 0)), nth(opts.twiddles, var.table.a54)))];
        
        c.cmds[1].cmds[2].cmds[1].cmds[1].cmd.cmds[1].cmd.cmds[1].cmd.cmds[1].cmd.cmds[1].cmd.cmds := ins;
        
        # Debug(true); Error();

        # set for parallelization
        var.table.b3.x.value := 1024/pow(2, opts.recursionLevel-1);
        SubstBottomUp(c, @(1, Value, e->e.v = 4), e-> V(1024/pow(2, opts.recursionLevel-1)));

    fi;

    # -------------------------------- First Pass --------------------------------
    # 64b -> 64b & 32b, with 16b Base

    currsize := opts.insize/2;

    # Debug(true); Error();

    spfunc := Collect(c, specifiers_func);
    spfunc := BinSplit(spfunc, opts);

    # now everything is binsplitted, continue here

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
    
    # type: TArray(T_UInt(2b), Value) -> TArray(TArray(T_UInt(b), 2), Value)
    vars := Collect(c, @(1, var, e->IsBound(e.t.t) and e.t.t=T_UInt(currsize*2)));
    for v in vars do
        v.t.t := TArray(T_UInt(currsize), 2);
    od;
    opts.modulus.t := TArray(T_UInt(currsize), 2);
    opts.barrettMu.t := TArray(T_UInt(currsize), 2);

    # -------- align point 1 --------

    # inspect datatype
    # all datatypes should be TArray(T_UInt(currsize), 2) or TInt
    vars := Set(Collect(c, var));
    for v in vars do
        PrintLine(v, ": ", v.t);
    od;

    # initial mul, add & sub
    # used for SubstBottomUp
    muls := Collect(c, [assign, @(1), [@(2, mul, e->IsBound(e.t) and e.t = opts.abstractType), @(3), @(4)]]);
    mul_vars := List(muls, e->e.loc);
    adds := Collect(c, [assign, @(1), [@(2, add, e->IsBound(e.t) and e.t = opts.abstractType), @(3), @(4)]]);
    add_vars := List(adds, e->e.loc);
    subs := Collect(c, [assign, @(1), [@(2, sub, e->IsBound(e.t) and e.t = opts.abstractType), @(3), @(4)]]);
    sub_vars := List(subs, e->e.loc);

    # Debug(true); Error();
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

    # -------- align point 2 --------
    
    if opts.useMacro then
        # add function implementation
        # append mpmulqdd to the main body
        # func(TVoid, "MPMulQDD", [c0, c1, c2, c3, a0, a1, b0, b1, mod0, mod1, mu0, mu1],
        # chain(MPMulQDD())
        # then I need to a function that takes 12 inputs?
        #)
        # c.cmds[1].cmds[1].cmds
        # 
        fa := var.fresh_t("fa_", TArray(T_UInt(currsize), 2)); 
        fb := var.fresh_t("fb_", TArray(T_UInt(currsize), 2)); 
        fc := var.fresh_t("fc_", TArray(T_UInt(currsize), 4)); 
        # 
        mulqdd_func := specifiers_func(["__device__"], TVoid, "MPMulQDD_L1", [nth(fc, 0), nth(fc, 1), nth(fc, 2), nth(fc, 3),
                                                nth(fa, 0), nth(fa, 1), nth(fb, 0), nth(fb, 1)],
                            chain(opts.mulqdd(fc, fa, fb, currsize, opts))
                        );
        c := SubstBottomUp(c, @(1, func, e->e.id = "init"), e->chain(mulqdd_func, @(1).val));
        # funcs := [mulqdd_func];
        # Debug(true); Error();
        # Append(funcs, c.cmds[1].cmds);
        # # c.cmds[1].cmd.cmds > 4096
        # Collect(c, @(1, chain, e->e))
        # c.cmds[1].cmds := funcs;
    fi;

    if useVerbose then PrintLine("10\% Done. Time spent: ", StringTime(Runtime()-time_stamp)); fi;

    c := FlattenCode(c);
    c := Rewrite(c, RulesStrengthReduce, opts); 
        
    # put X, Y in nth
    # otherwise cannot tell which nth needs to be removed/scalarized
    # Debug(true); Error();
    c := NCopyPropagate(c, opts);
    c := ForceCopyPropagate(c, opts);

    # X/Y/twds[i][j] -> X[i*R+j]
    # Collect(c, @(1, nth, e->IsBound(e.loc.loc))); # nth(nth(...))
    c := SubstBottomUp(c, @(1, nth, e->IsBound(e.loc.loc)), e->nth(e.loc.loc, e.loc.idx*2+e.idx));
    
    # -------- align point 3 --------

    # Pass to remove intermediates nths
    # Assumes that any generated nth will be consumed
        # only allow 32b and 16b
        # does not allow arrays
        # Collect(c, @(1, var, e->e.t=TArray(T_UInt(currsize), 2)));
        # c.cmds[1].cmds[1].cmds[2] := BinSplit(c.cmds[1].cmds[1].cmds[2], opts);
        spfunc := Collect(c, specifiers_func);
        spfunc := BinSplit(spfunc, opts);
        c := MarkDefUse(c);

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
        
        c := FlattenCode(c);
        c := SCopyPropagate(c, opts);
        c := ForceCopyPropagate(c, opts);

    # should be no TArray(T_UInt(currsize), 2)
    # vars := Set(Collect(c, var)); # some vars are not in the actual code
    # for v in vars do
    #     PrintLine(v, ": ", v.t);
    # od;

    # DIFF 2
    # remove vars in decl, only keep T*
    # list := Collect(c, decl);
    # for v in list do
    #     v.vars := Filtered(v.vars, e->IsArray(e.t) and IsBound(e.t.t) and IsArray(e.t.t));
    # od;

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
    # Opt Rule 2
    c := EliminateDeadCode(c, opts);

    # -------------------------------- Second & Up Passes --------------------------------
    
    cutsize := 0;
    
    if opts.recursionLevel > 1 then
        currRecur := 1;
        
        repeat
            # update recursionlevel
            currRecur := currRecur + 1;

            if useVerbose then PrintLine("Starting recursion level ", currRecur); fi;
            
            # 64b & 32b -> 32b & 16b, with 16b Base
            
            opts.basesize := opts.basesize/2;
            currsize := currsize/2;
            # currtype := T_UInt(currsize);
            # TArray(T_UInt(current), 4)

            # Y datatype error
            # Y.t := TPtr(TArray(T_UInt(currsize), 2)).aligned([ 16, 0 ]);
            
            # BinSplit is not working for all X, and twiddles related
            # Debug(true); Error();
            
            spfunc := Collect(c, specifiers_func);
            # fix ldepth used by BinSplit
            # assign(a76, add(V(2), a75))
            vars := Collect(c, @(1, var, e->not IsBound(e.ldepth)));
            for v in vars do
                v.ldepth := 0;
            od;
            spfunc := BinSplit(spfunc, opts);
            
            # fix BinSplit
            vars := Set(Collect(c, @(1, var, e->IsArray(e.t) and e.id[1] <> 'T' and e.id[1] <> 'P')));
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

            # -------- align point 1 --------
            
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

            # Debug(true); Error();

            # fix datatype of nth()
            vars := Collect(c, @(1, nth, e->e.t <> e.computeType()));
            for v in vars do
                v.t := v.computeType();
            od;

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
                e -> opts.mulqdd(@(1).val, @(3).val, @(4).val, currsize, opts));
            
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

            # Debug(true); Error();
            # assumption: @(1) must be 2b; does not explicitly check because of nth(Y, *)
            # Rule 17: 2b = TBool/(0/1) ? 2b : 2b
            # Collect(c, [assign, @(1), [@(2, cond), @(3, var, e->e.t = TInt), @(4, var, e->e.t = TArray(T_UInt(currsize), 2)), @(5, var, e->e.t = TArray(T_UInt(currsize), 2))]]);
            c := SubstBottomUp(c, [assign, @(1), [@(2, cond), @(3, var, e->e.t in [TBool, TInt]), @(4, var, e->e.t = TArray(T_UInt(currsize), 2)), @(5, var, e->e.t = TArray(T_UInt(currsize), 2))]],
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
            # Collect(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 2)), [@(2, sub), @(3, var, e->e.t = TInt), @(4, var, e->e.t = TInt)]]);
            c := SubstBottomUp(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 2)), [@(2, sub), @(3, var, e->e.t = TInt), @(4, var, e->e.t = TInt)]],
                e -> MPSubDII(@(1).val, @(3).val, @(4).val, currsize, opts));
            
            # Rule 32: 2b = TInt or 0/1
            c := SubstBottomUp(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 2)), [@(2, [var, Value], e->e.t = TInt)]],
                e -> MPTypeCastDI(@(1).val, @(2).val, currsize, opts));

            # Debug(true); Error();

            # Rule 33: TBool = int < 2b
            # Collect(c, [assign, @(1, var, e->e.t = TBool), [@(2, lt), @(3, Value, e->e.t = TInt), @(4, var, e->e.t = TArray(T_UInt(currsize), 2))]]);
            c := SubstBottomUp(c, [assign, @(1, var, e->e.t = TBool), [@(2, lt), @(3, Value, e->e.t = TInt), @(4, var, e->e.t = TArray(T_UInt(currsize), 2))]],
                e -> MPLessThanID(@(1).val, @(3).val, @(4).val, currsize, opts));

            # Rule 34: TBool = 2b == int
            # Collect(c, [assign, @(1, var, e->e.t = TBool), [@(2, eq), @(3, var, e->e.t = TArray(T_UInt(currsize), 2)), @(4, Value, e->e.t = TInt)]]);
            c := SubstBottomUp(c, [assign, @(1, var, e->e.t = TBool), [@(2, eq), @(3, var, e->e.t = TArray(T_UInt(currsize), 2)), @(4, Value, e->e.t = TInt)]],
                e -> MPEqualDI(@(1).val, @(3).val, @(4).val, currsize, opts));

            # Rule 35: 4b = 4b + 4b
            c := SubstBottomUp(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 4)), [@(2, add), @(3, var, e->e.t = TArray(T_UInt(currsize), 4)), @(4, var, e->e.t = TArray(T_UInt(currsize), 4))]],
                e -> MPAddQQQ(@(1).val, @(3).val, @(4).val, currsize, opts));

            # Rule 36: 4b = 4b + 2b
            c := SubstBottomUp(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 4)), [@(2, add), @(3, var, e->e.t = TArray(T_UInt(currsize), 4)), @(4, var, e->e.t = TArray(T_UInt(currsize), 2))]],
                e -> MPAddQQD(@(1).val, @(3).val, @(4).val, currsize, opts));

            # assumption: all TInt (involved in computation, not shift) is actually 0/1
            # Rule 37: 4b = 0/1 + 2b
            # Collect(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 4)), [@(2, add), @(3, var, e->e.t = TArray(T_UInt(currsize), 2)), @(4, var, e->e.t = TInt)]]);
            c := SubstBottomUp(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 4)), [@(2, add), @(3, var, e->e.t = TArray(T_UInt(currsize), 2)), @(4, var, e->e.t = TInt)]],
                e -> MPAddQID(@(1).val, @(4).val, @(3).val, currsize, opts));

            # assumption: all TInt (involved in computation, not shift) is actually 0/1
            # Rule 38: 2b = 2b + 0/1
            # Collect(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 2)), [@(2, add), @(3, var, e->e.t = TArray(T_UInt(currsize), 2)), @(4, var, e->e.t = TInt)]]);
            c := SubstBottomUp(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 2)), [@(2, add), @(3, var, e->e.t = TArray(T_UInt(currsize), 2)), @(4, var, e->e.t = TInt)]],
                e -> MPAddDDI(@(1).val, @(3).val, @(4).val, currsize, opts));

            # Debug(true); Error();

            # assumption: all TInt (involved in computation, not shift) is actually 0/1
            # Rule 39: 2b = 0/1 + 2b
            # Collect(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 2)), [@(2, add), @(3, var, e->e.t = TInt), @(4, var, e->e.t = TArray(T_UInt(currsize), 2))]]);
            c := SubstBottomUp(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 2)), [@(2, add), @(3, var, e->e.t = TInt), @(4, var, e->e.t = TArray(T_UInt(currsize), 2))]],
                e -> MPAddDDI(@(1).val, @(4).val, @(3).val, currsize, opts));
            
            # assumption: all TInt (involved in computation, not shift) is actually 0/1
            # Rule 40: 2b = 0/1 + 0/1
            # Collect(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 2)), [@(2, add), @(3, var, e->e.t = TInt), @(4, var, e->e.t = TInt)]]);
            c := SubstBottomUp(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 2)), [@(2, add), @(3, var, e->e.t = TInt), @(4, var, e->e.t = TInt)]],
                e -> MPAddDII(@(1).val, @(3).val, @(4).val, currsize, opts));
            
            # Rule 41: 2b = TBool ? 2b : int
            c := SubstBottomUp(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 2)), [@(2, cond), @(3, var, e->e.t in [TBool]), @(4, var, e->e.t = TArray(T_UInt(currsize), 2)), @(5, var, e->e.t = TInt)]],
                e -> MPCondDDI(@(1).val, @(3).val, @(4).val, @(5).val, currsize, opts));

            # Rule 42: TBool/TInt = 2b < 1
            c := SubstBottomUp(c, [assign, @(1, var, e->e.t in [TBool, TInt]), [@(2, lt), @(3, var, e->e.t = TArray(T_UInt(currsize), 2)), @(4, Value, e->e.v = V(1))]],
                e -> MPLessThanDI(@(1).val, @(3).val, @(4).val, currsize, opts));

            # Rule 43: TBool/TInt = 2b < TInt
            c := SubstBottomUp(c, [assign, @(1, var, e->e.t in [TBool, TInt]), [@(2, lt), @(3, var, e->e.t = TArray(T_UInt(currsize), 2)), @(4, var, e->e.t = TInt)]],
                e -> MPLessThanDI(@(1).val, @(3).val, @(4).val, currsize, opts));

            # Rule 44: 2b = TBool ? 2b : Value
            c := SubstBottomUp(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 2)), [@(2, cond), @(3, var, e->e.t in [TBool]), @(4, var, e->e.t = TArray(T_UInt(currsize), 2)), @(5, Value)]],
                e -> MPCondDDI(@(1).val, @(3).val, @(4).val, @(5).val, currsize, opts));

            # Rule 45: 2b = -(0/1)
            # used for l3 karatsuba
            c := SubstBottomUp(c, [assign, @(1, var, e->e.t = TArray(T_UInt(currsize), 2)), [@(2, neg), @(3, var, e->e.t = TInt)]],
                e -> MPTypeCastDI(@(1).val, @(2).val, currsize, opts));

            if useVerbose then PrintLine("60\% Done. Time spent: ", StringTime(Runtime()-time_stamp)); fi;
            
            # find assign cmds that need to be reduced
            # for dev use
            # if currRecur = 3 then
            #     # Debug(true); Error();
            #     if opts.useMacro then
            #         cmds := c.cmds[1].cmds[1].cmds[3].cmd.cmds[1].cmd.cmds;
            #         # cmds := c.cmds[1].cmds[1].cmds[1].cmd.cmds; # for macro itself
            #         # cmds := c.cmds[1].cmd.cmds[1].cmd.cmds;
            #     else
            #         # l2: single kernel without macro
            #         cmds := c.cmds[1].cmds[2].cmd.cmds[1].cmd.cmds[1].cmd.cmds[1].cmd.cmds[1].cmd.cmds;
            #         # cmds := c.cmds[1].cmds[2].cmds[1].cmd.cmds[1].cmd.cmds[1].cmd.cmds[1].cmd.cmds[1].cmd.cmds;
            #     fi;
            #     list := Filtered(cmds, e->e.__bases__[1] = assign);
            #     filtered_list := [];
            #     for v in list do
            #         if not v.loc.t in [TInt, TBool] then Append(filtered_list, [v]);
            #         else
            #             if IsBound(v.exp.args) then
            #                 flag := 0;
            #                 for arg in v.exp.args do
            #                     # if there is any arg that is not TInt or TBool
            #                     if IsBound(arg.t) and not arg.t in [TInt, TBool] then flag := 1; fi;
            #                 od;
            #                 if flag = 1 then Append(filtered_list, [v]); fi;
            #             else
            #                 if not v.exp.t in [TInt, TBool] then Append(filtered_list, [v]); fi;
            #             fi;
            #         fi;
            #     od;
            #     list := Filtered(filtered_list, e->(not IsBound(e.exp.loc)) or (IsBound(e.exp.loc) and not e.exp.loc in [opts.barrettMu, opts.modulus]));
            #     Debug(true); Error();
            # fi;

            # Debug Rule for printing
            c := SubstBottomUp(c, @(1, call, e->not IsNth(e.args[3])), e -> MPCallD(@(1).val.args[2], @(1).val.args[3], currsize, opts));

            # -------- align point 2 --------

            if opts.useMacro then
                
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
                
                if currRecur = 2 then
                    # Debug(true); Error();
                    # change function calls in main body
                    # mu and mod should not be in function arguments: binsplit on fmulqdd guarantees this
                    c := SubstBottomUp(c, @(1, fmulqdd_l1), e->ApplyFunc(fmulqdd_l2, Concatenation(List([1..pow(2, currRecur+1).v], i -> [nth(@(1).val.args[i], 0), nth(@(1).val.args[i], 1)]))));
                    c := SubstBottomUp(c, @(1, specifiers_func, e->e.id = "MPMulQDD_L1"), e -> specifiers_func(["__device__"], @(1).val.ret, "MPMulQDD_L2", 
                                        Concatenation(List([1..pow(2, currRecur+1).v], i -> [nth(@(1).val.params[i], 0), nth(@(1).val.params[i], 1)])), 
                                        @(1).val.cmd));
                elif currRecur = 3 then
                    # Debug(true); Error();
                    c := SubstBottomUp(c, @(1, fmulqdd_l2), e->ApplyFunc(fmulqdd_l3, Concatenation(List([1..pow(2, currRecur+1).v], i -> [nth(@(1).val.args[i], 0), nth(@(1).val.args[i], 1)]))));
                    c := SubstBottomUp(c, @(1, specifiers_func, e->e.id = "MPMulQDD_L2"), e -> specifiers_func(["__device__"], @(1).val.ret, "MPMulQDD_L3", 
                                        Concatenation(List([1..pow(2, currRecur+1).v], i -> [nth(@(1).val.params[i], 0), nth(@(1).val.params[i], 1)])), 
                                        @(1).val.cmd));
                elif currRecur = 4 then
                    # Debug(true); Error();
                    c := SubstBottomUp(c, @(1, fmulqdd_l3), e->ApplyFunc(fmulqdd_l4, Concatenation(List([1..pow(2, currRecur+1).v], i -> [nth(@(1).val.args[i], 0), nth(@(1).val.args[i], 1)]))));
                    c := SubstBottomUp(c, @(1, specifiers_func, e->e.id = "MPMulQDD_L3"), e -> specifiers_func(["__device__"], @(1).val.ret, "MPMulQDD_L4", 
                                        Concatenation(List([1..pow(2, currRecur+1).v], i -> [nth(@(1).val.params[i], 0), nth(@(1).val.params[i], 1)])), 
                                        @(1).val.cmd));
                fi;

            fi;

            if useVerbose then PrintLine("70\% Done. Time spent: ", StringTime(Runtime()-time_stamp)); fi;
            
            # there are two design choices
            # break down 2b or delay till 4b for reduction
            # breaking down 2b to b might hinder performance since machine already supports 2b arithmetic (by assumption)
            # but implementation-wise, 2b breakdown (i.e., reduction) might be easier
            
            c := FlattenCode(c);
            c := Rewrite(c, RulesStrengthReduce, opts); 

            # put X, Y in nth
            # otherwise cannot tell which nth needs to be removed/scalarized
            # Debug(true); Error();
            c := NCopyPropagate(c, opts); # needed for code gen.
            c := ForceCopyPropagate(c, opts); 

            # X/Y/twds[i][j] -> X[i*R+j]
            # Collect(c, @(1, nth, e->IsBound(e.loc.loc))); # nth(nth(...))
            c := SubstBottomUp(c, @(1, nth, e->IsBound(e.loc.loc)), e->nth(e.loc.loc, e.loc.idx*2+e.idx));

            # -------- align point 3 --------

            if useVerbose then PrintLine("80\% Done. Time spent: ", StringTime(Runtime()-time_stamp)); fi;

            # Pass to remove intermediates nths
            # Assumes that any generated nth will be consumed
                # only allow 32b and 16b
                # does not allow arrays
                # Collect(c, @(1, var, e->e.t=TArray(T_UInt(currsize), 2)));
                # c := BinSplit(c, opts); 
                spfunc := Collect(c, specifiers_func);
                spfunc := BinSplit(spfunc, opts);
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

            # X, Y, twds' datatype now is splitted for correct function inputs' datatype
            # TPtr(TArray(T_UInt(16), 2)) -> TPtr(T_UInt(16))
            X.t := TPtr(T_UInt(currsize)).aligned([ 16, 0 ]); opts.XType := X.t;
            Y.t := TPtr(T_UInt(currsize)).aligned([ 16, 0 ]); opts.YType := Y.t;
            opts.twiddles.t := TPtr(T_UInt(currsize)).aligned([ 16, 0 ]);
            for v in loop_vars do
                v.t := TArray(T_UInt(currsize), v.t.size*(insize/currsize));
            od;

            # bit-reduction
            # calculate in which recursionLevel this should happen
            cutsize := cutsize + currsize;
            if (insize - cutsize) > opts.mbits then
                # if currRecur = 3 then Debug(true); Error(); fi;
                # there is room to cut the extra currsize (i.e., cutsize in total)
                
                # Debug(true); Error();

                # In 96b = 3 * 32b
                # code reduction for arbitrary InInt bit-width
                # 1. track every first element of X, modulus, mu, and twds
                # 2. set them to 0
                # 3. trust copypropagation

                # the 0th out of n elements to be removed
                # 4: [x, x, x, x] -> [0, x, x, x] l2
                # 8: [x, x, x, x, x, x, x, x] -> [0, x, x, x, x, x, x, x] l3
                n_elm := pow(2, currRecur).v;
                # offset
                # 4: [x, x, x, x] -> [0, x, x, x] l2 then
                # 8 + 2: [0, 0, x, x, x, x, x, x] -> [0, 0, 0, x, x, x, x, x] l3
                n_off := (cutsize / currsize) - 1;
                
                # cut off the first element
                # modulus
                SubstBottomUp(c, [assign, @(1), [@(2, nth), @(3, var, e->e = opts.modulus), @(4, Value, e->e.v = n_off)]], e->assign(@(1).val, V(0)));
                # mu
                SubstBottomUp(c, [assign, @(1), [@(2, nth), @(3, var, e->e = opts.barrettMu), @(4, Value, e->e.v = n_off)]], e->assign(@(1).val, V(0)));
                
                # X
                # set i2 = 0 (blockId.x = 0) # for batch NTT
                # set i5 = 0 (threadId.x = 0) # for each btfy
                # 4-point NTT -> 2 btfys -> 2 threads
                # each thread handles one btfy -> 2 X -> 8 BaseInt
                # I need to set two X[0] and X[4] to 0
                # collect every cmd that has i* as an argument
                cc := Copy(c);
                # Debug(true); Error();
                vars := List(Collect(cc, @(1, [simt_loop, loop])),  e->e.var);
                # set i* to 0
                SubstBottomUp(cc, [assign, @(1), [@(2), @(3), @(4, var, e->e in vars)]], e->assign(@(1).val, @(2).val(@(3).val, V(0))));
                SubstBottomUp(cc, [assign, @(1), [@(2), @(3, var, e->e in vars), @(4)]], e->assign(@(1).val, @(2).val(V(0), @(4).val)));
                # copyprop. the values
                cc := SECopyPropagate(cc, opts);
                # record the vars in c that needs to be sent to 0 using cc
                vars := List(Collect(cc, [assign, @(1), [@(2, nth), @(3, var, e->e = X), @(4, Value, e->imod(e, n_elm) = n_off)]]), e->e.loc);
                SubstBottomUp(c, [assign, @(1, var, e->e in vars), [@(2, nth), @(3, var, e->e = X), @(4)]], e->assign(@(1).val, V(0)));
                # Collect(cc, @(1, nth, e->e.loc = X));
                # Collect(c, @(1, nth, e->e.loc = X));

                # twiddles
                # do the same for twiddles (like X)
                vars := List(Collect(cc, [assign, @(1), [@(2, nth), @(3, var, e->e = opts.twiddles), @(4, Value, e->imod(e, n_elm) = n_off)]]), e->e.loc);
                SubstBottomUp(c, [assign, @(1, var, e->e in vars), [@(2, nth), @(3, var, e->e = opts.twiddles), @(4)]], e->assign(@(1).val, V(0)));
                
                # T*
                # T1 also has values copyprop'ed
                # just reduce all T1[mod 4 = 0] when loading from T1 (like X)
                vars := List(Collect(cc, [assign, @(1), [@(2, nth), @(3, var, e->e.id[1] in ['T', 'P']), @(4, Value, e->imod(e, n_elm) = n_off)]]), e->e.loc);
                SubstBottomUp(c, [assign, @(1, var, e->e in vars), [@(2, nth), @(3, var, e->e.id[1] in ['T', 'P']), @(4)]], e->assign(@(1).val, V(0)));
                # when storing to T1, those values should not matter as it is 0; (like Y)
                # EliminateDeadCode should take care of pruning them
                exps := List(Collect(cc, [assign, [@(1, nth), @(2, var, e->e.id[1] in ['T', 'P']), @(3, Value, e->imod(e, n_elm) = n_off)], @(4)]), e->e.exp);
                SubstBottomUp(c, @(1, assign, e->e.exp in exps), e->skip());

                # Y
                # when storing to Y, those values should not matter as it is 0; 
                # EliminateDeadCode should take care of pruning them
                exps := List(Collect(cc, [assign, [@(1, nth), @(2, var, e->e = Y), @(3, Value, e->imod(e, n_elm) = n_off)], @(4)]), e->e.exp);
                SubstBottomUp(c, @(1, assign, e->e.exp in exps), e->skip());

                # Debug(true); Error();

                c := EliminateDeadCode(c, opts);
            else
                # undo the addition
                cutsize := cutsize - currsize;
            fi;
        
        until currRecur = opts.recursionLevel;
    fi;

    # -------------------------------- End of Passes --------------------------------

    # Optimization Rules
    useOptm := true;
    if useOptm then
        # Debug(true); Error();
        # Strength Reduction
        # b >> blen -> 0
        # Collect(c, [assign, @(1), [@(2, bin_shr), @(3, var, e->e.t = T_UInt(currsize)), @(4, Value, e->e = currsize)]]);
        # c := SubstBottomUp(c, [assign, @(1), [@(2, bin_shr), @(3, var, e->e.t = T_UInt(currsize)), @(4, Value, e->e = currsize)]],
        #     e -> assign(@(1).val, V(0))); 

        # Opt Rule 4-5
        c := EliminateZeroAssignment(c, currsize, opts);
        
        # Opt Rule 10
        # (0-1) -> -1
        SubstBottomUp(c, [assign, @(1, var), [@(2, sub), @(3, Value, e->e = 0), @(4, Value, e->e = 1)]], e->assign(@(1).val, -1));
        
        # Opt Rule 7 remove a = 1 and propagate to later commands
        # t1392 = 1;
        cmds := Collect(c, @(1, assign, e->e.exp = 1));
        vars := List(cmds, e->e.exp);
        tmps := List(cmds, e->e.loc);
        c := SubstVars(c, FoldR(Zip2(tmps, vars), (a,b) -> CopyFields(a, rec((b[1].id) := b[2])), rec())); 
        c := SubstBottomUp(c, @(1, assign, e->e.loc = e.exp), e->skip());
        
        # Opt Rule 8
        # t1389 = (1 << 57);
        # no need for MK
        # spfuncs := Collect(c, specifiers_func);
        # # assign(t647, bin_shl(V(1), V(50))),
        # for spfunc in spfuncs do
        #     cmds := Collect(spfunc, [assign, @(1), [@(2, bin_shl), @(3, Value, e->e = 1), @(4, Value)]]);
        #     if Length(cmds) > 0 then EliminateDuplicateLoad(spfunc, cmds, opts); fi;
        # od;

        # Opt Rule 9
        # Debug(true); Error();
        # t2015 = (((t1397)|(0)));
        SubstBottomUp(c, [assign, @(1), [@(2, bin_or), @(3), @(4, Value, e->e = 0)]], e->assign(@(1).val, @(3).val));
        SubstBottomUp(c, [assign, @(1), [@(2, bin_or), @(3, Value, e->e = 0), @(4)]], e->assign(@(1).val, @(4).val));

        # option 2: evaluate comparisons right here
        # Debug(true); Error();
        # c := FlattenCode(c);
        # repeat 
        #     cmds := Collect(c, [assign, @(1, var), [@(2, [lt, gt, eq, logic_and, logic_or]), @(3, Value), @(4, Value)]]);
            
        #     for cmd in cmds do
        #         # can directly eval. lt, gt, and eq
        #         tmps := [cmd.loc];
        #         # evaluation
        #         if cmd.exp.__bases__[1] = logic_and then
        #             if cmd.exp.args = [V(1), V(1)] then r := V(1);
        #             else r := V(0); fi;
        #         elif cmd.exp.__bases__[1] = logic_or then
        #             if cmd.exp.args = [V(0), V(0)] then r := V(0);
        #             else r := V(1); fi;
        #         else
        #             if cmd.exp.ev() then r := V(1);
        #             else r := V(0); fi;
        #         fi;
        #         vars := [r];
        #         c := SubstVars(c, FoldR(Zip2(tmps, vars), (a,b) -> CopyFields(a, rec((b[1].id) := b[2])), rec())); 
        #         c := SubstBottomUp(c, @(1, assign, e->e.loc = r), e->skip());
        #     od;
            
        #     # Debug(true); Error();
        #     # any comparison cmd with both explicit args
        #     cmds := Collect(c, [assign, @(1, var), [@(2, [lt, gt, eq, logic_and, logic_or]), @(3, Value), @(4, Value)]]);
        # until Length(cmds) = 0;
        
        # Opt Rule 6
        # manually evaluate comparison
        # b12 = ((0 < 1)) -> (b12 -> 1)
        # this solves: operations difference of integer and boolean is not defined for l2
        # cmds := Collect(c, [assign, @(1, var), [@(2, lt), @(3, Value, e->e = 0), @(4, Value, e->e = 1)]]);
        # tmps := List(cmds, e->e.loc);
        # vars := [];
        # for i in [1..Length(tmps)] do Append(vars, [V(1)]); od;
        # c := SubstVars(c, FoldR(Zip2(tmps, vars), (a,b) -> CopyFields(a, rec((b[1].id) := b[2])), rec())); 
        # c := SubstBottomUp(c, @(1, assign, e->e.loc = V(1)), e->skip());

        # manually eval eq but introduces another error: <expr> must evaluate to 'true' or 'false'
        # cmds := Collect(c, [assign, @(1, var), [@(2, eq), @(3, Value, e->e = 0), @(4, Value, e->e = 0)]]);
        # tmps := List(cmds, e->e.loc);
        # vars := [];
        # for i in [1..Length(tmps)] do Append(vars, [V(1)]); od;
        # c := SubstVars(c, FoldR(Zip2(tmps, vars), (a,b) -> CopyFields(a, rec((b[1].id) := b[2])), rec())); 
        # c := SubstBottomUp(c, @(1, assign, e->e.loc = V(1)), e->skip());

        # manually eval logic_and(1,1)
        # cmds := Collect(c, [assign, @(1, var), [@(2, logic_and), @(3, Value, e->e = 1), @(4, Value, e->e = 1)]]);
        # tmps := List(cmds, e->e.loc);
        # vars := [];
        # for i in [1..Length(tmps)] do Append(vars, [V(1)]); od;
        # c := SubstVars(c, FoldR(Zip2(tmps, vars), (a,b) -> CopyFields(a, rec((b[1].id) := b[2])), rec())); 
        # c := SubstBottomUp(c, @(1, assign, e->e.loc = V(1)), e->skip());

        # Opt Rule 3: remove multiple loads of modulus and mu
        spfuncs := Collect(c, specifiers_func);
        for spfunc in spfuncs do
        
            # Debug(true); Error();
            for i in [0..(pow(2, opts.recursionLevel).v-1)] do
                cmds := Collect(spfunc, [assign, @(1), [@(2, nth), @(3, var, e->e = opts.modulus), @(4, Value, e->e=i)]]);
                if Length(cmds) > 0 then spfunc := EliminateDuplicateLoad(spfunc, cmds, opts); fi;

                cmds := Collect(spfunc, [assign, @(1), [@(2, nth), @(3, var, e->e = opts.barrettMu), @(4, Value, e->e=i)]]);
                if Length(cmds) > 0 then spfunc := EliminateDuplicateLoad(spfunc, cmds, opts); fi;
            od;

        od;

        # test performance impact on 128b and 256b
        # within 1% performance impact on 128b and 256b
        # let's keep this for better code readability

        # the following lines of code are added to make CopyPropagation work
        # Debug(true); Error();
        # collect all cmds that output return values in macro
        ret_vars := Flat(List(Collect(c, specifiers_func), d->d.params));
        cmds := Collect(c, @(1, assign, e->e.loc in ret_vars));
        for v in cmds do
            # not copypropagation on those cmds
            v.isExpCommand := true;
            v.isAssign := false;
        od;
        
        # mark var = nth(mod, int) as not copypropagatable
        # otherwise after copypropagation there will be multiple instances of nth(mod, int)
        cmds := Collect(c, [assign, @(1), [@(2, nth), @(3, var, e->e = opts.modulus), @(4)]]);
        for v in cmds do
            # not copypropagation on those cmds
            v.isExpCommand := true;
            v.isAssign := false;
        od;
        
        # do the same for mu
        cmds := Collect(c, [assign, @(1), [@(2, nth), @(3, var, e->e = opts.barrettMu), @(4)]]);
        for v in cmds do
            # not copypropagation on those cmds
            v.isExpCommand := true;
            v.isAssign := false;
        od;
        
        # this solves: Error, Can't unify T_UInt(64) and TBool
        vars := Collect(c, @(1, var, e->e.t = TBool));
        for v in vars do
            v.t := TInt;
        od;

        # FUTURE: something weird with twiddles for l2 without macro
        # binsplit solves multiple X or twds but introduce wrong datatypes
        # spfunc := Collect(c, specifiers_func);
        # vars := Collect(c, @(1, var, e->not IsBound(e.ldepth)));
        # for v in vars do
        #     v.ldepth := 0;
        # od;
        # spfunc := BinSplit(spfunc, opts);
        
        # this solves: add(nth(X, var.table.a890), var.table.t396).computeType()
        nths := Collect(c, @(1, nth));
        for v in nths do
            if IsBound(v.computeType) then v.t := v.computeType(); fi;
        od;
        
        # Optimizations for using macro with mix-radix inputs
        # Debug(true); Error();
        if useMacro and cutsize <> 0 then

            # identify which macros need special treatment and how many zeros are there
            # duplicate original macro with modifications
            # record zero locations
            # subst var to zero with macro
            # subst macros in the code
            # trust copyprop.
   
            # act on spfunc from now on; not c
            spfunc1 := Copy(Collect(c, @(1, specifiers_func, e->IsSubset(e.id, "MPMulQDD_L")))[1]);
            spfunc2 := Copy(Collect(c, @(1, specifiers_func, e->IsSubset(e.id, "MPMulQDD_L")))[1]);
            
            # fmulqdd_l3(t1763, t1764, t1765, t1766, t1767, t1768, t1769, t1770, 
            #            t1771, t1772, t1773, t1774, t1775, t1776, t1777, t1778, 
            #            t1803, t1804, t1805, t1806, t1807, t1808, t1809, t1810, 
            #            V(0), V(0), V(0), a3168, a3169, a3170, a3171, a3172),
            # find the zero vars (assuming they are from the second arg)
            # opts.insize / opts.basesize; # how many elements per arg
            # cutsize / opts.basesize; # first n elements are 0 in one arg (assuming to be the second)
            # t1819, t1820, t1821
            # Debug(true); Error();
            params := Copy(spfunc1.params);
            n_start := (opts.insize/opts.basesize)*3+1;
            n_end := (opts.insize/opts.basesize)*3 + (cutsize/opts.basesize);
            vars := Sublist(spfunc1.params, n_start, n_end);
            # reduce zero locations
            tmps := [];
            for i in [1..Length(vars)] do Append(tmps, [V(0)]); od;
            spfunc1 := SubstVars(spfunc1, FoldR(Zip2(vars, tmps), (a,b) -> CopyFields(a, rec((b[1].id) := b[2])), rec())); 
            spfunc1.id := spfunc1.id::"_1";
            spfunc1.params := params;

            # fmulqdd_l3(t1747, t1748, t1749, t1750, t1751, t1752, t1753, t1754, 
            #            t1755, t1756, t1757, t1758, t1759, t1760, t1761, t1762, 
            #            V(0), V(0), V(0), t1968, t1969, t1970, t1971, t1972, 
            #            V(0), V(0), V(0), t1976, t1977, t1978, t1979, t1980)
            # t1811, t1812, t1813 & t1819, t1820, t1821
            params := Copy(spfunc2.params);
            n_start := (opts.insize/opts.basesize)*3+1;
            n_end := (opts.insize/opts.basesize)*3 + (cutsize/opts.basesize);
            vars := Sublist(spfunc2.params, n_start, n_end);
            vars := vars::Sublist(spfunc2.params, n_start-(opts.insize/opts.basesize), n_end-(opts.insize/opts.basesize));
            # reduce zero locations
            tmps := [];
            for i in [1..Length(vars)] do Append(tmps, [V(0)]); od;
            spfunc2 := SubstVars(spfunc2, FoldR(Zip2(vars, tmps), (a,b) -> CopyFields(a, rec((b[1].id) := b[2])), rec())); 
            spfunc2.id := spfunc2.id::"_2";
            spfunc2.params := params;

            # eliminate output that should be zero
            # Debug(true); Error();
            # Case 1: set first (cutsize/opts.basesize) outputs to 0
            vars := Sublist(spfunc1.params, 1, (cutsize/opts.basesize));
            SubstBottomUp(spfunc1, @(1, assign, e->e.loc in vars), e->skip());

            # Case 2: set first 2*(cutsize/opts.basesize) outputs to 0
            vars := Sublist(spfunc2.params, 1, (cutsize/opts.basesize)*2);
            SubstBottomUp(spfunc2, @(1, assign, e->e.loc in vars), e->skip());

            # glue back new code
            c := SubstBottomUp(c, @(1, specifiers_func, e->IsSubset(e.id, "MPMulQDD_L")), e->chain(@(1).val, spfunc1, spfunc2));

            # mark macros in the code for unparser
            # Case 1: one input arg is reduced
            cmds := Collect(c, @(1).cond(e->IsCommand(e) and IsBound(e.isMacro) and e.isMacro 
                        and ForAll(Sublist(e.args, n_start, n_end), IsZero)
                        and not ForAll(Sublist(e.args, n_start-(opts.insize/opts.basesize), n_end-(opts.insize/opts.basesize)), IsZero)));
            for v in cmds do v.zeroArg := 1; od;

            # Case 2: two input args are reduced
            cmds := Collect(c, @(1).cond(e->IsCommand(e) and IsBound(e.isMacro) and e.isMacro 
                and ForAll(Sublist(e.args, n_start, n_end), IsZero)
                and ForAll(Sublist(e.args, n_start-(opts.insize/opts.basesize), n_end-(opts.insize/opts.basesize)), IsZero)));
            for v in cmds do v.zeroArg := 2; od;

        fi;



        # Debug(true); Error();
        c := NCopyPropagate(c, opts);

        # remove TInt = (int) TBool
        # assign(b77, tcast(TInt, a1762)),
        # repeat
            # 1. subst (a35 = t444)
            # 2. assign(t444 = t444) -> skip()
            cmds := Collect(c, [assign, @(1, var, e->e.t = TInt), [@(2, tcast, e->e.args[1] = TInt), @(3), @(4, var, e->e.t = TInt)]]);
            vars := List(cmds, e->e.loc);
            tmps := List(cmds, e->e.exp.args[2]);
            c := SubstVars(c, FoldR(Zip2(tmps, vars), (a,b) -> CopyFields(a, rec((b[1].id) := b[2])), rec())); 
            SubstBottomUp(c, @(1, assign, e->IsBound(e.exp.args) and e.loc = e.exp.args[2]), e->skip());
        #     PrintLine("Length(cmds): ", Length(cmds));
        # until Length(cmds) = 0;

        # Debug(true); Error();

        # just to make the generated code absolutely pretty
        if false then
            # b = (b) 0
            SubstBottomUp(c, [assign, @(1, var), [@(2, tcast), @(3), @(4, Value, e->e.v = 0)]], e->assign(@(1).val, V(0)));
            # TInt = (int) V(true)
            SubstBottomUp(c, [assign, @(1, var, e->e.t = TInt), [@(2, tcast, e->e.args[1] = TInt), @(3), @(4, Value, e->e.v)]], e->assign(@(1).val, 1));
            c := NCopyPropagate(c, opts);
        fi;
    
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

    c := FlattenCode(c);

    # call after recursion, basesize is used
    ReduceTempStages(c, opts);

    # remove double declared vars
    SubstBottomUp(c, @(1, decl, e -> IsBound(e.vars[1]) and e.vars[1].t = TInt), e -> decl([], @(1).val.cmd));

    # fix twiddles datatype in func
    main_func := Collect(c, @(1, func, e -> e.id = "transform"))[1];
    twd_decl := Collect(main_func.params, @(1, var, e->e.id = "twiddles"))[1];
    twd_decl.t := X.t;

    # Debug(true); Error();
    c := EliminateDeadCode(c, opts);

    # instruction analysis
    # if not useMacro then
    #     # manually times loop size in spreadsheet
    #     # 2b = b * b
    #     PrintLine("mul: ", Length(Collect(c, @(1, mul, e->not e.t = TInt))));
    #     PrintLine("add: ", Length(Collect(c, @(1, add, e->not e.t = TInt))));
    #     PrintLine("sub: ", Length(Collect(c, @(1, sub, e->not e.t = TInt))));
        
    #     PrintLine("bin_shr: ", Length(Collect(c, @(1, bin_shr))));
    #     PrintLine("bin_shl: ", Length(Collect(c, @(1, bin_shl))));
    #     PrintLine("logic_and: ", Length(Collect(c, @(1, logic_and))));
    #     PrintLine("logic_or: ", Length(Collect(c, @(1, logic_or))));
    #     PrintLine("lt: ", Length(Collect(c, @(1, lt))));
    #     PrintLine("gt: ", Length(Collect(c, @(1, gt))));
    #     PrintLine("eq: ", Length(Collect(c, @(1, eq))));

    #     # missing: bin_or, assign, tcast, cond

    #     # cmds := Collect(c, assign);
    #     # for v in cmds do
    #     #     PrintLine(v.exp.__bases__[1]);
    #     # od;
    # else
    #     # causes l1 with macro to fail -> need to change "MPMulQDD_L2" to "MPMulQDD_L1"
    #     spfunc := Collect(c, @(1, specifiers_func, e->e.id = "MPMulQDD_L2"))[1];
    #     # count macro appearance
    #     n_macro := Length(Collect(c, fmulqdd_l2));
    #     PrintLine("mul: ", Length(Collect(spfunc, @(1, mul, e->not e.t = TInt)))*(n_macro-1) + Length(Collect(c, @(1, mul, e->not e.t = TInt))));
    #     PrintLine("add: ", Length(Collect(spfunc, @(1, add, e->not e.t = TInt)))*(n_macro-1) + Length(Collect(c, @(1, add, e->not e.t = TInt))));
    #     PrintLine("sub: ", Length(Collect(spfunc, @(1, sub, e->not e.t = TInt)))*(n_macro-1) + Length(Collect(c, @(1, sub, e->not e.t = TInt))));
        
    #     PrintLine("bin_shr: ", Length(Collect(spfunc, @(1, bin_shr, e->not e.t = TInt)))*(n_macro-1) + Length(Collect(c, @(1, bin_shr))));
    #     PrintLine("bin_shl: ", Length(Collect(spfunc, @(1, bin_shl, e->not e.t = TInt)))*(n_macro-1) + Length(Collect(c, @(1, bin_shl))));
    #     PrintLine("logic_and: ", Length(Collect(spfunc, @(1, logic_and, e->not e.t = TInt)))*(n_macro-1) + Length(Collect(c, @(1, logic_and))));
    #     PrintLine("logic_or: ", Length(Collect(spfunc, @(1, logic_or, e->not e.t = TInt)))*(n_macro-1) + Length(Collect(c, @(1, logic_or))));
    #     PrintLine("lt: ", Length(Collect(spfunc, @(1, lt, e->not e.t = TInt)))*(n_macro-1) + Length(Collect(c, @(1, lt))));
    #     PrintLine("gt: ", Length(Collect(spfunc, @(1, gt, e->not e.t = TInt)))*(n_macro-1) + Length(Collect(c, @(1, gt))));
    #     PrintLine("eq: ", Length(Collect(spfunc, @(1, eq, e->not e.t = TInt)))*(n_macro-1) + Length(Collect(c, @(1, eq))));
        
    # fi;
    
    # Debug(true); Error();

    # decl vars
    SubstBottomUp(c, @(1, specifiers_func), 
        e -> specifiers_func(@(1).val.decl_specs, @(1).val.ret, @(1).val.id, @(1).val.params, Compile.declareVars(@(1).val.cmd)));    

    if opts.useMacro then
        # fix decl in mpmulqdd
        # remove extra declared vars what are function inputs
        func_list := Collect(c, @(1, specifiers_func));
        for v in func_list do
            if IsBound(v.cmd.vars) then
                v.cmd.vars := Difference(v.cmd.vars, v.params);
            fi;
        od;
    fi;

    if useVerbose then PrintLine("100\% Done. Time spent: ", StringTime(Runtime()-time_stamp)); fi;

    return c;
end;
