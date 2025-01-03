Class(NTTXOpts, SpiralDefaults, rec(
    tags := [],
    operations := rec(Print := s -> Print("<NTTX options record>")),
    tagIt := (self, t) >> t.withTags(self.tags),
    search := (self, t) >> RandomRuleTree(t, self),
    sumsRuleTree := (self, rt) >> SumsRuleTree(rt, self),
    codeSums := meth(self, ss)
        local c, X, Y, opts;
        opts := self;
        X := var("X", self.XType);
        Y := var("Y", self.YType);
        # Debug(true);
        # Error(); # X type is fine till this step
        c := opts.codegen(Formula(ss), Y, X, opts);
        c.ruletree := Cond(IsBound(ss.ruletree), ss.ruletree, rec());
        c := opts.postProcessCode(c, opts);
        c.ruletree := Cond(IsBound(ss.ruletree), ss.ruletree, rec());
        if IsBound(self.params) then
            c := SubstBottomUp(c, @(1, func, e->e.id = "transform"),
                e ->func(@(1).val.ret, @(1).val.id, @(1).val.params::self.params, @(1).val.cmd));
        fi;
        if IsBound(opts.useBinSplit) and opts.useBinSplit then c:= BinSplit(c); fi;
        return c;
    end,
    prettyPrint := (self, c) >> PrintCode(c.ruletree.node.params[2].fname, c, self),
    genNttx := (self, t) >> self.codeSums(self.sumsRuleTree(self.search(t))),
    globalUnrolling := 16
));

Declare(NTTXDefaultConf);

Class(NTTXDefaultConf, LocalConfig, rec(
    __call__ :=  arg -> CopyFields(NTTXDefaultConf, 
        rec(
            modulus := arg[1][1],
            modulusBitwidth := LogInt(arg[1][1], 2) + 1,
            abstractType := _T_IntMod(arg[1][1]),
            machineBitwidth := 32,
            machineType := T_UInt(32),
            machineSignedType := T_Int(32),
            machineMulType := T_UInt(64)
        )),
    getOpts := meth(self, t)
        local opts;
        opts := Copy(NTTXOpts);
        
        opts.modulus := self.modulus;
        opts.modulusBitwidth := self.modulusBitwidth;
        opts.abstractType := self.abstractType;
        opts.machineBitwidth := self.machineBitwidth;
        opts.machineType := self.machineType;
        opts.machineSignedType := self.machineSignedType;
        opts.machineMulType := self.machineMulType;
        
        opts.XType := TPtr(self.abstractType);
        opts.YType := TPtr(self.abstractType);
        opts.useDeref := false;
        opts.breakdownRules.NTT := [ NTT_Base, NTT_iter ];
        opts.breakdownRules.iNTT := [ iNTT_Base, iNTT_iter ];
        opts.includes := ["\"nttx-spiral.h\""];
        
        opts.postProcessCode := NTTXFixMod;
        opts.useBinSplit := false;
        
        return opts;    
    end,
    operations := rec(Print := s -> Print("<NTTX Default Configuration>")),
    type := self >> self.abstractType
));

Class(NTTXBigIntConf, NTTXDefaultConf, rec(
    __call__ :=  arg -> CopyFields(NTTXDefaultConf, 
        rec(
            nttxConf := When(arg[1] =[], [rec()], arg[1]),
            modulus := errExp(TUInt),
            twiddles := errExp(TPtr(TUInt)),
            modulusBitwidth := errExp(TUInt),
            abstractType := _T_IntMod(1),
            machineBitwidth := errExp(TUInt),
            machineType := T_UInt(1),
            machineSignedType := T_Int(1),
            machineMulType := T_UInt(2),
            operations := rec(Print := s -> Print("<NTTX PALISADE BigInt Configuration>")
        ),
        getOpts := meth(self, t)
            local opts;
            opts := Copy(NTTXOpts);

            opts.modulus := self.modulus;
            opts.twiddles := self.twiddles;
            opts.nttxConf := self.nttxConf;
            if Length(self.nttxConf) >= 1 and IsRec(self.nttxConf[1]) and IsBound(self.nttxConf[1].useBarrettMult) and self.nttxConf[1].useBarrettMult then 
                opts.useBarrettMult := self.nttxConf[1].useBarrettMult; 
                opts.barrettMu := t.params[2].mu;
            fi;
            if Length(self.nttxConf) >= 1 and IsRec(self.nttxConf[1]) and IsBound(self.nttxConf[1].useTwiddleGen) then 
                opts.useTwiddleGen := self.nttxConf[1].useTwiddleGen; 
            fi;
            if Length(t.params) >= 2 and IsBound(t.params[2].modulus) then opts.modulus := t.params[2].modulus; fi;
            if Length(t.params) >= 2 and IsBound(t.params[2].twiddles) then opts.twiddles := t.params[2].twiddles; fi;

            opts.modulusBitwidth := self.modulusBitwidth;
            opts.abstractType := self.abstractType;
            opts.machineBitwidth := self.machineBitwidth;
            opts.machineType := self.machineType;
            opts.machineSignedType := self.machineSignedType;
            opts.machineMulType := self.machineMulType;
            
            opts.XType := TPtr(self.abstractType);
            opts.YType := TPtr(self.abstractType);
            opts.useDeref := false;
            opts.breakdownRules.NTT := [ NTT_Base ]::
                When(IsBound(self.nttxConf[1].useIter) and self.nttxConf[1].useIter, [ NTT_iter ], [])::
                When(IsBound(self.nttxConf[1].usePease) and self.nttxConf[1].usePease, [ NTT_KL ], [])::
                When((IsBound(self.nttxConf[1].useCT) and self.nttxConf[1].useCT) or (not IsBound(self.nttxConf[1].useCT)), [ NTT_SkewNTT ], []);
            opts.breakdownRules.SkewNTT := [ SkewNTT_Base, SkewNTT_CT ];
            opts.breakdownRules.iNTT := [ iNTT_Base ]::
                When(IsBound(self.nttxConf[1].useIter) and self.nttxConf[1].useIter, [ iNTT_iter ], [])::
                When(IsBound(self.nttxConf[1].usePease) and self.nttxConf[1].usePease, [ iNTT_Pease ], [])::
                When((IsBound(self.nttxConf[1].useCT) and self.nttxConf[1].useCT) or (not IsBound(self.nttxConf[1].useCT)), [ iNTT_iSkewNTT ], []);
            opts.breakdownRules.iSkewNTT := [ iSkewNTT_Base, iSkewNTT_CT ];
            opts.includes := ["\"big_int.h\""];
            opts.unparser := NTTXBigIntUnparser;
#            opts.useBinSplit := true;
            opts.useBinSplit := false;
    
            opts.postProcessCode := NTTXFixBigIntOps;
            opts.operations := rec(Print := s -> Print("<NTTX PALISADE BigInt Options>"));
            if Length(t.params) >= 2 and  IsBound(t.params[2].params) then opts.params := t.params[2].params; fi;
            
            return opts;    
        end,
        operations := rec(Print := s -> Print("<NTTX PALISADE BigInt Configuration>")),
        type := self >> self.abstractType
    ))
));

Class(NTTXNativeConf, NTTXBigIntConf, rec(
    __call__ :=  arg -> CopyFields(NTTXDefaultConf, 
        rec(
            nttxConf := When(arg[1] =[], [rec()], arg[1]),
            modulus := errExp(TUInt),
            twiddles := errExp(TPtr(TUInt)),
            machineBitwidth := 32,
            machineType := T_UInt(32),
            machineSignedType := T_Int(32),
            machineMulType := T_UInt(64),
            modulusBitwidth := errExp(TUInt),
            abstractType := _T_IntMod(1),
            mbits := 28,
            operations := rec(Print := s -> Print("<NTTX PALISADE Native Configuration>")
        ),
        getOpts := meth(self, t)
            local opts;
            opts := Copy(NTTXOpts);
            
            opts.modulus := self.modulus;
            opts.nttxConf := self.nttxConf;

            opts.twiddles := self.twiddles;
            opts.modulusBitwidth := self.modulusBitwidth;
            opts.abstractType := self.abstractType;
            opts.machineBitwidth := self.machineBitwidth;
            opts.machineType := self.machineType;
            opts.machineSignedType := self.machineSignedType;
            opts.machineMulType := self.machineMulType;
            opts.mbits := self.mbits;

            if Length(t.params) >= 2 and  IsBound(t.params[2].modulus) then opts.modulus := t.params[2].modulus; fi;
            if Length(t.params) >= 2 and  IsBound(t.params[2].mu) then opts.barrettMu := t.params[2].mu; fi;
            if Length(t.params) >= 2 and  IsBound(t.params[2].twiddles) then opts.twiddles := t.params[2].twiddles; fi;
            opts.useBarrettMult := true;
            
            opts.XType := TPtr(self.abstractType);
            opts.YType := TPtr(self.abstractType);
            opts.useDeref := false;
            opts.breakdownRules.NTT := [ NTT_Base ]::
                When(IsBound(self.nttxConf[1].useIter) and self.nttxConf[1].useIter, [ NTT_iter ], [])::
                When((IsBound(self.nttxConf[1].useCT) and self.nttxConf[1].useCT) or (not IsBound(self.nttxConf[1].useCT)), [ NTT_SkewNTT ], []);
            opts.breakdownRules.SkewNTT := [ SkewNTT_Base, SkewNTT_CT ];
            opts.breakdownRules.iNTT := [ iNTT_Base ]::
                When(IsBound(self.nttxConf[1].useIter) and self.nttxConf[1].useIter, [ iNTT_iter ], [])::
                When((IsBound(self.nttxConf[1].useCT) and self.nttxConf[1].useCT) or (not IsBound(self.nttxConf[1].useCT)), [ iNTT_iSkewNTT ], []);
            opts.breakdownRules.iSkewNTT := [ iSkewNTT_Base, iSkewNTT_CT ];
            opts.includes := [];
#            opts.useBinSplit := true;
            opts.useBinSplit := false;
    
            opts.postProcessCode := NTTXFixModNativeBarrett;
            opts.operations := rec(Print := s -> Print("<NTTX PALISADE Native __int32 Options>"));
            if Length(t.params) >= 2 and  IsBound(t.params[2].params) then opts.params := t.params[2].params; fi;
            
            return opts;    
        end,
        operations := rec(Print := s -> Print("<NTTX PALISADE Native Configuration>")),
        type := self >> self.abstractType
    ))
));

# Adapted from NTTXNativeConf
Class(NTTXMPConf, NTTXBigIntConf, rec(
    __call__ :=  arg -> CopyFields(NTTXDefaultConf, 
        rec(
            nttxConf := When(arg[1] =[], [rec()], arg[1]),
            modulus := errExp(TUInt),
            twiddles := errExp(TPtr(TUInt)),
            machineBitwidth := 32,
            machineType := TUInt, # changed
            machineDType := T_UInt(1), 
            machineSignedType := T_Int(32),
            machineMulType := T_UInt(64),
            modulusBitwidth := errExp(TUInt),
            # abstractType := _T_IntMod(1),
            mbits := errExp(TUInt), 
            insize := errExp(TUInt),
            basesize := errExp(TUInt),
            abstractType := T_UInt(basesize*2), # TODO: need to be InInt or BaseInt[]
            operations := rec(Print := s -> Print("<NTTX PALISADE Multi-Precision Configuration>")
        ),
        getOpts := meth(self, t)
            local opts;
            opts := Copy(NTTXOpts);
            
            opts.modulus := self.modulus;
            opts.nttxConf := self.nttxConf;

            opts.twiddles := self.twiddles;
            opts.modulusBitwidth := self.modulusBitwidth;
            opts.abstractType := self.abstractType;
            opts.machineBitwidth := self.machineBitwidth;
            
            # opts.machineType := self.machineType;
            # opts.machineDType := self.machineDType;

            opts.machineSignedType := self.machineSignedType;
            opts.machineMulType := self.machineMulType;
            
            opts.mbits := self.mbits;
            opts.insize := self.insize;
            opts.basesize := self.basesize;

            opts.machineType := T_UInt(opts.basesize);
            opts.machineDType := T_UInt(opts.basesize*2);

            if Length(t.params) >= 2 and IsBound(t.params[2].modulus) then opts.modulus := t.params[2].modulus; fi;
            if Length(t.params) >= 2 and IsBound(t.params[2].mu) then opts.barrettMu := t.params[2].mu; fi;
            if Length(t.params) >= 2 and IsBound(t.params[2].twiddles) then opts.twiddles := t.params[2].twiddles; fi;
            
            if Length(t.params) >= 2 and IsBound(t.params[2].useMacro) then opts.useMacro := t.params[2].useMacro; fi;
            if Length(t.params) >= 2 and IsBound(t.params[2].useArray) then opts.useArray := t.params[2].useArray; fi;
            if Length(t.params) >= 2 and IsBound(t.params[2].recursionLevel) then opts.recursionLevel := t.params[2].recursionLevel; fi;
            if Length(t.params) >= 2 and IsBound(t.params[2].mxp) then opts.mxp := t.params[2].mxp; fi;
            if Length(t.params) >= 2 and IsBound(t.params[2].basesize) then 
                opts.basesize := t.params[2].basesize; 
                opts.dbasesize := opts.basesize * 2;
            fi;
            if Length(t.params) >= 2 and IsBound(t.params[2].insize) then opts.insize := t.params[2].insize; fi;
            if Length(t.params) >= 2 and IsBound(t.params[2].mbits) then opts.mbits := t.params[2].mbits; fi;

            opts.useBarrettMult := true;
            
            opts.XType := TPtr(self.abstractType);
            opts.YType := TPtr(self.abstractType);
            opts.useDeref := false;
            opts.breakdownRules.NTT := [ NTT_Base ]::
                When(IsBound(self.nttxConf[1].useIter) and self.nttxConf[1].useIter, [ NTT_iter ], [])::
                When((IsBound(self.nttxConf[1].useCT) and self.nttxConf[1].useCT) or (not IsBound(self.nttxConf[1].useCT)), [ NTT_SkewNTT ], []);
            opts.breakdownRules.SkewNTT := [ SkewNTT_Base, SkewNTT_CT ];
            opts.breakdownRules.iNTT := [ iNTT_Base ]::
                When(IsBound(self.nttxConf[1].useIter) and self.nttxConf[1].useIter, [ iNTT_iter ], [])::
                When((IsBound(self.nttxConf[1].useCT) and self.nttxConf[1].useCT) or (not IsBound(self.nttxConf[1].useCT)), [ iNTT_iSkewNTT ], []);
            opts.breakdownRules.iSkewNTT := [ iSkewNTT_Base, iSkewNTT_CT ];
            opts.includes := [];
            # opts.useBinSplit := true;
            opts.useBinSplit := false;
            if opts.mxp then
                opts.postProcessCode := NTTXFixMxPOps;
            else
                opts.postProcessCode := NTTXFixMPOps;
            fi;
            opts.unparser := NTTXMPUnparser;
            opts.operations := rec(Print := s -> Print("<NTTX PALISADE Multi-Precision Options>"));
            if Length(t.params) >= 2 and IsBound(t.params[2].params) then opts.params := t.params[2].params; fi;
            
            return opts;    
        end,
        operations := rec(Print := s -> Print("<NTTX PALISADE Multi-Precision Configuration>")),
        type := self >> self.abstractType
    ))
));

# Adapted from NTTXMPConf
Class(NTTXMPPyConf, NTTXBigIntConf, rec(
    __call__ :=  arg -> CopyFields(NTTXDefaultConf, 
        rec(
            nttxConf := When(arg[1] =[], [rec()], arg[1]),
            modulus := errExp(TUInt),
            twiddles := errExp(TPtr(TUInt)),
            machineBitwidth := 32,
            machineType := TUInt, # changed
            machineDType := T_UInt(1), 
            machineSignedType := T_Int(32),
            machineMulType := T_UInt(64),
            modulusBitwidth := errExp(TUInt),
            # abstractType := _T_IntMod(1),
            mbits := errExp(TUInt), 
            insize := errExp(TUInt),
            basesize := errExp(TUInt),
            abstractType := T_UInt(basesize*2), # TODO: need to be InInt or BaseInt[]
            operations := rec(Print := s -> Print("<NTTX PALISADE Python Configuration>")
        ),
        getOpts := meth(self, t)
            local opts;
            opts := Copy(NTTXOpts);
            
            opts.modulus := self.modulus;
            opts.nttxConf := self.nttxConf;

            opts.twiddles := self.twiddles;
            opts.modulusBitwidth := self.modulusBitwidth;
            opts.abstractType := self.abstractType;
            opts.machineBitwidth := self.machineBitwidth;
            
            # opts.machineType := self.machineType;
            # opts.machineDType := self.machineDType;

            opts.machineSignedType := self.machineSignedType;
            opts.machineMulType := self.machineMulType;
            
            opts.mbits := self.mbits;
            opts.insize := self.insize;
            opts.basesize := self.basesize;

            opts.machineType := T_UInt(opts.basesize);
            opts.machineDType := T_UInt(opts.basesize*2);

            if Length(t.params) >= 2 and IsBound(t.params[2].modulus) then opts.modulus := t.params[2].modulus; fi;
            if Length(t.params) >= 2 and IsBound(t.params[2].mu) then opts.barrettMu := t.params[2].mu; fi;
            if Length(t.params) >= 2 and IsBound(t.params[2].twiddles) then opts.twiddles := t.params[2].twiddles; fi;
            
            if Length(t.params) >= 2 and IsBound(t.params[2].useMacro) then opts.useMacro := t.params[2].useMacro; fi;
            if Length(t.params) >= 2 and IsBound(t.params[2].mxp) then opts.mxp := t.params[2].mxp; fi;
            if Length(t.params) >= 2 and IsBound(t.params[2].basesize) then 
                opts.basesize := t.params[2].basesize; 
                opts.dbasesize := opts.basesize * 2;
            fi;
            if Length(t.params) >= 2 and IsBound(t.params[2].insize) then opts.insize := t.params[2].insize; fi;
            if Length(t.params) >= 2 and IsBound(t.params[2].mbits) then opts.mbits := t.params[2].mbits; fi;

            opts.useBarrettMult := true;
            
            opts.XType := TPtr(self.abstractType);
            opts.YType := TPtr(self.abstractType);
            opts.useDeref := false;
            opts.breakdownRules.NTT := [ NTT_Base ]::
                When(IsBound(self.nttxConf[1].useIter) and self.nttxConf[1].useIter, [ NTT_iter ], [])::
                When((IsBound(self.nttxConf[1].useCT) and self.nttxConf[1].useCT) or (not IsBound(self.nttxConf[1].useCT)), [ NTT_SkewNTT ], []);
            opts.breakdownRules.SkewNTT := [ SkewNTT_Base, SkewNTT_CT ];
            opts.breakdownRules.iNTT := [ iNTT_Base ]::
                When(IsBound(self.nttxConf[1].useIter) and self.nttxConf[1].useIter, [ iNTT_iter ], [])::
                When((IsBound(self.nttxConf[1].useCT) and self.nttxConf[1].useCT) or (not IsBound(self.nttxConf[1].useCT)), [ iNTT_iSkewNTT ], []);
            opts.breakdownRules.iSkewNTT := [ iSkewNTT_Base, iSkewNTT_CT ];
            opts.includes := [];
            # opts.useBinSplit := true;
            opts.useBinSplit := false;
            opts.arrayBufModifier := "";
            opts.postProcessCode := NTTXFixMPPyOps;
            opts.unparser := NTTXMPPyUnparser;
            opts.operations := rec(Print := s -> Print("<NTTX PALISADE Python Options>"));
            if Length(t.params) >= 2 and  IsBound(t.params[2].params) then opts.params := t.params[2].params; fi;
            
            return opts;    
        end,
        operations := rec(Print := s -> Print("<NTTX PALISADE Python Configuration>")),
        type := self >> self.abstractType
    ))
));

# minimum configuration for HKS
Class(NTTXBigIntHKSConf, NTTXBigIntConf, rec(

    __call__ :=  arg -> CopyFields(NTTXDefaultConf, 
        rec(
            nttxConf := When(arg[1] = [], [rec()], arg[1]),
            # modulus := errExp(TUInt),
            # twiddles := errExp(TPtr(TUInt)),
            # modulusBitwidth := errExp(TUInt),
            abstractType := _T_IntMod(1),
            # machineBitwidth := errExp(TUInt),
            # machineType := T_UInt(1),
            # machineSignedType := T_Int(1),
            # machineMulType := T_UInt(2),
            operations := rec(Print := s -> Print("<NTTX BigInt HKS Configuration>")),
            
            getOpts := meth(self, t)
                local opts;
                opts := Copy(NTTXOpts);
                
                opts.nttxConf := self.nttxConf;

                # opts.twiddles := self.twiddles;
                # opts.modulusBitwidth := self.modulusBitwidth;
                opts.abstractType := self.abstractType;
                # opts.machineBitwidth := self.machineBitwidth;
                # opts.machineType := self.machineType;
                # opts.machineSignedType := self.machineSignedType;
                # opts.machineMulType := self.machineMulType;

                opts.XType := TPtr(self.abstractType);
                opts.YType := TPtr(self.abstractType);
                opts.useDeref := false;

                opts.globalUnrolling := 0;

                opts.includes := ["\"big_int.h\""];
                opts.unparser := NTTXBigIntUnparser; # TODO: customize it?
                opts.useBinSplit := false;

                # remove "static"
                opts.arrayBufModifier := "";

                opts.postProcessCode := NTTXFixBigIntHKSOps;
                opts.operations := rec(Print := s -> Print("<NTTX BigInt HKS Configuration>"));
                
                return opts;   
            end,

        operations := rec(Print := s -> Print("<NTTX BigInt HKS Configuration>")),
        type := self >> self.abstractType

    ))
));

spiral.LocalConfig.nttx := rec(
    defaultConf := (arg) -> NTTXDefaultConf(arg),
    bigintConf := (arg) -> NTTXBigIntConf(arg),
    nativeConf := (arg) -> NTTXNativeConf(arg),
    mpConf := (arg) -> NTTXMPConf(arg),
    mpPyConf := (arg) -> NTTXMPPyConf(arg),
    bigintHKSConf := (arg) -> NTTXBigIntHKSConf(arg)
);

