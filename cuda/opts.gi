Class(NTTXBigIntCUDAConf, NTTXDefaultConf, rec(
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
            operations := rec(Print := s -> Print("<NTTX BigInt CUDA Configuration>")
        ),
        getOpts := meth(self, t)

            local tt, _tt, _tt2, _conf, opts, _HPCSupportedSizesCUDA, _thold,
                  MAX_KERNEL, MAX_PRIME, MIN_SIZE, MAX_SIZE, size1, filter, N;

            # all dimensions need to be inthis array for the high perf MDDFT conf to kick in for now
            # size 320 is problematic at this point and needs attention. Need support for 3 stages to work first
            MAX_KERNEL := 23;
            MAX_PRIME := 17;
            MIN_SIZE := 32;
            MAX_SIZE := 680;

            # Error();

            N := t.params[2].n;

            _thold := MAX_KERNEL;
            filter := (e) -> When(e[1] * e[2] <= _thold ^ 2, e[1] <= _thold and e[2] <= _thold, e[1] <= _thold and e[2] >= _thold);
            size1 := Filtered([MIN_SIZE..MAX_SIZE], i -> ForAny(DivisorPairs(i), filter) and ForAll(Factors(i), j -> not IsPrime(j) or j <= MAX_PRIME));
            _HPCSupportedSizesCUDA := size1;

            _conf := FFTXGlobals.confFFTCUDADevice();
            opts := FFTXGlobals.getOpts(_conf);

            opts.modulus := self.modulus;
            if Length(t.params) >= 2 and IsBound(t.params[2].modulus) then opts.modulus := t.params[2].modulus; fi;
            opts.nttxConf := self.nttxConf;

            if Length(self.nttxConf) >= 1 and IsRec(self.nttxConf[1]) and IsBound(self.nttxConf[1].isNative) and self.nttxConf[1].isNative then 
                # opts.useBarrettMult := self.nttxConf[1].useBarrettMult; 
                # native implicitly means useBarrett
                opts.barrettMu := t.params[2].mu;
            fi;

            opts.isNative := self.nttxConf[1].isNative;
            opts.insize :=  self.nttxConf[1].insize;

            opts.globalUnrolling := 2;
            opts.tags := [ASIMTKernelFlag(ASIMTGridDimX), ASIMTBlockDimX];

            # syncwarp doesn't work for larger NTT sizes
            opts.unparser.simt_synccluster := opts.unparser.simt_syncblock;

            opts.codegen := NTTXCUDACodegen;
            
            
            # Error();
            if opts.isNative then
                
                opts.abstractType := self.abstractType;
                opts.machineBitwidth := 32; # not used in rewrite
                
                if opts.insize = 32 then
                    # 32b InInt
                    opts.machineType := T_UInt(32);
                    opts.machineSignedType := T_Int(32);
                    opts.mbits := 28;
                    opts.machineMulType := T_UInt(64); # not used in rewrite
                else
                    # 64b InInt
                    opts.machineType := T_UInt(64);
                    opts.machineSignedType := T_Int(64);
                    opts.machineMulType := T_UInt(128);
                    opts.mbits := 60;
                fi;

                opts.postProcessCode := NTTXFixCUDANativeOps;
                opts.unparser := NTTXCUDANativeUnparser;
            else
                opts.postProcessCode := NTTXFixCUDAOps;
                    
                # TODO: 
                # opts.postProcessCode := NTTXFixMPCUDAOps;
                

                opts.machineType := self.machineType; # only thing that non-native needs
                # opts.twiddles := self.twiddles;
                # opts.modulusBitwidth := self.modulusBitwidth;
                # opts.abstractType := self.abstractType;
                # opts.machineBitwidth := self.machineBitwidth;
                # opts.machineSignedType := self.machineSignedType;
                # opts.machineMulType := self.machineMulType;
                
                
                opts.unparser := NTTXCUDAUnparser;

                # TODO:
                # opts.unparser := NTTXMPCUDAUnparser;
            fi;
            
            opts.XType := TPtr(self.abstractType);
            opts.YType := TPtr(self.abstractType);
            # opts.useDeref := false;

            opts.breakdownRules.NTT := [ NTT_Base, CopyFields(NTT_KL_CUDA, rec(switch := true)) ];
            # _opts.breakdownRules.SkewNTT := [ SkewNTT_Base, SkewNTT_CT ];
            

            if N <= 2048 then # 2048 is the largest size that 1024 threads can handle
                opts.breakdownRules.TTensorI := [ IxA_SIMT, AxI_SIMT, L_IxA_SIMT_nopeel, IxA_L_SIMT_nopeel ]; 
            else 
                opts.breakdownRules.TTensorI := [ IxA_SIMT, AxI_SIMT, L_IxA_SIMT_nested, IxA_L_SIMT_nested ]; 

                # 8K & 16K on H100 & 4090 & V100 SK
                # nthread := 256;
                # L_IxA_SIMT_nested.max_threads := nthread;
                # IxA_L_SIMT_nested.max_threads := nthread;
            
            fi;

            return opts;

        end,
        operations := rec(Print := s -> Print("<NTTX BigInt CUDA Configuration>")),
        type := self >> self.abstractType
    ))
));

# based on NTTXMPConf
Class(NTTXMPCUDAConf, NTTXDefaultConf, rec(
    __call__ :=  arg -> CopyFields(NTTXDefaultConf, 
        rec(
            nttxConf := When(arg[1] =[], [rec()], arg[1]),
            modulus := errExp(TUInt),
            twiddles := errExp(TPtr(TUInt)),
            modulusBitwidth := errExp(TUInt),
            abstractType := _T_IntMod(1),
            machineBitwidth := 32,
            machineType := TUInt,
            machineDType := T_UInt(1),
            machineSignedType := T_Int(32),
            machineMulType := T_UInt(2),
            mbits := errExp(TUInt), 
            insize := errExp(TUInt),
            basesize := errExp(TUInt),
            operations := rec(Print := s -> Print("<NTTX MP CUDA Configuration>")
        ),
        getOpts := meth(self, t)

            local tt, _tt, _tt2, _conf, opts, _HPCSupportedSizesCUDA, _thold,
                  MAX_KERNEL, MAX_PRIME, MIN_SIZE, MAX_SIZE, size1, filter, N;

            # all dimensions need to be in this array for the high perf MDDFT conf to kick in for now
            # size 320 is problematic at this point and needs attention. Need support for 3 stages to work first
            MAX_KERNEL := 23;
            MAX_PRIME := 17;
            MIN_SIZE := 32;
            MAX_SIZE := 680;

            N := t.params[2].n;

            _thold := MAX_KERNEL;
            filter := (e) -> When(e[1] * e[2] <= _thold ^ 2, e[1] <= _thold and e[2] <= _thold, e[1] <= _thold and e[2] >= _thold);
            size1 := Filtered([MIN_SIZE..MAX_SIZE], i -> ForAny(DivisorPairs(i), filter) and ForAll(Factors(i), j -> not IsPrime(j) or j <= MAX_PRIME));
            _HPCSupportedSizesCUDA := size1;

            _conf := FFTXGlobals.confFFTCUDADevice();
            opts := FFTXGlobals.getOpts(_conf);

            opts.mbits := self.mbits;
            opts.insize := self.insize;
            opts.basesize := self.basesize;

            opts.modulus := self.modulus;
            if Length(t.params) >= 2 and IsBound(t.params[2].modulus) then opts.modulus := t.params[2].modulus; fi;
            opts.nttxConf := self.nttxConf;
            opts.barrettMu := t.params[2].mu;

            if Length(t.params) >= 2 and IsBound(t.params[2].useMacro) then opts.useMacro := t.params[2].useMacro; fi;
            if Length(t.params) >= 2 and IsBound(t.params[2].mxp) then opts.mxp := t.params[2].mxp; fi;
            if Length(t.params) >= 2 and IsBound(t.params[2].basesize) then 
                opts.basesize := t.params[2].basesize; 
                opts.dbasesize := opts.basesize * 2;
            fi;
            if Length(t.params) >= 2 and IsBound(t.params[2].insize) then opts.insize := t.params[2].insize; fi;
            if Length(t.params) >= 2 and IsBound(t.params[2].mbits) then opts.mbits := t.params[2].mbits; fi;

            # Error();

            opts.globalUnrolling := 2;
            opts.tags := [ASIMTKernelFlag(ASIMTGridDimX), ASIMTBlockDimX];

            # syncwarp doesn't work for larger NTT sizes
            # using syncthreads instead
            opts.unparser.simt_synccluster := opts.unparser.simt_syncblock;

            opts.codegen := NTTXCUDACodegen;
            opts.postProcessCode := NTTXFixMPCUDAOps;
            
            opts.twiddles := self.twiddles;
            opts.modulusBitwidth := self.modulusBitwidth;
            opts.abstractType := self.abstractType;
            opts.machineBitwidth := self.machineBitwidth;
            opts.machineSignedType := self.machineSignedType;
            opts.machineMulType := self.machineMulType;

            opts.machineType := self.machineType;
            opts.machineDType := self.machineDType;

            # opts.mbits := self.mbits;
            # opts.basesize := self.basesize;
            
            opts.unparser := NTTXMPCUDAUnparser;
            
            opts.XType := TPtr(self.abstractType);
            opts.YType := TPtr(self.abstractType);
            # opts.useDeref := false;

            opts.breakdownRules.NTT := [ NTT_Base, CopyFields(NTT_KL_CUDA, rec(switch := true)) ];
            # _opts.breakdownRules.SkewNTT := [ SkewNTT_Base, SkewNTT_CT ];
            

            if N <= 2048 then # 2048 is the largest size that 1024 threads can handle
                opts.breakdownRules.TTensorI := [ IxA_SIMT, AxI_SIMT, L_IxA_SIMT_nopeel, IxA_L_SIMT_nopeel ]; 
            else 
                # TODO: multi kernel launch instead of nested?
                opts.breakdownRules.TTensorI := [ IxA_SIMT, AxI_SIMT, L_IxA_SIMT_nested, IxA_L_SIMT_nested ]; 
            fi;

            return opts;

        end,
        operations := rec(Print := s -> Print("<NTTX MP CUDA Configuration>")),
        type := self >> self.abstractType
    ))
));

# based on NTTXMxPConf
Class(NTTXMxPCUDAConf, NTTXDefaultConf, rec(
    __call__ :=  arg -> CopyFields(NTTXDefaultConf, 
        rec(
            nttxConf := When(arg[1] =[], [rec()], arg[1]),
            modulus := errExp(TUInt),
            twiddles := errExp(TPtr(TUInt)),
            machineBitwidth := 32,
            machineType := TUInt,
            machineDType := T_UInt(1),
            machineSignedType := T_Int(32),
            machineMulType := T_UInt(64),
            modulusBitwidth := errExp(TUInt),
            mbits := errExp(TUInt), 
            insize := errExp(TUInt),
            basesize := errExp(TUInt),
            abstractType := T_UInt(basesize*2), # TODO: need to be InInt or BaseInt[]
            operations := rec(Print := s -> Print("<NTTX MxP CUDA Configuration>")
        ),
        getOpts := meth(self, t)

            local tt, _tt, _tt2, _conf, opts, _HPCSupportedSizesCUDA, _thold,
                  MAX_KERNEL, MAX_PRIME, MIN_SIZE, MAX_SIZE, size1, filter, N,
                  nthread;

            # all dimensions need to be in this array for the high perf MDDFT conf to kick in for now
            # size 320 is problematic at this point and needs attention. Need support for 3 stages to work first
            MAX_KERNEL := 23;
            MAX_PRIME := 17;
            MIN_SIZE := 32;
            MAX_SIZE := 680;
            
            N := t.params[2].n;

            _thold := MAX_KERNEL;
            filter := (e) -> When(e[1] * e[2] <= _thold ^ 2, e[1] <= _thold and e[2] <= _thold, e[1] <= _thold and e[2] >= _thold);
            size1 := Filtered([MIN_SIZE..MAX_SIZE], i -> ForAny(DivisorPairs(i), filter) and ForAll(Factors(i), j -> not IsPrime(j) or j <= MAX_PRIME));
            _HPCSupportedSizesCUDA := size1;

            _conf := FFTXGlobals.confFFTCUDADevice();
            opts := FFTXGlobals.getOpts(_conf);

            opts.mbits := self.mbits;
            opts.insize := self.insize;
            opts.basesize := self.basesize;

            opts.modulus := self.modulus;
            if Length(t.params) >= 2 and IsBound(t.params[2].modulus) then opts.modulus := t.params[2].modulus; fi;
            opts.nttxConf := self.nttxConf;
            opts.barrettMu := t.params[2].mu;

            if Length(t.params) >= 2 and IsBound(t.params[2].useMacro) then opts.useMacro := t.params[2].useMacro; fi;
            if Length(t.params) >= 2 and IsBound(t.params[2].useArray) then opts.useArray := t.params[2].useArray; fi;
            if Length(t.params) >= 2 and IsBound(t.params[2].useMont) then opts.useMont := t.params[2].useMont; fi;
            if Length(t.params) >= 2 and IsBound(t.params[2].gpuConfig) then opts.gpuConfig := t.params[2].gpuConfig; fi;
            if Length(t.params) >= 2 and IsBound(t.params[2].mxp) then opts.mxp := t.params[2].mxp; fi;
            if Length(t.params) >= 2 and IsBound(t.params[2].basesize) then 
                opts.basesize := t.params[2].basesize; 
                opts.dbasesize := opts.basesize * 2;
            fi;
            if Length(t.params) >= 2 and IsBound(t.params[2].insize) then opts.insize := t.params[2].insize; fi;
            if Length(t.params) >= 2 and IsBound(t.params[2].mbits) then opts.mbits := t.params[2].mbits; fi;
            if Length(t.params) >= 2 and IsBound(t.params[2].recursionLevel) then opts.recursionLevel := t.params[2].recursionLevel; fi;

            opts.globalUnrolling := 2;
            opts.tags := [ASIMTKernelFlag(ASIMTGridDimX), ASIMTBlockDimX];

            # syncwarp doesn't work for larger NTT sizes
            # using syncthreads instead
            opts.unparser.simt_synccluster := opts.unparser.simt_syncblock;

            opts.codegen := NTTXCUDACodegen;
            opts.postProcessCode := NTTXFixMxPCUDAOps;
            
            opts.twiddles := self.twiddles;
            # added for mxp l2 recursion
            if Length(t.params) >= 2 and IsBound(t.params[2].twiddles) then opts.twiddles := t.params[2].twiddles; fi;
            # Debug(true); Error();
            
            opts.modulusBitwidth := self.modulusBitwidth;
            opts.abstractType := self.abstractType;
            opts.machineBitwidth := self.machineBitwidth;
            opts.machineSignedType := self.machineSignedType;
            opts.machineMulType := self.machineMulType;

            opts.machineType := self.machineType;
            opts.machineDType := self.machineDType;

            # choose which mulqdd algorithm to use
            # schoolbook algorithm outperforms karatsuba on both l1 and l2 recursion
            if opts.recursionLevel = 1 then
                if not opts.useMont then
                    opts.mulqdd := MPMulQDD_Schoolbook_P;
                    if opts.gpuConfig = "rtx4090" and opts.insize = 128 and n >= 4096 then
                        if n < pow(2, 22).v then
                            opts.mulqdd := MPMulQDD_Karatsuba;
                        else
                            opts.mulqdd := MPMulQDD_Karatsuba_uo;
                        fi;
                    fi;
                else
                    # since Mont. usually requires full bit-width
                    opts.mulqdd := MPMulQDD_Schoolbook_F;
                fi;
            else
                opts.mulqdd := MPMulQDD_Schoolbook_F;
                # Debug(true); Error();
                if opts.gpuConfig = "h100" and opts.insize = 256 and n in [512, 1024] then
                    opts.mulqdd := MPMulQDD_Karatsuba;
                elif opts.gpuConfig = "rtx4090" and opts.insize = 256 then
                    opts.mulqdd := MPMulQDD_Karatsuba;
                    if n in [512, 1024] then
                        opts.mulqdd := MPMulQDD_Schoolbook_F;
                    fi;
                fi;
            fi;

            # opts.mbits := self.mbits;
            # opts.basesize := self.basesize;
            
            if opts.mxp then
                opts.unparser := NTTXMxPCUDAUnparser;
            else
                opts.unparser := NTTXMPCUDAUnparser;
            fi;

            opts.XType := TPtr(self.abstractType);
            opts.YType := TPtr(self.abstractType);
            # opts.useDeref := false;

            opts.breakdownRules.NTT := [ NTT_Base, CopyFields(NTT_KL_CUDA, rec(switch := true)) ];
            # _opts.breakdownRules.SkewNTT := [ SkewNTT_Base, SkewNTT_CT ];
            
            # 2048 is the largest size that 1024 threads can handle
            # SK:
            # 32-128b & l1 -> switch at 4096 with 1024 threads
            # 32-128b & l2 -> >=2048 needs 512 threads
            # 256b & l2 -> >=1024 needs 256 threads

            useNested := false;
            if opts.gpuConfig = "h100" and opts.insize = 256 and n = 512 then
                useNested := true;
            elif opts.gpuConfig = "h100" and opts.insize = 128 and n = 2048 then
                useNested := true;
            elif opts.gpuConfig = "rtx4090" and opts.insize = 128 and n = 2048 then
                useNested := true;
            elif opts.gpuConfig = "rtx4090" and opts.insize = 256 and n = 512 then
                useNested := true;
            fi;

            # Debug(true); Error();
            if N * pow(2, opts.recursionLevel - 1).v <= (2048/pow(2, opts.recursionLevel - 1).v) and not useNested then # does not work for 1K l2 MK 64bIn
            # if false then # 4090, SK, 2048-point, 128b; H100, MK, 2048-point, 128b, MK, 512-point, 256b
                opts.breakdownRules.TTensorI := [ IxA_SIMT, AxI_SIMT, L_IxA_SIMT_nopeel, IxA_L_SIMT_nopeel ]; 
            else
                # using loops within a thread block
                opts.breakdownRules.TTensorI := [ IxA_SIMT, AxI_SIMT, L_IxA_SIMT_nested, IxA_L_SIMT_nested ]; 

                nthread := 1024/pow(2, opts.recursionLevel - 1).v;
                if opts.insize >= 256 then nthread := nthread / 2; fi;
                
                # knowledge base for performance tuning
                # FUTURE: complete automation is supported by integrating with the SPIRAL profiler
                if opts.gpuConfig = "h100" then
                    if opts.insize = 128 then
                        if n = 2048 then 
                            nthread := 256;
                        elif n in [4096, 8192] then
                            nthread := 512;
                        elif n >= 16384 and n < pow(2,21).v then
                            nthread := 64;
                        fi;
                    elif opts.insize = 256 then
                        if n = 512 then
                            nthread := 128;
                        elif n > 2048 then
                            nthread := 512;
                        fi;
                    elif opts.insize = 512 then
                        if n in [128, 256] then
                            nthread := 64;
                        elif n >= pow(2,21).v then
                            nthread := 256;
                        fi;
                    elif opts.insize = 1024 then
                        if n >= pow(2,19).v then
                            nthread := 256;
                        fi;
                    fi;
                elif opts.gpuConfig = "v100" then
                    if opts.insize = 512 then
                        if n = 256 then
                            nthread := 64;
                        elif n >= 2048 then
                            nthread := 512;
                        fi;
                    elif opts.insize = 1024 then
                        if n >= 1024 then
                            nthread := 128;
                        fi;
                    fi;
                elif opts.gpuConfig = "rtx4090" then
                    if opts.insize = 128 then
                        if n >= 2048 and n < pow(2,22).v then 
                            nthread := 64;
                        fi;
                    elif opts.insize = 256 then
                        if n >= 4096 and n < pow(2,20).v then 
                            nthread := 64;
                        elif n in [512, 1024] then
                            nthread := 16;
                        fi;
                    elif opts.insize = 512 then
                        if n = 256 then
                            nthread := 64;
                        elif n >= 2048 then
                            nthread := 512;
                        fi;
                    elif opts.insize = 1024 then
                        if n >= 2048 then
                            nthread := 256;
                        fi;
                    fi;
                fi;

                # Debug(true); Error();

                L_IxA_SIMT_nested.max_threads := nthread;
                IxA_L_SIMT_nested.max_threads := nthread;
                
            fi;

            # Debug(true); Error();

            return opts;

        end,
        operations := rec(Print := s -> Print("<NTTX MxP CUDA Configuration>")),
        type := self >> self.abstractType
    ))
));

spiral.LocalConfig.nttx.bigintCUDAConf := (arg) -> NTTXBigIntCUDAConf(arg);
spiral.LocalConfig.nttx.mpCUDAConf := (arg) -> NTTXMPCUDAConf(arg);
spiral.LocalConfig.nttx.mxpCUDAConf := (arg) -> NTTXMxPCUDAConf(arg);


