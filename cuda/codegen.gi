Class(NTTXCUDACodegen, CudaCodegen, rec(

    # adapted from simt/cuda_codegen.gi
    make_kernels := meth(self, full_kernel, device_data, full_args, opts)
        local kercx, ker_cnt, ker, ker_args, ker_datas, cuda_ker, cuda_desc, cuda_icode, cuda_sub, 
                dim_grid, dim_block, tbody, tas_grid, tas_block_shmem, cross_ker_tas, ta;
                
        cuda_sub := Cond(IsBound(opts.cudasubName), Concat("ker_",opts.cudasubName), "ker_code");

        cuda_desc := rec(grid_tarrays := [], cuda_kers := [] );

        [full_kernel, ker_datas] := self.extract_ker_datas(full_kernel, opts);
        
        # Mark cross kernel temporaries
        cross_ker_tas := Filtered(Flat(List(Collect(full_kernel, @@(1, decl, (d, ctx) -> not IsBound(ctx.simt_block) or ctx.simt_block = [] )),
                            d -> d.vars)), v -> IsArrayT(v.t));
        DoForAll(cross_ker_tas, v -> v.setAttrTo("crossker", true));
        #Extract all temp arrays that should map to dev mem 
        tas_grid := self.extract_tarrays(full_kernel, 
                                            When(opts.use_shmem,
                                                    v -> (IsBound(v.crossker) and v.crossker) or (IsBound(v.t.size) and (v.t.size >= opts.max_shmem_size/8/2)),
                                                    True
                                            ), opts);
        #Allocate in dev mem 
        [full_kernel, tas_grid] := self.to_grid_arrays(full_kernel, tas_grid, full_args, opts);
        Append(cuda_desc.grid_tarrays, tas_grid);

        kercx := Collect(full_kernel, simt_block);
        kercx := When(kercx = [], [ full_kernel ], kercx);
        ker_cnt := 0;
        for ker in kercx do
            
            tbody := When(ObjId(ker) = simt_block, chain(ker.cmds), ker);
            
            # ker_args := Intersection(device_data, tbody.free())::Intersection(full_args, tbody.free());
            # this way to include modulus
            # Error(); 
            ker_args := Set(full_args);

            #Extract remaining shared mem temp arrays if required 
            tas_block_shmem := self.extract_tarrays(tbody, v -> opts.use_shmem, opts);
            #Allocate in shared mem 
            [tbody, tas_block_shmem] := self.to_block_shmem_arrays(tbody, tas_block_shmem, ker_args, opts);

            dim_grid := var.fresh_t_obj("g", Dim3(), rec( x := self.get_dim_idx(tbody, simtBlockIdxX), 
                                                          y := self.get_dim_idx(tbody, simtBlockIdxY), 
                                                          z := self.get_dim_idx(tbody, simtBlockIdxZ)
                                                        ) );
            dim_block := var.fresh_t_obj("b", Dim3(), rec( x := self.get_dim_idx(tbody, simtThreadIdxX), 
                                                           y := self.get_dim_idx(tbody, simtThreadIdxY), 
                                                           z := self.get_dim_idx(tbody, simtThreadIdxZ)
                                                        ) );
            # Error();
            cuda_ker := specifiers_func(["__global__"], TVoid, cuda_sub::StringInt(ker_cnt), Filtered(ker_args, d -> not IsBound(d.("decl_specs")) or not "__constant__" in d.("decl_specs")), tbody );

            Add(cuda_desc.cuda_kers, rec(dim_grid := dim_grid, dim_block := dim_block, cuda_ker := cuda_ker));

            ker_cnt := ker_cnt + 1;
        od;

        cuda_icode := chain(List(cuda_desc.cuda_kers, ck -> ck.cuda_ker));
        cuda_icode := self.ker_datas_to_device(ker_datas, cuda_icode, opts);

        return [cuda_desc, cuda_icode];

    end,

));