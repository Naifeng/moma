# TODO: make this cudabigint
Class(NTTXCUDAUnparser, CudaUnparser, rec(
    # adapted from NTTXBigIntUnparser
    cudaint := "BigInt", # BigInt for now to make use of big_int.h for verification
    T_UInt := (self, t, vars, i, is) >> Print(self.cudaint, " ", self.infix(vars, ", ", i + is)),
    
    addmod := (self, o, i, is) >> Print("ModAdd"::self.cudaint, "(", self.infix(o.args, ", "), ")"),
    submod := (self, o, i, is) >> Print("ModSub"::self.cudaint, "(", self.infix(o.args, ", "), ")"),
    mulmod := (self, o, i, is) >> Print("ModMul"::When(IsBound(self.opts.useBarrettMult) and self.opts.useBarrettMult, "Barrett", "")::self.cudaint, 
        "(", self.infix(o.args, ", "), ")"),

));

Class(NTTXCUDANativeUnparser, CudaUnparser, rec(
    # adapted from NTTXBigIntUnparser
    # deprecated
    # nativeint_32 := "uint32_t", 
    # nativeint_64 := "uint64_t", 
    # nativeint_64 := "uint128_t", 
    # T_Int := (self, t, vars, i, is) >> Print(self.nativeint_64, " ", self.infix(vars, ", ", i + is)),
    # T_UInt := (self, t, vars, i, is) >> Print(self.nativeint_64, " ", self.infix(vars, ", ", i + is)),

    T_Int := (self, t, vars, i, is) >> Print("uint", t.params[1], "_t ", self.infix(vars, ", ", i + is)),
    T_UInt := (self, t, vars, i, is) >> Print("uint", t.params[1], "_t ", self.infix(vars, ", ", i + is)),

));

# TODO: add cudamp - ?
Class(NTTXMPCUDAUnparser, CudaUnparser, rec(
    mp := "MP",
    TUInt := (self, t, vars, i, is) >> Print("uint", self.opts.basesize, "_t ", self.infix(vars, ", ", i + is)),
    T_UInt := (self, t, vars, i, is) >> Print("uint", self.opts.dbasesize, "_t ", self.infix(vars, ", ", i + is)),
    addmod := (self, o, i, is) >> Print("_ModAdd"::self.mp, "(", self.infix(o.args, ", "), ")"),
    submod := (self, o, i, is) >> Print("_ModSub"::self.mp, "(", self.infix(o.args, ", "), ")"),
    mulmod := (self, o, i, is) >> Print("_ModMul"::self.mp, "(", self.infix(o.args, ", "), ")"),
));

Class(NTTXMxPCUDAUnparser, CudaUnparser, rec(
    mp := "MxP",
    # T_UInt := (self, t, vars, i, is) >> Error(),
    T_UInt := (self, t, vars, i, is) >> Print("uint", t.params[1], "_t ", self.infix(vars, ", ", i + is)),
    addmod := (self, o, i, is) >> Print("_ModAdd"::self.mp, "(", self.infix(o.args, ", "), ")"),
    submod := (self, o, i, is) >> Print("_ModSub"::self.mp, "(", self.infix(o.args, ", "), ")"),
    mulmod := (self, o, i, is) >> Print("_ModMul"::self.mp, "(", self.infix(o.args, ", "), ")"),

    # for function inside the main body
    fmulqdd_l1 := (self, o, i, is) >> Print(Blanks(i), "MPMulQDD_L1", "(", self.infix(o.args, ", "), ");\n"),
    fmulqdd_l2 := (self, o, i, is) >> Print(Blanks(i), "MPMulQDD_L2", "(", self.infix(o.args, ", "), ");\n"),
    fmulqdd_l3 := (self, o, i, is) >> Print(Blanks(i), Cond(o.zeroArg=0, "MPMulQDD_L3", o.zeroArg=1, "MPMulQDD_L3_1", o.zeroArg=2, "MPMulQDD_L3_2"), "(", self.infix(o.args, ", "), ");\n"),
    fmulqdd_l4 := (self, o, i, is) >> Print(Blanks(i), Cond(o.zeroArg=0, "MPMulQDD_L4", o.zeroArg=1, "MPMulQDD_L4_1", o.zeroArg=2, "MPMulQDD_L4_2"), "(", self.infix(o.args, ", "), ");\n"),

    specifiers_func := (self, o, i, is) >> let(
        parameters := Flat(o.params),
        id := o.id,
        Print("\n", Blanks(i),
            self.opts.funcModifier, self.infix(o.decl_specs, " "), " ", self.declare(o.ret, var(id, o.ret), i, is), "(",
            
            Cond(o.id="MPMulQDD_L1", DoForAll(Sublist(parameters,1,4), p->Print(self.declare(p.t, "", i, is), "&", p, ", ")), 
                 o.id="MPMulQDD_L2", DoForAll(Sublist(parameters,1,8), p->Print(self.declare(p.t, "", i, is), "&", p, ", ")), 
                 IsSubset(o.id, "MPMulQDD_L3"), DoForAll(Sublist(parameters,1,16), p->Print(self.declare(p.t, "", i, is), "&", p, ", ")),
                 IsSubset(o.id, "MPMulQDD_L4"), DoForAll(Sublist(parameters,1,32), p->Print(self.declare(p.t, "", i, is), "&", p, ", ")),
                                     ""),
            Cond(o.id="MPMulQDD_L1", DoForAllButLast(Sublist(parameters,5,8), p->Print(self.declare(p.t, p,i,is), ", ")),
                 o.id="MPMulQDD_L2", DoForAllButLast(Sublist(parameters,9,16), p->Print(self.declare(p.t, p,i,is), ", ")),
                 IsSubset(o.id, "MPMulQDD_L3"), DoForAllButLast(Sublist(parameters,17,32), p->Print(self.declare(p.t, p,i,is), ", ")),
                 IsSubset(o.id, "MPMulQDD_L4"), DoForAllButLast(Sublist(parameters,33,64), p->Print(self.declare(p.t, p,i,is), ", ")),
                                     DoForAllButLast(parameters, p->Print(self.declare(p.t, p,i,is), ", "))
            ),
            
            When(Length(parameters)>0, self.declare(Last(parameters).t, Last(parameters),i,is), ""), ") ",
            "{\n",
            When(IsBound(self.opts.postalign), DoForAll(parameters, p->self.opts.postalign(p,i+is,is))),
            self(o.cmd, i+is, is),
            Blanks(i),
            "}\n")),
));