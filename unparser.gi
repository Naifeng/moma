Class(NTTXBigIntUnparser, CUnparser, rec(
    bigint := "BigInt",
    dbigint := "DBigInt",
    biguint := "BigInt",
    dbiguint := "DBigInt",
    T_Int := (self, t, vars, i, is) >> Print(self.bigint, " ", self.infix(vars, ", ", i + is)),
    T_UInt := (self, t, vars, i, is) >> Print(self.biguint, " ", self.infix(vars, ", ", i + is)),
#    add := (self, o, i, is) >> Cond(o.t = self.opts.abstractType, 
#        Print("ModAdd"::self.biguint, "(", self.infix(o.args::[self.opts.modulus], ", "),")"),
#        CUnparser.add(o, i, is)),
#    sub := (self, o, i, is) >> Cond(o.t = self.opts.abstractType, 
#        Print("ModSub"::self.biguint, "(", self.infix(o.args::[self.opts.modulus], ", "),")"),
#        CUnparser.sub(o, i, is)),
#    mul := (self, o, i, is) >> Cond(o.t = self.opts.abstractType, 
#        Print("ModMul"::When(IsBound(self.opts.useBarrettMult) and self.opts.useBarrettMult, "Barrett", "")::self.biguint, "(", 
#            self.infix(o.args::[self.opts.modulus]::When(IsBound(self.opts.useBarrettMult) and self.opts.useBarrettMult, [self.opts.barrettMu],[]), ", "),")"),
#        CUnparser.mul(o, i, is)),
#    assign := (self, o, i, is) >> Print(Blanks(i), "Assign"::self.biguint, "(", self(o.loc, i, is), ", ", self(o.exp, i, is), ");\n")
    addmod := (self, o, i, is) >> Print("ModAdd"::self.biguint, "(", self.infix(o.args, ", "), ")"),
    submod := (self, o, i, is) >> Print("ModSub"::self.biguint, "(", self.infix(o.args, ", "), ")"),
    mulmod := (self, o, i, is) >> Print("ModMul"::When(IsBound(self.opts.useBarrettMult) and self.opts.useBarrettMult, "Barrett", "")::self.biguint, 
        "(", self.infix(o.args, ", "), ")"),
));

Class(NTTXMPUnparser, CUnparser, rec(
    mp := "MP",
    qbaseint := "QBaseInt", # debug
    # TUInt := (self, t, vars, i, is) >> Print("uint", self.opts.basesize, "_t ", self.infix(vars, ", ", i + is)),
    # T_UInt := (self, t, vars, i, is) >> Print("uint", self.opts.dbasesize, "_t ", self.infix(vars, ", ", i + is)), # used for input params
    T_UInt := (self, t, vars, i, is) >> Print("uint", t.params[1], "_t ", self.infix(vars, ", ", i + is)), # for MxP
    TReal := (self, t, vars, i, is) >> Print(self.qbaseint, " ", self.infix(vars, ", ", i + is)), # debug
    addmod := (self, o, i, is) >> Print("_ModAdd"::self.mp, "(", self.infix(o.args, ", "), ")"),
    submod := (self, o, i, is) >> Print("_ModSub"::self.mp, "(", self.infix(o.args, ", "), ")"),
    mulmod := (self, o, i, is) >> Print("_ModMul"::self.mp, "(", self.infix(o.args, ", "), ")"),
    
    # for function inside the main body
    fmulqdd_l1 := (self, o, i, is) >> Print(Blanks(i), "MPMulQDD_L1", "(", self.infix(o.args, ", "), ");\n"),
    fmulqdd_l2 := (self, o, i, is) >> Print(Blanks(i), "MPMulQDD_L2", "(", self.infix(o.args, ", "), ");\n"),

    func := (self, o, i, is) >> let(
        parameters:=Flat(o.params),
        id := Cond(o.id="transform" and IsBound(self.opts.subName),
                     self.opts.subName,
                   o.id="init"      and IsBound(self.opts.subName),
                     Concat("init_",self.opts.subName),
                   o.id="destroy"   and IsBound(self.opts.subName),
                     Concat("destroy_",self.opts.subName),
                   o.id),
		When((IsBound(self.opts.wrapCFuncs) and self.opts.wrapCFuncs), Print("\nextern \"C\" {")),
        # Error(),
        Print("\n", Blanks(i), self.opts.funcModifier, self.declare(o.ret, var(id, o.ret), i, is), "(",
            Cond(o.id="MPMulQDD_L1", DoForAll(Sublist(parameters,1,4), p->Print(self.declare(p.t, "", i, is), "&", p, ", ")), 
                 o.id="MPMulQDD_L2", DoForAll(Sublist(parameters,1,8), p->Print(self.declare(p.t, "", i, is), "&", p, ", ")), 
                                     ""),
            Cond(o.id="MPMulQDD_L1", DoForAllButLast(Sublist(parameters,5,8), p->Print(self.declare(p.t, p,i,is), ", ")),
                 o.id="MPMulQDD_L2", DoForAllButLast(Sublist(parameters,9,16), p->Print(self.declare(p.t, p,i,is), ", ")),
                                     DoForAllButLast(parameters, p->Print(self.declare(p.t, p,i,is), ", "))
            ),
            When(Length(parameters)>0, self.declare(Last(parameters).t, Last(parameters),i,is), ""), ") ",
            "{\n",
            When(IsBound(self.opts.postalign), DoForAll(parameters, p->self.opts.postalign(p,i+is,is))),
            self(o.cmd, i+is, is),
            Blanks(i),
            "}\n"
        ),
        When((IsBound(self.opts.wrapCFuncs) and self.opts.wrapCFuncs), Print("}\n"))),
));

Class(NTTXMPPyUnparser, CUnparser, rec(
    mp := "MPPy",
    qbaseint := "QBaseInt", # debug
    # TUInt := (self, t, vars, i, is) >> Print("uint", self.opts.basesize, "_t ", self.infix(vars, ", ", i + is)),
    # T_UInt := (self, t, vars, i, is) >> Print("uint", self.opts.dbasesize, "_t ", self.infix(vars, ", ", i + is)), # used for input params
    T_UInt := (self, t, vars, i, is) >> Print("uint", t.params[1], "_t ", self.infix(vars, ", ", i + is)), # for MxP
    addmod := (self, o, i, is) >> Print("addmod(", self.infix(o.args, ", "), ")"),
    submod := (self, o, i, is) >> Print("submod(", self.infix(o.args, ", "), ")"),
    mulmod := (self, o, i, is) >> Print("mulmod(", self.infix(o.args, ", "), ")"),
    assign := (self,o,i,is) >> Print(Blanks(i), self(o.loc,i,is), " = ", self(o.exp,i,is), "\n"),
    includes := [],
    loop := (self, o, i, is) >> let(v := o.var, lo := o.range[1], hi := Last(o.range),
        Print(Blanks(i), "for ", v, " in range(", lo, ", ", hi+1, "):\n",
          self(o.cmd,i+is,is))),
    decl := meth(self,o,i,is)
        local arrays, other, l, arri, myMem;
        [arrays, other] := SplitBy(o.vars, x->IsArray(x.t));
        # DoForAll(arrays, v -> Print(Blanks(i), 
        #                             When(self.opts.arrayBufModifier <> "", self.opts.arrayBufModifier::" ", ""), 
        #                             self.declare(v.t, v, i, is), ";\n"));
        DoForAll(arrays, v -> Print(Blanks(i), 
                            When(self.opts.arrayBufModifier <> "", self.opts.arrayBufModifier::" ", ""), 
                            # Debug(true),
                            # Error(),
                            v, " = [0] * ", v.t.size, "\n"));

        if (Length(other)>0) then
            other:=SortRecordList(other,x->x.t);
            for l in other do
               Sort(l, (a,b)->a.id < b.id);
               # Print(Blanks(i), self.declare(l[1].t, l, i, is), ";\n");
               Print("");
            od;
        fi;

        self(o.cmd, i, is);

        #Pop arena for this decl
        if IsBound(self.opts.useMemoryArena) and self.opts.useMemoryArena and Length(arrays) > 0 and arrays[1].id[1] <> 'D' then
          myMem := 0;
          for arri in arrays do 
             # Account for vector allocations in memory arena (which is scalar)
             myMem := myMem + (arri.t.size * When(IsBound(arri.t.t) and ObjId(arri.t.t)=TVect, arri.t.t.size, 1));
          od;
          if ObjId(myMem) = Value then myMem := myMem.v; fi;
          Print(Blanks(i));
          Print("arenalevel += ", myMem, ";\n" );
        fi;
    end,
    func := (self, o, i, is) >> let(
        parameters:=Flat(o.params),
        id := Cond(o.id="transform" and IsBound(self.opts.subName),
                     self.opts.subName,
                   o.id="init"      and IsBound(self.opts.subName),
                     Concat("init_",self.opts.subName),
                   o.id="destroy"   and IsBound(self.opts.subName),
                     Concat("destroy_",self.opts.subName),
                   o.id),
        When ((IsBound(self.opts.wrapCFuncs) and self.opts.wrapCFuncs), Print("\nextern \"C\" {")),
            Print("\n", Blanks(i),
                "def ", var(id, o.ret), "(",
                DoForAllButLast(parameters, p->Print(p, ", ")),
                When(Length(parameters)>0, Last(parameters), ""), "): ",
                "\n",
                When(IsBound(self.opts.postalign), DoForAll(parameters, p->self.opts.postalign(p,i+is,is))),
                self(o.cmd, i+is, is),
                Blanks(i),
                "\n"),
        When ((IsBound(self.opts.wrapCFuncs) and self.opts.wrapCFuncs), Print("}\n"))),
    generated_by := Concat("\n# This code was generated by Spiral ", SpiralVersion, ", www.spiral.net\n"),
));

