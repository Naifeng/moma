Class(mulmod, mul);
Class(addmod, add);
Class(submod, add);
Class(fmulqdd, assign_cmd, rec(
    op_in := self >> Set([self.args[2], self.args[3]]), 
    op_out := self >> Set([self.args[1]]),
    op_inout := self >> Set([]),
    # isExpComposite := false # disable BinSplit on this exp
));

Class(fmulqdd_l1, assign_cmd, rec(
    op_in := self >> Set([self.args[5], self.args[6], self.args[7], self.args[8]]), 
    op_out := self >> Set([self.args[1], self.args[2], self.args[3], self.args[4]]),
    op_inout := self >> Set([]),
    isMacro := true
    # isExpComposite := false # disable BinSplit on this exp
));
Class(fmulqdd_l2, assign_cmd, rec(
    op_in := self >> Set([self.args[9], self.args[10], self.args[11], self.args[12],
                          self.args[13], self.args[14], self.args[15], self.args[16]]), 
    op_out := self >> Set([self.args[1], self.args[2], self.args[3], self.args[4], 
                           self.args[5], self.args[6], self.args[7], self.args[8]]),
    op_inout := self >> Set([]),
    isMacro := true,
    isExpComposite := true # setting to false disables BinSplit on this exp
));
Class(fmulqdd_l3, assign_cmd, rec(
    op_in := self >> Set(List([17..32], i -> self.args[i])),
    op_out := self >> Set(List([1..16], i -> self.args[i])),
    op_inout := self >> Set([]),
    zeroArg := 0,
    isMacro := true,
    isExpComposite := true # setting to false disables BinSplit on this exp
));
Class(fmulqdd_l4, assign_cmd, rec(
    op_in := self >> Set(List([33..64], i -> self.args[i])),
    op_out := self >> Set(List([1..32], i -> self.args[i])),
    op_inout := self >> Set([]),
    zeroArg := 0,
    isMacro := true,
    isExpComposite := true # setting to false disables BinSplit on this exp
));