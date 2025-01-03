Class(NTT, TaggedNonTerminal, rec(
  abbrevs   := [ (n, p) -> Checked(IsPosInt(n), [n, p]) ],
  dims      := self >> let(size := self.params[1], [size, size]),
  terminate := self >> Error("Undefined."),
  # terminate := self >> Mat([[1, 1], [1, -1]]),
  transpose := self >> Copy(self),
  isReal    := self >> true,
  SmallRandom := () -> Random([2..5]),
  LargeRandom := () -> Random([6..15]),
  normalizedArithCost := self >> self.params[1]*2^self.params[1],
  TType := TInt
));


Class(SkewNTT, NTT, rec(
  abbrevs   := [ (n, i, p) -> Checked(IsPosInt(n), [n, i, p]) ]
));

Class(iNTT, NTT);
Class(iSkewNTT, SkewNTT);


Class(ModSwitch, NTT, rec(
  # doNotMarkBB := true,
));


