# Used for the lambda function in modulus switching
DefaultCodegen.Pointwise := (self, o, y, x, opts) >> let(
    i := Ind(), 
    elt := o.element,
    loop(i, elt.domain(), Compile(chain(assign(nth(y,i), RulesStrengthReduce(elt.at(i).at(nth(x,i))))), opts))
);
