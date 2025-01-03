#_T_Int := CopyFields(T_Int, rec(value := (self, v) >> Value.new(_T_Int(self.params[1]), v)));

_T_IntMod := T_UInt;

# T_Int computes the modulo which is very slow. This is a way to turn this off
spiral.code.T_UInt.check := (self, v) >> v;

