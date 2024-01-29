from z3 import Bool, And, simplify

a = Bool('a')
b = Bool('b')
c = Bool('c')

print(simplify(And(a,And(b,c))))