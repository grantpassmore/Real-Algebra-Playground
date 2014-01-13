import sympy as s
import sympy.abc
import muchnik as m
import sympywrapper as sw

#x = s.var('x')
x, y, z = sympy.abc.x, sympy.abc.y, sympy.abc.z

mer = m.Muchniker(sw.SympyWrapper(x))
