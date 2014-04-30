import z3rcf
from uni_vts import internal_vts
import prog_printer

prog_printer.mute()

print "===FIRST EXAMPLE==="
f_1 = [-2, 1]
f_2 = [2, -3, 1]
f_3 = [-1, 1]
print internal_vts([], [f_1], [f_2], [])
print internal_vts([], [f_1], [f_2], [f_3])

print "\n===SECOND EXAMPLE==="
eps_1 = z3rcf.MkInfinitesimal('eps_1')
eps_2 = z3rcf.MkInfinitesimal('eps_2')
h_1 = [-eps_2, 1]
h_2 = [eps_1 * eps_2, -(eps_1 + eps_2), 1]
h_3 = [-eps_1, 1]
print internal_vts([], [h_1], [h_2], [])
print "",
print internal_vts([], [h_3], [h_2], [])
print internal_vts([], [h_1], [h_2], [h_3])


print "\n===THIRD EXAMPLE==="
g_1 = [24, -50, 35, -10, 1]
g_2 = [4, 0, -5, 0, 1]
print internal_vts([], [g_1, g_2], [], [])

g_3 = [-1, 1]
g_4 = [2, -1]
print internal_vts([g_3], [g_1, g_2], [], [])
print internal_vts([g_4], [g_1, g_2], [], [])

eps = z3rcf.MkInfinitesimal('eps')
g_5 = [-1 - eps, 1]
g_6 = [2 - eps, -1]
print internal_vts([], [g_5, g_1, g_2], [], [])
print internal_vts([], [g_6, g_1, g_2], [], [])

# (x-1)*(x-2)*(x-3)*(x-4)
g1 = [-24, 50, -35, 10, 1]
# (x + 0.5)*(x - 0.5)*(x-1.5)*(x-2.5)
g2 = [-0.9375, 1, 3.5, -4, 1]
internal_vts([], [g1, g2], [], [])
