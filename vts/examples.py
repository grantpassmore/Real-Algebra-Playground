import z3rcf
import uni_vts

f_1 = [-2, 1]
f_2 = [2, -3, 1]
print uni_vts.internal_vts([], [f_1], [f_2], [])
f_3 = [-1, 1]
print uni_vts.internal_vts([], [], [f_2], [f_1, f_3])


eps_1 = z3rcf.MkInfinitesimal('eps_1')
eps_2 = z3rcf.MkInfinitesimal('eps_2')
h_1 = [-eps_2, 1]
h_2 = [eps_1 * eps_2, -(eps_1 + eps_2), 1]
print uni_vts.internal_vts([], [h_1], [h_2], [])
h_3 = [-eps_1, 1]
print uni_vts.internal_vts([], [], [h_2], [h_1, h_3])

print uni_vts.internal_vts([], [h_3], [h_2], [])
