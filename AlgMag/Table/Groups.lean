/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Table.Compute

/-!
# Table 1: the root data of rank ≤ 3

Cartan matrix `A i j = ⟨α_i, α_j^∨⟩` (Bourbaki numbering; `B_n`: `α_n` short, `C_n`: `α_n` long,
`G_2`: `α_1` short) and generators of `M` in fundamental-weight coordinates (`P` = identity,
`Q` = rows of `A`). `B_1 = C_1 = A_1`, `D_2 = A_1 × A_1`, `D_3 = A_3`: `Spin_3 = Sp_2 = SL_2`,
`SO_3 = PSp_2 = PGL_2`, `Spin_6 = SL_4`, `SO_6 = SL_4/μ_2`, `PSO_6 = PGL_4` (same root datum).
-/

namespace AlgMag.Table

def cA1 : Mat := [[2]]
def cA2 : Mat := [[2, -1], [-1, 2]]
def cB2 : Mat := [[2, -2], [-1, 2]]
def cC2 : Mat := [[2, -1], [-2, 2]]
def cD2 : Mat := [[2, 0], [0, 2]]
def cG2 : Mat := [[2, -1], [-3, 2]]
def cA3 : Mat := [[2, -1, 0], [-1, 2, -1], [0, -1, 2]]
def cB3 : Mat := [[2, -1, 0], [-1, 2, -2], [0, -1, 2]]
def cC3 : Mat := [[2, -1, 0], [-1, 2, -1], [0, -2, 2]]

def SL2 : RD := ofCartan cA1 (idMat 1)
def PGL2 : RD := ofCartan cA1 cA1
def SL3 : RD := ofCartan cA2 (idMat 2)
def PGL3 : RD := ofCartan cA2 cA2
def Spin5 : RD := ofCartan cB2 (idMat 2)
def SO5 : RD := ofCartan cB2 cB2
def Sp4 : RD := ofCartan cC2 (idMat 2)
def PSp4 : RD := ofCartan cC2 cC2
def Spin4 : RD := ofCartan cD2 (idMat 2)
def PSO4 : RD := ofCartan cD2 cD2
/-- `M = Q + ℤ(ϖ_1 + ϖ_2)`. -/
def SO4 : RD := ofCartan cD2 (cD2 ++ [[1, 1]])
/-- `M = Q + ℤϖ_1` (`≅ SL_2 × PGL_2`). -/
def HSpin4 : RD := ofCartan cD2 (cD2 ++ [[1, 0]])
def G2 : RD := ofCartan cG2 cG2
def SL4 : RD := ofCartan cA3 (idMat 3)
/-- `M = Q + ℤ 2ϖ_1`. -/
def SL4mu2 : RD := ofCartan cA3 (cA3 ++ [[2, 0, 0]])
def PGL4 : RD := ofCartan cA3 cA3
def Spin7 : RD := ofCartan cB3 (idMat 3)
def SO7 : RD := ofCartan cB3 cB3
def Sp6 : RD := ofCartan cC3 (idMat 3)
def PSp6 : RD := ofCartan cC3 cC3

end AlgMag.Table
