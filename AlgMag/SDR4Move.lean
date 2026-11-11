/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SDR4Orbit

/-!
# Lemma D, final bridge: the action on `𝔸(P)_T` and on the closed orbit

For Props. 3.31 (ii), 3.32 (ii) of `Algebraic Magnetism`, Steps 1-2. `π : 𝔸(P)_T → 𝔸(P₀)_T` is
invariant, and the orbit point is equivariant for the translation `m` of `𝔸(L)_{V'}`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgMag.SD

open AlgMag AlgMag.SQ AlgMag.SDTorus

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

section Along

variable {P P₀ Γ' : Type u} [AddCommMonoid P] [Countable P] [AddCommMonoid P₀] [Countable P₀] [AddCommGroup Γ']
  {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] (j : P₀ →+ P)

lemma SDR4_along {T' : BigFppfOver B S hS} (x : T' ⟶ specObj P T) :
    x ≫ specAlong T j = specLift (x ≫ specPr P T) (APt.along j (APt.res x.op (specPt P T))) := by
  refine specLift_uniq _ _ _ ?_ ?_
  · rw [Category.assoc, specAlong_pr]
  · rw [op_comp, APt.res_comp, res_specAlong]
    rfl

/-- `π` is invariant, for `δ ∘ j = 0`. -/
theorem SDR4_smulW_along (δ : P →+ Γ') (hk : ∀ k, δ (j k) = 0) {T' : BigFppfOver B S hS}
    (g : APt (fppfO B S hS) Γ' (op T')) (t : T' ⟶ specObj P T) :
    SDR3Coact_smulW δ g t ≫ specAlong T j = t ≫ specAlong T j := by
  rw [SDR4_along, SDR4_along]
  have h1 : SDR3Coact_smulW δ g t ≫ specPr P T = t ≫ specPr P T := specLift_pr _ _
  have h2 : APt.res (SDR3Coact_smulW δ g t).op (specPt P T) =
      g.comp (AddMonoidHom.toMultiplicative δ) * APt.res t.op (specPt P T) := res_specLift _ _
  rw [h1, h2]
  congr 1
  refine MonoidHom.ext fun k => ?_
  change g (Multiplicative.ofAdd (δ (j k.toAdd))) * _ = _
  rw [hk]
  have : g (Multiplicative.ofAdd (0 : Γ')) = 1 := map_one g
  rw [this, one_mul]
  rfl

end Along

section Move

variable {Γ' P : Type u} [AddCommGroup Γ'] [Countable Γ'] [AddGroup.FG Γ'] [AddCommMonoid P] [Countable P]
  (L : AddSubgroup Γ') (δ : P →+ Γ') {V' T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V')]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]

/-- The character on `𝔸(Γ)_{𝔸(L)}`: the point `pt(l) [l]`. -/
noncomputable def SDR4_cT : APt (fppfO B S hS) (SDR3Orbit_OM L) (op (specObj Γ' (specObj (SDR3Orbit_OM L) V'))) :=
  APt.res (specPr Γ' (specObj (SDR3Orbit_OM L) V')).op (specPt (SDR3Orbit_OM L) V') *
    APt.along (SDR4_omι L) (specPt Γ' (specObj (SDR3Orbit_OM L) V'))

/-- The translation `𝔸(Γ) × 𝔸(L)_{V'} → 𝔸(L)_{V'}`. -/
noncomputable def SDR4_m : specObj Γ' (specObj (SDR3Orbit_OM L) V') ⟶ specObj (SDR3Orbit_OM L) V' :=
  specLift (specPr Γ' _ ≫ specPr (SDR3Orbit_OM L) V') (SDR4_cT L)

lemma SDR4_m_pr :
    SDR4_m (V' := V') L ≫ specPr (SDR3Orbit_OM L) V' = specPr Γ' _ ≫ specPr (SDR3Orbit_OM L) V' := specLift_pr _ _

lemma SDR4_m_pt : APt.res (SDR4_m (V' := V') L).op (specPt (SDR3Orbit_OM L) V') = SDR4_cT L := res_specLift _ _

variable (t' : V' ⟶ T) (c' : APt (fppfO B S hS) P (op V')) (hL : ∀ p : Multiplicative P, δ p.toAdd ∉ L → c' p = 0)

/-- **Equivariance of the orbit point** on the factor `𝔸(P)_T`. -/
theorem SDR4_m_W :
    SDR4_m L ≫ specLift (specPr (SDR3Orbit_OM L) V' ≫ t') (SDR3Orbit_c₀ L δ c' hL) =
      SDR3Coact_smulW δ (specPt Γ' (specObj (SDR3Orbit_OM L) V'))
        (specPr Γ' _ ≫ specLift (specPr (SDR3Orbit_OM L) V' ≫ t') (SDR3Orbit_c₀ L δ c' hL)) := by
  classical
  let a₀ := specLift (specPr (SDR3Orbit_OM L) V' ≫ t') (SDR3Orbit_c₀ L δ c' hL)
  let pr := specPr Γ' (specObj (SDR3Orbit_OM L) V')
  have hp : (pr ≫ a₀) ≫ specPr P T = SDR4_m L ≫ specPr (SDR3Orbit_OM L) V' ≫ t' := by
    rw [Category.assoc, specLift_pr, ← Category.assoc (SDR4_m L), SDR4_m_pr, Category.assoc]
  have hr : APt.res (pr ≫ a₀).op (specPt P T) = APt.res pr.op (SDR3Orbit_c₀ L δ c' hL) := by
    rw [op_comp, APt.res_comp, res_specLift]
  rw [SDR3Orbit_comp_specLift]
  change _ = specLift ((pr ≫ a₀) ≫ specPr P T) (_ * APt.res (pr ≫ a₀).op (specPt P T))
  rw [hp, hr]
  congr 1
  refine MonoidHom.ext fun n => ?_
  by_cases h : δ n.toAdd ∈ L
  · have e0 := SDR3Orbit_c₀_pos L δ c' hL n h
    have e1 : APt.res (SDR4_m L).op (SDR3Orbit_c₀ L δ c' hL) n =
        APt.res (SDR4_m (V' := V') L).op (APt.res (specPr (SDR3Orbit_OM L) V').op c') n *
          APt.res (SDR4_m (V' := V') L).op (specPt (SDR3Orbit_OM L) V') (Multiplicative.ofAdd (SDR3Orbit_om L h)) := by
      rw [APt.res_apply, e0]
      exact map_mul _ _ _
    have e2 : APt.res pr.op (SDR3Orbit_c₀ L δ c' hL) n =
        APt.res pr.op (APt.res (specPr (SDR3Orbit_OM L) V').op c') n *
          APt.res pr.op (specPt (SDR3Orbit_OM L) V') (Multiplicative.ofAdd (SDR3Orbit_om L h)) := by
      rw [APt.res_apply, e0]
      exact map_mul _ _ _
    have e3 : APt.res (SDR4_m (V' := V') L).op (APt.res (specPr (SDR3Orbit_OM L) V').op c') =
        APt.res pr.op (APt.res (specPr (SDR3Orbit_OM L) V').op c') := by
      rw [← APt.res_comp, ← APt.res_comp, ← op_comp, ← op_comp, SDR4_m_pr]
    rw [e1, SDR4_m_pt, e3]
    change _ * (APt.res pr.op (specPt (SDR3Orbit_OM L) V') (Multiplicative.ofAdd (SDR3Orbit_om L h)) *
      specPt Γ' (specObj (SDR3Orbit_OM L) V') (Multiplicative.ofAdd (δ n.toAdd))) =
      specPt Γ' (specObj (SDR3Orbit_OM L) V') (Multiplicative.ofAdd (δ n.toAdd)) * APt.res pr.op (SDR3Orbit_c₀ L δ c' hL) n
    rw [e2]
    ring
  · have e0 := SDR3Orbit_c₀_neg L δ c' hL n h
    have e1 : APt.res (SDR4_m L).op (SDR3Orbit_c₀ L δ c' hL) n = 0 := by
      rw [APt.res_apply, e0]
      exact map_zero _
    have e2 : APt.res pr.op (SDR3Orbit_c₀ L δ c' hL) n = 0 := by
      rw [APt.res_apply, e0]
      exact map_zero _
    rw [e1, MonoidHom.mul_apply, e2, mul_zero]

end Move

end AlgMag.SD

#print axioms AlgMag.SD.SDR4_smulW_along
#print axioms AlgMag.SD.SDR4_m_W
