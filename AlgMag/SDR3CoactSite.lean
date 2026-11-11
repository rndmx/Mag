/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SDR3CoactBase
import AlgMag.SDLocSFactor

/-!
# Lemma D, Steps 2, 3: the action as a morphism, the coaction on sections

For `Z` in the site with an action of `D(Λ)` on points and `r : Z → W`, `W` affine,
`Y = Spec O(W)[Λ] ×_W Z` is `D(Λ) × Z`. The action on points is a morphism `a : Y → Z`
(`SDR3Coact_a`), `a(π⁻¹ U₀)` is open and saturated (`SDR3Coact_sat`), and for `Z` quasi-compact the action
gives a coaction on `Γ(Z)` (`SDR3Coact_coact`).
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgMag.SD

open AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

variable (Λ : Type u) [AddCommGroup Λ] [Countable Λ] {W Z : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]

/-- `D(Λ) × Z`. -/
noncomputable abbrev SDR3Coact_Y (r : Z ⟶ W) : BigFppfOver B S hS := pullback (specPr Λ W) r

/-- The projection `D(Λ) × Z → Z`. -/
noncomputable abbrev SDR3Coact_π (r : Z ⟶ W) : SDR3Coact_Y Λ r ⟶ Z := pullback.snd _ _

/-- The universal point of `D(Λ)` on `D(Λ) × Z`. -/
noncomputable def SDR3Coact_χ (r : Z ⟶ W) : APt (fppfO B S hS) Λ (op (SDR3Coact_Y Λ r)) :=
  APt.res (pullback.fst (specPr Λ W) r).op (specPt Λ W)

variable {Λ}

/-- The point `(c, t)` of `D(Λ) × Z`. -/
noncomputable def SDR3Coact_pt {r : Z ⟶ W} {T : BigFppfOver B S hS} (t : T ⟶ Z) (c : APt (fppfO B S hS) Λ (op T)) :
    T ⟶ SDR3Coact_Y Λ r :=
  pullback.lift (specLift (t ≫ r) c) t (specLift_pr _ _)

@[reassoc (attr := simp)]
lemma SDR3Coact_pt_π {r : Z ⟶ W} {T : BigFppfOver B S hS} (t : T ⟶ Z) (c : APt (fppfO B S hS) Λ (op T)) :
    SDR3Coact_pt (r := r) t c ≫ SDR3Coact_π Λ r = t := pullback.lift_snd _ _ _

lemma SDR3Coact_pt_χ {r : Z ⟶ W} {T : BigFppfOver B S hS} (t : T ⟶ Z) (c : APt (fppfO B S hS) Λ (op T)) :
    APt.res (SDR3Coact_pt (r := r) t c).op (SDR3Coact_χ Λ r) = c := by
  unfold SDR3Coact_χ
  rw [← APt.res_comp, ← op_comp, SDR3Coact_pt, pullback.lift_fst]
  exact res_specLift _ _

lemma SDR3Coact_hom_ext {r : Z ⟶ W} {T : BigFppfOver B S hS} {h h' : T ⟶ SDR3Coact_Y Λ r}
    (h1 : h ≫ SDR3Coact_π Λ r = h' ≫ SDR3Coact_π Λ r)
    (h2 : APt.res h.op (SDR3Coact_χ Λ r) = APt.res h'.op (SDR3Coact_χ Λ r)) : h = h' := by
  have key : ∀ k : T ⟶ SDR3Coact_Y Λ r, k = SDR3Coact_pt (k ≫ SDR3Coact_π Λ r) (APt.res k.op (SDR3Coact_χ Λ r)) := by
    intro k
    refine pullback.hom_ext ?_ ?_
    · rw [SDR3Coact_pt, pullback.lift_fst]
      refine specLift_uniq _ _ _ ?_ ?_
      · rw [Category.assoc, pullback.condition, Category.assoc]
      · unfold SDR3Coact_χ
        rw [← APt.res_comp, ← op_comp]
    · rw [SDR3Coact_pt, pullback.lift_snd]
  rw [key h, key h', h1, h2]

variable (actZ : AAction (fppfO B S hS) Λ (yoneda.obj Z)) (r : Z ⟶ W)

/-- **Step 2**: the action as a morphism `D(Λ) × Z → Z`. -/
noncomputable def SDR3Coact_a : SDR3Coact_Y Λ r ⟶ Z :=
  actZ.smul (U := op (SDR3Coact_Y Λ r)) (SDR3Coact_χ Λ r) (SDR3Coact_π Λ r)

lemma SDR3Coact_pt_a {T : BigFppfOver B S hS} (t : T ⟶ Z) (c : APt (fppfO B S hS) Λ (op T)) :
    SDR3Coact_pt (r := r) t c ≫ SDR3Coact_a actZ r = actZ.smul (U := op T) c t := by
  have h := actZ.map_smul (SDR3Coact_pt (r := r) t c).op (SDR3Coact_χ Λ r) (SDR3Coact_π Λ r)
  rw [SDR3Coact_pt_χ] at h
  have h2 : (yoneda.obj Z).map (SDR3Coact_pt (r := r) t c).op (SDR3Coact_π Λ r) = t := SDR3Coact_pt_π t c
  rw [h2] at h
  exact h

/-- `Y₂ = D(Λ) × D(Λ) × Z`, with `p (t,s,z) = (s,z)`. -/
noncomputable abbrev SDR3Coact_Y₂ : BigFppfOver B S hS := SDR3Coact_Y Λ (SDR3Coact_π Λ r ≫ r)

/-- `p (t,s,z) = (s,z)`. -/
noncomputable abbrev SDR3Coact_p : SDR3Coact_Y₂ (Λ := Λ) r ⟶ SDR3Coact_Y Λ r := SDR3Coact_π Λ (SDR3Coact_π Λ r ≫ r)

/-- `τ (t,s,z) = t`. -/
noncomputable abbrev SDR3Coact_τ : APt (fppfO B S hS) Λ (op (SDR3Coact_Y₂ (Λ := Λ) r)) :=
  SDR3Coact_χ Λ (SDR3Coact_π Λ r ≫ r)

/-- `s (t,s,z) = s`. -/
noncomputable abbrev SDR3Coact_s : APt (fppfO B S hS) Λ (op (SDR3Coact_Y₂ (Λ := Λ) r)) :=
  APt.res (SDR3Coact_p (Λ := Λ) r).op (SDR3Coact_χ Λ r)

/-- `m (t,s,z) = (ts,z)`. -/
noncomputable def SDR3Coact_m : SDR3Coact_Y₂ (Λ := Λ) r ⟶ SDR3Coact_Y Λ r :=
  SDR3Coact_pt (SDR3Coact_p r ≫ SDR3Coact_π Λ r) (SDR3Coact_τ r * SDR3Coact_s r)

/-- `act (t,s,z) = (t,sz)`. -/
noncomputable def SDR3Coact_act : SDR3Coact_Y₂ (Λ := Λ) r ⟶ SDR3Coact_Y Λ r :=
  SDR3Coact_pt (SDR3Coact_p r ≫ SDR3Coact_a actZ r) (SDR3Coact_τ r)

/-- The unit section `z ↦ (1,z)`. -/
noncomputable def SDR3Coact_e : Z ⟶ SDR3Coact_Y Λ r := SDR3Coact_pt (𝟙 Z) 1

/-- `ι (t,z) = (t⁻¹,tz)`. -/
noncomputable def SDR3Coact_ι : SDR3Coact_Y Λ r ⟶ SDR3Coact_Y Λ r :=
  SDR3Coact_pt (SDR3Coact_a actZ r) (APt.inv (SDR3Coact_χ Λ r))

lemma SDR3Coact_p_a : SDR3Coact_p (Λ := Λ) r ≫ SDR3Coact_a actZ r =
    actZ.smul (U := op (SDR3Coact_Y₂ (Λ := Λ) r)) (SDR3Coact_s r) (SDR3Coact_p r ≫ SDR3Coact_π Λ r) :=
  actZ.map_smul (SDR3Coact_p (Λ := Λ) r).op (SDR3Coact_χ Λ r) (SDR3Coact_π Λ r)

lemma SDR3Coact_m_a : SDR3Coact_m (Λ := Λ) r ≫ SDR3Coact_a actZ r = SDR3Coact_act actZ r ≫ SDR3Coact_a actZ r := by
  rw [SDR3Coact_m, SDR3Coact_act, SDR3Coact_pt_a, SDR3Coact_pt_a, SDR3Coact_p_a, actZ.mul_smul]

lemma SDR3Coact_e_a : SDR3Coact_e (Λ := Λ) r ≫ SDR3Coact_a actZ r = 𝟙 Z := by
  rw [SDR3Coact_e, SDR3Coact_pt_a]
  exact actZ.one_smul (U := op Z) (𝟙 Z)

lemma SDR3Coact_ι_π : SDR3Coact_ι actZ r ≫ SDR3Coact_π Λ r = SDR3Coact_a actZ r := SDR3Coact_pt_π _ _

lemma SDR3Coact_ι_a : SDR3Coact_ι actZ r ≫ SDR3Coact_a actZ r = SDR3Coact_π Λ r := by
  rw [SDR3Coact_ι, SDR3Coact_pt_a]
  change actZ.smul (U := op (SDR3Coact_Y Λ r)) _ (actZ.smul (U := op (SDR3Coact_Y Λ r)) _ _) = _
  rw [← actZ.mul_smul, APt.inv_mul]
  exact actZ.one_smul (U := op (SDR3Coact_Y Λ r)) _

/-- `Y₂` is the fibre product of `a` and `π`, in the site. -/
theorem SDR3Coact_isPullback_site :
    IsPullback (SDR3Coact_p (Λ := Λ) r) (SDR3Coact_act actZ r) (SDR3Coact_a actZ r) (SDR3Coact_π Λ r) := by
  have hw : SDR3Coact_p (Λ := Λ) r ≫ SDR3Coact_a actZ r = SDR3Coact_act actZ r ≫ SDR3Coact_π Λ r :=
    (SDR3Coact_pt_π _ _).symm
  refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk hw (fun c => SDR3Coact_pt c.fst (APt.res c.snd.op (SDR3Coact_χ Λ r)))
    (fun c => SDR3Coact_pt_π _ _) (fun c => ?_) (fun c l h1 h2 => ?_)⟩⟩
  · refine SDR3Coact_hom_ext ?_ ?_
    · rw [SDR3Coact_act, Category.assoc, SDR3Coact_pt_π, ← Category.assoc, SDR3Coact_pt_π]
      exact c.condition
    · rw [SDR3Coact_act, op_comp, APt.res_comp, SDR3Coact_pt_χ, SDR3Coact_pt_χ]
  · refine SDR3Coact_hom_ext ?_ ?_
    · rw [SDR3Coact_pt_π, h1]
    · rw [SDR3Coact_pt_χ, ← h2, SDR3Coact_act, op_comp, APt.res_comp, SDR3Coact_pt_χ]

/-- **Step 2**, saturation: `V = a(π⁻¹ U₀)` satisfies `a y ∈ V ↔ π y ∈ V`. -/
theorem SDR3Coact_sat (U₀ : Set ((SCH).obj Z)) (y : (SCH).obj (SDR3Coact_Y Λ r)) :
    (SCH).map (SDR3Coact_a actZ r) y ∈ (SCH).map (SDR3Coact_a actZ r) '' ((SCH).map (SDR3Coact_π Λ r) ⁻¹' U₀) ↔
      (SCH).map (SDR3Coact_π Λ r) y ∈ (SCH).map (SDR3Coact_a actZ r) '' ((SCH).map (SDR3Coact_π Λ r) ⁻¹' U₀) := by
  refine SDR3Coact_saturated (p := (SCH).map (SDR3Coact_p (Λ := Λ) r)) (m := (SCH).map (SDR3Coact_m r))
    (act := (SCH).map (SDR3Coact_act actZ r)) (ι := (SCH).map (SDR3Coact_ι actZ r))
    ((SDR3Coact_isPullback_site actZ r).map (SCH)) ?_ ?_ ?_ ?_ U₀ y
  · rw [← Functor.map_comp, ← Functor.map_comp, SDR3Coact_m, SDR3Coact_pt_π]
  · rw [← Functor.map_comp, ← Functor.map_comp, SDR3Coact_m_a]
  · rw [← Functor.map_comp, SDR3Coact_ι_π]
  · rw [← Functor.map_comp, SDR3Coact_ι_a]

end AlgMag.SD

#print axioms AlgMag.SD.SDR3Coact_sat
