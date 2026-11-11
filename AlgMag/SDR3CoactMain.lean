/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SDR3CoactLift

/-!
# Lemma D, Steps 2, 3: the saturated open with its coaction

Entry point of Steps 2, 3 for the rest of `SDLocS_InvChart`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgMag.SD

open AlgMag AlgMag.SQ

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

variable {Λ : Type u} [AddCommGroup Λ] [Countable Λ] [AddGroup.FG Λ] {W Z : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]

/-- **Steps 2, 3**: a quasi-compact open `U₀` of `Z` lies in a quasi-compact stable open `V`, an object of the site with
the restricted action, and `Γ(V, O)` carries the coaction of this action. -/
theorem SDR3Coact_main (actZ : AAction (fppfO B S hS) Λ (yoneda.obj Z)) (r : Z ⟶ W) (U₀ : ((SCH).obj Z).Opens)
    (hc : IsCompact (U₀ : Set ((SCH).obj Z))) :
    ∃ (Vo : BigFppfOver B S hS) (k : Vo ⟶ Z) (actV : AAction (fppfO B S hS) Λ (yoneda.obj Vo)),
      IsOpenImmersion ((SCH).map k) ∧ (U₀ : Set ((SCH).obj Z)) ⊆ Set.range ((SCH).map k) ∧
      (∀ {T : BigFppfOver B S hS} (g : APt (fppfO B S hS) Λ (op T)) (t : T ⟶ Vo),
        actV.smul (U := op T) g t ≫ k = actZ.smul (U := op T) g (t ≫ k)) ∧
      CompactSpace ((SCH).obj Vo) ∧
      ∃ c : Coact Γ((SCH).obj Vo, ⊤) Λ, ∀ y,
        SDR3Coact_lift ((SCH).map (SDR3Coact_π Λ (k ≫ r))).appTop.hom
            (SDR3Coact_chi (SDR3Coact_g (Λ := Λ) (k ≫ r))) (c.σ y) =
          ((SCH).map (SDR3Coact_a actV (k ≫ r))).appTop.hom y := by
  let V : ((SCH).obj Z).Opens :=
    ⟨(SCH).map (SDR3Coact_a actZ r) '' ((SCH).map (SDR3Coact_π Λ r) ⁻¹' U₀), SDR3Coact_isOpen_sat actZ r U₀.2⟩
  obtain ⟨Vo, k, actV, hk, hr, heq⟩ := SDR3Coact_restrict actZ r V (fun y => SDR3Coact_sat actZ r _ y)
  have hcV : IsCompact (Set.range ((SCH).map k)) := by
    rw [hr]; exact SDR3Coact_isCompact_sat actZ r U₀.2 hc
  have hcomp : CompactSpace ((SCH).obj Vo) := by
    refine ⟨?_⟩
    rw [((SCH).map k).isOpenEmbedding.isEmbedding.isCompact_iff, Set.image_univ]
    exact hcV
  refine ⟨Vo, k, actV, hk, ?_, heq, hcomp, SDR3Coact_coact actV (k ≫ r)⟩
  rw [hr]
  exact SDR3Coact_subset_sat actZ r _

end AlgMag.SD

#print axioms AlgMag.SD.SDR3Coact_main
