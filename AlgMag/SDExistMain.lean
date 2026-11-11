/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SDExistGlue

/-!
# Lemma D, existence for a torsion-free grading, from the local factorization

Steps 3-4 of the proof of Props. 3.31 (ii), 3.32 (ii) of `Algebraic Magnetism`.
`SDExist_LocalFactor` is the conclusion of Steps 3-4 before gluing.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgMag.SD

open AlgMag AlgMag.SQ AlgMag.GenM

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

/-- Step 3 (i)-(v) and the factorization of Step 4: an invariant point over `𝔸(P)_T` comes from an étale neighbourhood
of each point of `𝔸(P₀)_T`. -/
def SDExist_LocalFactor (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (Γ : Type u) [AddCommGroup Γ] : Prop :=
  ∀ {P P₀ : Type u} [AddCommMonoid P] [Countable P] [AddCommMonoid P₀] [Countable P₀]
    (δ : P →+ Γ) (j : P₀ →+ P), Function.Injective j → (∀ p, δ p = 0 ↔ p ∈ Set.range j) →
    ∀ (T : BigFppfOver B S hS) [IsAffine ((SCH).obj T)] (x : X.obj (op (specObj P T))), IsInvPt X δ x →
    ∀ q : (SCH).obj (specObj P₀ T), ∃ (V : BigFppfOver B S hS) (_ : IsAffine ((SCH).obj V))
      (e : V ⟶ specObj P₀ T), Etale ((SCH).map e) ∧ q ∈ Set.range ((SCH).map e) ∧
      ∃ y : X.obj (op V), X.map (pullback.snd (specAlong T j) e).op y = X.map (pullback.fst (specAlong T j) e).op x

/-- **Lemma D, existence**, for a grading by `Γ` with `UniqueSums` (in particular `Γ = ℤ^r`). -/
theorem SDExist_desc {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hU : SDExist_UniqCoact X) {Γ : Type u} [AddCommGroup Γ] [UniqueSums Γ] (hL : SDExist_LocalFactor X Γ)
    {P P₀ : Type u} [AddCommMonoid P] [Countable P] [AddCommMonoid P₀] [Countable P₀]
    (δ : P →+ Γ) (j : P₀ →+ P) (hj : Function.Injective j) (hk : ∀ p, δ p = 0 ↔ p ∈ Set.range j)
    (T : BigFppfOver B S hS) [IsAffine ((SCH).obj T)] (x : X.obj (op (specObj P T))) (hx : IsInvPt X δ x) :
    ∃ x₀, X.map (specAlong T j).op x₀ = x := by
  let R := Γ((SCH).obj T, ⊤)
  have hι := monCoact_isInv (R := R) (δ := δ) hj hk
  exact SDExist_desc_of_local hX hU hι (specAlong T j) (Iso.refl _) (Iso.refl _) (by
    change (SCH).map (specAlong T j) ≫ 𝟙 _ = 𝟙 _ ≫ sp (monι j R)
    rw [Category.comp_id, Category.id_comp]
    rfl) x (hL δ j hj hk T x hx)

end AlgMag.SD

#print axioms AlgMag.SD.SDExist_desc
