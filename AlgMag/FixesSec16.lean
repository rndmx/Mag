/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec3Leftover2D

/-!
# Algebraic Magnetism, §16.4 (ii): the chain of equalities as isomorphisms of functors

`X^{N₁ × N₂} = (X^{N₁ × M₂})^{M₁ × N₂} = (X^{N₁})^{N₂}`, as natural isomorphisms compatible with the
maps to `X`.

The printed proof uses Propositions 3.31 and 3.32. Here the isomorphisms are those of
`AlgMag.S16R.stagesEquiv` and `AlgMag.S16R.stageTopEquiv`, explicit formulas needing no hypothesis on `X`.
-/

universe u

open CategoryTheory Opposite

noncomputable section

namespace AlgMag.S16R

variable {C : Type*} [Category.{u} C] {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}}

section Big

variable {P : Type*} [AddCommMonoid P] {W : Cᵒᵖ ⥤ Type*} (a : AAction 𝒪 P W) (N : AddSubmonoid P)

/-- The attractor functor of a functor in an arbitrary universe. -/
def bigAttractor : Cᵒᵖ ⥤ Type _ where
  obj T := BigPt a N (unop T)
  map f := ↾ BigPt.baseChange f.unop
  map_id T := by
    refine ConcreteCategory.hom_ext _ _ fun φ => ?_
    refine BigPt.ext ?_
    funext T' t b
    change φ.app (t ≫ 𝟙 _) b = φ.app t b
    rw [Category.comp_id]
  map_comp f g := by
    refine ConcreteCategory.hom_ext _ _ fun φ => ?_
    refine BigPt.ext ?_
    funext T' t b
    change φ.app (t ≫ g.unop ≫ f.unop) b = φ.app ((t ≫ g.unop) ≫ f.unop) b
    rw [Category.assoc]

variable {a N} in
/-- The map `X^N → X` for a functor in an arbitrary universe. -/
def BigPt.toPoint {T : C} (φ : BigPt a N T) : W.obj (op T) := φ.app (𝟙 T) 1

end Big

variable {M₁ M₂ : Type u} [AddCommMonoid M₁] [AddCommMonoid M₂] {F : Cᵒᵖ ⥤ Type u}
  (act : AAction 𝒪 (M₁ × M₂) F) (N₁ : AddSubmonoid M₁) (N₂ : AddSubmonoid M₂)

/-- **§16.4 (ii)**, second equality:
`(X^{N₁ × M₂}_{M₁ × M₂})^{M₁ × N₂}_{M₁ × M₂} = (X^{N₁ × 0}_{M₁ × 0})^{0 × N₂}_{0 × M₂}`. -/
def stageTopIso :
    bigAttractor (attractorAction act (N₁.prod (⊤ : AddSubmonoid M₂)))
        ((⊤ : AddSubmonoid M₁).prod N₂) ≅ bigAttractor (actSnd act N₁) N₂ :=
  NatIso.ofComponents (fun U => (stageTopEquiv act N₁ N₂ (unop U)).toIso) (fun {U V} s => by
    refine ConcreteCategory.hom_ext _ _ fun ψ => ?_
    exact stageTopEquiv_baseChange act N₁ N₂ s.unop ψ)

/-- `X^{N₁ × N₂} = (X^{N₁ × 0}_{M₁ × 0})^{0 × N₂}_{0 × M₂}`. -/
def stagesBigIso : attractor act (N₁.prod N₂) ≅ bigAttractor (actSnd act N₁) N₂ :=
  NatIso.ofComponents (fun U => (stagesEquiv act N₁ N₂ (unop U)).toIso) (fun {U V} s => by
    refine ConcreteCategory.hom_ext _ _ fun φ => ?_
    exact stagesEquiv_baseChange act N₁ N₂ s.unop φ)

/-- **§16.4 (ii)**, first equality: `X^{N₁ × N₂} = (X^{N₁ × M₂}_{M₁ × M₂})^{M₁ × N₂}_{M₁ × M₂}`. -/
def stagesChainIso :
    attractor act (N₁.prod N₂) ≅
      bigAttractor (attractorAction act (N₁.prod (⊤ : AddSubmonoid M₂)))
        ((⊤ : AddSubmonoid M₁).prod N₂) :=
  stagesBigIso act N₁ N₂ ≪≫ (stageTopIso act N₁ N₂).symm

/-- The component of `stagesChainIso` is `stagesChain`. -/
lemma stagesChainIso_hom_apply (T : C) (φ : AttractorPt act (N₁.prod N₂) T) :
    (stagesChainIso act N₁ N₂).hom.app (op T) φ = stagesChain act N₁ N₂ T φ := rfl

/-- `stagesEquiv` commutes with the maps to `X`. -/
lemma stagesEquiv_toPoint {T : C} (φ : AttractorPt act (N₁.prod N₂) T) :
    AttractorPt.toPoint (BigPt.toPoint (stagesEquiv act N₁ N₂ T φ)) = φ.toPoint := by
  change φ.app (𝟙 T ≫ 𝟙 T) (glue N₁ N₂ 1 (APt.res (𝟙 T).op 1)) = φ.app (𝟙 T) 1
  rw [Category.id_comp]
  congr 1
  refine MonoidHom.ext fun n => ?_
  simp [glue]

/-- `stageTopEquiv` commutes with the maps to `X`. -/
lemma stageTopEquiv_toPoint {T : C}
    (ψ : BigPt (attractorAction act (N₁.prod (⊤ : AddSubmonoid M₂)))
      ((⊤ : AddSubmonoid M₁).prod N₂) T) :
    AttractorPt.toPoint (BigPt.toPoint (stageTopEquiv act N₁ N₂ T ψ)) =
      AttractorPt.toPoint (BigPt.toPoint ψ) := by
  change (ψ.app (𝟙 T) (glue ⊤ N₂ 1 1)).app (𝟙 T) (glue N₁ ⊤ 1 1) = (ψ.app (𝟙 T) 1).app (𝟙 T) 1
  have h1 : glue (⊤ : AddSubmonoid M₁) N₂ (1 : APt 𝒪 _ (op T)) 1 = 1 :=
    MonoidHom.ext fun n => by simp [glue]
  have h2 : glue N₁ (⊤ : AddSubmonoid M₂) (1 : APt 𝒪 _ (op T)) 1 = 1 :=
    MonoidHom.ext fun n => by simp [glue]
  rw [h1, h2]

/-- **§16.4 (ii)**: the chain commutes with the maps to `X`. -/
theorem stagesChain_toPoint {T : C} (φ : AttractorPt act (N₁.prod N₂) T) :
    AttractorPt.toPoint (BigPt.toPoint (stagesChain act N₁ N₂ T φ)) = φ.toPoint := by
  rw [← stageTopEquiv_toPoint]
  change AttractorPt.toPoint (BigPt.toPoint (stageTopEquiv act N₁ N₂ T
    ((stageTopEquiv act N₁ N₂ T).symm (stagesEquiv act N₁ N₂ T φ)))) = _
  rw [Equiv.apply_symm_apply, stagesEquiv_toPoint]

end AlgMag.S16R

#print axioms AlgMag.S16R.stageTopIso
#print axioms AlgMag.S16R.stagesBigIso
#print axioms AlgMag.S16R.stagesChainIso
#print axioms AlgMag.S16R.stagesChain_toPoint
