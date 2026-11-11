/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec11SpacesFace
import AlgMag.Sec11SchemesLimit
import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.AffineCriterion
import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.LimitPreservingOfFinitePresentation
import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.SurjectiveCriterion

/-!
# Fact 3.19 for algebraic spaces

Mayeux, *Algebraic Magnetism*, Fact 3.19: if `f : X → Y` is equivariant and locally of finite
presentation, and `X^N`, `Y^N` are representable by algebraic spaces, then `f^N` is locally of finite
presentation. This uses Stacks 049J (limit preservation) for `f` on `𝔸(N)_T` and on `𝔸(N)_T × D(M)`,
and Stacks 0CM6 for `f^N`. `#M` is below the cutoff of the site.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.SpacesLift

open AlgMag.GB AlgMag.Lifts AlgMag.SmoothSchemes

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Square

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
  {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ BigFppfOver B S hS} {c : Cone D}

/-- The two halves of Tag 049J on a cofiltered limit of affine objects. -/
lemma limit_square (hf : RelativelyLimitPreserving.{u, u, u, u} B S hS f)
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
    (hA : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj i)))
    (hp : IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt)) :
    (∀ (x : X.obj (op c.pt)) (i : I) (y : Y.obj (op (D.obj i))),
      f.app _ x = Y.map (c.π.app i).op y → ∃ (j : I) (u : j ⟶ i) (xj : X.obj (op (D.obj j))),
        X.map (c.π.app j).op xj = x ∧ f.app _ xj = Y.map (D.map u).op y) ∧
    (∀ (i : I) (a b : X.obj (op (D.obj i))), f.app _ a = f.app _ b →
      X.map (c.π.app i).op a = X.map (c.π.app i).op b →
      ∃ (j : I) (u : j ⟶ i), X.map (D.map u).op a = X.map (D.map u).op b) := by
  have H := (relativelyLimitPreserving_iff_affineLimit_isPullback.{u, u, u, u} B S hS f).mp hf
    I D c hc hA hp
  obtain ⟨-, hinj, hsur⟩ := (Types.isPullback_iff _ _ _ _).1 H
  let U := CategoryTheory.uliftFunctor.{u, u}
  let F' := X ⋙ U
  let G' := Y ⋙ U
  have desc_ι : ∀ {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (j : Iᵒᵖ) (v : (D.op ⋙ Q).obj j),
      colimit.desc (D.op ⋙ Q) (Q.mapCocone c.op) (colimit.ι (D.op ⋙ Q) j v) =
        Q.map (c.π.app j.unop).op v := fun {Q} j v => by
    exact ConcreteCategory.congr_hom (colimit.ι_desc (Q.mapCocone c.op) j) v
  have map_ι : ∀ (j : Iᵒᵖ) (v : (D.op ⋙ F').obj j),
      colimMap (Functor.whiskerLeft D.op (Functor.whiskerRight f U)) (colimit.ι (D.op ⋙ F') j v) =
        colimit.ι (D.op ⋙ G') j ((Functor.whiskerRight f U).app _ v) := fun j v => by
    exact ConcreteCategory.congr_hom (ι_colimMap (Functor.whiskerLeft D.op (Functor.whiskerRight f U)) j) v
  constructor
  · intro x i y h
    obtain ⟨z, hz₁, hz₂⟩ := hsur ⟨x⟩ (colimit.ι (D.op ⋙ G') (op i) ⟨y⟩)
      ((congrArg ULift.up h).trans (desc_ι (Q := G') (op i) ⟨y⟩).symm)
    obtain ⟨j, v, hv⟩ := Types.jointly_surjective_of_isColimit (colimit.isColimit (D.op ⋙ F')) z
    subst hv
    have hz₂' := (map_ι j v).symm.trans hz₂
    obtain ⟨k, g₁, g₂, hk⟩ := (Types.FilteredColimit.colimit_eq_iff _).1 hz₂'
    refine ⟨k.unop, g₂.unop, X.map (D.map g₁.unop).op v.down, ?_, ?_⟩
    · have e := (desc_ι (Q := F') j v).symm.trans hz₁
      rw [← FunctorToTypes.map_comp_apply, ← op_comp, c.w]
      exact congrArg ULift.down e
    · rw [NatTrans.naturality_apply]
      exact congrArg ULift.down hk
  · intro i a b hf₁ hp₁
    have := hinj (colimit.ι (D.op ⋙ F') (op i) ⟨a⟩) (colimit.ι (D.op ⋙ F') (op i) ⟨b⟩)
      ⟨(desc_ι (Q := F') (op i) ⟨a⟩).trans ((congrArg ULift.up hp₁).trans
          (desc_ι (Q := F') (op i) ⟨b⟩).symm),
        (map_ι (op i) ⟨a⟩).trans ((congrArg (colimit.ι (D.op ⋙ G') (op i))
          (congrArg ULift.up hf₁)).trans (map_ι (op i) ⟨b⟩).symm)⟩
    obtain ⟨k, g₁, g₂, hk⟩ := (Types.FilteredColimit.colimit_eq_iff _).1 this
    obtain ⟨l, h, e⟩ := IsFilteredOrEmpty.cocone_maps g₁ g₂
    refine ⟨l.unop, (g₁ ≫ h).unop, ?_⟩
    have hk' : X.map (D.map g₁.unop).op a = X.map (D.map g₂.unop).op b := congrArg ULift.down hk
    have s₁ : ∀ (g : op i ⟶ k) (w : X.obj (op (D.obj i))),
        X.map (D.map (g ≫ h).unop).op w = X.map (D.map h.unop).op (X.map (D.map g.unop).op w) := by
      intro g w
      change X.map (D.map (h.unop ≫ g.unop)).op w = _
      rw [D.map_comp, op_comp, FunctorToTypes.map_comp_apply]
    rw [s₁ g₁ a, hk', ← s₁ g₂ b, e]

end Square

end AlgMag.SpacesLift
