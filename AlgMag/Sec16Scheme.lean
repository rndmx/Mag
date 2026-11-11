/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec16Lie
import AlgMag.AlgebraicSpace
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Algebra.DualNumber
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

/-!
# §16.1, §16.2 over a scheme

The category `Sch/S` of the paper is `Over S`. `I_S = Spec(ℤ[ε]) ×_ℤ S`; `I_T = T ×_S I_S` is the
product in `Over S`.
-/

open CategoryTheory Opposite Limits AlgebraicGeometry

universe u

namespace AlgMag

variable (S : Scheme.{u})

/-- The ring functor `T ↦ Γ(T, 𝒪_T)` on `Sch/S`. -/
noncomputable def overO : (Over S)ᵒᵖ ⥤ CommRingCat.{u} := (Over.forget S).op ⋙ Scheme.Γ

noncomputable instance : HasBinaryProducts (Over S) :=
  Over.ConstructProducts.over_binaryProduct_of_pullback

/-- `ℤ[ε]`. -/
abbrev dualRing : CommRingCat.{u} := CommRingCat.of (DualNumber (ULift.{u} ℤ))

/-- `ℤ → ℤ[ε]`. -/
noncomputable def dualUnit : CommRingCat.of (ULift.{u} ℤ) ⟶ dualRing.{u} :=
  CommRingCat.ofHom (algebraMap _ _)

/-- `ε ↦ 0`. -/
noncomputable def dualZero : dualRing.{u} ⟶ CommRingCat.of (ULift.{u} ℤ) :=
  CommRingCat.ofHom (TrivSqZeroExt.fstHom (ULift.{u} ℤ) (ULift.{u} ℤ) (ULift.{u} ℤ)).toRingHom

/-- **§16.1.** `I_S = Spec(ℤ[ε]) ×_ℤ S`, as an `S`-scheme. -/
noncomputable def dualS : Over S :=
  Over.mk (pullback.fst (specULiftZIsTerminal.from S) (Spec.map dualUnit.{u}))

/-- The zero section of `I_S`. -/
noncomputable def dualPointS : DualPoint (dualS S) where
  o T := Over.homMk
    (pullback.lift T.hom (T.hom ≫ specULiftZIsTerminal.from S ≫ Spec.map dualZero.{u})
      (specULiftZIsTerminal.hom_ext _ _)) (pullback.lift_fst _ _ _)
  comp_o {T T'} s := by
    ext : 1
    refine pullback.hom_ext ?_ ?_
    · change s.left ≫ pullback.lift _ _ _ ≫ pullback.fst _ _ = pullback.lift _ _ _ ≫ pullback.fst _ _
      rw [pullback.lift_fst, pullback.lift_fst]
      exact Over.w s
    · change s.left ≫ pullback.lift _ _ _ ≫ pullback.snd _ _ = pullback.lift _ _ _ ≫ pullback.snd _ _
      rw [pullback.lift_snd, pullback.lift_snd, ← Category.assoc, Over.w s]

variable {S} {M : Type*} [AddCommMonoid M]

/-- **Proposition 16.2** on `Sch/S`, for a functor `X` over a general scheme `S`. -/
noncomputable example {X : (Over S)ᵒᵖ ⥤ Type u} (act : AAction (overO S) M X) (N : AddSubmonoid M) :
    attractor (tangentAction (dualS S) act) N ≅ tangent (dualS S) (attractor act N) :=
  tangentAttractorIso _ act N

/-- **Proposition 16.4** on `Sch/S`. -/
noncomputable example {G : GrpFunctor.{u} (Over S)} (act : AAction (overO S) M G.F)
    (ha : ActsByMonoidEnd act) (N : AddSubmonoid M) :
    GrpIso (attrGrp (Lie (dualPointS S) G) (lieAction (dualPointS S) act ha)
        (actsByMonoidEnd_lie (dualPointS S) act ha) N)
      (Lie (dualPointS S) (attrGrp G act ha N)) :=
  lieAttractorIso _ act ha N

/-- The big fppf site has binary products: all of §16.1, §16.2, §16.3, §16.6 apply to algebraic
spaces over `S`, for `I_S` as soon as it is an object of the site. -/
theorem hasBinaryProducts_fppf (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasBinaryProducts (BigFppfOver B S hS) :=
  Over.ConstructProducts.over_binaryProduct_of_pullback

end AlgMag
