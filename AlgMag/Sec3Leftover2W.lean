/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec3LeftoverW
import AlgMag.SecLeftoverQCoh

/-!
# Algebraic Magnetism, Definition 2.20 and the action used in Proposition 2.21

`AlgMag.W.aModuleEquiv`: an `𝔸(M)_S`-`𝒪_S`-module structure in the form of Definition 2.20
(`AlgMag.W.AModule`, `W(F)` being the presheaf of Stacks 03DS) is the same as an `HModule` on
`AlgMag.Leftover.assocPMod F`, the action in `AlgMag.P221.QAMod` and `AlgMag.P221.prop221`.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry Magnetism

noncomputable section

namespace AlgMag.W

open AlgMag.GB AlgMag.S9

variable {S : Scheme.{u}} (F : S.Modules) [F.IsQuasicoherent] (M : Type u) [AddCommMonoid M]

lemma WF_map {U V : (Over S)ᵒᵖ} (f : U ⟶ V) (x : (WF F).obj U) :
    (WF F).map f x = (AlgMag.Leftover.assocPMod F).map f x := rfl

/-- **Definition 2.20**: both forms of an `𝔸(M)_S`-`𝒪_S`-module structure on `F` agree. -/
def aModuleEquiv : AModule F M ≃ HModule (Hm M S) (AlgMag.Leftover.assocPMod F) where
  toFun A :=
    { smul := fun {U} g x => A.smul (U := U) g x
      one_smul := fun {U} x => A.one_smul (U := U) x
      mul_smul := fun {U} g h x => A.mul_smul (U := U) g h x
      smul_add := fun {U} g x y => A.smul_add (U := U) g x y
      smul_smul := fun {U} g a x => A.smul_smul_scalar (U := U) g a x
      map_smul := fun {U V} f g x => A.map_smul f g x }
  invFun A :=
    { smul := fun {U} g x => A.smul (U := U) g x
      one_smul := fun {U} x => A.one_smul (U := U) x
      mul_smul := fun {U} g h x => A.mul_smul (U := U) g h x
      smul_add := fun {U} g x y => A.smul_add (U := U) g x y
      smul_smul_scalar := fun {U} g a x => A.smul_smul (U := U) g a x
      map_smul := fun {U V} f g x => (WF_map F f _).trans ((A.map_smul f g x).trans
        (congrArg (A.smul (U := V) _) (WF_map F f x).symm)) }
  left_inv _ := rfl
  right_inv _ := rfl

end AlgMag.W

#print axioms AlgMag.W.aModuleEquiv
