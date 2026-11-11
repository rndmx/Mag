/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.GeneralBaseAttractor
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Algebraic Magnetism, Proposition 3.28: the points `Hom_{𝒪_S}(E, p_* 𝒪_T)`

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026). For `p : T → S`, a `T`-point of
`V(E) = Spec_S Sym E` is an `𝒪_S`-linear map `E → p_* 𝒪_T`. This file builds, on `p_* 𝒪_T`, the
restriction maps along `T' → T` and multiplication by a global section of `T`.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace AlgMag.VB

variable {S : Scheme.{u}}

/-- The `𝒪_S`-module `p_* 𝒪_T` of a scheme `p : T → S`. -/
abbrev pO (T : Over S) : S.Modules :=
  (Scheme.Modules.pushforward T.hom).obj (SheafOfModules.unit T.left.ringCatSheaf)

/-- A section over `U` of a morphism into `p_* 𝒪_T`, as a section of `𝒪_T` over `p⁻¹ U`. -/
def sec {P : S.Modules} {T : Over S} (ξ : P ⟶ pO T) (U : S.Opens) (x : Γ(P, U)) :
    Γ(T.left, T.hom ⁻¹ᵁ U) :=
  (Scheme.Modules.Hom.app ξ U).hom x

/-- Multiplication by `r` on `Γ(T, p⁻¹ U)`. -/
def mulFun (T : Over S) (r : Γ(T.left, ⊤)) (U : S.Opens) :
    Γ(T.left, T.hom ⁻¹ᵁ U) →+ Γ(T.left, T.hom ⁻¹ᵁ U) :=
  AddMonoidHom.mulLeft ((T.left.presheaf.map (homOfLE le_top).op).hom r)

/-- Multiplication by a global section of `T` on `p_* 𝒪_T`. -/
def mulO (T : Over S) (r : Γ(T.left, ⊤)) : pO T ⟶ pO T :=
  ⟨PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom (mulFun T r U.unop)
      naturality := fun U V i => by
        ext (x : Γ(T.left, T.hom ⁻¹ᵁ U.unop))
        change (T.left.presheaf.map (homOfLE le_top).op).hom r *
            (T.left.presheaf.map ((Opens.map T.hom.base).map i.unop).op).hom x =
          (T.left.presheaf.map ((Opens.map T.hom.base).map i.unop).op).hom
            ((T.left.presheaf.map (homOfLE le_top).op).hom r * x)
        rw [map_mul, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
        rfl }
    (fun U s x => by
      change (T.left.presheaf.map (homOfLE le_top).op).hom r *
          ((T.hom.app U.unop).hom s * (show Γ(T.left, T.hom ⁻¹ᵁ U.unop) from x)) =
        (T.hom.app U.unop).hom s * ((T.left.presheaf.map (homOfLE le_top).op).hom r *
          (show Γ(T.left, T.hom ⁻¹ᵁ U.unop) from x))
      ring)⟩

lemma sec_mulO {P : S.Modules} {T : Over S} (ξ : P ⟶ pO T) (r : Γ(T.left, ⊤)) (U : S.Opens)
    (x : Γ(P, U)) :
    sec (ξ ≫ mulO T r) U x = (T.left.presheaf.map (homOfLE le_top).op).hom r * sec ξ U x := rfl

lemma preimage_le {T T' : Over S} (t : T' ⟶ T) (U : S.Opens) :
    T'.hom ⁻¹ᵁ U ≤ t.left ⁻¹ᵁ (T.hom ⁻¹ᵁ U) := by
  rw [← Over.w t]; exact le_rfl

/-- The map `Γ(T, p⁻¹ U) → Γ(T', p'⁻¹ U)`. -/
def resFun {T T' : Over S} (t : T' ⟶ T) (U : S.Opens) :
    Γ(T.left, T.hom ⁻¹ᵁ U) →+ Γ(T'.left, T'.hom ⁻¹ᵁ U) :=
  (t.left.appLE (T.hom ⁻¹ᵁ U) (T'.hom ⁻¹ᵁ U) (preimage_le t U)).hom.toAddMonoidHom

lemma app_appLE {X Y Z : Scheme.{u}} (f : X ⟶ Y) (p : Y ⟶ Z) (q : X ⟶ Z) (h : f ≫ p = q)
    {U : Z.Opens} (e : q ⁻¹ᵁ U ≤ f ⁻¹ᵁ (p ⁻¹ᵁ U)) (s : Γ(Z, U)) :
    (f.appLE (p ⁻¹ᵁ U) (q ⁻¹ᵁ U) e).hom ((p.app U).hom s) = (q.app U).hom s := by
  subst h
  have h : p.app U ≫ f.appLE (p ⁻¹ᵁ U) ((f ≫ p) ⁻¹ᵁ U) e = (f ≫ p).app U :=
    (Scheme.Hom.comp_appLE f p U ((f ≫ p) ⁻¹ᵁ U) le_rfl).symm.trans (Scheme.Hom.appLE_eq_app _)
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h) s

/-- The canonical map `p_* 𝒪_T → p'_* 𝒪_{T'}` of `t : T' → T` over `S`. -/
def resO {T T' : Over S} (t : T' ⟶ T) : pO T ⟶ pO T' :=
  ⟨PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom (resFun t U.unop)
      naturality := fun U V i => by
        ext (x : Γ(T.left, T.hom ⁻¹ᵁ U.unop))
        change (t.left.appLE (T.hom ⁻¹ᵁ V.unop) (T'.hom ⁻¹ᵁ V.unop) _).hom
            ((T.left.presheaf.map ((Opens.map T.hom.base).map i.unop).op).hom x) =
          (T'.left.presheaf.map ((Opens.map T'.hom.base).map i.unop).op).hom
            ((t.left.appLE (T.hom ⁻¹ᵁ U.unop) (T'.hom ⁻¹ᵁ U.unop) _).hom x)
        rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
          Scheme.Hom.map_appLE, Scheme.Hom.appLE_map] }
    (fun U s x => by
      change (t.left.appLE (T.hom ⁻¹ᵁ U.unop) (T'.hom ⁻¹ᵁ U.unop) _).hom
          ((T.hom.app U.unop).hom s * (show Γ(T.left, T.hom ⁻¹ᵁ U.unop) from x)) =
        (T'.hom.app U.unop).hom s * (t.left.appLE (T.hom ⁻¹ᵁ U.unop) (T'.hom ⁻¹ᵁ U.unop) _).hom
          (show Γ(T.left, T.hom ⁻¹ᵁ U.unop) from x)
      exact (map_mul _ _ _).trans (congrArg (· * _) (app_appLE t.left T.hom T'.hom (Over.w t) _ s)))⟩

lemma sec_resO {P : S.Modules} {T T' : Over S} (ξ : P ⟶ pO T) (t : T' ⟶ T) (U : S.Opens)
    (x : Γ(P, U)) :
    sec (ξ ≫ resO t) U x = (t.left.appLE (T.hom ⁻¹ᵁ U) (T'.hom ⁻¹ᵁ U) (preimage_le t U)).hom
      (sec ξ U x) := rfl

lemma pO_ext {P : S.Modules} {T : Over S} {ξ ξ' : P ⟶ pO T}
    (h : ∀ U x, sec ξ U x = sec ξ' U x) : ξ = ξ' := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  exact h U.unop x

lemma resO_id (T : Over S) : resO (𝟙 T) = 𝟙 (pO T) := by
  refine pO_ext fun U x => ?_
  have e : Scheme.Hom.appLE (𝟙 T : T ⟶ T).left (T.hom ⁻¹ᵁ U) (T.hom ⁻¹ᵁ U)
      (preimage_le (𝟙 T) U) = 𝟙 _ := by
    simp [Scheme.Hom.appLE]
    exact T.left.presheaf.map_id _
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom e) x

lemma resO_comp {T T' T'' : Over S} (s : T'' ⟶ T') (t : T' ⟶ T) :
    resO (s ≫ t) = resO t ≫ resO s := by
  refine pO_ext fun U x => ?_
  have e := Scheme.Hom.appLE_comp_appLE s.left t.left (T.hom ⁻¹ᵁ U) (T'.hom ⁻¹ᵁ U) (T''.hom ⁻¹ᵁ U)
    (preimage_le t U) (preimage_le s U)
  exact (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom e) x).symm

lemma mulO_one (T : Over S) : mulO T 1 = 𝟙 _ := by
  refine pO_ext fun U x => ?_
  let y : Γ(T.left, T.hom ⁻¹ᵁ U) := x
  change (T.left.presheaf.map (homOfLE le_top).op).hom 1 * y = y
  rw [map_one, one_mul]

lemma mulO_mul (T : Over S) (r r' : Γ(T.left, ⊤)) : mulO T (r * r') = mulO T r' ≫ mulO T r := by
  refine pO_ext fun U x => ?_
  let y : Γ(T.left, T.hom ⁻¹ᵁ U) := x
  change (T.left.presheaf.map (homOfLE le_top).op).hom (r * r') * y =
    (T.left.presheaf.map (homOfLE le_top).op).hom r *
      ((T.left.presheaf.map (homOfLE le_top).op).hom r' * y)
  rw [map_mul, mul_assoc]

lemma appLE_map_top {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Y.Opens) (B : X.Opens) (e : B ≤ f ⁻¹ᵁ A)
    (r : Γ(Y, ⊤)) :
    (f.appLE A B e).hom ((Y.presheaf.map (homOfLE le_top).op).hom r) =
      (X.presheaf.map (homOfLE le_top).op).hom (f.appTop.hom r) := by
  have h1 : Y.presheaf.map (homOfLE (le_top : A ≤ ⊤)).op ≫ f.appLE A B e =
      f.appTop ≫ X.presheaf.map (homOfLE (le_top : B ≤ ⊤)).op := by
    rw [Scheme.Hom.map_appLE]
    rfl
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h1) r

lemma mulO_resO {T T' : Over S} (t : T' ⟶ T) (r : Γ(T.left, ⊤)) :
    mulO T r ≫ resO t = resO t ≫ mulO T' (t.left.appTop.hom r) := by
  refine pO_ext fun U x => ?_
  let y : Γ(T.left, T.hom ⁻¹ᵁ U) := x
  change (t.left.appLE (T.hom ⁻¹ᵁ U) (T'.hom ⁻¹ᵁ U) (preimage_le t U)).hom
      ((T.left.presheaf.map (homOfLE le_top).op).hom r * y) =
    (T'.left.presheaf.map (homOfLE le_top).op).hom (t.left.appTop.hom r) *
      (t.left.appLE (T.hom ⁻¹ᵁ U) (T'.hom ⁻¹ᵁ U) (preimage_le t U)).hom y
  rw [map_mul, appLE_map_top]

end AlgMag.VB
