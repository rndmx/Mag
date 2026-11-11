/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec3Leftover221
import AlgMag.Sec3Leftover221Fin
import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme

/-!
# Algebraic Magnetism, Proposition 2.21: a grading gives an action

For a quasi-coherent `M`-graded `𝒪_S`-module `E`, the projections `E → E_m → E`, pulled back to `T`, form
a decomposition of `W(E)`, hence an `𝔸(M)_S`-action.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace AlgMag.P221

open AlgMag.Leftover AlgMag.S9 AlgMag.VB

open scoped Classical

variable {S : Scheme.{u}}

/-- `pullbackSectionsMap` is natural in the module. -/
lemma pullbackSectionsMap_natural {F F' : S.Modules} (θ : F ⟶ F') {X Y : Over S} (g : X ⟶ Y)
    (x : Γ((Scheme.Modules.pullback Y.hom).obj F, ⊤)) :
    pullbackSectionsMap F' g (((Scheme.Modules.pullback Y.hom).map θ).app ⊤ x) =
      ((Scheme.Modules.pullback X.hom).map θ).app ⊤ (pullbackSectionsMap F g x) := by
  let aF : (Scheme.Modules.pullback g.left).obj ((Scheme.Modules.pullback Y.hom).obj F) ⟶
      (Scheme.Modules.pullback X.hom).obj F :=
    (Scheme.Modules.pullbackComp g.left Y.hom).hom.app F ≫
      (Scheme.Modules.pullbackCongr (Over.w g)).hom.app F
  let aF' : (Scheme.Modules.pullback g.left).obj ((Scheme.Modules.pullback Y.hom).obj F') ⟶
      (Scheme.Modules.pullback X.hom).obj F' :=
    (Scheme.Modules.pullbackComp g.left Y.hom).hom.app F' ≫
      (Scheme.Modules.pullbackCongr (Over.w g)).hom.app F'
  have ha : (Scheme.Modules.pullback g.left).map ((Scheme.Modules.pullback Y.hom).map θ) ≫ aF' =
      aF ≫ (Scheme.Modules.pullback X.hom).map θ := by
    have n1 := (Scheme.Modules.pullbackComp g.left Y.hom).hom.naturality θ
    have n2 := (Scheme.Modules.pullbackCongr (Over.w g)).hom.naturality θ
    simp only [Functor.comp_map] at n1
    simp only [aF, aF', ← Category.assoc]
    rw [n1, Category.assoc, Category.assoc, n2]
  let θ1 := (Scheme.Modules.pullback Y.hom).map θ
  have hu := (Scheme.Modules.pullbackPushforwardAdjunction g.left).unit.naturality θ1
  simp only [Functor.id_map, Functor.comp_map] at hu
  have hb : θ1 ≫ (Scheme.Modules.pullbackPushforwardAdjunction g.left).unit.app _ ≫
        (Scheme.Modules.pushforward g.left).map aF' =
      ((Scheme.Modules.pullbackPushforwardAdjunction g.left).unit.app _ ≫
        (Scheme.Modules.pushforward g.left).map aF) ≫
        (Scheme.Modules.pushforward g.left).map ((Scheme.Modules.pullback X.hom).map θ) := by
    rw [← Category.assoc, hu, Category.assoc, Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
      ha]
  have hx := congrArg (fun k => (Scheme.Modules.Hom.app k ⊤) x) hb
  simp only [comp_app_apply] at hx
  have hres := PresheafOfModules.naturality_apply ((Scheme.Modules.pullback X.hom).map θ).val
    (eqToHom (show (⊤ : X.left.Opens) = g.left ⁻¹ᵁ ⊤ by simp)).op
    ((((Scheme.Modules.pullbackPushforwardAdjunction g.left).unit.app _ ≫
        (Scheme.Modules.pushforward g.left).map aF).app ⊤) x)
  exact (congrArg _ hx).trans hres.symm

/-- Pulling a section back is natural in the module. -/
lemma pullbackSectionHom_natural {F F' : S.Modules} (θ : F ⟶ F') {T : Scheme.{u}} (p : T ⟶ S)
    (U : S.Opens) (V : T.Opens) (h : V ≤ p ⁻¹ᵁ U) (x : Γ(F, U)) :
    pullbackSectionHom p F' U V h (θ.app U x) =
      ((Scheme.Modules.pullback p).map θ).app V (pullbackSectionHom p F U V h x) := by
  have hu := (Scheme.Modules.pullbackPushforwardAdjunction p).unit.naturality θ
  have hx := congrArg (fun k => (Scheme.Modules.Hom.app k U) x) hu
  simp only [Functor.id_map, Functor.comp_map, comp_app_apply] at hx
  have hres := PresheafOfModules.naturality_apply ((Scheme.Modules.pullback p).map θ).val
    (homOfLE h).op (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app F).app U x)
  exact (congrArg _ hx).trans hres.symm

variable {M : Type u} [AddCommMonoid M] (G : GrMod S M) [hq : ∀ m, (G.P m).IsQuasicoherent]

/-- The projection `E → E_m → E`. -/
def pr (m : M) : G.E ⟶ G.E := G.desc fun k => if k = m then G.ι k else 0

lemma ι_pr (m k : M) : G.ι k ≫ pr G m = if k = m then G.ι k else 0 := G.ι_desc _ k

lemma pr_idem (m : M) : pr G m ≫ pr G m = pr G m := by
  refine G.hom_ext fun k => ?_
  rw [← Category.assoc, ι_pr]
  split_ifs with h
  · rw [ι_pr, if_pos h]
  · simp

lemma pr_ortho (m k : M) (h : k ≠ m) : pr G k ≫ pr G m = 0 := by
  refine G.hom_ext fun j => ?_
  rw [← Category.assoc, ι_pr, comp_zero]
  split_ifs with hj
  · rw [ι_pr, if_neg (hj ▸ h)]
  · simp

instance isQc_E : G.E.IsQuasicoherent := G.isQuasicoherent_E

/-- The map `pr` on `W(E)(T)`. -/
def prOn (T : Over S) (θ : G.E ⟶ G.E) :
    (assocPMod G.E).obj (op T) →ₗ[(GB.overO S).obj (op T)] (assocPMod G.E).obj (op T) where
  toFun x := ((Scheme.Modules.pullback T.hom).map θ).app ⊤ x
  map_add' a b := map_add _ a b
  map_smul' r x := Scheme.Modules.Hom.app_smul _ r x

lemma pull_comp {E : S.Modules} (T : Over S) (a b : E ⟶ E)
    (x : Γ((Scheme.Modules.pullback T.hom).obj E, ⊤)) :
    ((Scheme.Modules.pullback T.hom).map (a ≫ b)).app ⊤ x =
      ((Scheme.Modules.pullback T.hom).map b).app ⊤ (((Scheme.Modules.pullback T.hom).map a).app ⊤ x) := by
  rw [Functor.map_comp, comp_app_apply]

lemma prOn_comp (T : Over S) (a b : G.E ⟶ G.E) (x) :
    prOn G T b (prOn G T a x) = prOn G T (a ≫ b) x :=
  (pull_comp T a b x).symm

lemma prOn_zero (T : Over S) (x) : prOn G T 0 x = 0 := by
  change ((Scheme.Modules.pullback T.hom).map 0).app ⊤ x = 0
  rw [Functor.map_zero, Scheme.Modules.Hom.zero_app]
  rfl

/-- The cofan of pullbacks is a coproduct. -/
def isColimitPull (T : Over S) :
    IsColimit (Cofan.mk ((Scheme.Modules.pullback T.hom).obj G.E)
      fun m => (Scheme.Modules.pullback T.hom).map (G.ι m)) :=
  isColimitCofanMkObjOfIsColimit (Scheme.Modules.pullback T.hom) G.P G.ι G.isColimit

section Alg
variable {A : Type u} [AddCommGroup A] (f : M → A →+ A)

/-- The elements on which the family has finite support and sum the identity. -/
def Cl (x : A) : Prop := (Function.support fun m => f m x).Finite ∧ ∑ᶠ m, f m x = x

lemma cl_zero : Cl f 0 := by
  simp only [Cl, map_zero]
  exact ⟨by simp [Function.support], finsum_zero⟩

lemma cl_add (a b : A) (ha : Cl f a) (hb : Cl f b) : Cl f (a + b) := by
  simp only [Cl, map_add]
  exact ⟨(ha.1.union hb.1).subset (Function.support_add _ _),
    (finsum_add_distrib ha.1 hb.1).trans (congrArg₂ (· + ·) ha.2 hb.2)⟩

lemma cl_single (k : M) (x : A) (h : ∀ m, f m x = if k = m then x else 0) : Cl f x := by
  simp only [Cl, h]
  refine ⟨(Set.finite_singleton k).subset fun m hm => ?_, ?_⟩
  · by_contra h'
    exact hm (if_neg (Ne.symm h'))
  · rw [finsum_eq_single (fun m => if k = m then x else 0) k (fun m hm => if_neg (Ne.symm hm)),
      if_pos rfl]

end Alg

lemma prOn_induction (T : Over S) [IsAffine T.left] (x : (assocPMod G.E).obj (op T)) :
    (Function.support fun m => prOn G T (pr G m) x).Finite ∧
      ∑ᶠ m, prOn G T (pr G m) x = x := by
  let f : M → Γ((Scheme.Modules.pullback T.hom).obj G.E, ⊤) →+ Γ((Scheme.Modules.pullback T.hom).obj G.E, ⊤) :=
    fun m => (((Scheme.Modules.pullback T.hom).map (pr G m)).app ⊤).hom
  refine sec_induction (fun m => (Scheme.Modules.pullback T.hom).map (G.ι m)) (isColimitPull G T)
    (C := Cl f) (cl_zero f) (cl_add f) ?_ x
  intro k y
  refine cl_single _ k _ fun m => ?_
  change ((Scheme.Modules.pullback T.hom).map (pr G m)).app ⊤ _ = _
  rw [← comp_app_apply, ← Functor.map_comp, ι_pr]
  split_ifs
  · rfl
  · rw [Functor.map_zero, Scheme.Modules.Hom.zero_app]; rfl

/-- **Proposition 2.21**, the decomposition of `W(E)` given by a grading. -/
def decompOfGr : Decomp (assocPMod G.E) M where
  comp m T := prOn G T (pr G m)
  natural m {T T'} s v := (pullbackSectionsMap_natural (pr G m) s v).symm
  finite T _ v := (prOn_induction G T v).1
  same m T v := by rw [prOn_comp, pr_idem]
  ne m k T v h := by rw [prOn_comp, pr_ortho G m k h, prOn_zero]
  sum T _ v := (prOn_induction G T v).2

/-- **Proposition 2.21**: the `𝔸(M)_S`-`𝒪_S`-module structure of a graded quasi-coherent module. -/
def actionOfGr : HModule (Hm M S) (assocPMod G.E) :=
  (hModuleEquivDecomp (isQCoh_assocPMod G.E)).symm (decompOfGr G)

end AlgMag.P221
