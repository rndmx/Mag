/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartStatement
import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# The action of `D(M)` on an affine object attached to a grading

For an object `U` of the site with `U` affine, and an `M`-grading of `Γ(U)` such that the structure
map from an affine `S` lands in degree `0`, a `T`-point `h` of `D(M)` acts on `x : T ⟶ U` by
`a ↦ x(a) h(d)`, `a` of degree `d`. This is "action = coaction by `ℤ[M]`; on affines = `M`-grading"
of the chart-lemma proof, §7, in the direction used for the chart `U` of §6.

## Main results

* `AlgMag.ChartMain.twist`: the ring map `a ↦ ∑ x(a_d) h(d)`.
* `AlgMag.ChartMain.gradedAction`: the action on `yoneda.obj U`.
* `AlgMag.ChartMain.gradedAction_appTop`: its formula on homogeneous elements.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry DirectSum

universe u

namespace AlgMag.ChartMain

section Twist

variable {M : Type*} [AddCommGroup M] [DecidableEq M] {A R R' : Type*} [CommRing A] [CommRing R]
  [CommRing R'] (𝒜 : M → AddSubgroup A) [GradedRing 𝒜]

/-- The additive map `a ↦ ∑ x(a_d) h(d)`. -/
noncomputable def twistAdd (x : A →+* R) (h : Multiplicative M →* R) : A →+ R :=
  (DirectSum.toAddMonoid fun d =>
    ((AddMonoidHom.mulRight (h (Multiplicative.ofAdd d))).comp x.toAddMonoidHom).comp
      (𝒜 d).subtype).comp (decomposeAddEquiv 𝒜).toAddMonoidHom

lemma twistAdd_of_mem (x : A →+* R) (h : Multiplicative M →* R) {d : M} {a : A} (ha : a ∈ 𝒜 d) :
    twistAdd 𝒜 x h a = x a * h (Multiplicative.ofAdd d) := by
  simp only [twistAdd, AddMonoidHom.comp_apply]
  change (DirectSum.toAddMonoid _) (decompose 𝒜 a) = _
  rw [decompose_of_mem 𝒜 ha]
  simp [DirectSum.toAddMonoid_of]

/-- Two additive maps out of a graded ring agreeing on homogeneous elements are equal. -/
lemma addHom_ext_homogeneous {N : Type*} [AddCommMonoid N] {f g : A →+ N}
    (h : ∀ d, ∀ a ∈ 𝒜 d, f a = g a) : f = g := by
  ext a
  induction a using Decomposition.inductionOn 𝒜 with
  | zero => simp
  | homogeneous a => exact h _ _ a.2
  | add a b ha hb => simp [ha, hb]

/-- The ring map `a ↦ ∑ x(a_d) h(d)`. -/
noncomputable def twist (x : A →+* R) (h : Multiplicative M →* R) : A →+* R :=
  { twistAdd 𝒜 x h with
    map_one' := by
      change twistAdd 𝒜 x h 1 = 1
      rw [twistAdd_of_mem 𝒜 x h (SetLike.GradedOne.one_mem (A := 𝒜))]
      simp
    map_mul' := fun a b => by
      change twistAdd 𝒜 x h (a * b) = twistAdd 𝒜 x h a * twistAdd 𝒜 x h b
      have key : ∀ d, ∀ a' ∈ 𝒜 d, ∀ b : A,
          twistAdd 𝒜 x h (a' * b) = twistAdd 𝒜 x h a' * twistAdd 𝒜 x h b := by
        intro d a' ha' b
        have := addHom_ext_homogeneous 𝒜
          (f := (twistAdd 𝒜 x h).comp (AddMonoidHom.mulLeft a'))
          (g := (AddMonoidHom.mulLeft (twistAdd 𝒜 x h a')).comp (twistAdd 𝒜 x h))
          (fun e c hc => by
            simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft]
            rw [twistAdd_of_mem 𝒜 x h (SetLike.GradedMul.mul_mem ha' hc),
              twistAdd_of_mem 𝒜 x h ha', twistAdd_of_mem 𝒜 x h hc, ofAdd_add, map_mul, map_mul]
            ring)
        exact DFunLike.congr_fun this b
      have := addHom_ext_homogeneous 𝒜
        (f := (AddMonoidHom.mulRight b).comp (AddMonoidHom.id A) |> (twistAdd 𝒜 x h).comp)
        (g := (AddMonoidHom.mulRight (twistAdd 𝒜 x h b)).comp (twistAdd 𝒜 x h))
        (fun d a' ha' => by
          simpa using key d a' ha' b)
      simpa using DFunLike.congr_fun this a }

lemma twist_of_mem (x : A →+* R) (h : Multiplicative M →* R) {d : M} {a : A} (ha : a ∈ 𝒜 d) :
    twist 𝒜 x h a = x a * h (Multiplicative.ofAdd d) :=
  twistAdd_of_mem 𝒜 x h ha

/-- Two ring maps out of a graded ring agreeing on homogeneous elements are equal. -/
lemma ringHom_ext_homogeneous {f g : A →+* R} (h : ∀ d, ∀ a ∈ 𝒜 d, f a = g a) : f = g := by
  have := addHom_ext_homogeneous 𝒜 (f := f.toAddMonoidHom) (g := g.toAddMonoidHom) h
  ext a
  exact DFunLike.congr_fun this a

lemma twist_one (x : A →+* R) : twist 𝒜 x 1 = x :=
  ringHom_ext_homogeneous 𝒜 fun d a ha => by simp [twist_of_mem 𝒜 x 1 ha]

lemma twist_mul (x : A →+* R) (g h : Multiplicative M →* R) :
    twist 𝒜 x (g * h) = twist 𝒜 (twist 𝒜 x h) g :=
  ringHom_ext_homogeneous 𝒜 fun d a ha => by
    rw [twist_of_mem 𝒜 _ _ ha, twist_of_mem 𝒜 _ _ ha, twist_of_mem 𝒜 _ _ ha]
    simp only [MonoidHom.mul_apply]
    ring

lemma comp_twist (φ : R →+* R') (x : A →+* R) (h : Multiplicative M →* R) :
    φ.comp (twist 𝒜 x h) = twist 𝒜 (φ.comp x) (φ.toMonoidHom.comp h) :=
  ringHom_ext_homogeneous 𝒜 fun d a ha => by
    simp [twist_of_mem 𝒜 _ _ ha]

end Twist

section Action

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [DecidableEq M]

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- The morphism to an affine scheme with a given map on global sections. -/
noncomputable def toAffine {T U : Scheme.{u}} [IsAffine U] (φ : Γ(U, ⊤) →+* Γ(T, ⊤)) : T ⟶ U :=
  T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫ U.isoSpec.inv

@[simp] lemma toAffine_appTop {T U : Scheme.{u}} [IsAffine U] (φ : Γ(U, ⊤) →+* Γ(T, ⊤)) :
    (toAffine φ).appTop.hom = φ := by
  have hT : T.toSpecΓ.appTop = (Scheme.ΓSpecIso Γ(T, ⊤)).hom := Scheme.toSpecΓ_appTop T
  have hS' : (Spec.map (CommRingCat.ofHom φ)).appTop =
      (Scheme.ΓSpecIso Γ(U, ⊤)).hom ≫ CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso Γ(T, ⊤)).inv := by
    rw [← cancel_mono (Scheme.ΓSpecIso Γ(T, ⊤)).hom, Category.assoc, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
    exact Scheme.ΓSpecIso_naturality _
  have hU : U.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(U, ⊤)).inv := by
    have h1 : U.isoSpec.hom.appTop = (Scheme.ΓSpecIso Γ(U, ⊤)).hom := Scheme.toSpecΓ_appTop U
    have h2 : U.isoSpec.hom.appTop ≫ U.isoSpec.inv.appTop = 𝟙 _ := by
      rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id]
      simp
    rw [h1] at h2
    rw [← cancel_epi (Scheme.ΓSpecIso Γ(U, ⊤)).hom, h2, Iso.hom_inv_id]
  have : (toAffine φ).appTop = CommRingCat.ofHom φ := by
    simp only [toAffine, Scheme.Hom.comp_appTop, hT, hS', hU]
    simp
  rw [this]
  rfl

lemma toAffine_ext {T U : Scheme.{u}} [IsAffine U] {f g : T ⟶ U}
    (h : f.appTop.hom = g.appTop.hom) : f = g :=
  ext_of_isAffine (CommRingCat.hom_ext h)

lemma siteExt {V W : BigFppfOver B S hS} {g g' : V ⟶ W} (h : (SCH).map g = (SCH).map g') : g = g' :=
  Over.OverMorphism.ext (ObjectProperty.hom_ext _ h)

lemma toAffine_comp {T U S' : Scheme.{u}} [IsAffine U] [IsAffine S'] (f : U ⟶ S') (q : T ⟶ S')
    (φ : Γ(U, ⊤) →+* Γ(T, ⊤)) (h : φ.comp f.appTop.hom = q.appTop.hom) : toAffine φ ≫ f = q := by
  refine toAffine_ext ?_
  rw [Scheme.Hom.comp_appTop]
  simpa using h

/-- The value of the action: `t ↦ h • t`. -/
noncomputable def gradedSmul [IsAffine S] (U : BigFppfOver B S hS) [IsAffine ((SCH).obj U)]
    (𝒜 : M → AddSubgroup Γ((SCH).obj U, ⊤)) [GradedRing 𝒜]
    (f : (SCH).obj U ⟶ S) (hf : f = U.hom.hom) (h0 : ∀ s : Γ(S, ⊤), f.appTop.hom s ∈ 𝒜 0)
    {T : BigFppfOver B S hS} (g : Multiplicative M →* Γ((SCH).obj T, ⊤)) (t : T ⟶ U) : T ⟶ U :=
  Over.homMk ⟨toAffine (T := (SCH).obj T) (U := (SCH).obj U)
    (twist 𝒜 ((SCH).map t).appTop.hom g)⟩ (by
      apply InducedCategory.hom_ext
      have ht : ((SCH).map t) ≫ f = T.hom.hom := by
        rw [hf]; exact congrArg (fun z => z.hom) (Over.w t)
      change toAffine (T := (SCH).obj T) (U := (SCH).obj U) (twist 𝒜 ((SCH).map t).appTop.hom g) ≫
        U.hom.hom = T.hom.hom
      rw [← hf]
      refine toAffine_comp f _ _ (RingHom.ext fun s => ?_)
      rw [← ht, Scheme.Hom.comp_appTop]
      simp only [RingHom.comp_apply, CommRingCat.hom_comp]
      rw [twist_of_mem 𝒜 _ _ (h0 s)]
      simp)

lemma map_gradedSmul [IsAffine S] (U : BigFppfOver B S hS) [IsAffine ((SCH).obj U)]
    (𝒜 : M → AddSubgroup Γ((SCH).obj U, ⊤)) [GradedRing 𝒜]
    (f : (SCH).obj U ⟶ S) (hf : f = U.hom.hom) (h0 : ∀ s : Γ(S, ⊤), f.appTop.hom s ∈ 𝒜 0)
    {T : BigFppfOver B S hS} (g : Multiplicative M →* Γ((SCH).obj T, ⊤)) (t : T ⟶ U) :
    ((SCH).map (gradedSmul U 𝒜 f hf h0 g t)).appTop.hom = twist 𝒜 ((SCH).map t).appTop.hom g :=
  toAffine_appTop _

lemma gradedSmul_ext [IsAffine S] (U : BigFppfOver B S hS) [IsAffine ((SCH).obj U)]
    {T : BigFppfOver B S hS} {t t' : T ⟶ U}
    (h : ((SCH).map t).appTop.hom = ((SCH).map t').appTop.hom) : t = t' :=
  siteExt (toAffine_ext h)

/-- A grading of `Γ(U)`, with the structure map from `S` in degree `0`, defines an action of `D(M)`
on `U`. -/
noncomputable def gradedAction [IsAffine S] (U : BigFppfOver B S hS) [IsAffine ((SCH).obj U)]
    (𝒜 : M → AddSubgroup Γ((SCH).obj U, ⊤)) [GradedRing 𝒜]
    (f : (SCH).obj U ⟶ S) (hf : f = U.hom.hom)
    (h0 : ∀ s : Γ(S, ⊤), f.appTop.hom s ∈ 𝒜 0) :
    AAction (fppfO B S hS) M (yoneda.obj U) where
  smul {T} g t := gradedSmul U 𝒜 f hf h0 (T := T.unop) g t
  one_smul {T} t := gradedSmul_ext U ((map_gradedSmul U 𝒜 f hf h0 (T := T.unop) 1 t).trans
    (twist_one 𝒜 _))
  mul_smul {T} g h t := gradedSmul_ext U ((map_gradedSmul U 𝒜 f hf h0 (T := T.unop) (g * h) t).trans
    ((twist_mul 𝒜 _ (R := Γ((SCH).obj T.unop, ⊤)) g h).trans (by
      have h1 := map_gradedSmul U 𝒜 f hf h0 (T := T.unop) h t
      have h2 := map_gradedSmul U 𝒜 f hf h0 (T := T.unop) g (gradedSmul U 𝒜 f hf h0 (T := T.unop) h t)
      exact (h1 ▸ h2).symm)))
  map_smul {T V} e g t := gradedSmul_ext U (by
    have h1 := map_gradedSmul U 𝒜 f hf h0 (T := V.unop)
      (APt.res (𝒪 := fppfO B S hS) e g) (e.unop ≫ t)
    have h2 := map_gradedSmul U 𝒜 f hf h0 (T := T.unop) g t
    have h3 := comp_twist 𝒜 ((SCH).map e.unop).appTop.hom ((SCH).map t).appTop.hom g
    have h4 : ((SCH).map (e.unop ≫ gradedSmul U 𝒜 f hf h0 (T := T.unop) g t)).appTop.hom =
        ((SCH).map e.unop).appTop.hom.comp
          ((SCH).map (gradedSmul U 𝒜 f hf h0 (T := T.unop) g t)).appTop.hom := by
      rw [Functor.map_comp, Scheme.Hom.comp_appTop]; rfl
    have h5 : ((SCH).map (e.unop ≫ t)).appTop.hom =
        ((SCH).map e.unop).appTop.hom.comp ((SCH).map t).appTop.hom := by
      rw [Functor.map_comp, Scheme.Hom.comp_appTop]; rfl
    refine h4.trans ?_
    rw [h2, h3, ← h5]
    exact h1.symm)

/-- The formula for the action on homogeneous elements. -/
lemma gradedAction_appTop [IsAffine S] (U : BigFppfOver B S hS) [IsAffine ((SCH).obj U)]
    (𝒜 : M → AddSubgroup Γ((SCH).obj U, ⊤)) [GradedRing 𝒜]
    (f : (SCH).obj U ⟶ S) (hf : f = U.hom.hom) (h0 : ∀ s : Γ(S, ⊤), f.appTop.hom s ∈ 𝒜 0)
    {T : BigFppfOver B S hS} (g : Multiplicative M →* Γ((SCH).obj T, ⊤)) (t : T ⟶ U)
    {d : M} {a : Γ((SCH).obj U, ⊤)} (ha : a ∈ 𝒜 d) :
    ((SCH).map (gradedSmul U 𝒜 f hf h0 g t)).appTop.hom a =
      ((SCH).map t).appTop.hom a * g (Multiplicative.ofAdd d) := by
  rw [map_gradedSmul, twist_of_mem 𝒜 _ _ ha]

end Action

end AlgMag.ChartMain
