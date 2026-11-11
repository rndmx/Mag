/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartConclude
import AlgMag.Sec8Limits

/-!
# Chart lemma, Artin approximation step: gradings and spreading on the site

Part of the proof of the equivariant étale chart lemma for `D(M)`-actions at a closed point (local
structure in the sense of Alper–Hall–Rydh), used for **Theorem 6.8** of Algebraic Magnetism.

* `homog_gradedAction`: the grading of `gradedAction 𝒜` is `𝒜`.
* `equivariant_of_universal`: equivariance is checked at the universal point over `Γ(U)[M]`.
* `exists_equivariant_rep`: an equivariant point over a cofiltered limit of affine objects with
  action comes from an equivariant point at a finite level (the map `φ̃`, with equivariance as an
  equality on `Spec(Q_R[M])`).
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.ChartS5

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [AddMonoid.FG M]

local notation "SCH" => BigFppfOver.toScheme B S hS

section Homog

variable [DecidableEq M] [IsAffine S] (U : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  (𝒜 : M → AddSubgroup Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) [GradedRing 𝒜]
  (fS : (BigFppfOver.toScheme B S hS).obj U ⟶ S) (hf : fS = U.hom.hom) (h0 : ∀ s : Γ(S, ⊤), fS.appTop.hom s ∈ 𝒜 0)

lemma mem_homog_of_mem {d : M} {a : Γ((SCH).obj U, ⊤)} (ha : a ∈ 𝒜 d) :
    a ∈ ChartMain.homog (ChartMain.gradedAction U 𝒜 fS hf h0) d := by
  change ChartMain.coact _ _ = _
  apply (spSec_bijective U (ChartMain.ι1 U (M := M)) ChartMain.contains1).1
  rw [ChartMain.spSec_coact]
  refine (ChartMain.gradedAction_appTop U 𝒜 fS hf h0 _ _ ha).trans ?_
  change ((SCH).map (spToT U (ChartMain.ι1 U (M := M)) ChartMain.contains1)).appTop.hom a *
    spSec U _ _ _ = _
  rw [spToT_appTop, ← map_mul]
  congr 1
  change AddMonoidAlgebra.single 0 _ * AddMonoidAlgebra.single d 1 = _
  rw [AddMonoidAlgebra.single_mul_single, zero_add, mul_one]

/-- The grading attached to `gradedAction 𝒜` is `𝒜`. -/
theorem homog_gradedAction (d : M) :
    ChartMain.homog (ChartMain.gradedAction U 𝒜 fS hf h0) d = 𝒜 d := by
  classical
  apply le_antisymm
  · intro a ha
    have hsum : ∑ e ∈ (DirectSum.decompose 𝒜 a).support, ((DirectSum.decompose 𝒜 a e : 𝒜 e) :
        Γ((SCH).obj U, ⊤)) = a := DirectSum.sum_support_decompose 𝒜 a
    have hc : ChartMain.coact (ChartMain.gradedAction U 𝒜 fS hf h0) a =
        AddMonoidAlgebra.single d a := ha
    have hc2 : ChartMain.coact (ChartMain.gradedAction U 𝒜 fS hf h0) a =
        ∑ e ∈ (DirectSum.decompose 𝒜 a).support,
          AddMonoidAlgebra.single e ((DirectSum.decompose 𝒜 a e : 𝒜 e) : Γ((SCH).obj U, ⊤)) := by
      conv_lhs => rw [← hsum]
      rw [map_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      exact mem_homog_of_mem U 𝒜 fS hf h0 (SetLike.coe_mem _)
    have key : ∀ e, e ≠ d → ((DirectSum.decompose 𝒜 a e : 𝒜 e) : Γ((SCH).obj U, ⊤)) = 0 := by
      intro e he
      have h1 := congrArg (fun z : AddMonoidAlgebra _ M => z.coeff e) (hc.symm.trans hc2)
      simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply] at h1
      simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg (Ne.symm he)] at h1
      rw [Finset.sum_ite_eq'] at h1
      split_ifs at h1 with hm
      · exact h1.symm
      · simpa using hm
    have : a = ((DirectSum.decompose 𝒜 a d : 𝒜 d) : Γ((SCH).obj U, ⊤)) := by
      conv_lhs => rw [← hsum]
      by_cases hd : d ∈ (DirectSum.decompose 𝒜 a).support
      · exact Finset.sum_eq_single_of_mem d hd fun e _ he => key e he
      · rw [Finset.sum_eq_zero fun e he => key e fun h => hd (h ▸ he)]
        have h0 : DirectSum.decompose 𝒜 a d = 0 := by simpa using hd
        rw [h0]; rfl
    rw [this]
    exact SetLike.coe_mem _
  · exact fun a ha => mem_homog_of_mem U 𝒜 fS hf h0 ha

end Homog

section Universal

lemma natA {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (x : F ⟶ G) {a b} (f : a ⟶ b) (y : F.obj a) :
    G.map f (x.app a y) = x.app b (F.map f y) :=
  (ConcreteCategory.congr_hom (x.naturality f) y).symm

variable {U : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  (actU : AAction (fppfO B S hS) M (yoneda.obj U))
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (actX : AAction (fppfO B S hS) M X)

/-- The universal value of `x ∘ (action)`. -/
noncomputable def kA (x : yoneda.obj U ⟶ X) :
    X.obj (op (spObj U (ChartMain.ι1 U (M := M)) ChartMain.contains1)) :=
  x.app _ (ChartMain.univMap actU)

/-- The universal value of `(action) ∘ x`. -/
noncomputable def kB (x : yoneda.obj U ⟶ X) :
    X.obj (op (spObj U (ChartMain.ι1 U (M := M)) ChartMain.contains1)) :=
  actX.smul (U := op _) ChartMain.univPt1
    (x.app _ (spToT U (ChartMain.ι1 U (M := M)) ChartMain.contains1))

/-- Equivariance is an equality on `Spec Γ(U)[M]`. -/
theorem equivariant_of_universal (x : yoneda.obj U ⟶ X) (h : kA actU x = kB actX x) :
    IsEquivariant actU actX x := by
  intro T g t
  have hψ : (ChartMain.evalAt ((SCH).map t).appTop.hom g).comp (ChartMain.ι1 U (M := M)) =
      ((SCH).map t).appTop.hom := RingHom.ext fun b => ChartMain.evalAt_ι _ _ b
  obtain ⟨τ, hτ₁, hτ₂⟩ := ChartMain.exists_spLift (R' := ChartMain.R1 U M) (ChartMain.ι1 U)
    ChartMain.contains1 t _ hψ
  have hres : ChartMain.secPt ((SCH).map τ).appTop.hom (ChartMain.univPt1 (U := U)) = g :=
    MonoidHom.ext fun m => by
      refine (hτ₂ _).trans ?_
      refine (ChartMain.evalAt_single _ _ (Multiplicative.toAdd m) 1).trans ?_
      rw [map_one, one_mul]
      rfl
  have e1 : actU.smul (F := yoneda.obj U) g t = τ ≫ ChartMain.univMap actU :=
    ChartMain.smulAt_eq_comp actU t g τ hτ₁ hres
  rw [e1]
  have nat := fun (y : _ ⟶ U) => natA x τ.op y
  have e2 : x.app T (τ ≫ ChartMain.univMap actU) = X.map τ.op (kA actU x) :=
    (nat (ChartMain.univMap actU)).symm
  rw [e2, h]
  refine (actX.map_smul τ.op _ _).trans ?_
  have e3 : X.map τ.op (x.app _ (spToT U (ChartMain.ι1 U (M := M)) ChartMain.contains1)) =
      x.app T t := by
    rw [← hτ₁]
    exact nat _
  rw [e3]
  exact congrArg (fun z => actX.smul (U := T) z (x.app T t)) hres

/-- The universal equality follows from equivariance. -/
theorem universal_of_equivariant (x : yoneda.obj U ⟶ X) (h : IsEquivariant actU actX x) :
    kA actU x = kB actX x :=
  h (T := op (spObj U (ChartMain.ι1 U (M := M)) ChartMain.contains1)) (ChartMain.univPt1 (U := U))
    (spToT U (ChartMain.ι1 U (M := M)) ChartMain.contains1)

end Universal

section Spread

/-- The system `Φ = (·)[M]`. -/
noncomputable def algM (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (M : Type u)
    [AddCommGroup M] [AddMonoid.FG M] : AlgSys B S hS where
  Φ := algF M
  τ _ := AddMonoidAlgebra.singleZeroRingHom
  τ_nat f := RingHom.ext fun r => algF_map_single M f 0 r
  pres hc := ⟨isColimit_algF hc M⟩
  cont _ _ := ChartMain.contains1

variable {T' T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]

lemma mp_univPt (s : T' ⟶ T) :
    ChartMain.secPt ((SCH).map ((algM B S hS M).mp s)).appTop.hom (ChartMain.univPt1 (U := T)) =
      ChartMain.univPt1 (U := T') :=
  MonoidHom.ext fun m => by
    refine ((algM B S hS M).mp_appTop s _).trans ?_
    exact congrArg (spSec T' _ _) ((algF_map_single M _ _ _).trans (by rw [map_one]; rfl))

lemma mp_toT (s : T' ⟶ T) :
    (algM B S hS M).mp s ≫ spToT T (ChartMain.ι1 T (M := M)) ChartMain.contains1 =
      spToT T' (ChartMain.ι1 T' (M := M)) ChartMain.contains1 ≫ s :=
  sp2_toT _ _ _

variable (actT' : AAction (fppfO B S hS) M (yoneda.obj T'))
  (actT : AAction (fppfO B S hS) M (yoneda.obj T))
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (actX : AAction (fppfO B S hS) M X)

lemma mp_univMap (s : T' ⟶ T) (hs : IsEquivariant actT' actT (yoneda.map s)) :
    (algM B S hS M).mp s ≫ ChartMain.univMap actT = ChartMain.univMap actT' ≫ s := by
  have h1 := ChartMain.comp_smulAt actT ((algM B S hS M).mp s) ChartMain.univPt1
    (spToT T (ChartMain.ι1 T (M := M)) ChartMain.contains1)
  rw [mp_univPt, mp_toT] at h1
  refine h1.trans ?_
  exact (hs (T := op _) ChartMain.univPt1
    (spToT T' (ChartMain.ι1 T' (M := M)) ChartMain.contains1)).symm

lemma kA_pull (x : yoneda.obj T ⟶ X) (s : T' ⟶ T) (hs : IsEquivariant actT' actT (yoneda.map s)) :
    X.map ((algM B S hS M).mp s).op (kA actT x) = kA actT' (yoneda.map s ≫ x) := by
  refine (natA x ((algM B S hS M).mp s).op _).trans ?_
  exact congrArg (x.app _) (mp_univMap actT' actT s hs)

lemma kB_pull (x : yoneda.obj T ⟶ X) (s : T' ⟶ T) :
    X.map ((algM B S hS M).mp s).op (kB actX x) = kB actX (yoneda.map s ≫ x) := by
  refine (actX.map_smul ((algM B S hS M).mp s).op _ _).trans ?_
  have e : X.map ((algM B S hS M).mp s).op
      (x.app _ (spToT T (ChartMain.ι1 T (M := M)) ChartMain.contains1)) =
      (yoneda.map s ≫ x).app _ (spToT T' (ChartMain.ι1 T' (M := M)) ChartMain.contains1) := by
    refine (natA x ((algM B S hS M).mp s).op _).trans ?_
    exact congrArg (x.app _) (mp_toT s)
  exact Eq.trans (congrArg (fun y => actX.smul (U := op (spObj T' (ChartMain.ι1 T' (M := M)) ChartMain.contains1))
      (ChartMain.secPt ((SCH).map ((algM B S hS M).mp s)).appTop.hom (ChartMain.univPt1 (U := T))) y) e)
    (congrArg (fun z => actX.smul (U := op (spObj T' (ChartMain.ι1 T' (M := M)) ChartMain.contains1)) z _) (mp_univPt s))

/-- **Artin approximation step, spreading of `φ`.** An equivariant point of a limit preserving `X` over a cofiltered limit
of affine objects with action comes from an equivariant point at a finite level. -/
theorem exists_equivariant_rep
    (hl : LimitPreserving.{u, u, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) X)
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ BigFppfOver B S hS) [AffDg D]
    (c : Cone D) [IsAffine ((SCH).obj c.pt)] (h : IsLimit ((SCH).mapCone c))
    (actD : ∀ i, AAction (fppfO B S hS) M (yoneda.obj (D.obj i)))
    (actC : AAction (fppfO B S hS) M (yoneda.obj c.pt))
    (hD : ∀ {i j} (f : i ⟶ j), IsEquivariant (actD i) (actD j) (yoneda.map (D.map f)))
    (hC : ∀ i, IsEquivariant actC (actD i) (yoneda.map (c.π.app i)))
    (x : yoneda.obj c.pt ⟶ X) (hx : IsEquivariant actC actX x) :
    ∃ (i : I) (xi : yoneda.obj (D.obj i) ⟶ X), IsEquivariant (actD i) actX xi ∧
      yoneda.map (c.π.app i) ≫ xi = x := by
  obtain ⟨hc⟩ := hl I D c h (fun i => AffDg.aff i) inferInstance
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit hc (yonedaEquiv x)
  let xj : yoneda.obj (D.obj j.unop) ⟶ X := yonedaEquiv.symm y
  have hxj : yoneda.map (c.π.app j.unop) ≫ xj = x := by
    apply yonedaEquiv.injective
    refine Eq.trans ?_ hy
    rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    simp [xj, yonedaEquiv_symm_app_apply]
  have e : X.map ((algM B S hS M).mp (T' := c.pt) (c.π.app j.unop)).op (kA (actD _) xj) =
      X.map ((algM B S hS M).mp (T' := c.pt) (c.π.app j.unop)).op (kB actX xj) := by
    rw [kA_pull actC (actD _) xj _ (hC _), kB_pull actX xj, hxj]
    exact universal_of_equivariant actC actX x hx
  obtain ⟨k, f, hf⟩ := AlgSys.exists_eq hl (algM B S hS M) D c h j.unop _ _ e
  refine ⟨k, yoneda.map (D.map f) ≫ xj, equivariant_of_universal _ _ _ ?_, ?_⟩
  · rw [← kA_pull (actD k) (actD _) xj _ (hD f), ← kB_pull actX xj]
    exact hf
  · rw [← Functor.map_comp_assoc, c.w, hxj]

end Spread

end AlgMag.ChartS5

#print axioms AlgMag.ChartS5.homog_gradedAction
#print axioms AlgMag.ChartS5.exists_equivariant_rep
