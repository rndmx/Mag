/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec14Strong
import AlgMag.Sec14CounterScheme
import StacksFrontier.AlgebraicGeometry.Spaces.Representability

/-!
# Counterexample to the last assertion of Proposition 14.4 as printed

Proposition 14.4 of *Algebraic Magnetism* ends: "If `N = Z` is a group the natural morphism
`X^Z → X` is representable by a closed immersion", without a `Z`-FPR atlas (the hypothesis of
Proposition 8.1, which its proof invokes).

Let `M = ℤ/2`, `Z = 0`, `S = Spec A` with `2` invertible, and `D ⊂ S` a dense open, `D ≠ S`. Let `X`
be `S` with the complement of `D` doubled, a quasi-separated scheme, locally of finite presentation
over `S`, not separated, and let `D(M) = μ₂` act through the swap `σ` of the two charts. Then
`X^0 = X^{μ₂}` is `D ⊂ X`, which is not closed.

* `AlgMag.Sec14Counter.not_isClosedImm`: the general statement.
* `AlgMag.Sec14Counter.not_isClosedImm_polynomial`: for `S = Spec ℚ[t]` and `D = {t ≠ 0}`.
* `AlgMag.Sec14Counter.not_existsZFPRAtlas`: this action has no `0`-FPR atlas. So in Theorem 6.8
  neither of the hypotheses (i) `X` separated, (ii) `M/Z` torsion-free can be dropped altogether.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgMag.Sec14Counter

variable (B : BigFppfSite.{0}) {S : Scheme.{0}} (hS : B.Contains S)
variable {D : Scheme.{0}} (i : D ⟶ S) [IsOpenImmersion i]

include hS in
/-- The doubled scheme is in the site as soon as the base is. -/
theorem contains_doubled : B.Contains (doubled i) := by
  refine B.contains_of_openCover (ι := Bool) ?_ (fun b => chart i b)
    (fun y => charts_cover i y) (fun _ => hS)
  exact lt_trans (by simpa using Cardinal.natCast_lt_aleph0 (n := 2)) B.aleph0_lt_cutoff_cof

/-- The doubled scheme, as an object of the big fppf category over `S`. -/
noncomputable abbrev XO : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS (contains_doubled B hS i) (doubledToBase i)

local notation "SCH" => BigFppfOver.toScheme B S hS

variable {B hS i}

/-- The structure morphism of a point of `X` over `S`. -/
theorem map_comp_base {U : BigFppfOver B S hS} (x : U ⟶ XO B hS i) :
    (SCH).map x ≫ doubledToBase i = B.inclusion.map U.hom := by
  have := Over.w x
  exact congrArg B.inclusion.map this

theorem isUnit_two_of_base (h2 : IsUnit (2 : Γ(S, ⊤))) (U : BigFppfOver B S hS) :
    IsUnit (2 : Γ((SCH).obj U, ⊤)) :=
  isUnit_two_map (B.inclusion.map U.hom) h2

/-- The twist of a point of `X`, as a morphism of the site. -/
noncomputable def smulHom (h2 : IsUnit (2 : Γ(S, ⊤))) {U : BigFppfOver B S hS}
    (ε : Γ((SCH).obj U, ⊤)) (hε : ε * ε = 1) (x : U ⟶ XO B hS i) : U ⟶ XO B hS i :=
  BigFppfOver.homMk B S hS (contains_doubled B hS i) (doubledToBase i)
    (twist (swap i) hε (isUnit_two_of_base h2 U) ((SCH).map x))
    ((twist_comp (swap i) (doubledToBase i) (swap_toBase i) hε _ _).trans (map_comp_base x))

theorem map_smulHom (h2 : IsUnit (2 : Γ(S, ⊤))) {U : BigFppfOver B S hS}
    (ε : Γ((SCH).obj U, ⊤)) (hε : ε * ε = 1) (x : U ⟶ XO B hS i) :
    (SCH).map (smulHom h2 ε hε x) = twist (swap i) hε (isUnit_two_of_base h2 U) ((SCH).map x) :=
  BigFppfOver.toScheme_map_homMk B S hS _ _ _ _

theorem smulHom_congr (h2 : IsUnit (2 : Γ(S, ⊤))) {U : BigFppfOver B S hS}
    {ε ε' : Γ((SCH).obj U, ⊤)} (e : ε = ε') (hε : ε * ε = 1) (hε' : ε' * ε' = 1)
    (x : U ⟶ XO B hS i) : smulHom h2 ε hε x = smulHom h2 ε' hε' x := by
  subst e; rfl

/-- The value at the generator of a point of `D(ℤ/2)`. -/
noncomputable def eps {U : (BigFppfOver B S hS)ᵒᵖ} (h : APt (fppfO B S hS) (ZMod 2) U) :
    Γ((SCH).obj (unop U), ⊤) :=
  h (Multiplicative.ofAdd 1)

theorem eps_sq {U : (BigFppfOver B S hS)ᵒᵖ} (h : APt (fppfO B S hS) (ZMod 2) U) :
    eps h * eps h = 1 := by
  have : (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd 1 = 1 := by decide
  exact (map_mul h _ _).symm.trans ((congrArg h this).trans (map_one h))

theorem eps_mul {U : (BigFppfOver B S hS)ᵒᵖ} (g h : APt (fppfO B S hS) (ZMod 2) U) :
    eps (g * h) = eps g * eps h := rfl

theorem eps_one {U : (BigFppfOver B S hS)ᵒᵖ} : eps (1 : APt (fppfO B S hS) (ZMod 2) U) = 1 := rfl

/-- The action of `D(ℤ/2) = μ₂` on the doubled scheme through the swap. -/
noncomputable def swapAction (h2 : IsUnit (2 : Γ(S, ⊤))) :
    AAction (fppfO B S hS) (ZMod 2) (yoneda.obj (XO B hS i)) where
  smul {U} h x := smulHom h2 (eps h) (eps_sq h) x
  one_smul {U} x := by
    apply (SCH).map_injective
    rw [map_smulHom]
    exact twist_of_eq_one _ _ _ _ eps_one
  mul_smul {U} g h x := by
    apply (SCH).map_injective
    rw [map_smulHom, map_smulHom, map_smulHom]
    have hm : (eps g * eps h) * (eps g * eps h) = 1 := by
      rw [mul_mul_mul_comm, eps_sq, eps_sq, one_mul]
    exact twist_mul (swap i) (swap_swap i) (eps_sq g) (eps_sq h) hm _ _
  map_smul {U V} f h x := by
    apply (SCH).map_injective
    change (SCH).map (f.unop ≫ smulHom h2 (eps h) (eps_sq h) x) =
      (SCH).map (smulHom h2 (eps (APt.res f h)) (eps_sq _) (f.unop ≫ x))
    rw [Functor.map_comp, map_smulHom, map_smulHom, Functor.map_comp]
    exact comp_twist (swap i) ((SCH).map f.unop) (eps_sq h) _ _ (eps_sq (APt.res f h)) _

/-- `X`, as a functor on the big affine category. -/
noncomputable abbrev XFun (B : BigFppfSite.{0}) {S : Scheme.{0}} (hS : B.Contains S) {D : Scheme.{0}}
    (i : D ⟶ S) [IsOpenImmersion i] : (BigAffineFppf B S hS)ᵒᵖ ⥤ Type :=
  (BigAffineFppf.inclusion B S hS).op ⋙ yoneda.obj (XO B hS i)

theorem isClosedImm_id (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type) : IsClosedImm (𝟙 F) := by
  haveI : (MorphismProperty.inverseImage (@IsClosedImmersion.{0} : MorphismProperty Scheme.{0})
      (BigFppfOver.toScheme B S hS)).ContainsIdentities :=
    ⟨fun X => by
      change IsClosedImmersion ((BigFppfOver.toScheme B S hS).map (𝟙 X))
      rw [CategoryTheory.Functor.map_id]; infer_instance⟩
  exact MorphismProperty.id_mem (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@IsClosedImmersion.{0} : MorphismProperty Scheme.{0}) (BigFppfOver.toScheme B S hS))) F

/-- The trivial presentation of the doubled scheme, as an ind-scheme. -/
noncomputable def trivialPres (B : BigFppfSite.{0}) {S : Scheme.{0}} (hS : B.Contains S)
    {D : Scheme.{0}} (i : D ⟶ S) [IsOpenImmersion i] :
    IndPresentation.{0, 0, 0} (IsAlgebraicSpace B S hS) (XFun B hS i) where
  I := PUnit
  obj _ := yoneda.obj (XO B hS i)
  prop _ := isAlgebraicSpace_yoneda B S hS _
  tr _ := 𝟙 _
  tr_refl _ := rfl
  tr_trans _ _ := (Category.comp_id _).symm
  closed _ := isClosedImm_id _
  π _ _ x := x
  π_map _ _ _ _ _ := rfl
  π_tr _ _ _ := rfl
  surj _ x := ⟨PUnit.unit, x, rfl⟩
  inj _ _ x x' h := ⟨PUnit.unit, le_refl _, h⟩

/-- The ind-action on the trivial presentation. -/
noncomputable def trivialAct (h2 : IsUnit (2 : Γ(S, ⊤))) :
    IndAction (ZMod 2) (trivialPres B hS i) where
  act _ := swapAction h2
  tr_smul _ _ _ _ := rfl

/-- The action on `X` as an ind-object is the action on points. -/
theorem toAction_smul (h2 : IsUnit (2 : Γ(S, ⊤))) {T : BigAffineFppf B S hS}
    (g : APt (affineO B S hS) (ZMod 2) (op T)) (x : (XFun B hS i).obj (op T)) :
    (trivialAct (i := i) h2).toAction.smul g x = (swapAction h2).smul g x :=
  ((trivialAct (i := i) h2).π_smul PUnit.unit g x).symm

/-- The sign character of `ℤ/2` with values in a ring. -/
noncomputable def signChar (R : Type) [CommRing R] : Multiplicative (ZMod 2) →* R where
  toFun n := if Multiplicative.toAdd n = 0 then 1 else -1
  map_one' := by simp
  map_mul' a b := by
    have h01 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    have h1 : (1 : ZMod 2) ≠ 0 := by decide
    have h2 : (1 : ZMod 2) + 1 = 0 := by decide
    change (if a.toAdd + b.toAdd = 0 then (1 : R) else -1) =
      (if a.toAdd = 0 then 1 else -1) * (if b.toAdd = 0 then 1 else -1)
    rcases h01 a.toAdd with ha | ha <;> rcases h01 b.toAdd with hb | hb <;> rw [ha, hb] <;>
      simp [h1, h2]

/-- **Counterexample to the last assertion of Proposition 14.4 as printed.** For `S` reduced affine
with `2` invertible, and `D → S` an open immersion from an affine scheme, dense and not surjective,
let `X` be `S` with the complement of `D` doubled, with `D(ℤ/2)` acting by the swap of the charts.
Then `X^0 → X` is not representable by closed immersions. -/
theorem not_isClosedImm [IsAffine S] [IsAffine D] [IsReduced S] (h2 : IsUnit (2 : Γ(S, ⊤)))
    (hd : DenseRange i) (hns : ¬ Function.Surjective i) :
    ¬ IndAttractorMapHasProp (trivialAct (i := i) (B := B) (hS := hS) h2)
      (⊥ : AddSubgroup (ZMod 2)).toAddSubmonoid (fun f => IsClosedImm f) := by
  intro H
  let a := trivialAct (i := i) (B := B) (hS := hS) h2
  let To : BigFppfOver B S hS := BigFppfOver.mk B S hS hS (𝟙 S)
  let T : BigAffineFppf B S hS := ⟨To, inferInstanceAs (IsAffine S)⟩
  let hD : B.Contains D := B.contains_of_mono i hS
  let T1o : BigFppfOver B S hS := BigFppfOver.mk B S hS hD i
  let T1 : BigAffineFppf B S hS := ⟨T1o, inferInstanceAs (IsAffine D)⟩
  let t1o : T1o ⟶ To := BigFppfOver.homMk B S hS hS (𝟙 S) i (Category.comp_id _)
  let t1 : T1 ⟶ T := ObjectProperty.homMk t1o
  let y : (XFun B hS i).obj (op T) :=
    BigFppfOver.homMk B S hS (contains_doubled B hS i) (doubledToBase i) (chart i true)
      ((chart_toBase i true).trans rfl)
  obtain ⟨Z, q, hq, he⟩ := H T y
  -- `D` lies in the attractor
  have hfix : ∀ {T' : BigAffineFppf B S hS} (t : T' ⟶ T1)
      (h : APt (affineO B S hS) (ZMod 2) (op T')),
      a.toAction.smul h ((XFun B hS i).map t.op ((XFun B hS i).map t1.op y)) =
        (XFun B hS i).map t.op ((XFun B hS i).map t1.op y) := by
    intro T' t h
    rw [show a.toAction.smul h _ = _ from toAction_smul h2 h _]
    apply (SCH).map_injective
    refine (map_smulHom h2 _ _ _).trans (twist_of_fixed _ _ _ _ ?_)
    change ((SCH).map t.hom ≫ i ≫ chart i true) ≫ swap i = (SCH).map t.hom ≫ i ≫ chart i true
    have e : (i ≫ chart i true) ≫ swap i = i ≫ chart i true := by
      rw [Category.assoc, chart_swap]; exact i_comp_chart i false true
    exact (Category.assoc _ _ _).trans (congrArg ((SCH).map t.hom ≫ ·) e)
  let ψ₁ : AttractorPt a.toAction (⊥ : AddSubgroup (ZMod 2)).toAddSubmonoid T1 :=
    { app := fun {T'} t _ => (XFun B hS i).map t.op ((XFun B hS i).map t1.op y)
      naturality := fun s t _ => by
        rw [op_comp, Functor.map_comp_apply]
      equivariant := fun t h _ => (hfix t h).symm }
  have hψ₁ : ψ₁.toPoint = (XFun B hS i).map t1.op y := by
    change (XFun B hS i).map (𝟙 T1).op _ = _
    simp
  obtain ⟨e₁⟩ := he T1 t1
  obtain ⟨⟨z₁, hz₁⟩, -⟩ := e₁.surjective ⟨ψ₁, hψ₁⟩
  -- the closed subscheme of `S`
  let R := hq.rep
  let W := R.pullback (𝟙 (yoneda.obj To))
  let j : W ⟶ To := R.snd (𝟙 _)
  let φ : yoneda.obj W ⟶ Z := R.fst (𝟙 _)
  have hpb := R.isPullback (𝟙 (yoneda.obj To))
  have hφ : φ ≫ q = yoneda.map j := by simpa using hpb.w
  have hφiso : IsIso φ := hpb.isIso_fst_of_isIso
  have hbij : ∀ T' : (BigFppfOver B S hS)ᵒᵖ, Function.Bijective (φ.app T') := fun T' =>
    (isIso_iff_bijective _).1 inferInstance
  have hqφ : ∀ {U : BigFppfOver B S hS} (v : U ⟶ W), q.app (op U) (φ.app (op U) v) = v ≫ j :=
    fun {U} v => congrArg (fun m => m.app (op U) v) hφ
  have hc : IsClosedImmersion ((SCH).map j) := hq.property_snd _
  obtain ⟨v, hv⟩ := (hbij (op T1o)).2 z₁
  have hvj : v ≫ j = t1o := (hqφ v).symm.trans ((congrArg _ hv).trans hz₁)
  have hvj' : (SCH).map v ≫ (SCH).map j = i := by
    rw [← Functor.map_comp, hvj]
    exact BigFppfOver.toScheme_map_homMk B S hS _ _ _ _
  haveI : Surjective ((SCH).map j) := ⟨by
    have hcl := ((SCH).map j).isClosedEmbedding.isClosed_range
    have hsub : Set.range i ⊆ Set.range ((SCH).map j) := by
      rintro _ ⟨d, rfl⟩
      refine ⟨(SCH).map v d, ?_⟩
      exact (Scheme.Hom.comp_apply ((SCH).map v) ((SCH).map j) d).symm.trans
        (congrArg (fun m : D ⟶ S => m d) hvj')
    have := hcl.closure_subset_iff.2 hsub
    exact fun x => this (hd x)⟩
  haveI : IsReduced ((SCH).obj To) := inferInstanceAs (IsReduced S)
  haveI : IsIso ((SCH).map j) := isIso_of_isClosedImmersion_of_surjective _
  have hw : (SCH).map j ≫ B.inclusion.map To.hom = B.inclusion.map W.hom :=
    congrArg B.inclusion.map (Over.w j)
  let s : To ⟶ W := Over.homMk (ObjectProperty.homMk (inv ((SCH).map j))) (by
    apply ObjectProperty.hom_ext
    change inv ((SCH).map j) ≫ B.inclusion.map W.hom = B.inclusion.map To.hom
    rw [← hw, IsIso.inv_hom_id_assoc])
  have hsj : s ≫ j = 𝟙 To := by
    apply (SCH).map_injective
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
    exact IsIso.inv_hom_id _
  -- so the point `y` of `X` lies in `X^0`, and `y` is fixed by `-1`
  obtain ⟨e₂⟩ := he T (𝟙 T)
  have hz : q.app (op To) (φ.app (op To) s) = (BigAffineFppf.inclusion B S hS).map (𝟙 T) :=
    (hqφ s).trans (hsj.trans ((BigAffineFppf.inclusion B S hS).map_id T).symm)
  obtain ⟨ψ, hψ⟩ := e₂ ⟨φ.app (op To) s, hz⟩
  have hψ' : ψ.toPoint = y := hψ.trans (by simp)
  let χ : APt (affineO B S hS) (ZMod 2) (op T) := signChar _
  have hχ : APt.toMagnet (⊥ : AddSubgroup (ZMod 2)).toAddSubmonoid χ * 1 = 1 := by
    rw [mul_one]
    refine MonoidHom.ext fun n => ?_
    have hn : ((Multiplicative.toAdd n : (⊥ : AddSubgroup (ZMod 2)).toAddSubmonoid) : ZMod 2) = 0 :=
      (Multiplicative.toAdd n).2
    rw [APt.toMagnet_apply, hn]
    exact map_one χ
  have hequiv := ψ.equivariant (𝟙 T) χ 1
  rw [hχ] at hequiv
  have hyy : y = (swapAction h2).smul χ y := by
    have h3 := hequiv.trans (toAction_smul (i := i) h2 χ _)
    exact (hψ'.symm.trans h3).trans (congrArg _ hψ')
  have hchart : chart i true = chart i false := by
    have hm : (SCH).map y = chart i true := BigFppfOver.toScheme_map_homMk B S hS _ _ _ _
    have h4 := congrArg (SCH).map hyy
    rw [show (swapAction h2).smul χ y = smulHom h2 (eps χ) (eps_sq χ) y from rfl, map_smulHom] at h4
    have hneg : eps χ = -1 := by
      have h1 : (1 : ZMod 2) ≠ 0 := by decide
      exact if_neg (t := 1) h1
    have h5 := h4.trans (twist_of_eq_neg_one (swap i) (eps_sq χ) _ ((SCH).map y) hneg)
    have h6 : chart i true = chart i true ≫ swap i := h5
    exact h6.trans (chart_swap i true)
  exact hns (surjective_of_chart_eq i hchart)

/-- The action of **Theorem `not_isClosedImm`** has no `0`-FPR atlas: Theorem 6.8 needs one of its
hypotheses. -/
theorem not_existsZFPRAtlas [IsAffine S] [IsAffine D] [IsReduced S] (h2 : IsUnit (2 : Γ(S, ⊤)))
    (hd : DenseRange i) (hns : ¬ Function.Surjective i) :
    ¬ ExistsZFPRAtlas (swapAction (i := i) (B := B) (hS := hS) h2) (⊥ : AddSubgroup (ZMod 2)) :=
  fun hat => not_isClosedImm h2 hd hns
    (indAttractorMap_isClosedImm (trivialAct (i := i) (B := B) (hS := hS) h2) ⊥
      (fun _ => isAlgebraicSpace_yoneda B S hS _) (fun _ => hat))

/-- The doubled scheme is quasi-separated, as Proposition 14.4 requires. -/
theorem quasiSeparatedSpace_doubled [IsAffine S] [IsAffine D] : QuasiSeparatedSpace (doubled i) := by
  have hA : ∀ b, IsAffineOpen (chart i b).opensRange := fun b => isAffineOpen_opensRange _
  refine Scheme.quasiSeparatedSpace_of_isOpenCover (fun b => (chart i b).opensRange) ?_ hA ?_
  · rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro x _
    obtain ⟨b, hb⟩ := charts_cover i x
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨b, hb⟩
  · intro b c
    by_cases hbc : b = c
    · subst hbc
      rw [Set.inter_self]
      exact (hA b).isCompact
    · have e : ((chart i b).opensRange : Set (doubled i)) ∩ (chart i c).opensRange =
          Set.range (i ≫ chart i b) := by
        ext x
        constructor
        · rintro ⟨⟨a, rfl⟩, ⟨a', ha'⟩⟩
          obtain ⟨k, fi, fj, z, h1, h2⟩ :=
            (Scheme.IsLocallyDirected.ι_eq_ι_iff (spanF i)).1 ha'
          rcases k with _ | k
          · rcases fj with _ | _
            refine ⟨z, ?_⟩
            rw [Scheme.Hom.comp_apply]
            exact congrArg _ h2
          · rcases fi with _ | _
            rcases fj with _ | _
            exact absurd rfl hbc
        · rintro ⟨z, rfl⟩
          refine ⟨⟨i z, (Scheme.Hom.comp_apply _ _ _).symm⟩, ⟨i z, ?_⟩⟩
          have := i_comp_chart i c b
          exact (Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg (fun m => m z) this)
      change IsCompact (((chart i b).opensRange : Set (doubled i)) ∩ (chart i c).opensRange)
      rw [e]
      exact isCompact_range (i ≫ chart i b).continuous

/-- The doubled scheme is quasi-separated over `S`. -/
theorem quasiSeparated_toBase [IsAffine S] [IsAffine D] : QuasiSeparated (doubledToBase i) := by
  haveI := quasiSeparatedSpace_doubled (i := i)
  exact (quasiSeparated_iff_quasiSeparatedSpace _).2 inferInstance

section Polynomial

open Polynomial

/-- `D(t) ⊂ Spec ℚ[t]`. -/
noncomputable abbrev iPoly : Spec (.of (Localization.Away (Polynomial.X : ℚ[X]))) ⟶ Spec (.of ℚ[X]) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ[X] (Localization.Away (Polynomial.X : ℚ[X]))))

instance : IsOpenImmersion iPoly := inferInstance

theorem isUnit_two_poly : IsUnit (2 : Γ(Spec (.of ℚ[X]), ⊤)) := by
  have h : IsUnit (2 : ℚ[X]) := by
    have : (2 : ℚ[X]) = C 2 := (map_ofNat C 2).symm
    rw [this]
    exact (isUnit_C.2 (by norm_num))
  have h' := h.map (Scheme.ΓSpecIso (.of ℚ[X])).inv.hom
  rwa [map_ofNat] at h'

theorem range_iPoly : Set.range iPoly = (PrimeSpectrum.basicOpen (Polynomial.X : ℚ[X]) : Set (PrimeSpectrum ℚ[X])) :=
  PrimeSpectrum.localization_away_comap_range _ _

theorem denseRange_iPoly : DenseRange iPoly := by
  change Dense (Set.range iPoly)
  rw [range_iPoly]
  refine (PrimeSpectrum.basicOpen (Polynomial.X : ℚ[X])).isOpen.dense ?_
  exact ⟨⊥, by simpa using (X_ne_zero : (Polynomial.X : ℚ[X]) ≠ 0)⟩

theorem not_surjective_iPoly : ¬ Function.Surjective iPoly := by
  intro h
  have h' : Set.range iPoly = Set.univ := h.range_eq
  rw [range_iPoly] at h'
  obtain ⟨m, hm, hx⟩ := exists_max_ideal_of_mem_nonunits (not_isUnit_X (R := ℚ))
  have hmem : (⟨m, hm.isPrime⟩ : PrimeSpectrum ℚ[X]) ∈
      (PrimeSpectrum.basicOpen (Polynomial.X : ℚ[X]) : Set (PrimeSpectrum ℚ[X])) :=
    h' ▸ Set.mem_univ _
  exact hmem hx

/-- **Counterexample to the last assertion of Proposition 14.4**: `S = Spec ℚ[t]`, `X` the affine
line with doubled origin, `M = ℤ/2`, `Z = 0`, `μ₂` acting by swapping the origins. -/
theorem not_isClosedImm_polynomial (B : BigFppfSite.{0}) (hS : B.Contains (Spec (.of ℚ[X]))) :
    ¬ IndAttractorMapHasProp (trivialAct (i := iPoly) (B := B) (hS := hS) isUnit_two_poly)
      (⊥ : AddSubgroup (ZMod 2)).toAddSubmonoid (fun f => IsClosedImm f) :=
  not_isClosedImm isUnit_two_poly denseRange_iPoly not_surjective_iPoly

end Polynomial

end AlgMag.Sec14Counter

#print axioms AlgMag.Sec14Counter.not_isClosedImm
#print axioms AlgMag.Sec14Counter.not_existsZFPRAtlas
#print axioms AlgMag.Sec14Counter.quasiSeparated_toBase
#print axioms AlgMag.Sec14Counter.not_isClosedImm_polynomial
