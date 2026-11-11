/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartPoint

/-!
# The stabilizer of a closed point, without separatedness

The stabilizer `H ⊂ G_k` of a point is closed when `X` is separated. For
`x : P → X` a closed immersion, `P` affine, closedness needs nothing of `X`: `H` is closed in the
closed subscheme `D(M)_P ×_X P`, as the equalizer of two maps to the affine `P`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.ChartPoint

open ChartMain

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [AddMonoid.FG M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

variable {P : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj P)]

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj P)] in
lemma closedι_appTop_eq_zero_of_mem {Y : Scheme.{u}} [IsAffine Y] (I : Ideal Γ(Y, ⊤)) (r : Γ(Y, ⊤))
    (h : r ∈ I) : (Chart.closedι Y I).appTop r = 0 := by
  have e : (Scheme.ΓSpecIso Γ(Y, ⊤)).hom ≫ Y.isoSpec.inv.appTop = 𝟙 _ := by
    rw [← Scheme.toSpecΓ_appTop, ← Scheme.isoSpec_hom, ← Scheme.Hom.comp_appTop, Iso.inv_hom_id]
    simp
  have hinv : Y.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(Y, ⊤)).inv := (Iso.hom_comp_eq_id _).mp e
  have hnat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have this : (Chart.closedι Y I).appTop r = (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop
      ((Scheme.ΓSpecIso Γ(Y, ⊤)).inv r) := by
    rw [Chart.closedι, Scheme.Hom.comp_appTop, hinv]; rfl
  have h1 := ConcreteCategory.congr_hom hnat ((Scheme.ΓSpecIso Γ(Y, ⊤)).inv r)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ← this] at h1
  have h3 : (Scheme.ΓSpecIso Γ(Y, ⊤)).hom ((Scheme.ΓSpecIso Γ(Y, ⊤)).inv r) = r := by simp
  erw [h3] at h1
  have h2 : (Ideal.Quotient.mk I) r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h
  have h4 : (Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, ⊤) ⧸ I))).hom ((Chart.closedι Y I).appTop r) = 0 := by
    first | exact h1.trans h2 | exact h1.symm.trans h2
  exact (Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, ⊤) ⧸ I))).commRingCatIsoToRingEquiv.injective
    (h4.trans (map_zero _).symm)

/-- The equalizer of `a` and `t ↦ x ∘ t`, for `x : P → X` a closed immersion: replaces
`AlgMag.exists_equalizer`, which assumes `X` separated. -/
theorem exists_equalizer_closedPoint (x : yoneda.obj P ⟶ X)
    (hx : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) (SCH))) x)
    {W : BigFppfOver B S hS} [IsAffine ((SCH).obj W)] (t : W ⟶ P) (a : X.obj (op W)) :
    ∃ (E : BigFppfOver B S hS) (e : E ⟶ W), AlgebraicGeometry.IsClosedImmersion ((SCH).map e) ∧
      X.map e.op a = x.app (op E) (e ≫ t) ∧
      ∀ {V : BigFppfOver B S hS} (r : V ⟶ W), X.map r.op a = x.app (op V) (r ≫ t) →
        ∃ l : V ⟶ E, l ≫ e = r := by
  let ya : yoneda.obj W ⟶ X := yonedaEquiv.symm a
  let F := hx.rep.pullback ya
  let j : F ⟶ W := hx.rep.snd ya
  let s : F ⟶ P := hx.rep.fst' ya
  have hj : AlgebraicGeometry.IsClosedImmersion ((SCH).map j) := hx.property_snd ya
  haveI hF : IsAffine ((SCH).obj F) := isAffine_of_isAffineHom ((SCH).map j)
  have hpb := hx.rep.isPullback' ya
  let I : Ideal Γ((SCH).obj F, ⊤) := Ideal.span (Set.range fun b : Γ((SCH).obj P, ⊤) =>
    ((SCH).map s).appTop.hom b - ((SCH).map (j ≫ t)).appTop.hom b)
  let c := Chart.closedι ((SCH).obj F) I
  let E := Chart.immObj F c
  let i : E ⟶ F := Chart.immι F c
  haveI hic : AlgebraicGeometry.IsClosedImmersion ((SCH).map i) :=
    inferInstanceAs (AlgebraicGeometry.IsClosedImmersion c)
  haveI hE : IsAffine ((SCH).obj E) := isAffine_of_isAffineHom ((SCH).map i)
  have hsurj : Function.Surjective ((SCH).map i).appTop.hom :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine ((SCH).map i)).2
  have hIk : ∀ r ∈ I, ((SCH).map i).appTop.hom r = 0 := fun r hr =>
    closedι_appTop_eq_zero_of_mem I r hr
  have hsE : i ≫ s = i ≫ j ≫ t := by
    refine site_hom_ext (toAffine_ext ?_)
    ext b
    have := hIk _ (Ideal.subset_span ⟨b, rfl⟩)
    rw [map_sub, sub_eq_zero] at this
    exact this
  have hsq : yoneda.map s ≫ x = yoneda.map j ≫ ya := hpb.w
  have hnat : ∀ {V : BigFppfOver B S hS} (r : V ⟶ W), (yoneda.map r ≫ ya).app (op V) (𝟙 V) =
      X.map r.op a := fun r => by
    simp [ya, yonedaEquiv_symm_app_apply]
  refine ⟨E, i ≫ j, ?_, ?_, fun {V} r hr => ?_⟩
  · rw [Functor.map_comp]; infer_instance
  · have h1 := congrArg (fun φ => φ.app (op E) i) hsq
    have h2 : x.app (op E) (i ≫ s) = (yoneda.map (i ≫ j) ≫ ya).app (op E) (𝟙 E) := by
      simpa using h1
    rw [hnat] at h2
    rw [← h2, hsE, Category.assoc]
  · have hc : yoneda.map (r ≫ t) ≫ x = yoneda.map r ≫ ya := by
      apply yonedaEquiv.injective
      have := hnat r
      simp only [yonedaEquiv_apply, FunctorToTypes.comp, yoneda_map_app, Category.comp_id] at this ⊢
      exact (this.trans hr).symm
    let l₀ : V ⟶ F := hx.rep.lift' (r ≫ t) r hc
    have h₁ : l₀ ≫ s = r ≫ t := hx.rep.lift'_fst _ _ _
    have h₂ : l₀ ≫ j = r := hx.rep.lift'_snd _ _ _
    have hle : RingHom.ker ((SCH).map i).appTop.hom ≤ RingHom.ker ((SCH).map l₀).appTop.hom := by
      have hkI : I ≤ RingHom.ker ((SCH).map l₀).appTop.hom := by
        refine Ideal.span_le.2 ?_
        rintro _ ⟨b, rfl⟩
        have e1 : (SCH).map l₀ ≫ (SCH).map s = (SCH).map l₀ ≫ (SCH).map (j ≫ t) := by
          rw [← Functor.map_comp, ← Functor.map_comp, h₁, ← Category.assoc, h₂]
        have e2 := congrArg (fun f => f.appTop.hom b) e1
        simp only [Scheme.Hom.comp_appTop] at e2
        simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, sub_eq_zero]
        exact e2
      intro y hy
      exact hkI (Chart.closedι_appTop_eq_zero I y hy)
    obtain ⟨φ, hφ⟩ := exists_ringHom_lift _ hsurj ((SCH).map l₀).appTop.hom hle
    have hfacS : toAffine (T := (SCH).obj V) (U := (SCH).obj E) φ ≫ (SCH).map i =
        (SCH).map l₀ := by
      refine toAffine_ext ?_
      rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, toAffine_appTop]
      exact hφ
    let l : V ⟶ E := siteHom (toAffine (T := (SCH).obj V) (U := (SCH).obj E) φ) (by
      rw [← site_w i, ← Category.assoc, hfacS, site_w])
    have hl : l ≫ i = l₀ := site_hom_ext (by rw [Functor.map_comp]; exact hfacS)
    exact ⟨l, by rw [← Category.assoc, hl, h₂]⟩

set_option maxHeartbeats 1600000 in
/-- **§1**, closed point: the stabilizer of a closed immersion `x : P → X` is closed in `D(M)_P`, with
no separatedness on `X`. Same statement as `exists_stab_ideal`. -/
theorem exists_stab_ideal_closedPoint (actX : AAction (fppfO B S hS) M X) (x : yoneda.obj P ⟶ X)
    (hx : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) (SCH))) x) :
    ∃ J : Ideal (R1 P M), ∀ {T : BigFppfOver B S hS} (t : T ⟶ P)
      (h : Multiplicative M →* Γ((SCH).obj T, ⊤)),
      actX.smul (U := op T) h (x.app (op T) t) = x.app (op T) t ↔
        ∀ f ∈ J, evalAt ((SCH).map t).appTop.hom h f = 0 := by
  haveI : IsAffine ((SCH).obj (Gk M P)) := inferInstance
  obtain ⟨E, ι, hc, heq, hfac⟩ := exists_equalizer_closedPoint x hx (Gπ M P)
    (actX.smul (U := op (Gk M P)) (univPt1 (U := P)) (x.app (op (Gk M P)) (Gπ M P)))
  have heq' : X.map ι.op (actX.smul (U := op (Gk M P)) (univPt1 (U := P))
      (x.app (op (Gk M P)) (Gπ M P))) = X.map ι.op (x.app (op (Gk M P)) (Gπ M P)) :=
    heq.trans (NatTrans.naturality_apply x ι.op (Gπ M P))
  have hfac' : ∀ {V : BigFppfOver B S hS} (r : V ⟶ Gk M P),
      X.map r.op (actX.smul (U := op (Gk M P)) (univPt1 (U := P)) (x.app (op (Gk M P)) (Gπ M P))) =
        X.map r.op (x.app (op (Gk M P)) (Gπ M P)) → ∃ l : V ⟶ E, l ≫ ι = r := fun r h =>
    hfac r (h.trans (NatTrans.naturality_apply x r.op (Gπ M P)).symm)
  have hE : IsAffine ((SCH).obj E) := isAffine_of_isAffineHom ((SCH).map ι)
  have hsurj : Function.Surjective ((SCH).map ι).appTop.hom :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine ((SCH).map ι)).2
  let J : Ideal (R1 P M) := (RingHom.ker ((SCH).map ι).appTop.hom).comap
    (spSec P (ι1 P (M := M)) contains1)
  refine ⟨J, ?_⟩
  intro T t h
  have hψ : (evalAt ((SCH).map t).appTop.hom h).comp (ι1 P (M := M)) = ((SCH).map t).appTop.hom :=
    RingHom.ext fun b => evalAt_ι _ _ b
  obtain ⟨τ, hτ₁, hτ₂⟩ := exists_spLift (R' := R1 P M) (ι1 P) contains1 t _ hψ
  have hres : secPt ((SCH).map τ).appTop.hom (univPt1 (U := P)) = h := MonoidHom.ext fun m => by
    refine (hτ₂ _).trans ?_
    refine (evalAt_single _ _ (Multiplicative.toAdd m) 1).trans ?_
    rw [map_one, one_mul]
    rfl
  have ea : X.map τ.op
      (actX.smul (U := op (Gk M P)) (univPt1 (U := P)) (x.app (op (Gk M P)) (Gπ M P))) =
      actX.smul (U := op T) h (x.app (op T) t) := by
    have := orbMap_app actX x τ
    rw [hres, hτ₁] at this
    exact this
  have eb : X.map τ.op (x.app (op (Gk M P)) (Gπ M P)) = x.app (op T) t := by
    rw [← hτ₁]
    exact (NatTrans.naturality_apply x τ.op (Gπ M P)).symm
  constructor
  · intro hfix f hf
    obtain ⟨l, hl⟩ := hfac' τ (ea.trans (hfix.trans eb.symm))
    rw [← hτ₂ f, ← hl, Functor.map_comp, Scheme.Hom.comp_appTop]
    change ((SCH).map l).appTop.hom (((SCH).map ι).appTop.hom _) = 0
    rw [show ((SCH).map ι).appTop.hom (spSec P (ι1 P (M := M)) contains1 f) = 0 from hf, map_zero]
  · intro hkill
    have hker : RingHom.ker ((SCH).map ι).appTop.hom ≤ RingHom.ker ((SCH).map τ).appTop.hom := by
      intro y hy
      obtain ⟨f, rfl⟩ := (spSec_bijective P (ι1 P (M := M)) contains1).2 y
      rw [RingHom.mem_ker, hτ₂]
      exact hkill f hy
    obtain ⟨φ, hφ⟩ := exists_ringHom_lift _ hsurj ((SCH).map τ).appTop.hom hker
    have hfacS : toAffine (T := (SCH).obj T) (U := (SCH).obj E) φ ≫ (SCH).map ι =
        (SCH).map τ := by
      refine toAffine_ext ?_
      rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, toAffine_appTop]
      exact hφ
    let l : T ⟶ E := siteHom (toAffine (T := (SCH).obj T) (U := (SCH).obj E) φ) (by
      rw [← site_w ι, ← Category.assoc, hfacS, site_w])
    have hl : l ≫ ι = τ := site_hom_ext (by rw [Functor.map_comp]; exact hfacS)
    have e2 := congrArg (X.map l.op) heq'
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply] at e2
    have hop : ι.op ≫ l.op = τ.op := by rw [← op_comp, hl]
    rw [hop] at e2
    exact ea.symm.trans (e2.trans eb)

end AlgMag.ChartPoint

#print axioms AlgMag.ChartPoint.exists_stab_ideal_closedPoint
