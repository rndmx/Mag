/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartQSLocalModel
import StacksFrontier.AlgebraicGeometry.Etale.LiftAcrossClosedImmersion

/-!
# The flat model `Y` from a chart of `V(b)`

For `LocalModelStep`: `E → V(b)` is an affine étale chart of `ψ₁`
(`DeligneQS.ChartOf`, one affine `E`, so no finite families are needed). Stacks 057R lifts it to an étale `X' → T`,
`L = Γ(X')` with `1 + I` inverted: `I` is in the Jacobson radical of `L`, and `L` still covers `V(b)`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Space

open Cardinal in
/-- A finite type algebra has no more elements than `max ℵ₀ #C`. -/
lemma AlgMag.ChartMain.DeligneQS.ChartQSLocal.card_finiteType.{v} {C R : Type v} [CommRing C] [CommRing R]
    [Algebra C R] [Algebra.FiniteType C R] : #R ≤ max ℵ₀ #C := by
  obtain ⟨s, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial.1 (inferInstance : Algebra.FiniteType C R)
  refine (Cardinal.mk_le_of_surjective hf).trans (MvPolynomial.cardinalMk_le_max.trans ?_)
  have h : #{x // x ∈ s} ≤ ℵ₀ := (Cardinal.lt_aleph0_of_finite _).le
  exact max_le (max_le (le_max_right _ _) (h.trans (le_max_left _ _))) (le_max_left _ _)

universe u

namespace AlgMag.ChartMain.DeligneQS.ChartQSLocal

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

variable {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)]

set_option maxHeartbeats 8000000 in
/-- **The flat model**: for a chart of `ψ₁`. -/
theorem exists_model [IsAffine S] {V : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] {φ : yoneda.obj V ⟶ X}
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
    (I b : Ideal Γ((SCH).obj T, ⊤)) [IsAdicComplete I Γ((SCH).obj T, ⊤)]
    (ψ : ∀ l : ℕ, X.obj (op (Vc T (b ^ l))))
    (hψ : ∀ (n k : ℕ) (e : Vc T (b ^ n) ⟶ Vc T (b ^ k)), e ≫ ιc T (b ^ k) = ιc T (b ^ n) →
      X.map e.op (ψ k) = ψ n)
    (P : ChartOf φ (ψ (0 + 1))) :
    ∃ (Y : BigFppfOver B S hS) (p : Y ⟶ T) (θ : X.obj (op Y)),
      IsAffine ((SCH).obj Y) ∧ IsNoetherianRing Γ((SCH).obj Y, ⊤) ∧ Flat ((SCH).map p) ∧
      (∀ y : (SCH).obj T, (∀ g ∈ b, y ∉ ((SCH).obj T).basicOpen g) → y ∈ Set.range ((SCH).map p)) ∧
      I.map (sec p) ≤ Ideal.jacobson ⊥ ∧ b.map (sec p) ≤ Ideal.jacobson ⊥ ∧
      ∀ (l : ℕ) ⦃W : BigFppfOver B S hS⦄ (i : W ⟶ Y) (s : W ⟶ Vc T (b ^ l)),
        s ≫ ιc T (b ^ l) = i ≫ p → X.map i.op θ = X.map s.op (ψ l) := by
  let Z := Vc T (b ^ (0 + 1))
  let ιZ : Z ⟶ T := ιc T (b ^ (0 + 1))
  haveI hEa := P.affine
  haveI hcl : IsClosedImmersion ((SCH).map ιZ) :=
    inferInstanceAs (IsClosedImmersion (Chart.closedι ((SCH).obj T) (b ^ (0 + 1))))
  haveI hpE : Etale ((SCH).map P.e₁) :=
    (HasRingHomProperty.iff_of_isAffine (P := @Etale)).2 P.etale
  obtain ⟨X', f, hX', hf, e, hee⟩ := Stacks.Etale.exists_etale_lift_of_isClosedImmersion
    ((SCH).map ιZ) ((SCH).map P.e₁)
  haveI := hX'
  haveI := hf
  let R : Type u := Γ(X', ⊤)
  let fr : Γ((SCH).obj T, ⊤) →+* R := f.appTop.hom
  let I' : Ideal R := I.map fr
  let L : Type u := Localization (ChartQSAlg.oneSub I')
  let loc : R →+* L := algebraMap R L
  let ρ : Γ((SCH).obj T, ⊤) →+* L := loc.comp fr
  have hft : fr.FiniteType :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).1 inferInstance
  letI := fr.toAlgebra
  haveI : Algebra.FiniteType Γ((SCH).obj T, ⊤) R := hft
  haveI hNR : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing Γ((SCH).obj T, ⊤) R
  haveI hNL : IsNoetherianRing L := IsLocalization.isNoetherianRing (ChartQSAlg.oneSub I') L inferInstance
  have hC : B.Contains (Spec (.of L)) := by
    refine Scheme.size_Spec_lt_of_mk_le B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit _ (contains_RT T) ?_
    rw [Scheme.size_Spec]
    have h1 : Cardinal.mk L ≤ Cardinal.mk R := IsLocalization.cardinalMk_le (ChartQSAlg.oneSub I')
    have h2 : Cardinal.mk R ≤ max Cardinal.aleph0 (Cardinal.mk Γ((SCH).obj T, ⊤)) := card_finiteType
    refine h1.trans (h2.trans ?_)
    exact Cardinal.self_le_power _ Cardinal.one_le_aleph0
  let q0 : (SCH).obj (spObj T ρ hC) ⟶ X' := Spec.map (CommRingCat.ofHom loc) ≫ X'.isoSpec.inv
  have hq0 : q0 ≫ f = (SCH).map (spToT T ρ hC) := by
    have hn := Scheme.isoSpec_inv_naturality f
    have hρ : CommRingCat.ofHom ρ = f.appTop ≫ CommRingCat.ofHom loc := rfl
    have e : Spec.map (CommRingCat.ofHom ρ) ≫ ((SCH).obj T).isoSpec.inv =
        Spec.map (CommRingCat.ofHom loc) ≫ X'.isoSpec.inv ≫ f := by
      rw [hρ, Spec.map_comp, Category.assoc, hn]
    exact (Category.assoc _ _ _).trans e.symm
  have hflat : Flat ((SCH).map (spToT T ρ hC)) := by
    rw [← hq0]
    haveI : Flat (Spec.map (CommRingCat.ofHom loc)) :=
      Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 (IsLocalization.flat L (ChartQSAlg.oneSub I')))
    change Flat ((Spec.map (CommRingCat.ofHom loc) ≫ X'.isoSpec.inv) ≫ f)
    infer_instance
  have hJL := ChartQSAlg.map_le_jacobson_localization (L := L) I'
  refine exists_model_of_ring he I b ψ hψ L ρ hC hflat
    (fun c hc => hJL (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hc))) ?_ ?_
    (IsAdicComplete.le_jacobson_bot I)
  · -- the chart on `V(bL)`
    intro W u s hs
    have hcomm : (SCH).map s ≫ (SCH).map ιZ = ((SCH).map u ≫ q0) ≫ f := by
      rw [Category.assoc, hq0, ← Functor.map_comp, ← Functor.map_comp, hs]
    let g₂ := pullback.lift ((SCH).map s) ((SCH).map u ≫ q0) hcomm
    let g₃ : (SCH).obj W ⟶ (SCH).obj P.E := g₂ ≫ e.inv
    have hg₃ : g₃ ≫ (SCH).map P.e₁ = (SCH).map s := by
      have h1 : e.inv ≫ (SCH).map P.e₁ = pullback.fst _ _ := by
        rw [Iso.inv_comp_eq, hee]
      simp only [g₃, Category.assoc, h1]
      exact pullback.lift_fst _ _ _
    have hw : g₃ ≫ P.E.hom.hom = W.hom.hom := by
      rw [← site_w P.e₁, ← Category.assoc, hg₃, site_w]
    let gs : W ⟶ P.E := siteHom g₃ hw
    have hgs : gs ≫ P.e₁ = s := (SCH).map_injective (by
      rw [Functor.map_comp]
      exact hg₃)
    refine ⟨gs ≫ P.e₂, ?_⟩
    rw [map_yoneda_app (φ := φ) gs P.e₂, P.w, ← Functor.map_comp_apply, ← op_comp, hgs]
  · -- the cover
    intro m hm hbm hIm
    haveI hmp : m.IsPrime := hm.isPrime
    have hker : RingHom.ker (sec ιZ) ≤ m := fun c hc => by
      have : c ∈ b ^ (0 + 1) := (ιc_ker _ c).1 hc
      rw [zero_add, pow_one] at this
      exact hbm this
    let n₀ : Ideal Γ((SCH).obj Z, ⊤) := m.map (sec ιZ)
    haveI hn₀ : n₀.IsPrime := Ideal.map_isPrime_of_surjective (ιc_surj _) hker
    have hn₀c : n₀.comap (sec ιZ) = m := by
      rw [Ideal.comap_map_of_surjective _ (ιc_surj _), ← RingHom.ker_eq_comap_bot, sup_eq_left]
      exact hker
    let x₀ : (SCH).obj Z := ((SCH).obj Z).isoSpec.inv ⟨n₀, hn₀⟩
    have hx₀ : ((SCH).obj Z).isoSpec.hom x₀ = ⟨n₀, hn₀⟩ := by
      change (((SCH).obj Z).isoSpec.inv ≫ ((SCH).obj Z).isoSpec.hom) _ = _
      rw [Iso.inv_hom_id]
      rfl
    obtain ⟨z, hz⟩ := P.surj.surj x₀
    let Qe : Ideal Γ((SCH).obj P.E, ⊤) := (((SCH).obj P.E).isoSpec.hom z).asIdeal
    haveI hQe : Qe.IsPrime := (((SCH).obj P.E).isoSpec.hom z).2
    have hQe₁ : Qe.comap (sec P.e₁) = n₀ := by
      rw [← prime_comap ((SCH).map P.e₁) z, hz, hx₀]
    let σ : (SCH).obj P.E ⟶ X' := e.hom ≫ pullback.snd _ _
    have hσ : σ ≫ f = (SCH).map P.e₁ ≫ (SCH).map ιZ := by
      simp only [σ, Category.assoc]
      rw [← pullback.condition, ← Category.assoc, hee]
    let QR : Ideal R := Qe.comap σ.appTop.hom
    haveI hQR : QR.IsPrime := Ideal.comap_isPrime _ _
    have hQRc : QR.comap fr = m := by
      rw [← hn₀c, ← hQe₁, Ideal.comap_comap, Ideal.comap_comap]
      congr 1
      have := congrArg (fun z => z.appTop.hom) hσ
      simp only [Scheme.Hom.comp_appTop] at this
      exact this
    have hI'Q : I' ≤ QR := Ideal.map_le_iff_le_comap.2 (hQRc ▸ hIm)
    have hdisj : Disjoint ((ChartQSAlg.oneSub I') : Set R) (QR : Set R) := by
      rw [Set.disjoint_left]
      rintro _ ⟨r, hr, rfl⟩ hx
      have : (1 : R) ∈ QR := by
        have h := QR.add_mem hx (hI'Q hr)
        simpa using h
      exact hQR.ne_top ((Ideal.eq_top_iff_one _).2 this)
    let Q : Ideal L := QR.map loc
    have hQp : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (ChartQSAlg.oneSub I') L QR hQR hdisj
    have hQc : Q.comap loc = QR :=
      IsLocalization.comap_map_of_isPrime_disjoint (ChartQSAlg.oneSub I') L hQR hdisj
    refine ⟨Q, hQp, Ideal.map_le_iff_le_comap.2 fun g hg => ?_, ?_⟩
    · have : fr g ∈ QR := by
        change g ∈ QR.comap fr
        rw [hQRc]
        exact hbm hg
      exact Ideal.mem_map_of_mem _ this
    · change (Q.comap loc).comap fr = m
      rw [hQc, hQRc]

end AlgMag.ChartMain.DeligneQS.ChartQSLocal
