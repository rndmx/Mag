/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartQSLift

/-!
# Common étale chart for two points agreeing on thickenings

`X` an algebraic space, `W` affine, `p, q ∈ X(W)` agreeing on every `V(J^k)`. Around any `y ∈ V(J)`:
an étale `P → W`, `P` affine, an affine étale chart `V → X` and lifts `s, t : P → V` of `p, q` with
`s = t` on every `V(J^k Γ(P))`. No separatedness. Step 1 of the chart-lemma proof without separatedness.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.ChartQS

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

lemma mem_basicOpen_iff {Y : Scheme.{u}} [IsAffine Y] (y : Y) (r : Γ(Y, ⊤)) :
    y ∈ Y.basicOpen r ↔ r ∉ (Y.isoSpec.hom y).asIdeal := by
  have := congrArg (fun U : Y.Opens => y ∈ U) (Scheme.toSpecΓ_preimage_basicOpen Y r)
  exact (iff_of_eq this).symm

/-- A map killing `J^k`, on the site: `p, q` agree on it. -/
lemma agree_of_kill {W Z : BigFppfOver B S hS} [IsAffine ((SCH).obj W)] (J : Ideal Γ((SCH).obj W, ⊤))
    (p q : yoneda.obj W ⟶ X)
    (hV : yoneda.map (Chart.immι W (Chart.closedι ((SCH).obj W) J)) ≫ p =
      yoneda.map (Chart.immι W (Chart.closedι ((SCH).obj W) J)) ≫ q)
    (r : Z ⟶ W) (hr : ∀ x ∈ J, ((SCH).map r).appTop.hom x = 0) :
    yoneda.map r ≫ p = yoneda.map r ≫ q := by
  obtain ⟨c, hc⟩ := ChartMain.exists_factor_closed r J hr
  rw [← hc, yoneda.map_comp, Category.assoc, Category.assoc, hV]

/-- Range of `closedι`. -/
lemma closed_surj_iff {Y : Scheme.{u}} [IsAffine Y] (I : Ideal Γ(Y, ⊤)) (y : Y) :
    y ∈ Set.range (Chart.closedι Y I) ↔ I ≤ (Y.isoSpec.hom y).asIdeal := by
  have hhi : Y.isoSpec.inv (Y.isoSpec.hom y) = y := by
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]; rfl
  have hrg := range_comap_of_surjective _ (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  constructor
  · rintro ⟨z, rfl⟩
    have hhj : ∀ p : Spec Γ(Y, ⊤), Y.isoSpec.hom (Y.isoSpec.inv p) = p := fun p => by
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl
    intro i hi
    have h0 : Chart.closedι Y I z = Y.isoSpec.inv (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) z) := rfl
    rw [h0, hhj]
    have h00 : Ideal.Quotient.mk I i = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hi
    exact (show Ideal.Quotient.mk I i ∈ PrimeSpectrum.asIdeal (R := Γ(Y, ⊤) ⧸ I) z from
      h00 ▸ Ideal.zero_mem _)
  · intro h
    have hmem : Y.isoSpec.hom y ∈ PrimeSpectrum.zeroLocus (RingHom.ker (Ideal.Quotient.mk I) : Set _) := by
      intro i hi
      exact h (by simpa [Ideal.Quotient.eq_zero_iff_mem] using hi)
    rw [← hrg] at hmem
    obtain ⟨z, hz⟩ := hmem
    exact ⟨z, (congrArg (fun w => Y.isoSpec.inv w) hz).trans hhi⟩

/-- Pull an ideal along `r`, kill it. -/
lemma kill_map {Y Z E : Scheme.{u}} [IsAffine Y] (r : Y ⟶ Z) (c : E ⟶ Y) (J : Ideal Γ(Z, ⊤))
    (hc : ∀ x ∈ J.map r.appTop.hom, c.appTop.hom x = 0) (x : Γ(Z, ⊤)) (hx : x ∈ J) :
    (c ≫ r).appTop.hom x = 0 := by
  rw [Scheme.Hom.comp_appTop]
  exact hc _ (Ideal.mem_map_of_mem _ hx)

/-- Vanishing on an ideal map from vanishing on generators. -/
lemma kill_of_map {A D E : Type*} [CommRing A] [CommRing D] [CommRing E] (r : A →+* D) (c : D →+* E)
    (J : Ideal A) (h : ∀ x ∈ J, c (r x) = 0) : ∀ x ∈ J.map r, c x = 0 := by
  have : J.map r ≤ RingHom.ker c := Ideal.map_le_iff_le_comap.2 fun x hx => h x hx
  exact fun x hx => this hx

set_option maxHeartbeats 2000000 in
/-- **Common chart.** Step 1 of the chart-lemma proof without separatedness. -/
theorem exists_chart_agree (hX : IsAlgebraicSpace B S hS X) {W : BigFppfOver B S hS}
    [IsAffine ((SCH).obj W)] (J : Ideal Γ((SCH).obj W, ⊤)) (p q : yoneda.obj W ⟶ X)
    (hV : ∀ k : ℕ, yoneda.map (Chart.immι W (Chart.closedι ((SCH).obj W) (J ^ k))) ≫ p =
      yoneda.map (Chart.immι W (Chart.closedι ((SCH).obj W) (J ^ k))) ≫ q)
    (y : (SCH).obj W) (hy : ∀ r ∈ J, y ∉ ((SCH).obj W).basicOpen r) :
    ∃ (P V : BigFppfOver B S hS) (_ : IsAffine ((SCH).obj P)) (e : P ⟶ W) (v : yoneda.obj V ⟶ X)
      (hv : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) v) (s t : P ⟶ V),
      IsAffine ((SCH).obj V) ∧ Etale ((SCH).map e) ∧ y ∈ Set.range ((SCH).map e) ∧
      yoneda.map s ≫ v = yoneda.map e ≫ p ∧ yoneda.map t ≫ v = yoneda.map e ≫ q ∧
      ∀ k : ℕ, Chart.immι P (Chart.closedι ((SCH).obj P) ((J ^ k).map ((SCH).map e).appTop.hom)) ≫ s =
        Chart.immι P (Chart.closedι ((SCH).obj P) ((J ^ k).map ((SCH).map e).appTop.hom)) ≫ t := by
  have hV1 : yoneda.map (Chart.immι W (Chart.closedι ((SCH).obj W) J)) ≫ p =
      yoneda.map (Chart.immι W (Chart.closedι ((SCH).obj W) J)) ≫ q := by
    have : ∀ I : Ideal Γ((SCH).obj W, ⊤), J ^ 1 = I →
        yoneda.map (Chart.immι W (Chart.closedι ((SCH).obj W) I)) ≫ p =
        yoneda.map (Chart.immι W (Chart.closedι ((SCH).obj W) I)) ≫ q := by
      rintro _ rfl
      exact hV 1
    exact this J (pow_one J)
  obtain ⟨T₁, V, e₁, y₁, v, u₁, hVa, he₁, hy₁, hv, hu₁⟩ := ChartPoint.exists_affine_chart hX p y
  obtain ⟨O, hO, hmO, -⟩ := exists_isAffineOpen_mem_and_subset (x := y₁) (U := ⊤) trivial
  let T₀ := Space.openSiteObject B S hS T₁ O
  let j₀ : T₀ ⟶ T₁ := Space.openSiteObjectHom B S hS T₁ O
  haveI hT₀ : IsAffine ((SCH).obj T₀) := hO
  let y₀ : (SCH).obj T₀ := (⟨y₁, hmO⟩ : O)
  have hy₀ : (SCH).map j₀ y₀ = y₁ := rfl
  let e₀ : T₀ ⟶ W := j₀ ≫ e₁
  let u₀ : T₀ ⟶ V := j₀ ≫ u₁
  have hu₀ : yoneda.map u₀ ≫ v = yoneda.map e₀ ≫ p := by
    have h := ChartPoint.pb_of_app_eq (o := v) (t := p) hu₁
    simp only [u₀, e₀, yoneda.map_comp, Category.assoc, h]
  have hj₀E : Etale ((SCH).map j₀) := by
    change Etale O.ι
    infer_instance
  have he₀E : Etale ((SCH).map e₀) := by
    change Etale ((SCH).map (_ ≫ _))
    rw [Functor.map_comp]
    infer_instance
  let K₀ : Ideal Γ((SCH).obj T₀, ⊤) := J.map ((SCH).map e₀).appTop.hom
  let i₀ := Chart.immι T₀ (Chart.closedι ((SCH).obj T₀) K₀)
  let E₀ := Chart.immObj T₀ (Chart.closedι ((SCH).obj T₀) K₀)
  haveI hE₀a : IsAffine ((SCH).obj E₀) := by
    change IsAffine (Spec _)
    infer_instance
  have hKi₀ : ∀ x ∈ J, ((SCH).map (i₀ ≫ e₀)).appTop.hom x = 0 := by
    intro x hx
    rw [Functor.map_comp]
    exact kill_map _ _ _ (fun z hz => ChartMain.closedι_appTop_of_mem K₀ hz) x hx
  let q₀ : yoneda.obj T₀ ⟶ X := yoneda.map e₀ ≫ q
  let A := hv.rep.pullback q₀
  let toV : A ⟶ V := hv.rep.fst' q₀
  let sn : A ⟶ T₀ := hv.rep.snd q₀
  have hA : yoneda.map toV ≫ v = yoneda.map sn ≫ q₀ := (hv.rep.isPullback' q₀).w
  have hsnE : Etale ((SCH).map sn) := hv.property_snd q₀
  have hσc : yoneda.map (i₀ ≫ u₀) ≫ v = yoneda.map i₀ ≫ q₀ := by
    have := agree_of_kill J p q hV1 (i₀ ≫ e₀) hKi₀
    simp only [yoneda.map_comp, Category.assoc, hu₀, q₀] at this ⊢
    exact this
  let σ : E₀ ⟶ A := hv.rep.lift' (i₀ ≫ u₀) i₀ hσc
  have hσ₁ : σ ≫ toV = i₀ ≫ u₀ := hv.rep.lift'_fst _ _ _
  have hσ₂ : σ ≫ sn = i₀ := hv.rep.lift'_snd _ _ _
  -- the point
  have hrng : y₀ ∈ Set.range (Chart.closedι ((SCH).obj T₀) K₀) := by
    have hpr := closed_surj_iff (Y := (SCH).obj T₀) K₀ y₀
    refine hpr.2 fun r hr => ?_
    have hle : K₀ ≤ ((((SCH).obj T₀).isoSpec.hom y₀).asIdeal) := by
      refine Ideal.map_le_iff_le_comap.2 fun x hx => ?_
      by_contra hc
      have hm := (mem_basicOpen_iff y₀ (((SCH).map e₀).appTop.hom x)).2 hc
      have e' : ((SCH).obj T₀).basicOpen (((SCH).map e₀).appTop.hom x) =
          (SCH).map e₀ ⁻¹ᵁ ((SCH).obj W).basicOpen x := (Scheme.preimage_basicOpen _ x).symm
      rw [e'] at hm
      refine hy x hx ?_
      have : (SCH).map e₀ y₀ = y := by
        change (SCH).map (j₀ ≫ e₁) y₀ = y
        rw [Functor.map_comp, Scheme.Hom.comp_apply, hy₀, hy₁]
      rw [← this]
      exact hm
    exact hle hr
  obtain ⟨x₀, hx₀⟩ := hrng
  let a : (SCH).obj A := (SCH).map σ x₀
  obtain ⟨OA, hOA, hmA, -⟩ := exists_isAffineOpen_mem_and_subset (x := a) (U := ⊤) trivial
  let A₀ := Space.openSiteObject B S hS A OA
  let jA : A₀ ⟶ A := Space.openSiteObjectHom B S hS A OA
  haveI hA₀ : IsAffine ((SCH).obj A₀) := hOA
  have hjAE : Etale ((SCH).map jA) := by
    change Etale OA.ι
    infer_instance
  let O' : ((SCH).obj E₀).Opens := (SCH).map σ ⁻¹ᵁ OA
  let Eo := Space.openSiteObject B S hS E₀ O'
  let jE : Eo ⟶ E₀ := Space.openSiteObjectHom B S hS E₀ O'
  let σ' : Eo ⟶ A₀ := siteHom ((SCH).map σ ∣_ OA) (by
    have e0 := morphismRestrict_ι ((SCH).map σ) OA
    change ((SCH).map σ ∣_ OA) ≫ (OA.ι ≫ A.hom.hom) = O'.ι ≫ E₀.hom.hom
    rw [← Category.assoc, e0, Category.assoc, site_w])
  have hσ' : σ' ≫ jA = jE ≫ σ :=
    site_hom_ext (morphismRestrict_ι ((SCH).map σ) OA)
  let r₀ : A₀ ⟶ W := jA ≫ sn ≫ e₀
  have hr₀E : Etale ((SCH).map r₀) := by
    change Etale ((SCH).map (_ ≫ _ ≫ _))
    rw [Functor.map_comp, Functor.map_comp]
    infer_instance
  let s₀ : A₀ ⟶ V := jA ≫ sn ≫ u₀
  let t₀ : A₀ ⟶ V := jA ≫ toV
  have hs₀ : yoneda.map s₀ ≫ v = yoneda.map r₀ ≫ p := by
    simp only [s₀, r₀, yoneda.map_comp, Category.assoc, hu₀]
  have ht₀ : yoneda.map t₀ ≫ v = yoneda.map r₀ ≫ q := by
    simp only [t₀, r₀, yoneda.map_comp, Category.assoc, hA, q₀]
  let K : Ideal Γ((SCH).obj A₀, ⊤) := J.map ((SCH).map r₀).appTop.hom
  let c := Chart.closedι ((SCH).obj A₀) K
  let E := Chart.immObj A₀ c
  let i : E ⟶ A₀ := Chart.immι A₀ c
  have hKσ' : ∀ x ∈ K, ((SCH).map σ').appTop.hom x = 0 := by
    refine kill_of_map _ _ J fun x hx => ?_
    have e0 : σ' ≫ r₀ = jE ≫ i₀ ≫ e₀ := by
      simp only [r₀, ← Category.assoc, hσ']
      simp only [Category.assoc, ← hσ₂]
    have h1 := congrArg (fun f => ((SCH).map f).appTop.hom x) e0
    simp only [Functor.map_comp (SCH) σ' r₀, Scheme.Hom.comp_appTop] at h1
    refine h1.trans ?_
    have h2 := hKi₀ x hx
    rw [Functor.map_comp, Scheme.Hom.comp_appTop]
    change ((SCH).map jE).appTop.hom _ = 0
    exact (congrArg _ h2).trans (map_zero _)
  obtain ⟨φ, hφ⟩ := ChartMain.exists_factor_closed σ' K hKσ'
  have hc0 : yoneda.map (i ≫ s₀) ≫ v = yoneda.map (i ≫ t₀) ≫ v := by
    have := agree_of_kill J p q hV1 (i ≫ r₀) (by
      intro x hx
      rw [Functor.map_comp]
      exact kill_map _ _ _ (fun z hz => ChartMain.closedι_appTop_of_mem K hz) x hx)
    simp only [yoneda.map_comp, Category.assoc, hs₀, ht₀] at this ⊢
    exact this
  let d := hv.rep.lift' (𝟙 V) (𝟙 V) rfl
  let m := hv.rep.lift' (i ≫ s₀) (i ≫ t₀) hc0
  have hφm : φ ≫ m = (jE ≫ i₀ ≫ u₀) ≫ d := by
    refine hv.rep.hom_ext' ?_ ?_
    · simp only [m, d, Category.assoc, hv.rep.lift'_fst, Category.comp_id]
      change φ ≫ i ≫ s₀ = _
      rw [← Category.assoc, hφ]
      simp only [s₀, ← Category.assoc, hσ']
      simp only [Category.assoc]
      rw [← Category.assoc σ, hσ₂]
    · simp only [m, d, Category.assoc, hv.rep.lift'_snd, Category.comp_id]
      change φ ≫ i ≫ t₀ = _
      rw [← Category.assoc, hφ]
      simp only [t₀, ← Category.assoc, hσ']
      simp only [Category.assoc, hσ₁]
  haveI hdo := diag_open v hv
  let L : ((SCH).obj E).Opens := (SCH).map m ⁻¹ᵁ ((SCH).map d).opensRange
  let a₀ : (SCH).obj A₀ := (⟨a, hmA⟩ : OA)
  let x' : (SCH).obj Eo := (⟨x₀, hmA⟩ : O')
  have hLm : (SCH).map φ x' ∈ L := by
    change (SCH).map m ((SCH).map φ x') ∈ Set.range ((SCH).map d)
    have e' := congrArg (SCH).map hφm
    simp only [Functor.map_comp (SCH) φ m] at e'
    have e'' := congr($e' x')
    simp only [Scheme.Hom.comp_apply] at e''
    rw [e'', Functor.map_comp, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  let c' : (SCH).obj E ⟶ (SCH).obj A₀ := (SCH).map i
  haveI hc'cl : IsClosedImmersion c' := inferInstanceAs (IsClosedImmersion c)
  have hjAinj : Function.Injective ((SCH).map jA) := Subtype.val_injective
  have hca : c' ((SCH).map φ x') = a₀ := by
    apply hjAinj
    have e1 : φ ≫ i = σ' := hφ
    have e2 := congrArg (SCH).map e1
    rw [Functor.map_comp] at e2
    have e3 : c' ((SCH).map φ x') = (SCH).map σ' x' := by
      have := congr($e2 x')
      simpa only [Scheme.Hom.comp_apply] using this
    rw [e3]
    have e4 := congrArg (SCH).map hσ'
    simp only [Functor.map_comp] at e4
    have e5 := congr($e4 x')
    simp only [Scheme.Hom.comp_apply] at e5
    exact e5
  have hcinj : Function.Injective c' := c'.isClosedEmbedding.injective
  let C : Set ((SCH).obj A₀) := c' '' (L : Set _)ᶜ
  have hCc : IsClosed C := c'.isClosedEmbedding.isClosedMap _ L.isOpen.isClosed_compl
  have ha₀C : a₀ ∉ C := by
    rintro ⟨z, hz, hz'⟩
    exact hz (hcinj (hz'.trans hca.symm) ▸ hLm)
  obtain ⟨f, hf1, hf2⟩ := (isAffineOpen_top ((SCH).obj A₀)).exists_basicOpen_le
    (V := ⟨Cᶜ, hCc.isOpen_compl⟩) ⟨a₀, ha₀C⟩ trivial
  let D := ((SCH).obj A₀).basicOpen f
  let P := Chart.immObj A₀ D.ι
  let jP : P ⟶ A₀ := Chart.immι A₀ D.ι
  haveI hPa : IsAffine ((SCH).obj P) := (isAffineOpen_top ((SCH).obj A₀)).basicOpen f
  let e : P ⟶ W := jP ≫ r₀
  have heE : Etale ((SCH).map e) := by
    change Etale (D.ι ≫ (SCH).map r₀)
    infer_instance
  let s : P ⟶ V := jP ≫ s₀
  let t : P ⟶ V := jP ≫ t₀
  have hs : yoneda.map s ≫ v = yoneda.map e ≫ p := by
    simp only [s, e, yoneda.map_comp, Category.assoc, hs₀]
  have ht : yoneda.map t ≫ v = yoneda.map e ≫ q := by
    simp only [t, e, yoneda.map_comp, Category.assoc, ht₀]
  have hyr : y ∈ Set.range ((SCH).map e) := by
    refine ⟨(⟨a₀, hf2⟩ : D), ?_⟩
    change (SCH).map r₀ a₀ = y
    change (SCH).map (jA ≫ sn ≫ e₀) a₀ = y
    rw [Functor.map_comp, Functor.map_comp, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    change (SCH).map e₀ ((SCH).map sn a) = y
    have e6 : (SCH).map sn a = (SCH).map i₀ x₀ := by
      have := congrArg (SCH).map hσ₂
      rw [Functor.map_comp] at this
      have := congr($this x₀)
      exact this
    rw [e6]
    change (SCH).map e₀ (Chart.closedι ((SCH).obj T₀) K₀ x₀) = y
    rw [hx₀]
    change (SCH).map (j₀ ≫ e₁) y₀ = y
    rw [Functor.map_comp, Scheme.Hom.comp_apply, hy₀, hy₁]
  refine ⟨P, V, hPa, e, v, hv, s, t, hVa, heE, hyr, hs, ht, ?_⟩
  -- on `V(J)`
  let K1 : Ideal Γ((SCH).obj P, ⊤) := J.map ((SCH).map e).appTop.hom
  let i1 := Chart.immι P (Chart.closedι ((SCH).obj P) K1)
  have hKk : ∀ x ∈ K, ((SCH).map (i1 ≫ jP)).appTop.hom x = 0 := by
    refine kill_of_map _ _ J fun x hx => ?_
    have e7 : (SCH).map (i1 ≫ jP) ≫ (SCH).map r₀ = (SCH).map i1 ≫ (SCH).map e := by
      simp only [e, Functor.map_comp, Category.assoc]
    have h7 := congrArg (fun φ => φ.appTop.hom x) e7
    simp only [Scheme.Hom.comp_appTop] at h7
    refine h7.trans ?_
    exact ChartMain.closedι_appTop_of_mem K1 (Ideal.mem_map_of_mem _ hx)
  obtain ⟨ψ, hψ⟩ := ChartMain.exists_factor_closed (i1 ≫ jP) K hKk
  have hagree : ∀ (I : Ideal Γ((SCH).obj W, ⊤))
      (_ : yoneda.map (Chart.immι W (Chart.closedι ((SCH).obj W) I)) ≫ p =
        yoneda.map (Chart.immι W (Chart.closedι ((SCH).obj W) I)) ≫ q)
      {Z : BigFppfOver B S hS} (iz : Z ⟶ P)
      (_ : ∀ x ∈ I, ((SCH).map (iz ≫ e)).appTop.hom x = 0),
      yoneda.map (iz ≫ s) ≫ v = yoneda.map (iz ≫ t) ≫ v := by
    intro I hI Z iz hz
    have := agree_of_kill I p q hI (iz ≫ e) hz
    simp only [yoneda.map_comp, Category.assoc, hs, ht] at this ⊢
    exact this
  haveI hPa' : IsAffine P.left.obj := hPa
  have hkill : ∀ I : Ideal Γ((SCH).obj W, ⊤), ∀ x ∈ I,
      ((SCH).map (Chart.immι P (Chart.closedι ((SCH).obj P) (I.map ((SCH).map e).appTop.hom)) ≫ e)).appTop.hom x = 0 := by
    intro I x hx
    rw [Functor.map_comp]
    exact kill_map _ _ _ (fun z hz => ChartMain.closedι_appTop_of_mem _ hz) x hx
  have h1 : i1 ≫ s = i1 ≫ t := by
    have hc1 := hagree J hV1 i1 (hkill J)
    refine eq_of_range v hv _ _ hc1 fun z => ?_
    have e8 : hv.rep.lift' (i1 ≫ s) (i1 ≫ t) hc1 = ψ ≫ m := by
      refine hv.rep.hom_ext' ?_ ?_
      · rw [hv.rep.lift'_fst, Category.assoc, show m ≫ hv.rep.fst' v = i ≫ s₀ from hv.rep.lift'_fst _ _ _,
          ← Category.assoc ψ, show ψ ≫ i = i1 ≫ jP from hψ, Category.assoc]
      · rw [hv.rep.lift'_snd, Category.assoc, show m ≫ hv.rep.snd v = i ≫ t₀ from hv.rep.lift'_snd _ _ _,
          ← Category.assoc ψ, show ψ ≫ i = i1 ≫ jP from hψ, Category.assoc]
    rw [e8, Functor.map_comp, Scheme.Hom.comp_apply]
    by_contra hn
    have hnC : c' ((SCH).map ψ z) ∈ C := ⟨_, hn, rfl⟩
    have e9 : c' ((SCH).map ψ z) = (SCH).map (i1 ≫ jP) z := by
      have := congrArg (SCH).map hψ
      rw [Functor.map_comp] at this
      have := congr($this z)
      simpa only [Scheme.Hom.comp_apply] using this
    have hD : c' ((SCH).map ψ z) ∈ D := by
      rw [e9, Functor.map_comp, Scheme.Hom.comp_apply]
      exact ((((SCH).map i1 z : (SCH).obj P) : D)).2
    exact hf1 hD hnC
  intro k
  let ik := Chart.immι P (Chart.closedι ((SCH).obj P) ((J ^ k).map ((SCH).map e).appTop.hom))
  have hck := hagree (J ^ k) (hV k) ik (hkill (J ^ k))
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine eq_of_range v hv _ _ hck fun z => ?_
    exfalso
    have hle := (closed_surj_iff ((J ^ 0).map ((SCH).map e).appTop.hom)
      (Chart.closedι ((SCH).obj P) ((J ^ 0).map ((SCH).map e).appTop.hom) z)).1 (Set.mem_range_self z)
    have h11 : (1 : Γ((SCH).obj P, ⊤)) ∈ (J ^ 0).map ((SCH).map e).appTop.hom := by
      have h12 := Ideal.mem_map_of_mem ((SCH).map e).appTop.hom
        (show (1 : Γ((SCH).obj W, ⊤)) ∈ J ^ 0 by simp)
      rwa [map_one] at h12
    exact (((SCH).obj P).isoSpec.hom _).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hle h11))
  · have hJk : J ^ k ≤ J := Ideal.pow_le_self hk.ne'
    have hkl : ∀ x ∈ (J ^ k).map ((SCH).map e).appTop.hom, ((SCH).map i1).appTop.hom x = 0 :=
      fun x hx => ChartMain.closedι_appTop_of_mem K1 (Ideal.map_mono hJk hx)
    obtain ⟨g, hg⟩ := ChartMain.exists_factor_closed i1 _ hkl
    have hsurj : Function.Surjective ((SCH).map g) := by
      intro z
      have hle : K1 ≤ ((J ^ k).map ((SCH).map e).appTop.hom).radical := by
        refine Ideal.map_le_iff_le_comap.2 fun x hx => ?_
        exact ⟨k, by
          rw [← map_pow]
          exact Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow hx k)⟩
      obtain ⟨z1, hz1⟩ := closed_surj hle
        (Chart.closedι ((SCH).obj P) ((J ^ k).map ((SCH).map e).appTop.hom) z) (Set.mem_range_self z)
      refine ⟨z1, (Chart.closedι ((SCH).obj P) _).isClosedEmbedding.injective ?_⟩
      have := congrArg (SCH).map hg
      rw [Functor.map_comp] at this
      have := congr($this z1)
      simp only [Scheme.Hom.comp_apply] at this
      exact this.trans hz1
    refine eq_of_surj v hv g hsurj _ _ hck ?_
    have hg' : g ≫ ik = i1 := hg
    have e1 : g ≫ ik ≫ s = i1 ≫ s := by rw [← Category.assoc, hg']
    have e2 : g ≫ ik ≫ t = i1 ≫ t := by rw [← Category.assoc, hg']
    exact e1.trans (h1.trans e2.symm)

end AlgMag.ChartQS

#print axioms AlgMag.ChartQS.exists_chart_agree
