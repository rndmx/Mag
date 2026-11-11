/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartQSAgree
import AlgMag.ChartPointL11Local

/-!
# Two points agreeing on thickenings: tools, without separatedness

* `eq_of_surj`: two lifts to an étale chart, equal in `X`, equal after a map surjective on points, are equal.
* `exists_basicOpen_eq`: the locus of agreement on `V(K)` extends to a basic open of the ambient affine.
* `eq_of_family`: points of an algebraic space are determined on a jointly surjective family of open flat maps.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.ChartQS

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

section Chart

variable {V : BigFppfOver B S hS} (v : yoneda.obj V ⟶ X)
  (hv : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) v)

include hv in
/-- The diagonal of `V ×_X V`, for `V → X` étale, is an open immersion. -/
lemma diag_open :
    IsOpenImmersion ((SCH).map (hv.rep.lift' (𝟙 V) (𝟙 V) rfl)) := by
  haveI hπ₂ : Etale ((SCH).map (hv.rep.snd v)) := hv.property_snd v
  refine isOpenImmersion_section ((SCH).map (hv.rep.snd v)) _ ?_
  rw [← CategoryTheory.Functor.map_comp, hv.rep.lift'_snd, CategoryTheory.Functor.map_id]

/-- A map to `V ×_X V` whose two components coincide is through the diagonal. -/
lemma lift_self {Z : BigFppfOver B S hS} (a : Z ⟶ V) (hc : yoneda.map a ≫ v = yoneda.map a ≫ v) :
    hv.rep.lift' a a hc = a ≫ hv.rep.lift' (𝟙 V) (𝟙 V) rfl := by
  refine hv.rep.hom_ext' ?_ ?_
  · rw [hv.rep.lift'_fst, Category.assoc, hv.rep.lift'_fst, Category.comp_id]
  · rw [hv.rep.lift'_snd, Category.assoc, hv.rep.lift'_snd, Category.comp_id]

/-- A map into `V ×_X V` landing in the diagonal has equal components. -/
lemma eq_of_range {Z : BigFppfOver B S hS} (a b : Z ⟶ V) (hc : yoneda.map a ≫ v = yoneda.map b ≫ v)
    (hr : ∀ z : (SCH).obj Z, (SCH).map (hv.rep.lift' a b hc) z ∈
      Set.range ((SCH).map (hv.rep.lift' (𝟙 V) (𝟙 V) rfl))) : a = b := by
  haveI := diag_open v hv
  let d := hv.rep.lift' (𝟙 V) (𝟙 V) rfl
  let m := hv.rep.lift' a b hc
  let l : (SCH).obj Z ⟶ (SCH).obj V := IsOpenImmersion.lift ((SCH).map d) ((SCH).map m) (by
    rintro _ ⟨z, rfl⟩
    exact hr z)
  have hl : l ≫ (SCH).map d = (SCH).map m := IsOpenImmersion.lift_fac _ _ _
  have h₁ : (SCH).map a = l := by
    have e : (SCH).map (m ≫ hv.rep.fst' v) = (SCH).map a := congrArg _ (hv.rep.lift'_fst _ _ _)
    rw [← e, Functor.map_comp, ← hl, Category.assoc, ← Functor.map_comp,
      show d ≫ hv.rep.fst' v = 𝟙 V from hv.rep.lift'_fst _ _ _, CategoryTheory.Functor.map_id, Category.comp_id]
  have h₂ : (SCH).map b = l := by
    have e : (SCH).map (m ≫ hv.rep.snd v) = (SCH).map b := congrArg _ (hv.rep.lift'_snd _ _ _)
    rw [← e, Functor.map_comp, ← hl, Category.assoc, ← Functor.map_comp,
      show d ≫ hv.rep.snd v = 𝟙 V from hv.rep.lift'_snd _ _ _, CategoryTheory.Functor.map_id, Category.comp_id]
  exact ChartMain.siteExt (h₁.trans h₂.symm)

include hv in
/-- Equal in `X`, and equal after a map surjective on points: equal. -/
theorem eq_of_surj {Z Z' : BigFppfOver B S hS} (f : Z' ⟶ Z) (hf : Function.Surjective ((SCH).map f))
    (a b : Z ⟶ V) (hc : yoneda.map a ≫ v = yoneda.map b ≫ v) (h : f ≫ a = f ≫ b) : a = b := by
  refine eq_of_range v hv a b hc fun z => ?_
  obtain ⟨z', rfl⟩ := hf z
  have e : f ≫ hv.rep.lift' a b hc = (f ≫ a) ≫ hv.rep.lift' (𝟙 V) (𝟙 V) rfl := by
    refine hv.rep.hom_ext' ?_ ?_
    · simp only [Category.assoc, hv.rep.lift'_fst, Category.comp_id]
    · simp only [Category.assoc, hv.rep.lift'_snd, Category.comp_id, h]
  have e' := congrArg (SCH).map e
  simp only [Functor.map_comp] at e'
  have e'' := congr($e' z')
  simp only [Scheme.Hom.comp_apply] at e''
  rw [e'']
  exact ⟨_, rfl⟩

end Chart

/-- `closedι` is surjective onto `V(K')` from `V(K)` when `K' ≤ K ≤ rad K'`. -/
lemma closed_surj {Y : Scheme.{u}} [IsAffine Y] {K K' : Ideal Γ(Y, ⊤)} (hle : K ≤ K'.radical)
    (y : Y) (hy : y ∈ Set.range (Chart.closedι Y K')) : y ∈ Set.range (Chart.closedι Y K) := by
  have hr : ∀ I : Ideal Γ(Y, ⊤), y ∈ Set.range (Chart.closedι Y I) ↔ I ≤ (Y.isoSpec.hom y).asIdeal := by
    intro I
    have hhi : Y.isoSpec.inv (Y.isoSpec.hom y) = y := by
      rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]; rfl
    have hhj : ∀ p : Spec Γ(Y, ⊤), Y.isoSpec.hom (Y.isoSpec.inv p) = p := fun p => by
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl
    have hrg := range_comap_of_surjective _ (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    constructor
    · rintro ⟨z, rfl⟩
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
      refine ⟨z, ?_⟩
      exact (congrArg (fun w => Y.isoSpec.inv w) hz).trans hhi
  rw [hr] at hy ⊢
  intro i hi
  have := hle hi
  exact (Y.isoSpec.hom y).isPrime.isRadical.radical_le_iff.2 hy this

/-- Points of an algebraic space are determined on a family of open flat maps, jointly surjective. -/
theorem eq_of_family (hX : IsAlgebraicSpace B S hS X) {W : BigFppfOver B S hS} {ι : Type u}
    (Z : ι → BigFppfOver B S hS) (e : ∀ i, Z i ⟶ W) (hf : ∀ i, Flat ((SCH).map (e i)))
    (ho : ∀ i, IsOpenMap ((SCH).map (e i)))
    (hcov : ∀ y : (SCH).obj W, ∃ i, y ∈ Set.range ((SCH).map (e i)))
    (p q : X.obj (op W)) (h : ∀ i, X.map (e i).op p = X.map (e i).op q) : p = q := by
  have hsh := IsAlgebraicSpace.isSheaf_fpqc hX
  rw [isSheaf_iff_isSheaf_of_type,
    Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange] at hsh
  let 𝒰 : ((SCH).obj W).Cover (Scheme.precoverage @Flat) :=
    Scheme.Cover.mkOfCovers ι (fun i => (SCH).obj (Z i)) (fun i => (SCH).map (e i)) hcov hf
  have := Scheme.jointlySurjective_precoverage_flat
  have hqc : QuasiCompactCover 𝒰.toPreZeroHypercover := QuasiCompactCover.of_isOpenMap ho
  have hc : Presieve.ofArrows (fun i => (SCH).obj (Z i)) (fun i => (SCH).map (e i)) ∈
      Scheme.fpqcPrecoverage ((SCH).obj W) :=
    ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.2 hqc,
      (Scheme.ofArrows_mem_precoverage_iff _).2 ⟨hcov, hf⟩⟩
  have hR : Presieve.ofArrows Z e ∈ Scheme.fpqcPrecoverage.comap (SCH) W := by
    rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows]
    exact hc
  have hF := (Presieve.isSheafFor_arrows_iff X e).1 (hsh _ hR)
  obtain ⟨_, _, hu⟩ := hF (fun i => X.map (e i).op p) (fun i j W' g₁ g₂ hg => by
    simp only [← Functor.map_comp_apply, ← op_comp, hg])
  exact (hu p fun _ => rfl).trans (hu q fun i => (h i).symm).symm

end AlgMag.ChartQS

#print axioms AlgMag.ChartQS.eq_of_surj
#print axioms AlgMag.ChartQS.eq_of_family
