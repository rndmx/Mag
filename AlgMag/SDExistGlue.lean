/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SpacesDescentScheme
import AlgMag.SDExistBaseChange
import StacksFrontier.AlgebraicGeometry.Descent.IndQuasiAffineFpqcSheaf

/-!
# Lemma D, Step 4: gluing

Step 4 of the proof of Props. 3.31 (ii),
3.32 (ii) of `Algebraic Magnetism`. Existence for `ℤ^r`-gradings follows from local factorizations on an étale cover.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct

universe u

namespace AlgMag.SD

open AlgMag AlgMag.SQ

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Step 2 of the note for a graded ring (peer result `AlgMag.SD.SDUnique_uniq_coact`, stated here as a hypothesis). -/
def SDExist_UniqCoact (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∀ {A A₀ Γ : Type u} [CommRing A] [CommRing A₀] [AddCommGroup Γ] [UniqueSums Γ]
    {c : Coact A Γ} {ι : A₀ →+* A} (_ : c.IsInv ι) {W Q : BigFppfOver B S hS} (π : W ⟶ Q)
    (i : (SCH).obj W ≅ Spec (.of A)) (i₀ : (SCH).obj Q ≅ Spec (.of A₀))
    (_ : (SCH).map π ≫ i₀.hom = i.hom ≫ sp ι)
    (x y : X.obj (op Q)), X.map π.op x = X.map π.op y → x = y

/-- Uniqueness over `W ×_Q V → V` for `V` affine: Step 2 of the note for the base change `A₀ → O(V)`. -/
theorem SDExist_uniq_bc (hU : SDExist_UniqCoact X)
    {A A₀ Γ : Type u} [CommRing A] [CommRing A₀] [AddCommGroup Γ] [UniqueSums Γ]
    {c : Coact A Γ} {ι : A₀ →+* A} (hι : c.IsInv ι) {W Q V : BigFppfOver B S hS} (π : W ⟶ Q) (g : V ⟶ Q)
    [IsAffine ((SCH).obj V)]
    (i : (SCH).obj W ≅ Spec (.of A)) (i₀ : (SCH).obj Q ≅ Spec (.of A₀))
    (hπ : (SCH).map π ≫ i₀.hom = i.hom ≫ sp ι)
    (y y' : X.obj (op V)) (h : X.map (pullback.snd π g).op y = X.map (pullback.snd π g).op y') : y = y' := by
  let R' : Type u := Γ((SCH).obj V, ⊤)
  let iV : (SCH).obj V ≅ Spec (.of R') := ((SCH).obj V).isoSpec
  let ρ : A₀ →+* R' := (Spec.preimage (iV.inv ≫ (SCH).map g ≫ i₀.hom)).hom
  have hρ : sp ρ = iV.inv ≫ (SCH).map g ≫ i₀.hom := by
    change Spec.map (CommRingCat.ofHom ρ) = _
    simp [ρ]
  letI : Algebra A₀ A := ι.toAlgebra
  letI : Algebra A₀ R' := ρ.toAlgebra
  have hc : ∀ r : A₀, c.σ (algebraMap A₀ A r) = AddMonoidAlgebra.single 0 (algebraMap A₀ A r) :=
    fun r => (hι.range _).2 ⟨r, rfl⟩
  have hι' := SDExist_bc_isInv R' c hc hι
  have hpb : IsPullback (sp (Algebra.TensorProduct.includeLeftRingHom : R' →+* R' ⊗[A₀] A))
      (sp (Algebra.TensorProduct.includeRight : A →ₐ[A₀] R' ⊗[A₀] A).toRingHom) (sp ρ) (sp ι) :=
    isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A₀ R' A)
  have hsite : IsPullback ((SCH).map (pullback.snd π g)) ((SCH).map (pullback.fst π g)) ((SCH).map g) ((SCH).map π) :=
    ((IsPullback.of_hasPullback π g).map (SCH)).flip
  have hsite2 : IsPullback ((SCH).map (pullback.snd π g) ≫ iV.hom) ((SCH).map (pullback.fst π g) ≫ i.hom)
      (sp ρ) (sp ι) := by
    refine IsPullback.of_iso hsite (Iso.refl _) iV i i₀ (by simp) (by simp) ?_ hπ
    rw [hρ]
    simp
  let j := hsite2.isoIsPullback _ _ hpb
  have hj : (SCH).map (pullback.snd π g) ≫ iV.hom =
      j.hom ≫ sp (Algebra.TensorProduct.includeLeftRingHom : R' →+* R' ⊗[A₀] A) :=
    (hsite2.isoIsPullback_hom_fst _ _ hpb).symm
  exact hU hι' (pullback.snd π g) j iV hj y y' h

/-- Points of an algebraic space glue along a family of open flat maps, jointly surjective. -/
theorem SDExist_glue (hX : IsAlgebraicSpace B S hS X) {Q : BigFppfOver B S hS} {I : Type u}
    (V : I → BigFppfOver B S hS) (e : ∀ i, V i ⟶ Q) (hf : ∀ i, Flat ((SCH).map (e i)))
    (ho : ∀ i, IsOpenMap ((SCH).map (e i)))
    (hcov : ∀ y : (SCH).obj Q, ∃ i, y ∈ Set.range ((SCH).map (e i)))
    (y : ∀ i, X.obj (op (V i)))
    (hy : ∀ i j, X.map (pullback.fst (e i) (e j)).op (y i) = X.map (pullback.snd (e i) (e j)).op (y j)) :
    ∃ y₀ : X.obj (op Q), ∀ i, X.map (e i).op y₀ = y i := by
  have hsh := IsAlgebraicSpace.isSheaf_fpqc hX
  rw [isSheaf_iff_isSheaf_of_type,
    Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange] at hsh
  let 𝒰 : ((SCH).obj Q).Cover (Scheme.precoverage @Flat) :=
    Scheme.Cover.mkOfCovers I (fun i => (SCH).obj (V i)) (fun i => (SCH).map (e i)) hcov hf
  have := Scheme.jointlySurjective_precoverage_flat
  have hqc : QuasiCompactCover 𝒰.toPreZeroHypercover := QuasiCompactCover.of_isOpenMap ho
  have hc : Presieve.ofArrows (fun i => (SCH).obj (V i)) (fun i => (SCH).map (e i)) ∈
      Scheme.fpqcPrecoverage ((SCH).obj Q) :=
    ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.2 hqc,
      (Scheme.ofArrows_mem_precoverage_iff _).2 ⟨hcov, hf⟩⟩
  have hR : Presieve.ofArrows V e ∈ Scheme.fpqcPrecoverage.comap (SCH) Q := by
    rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows]
    exact hc
  have hF := (Presieve.isSheafFor_arrows_iff X e).1 (hsh _ hR)
  obtain ⟨y₀, h₀, -⟩ := hF y (fun i j W' g₁ g₂ hg => by
    obtain ⟨l, rfl, rfl⟩ : ∃ l : W' ⟶ pullback (e i) (e j), l ≫ pullback.fst (e i) (e j) = g₁ ∧
        l ≫ pullback.snd (e i) (e j) = g₂ :=
      ⟨pullback.lift g₁ g₂ hg, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    rw [op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hy])
  exact ⟨y₀, h₀⟩

/-- Separatedness for a family of open flat maps, jointly surjective. -/
theorem SDExist_eq_of_family (hX : IsAlgebraicSpace B S hS X) {W : BigFppfOver B S hS} {I : Type u}
    (Z : I → BigFppfOver B S hS) (e : ∀ i, Z i ⟶ W) (hf : ∀ i, Flat ((SCH).map (e i)))
    (ho : ∀ i, IsOpenMap ((SCH).map (e i)))
    (hcov : ∀ y : (SCH).obj W, ∃ i, y ∈ Set.range ((SCH).map (e i)))
    (p q : X.obj (op W)) (h : ∀ i, X.map (e i).op p = X.map (e i).op q) : p = q := by
  have hsh := IsAlgebraicSpace.isSheaf_fpqc hX
  rw [isSheaf_iff_isSheaf_of_type,
    Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange] at hsh
  let 𝒰 : ((SCH).obj W).Cover (Scheme.precoverage @Flat) :=
    Scheme.Cover.mkOfCovers I (fun i => (SCH).obj (Z i)) (fun i => (SCH).map (e i)) hcov hf
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

/-- **Step 4**, the gluing: `π : W → Q` a map of affine objects of the site, the spectrum of the inclusion of the
invariants of a grading by `Γ`. A point `x` of `X` over `W` which, near each point of `Q`, for the étale topology,
comes from `Q`, comes from `Q`. -/
theorem SDExist_desc_of_local (hX : IsAlgebraicSpace B S hS X) (hU : SDExist_UniqCoact X)
    {A A₀ Γ : Type u} [CommRing A] [CommRing A₀] [AddCommGroup Γ] [UniqueSums Γ]
    {c : Coact A Γ} {ι : A₀ →+* A} (hι : c.IsInv ι) {W Q : BigFppfOver B S hS} (π : W ⟶ Q)
    (i : (SCH).obj W ≅ Spec (.of A)) (i₀ : (SCH).obj Q ≅ Spec (.of A₀))
    (hπ : (SCH).map π ≫ i₀.hom = i.hom ≫ sp ι) (x : X.obj (op W))
    (hloc : ∀ q : (SCH).obj Q, ∃ (V : BigFppfOver B S hS) (_ : IsAffine ((SCH).obj V)) (e : V ⟶ Q),
      Etale ((SCH).map e) ∧ q ∈ Set.range ((SCH).map e) ∧
      ∃ y : X.obj (op V), X.map (pullback.snd π e).op y = X.map (pullback.fst π e).op x) :
    ∃ x₀ : X.obj (op Q), X.map π.op x₀ = x := by
  haveI : IsAffine ((SCH).obj Q) := IsAffine.of_isIso i₀.hom
  choose V hV e hE hq y hy using hloc
  have hfl : ∀ a, Flat ((SCH).map (e a)) := fun a => by have := hE a; infer_instance
  have hop : ∀ a, IsOpenMap ((SCH).map (e a)) := fun a => by have := hE a; exact ((SCH).map (e a)).isOpenMap
  obtain ⟨x₀, hx₀⟩ := SDExist_glue hX V e hfl hop (fun a => ⟨a, hq a⟩) y (fun a b => by
    let g := pullback.fst (e a) (e b) ≫ e a
    have hpb : IsPullback ((SCH).map (pullback.fst (e a) (e b))) ((SCH).map (pullback.snd (e a) (e b)))
        ((SCH).map (e a)) ((SCH).map (e b)) := (IsPullback.of_hasPullback (e a) (e b)).map (SCH)
    haveI : IsAffine ((SCH).obj (pullback (e a) (e b))) := by
      haveI := hV a
      haveI := hV b
      exact IsAffine.of_isIso hpb.isoPullback.hom
    refine SDExist_uniq_bc hU hι π g i i₀ hπ _ _ ?_
    have w1 : pullback.fst π g ≫ π = (pullback.snd π g ≫ pullback.fst (e a) (e b)) ≫ e a := by
      rw [pullback.condition, Category.assoc]
    have w2 : pullback.fst π g ≫ π = (pullback.snd π g ≫ pullback.snd (e a) (e b)) ≫ e b := by
      rw [pullback.condition, Category.assoc]
      exact congrArg _ pullback.condition
    have h1 := congrArg (X.map (pullback.lift _ _ w1).op) (hy a)
    have h2 := congrArg (X.map (pullback.lift _ _ w2).op) (hy b)
    simp only [← Functor.map_comp_apply, ← op_comp, pullback.lift_fst, pullback.lift_snd] at h1 h2
    simp only [← Functor.map_comp_apply, ← op_comp]
    exact h1.trans h2.symm)
  refine ⟨x₀, SDExist_eq_of_family hX (fun a => pullback π (e a)) (fun a => pullback.fst π (e a)) ?_ ?_ ?_ _ _ ?_⟩
  · intro a
    have hp : IsPullback ((SCH).map (pullback.fst π (e a))) ((SCH).map (pullback.snd π (e a)))
        ((SCH).map π) ((SCH).map (e a)) := (IsPullback.of_hasPullback π (e a)).map (SCH)
    exact MorphismProperty.of_isPullback hp.flip (hfl a)
  · intro a
    have hp : IsPullback ((SCH).map (pullback.fst π (e a))) ((SCH).map (pullback.snd π (e a)))
        ((SCH).map π) ((SCH).map (e a)) := (IsPullback.of_hasPullback π (e a)).map (SCH)
    have : Etale ((SCH).map (pullback.fst π (e a))) := by
      have := hE a
      exact MorphismProperty.of_isPullback hp.flip this
    exact ((SCH).map (pullback.fst π (e a))).isOpenMap
  · intro w
    obtain ⟨v, hv⟩ := hq ((SCH).map π w)
    have hp : IsPullback ((SCH).map (pullback.fst π (e ((SCH).map π w)))) ((SCH).map (pullback.snd π (e ((SCH).map π w))))
        ((SCH).map π) ((SCH).map (e ((SCH).map π w))) := (IsPullback.of_hasPullback π _).map (SCH)
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback w v hv.symm
    refine ⟨(SCH).map π w, hp.isoPullback.inv z, ?_⟩
    rw [← Scheme.Hom.comp_apply, hp.isoPullback_inv_fst]
    exact hz
  · intro a
    simp only [← Functor.map_comp_apply, ← op_comp, pullback.condition]
    rw [op_comp, Functor.map_comp_apply, hx₀ a, hy a]

end AlgMag.SD

#print axioms AlgMag.SD.SDExist_desc_of_local
