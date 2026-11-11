/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SDR3CoactSite

/-!
# Lemma D, Step 3: the coaction on `Γ(Z, O)`; the saturated open is open

continuing `AlgMag.SDR3CoactSite`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgMag.SD

open AlgMag AlgMag.SQ

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

variable {Λ : Type u} [AddCommGroup Λ] [Countable Λ] {W Z : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]

/-- The scheme map `D(Λ) × Z → Spec O(W)[Λ]`. -/
noncomputable abbrev SDR3Coact_g (r : Z ⟶ W) :
    (SCH).obj (SDR3Coact_Y Λ r) ⟶ Spec (.of (AddMonoidAlgebra Γ((SCH).obj W, ⊤) Λ)) :=
  (SCH).map (pullback.fst (specPr Λ W) r)

/-- `D(Λ) × Z` is a base change of `Spec O(W)[Λ] → Spec O(W)`. -/
theorem SDR3Coact_schemePb (r : Z ⟶ W) :
    IsPullback (SDR3Coact_g (Λ := Λ) r) ((SCH).map (SDR3Coact_π Λ r)) (SDR3Coact_str Γ((SCH).obj W, ⊤) Λ)
      ((SCH).map r ≫ ((SCH).obj W).isoSpec.hom) := by
  have h := (IsPullback.of_hasPullback (specPr Λ W) r).map (SCH)
  refine IsPullback.of_iso h (Iso.refl _) (Iso.refl _) (Iso.refl _) ((SCH).obj W).isoSpec
    ((Category.comp_id _).trans (Category.id_comp _).symm) ((Category.comp_id _).trans (Category.id_comp _).symm) ?_
    (by simp only [Iso.refl_hom, Category.id_comp])
  simp only [Iso.refl_hom, Category.id_comp]
  change (Spec.map _ ≫ ((SCH).obj W).isoSpec.inv) ≫ _ = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

lemma SDR3Coact_app {X Y' T : Scheme.{u}} {f : T ⟶ X} {k : X ⟶ Y'} {h : T ⟶ Y'} (e : f ≫ k = h) (y : Γ(Y', ⊤)) :
    f.appTop.hom (k.appTop.hom y) = h.appTop.hom y := by
  subst e; rw [Scheme.Hom.comp_appTop]; rfl

variable (actZ : AAction (fppfO B S hS) Λ (yoneda.obj Z)) (r : Z ⟶ W)

/-- **Step 3**: for `Z` quasi-compact the action gives a coaction `σ` on `Γ(Z, O)`, with `Σ y_d χ^d = a^* y`. -/
theorem SDR3Coact_coact [CompactSpace ((SCH).obj Z)] :
    ∃ c : Coact Γ((SCH).obj Z, ⊤) Λ, ∀ y,
      SDR3Coact_lift ((SCH).map (SDR3Coact_π Λ r)).appTop.hom (SDR3Coact_chi (SDR3Coact_g (Λ := Λ) r)) (c.σ y) =
        ((SCH).map (SDR3Coact_a actZ r)).appTop.hom y := by
  have hbase := SDR3Coact_base_bijective (SDR3Coact_schemePb (Λ := Λ) r)
  have hbase₂ := SDR3Coact_base_bijective (SDR3Coact_schemePb (Λ := Λ) (SDR3Coact_π Λ r ≫ r))
  have hφ : Function.Bijective (SDR3Coact_lift ((SCH).map (SDR3Coact_π Λ r)).appTop.hom
      (SDR3Coact_chi (SDR3Coact_g (Λ := Λ) r))) := by
    have h := SDR3Coact_φ_bijective hbase (U := ⊤) (show IsCompact (Set.univ : Set ((SCH).obj Z)) from isCompact_univ)
    have e : ⇑(SDR3Coact_lift ((SCH).map (SDR3Coact_π Λ r)).appTop.hom (SDR3Coact_chi (SDR3Coact_g (Λ := Λ) r))) =
        ⇑(SDR3Coact_φ ((SCH).map (SDR3Coact_π Λ r)) (SDR3Coact_chi (SDR3Coact_g (Λ := Λ) r)) ⊤) :=
      funext fun a => (SDR3Coact_φ_top _ _ a).symm
    rw [e]; exact h
  have hψ : Function.Injective (SDR3Coact_lift ((SCH).map (SDR3Coact_p (Λ := Λ) r)).appTop.hom
      (SDR3Coact_chi (SDR3Coact_g (Λ := Λ) (SDR3Coact_π Λ r ≫ r)))) := by
    have h := SDR3Coact_φ_injective hbase₂ ⊤
    have e : ⇑(SDR3Coact_lift ((SCH).map (SDR3Coact_p (Λ := Λ) r)).appTop.hom
        (SDR3Coact_chi (SDR3Coact_g (Λ := Λ) (SDR3Coact_π Λ r ≫ r)))) =
        ⇑(SDR3Coact_φ ((SCH).map (SDR3Coact_p (Λ := Λ) r))
          (SDR3Coact_chi (SDR3Coact_g (Λ := Λ) (SDR3Coact_π Λ r ≫ r))) ⊤) :=
      funext fun a => (SDR3Coact_φ_top _ _ a).symm
    rw [e]; exact h
  have mk : ∀ {X X' X'' : BigFppfOver B S hS} {f : X ⟶ X'} {k : X' ⟶ X''} {h : X ⟶ X''} (_ : f ≫ k = h)
      (y : Γ((SCH).obj X'', ⊤)), ((SCH).map f).appTop.hom (((SCH).map k).appTop.hom y) = ((SCH).map h).appTop.hom y := by
    intro X X' X'' f k h e y
    exact SDR3Coact_app (by rw [← e, Functor.map_comp]) y
  have hres : ∀ {T : BigFppfOver B S hS} (f : T ⟶ SDR3Coact_Y Λ r) (d : Multiplicative Λ),
      ((SCH).map f).appTop.hom (SDR3Coact_chi (SDR3Coact_g (Λ := Λ) r) d) = APt.res f.op (SDR3Coact_χ Λ r) d :=
    fun _ _ => rfl
  refine SDR3Coact_ofRing _ _ ((SCH).map (SDR3Coact_e (Λ := Λ) r)).appTop.hom _
    ((SCH).map (SDR3Coact_m (Λ := Λ) r)).appTop.hom ((SCH).map (SDR3Coact_act actZ r)).appTop.hom _ _ hφ hψ
    (fun y => ?_) (fun y => ?_) (fun d => ?_) (fun y => ?_) (fun d => ?_) (fun y => ?_) (fun d => ?_) (fun y => ?_)
  · refine (mk (SDR3Coact_pt_π (r := r) (𝟙 Z) (1 : APt (fppfO B S hS) Λ (op Z))) y).trans ?_
    rw [CategoryTheory.Functor.map_id]; simp
  · refine (mk (SDR3Coact_e_a actZ r) y).trans ?_
    rw [CategoryTheory.Functor.map_id]; simp
  · rw [hres]
    change APt.res (SDR3Coact_pt (r := r) (𝟙 Z) 1).op (SDR3Coact_χ Λ r) d = 1
    rw [SDR3Coact_pt_χ]; rfl
  · exact (mk (SDR3Coact_pt_π _ _) y).trans (mk rfl y).symm
  · rw [hres]
    change APt.res (SDR3Coact_pt _ _).op (SDR3Coact_χ Λ r) d = _
    rw [SDR3Coact_pt_χ, mul_comm]
    rfl
  · exact (mk (SDR3Coact_pt_π _ _) y).trans (mk rfl y).symm
  · rw [hres]
    change APt.res (SDR3Coact_pt _ _).op (SDR3Coact_χ Λ r) d = _
    rw [SDR3Coact_pt_χ]
    rfl
  · exact (mk (SDR3Coact_m_a actZ r) y)

lemma SDR3Coact_ι_ι : SDR3Coact_ι actZ r ≫ SDR3Coact_ι actZ r = 𝟙 _ := by
  refine SDR3Coact_hom_ext ?_ ?_
  · rw [Category.assoc, SDR3Coact_ι_π, SDR3Coact_ι_a, Category.id_comp]
  · rw [op_comp, APt.res_comp, SDR3Coact_ι, SDR3Coact_pt_χ, APt.inv_res, SDR3Coact_pt_χ]
    refine MonoidHom.ext fun d => ?_
    change SDR3Coact_χ Λ r d⁻¹⁻¹ = (APt.res (𝟙 _) (SDR3Coact_χ Λ r)) d
    rw [inv_inv, APt.res_id]

/-- The projection is open, for `Λ` finitely generated. -/
theorem SDR3Coact_π_isOpenMap [AddGroup.FG Λ] : IsOpenMap ((SCH).map (SDR3Coact_π Λ r)) := by
  let A := Γ((SCH).obj W, ⊤)
  have : Flat (SDR3Coact_str A Λ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    change (algebraMap A (AddMonoidAlgebra A Λ)).Flat
    exact RingHom.flat_algebraMap_iff.2 inferInstance
  have : LocallyOfFinitePresentation (SDR3Coact_str A Λ) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
    change (algebraMap A (AddMonoidAlgebra A Λ)).FinitePresentation
    have hft : Algebra.FiniteType ℤ (AddMonoidAlgebra ℤ Λ) := AddMonoidAlgebra.finiteType_of_fg ℤ Λ
    have hfp : Algebra.FinitePresentation ℤ (AddMonoidAlgebra ℤ Λ) := Algebra.FinitePresentation.of_finiteType.1 hft
    exact RingHom.finitePresentation_algebraMap.2
      (Algebra.FinitePresentation.equiv (R := A) (A := TensorProduct ℤ A (AddMonoidAlgebra ℤ Λ))
        (AddMonoidAlgebra.scalarTensorEquiv ℤ A))
  have ho : UniversallyOpen (SDR3Coact_str A Λ) := UniversallyOpen.of_flat _
  have := MorphismProperty.of_isPullback (P := @UniversallyOpen) (SDR3Coact_schemePb (Λ := Λ) r) ho
  exact Scheme.Hom.isOpenMap _

/-- **Step 2**: `V = a(π⁻¹ U₀)` is open, for `U₀` open. -/
theorem SDR3Coact_isOpen_sat [AddGroup.FG Λ] {U₀ : Set ((SCH).obj Z)} (hU : IsOpen U₀) :
    IsOpen ((SCH).map (SDR3Coact_a actZ r) '' ((SCH).map (SDR3Coact_π Λ r) ⁻¹' U₀)) := by
  have hιι := SDR3Coact_ι_ι actZ r
  have hh : (SCH).map (SDR3Coact_ι actZ r) ≫ (SCH).map (SDR3Coact_ι actZ r) = 𝟙 _ := by
    rw [← Functor.map_comp, hιι, CategoryTheory.Functor.map_id]
  have : IsIso ((SCH).map (SDR3Coact_ι actZ r)) := ⟨⟨_, hh, hh⟩⟩
  have hopen : IsOpenMap ((SCH).map (SDR3Coact_ι actZ r)) := ((SCH).map (SDR3Coact_ι actZ r)).homeomorph.isOpenMap
  have hfac : ⇑((SCH).map (SDR3Coact_a actZ r)) = ⇑((SCH).map (SDR3Coact_π Λ r)) ∘ ⇑((SCH).map (SDR3Coact_ι actZ r)) := by
    rw [← SDR3Coact_ι_π, Functor.map_comp]; rfl
  rw [hfac]
  exact ((SDR3Coact_π_isOpenMap r).comp hopen) _ (hU.preimage ((SCH).map (SDR3Coact_π Λ r)).continuous)

/-- `U₀ ⊆ V`. -/
theorem SDR3Coact_subset_sat (U₀ : Set ((SCH).obj Z)) :
    U₀ ⊆ (SCH).map (SDR3Coact_a actZ r) '' ((SCH).map (SDR3Coact_π Λ r) ⁻¹' U₀) := by
  intro z hz
  have h1 : (SCH).map (SDR3Coact_e (Λ := Λ) r) ≫ (SCH).map (SDR3Coact_π Λ r) = 𝟙 _ := by
    rw [← Functor.map_comp, SDR3Coact_e, SDR3Coact_pt_π, CategoryTheory.Functor.map_id]
  have h2 : (SCH).map (SDR3Coact_e (Λ := Λ) r) ≫ (SCH).map (SDR3Coact_a actZ r) = 𝟙 _ := by
    rw [← Functor.map_comp, SDR3Coact_e_a, CategoryTheory.Functor.map_id]
  refine ⟨(SCH).map (SDR3Coact_e (Λ := Λ) r) z, ?_, ?_⟩
  · change ((SCH).map (SDR3Coact_π Λ r)) ((SCH).map (SDR3Coact_e (Λ := Λ) r) z) ∈ U₀
    have t : ((SCH).map (SDR3Coact_π Λ r)) ((SCH).map (SDR3Coact_e (Λ := Λ) r) z) = z :=
      congrArg (fun k : (SCH).obj Z ⟶ (SCH).obj Z => k z) h1
    rw [t]; exact hz
  · exact congrArg (fun k : (SCH).obj Z ⟶ (SCH).obj Z => k z) h2

/-- `V` is quasi-compact, for `U₀` quasi-compact and open. -/
theorem SDR3Coact_isCompact_sat {U₀ : Set ((SCH).obj Z)} (hU : IsOpen U₀) (hc : IsCompact U₀) :
    IsCompact ((SCH).map (SDR3Coact_a actZ r) '' ((SCH).map (SDR3Coact_π Λ r) ⁻¹' U₀)) := by
  have hq : QuasiCompact (SDR3Coact_str Γ((SCH).obj W, ⊤) Λ) := inferInstance
  have := MorphismProperty.of_isPullback (P := @QuasiCompact) (SDR3Coact_schemePb (Λ := Λ) r) hq
  exact (QuasiCompact.isCompact_preimage _ hU hc).image ((SCH).map (SDR3Coact_a actZ r)).continuous

end AlgMag.SD

#print axioms AlgMag.SD.SDR3Coact_coact
#print axioms AlgMag.SD.SDR3Coact_isOpen_sat
#print axioms AlgMag.SD.SDR3Coact_isCompact_sat
#print axioms AlgMag.SD.SDR3Coact_subset_sat
