/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Lemma D, Step 3: `Γ(V × D(Λ)) = Γ(V)[Λ]` for quasi-compact `V`

Base change along the free map `ℤ → ℤ[Λ]`. As `ℤ[Λ]` is free,
only quasi-compactness is needed (and not quasi-separatedness): the components are sections of the sheaf `O`.

The input is `π : Y → Z` with a character `χ` on `Y`, such that `O(U)[Λ] → Γ(π⁻¹U)` is bijective for `U` affine.
-/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace AlgMag.SD

variable {Y Z : Scheme.{u}} (π : Y ⟶ Z) {Λ : Type u} [AddCommGroup Λ]
  (χ : Multiplicative Λ →* Γ(Y, ⊤))

/-- The restriction of the character `χ` to an open of `Y`. -/
noncomputable def SDR3Coact_resχ (W : Y.Opens) : Multiplicative Λ →* Γ(Y, W) :=
  ((Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom : Γ(Y, ⊤) →+* Γ(Y, W)).toMonoidHom.comp χ

/-- The comparison `O(U)[Λ] → Γ(π⁻¹U)`. -/
noncomputable def SDR3Coact_φ (U : Z.Opens) : AddMonoidAlgebra Γ(Z, U) Λ →+* Γ(Y, π ⁻¹ᵁ U) :=
  AddMonoidAlgebra.liftNCRingHom (π.app U).hom (SDR3Coact_resχ χ (π ⁻¹ᵁ U)) (fun _ _ => mul_comm _ _)

lemma SDR3Coact_φ_single (U : Z.Opens) (d : Λ) (r : Γ(Z, U)) :
    SDR3Coact_φ π χ U (AddMonoidAlgebra.single d r) =
      (π.app U).hom r * SDR3Coact_resχ χ (π ⁻¹ᵁ U) (Multiplicative.ofAdd d) := by
  simp [SDR3Coact_φ, AddMonoidAlgebra.liftNCRingHom, AddMonoidAlgebra.liftNC_single]

/-- Restriction on coefficients. -/
noncomputable def SDR3Coact_res {U U' : Z.Opens} (h : U' ≤ U) :
    AddMonoidAlgebra Γ(Z, U) Λ →+* AddMonoidAlgebra Γ(Z, U') Λ :=
  AddMonoidAlgebra.mapRingHom Λ (Z.presheaf.map (homOfLE h).op).hom

lemma SDR3Coact_coeff_res {U U' : Z.Opens} (h : U' ≤ U) (a : AddMonoidAlgebra Γ(Z, U) Λ) (d : Λ) :
    (SDR3Coact_res (Λ := Λ) h a).coeff d = (Z.presheaf.map (homOfLE h).op).hom (a.coeff d) := by
  simp [SDR3Coact_res]

/-- The comparison is compatible with restriction. -/
lemma SDR3Coact_φ_res {U U' : Z.Opens} (h : U' ≤ U) (a : AddMonoidAlgebra Γ(Z, U) Λ) :
    SDR3Coact_φ π χ U' (SDR3Coact_res h a) =
      (Y.presheaf.map (homOfLE (Scheme.Hom.preimage_mono π h)).op).hom (SDR3Coact_φ π χ U a) := by
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single d r =>
    have hs : SDR3Coact_res (Λ := Λ) h (AddMonoidAlgebra.single d r) =
        AddMonoidAlgebra.single d ((Z.presheaf.map (homOfLE h).op).hom r) := by
      simp [SDR3Coact_res]
    rw [hs, SDR3Coact_φ_single, SDR3Coact_φ_single, map_mul]
    congr 1
    · have := π.naturality (homOfLE h).op
      exact congrArg (fun k => k.hom r) this
    · simp only [SDR3Coact_resχ, MonoidHom.comp_apply]
      change _ = (Y.presheaf.map _).hom ((Y.presheaf.map _).hom _)
      rw [← CommRingCat.comp_apply, ← Y.presheaf.map_comp]
      rfl

variable {π χ}

/-- Injectivity of the comparison on every open: its components are sections of a sheaf. -/
theorem SDR3Coact_φ_injective
    (haff : ∀ U : Z.Opens, IsAffineOpen U → Function.Bijective (SDR3Coact_φ π χ U)) (U : Z.Opens) :
    Function.Injective (SDR3Coact_φ π χ U) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  let ι := {W : Z.Opens // IsAffineOpen W ∧ W ≤ U}
  let C : ι → Z.Opens := fun W => W.1
  have hcover : U ≤ iSup C := by
    intro x hx
    obtain ⟨W, hW, hxW, hWU⟩ := Opens.isBasis_iff_nbhd.1 Z.isBasis_affineOpens hx
    exact Opens.mem_iSup.2 ⟨⟨W, hW, hWU⟩, hxW⟩
  have hres : ∀ i : ι, SDR3Coact_res i.2.2 a = 0 := by
    intro i
    apply (haff _ i.2.1).1
    rw [map_zero, SDR3Coact_φ_res, ha, map_zero]
  ext d
  refine TopCat.Sheaf.eq_of_locally_eq' Z.sheaf C U (fun i => homOfLE i.2.2) hcover _ _ fun i => ?_
  have := congrArg (fun z => z.coeff d) (hres i)
  simp only [SDR3Coact_coeff_res] at this
  refine Eq.trans this ?_
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
  exact (map_zero _).symm

/-- **Step 3**: `Γ(V × D(Λ)) = Γ(V)[Λ]` for quasi-compact `V`. -/
theorem SDR3Coact_φ_bijective
    (haff : ∀ U : Z.Opens, IsAffineOpen U → Function.Bijective (SDR3Coact_φ π χ U)) {U : Z.Opens}
    (hU : IsCompact (U : Set Z)) : Function.Bijective (SDR3Coact_φ π χ U) := by
  classical
  refine ⟨SDR3Coact_φ_injective haff U, fun s => ?_⟩
  obtain ⟨F, hFB, hFf, hFU⟩ := Z.isBasis_affineOpens.exists_finite_of_isCompact hU
  have hF' : Finite F := hFf
  have := Fintype.ofFinite F
  let C : F → Z.Opens := fun W => W.1
  have hCU : ∀ i, C i ≤ U := fun i => by
    rw [hFU]; exact le_sSup i.2
  have hcover : U ≤ iSup C := by
    rw [hFU, sSup_eq_iSup']
  have haffC : ∀ i, IsAffineOpen (C i) := fun i => hFB i.2
  have hP : ∀ i : F, ∃ a, SDR3Coact_φ π χ (C i) a =
      (Y.presheaf.map (homOfLE (Scheme.Hom.preimage_mono π (hCU i))).op).hom s :=
    fun i => (haff _ (haffC i)).2 _
  choose a ha using hP
  have hcomp : ∀ i j, SDR3Coact_res (inf_le_left : C i ⊓ C j ≤ C i) (a i) =
      SDR3Coact_res (inf_le_right : C i ⊓ C j ≤ C j) (a j) := by
    intro i j
    apply SDR3Coact_φ_injective haff
    rw [SDR3Coact_φ_res, SDR3Coact_φ_res, ha, ha, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
      ← Y.presheaf.map_comp, ← Y.presheaf.map_comp]
    rfl
  have hglue : ∀ d, ∃ g : Γ(Z, U), ∀ i, (Z.presheaf.map (homOfLE (hCU i)).op).hom g = (a i).coeff d := by
    intro d
    obtain ⟨g, hg, -⟩ := TopCat.Sheaf.existsUnique_gluing' Z.sheaf C U (fun i => homOfLE (hCU i)) hcover
      (fun i => (a i).coeff d) (fun i j => by
        have := congrArg (fun z => z.coeff d) (hcomp i j)
        simp only [SDR3Coact_coeff_res] at this
        exact this)
    exact ⟨g, hg⟩
  choose g hg using hglue
  let S : Finset Λ := Finset.univ.biUnion fun i => (a i).coeff.support
  refine ⟨∑ d ∈ S, AddMonoidAlgebra.single d (g d), ?_⟩
  have hsum : ∀ i, SDR3Coact_res (hCU i) (∑ d ∈ S, AddMonoidAlgebra.single d (g d)) = a i := by
    intro i
    ext e
    rw [SDR3Coact_coeff_res, AddMonoidAlgebra.coeff_sum]
    by_cases he : e ∈ S
    · rw [Finsupp.finsetSum_apply, Finset.sum_eq_single e]
      · simpa using hg e i
      · intro b _ hbe
        simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, hbe]
      · exact fun h => (h he).elim
    · have h0 : (a i).coeff e = 0 := by
        by_contra hne
        exact he (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Finsupp.mem_support_iff.2 hne⟩)
      rw [h0, Finsupp.finsetSum_apply, Finset.sum_eq_zero, map_zero]
      intro b hb
      have : b ≠ e := fun h => he (h ▸ hb)
      simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, this]
  have hYcover : π ⁻¹ᵁ U ≤ iSup fun i => π ⁻¹ᵁ C i := by
    intro y hy
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hcover hy)
    exact Opens.mem_iSup.2 ⟨i, hi⟩
  refine TopCat.Sheaf.eq_of_locally_eq' Y.sheaf (fun i => π ⁻¹ᵁ C i) (π ⁻¹ᵁ U)
    (fun i => homOfLE (Scheme.Hom.preimage_mono π (hCU i))) hYcover _ _ fun i => ?_
  refine Eq.trans ?_ (ha i)
  rw [← hsum i, SDR3Coact_φ_res]
  rfl

end AlgMag.SD

#print axioms AlgMag.SD.SDR3Coact_φ_bijective
