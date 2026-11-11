/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.RegularConjugatesOpen
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.RingTheory.Ideal.GoingDown

/-!
# Step C2(d), assembly: flat images are open on `k`-points

* `isOpen_points_image`: for `H → B` flat of finite presentation, `B` of finite type over an
  algebraically closed `k`, the set of `k`-points of `H` that lift to `k`-points of `B` is open
  for the Zariski topology `zariski`.
* `exists_open_of_flat_slice`: the C2(d) statement, from a flat slice `B` whose `k`-points map
  to regular conjugates in `K`.
-/

suppress_compilation

open Magnetism TauCeti WithConv
open scoped AlgMag.Reductive.Zariski

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} [Field k] [CommRing H] [HopfAlgebra k H] [IsAlgClosed k]
  [Algebra.FiniteType k H]

omit [IsAlgClosed k] [Algebra.FiniteType k H] in
/-- Two `k`-points with `ker x ≤ ker y` are equal. -/
lemma algHom_eq_of_ker_le {A : Type*} [CommRing A] [Algebra k A] {x y : A →ₐ[k] k}
    (h : RingHom.ker x ≤ RingHom.ker y) : x = y := by
  ext a
  have : a - algebraMap k A (x a) ∈ RingHom.ker x := by
    rw [RingHom.mem_ker]; simp
  have := h this
  rw [RingHom.mem_ker] at this
  simp only [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] at this
  exact (sub_eq_zero.1 this).symm

variable {B : Type u} [CommRing B] [Algebra k B] [Algebra H B] [IsScalarTower k H B]
  [Algebra.FiniteType k B]

/-- The `k`-points of `H` lifting to `k`-points of `B`. -/
def liftPoints (B : Type u) [CommRing B] [Algebra k B] [Algebra H B] [IsScalarTower k H B] :
    Set (WithConv (H →ₐ[k] k)) :=
  {x | ∃ y : B →ₐ[k] k, y.comp (IsScalarTower.toAlgHom k H B) = x.ofConv}

lemma liftPoints_eq : liftPoints (k := k) (H := H) B =
    kerPt ⁻¹' Set.range (PrimeSpectrum.comap (algebraMap H B)) := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨⟨RingHom.ker y, RingHom.ker_isPrime _⟩, ?_⟩
    ext a
    simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, RingHom.mem_ker, kerPt]
    rw [← hy]; rfl
  · rintro ⟨q, hq⟩
    -- the fibre `B ⧸ (ker x) B` is nonzero, so it has a `k`-point.
    set m := RingHom.ker x.ofConv
    have hle : Ideal.map (algebraMap H B) m ≤ q.asIdeal := by
      rw [Ideal.map_le_iff_le_comap]
      have := congrArg PrimeSpectrum.asIdeal hq
      simp only [PrimeSpectrum.comap_asIdeal, kerPt] at this
      rw [this]
    have hne : Ideal.map (algebraMap H B) m ≠ ⊤ := fun h => q.isPrime.ne_top (top_le_iff.1 (h ▸ hle))
    obtain ⟨M, hM, hmM⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨y, hy⟩ := OpenCellNotes.exists_algHom_ker_eq (K := k) M
    refine ⟨y, (algHom_eq_of_ker_le ?_).symm⟩
    intro a ha
    rw [RingHom.mem_ker, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', ← RingHom.mem_ker, hy]
    exact hmM (Ideal.mem_map_of_mem _ ha)

/-- **Flat images are open on `k`-points.** -/
theorem isOpen_points_image [Module.Flat H B] [Algebra.FinitePresentation H B] :
    IsOpen (liftPoints (k := k) (H := H) B) := by
  rw [liftPoints_eq, ← Set.image_univ]
  exact (PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation _
    isOpen_univ).preimage isInducing_kerPt.continuous

/-- **C2(d) from a flat slice.** If `H → B` is flat of finite presentation, `B` has a `k`-point,
and every `k`-point of `H` lifting to `B` is in `K` and a conjugate `g t g⁻¹` (`g ∈ K`,
`t ∈ Treg`), then `K` contains a nonempty open set of such conjugates. -/
theorem exists_open_of_flat_slice [Module.Flat H B] [Algebra.FinitePresentation H B]
    (K : Set (WithConv (H →ₐ[k] k))) (Treg : Set (WithConv (H →ₐ[k] k)))
    (hne : Nonempty (B →ₐ[k] k))
    (hK : ∀ x ∈ liftPoints (k := k) (H := H) B, x ∈ K)
    (hconj : ∀ x ∈ liftPoints (k := k) (H := H) B, ∃ g ∈ K, ∃ t ∈ Treg, x = g * t * g⁻¹) :
    ∃ U : Set K, IsOpen U ∧ U.Nonempty ∧
      ∀ x ∈ U, ∃ g ∈ K, ∃ t ∈ Treg, (x : WithConv (H →ₐ[k] k)) = g * t * g⁻¹ := by
  refine ⟨Subtype.val ⁻¹' liftPoints B, (isOpen_points_image).preimage continuous_subtype_val,
    ?_, fun x hx => hconj x hx⟩
  obtain ⟨y⟩ := hne
  have hy : toConv (y.comp (IsScalarTower.toAlgHom k H B)) ∈ liftPoints (k := k) (H := H) B :=
    ⟨y, rfl⟩
  exact ⟨⟨_, hK _ hy⟩, hy⟩

/-- **Flat images over a closed subgroup.** If `H → A` is surjective (`A = O(K)`) and `B` is
flat of finite presentation over `A`, the `k`-points of `K` lifting to `B` form an open subset
of `K(k)`. -/
theorem isOpen_liftPoints_subtype {A : Type u} [CommRing A] [Algebra k A] [Algebra H A]
    [IsScalarTower k H A] (hp : Function.Surjective (algebraMap H A))
    [Algebra A B] [IsScalarTower H A B] [Module.Flat A B] [Algebra.FinitePresentation A B]
    (K : Set (WithConv (H →ₐ[k] k)))
    (hK : ∀ x, x ∈ K ↔ RingHom.ker (algebraMap H A) ≤ RingHom.ker x.ofConv) :
    IsOpen (Subtype.val ⁻¹' liftPoints (k := k) (H := H) B : Set K) := by
  set e := PrimeSpectrum.comap (algebraMap H A)
  have he := PrimeSpectrum.isClosedEmbedding_comap_of_surjective A (algebraMap H A) hp
  have hS : IsOpen (Set.range (PrimeSpectrum.comap (algebraMap A B))) := by
    rw [← Set.image_univ]
    exact PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation _ isOpen_univ
  obtain ⟨O, hO, hOS⟩ := he.isInducing.isOpen_iff.1 hS
  have heq : (Subtype.val ⁻¹' liftPoints (k := k) (H := H) B : Set K) =
      (fun x : K => kerPt (x : WithConv (H →ₐ[k] k))) ⁻¹' O := by
    ext ⟨x, hx⟩
    have hxr : kerPt x ∈ Set.range e := by
      rw [range_comap_of_surjective _ _ hp]
      exact (hK x).1 hx
    obtain ⟨q, hq⟩ := hxr
    simp only [Set.mem_preimage, liftPoints_eq]
    rw [← hq]
    have hcomp : algebraMap H B = (algebraMap A B).comp (algebraMap H A) :=
      IsScalarTower.algebraMap_eq H A B
    constructor
    · rintro ⟨r, hr⟩
      rw [hcomp, PrimeSpectrum.comap_comp_apply] at hr
      have : PrimeSpectrum.comap (algebraMap A B) r = q := he.injective hr
      have hqS : q ∈ Set.range (PrimeSpectrum.comap (algebraMap A B)) := ⟨r, this⟩
      rw [← hOS] at hqS
      exact hqS
    · intro h
      have hqS : q ∈ e ⁻¹' O := h
      rw [hOS] at hqS
      obtain ⟨r, hr⟩ := hqS
      exact ⟨r, by rw [hcomp, PrimeSpectrum.comap_comp_apply, hr]⟩
  rw [heq]
  exact hO.preimage (isInducing_kerPt.continuous.comp continuous_subtype_val)

end AlgMag.Reductive
