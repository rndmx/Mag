/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.RegularConjugatesOpen

/-!
# Left translations on `k`-points, and subgroups containing an open set

For the Zariski topology on `k`-points (`AlgMag.Reductive.zariski`):

* `leftTranslation`: the coordinate map `ℓ_a = (a ⊗ id) ∘ Δ` of left translation by a `k`-point;
* `comp_leftTranslation`: `x ∘ ℓ_a = a * x`;
* `continuous_mul_left`: `x ↦ a * x` is continuous;
* `eq_of_isOpen_subset`: in an irreducible set `K` of `k`-points closed under left
  multiplication by its elements, a subgroup containing a nonempty open subset of `K` contains
  `K` (two nonempty opens meet).

Used for the endgame of the converse of the reductivity criterion: a point of the rank-one Levi
is a product of two points of its open cell.
-/

suppress_compilation

open Magnetism TauCeti WithConv
open scoped TensorProduct

namespace AlgMag.Reductive

universe u

section Translation

variable {k : Type u} {H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]

/-- Left translation by a `k`-point on coordinates: `h ↦ Σ a(h₁) h₂`. -/
def leftTranslation (a : WithConv (H →ₐ[k] k)) : H →ₐ[k] H :=
  (Algebra.TensorProduct.lmul' k).comp
    ((Algebra.TensorProduct.map ((Algebra.ofId k H).comp a.ofConv) (AlgHom.id k H)).comp
      (Bialgebra.comulAlgHom k H))

lemma comp_leftTranslation_apply (a x : WithConv (H →ₐ[k] k)) (h : H) :
    x.ofConv (leftTranslation a h) = (a * x).ofConv h := by
  rw [AlgHom.convMul_apply]
  simp only [leftTranslation, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply]
  induction (Coalgebra.comul (R := k) h : H ⊗[k] H) using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul s t =>
    simp [Algebra.TensorProduct.lmul'_apply_tmul, Algebra.TensorProduct.lift_tmul]

/-- `ker (a x) = ℓ_a⁻¹ (ker x)`. -/
lemma kerPt_mul_left (a x : WithConv (H →ₐ[k] k)) :
    kerPt (a * x) = PrimeSpectrum.comap (leftTranslation a).toRingHom (kerPt x) := by
  ext h
  simp only [kerPt, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, RingHom.mem_ker]
  change (a * x).ofConv h = 0 ↔ x.ofConv (leftTranslation a h) = 0
  rw [comp_leftTranslation_apply]

open scoped Zariski

/-- Left translation by a `k`-point is continuous for the Zariski topology. -/
theorem continuous_mul_left (a : WithConv (H →ₐ[k] k)) :
    Continuous fun x : WithConv (H →ₐ[k] k) => a * x := by
  rw [isInducing_kerPt.continuous_iff]
  have : (kerPt ∘ fun x : WithConv (H →ₐ[k] k) => a * x) =
      PrimeSpectrum.comap (leftTranslation a).toRingHom ∘ kerPt := by
    funext x; exact kerPt_mul_left a x
  rw [this]
  exact (PrimeSpectrum.continuous_comap _).comp isInducing_kerPt.continuous

/-- **A subgroup containing a nonempty open subset of an irreducible set of points contains it.**
`K` is a set of `k`-points closed under products and inverses, irreducible for the Zariski
topology; `S` is a subgroup of `G(k)` containing a nonempty open subset `O` of `K`. -/
theorem subset_of_isOpen_subset (K : Set (WithConv (H →ₐ[k] k))) [IrreducibleSpace K]
    (hmul : ∀ x ∈ K, ∀ y ∈ K, x * y ∈ K) (hinv : ∀ x ∈ K, x⁻¹ ∈ K)
    (S : Subgroup (WithConv (H →ₐ[k] k))) (O : Set K) (hO : IsOpen O) (hOn : O.Nonempty)
    (hOS : ∀ x ∈ O, (x : WithConv (H →ₐ[k] k)) ∈ S) :
    ∀ g ∈ K, g ∈ S := by
  intro g hg
  -- `V = {x ∈ K | g x ∈ O}` is open and nonempty
  let f : K → K := fun x => ⟨g * x, hmul g hg x x.2⟩
  have hf : Continuous f :=
    ((continuous_mul_left g).comp continuous_subtype_val).subtype_mk _
  set V := f ⁻¹' O
  have hV : IsOpen V := hO.preimage hf
  obtain ⟨o, ho⟩ := hOn
  have hVn : V.Nonempty := by
    refine ⟨⟨g⁻¹ * o, hmul _ (hinv g hg) o o.2⟩, ?_⟩
    show f _ ∈ O
    have : f ⟨g⁻¹ * o, hmul _ (hinv g hg) o o.2⟩ = o := by
      apply Subtype.ext; simp [f]
    rw [this]; exact ho
  obtain ⟨x, -, hxO, hxV⟩ := IrreducibleSpace.isIrreducible_univ K |>.2 O V hO hV
    ⟨o, trivial, ho⟩ (by obtain ⟨v, hv⟩ := hVn; exact ⟨v, trivial, hv⟩)
  have h1 : (x : WithConv (H →ₐ[k] k)) ∈ S := hOS x hxO
  have h2 : g * x ∈ S := hOS (f x) hxV
  have : g = (g * x) * (x : WithConv (H →ₐ[k] k))⁻¹ := by group
  rw [this]
  exact S.mul_mem h2 (S.inv_mem h1)

end Translation

end AlgMag.Reductive
