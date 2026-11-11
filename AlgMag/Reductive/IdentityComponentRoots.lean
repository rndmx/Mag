/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.RootAttractor
import AlgMag.Reductive.AttractorSmooth
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Smooth.LieAlgebra

/-!
# The identity component of an attractor depends only on its roots (F9 blueprint, Lemma 3)

Over an algebraically closed field, for a smooth `G` with a `D(X)`-action: if `N ≤ N'` and
`N ∩ Φ = N' ∩ Φ`, then `(G^N)° = (G^{N'})°` (`identityComponent_attractor_eq_of_roots`).
We record `(G^N)°` as the ideal `compIdeal π N` of `O(G)` (pull-back of the identity-component
ideal of `O(G^N)`). With `K_R := (G^{[R⟩})°`, this is `(G^N)° = K_{N ∩ Φ}`
(Theorem `thm:red-attractors` (ii)).
-/

suppress_compilation

open Magnetism TauCeti TauCeti.HopfIdeal WithConv
open scoped TensorProduct

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X)

section AlgClosed

variable [IsAlgClosed k] [Algebra.FiniteType k H]

/-- The quotient map `O(G) → O(G^N)`. -/
abbrev attrMk (N : Magnet (Additive X)) : H →ₐc[k] H ⧸ (magnetHopfIdeal π N).toIdeal :=
  Bialgebra.Quotient.mkBialgHom (magnetHopfIdeal π N).toIdeal

/-- The identity-component ideal of `O(G^N)`. -/
abbrev attrComp (N : Magnet (Additive X)) : HopfIdeal k (H ⧸ (magnetHopfIdeal π N).toIdeal) :=
  HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H ⧸ (magnetHopfIdeal π N).toIdeal)

/-- The quotient map `O(G) → O((G^N)°)`. -/
abbrev compMk (N : Magnet (Additive X)) :
    H →ₐc[k] (H ⧸ (magnetHopfIdeal π N).toIdeal) ⧸ (attrComp π N).toIdeal :=
  (Bialgebra.Quotient.mkBialgHom (attrComp π N).toIdeal).comp (attrMk π N)

/-- The ideal of `(G^N)°` in `O(G)`. -/
def compIdeal (N : Magnet (Additive X)) : Ideal H := RingHom.ker (compMk π N).toAlgHom.toRingHom

lemma compMk_surjective (N : Magnet (Additive X)) : Function.Surjective (compMk π N) :=
  Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective

lemma derivationComp_compMk_apply (N : Magnet (Additive X)) (e) :
    derivationCompLieHom (B := k) (compMk π N) e =
      (magnetHopfIdeal π N).quotientLieHom (B := k)
        (derivationCompLieHom (B := k) (Bialgebra.Quotient.mkBialgHom (attrComp π N).toIdeal) e) := by
  rw [derivationCompLieHom_comp, LieHom.comp_apply, quotientLieHom_apply,
    derivationCompLieHom_apply]

/-- Derivations of `O((G^N)°)` pulled back to `O(G)` are exactly `Lie(G^N)`. -/
lemma range_derivationComp_compMk (N : Magnet (Additive X)) :
    (derivationCompLieHom (B := k) (compMk π N)).range =
      (magnetHopfIdeal π N).lieSubalgebra (B := k) := by
  ext d
  rw [LieHom.mem_range, HopfIdeal.lieSubalgebra, LieHom.mem_range]
  constructor
  · rintro ⟨e, rfl⟩
    rw [derivationComp_compMk_apply]
    exact ⟨_, rfl⟩
  · rintro ⟨e, rfl⟩
    have htop := lieSubalgebra_identityComponentHopfIdeal_eq_top
      (H := FiniteTypeCommHopfAlgCat.of (R := k) (H ⧸ (magnetHopfIdeal π N).toIdeal))
    have he : e ∈ (attrComp π N).lieSubalgebra (B := k) := htop ▸ LieSubalgebra.mem_top e
    rw [HopfIdeal.lieSubalgebra, LieHom.mem_range] at he
    obtain ⟨e', he'⟩ := he
    refine ⟨e', ?_⟩
    rw [derivationComp_compMk_apply, ← he']
    simp only [quotientLieHom_apply, derivationCompLieHom_apply]

lemma derivationComp_compMk_injective (N : Magnet (Additive X)) :
    Function.Injective (derivationCompLieHom (B := k) (compMk π N)) := by
  rw [derivationCompLieHom_comp, LieHom.coe_comp]
  exact (quotientLieHom_injective _).comp (quotientLieHom_injective _)

/-- `(G^N)° ⊆ (G^{N'})°` for `N ≤ N'`: `compMk π N` factors through `compMk π N'`. -/
lemma exists_comp_compMk {N N' : Magnet (Additive X)} (hle : N ≤ N') :
    ∃ f : (H ⧸ (magnetHopfIdeal π N').toIdeal) ⧸ (attrComp π N').toIdeal →ₐc[k]
        (H ⧸ (magnetHopfIdeal π N).toIdeal) ⧸ (attrComp π N).toIdeal,
      f.comp (compMk π N') = compMk π N := by
  have hJ : (magnetHopfIdeal π N').toIdeal ≤ RingHom.ker (compMk π N).toAlgHom.toRingHom := by
    intro x hx
    have hx' : x ∈ (magnetHopfIdeal π N).toIdeal := by
      rw [magnetHopfIdeal_toIdeal] at hx ⊢; exact magnetIdeal_anti _ hle hx
    rw [RingHom.mem_ker]
    show Ideal.Quotient.mk _ (Ideal.Quotient.mk _ x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx', map_zero]
  let g := Bialgebra.Quotient.liftBialgHom _ (compMk π N) hJ
  have : ConnectedSpace (PrimeSpectrum
      ((H ⧸ (magnetHopfIdeal π N).toIdeal) ⧸ (attrComp π N).toIdeal)) :=
    FiniteTypeCommHopfAlgCat.connectedSpace_identityComponent
      (FiniteTypeCommHopfAlgCat.of (R := k) (H ⧸ (magnetHopfIdeal π N).toIdeal))
  have hI : (attrComp π N').toIdeal ≤ RingHom.ker g.toAlgHom.toRingHom :=
    CommHopfAlgCat.identityComponentHopfIdeal_toIdeal_le_ker_of_connected
      (H := _root_.CommHopfAlgCat.of k (H ⧸ (magnetHopfIdeal π N').toIdeal))
      (K := _root_.CommHopfAlgCat.of k
        ((H ⧸ (magnetHopfIdeal π N).toIdeal) ⧸ (attrComp π N).toIdeal))
      (_root_.CommHopfAlgCat.ofHom g)
  refine ⟨Bialgebra.Quotient.liftBialgHom _ g hI, ?_⟩
  ext x
  rfl

variable [Algebra.Smooth k H] [Module.Finite k (Bialgebra.CotangentSpace k H)]

/-- **Lemma 3 (F9).** If `N ≤ N'` contain the same roots, `(G^N)° = (G^{N'})°`. -/
theorem compIdeal_eq_of_roots {N N' : Magnet (Additive X)} (hle : N ≤ N')
    (h : ∀ α ∈ roots π, α ∈ N ↔ α ∈ N') : compIdeal π N = compIdeal π N' := by
  obtain ⟨f, hf⟩ := exists_comp_compMk π hle
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := compMk_surjective π N y
    exact ⟨compMk π N' x, by rw [← hf]; rfl⟩
  have : Algebra.Smooth k (H ⧸ (magnetHopfIdeal π N).toIdeal) := smooth_quotient_magnetHopfIdeal π N
  have : Algebra.Smooth k (H ⧸ (magnetHopfIdeal π N').toIdeal) :=
    smooth_quotient_magnetHopfIdeal π N'
  have hS : ∀ M : Magnet (Additive X),
      Algebra.Smooth k ((H ⧸ (magnetHopfIdeal π M).toIdeal) ⧸ (attrComp π M).toIdeal) := fun M =>
    haveI : Algebra.Smooth k (H ⧸ (magnetHopfIdeal π M).toIdeal) :=
      smooth_quotient_magnetHopfIdeal π M
    FiniteTypeCommHopfAlgCat.smooth_identityComponent (FiniteTypeCommHopfAlgCat.of (R := k) (H ⧸ (magnetHopfIdeal π M).toIdeal))
  have hC : ∀ M : Magnet (Additive X), ConnectedSpace (PrimeSpectrum
      ((H ⧸ (magnetHopfIdeal π M).toIdeal) ⧸ (attrComp π M).toIdeal)) := fun M =>
    FiniteTypeCommHopfAlgCat.connectedSpace_identityComponent
      (FiniteTypeCommHopfAlgCat.of (R := k) (H ⧸ (magnetHopfIdeal π M).toIdeal))
  have hdf : Function.Surjective (derivationCompLieHom (B := k) f) := by
    intro d
    have hd : derivationCompLieHom (B := k) (compMk π N') d ∈
        (derivationCompLieHom (B := k) (compMk π N)).range := by
      rw [range_derivationComp_compMk, lieSubalgebra_magnetHopfIdeal_eq_of_roots h,
        ← range_derivationComp_compMk]
      exact LieHom.mem_range_self _ _
    obtain ⟨e, he⟩ := (LieHom.mem_range _ _).1 hd
    refine ⟨e, derivationComp_compMk_injective π N' ?_⟩
    rw [← he, ← hf, derivationCompLieHom_comp f (compMk π N'), LieHom.comp_apply]
  have hker := ker_eq_bot_of_smooth_of_connected_of_conormalSubspace_eq_bot f hfs
    ((smoothCommHopfAlgProperty_iff _).mpr (hS N')) (hC N')
    ((smoothCommHopfAlgProperty_iff _).mpr (hS N)) (hC N)
    (conormalSubspace_ker_eq_bot_of_surjective_of_derivationCompLieHom_surjective f hfs hdf)
  apply le_antisymm
  · intro x hx
    have h0 : f (compMk π N' x) = 0 := by
      rw [← BialgHom.comp_apply, hf]; exact hx
    have hmem : compMk π N' x ∈ HopfIdeal.ker f := by rw [mem_ker]; exact h0
    rw [hker, HopfIdeal.mem_bot] at hmem
    exact hmem
  · intro x hx
    show compMk π N x = 0
    rw [← hf, BialgHom.comp_apply]
    have : compMk π N' x = 0 := hx
    rw [this, map_zero]

/-- `K_R := (G^{[R⟩})°`, the identity component of the attractor of the magnet generated by `R`
(as an ideal of `O(G)`). -/
def rootComp (R : Set (Additive X)) : Ideal H := compIdeal π (AddSubmonoid.closure R)

/-- **Theorem `thm:red-attractors` (ii), identity component.** `(G^N)° = K_{N ∩ Φ}`. -/
theorem compIdeal_eq_rootComp (N : Magnet (Additive X)) :
    compIdeal π N = rootComp π ({α | α ∈ N} ∩ roots π) := by
  refine (compIdeal_eq_of_roots π (AddSubmonoid.closure_le.2 Set.inter_subset_left)
    fun α hα => ⟨fun h => AddSubmonoid.closure_le.2 Set.inter_subset_left h,
      fun h => AddSubmonoid.subset_closure ⟨h, hα⟩⟩).symm

end AlgClosed

end AlgMag.Reductive

