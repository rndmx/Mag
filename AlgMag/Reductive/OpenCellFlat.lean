/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.OpenCellEpi
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.FiniteStability

/-!
# The open cell is an open immersion once it is flat

The open cell map `openCellRingHom λ` is an epimorphism of rings (from
`openCellMap_comp_injective`), so `Spec` of it is a monomorphism of schemes; it is of finite
presentation. By Mathlib's `IsOpenImmersion.of_flat_of_mono` it is an open immersion as soon as it
is flat. Hence Proposition 16.10 (ii) over an algebraically closed field, for `G` smooth and
irreducible, reduces to the flatness of the open cell map.
-/

suppress_compilation

open CategoryTheory AlgebraicGeometry Magnetism TauCeti TauCeti.Cocharacter
open scoped TensorProduct

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
variable (l : H →ₐc[k] LaurentPolynomial k)

/-- The open cell map is an epimorphism of commutative rings. -/
theorem epi_openCellRingHom :
    Epi (CommRingCat.ofHom (R := H) (S := OpenCellRing l) (openCellRingHom l) :
      CommRingCat.of H ⟶ CommRingCat.of (OpenCellRing l)) := by
  refine ⟨fun {C} g h e => ?_⟩
  have e' : g.hom.comp (openCellRingHom l) = h.hom.comp (openCellRingHom l) :=
    congrArg CommRingCat.Hom.hom e
  let _ : Algebra k C := (g.hom.comp (algebraMap k (OpenCellRing l))).toAlgebra
  let g' : OpenCellRing l →ₐ[k] C := { g.hom with commutes' := fun _ => rfl }
  let h' : OpenCellRing l →ₐ[k] C :=
    { h.hom with
      commutes' := fun r => by
        change h.hom (algebraMap k (OpenCellRing l) r) = g.hom (algebraMap k (OpenCellRing l) r)
        rw [← (openCellMap l).commutes r]
        exact (RingHom.congr_fun e' (algebraMap k H r)).symm }
  have : g' = h' := openCellMap_comp_injective l (AlgHom.ext fun x => RingHom.congr_fun e' x)
  exact CommRingCat.hom_ext (RingHom.ext fun x =>
    congrArg (fun φ : OpenCellRing l →ₐ[k] C => φ x) this)

/-- `Spec` of the open cell map is a monomorphism of schemes. -/
theorem mono_spec_openCellRingHom :
    Mono (Spec.map (CommRingCat.ofHom (R := H) (S := OpenCellRing l) (openCellRingHom l) :
      CommRingCat.of H ⟶ CommRingCat.of (OpenCellRing l))) := by
  have := epi_openCellRingHom l
  exact inferInstanceAs (Mono (Scheme.Spec.map (CommRingCat.ofHom (R := H) (S := OpenCellRing l) (openCellRingHom l)).op))

/-- The open cell ring is of finite type over `k`. -/
instance [Algebra.FiniteType k H] : Algebra.FiniteType k (OpenCellRing l) := by
  have h1 : ∀ (B C : Type u) [CommRing B] [CommRing C] [Algebra k B] [Algebra k C]
      [Algebra.FiniteType k B] [Algebra.FiniteType k C], Algebra.FiniteType k (B ⊗[k] C) :=
    fun B C _ _ _ _ _ _ => Algebra.FiniteType.trans (S := B) inferInstance inferInstance
  exact h1 _ _

/-- The open cell map is of finite presentation. -/
theorem finitePresentation_openCellRingHom [Algebra.FiniteType k H] :
    RingHom.FinitePresentation (A := H) (B := OpenCellRing l) (openCellRingHom l) := by
  have : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
  rw [← RingHom.FinitePresentation.of_finiteType]
  apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap k H)
  have h0 : (algebraMap k (OpenCellRing l)).FiniteType :=
    RingHom.finiteType_algebraMap.mpr inferInstance
  convert h0 using 1
  exact RingHom.ext fun r => (openCellMap l).commutes r

/-- **A flat open cell is an open embedding** on spectra. -/
theorem isOpenEmbedding_openCell_of_flat [Algebra.FiniteType k H]
    (hflat : RingHom.Flat (R := H) (S := OpenCellRing l) (openCellRingHom l)) :
    Topology.IsOpenEmbedding
      (PrimeSpectrum.comap (R := H) (S := OpenCellRing l) (openCellRingHom l)) := by
  let f : CommRingCat.of H ⟶ CommRingCat.of (OpenCellRing l) := CommRingCat.ofHom (R := H) (S := OpenCellRing l) (openCellRingHom l)
  have := mono_spec_openCellRingHom l
  have : Flat (Spec.map f) := HasRingHomProperty.Spec_iff.mpr hflat
  have : LocallyOfFinitePresentation (Spec.map f) :=
    HasRingHomProperty.Spec_iff.mpr (finitePresentation_openCellRingHom l)
  have hi := IsOpenImmersion.of_flat_of_mono (Spec.map f)
  exact (Spec.map f).isOpenEmbedding

/-- **Proposition 16.10 (ii) of Algebraic Magnetism, `k` algebraically closed, from a flat open
cell.** Let `G` be smooth and irreducible over `k = k̄`, `Φ` the roots, `f` a magnet map and
`N ⊆ f⁻¹(ℕ)` with `N ∩ Φ = f⁻¹(ℕ) ∩ Φ`. If the open cell map of `λ_f` is flat, then
`G^N = P(λ_f)`. -/
theorem magnetIdeal_eq_parabolic_of_openCell_flat {X : Type u} [CommGroup X] [DecidableEq X]
    [IsAlgClosed k] [Algebra.Smooth k H] [IrreducibleSpace (PrimeSpectrum H)]
    (π : H →ₐc[k] MonoidAlgebra k X) (ψ : X →* Multiplicative ℤ)
    {N : Magnet (Additive X)} (hN : N ≤ natMagnet.comap (pairingHom ψ))
    (hΦ : {α | α ∈ N} ∩ roots π = {α | α ∈ natMagnet.comap (pairingHom ψ)} ∩ roots π)
    (hflat : RingHom.Flat (R := H) (S := OpenCellRing (π.cocharacter ψ))
      (openCellRingHom (π.cocharacter ψ))) :
    magnetIdeal (torusGrading π) N =
      (parabolicDefiningHopfIdeal (π.cocharacter ψ)).toIdeal :=
  magnetIdeal_eq_parabolic_of_openCell π ψ hN hΦ
    (isOpenEmbedding_openCell_of_flat _ hflat)

end AlgMag.Reductive
