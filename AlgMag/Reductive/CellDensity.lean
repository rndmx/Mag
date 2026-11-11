/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Irreducible

/-!
# Density of an open cell: injectivity of the comorphism

If `Spec R → Spec L` is an open embedding with nonempty source, `Spec L` is irreducible and `L` is
reduced, then `L → R` is injective: a function on `L` vanishing on a nonempty open subset vanishes.
For the open cell `U⁻ × Z × U⁺ → G` of a smooth connected group this says that an identity of
regular functions checked on the cell holds on `G`.
-/

namespace AlgMag.Reductive

universe u v

/-- **Functions vanishing on a nonempty open subset of an integral scheme vanish.** -/
theorem injective_of_isOpenEmbedding_comap {L : Type u} {R : Type v} [CommRing L] [CommRing R]
    [IsReduced L] [IrreducibleSpace (PrimeSpectrum L)] [Nontrivial R] (f : L →+* R)
    (hf : Topology.IsOpenEmbedding (PrimeSpectrum.comap f)) : Function.Injective f := by
  have hne : (Set.range (PrimeSpectrum.comap f)).Nonempty := by
    obtain ⟨q⟩ := (inferInstance : Nonempty (PrimeSpectrum R))
    exact ⟨_, q, rfl⟩
  have hdense : DenseRange (PrimeSpectrum.comap f) := hf.isOpen_range.dense hne
  have hker := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f).1 hdense
  rw [nilradical_eq_zero, Submodule.zero_eq_bot] at hker
  exact (RingHom.injective_iff_ker_eq_bot f).2 (le_bot_iff.1 hker)

end AlgMag.Reductive
