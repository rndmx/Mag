/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.BorelRouteReal

/-!
# (Base±): one regular pair `±ν₀` with `P(±ν₀)` Borel

Ideals order subgroups contravariantly: `P ν ≤ B` means `V(B) ⊆ V(P ν)`.

* `eq_of_borel_le_of_candidate` (proved): a Borel `B ⊆ P(ν)` with `P(ν)` connected smooth
  solvable equals `P(ν)`; hence `P(ν)` is Borel.
* `basePair_of_core` (proved): (Base±) from the single named input `BaseCore C`.
* `BaseCore C` (named, NOT proved): one regular `ν₀` such that `P(ν₀)` and `P(−ν₀)` are
  Borel candidates (smooth, geometrically connected, geometrically solvable), each lying
  over some Borel.  The missing mathematical fact is solvability of `P(±ν₀)`, i.e.
  `Φ(G) = Φ(B) ⊔ −Φ(B)` for a Borel `B ⊇ T` (Borel 14.1 / Bruhat big cell); the inclusion
  `B ⊆ P(ν₀)` for generic positive `ν₀` is the dynamic description of `B`.
-/

open Magnetism TauCeti TauCeti.Cocharacter

namespace AlgMag.Reductive.BorBasePair

open AlgMag.Reductive.BorelRoute

universe u

variable {k : Type u} {H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H]

local notation "Hf" => FiniteTypeCommHopfAlgCat.of k H

/-- Maximality: a Borel `B ⊆ P(ν)` equals `P(ν)` once `P(ν)` is a Borel candidate. -/
theorem eq_of_borel_le_of_candidate {B I : HopfIdeal k H}
    (hB : HopfIdeal.IsBorelOverAlgClosed k Hf B) (hIB : I ≤ B)
    (hI : HopfIdeal.IsBorelCandidate k Hf I) : I = B :=
  le_antisymm hIB (hB.2.2 hI hIB)

theorem isBorel_of_borel_le_of_candidate {B I : HopfIdeal k H}
    (hB : HopfIdeal.IsBorelOverAlgClosed k Hf B) (hIB : I ≤ B)
    (hI : HopfIdeal.IsBorelCandidate k Hf I) : HopfIdeal.IsBorelOverAlgClosed k Hf I := by
  rwa [eq_of_borel_le_of_candidate hB hIB hI]

/-- **(Base±).** -/
def BasePair (C : HopfIdeal k H) : Prop :=
  ∃ ν : H →ₐc[k] LaurentPolynomial k, IsRegular C ν ∧
    HopfIdeal.IsBorelOverAlgClosed k Hf (P ν) ∧
    HopfIdeal.IsBorelOverAlgClosed k Hf (P ν.oppositeCocharacter)

/-- **The core (named input).** -/
def BaseCore (C : HopfIdeal k H) : Prop :=
  ∃ ν : H →ₐc[k] LaurentPolynomial k, IsRegular C ν ∧
    (∃ B, HopfIdeal.IsBorelOverAlgClosed k Hf B ∧ P ν ≤ B) ∧
    (∃ B', HopfIdeal.IsBorelOverAlgClosed k Hf B' ∧ P ν.oppositeCocharacter ≤ B') ∧
    HopfIdeal.IsBorelCandidate k Hf (P ν) ∧
    HopfIdeal.IsBorelCandidate k Hf (P ν.oppositeCocharacter)

theorem basePair_of_core {C : HopfIdeal k H} (h : BaseCore C) : BasePair C := by
  obtain ⟨ν, hν, ⟨B, hB, hPB⟩, ⟨B', hB', hPB'⟩, hc, hc'⟩ := h
  exact ⟨ν, hν, isBorel_of_borel_le_of_candidate hB hPB hc,
    isBorel_of_borel_le_of_candidate hB' hPB' hc'⟩

end AlgMag.Reductive.BorBasePair
