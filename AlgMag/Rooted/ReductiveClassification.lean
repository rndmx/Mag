/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Rooted.ReductivePure

/-!
# Classification of pure magnets by pairs (Theorem `thm:red-classification` (i))

For `R ⊆ M` and `W' ⊆ W` put `L(R, W') = [R⟩ + Σ_{w ∈ W'} (1 - w)M` (`pairMagnet`). A pair is
*compatible* if `Φ ∩ L(R, W') = R` and `{w | (1 - w)M ⊆ L(R, W')} = W'`. Given `ReductiveInput`
(Theorem `thm:red-pure`), `N ↦ (N ∩ Φ, W_N)` is a bijection from the pure magnets onto the
compatible pairs, with inverse `(R, W') ↦ L(R, W')` (`bijOn_pairOf`).
-/

namespace AlgMag.Rooted

variable {M : Type*} [AddCommGroup M] {Φ : Set M} {W : Type*} {act : W → M →+ M}

/-- `L(R, W') = [R⟩ + Σ_{w ∈ W'} (1 - w)M`. -/
def pairMagnet (act : W → M →+ M) (R : Set M) (W' : Set W) : AddSubmonoid M :=
  AddSubmonoid.closure R ⊔ ⨆ w ∈ W', weylMagnet (act w)

/-- The pair `(R(N), W_N) = (N ∩ Φ, {w | (1 - w)M ⊆ N})`. -/
def pairOf (Φ : Set M) (act : W → M →+ M) (N : AddSubmonoid M) : Set M × Set W :=
  ((N : Set M) ∩ Φ, {w | weylMagnet (act w) ≤ N})

/-- Compatible pairs: `Φ ∩ L(R, W') = R` and `{w | (1 - w)M ⊆ L(R, W')} = W'`. -/
def IsCompatiblePair (Φ : Set M) (act : W → M →+ M) (p : Set M × Set W) : Prop :=
  pairOf Φ act (pairMagnet act p.1 p.2) = p

lemma isCompatiblePair_iff {R : Set M} {W' : Set W} :
    IsCompatiblePair Φ act (R, W') ↔
      (pairMagnet act R W' : Set M) ∩ Φ = R ∧
        {w | weylMagnet (act w) ≤ pairMagnet act R W'} = W' :=
  Prod.ext_iff

lemma pairMagnet_pairOf (N : AddSubmonoid M) :
    pairMagnet act (pairOf Φ act N).1 (pairOf Φ act N).2 = reductiveHull Φ act N := rfl

variable {P : AddSubmonoid M → Prop}

/-- **Theorem `thm:red-classification` (i).** `N ↦ (R(N), W_N)` is a bijection from the pure
magnets onto the compatible pairs, with inverse `(R, W') ↦ L(R, W')`. -/
theorem bijOn_pairOf (H : ReductiveInput P Φ act) :
    Set.BijOn (pairOf Φ act) {N | P N} {p | IsCompatiblePair Φ act p} ∧
      Set.InvOn (fun p : Set M × Set W => pairMagnet act p.1 p.2) (pairOf Φ act)
        {N | P N} {p | IsCompatiblePair Φ act p} := by
  have hN : ∀ N, P N → pairMagnet act (pairOf Φ act N).1 (pairOf Φ act N).2 = N :=
    fun N h => ((H.pure_iff N).1 h).symm
  have hinv : Set.InvOn (fun p : Set M × Set W => pairMagnet act p.1 p.2) (pairOf Φ act)
      {N | P N} {p | IsCompatiblePair Φ act p} :=
    ⟨fun N h => hN N h, fun p h => h⟩
  refine ⟨hinv.bijOn (fun N h => ?_) (fun p h => ?_), hinv⟩
  · show pairOf Φ act (pairMagnet act _ _) = _
    rw [hN N h]
  · show P (pairMagnet act p.1 p.2)
    refine (H.pure_iff _).2 ?_
    rw [← pairMagnet_pairOf, show pairOf Φ act (pairMagnet act p.1 p.2) = p from h]

end AlgMag.Rooted
