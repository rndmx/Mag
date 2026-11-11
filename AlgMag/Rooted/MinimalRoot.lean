/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Rooted.RootedBasic
import Mathlib.Order.WellFoundedSet

/-!
# The minimal root

`algmag-notes/reductive/reductive-rooted.md`, Proposition M. If an action is rooted by some `Φ`,
the pure magnets are closed under sums and every member of a root is pure. When the pure magnets
are well-founded under `<` (e.g. finitely many), the sum-irreducible pure magnets
`Φ_min = {X pure : X ≠ Σ {Y pure : Y ⊊ X}}`
form a root contained in every root; hence the minimal root exists and is unique.
-/

namespace AlgMag.Rooted

variable {M : Type*} [AddCommMonoid M] {P : AddSubmonoid M → Prop}

/-- The sum-irreducible pure magnets. -/
def joinIrreducibles (P : AddSubmonoid M → Prop) : Set (AddSubmonoid M) :=
  {X | P X ∧ X ≠ sSup {Y | P Y ∧ Y < X}}

/-- Every sum-irreducible pure magnet lies in every root. -/
theorem joinIrreducibles_subset {Φ : Set (AddSubmonoid M)} (R : IsJoinDense P Φ) : joinIrreducibles P ⊆ Φ := by
  intro X hX
  by_contra hXΦ
  have hsp : X ∈ span Φ := by
    rw [← isJoinDense_iff_eq_span.1 R]
    exact hX.1
  obtain ⟨E, hE, hEX⟩ := hsp
  have hlt : ∀ I ∈ E, P I ∧ I < X := by
    intro I hI
    have hle : I ≤ X := by rw [← hEX]; exact le_sSup hI
    refine ⟨R.pure_of_mem (hE hI), lt_of_le_of_ne hle ?_⟩
    rintro rfl
    exact hXΦ (hE hI)
  apply hX.2
  refine le_antisymm ?_ (sSup_le fun Y hY => hY.2.le)
  calc X = sSup E := hEX.symm
    _ ≤ sSup {Y | P Y ∧ Y < X} := sSup_le_sSup fun I hI => hlt I hI

/-- Under well-foundedness, every pure magnet is the sum of the irreducibles it contains. -/
theorem sSup_joinIrreducibles_le (hwf : ({N | P N} : Set (AddSubmonoid M)).WellFoundedOn (· < ·)) {X : AddSubmonoid M}
    (hX : P X) : sSup {Y | Y ∈ joinIrreducibles P ∧ Y ≤ X} = X := by
  refine Set.WellFoundedOn.induction hwf hX
    (P := fun X => sSup {Y | Y ∈ joinIrreducibles P ∧ Y ≤ X} = X) ?_
  intro X hX ih
  have ih : ∀ Z, P Z → Z < X → sSup {Y | Y ∈ joinIrreducibles P ∧ Y ≤ Z} = Z := fun Z hZ hZX => ih Z hZ hZX
  refine le_antisymm (sSup_le fun Y hY => hY.2) ?_
  by_cases hm : X ∈ joinIrreducibles P
  · exact le_sSup ⟨hm, le_rfl⟩
  · have hX' : X = sSup {Y | P Y ∧ Y < X} := by
      by_contra hne
      exact hm ⟨hX, hne⟩
    calc X = sSup {Y | P Y ∧ Y < X} := hX'
      _ ≤ sSup {Y | Y ∈ joinIrreducibles P ∧ Y ≤ X} := sSup_le fun Y hY => by
          calc Y = sSup {Z | Z ∈ joinIrreducibles P ∧ Z ≤ Y} := (ih Y hY.1 hY.2).symm
            _ ≤ sSup {Y | Y ∈ joinIrreducibles P ∧ Y ≤ X} := sSup_le_sSup fun Z (hZ : Z ∈ joinIrreducibles P ∧ Z ≤ Y) =>
              (⟨hZ.1, hZ.2.trans hY.2.le⟩ : Z ∈ joinIrreducibles P ∧ Z ≤ X)

/-- If the action is rooted by some `Φ`, then `Φ_min` is a root. -/
theorem isJoinDense_joinIrreducibles (hwf : ({N | P N} : Set (AddSubmonoid M)).WellFoundedOn (· < ·)) {Φ : Set (AddSubmonoid M)}
    (R : IsJoinDense P Φ) : IsJoinDense P (joinIrreducibles P) := by
  rw [isJoinDense_iff_eq_span]
  ext X
  constructor
  · intro hX
    exact (⟨{Y | Y ∈ joinIrreducibles P ∧ Y ≤ X}, fun _ hY => hY.1, sSup_joinIrreducibles_le hwf hX⟩ :
      ∃ E ⊆ joinIrreducibles P, sSup E = X)
  · rintro ⟨E, hE, rfl⟩
    exact R.pure_sSup fun N hN => (hE hN).1

/-- **Proposition M (c), abstract form.** The minimal root exists, is unique, and is contained in
every root. -/
theorem existsUnique_minimal_root (hwf : ({N | P N} : Set (AddSubmonoid M)).WellFoundedOn (· < ·))
    (h : ∃ Φ, IsJoinDense P Φ) :
    ∃! Φ₀ : Set (AddSubmonoid M), IsJoinDense P Φ₀ ∧ ∀ Φ, IsJoinDense P Φ → Φ₀ ⊆ Φ := by
  obtain ⟨Φ, R⟩ := h
  refine ⟨joinIrreducibles P, ⟨isJoinDense_joinIrreducibles hwf R, fun Ψ hΨ => joinIrreducibles_subset hΨ⟩, ?_⟩
  rintro Φ₀ ⟨h0, hmin⟩
  exact le_antisymm (hmin _ (isJoinDense_joinIrreducibles hwf R)) (joinIrreducibles_subset h0)

/-- Finite version. -/
theorem existsUnique_minimal_root_of_finite (hfin : ({N | P N} : Set (AddSubmonoid M)).Finite)
    (h : ∃ Φ, IsJoinDense P Φ) :
    ∃! Φ₀ : Set (AddSubmonoid M), IsJoinDense P Φ₀ ∧ ∀ Φ, IsJoinDense P Φ → Φ₀ ⊆ Φ :=
  existsUnique_minimal_root hfin.wellFoundedOn h

end AlgMag.Rooted
