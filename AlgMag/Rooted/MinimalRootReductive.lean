/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Rooted.ReductivePure
import AlgMag.Rooted.MinimalRoot

/-!
# Theorem `thm:red-classification` (ii) and the minimal root of Theorem `thm:red-rooted`

Same abstract setting as `AlgMag.Rooted.ReductivePure`: `Y N` is the attractor of `N`, and the
hypotheses `hdet`, `hrefl` are Theorem `thm:red-attractors` (iii), (i).

* `reductive_classification_ii`: for `R ⊆ Φ` additively stable (`[R⟩ ∩ Φ = R`),
  `E(G^{[R⟩})` is a pure magnet with `E(G^{[R⟩}) ∩ Φ = R`.
* `joinIrreducibles_reductive`: the minimal root is
  `{ℕα | α ∈ Φ} ∪ {Z_w | Z_w ≠ [Φ ∩ Z_w⟩ + Σ_{Z_v ⊊ Z_w} Z_v}`.
  Here `[Φ ∩ Z_w⟩` is the submonoid generated; it equals `ℤ(Φ ∩ Z_w)` as soon as `Φ = -Φ`
  (`Z_w` is a group). Combinatorial hypotheses: `0 ∉ Φ`, `ℕα ∩ -ℕα = 0` and `ℕα ∩ Φ = {α}`
  for `α ∈ Φ` (reduced root system in a lattice).
-/

namespace AlgMag.Rooted

variable {M : Type*} [AddCommGroup M] {Φ : Set M} {W : Type*} {act : W → M →+ M}
variable {α : Type*} {Y : AddSubmonoid M → α}

lemma neg_mem_weylMagnet {w : M →+ M} {x : M} (hx : x ∈ weylMagnet w) : -x ∈ weylMagnet w := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨-y, by simp only [AddMonoidHom.sub_apply, AddMonoidHom.id_apply, map_neg]⟩

/-- The sum appearing in the minimal-root formula. -/
def weylMagnetLower (Φ : Set M) (act : W → M →+ M) (w : W) : AddSubmonoid M :=
  AddSubmonoid.closure ((weylMagnet (act w) : Set M) ∩ Φ) ⊔
    ⨆ v ∈ {v | weylMagnet (act v) < weylMagnet (act w)}, weylMagnet (act v)

variable
  (hdet : ∀ N L : AddSubmonoid M, L ≤ N → (∀ a ∈ Φ, a ∈ N → a ∈ L) →
    (∀ w, weylMagnet (act w) ≤ N → weylMagnet (act w) ≤ L) → Y L = Y N)
  (hrefl : ∀ N L : AddSubmonoid M, Y N = Y L →
    (∀ a ∈ Φ, a ∈ N → a ∈ L) ∧ ∀ w, weylMagnet (act w) ≤ N → weylMagnet (act w) ≤ L)
include hdet hrefl
set_option linter.unusedSectionVars false

/-- **Theorem `thm:red-classification` (ii).** For `R ⊆ Φ` additively stable, `E(G^{[R⟩})`
(the least magnet with the attractor of `[R⟩`) is pure and meets `Φ` in `R`. -/
theorem reductive_classification_ii {R : Set M} (hRΦ : R ⊆ Φ)
    (hR : (AddSubmonoid.closure R : Set M) ∩ Φ = R) :
    IsPure Y (sInf {L | Y L = Y (AddSubmonoid.closure R)}) ∧
      ((sInf {L | Y L = Y (AddSubmonoid.closure R)} : AddSubmonoid M) : Set M) ∩ Φ = R := by
  rw [← reductiveHull_eq_pureOf hdet hrefl]
  refine ⟨(reductiveInput_of_attractors hdet hrefl).hull_pure _, ?_⟩
  apply Set.Subset.antisymm
  · rintro a ⟨ha, haΦ⟩
    rw [← hR]; exact ⟨reductiveHull_le _ ha, haΦ⟩
  · intro a ha
    exact ⟨mem_reductiveHull_of_root (hRΦ ha) (AddSubmonoid.subset_closure ha), hRΦ ha⟩

/-- Surjectivity form of `thm:red-classification` (ii). -/
theorem reductive_classification_ii_surj {R : Set M} (hRΦ : R ⊆ Φ)
    (hR : (AddSubmonoid.closure R : Set M) ∩ Φ = R) :
    ∃ N, IsPure Y N ∧ (N : Set M) ∩ Φ = R :=
  ⟨_, reductive_classification_ii hdet hrefl hRΦ hR⟩

/-- With `Φ` and `W` finite, `Π(a)` is finite and the set of `joinIrreducibles_reductive` is the unique
minimal root. -/
theorem joinIrreducibles_reductive_isLeast [Finite W] (hΦ : Φ.Finite) :
    IsJoinDense (IsPure Y) (joinIrreducibles (IsPure Y)) ∧
      ∀ Ψ, IsJoinDense (IsPure Y) Ψ → joinIrreducibles (IsPure Y) ⊆ Ψ :=
  ⟨isJoinDense_joinIrreducibles (finite_pure hdet hrefl hΦ).wellFoundedOn
      (reductive_joinDense_of_attractors hdet hrefl),
    fun _ hΨ => joinIrreducibles_subset hΨ⟩

variable (h0 : (0 : M) ∉ Φ)
  (hcone : ∀ a ∈ Φ, ∀ x, x ∈ mono a → -x ∈ mono a → x = 0)
  (hred : ∀ a ∈ Φ, ∀ b ∈ Φ, b ∈ mono a → b = a)
include h0 hcone hred

/-- The pure magnets strictly below `ℕα` are `0`. -/
lemma pure_lt_mono_eq_bot {a : M} (ha : a ∈ Φ) {L : AddSubmonoid M} (hL : IsPure Y L)
    (hlt : L < mono a) : L = ⊥ := by
  have H := reductiveInput_of_attractors hdet hrefl
  rw [(H.pure_iff L).1 hL]
  refine le_antisymm (sup_le (AddSubmonoid.closure_le.2 ?_) (iSup₂_le fun w hw => ?_)) bot_le
  · rintro b ⟨hbL, hbΦ⟩
    have hb := hred a ha b hbΦ (hlt.le hbL); subst hb
    exact absurd (hlt.le.antisymm (mono_le_iff.2 hbL)) hlt.ne
  · intro x hx
    have := hcone a ha x (hlt.le (hw hx)) (hlt.le (hw (neg_mem_weylMagnet hx)))
    simp [this]

/-- The sum of the pure magnets strictly below `Z_w`. -/
lemma sSup_pure_lt_weylMagnet (w : W) :
    sSup {L | IsPure Y L ∧ L < weylMagnet (act w)} = weylMagnetLower Φ act w := by
  have H := reductiveInput_of_attractors hdet hrefl
  have R := reductive_joinDense H
  apply le_antisymm
  · refine sSup_le fun L ⟨hL, hlt⟩ => ?_
    rw [(H.pure_iff L).1 hL]
    refine sup_le_sup (AddSubmonoid.closure_mono fun b hb => ⟨hlt.le hb.1, hb.2⟩) ?_
    exact iSup₂_le fun v hv => le_iSup₂_of_le (f := fun v
      (_ : v ∈ {v | weylMagnet (act v) < weylMagnet (act w)}) => weylMagnet (act v)) v
      (lt_of_le_of_lt hv hlt) le_rfl
  · refine sup_le (AddSubmonoid.closure_le.2 ?_) (iSup₂_le fun v hv => ?_)
    · rintro b ⟨hbZ, hbΦ⟩
      have hle : mono b ≤ weylMagnet (act w) := mono_le_iff.2 hbZ
      have hne : mono b ≠ weylMagnet (act w) := by
        intro he
        have hneg : -b ∈ mono b := he ▸ neg_mem_weylMagnet hbZ
        have := hcone b hbΦ b (mono_le_iff.1 le_rfl) hneg
        exact h0 (this ▸ hbΦ)
      exact mono_le_iff.1 (le_sSup ⟨R.pure_of_mem (Or.inl ⟨b, hbΦ, rfl⟩), lt_of_le_of_ne hle hne⟩)
    · exact le_sSup ⟨R.pure_of_mem (Or.inr ⟨v, rfl⟩), hv⟩

/-- **Theorem `thm:red-rooted`, minimal root.** The sum-irreducible pure magnets are the
classical roots `ℕα` and the Weyl magnets `Z_w` with `Z_w ≠ [Φ ∩ Z_w⟩ + Σ_{Z_v ⊊ Z_w} Z_v`. -/
theorem joinIrreducibles_reductive :
    joinIrreducibles (IsPure Y) = mono '' Φ ∪
      {Z | ∃ w, Z = weylMagnet (act w) ∧ weylMagnet (act w) ≠ weylMagnetLower Φ act w} := by
  have R := reductive_joinDense (reductiveInput_of_attractors hdet hrefl)
  ext X
  constructor
  · intro hX
    rcases joinIrreducibles_subset R hX with hm | ⟨w, rfl⟩
    · exact Or.inl hm
    · refine Or.inr ⟨w, rfl, ?_⟩
      rw [← sSup_pure_lt_weylMagnet hdet hrefl h0 hcone hred]
      exact hX.2
  · rintro (⟨a, ha, rfl⟩ | ⟨w, rfl, hw⟩)
    · refine ⟨R.pure_of_mem (Or.inl ⟨a, ha, rfl⟩), ?_⟩
      have : sSup {L | IsPure Y L ∧ L < mono a} = ⊥ :=
        le_antisymm (sSup_le fun L hL =>
          (pure_lt_mono_eq_bot hdet hrefl h0 hcone hred ha hL.1 hL.2).le) bot_le
      rw [this]
      intro he
      have h1 : a ∈ (⊥ : AddSubmonoid M) := he ▸ mono_le_iff.1 le_rfl
      rw [AddSubmonoid.mem_bot] at h1
      exact h0 (h1 ▸ ha)
    · refine ⟨R.pure_of_mem (Or.inr ⟨w, rfl⟩), ?_⟩
      rw [sSup_pure_lt_weylMagnet hdet hrefl h0 hcone hred]
      exact hw

end AlgMag.Rooted
