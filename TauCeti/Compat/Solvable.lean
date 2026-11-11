/-
Copyright (c) 2026 Xavier Roblot (isSimpleGroup_of_isCoatom). Released under Apache 2.0 license.
Backport (compat, not Tau Ceti code), 2026-11-10: statement copied from Mathlib 1b1ccf4
`Mathlib/GroupTheory/QuotientGroup/Simple.lean` (module absent in 16edf57); the proof is rewritten
(the 1b1ccf4 proof uses order-isomorphism API absent in 16edf57). See TauCeti/CHANGES.md.
-/
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.Solvable

/-- The quotient by a normal coatom is a simple group. -/
theorem Group.isSimpleGroup_of_isCoatom {G : Type*} [Group G] {M : Subgroup G} [M.Normal]
    (h : IsCoatom M) : IsSimpleGroup (G ⧸ M) := by
  obtain ⟨g, hg⟩ : ∃ g, g ∉ M := by
    by_contra hc
    push_neg at hc
    exact h.1 (eq_top_iff.2 fun g _ => hc g)
  haveI : Nontrivial (G ⧸ M) := ⟨⟨(g : G ⧸ M), 1, by rwa [Ne, QuotientGroup.eq_one_iff]⟩⟩
  refine { eq_bot_or_eq_top_of_normal := fun N _ => ?_ }
  have hle : M ≤ N.comap (QuotientGroup.mk' M) := fun x hx => by
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]
    exact N.one_mem
  rcases hle.eq_or_lt with heq | hlt
  · left
    rw [eq_bot_iff]
    intro y hy
    induction y using QuotientGroup.induction_on with
    | H x =>
      have hx : x ∈ N.comap (QuotientGroup.mk' M) := hy
      rw [← heq] at hx
      exact Subgroup.mem_bot.2 ((QuotientGroup.eq_one_iff x).2 hx)
  · right
    have htop := h.2 _ hlt
    rw [eq_top_iff]
    intro y _
    induction y using QuotientGroup.induction_on with
    | H x =>
      have hx : x ∈ N.comap (QuotientGroup.mk' M) := htop ▸ Subgroup.mem_top x
      exact hx