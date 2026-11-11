/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Algebra.MonoidAlgebra.Grading
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Tactic.SuppressCompilation
import AlgMag.Affine.Magnet

/-!
# The `M`-graded algebra `C[N]` attached to a magnet

For a magnet `N` of `M` and a ring `C`, the paper's `C[N]` is the monoid algebra of `N`
regarded as an `M`-graded algebra: its degree `m` part is `C · X^m` if `m ∈ N` and `0`
otherwise.

This is exactly Mathlib's `AddMonoidAlgebra.gradeBy C ⇑N.subtype`, so the
`GradedAlgebra` instance comes for free.
-/

suppress_compilation

namespace Magnetism

open AddMonoidAlgebra

variable {M : Type*} [AddCommMonoid M] [DecidableEq M] (N : Magnet M)
variable (C : Type*) [CommRing C]

/-- The `M`-grading on `C[N]`: degree `m` is `C · X^m` for `m ∈ N`, and `0` otherwise. -/
abbrev magnetGrading : M → Submodule C (AddMonoidAlgebra C N) :=
  AddMonoidAlgebra.gradeBy C (⇑(AddSubmonoid.subtype N))

example : GradedAlgebra (magnetGrading N C) := inferInstance

variable {N C}

lemma single_mem_magnetGrading (n : N) (c : C) :
    AddMonoidAlgebra.single n c ∈ magnetGrading N C (n : M) :=
  AddMonoidAlgebra.single_mem_gradeBy _ _ _

/-- Off the magnet, `C[N]` has no homogeneous part. -/
lemma magnetGrading_eq_bot {m : M} (hm : m ∉ N) : magnetGrading N C m = ⊥ := by
  refine le_antisymm (fun a ha => ?_) bot_le
  rw [Submodule.mem_bot]
  refine AddMonoidAlgebra.coeff_inj.mp (Finsupp.ext fun n => ?_)
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
  by_contra hn
  exact hm ((ha n (Finsupp.mem_support_iff.mpr hn)) ▸ n.2)

/-- A homogeneous element of `C[N]` of degree `m ∈ N` is a single monomial. -/
lemma exists_single_of_mem_magnetGrading {m : M} (hm : m ∈ N) {a : AddMonoidAlgebra C N}
    (ha : a ∈ magnetGrading N C m) : ∃ c : C, a = AddMonoidAlgebra.single ⟨m, hm⟩ c := by
  refine ⟨a.coeff ⟨m, hm⟩, AddMonoidAlgebra.coeff_inj.mp (Finsupp.ext fun n => ?_)⟩
  rw [AddMonoidAlgebra.coeff_single]
  by_cases hn : n = ⟨m, hm⟩
  · subst hn; simp
  · rw [Finsupp.single_eq_of_ne hn]
    by_contra h
    exact hn (Subtype.ext (ha n (Finsupp.mem_support_iff.mpr h)))

variable (N C)

/-- The augmentation `C[N] → C`, `X^n ↦ 1`. -/
def magnetAug : AddMonoidAlgebra C N →ₐ[C] C :=
  AddMonoidAlgebra.lift C C N 1

@[simp] lemma magnetAug_single (n : N) (c : C) :
    magnetAug N C (AddMonoidAlgebra.single n c) = c := by
  simp [magnetAug, AddMonoidAlgebra.lift_single]

end Magnetism
