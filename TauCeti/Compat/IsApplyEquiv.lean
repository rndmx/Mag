/-
Copyright: the Mathlib contributors (see the source file named below).
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from Tau Ceti (github.com/TauCetiProject/TauCeti, commit d2083f0); see TauCeti/CHANGES.md
-/
import Mathlib.Data.FunLike.IsApply
import Mathlib.Algebra.Module.Equiv.Basic

/-!
# Backport (compat, not Tau Ceti code): `Is*Apply` instances for linear automorphisms

From Mathlib 1b1ccf4 `Mathlib/Algebra/Module/Equiv/Basic.lean`: `IsOneApplyEqSelf` and
`IsMulApplyEqComp` for `M ≃ₗ[R] M`. Fields given by `rfl` (16edf57 has no defaults).
-/

namespace LinearEquiv
variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

instance : IsOneApplyEqSelf (M ≃ₗ[R] M) M where
  one_apply_eq_self _ := rfl

instance : IsMulApplyEqComp (M ≃ₗ[R] M) M where
  mul_apply_eq_comp _ _ _ := rfl

end LinearEquiv
