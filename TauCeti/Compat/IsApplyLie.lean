/-
Copyright: the Mathlib contributors (see the source file named below).
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from Tau Ceti (github.com/TauCetiProject/TauCeti, commit d2083f0); see TauCeti/CHANGES.md
-/
import Mathlib.Data.FunLike.IsApply
import Mathlib.Algebra.Lie.Basic

/-!
# Backport (compat, not Tau Ceti code): `IsOneApplyEqSelf` for Lie morphisms

From Mathlib 1b1ccf4 `Mathlib/Algebra/Lie/Basic.lean`: `IsOneApplyEqSelf` instances for
`L →ₗ⁅R⁆ L`, `L ≃ₗ⁅R⁆ L`, `M →ₗ⁅R,L⁆ M`, `M ≃ₗ⁅R,L⁆ M`. Fields given by `rfl`.
-/

section
variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

instance LieHom.instIsOneApplyEqSelfCompat : IsOneApplyEqSelf (L →ₗ⁅R⁆ L) L where
  one_apply_eq_self _ := rfl

instance LieEquiv.instIsOneApplyEqSelfCompat : IsOneApplyEqSelf (L ≃ₗ⁅R⁆ L) L where
  one_apply_eq_self _ := rfl

variable {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

instance LieModuleHom.instIsOneApplyEqSelfCompat : IsOneApplyEqSelf (M →ₗ⁅R,L⁆ M) M where
  one_apply_eq_self _ := rfl

instance LieModuleEquiv.instIsOneApplyEqSelfCompat : IsOneApplyEqSelf (M ≃ₗ⁅R,L⁆ M) M where
  one_apply_eq_self _ := rfl

end
