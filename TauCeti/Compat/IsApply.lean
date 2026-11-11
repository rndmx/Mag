/-
Copyright: the Mathlib contributors (see the source files named below).
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from Tau Ceti (github.com/TauCetiProject/TauCeti, commit d2083f0); see TauCeti/CHANGES.md
-/
import Mathlib.Data.FunLike.IsApply
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.RingTheory.Derivation.Basic

/-!
# Backport (compat, not Tau Ceti code): `Is*Apply` instances

Mathlib 16edf57 already has `Mathlib/Data/FunLike/IsApply.lean` (with explicit `α β` arguments),
but lacks instances that Mathlib 1b1ccf4 declares in
* `Mathlib/Algebra/Module/LinearMap/End.lean`: `IsOneApplyEqSelf`, `IsMulApplyEqComp` for `Module.End`;
* `Mathlib/RingTheory/Derivation/Basic.lean`: `IsZeroApply`, `IsAddApply`, `IsSMulApply`
  for `Derivation`.
All proofs are `rfl`, as upstream.
-/

namespace Module.End
variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

instance : IsOneApplyEqSelf (End R M) M where
  one_apply_eq_self _ := rfl

instance : IsMulApplyEqComp (End R M) M where
  mul_apply_eq_comp _ _ _ := rfl

end Module.End

namespace Derivation
variable {R A M : Type*} [CommSemiring R] [CommSemiring A] [AddCommMonoid M] [Algebra R A]
  [Module A M] [Module R M]

instance : IsZeroApply (Derivation R A M) A M where
  zero_apply _ := rfl

instance : IsAddApply (Derivation R A M) A M where
  add_apply _ _ _ := rfl

variable {S : Type*} [Monoid S] [DistribMulAction S M] [SMulCommClass R S M] [SMulCommClass S A M]

instance : IsSMulApply S (Derivation R A M) A M where
  smul_apply _ _ _ := rfl

end Derivation
