/-
Copyright: the Mathlib contributors (see the source files named below).
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from Tau Ceti (github.com/TauCetiProject/TauCeti, commit d2083f0); see TauCeti/CHANGES.md
-/
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.Algebra.Equiv

/-!
# Backport (compat, not Tau Ceti code): renamed or new Mathlib lemmas

Mathlib 1b1ccf4 names used by Tau Ceti, provided on Mathlib 16edf57.
* `LinearMap.baseChange_eq_lTensor` (1b1ccf4 `LinearAlgebra/TensorProduct/Tower.lean`):
  alias of 16edf57 `LinearMap.baseChange_eq_ltensor`.
* `Abelianization.commutator_le_ker` (1b1ccf4 `GroupTheory/Abelianization/Defs.lean`):
  alias of 16edf57 `Abelianization.commutator_subset_ker` (stated there for `[CommGroup A]`;
  1b1ccf4 uses `[Group A] [IsMulCommutative A]`).
* `IsConcreteLE.le_iff` (1b1ccf4 `Basic/SetLike/Basic.lean`, a class field there):
  alias of 16edf57 `SetLike.le_def`.
* `AlgEquiv.coe_toRingEquiv` (1b1ccf4 `Algebra/Algebra/Equiv.lean`): alias of 16edf57
  `AlgEquiv.coe_ringEquiv`.
* `IsUnit.map_ringInverse`, `map_ringInverse` (1b1ccf4 `Algebra/GroupWithZero/Units/Lemmas.lean`),
  copied with `.ofClass f` written as `(f : M₀ →* M₀')`.
-/

alias LinearMap.baseChange_eq_lTensor := LinearMap.baseChange_eq_ltensor

alias Abelianization.commutator_le_ker := Abelianization.commutator_subset_ker

alias IsConcreteLE.le_iff := SetLike.le_def

alias AlgEquiv.coe_toRingEquiv := AlgEquiv.coe_ringEquiv

open scoped Ring

section
variable {M₀ M₀' F : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] [FunLike F M₀ M₀']

protected theorem IsUnit.map_ringInverse [MonoidHomClass F M₀ M₀'] (f : F) {a : M₀} (h : IsUnit a) :
    f a⁻¹ʳ = (f a)⁻¹ʳ := by
  lift a to M₀ˣ using h
  simpa [Ring.inverse_unit] using (Ring.inverse_unit (Units.map (f : M₀ →* M₀') a)).symm

/-- A homomorphism which reflects units commutes with `Ring.inverse`. -/
theorem map_ringInverse [MonoidWithZeroHomClass F M₀ M₀'] (f : F) [IsLocalHom f] (a : M₀) :
    f a⁻¹ʳ = (f a)⁻¹ʳ := by
  by_cases h : IsUnit a
  · exact h.map_ringInverse f
  · rw [Ring.inverse_non_unit _ h, Ring.inverse_non_unit _ (h <| IsUnit.of_map f a ·), map_zero]

end

/-- 1b1ccf4 `Mathlib/Data/Finsupp/Basic.lean` name of 16edf57 `Finsupp.mapDomain_apply`. -/
alias Finsupp.mapDomain_apply_of_injective := Finsupp.mapDomain_apply
