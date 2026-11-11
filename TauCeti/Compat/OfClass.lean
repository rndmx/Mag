/-
Copyright: the Mathlib contributors (see the source files named below).
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from Tau Ceti (github.com/TauCetiProject/TauCeti, commit d2083f0); see TauCeti/CHANGES.md
-/
import Mathlib.RingTheory.Coalgebra.Hom
import Mathlib.Algebra.Algebra.Hom

/-!
# Backport (compat, not Tau Ceti code)

Newer Mathlib (1b1ccf4, `Mathlib/Algebra/Algebra/Hom.lean`, `Mathlib/RingTheory/Coalgebra/Hom.lean`)
renamed `AlgHomClass.toAlgHom` to `AlgHom.ofClass`, `CoalgHomClass.toCoalgHom` to
`CoalgHom.ofClass`, and `AlgHomClass.toLinearMap_toAlgHom` to
`AlgHomClass.linearMapOfClass_ofClass`. These are abbreviations to the 16edf57 declarations.
-/

abbrev AlgHom.ofClass {R A B F : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [FunLike F A B] [AlgHomClass F R A B] (f : F) : A →ₐ[R] B :=
  AlgHomClass.toAlgHom f

abbrev CoalgHom.ofClass {R A B F : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
    [AddCommMonoid B] [Module R B] [CoalgebraStruct R A] [CoalgebraStruct R B] [FunLike F A B]
    [CoalgHomClass F R A B] (f : F) : A →ₗc[R] B :=
  CoalgHomClass.toCoalgHom f

alias AlgHomClass.linearMapOfClass_ofClass := AlgHomClass.toLinearMap_toAlgHom

/-! 1b1ccf4 `Mathlib/RingTheory/Coalgebra/Hom.lean` renamed `CoalgHom.toLinearMap_eq_coe`,
`CoalgHom.coe_toLinearMap`, `CoalgHom.coe_linearMap_injective` (kept there as deprecated aliases). -/
alias CoalgHom.toLinearMap_eq_ofClass := CoalgHom.toLinearMap_eq_coe
alias CoalgHom.coe_linearMapOfClass := CoalgHom.coe_toLinearMap
alias CoalgHom.linearMapOfClass_injective := CoalgHom.coe_linearMap_injective
