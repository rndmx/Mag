/-
Copyright (c) 2026 Kirill Kondrashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kirill Kondrashov, Oliver Nash
-/
/- Backport compat (not Tau Ceti code): truncated copy (wedge, wedgePairing, wedge_apply_of_not_disjoint only) of Mathlib 1b1ccf4 Mathlib/LinearAlgebra/ExteriorPower/WedgePairing.lean. -/

import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# Wedge pairing on exterior powers

Given a trivialisation of the top exterior power, the wedge pairing in complementary degrees
is a scalar-valued bilinear map. We construct this here and prove that it is a perfect pairing.

## Main definitions / results:
 * `exteriorPower.wedge`: the bilinear map `∧^k × ∧^l → ∧^(k + l)`
 * `exteriorPower.wedgePairing`: the bilinear map `∧^k × ∧^l → R` when `k + l` = top degree
 * `exteriorPower.instIsPerfPairWedgePairing`: the proof that `exteriorPower.wedgePairing` is
   perfect.

-/

noncomputable section

open Function Module Set

namespace exteriorPower

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] (k l : ℕ)

/-- The wedge product as an operation on exterior powers. -/
abbrev wedge :
    ⋀[R]^k M →ₗ[R] ⋀[R]^l M →ₗ[R] ⋀[R]^(k + l) M :=
  DirectSum.gMulLHom R <| fun d ↦ ⋀[R]^d M

variable {R M k l} (vol : ⋀[R]^(finrank R M) M ≃ₗ[R] R) (hkl : k + l = finrank R M)

/-- The wedge product in complementary degrees as a scalar-valued bilinear map (for a choice of
trivialisation of the top exterior power). -/
abbrev wedgePairing :
    ⋀[R]^k M →ₗ[R] ⋀[R]^l M →ₗ[R] R :=
  (wedge R M k l).compr₂ (hkl ▸ vol)

/-- An auxiliary lemma for `exteriorPower.wedgePairing_eq_apply_topVector_smul`. -/
lemma apply_eqRec {N : Type*} [AddCommGroup N] [Module R N]
    (h : k = l) (f : ⋀[R]^l M →ₗ[R] N)
    {x : ⋀[R]^k M} {y : ⋀[R]^l M} (hxy : (x : ExteriorAlgebra R M) = y) :
    (h ▸ f) x = f y := by
  subst h
  exact congrArg f (Subtype.ext hxy)

section Basis

variable {ι : Type*} [LinearOrder ι] (b : Basis ι R M)

lemma wedge_apply_of_not_disjoint
    {I : powersetCard ι k} {J : powersetCard ι l} (h : ¬ Disjoint I.val J.val) :
    wedge R M k l (b.exteriorPower k I) (b.exteriorPower l J) = 0 := by
  ext
  simp_rw [DirectSum.gMulLHom_apply_apply, SetLike.coe_gMul, ← ExteriorAlgebra.basis_eq_coe_basis,
    ZeroMemClass.coe_zero, ExteriorAlgebra.basis_mul_of_not_disjoint b I J h]

end Basis

end exteriorPower

end
