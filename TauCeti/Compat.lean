/- Backport shim (not Tau Ceti code): newer-Mathlib names used by Tau Ceti. Released under Apache 2.0 license. 
Adapted from Tau Ceti (github.com/TauCetiProject/TauCeti, commit d2083f0); see TauCeti/CHANGES.md
-/
import Mathlib.LinearAlgebra.TensorProduct.Basic
namespace TensorProduct
variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
@[elab_as_elim, induction_eliminator]
protected theorem inductionOn {motive : M ⊗[R] N → Prop} (z : M ⊗[R] N)
    (tmul : ∀ x y, motive (x ⊗ₜ[R] y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
end TensorProduct
