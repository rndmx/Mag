/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Antoine Labelle
Adapted from Tau Ceti (github.com/TauCetiProject/TauCeti, commit d2083f0); see TauCeti/CHANGES.md
-/
import Mathlib.LinearAlgebra.Contraction

/-!
# Backport (compat, not Tau Ceti code): `dualTensorHomEquiv` API

Copied from Mathlib 1b1ccf4 `Mathlib/LinearAlgebra/Contraction.lean` (section FiniteProjective).
On Mathlib 16edf57 `dualTensorHomEquiv` is `.ofBijective _ (dualTensorHom_bijective ..)`, so
these lemmas hold by `rfl` as in the source.
-/

open Module TensorProduct LinearMap

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N] [Module.Finite R M] [Projective R M]

@[simp] lemma toLinearMap_dualTensorHomEquiv :
    (dualTensorHomEquiv R M N).toLinearMap = dualTensorHom R M N := rfl

@[simp] lemma dualTensorHomEquiv_tmul (f : Dual R M) (m : M) (n : N) :
    dualTensorHomEquiv R M N (f ⊗ₜ n) m = f m • n := rfl

@[simp] lemma dualTensorHomEquiv_symm_dualTensorHom (x : Dual R M ⊗[R] N) :
    (dualTensorHomEquiv R M N).symm (dualTensorHom R M N x) = x :=
  (dualTensorHomEquiv R M N).symm_apply_apply _

@[simp] lemma dualTensorHom_dualTensorHomEquiv_symm (x : M →ₗ[R] N) :
    dualTensorHom R M N ((dualTensorHomEquiv R M N).symm x) = x :=
  (dualTensorHomEquiv R M N).apply_symm_apply _
