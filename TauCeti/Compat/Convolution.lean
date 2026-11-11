/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Yunzhou Xie
Adapted from Tau Ceti (github.com/TauCetiProject/TauCeti, commit d2083f0); see TauCeti/CHANGES.md
-/
import Mathlib.RingTheory.Coalgebra.Convolution
import Mathlib.RingTheory.Bialgebra.Convolution

/-!
# Backport (compat, not Tau Ceti code)

Declarations copied verbatim (modulo the `module`/`public`/`@[expose]` syntax) from
Mathlib commit 1b1ccf4, files `Mathlib/RingTheory/Coalgebra/Convolution.lean` and
`Mathlib/RingTheory/Bialgebra/Convolution.lean`, which are absent from Mathlib 16edf57.
In 16edf57 the convolution unit needs `[Coalgebra R C]` (in 1b1ccf4 only `[CoalgebraStruct R C]`),
so `convOne_comp_coalgHom` and `algHom_comp_convOne` are stated under `[Coalgebra R C]`.
Mathlib 16edf57 already has special cases with these two names in
`Mathlib/RingTheory/HopfAlgebra/Quotient.lean`, so the general 1b1ccf4 versions are renamed
here with the suffix `_gen`.
-/

open TensorProduct WithConv Coalgebra

namespace LinearMap

variable {R A B C : Type*} [CommSemiring R]
variable [Semiring A] [Algebra R A] [AddCommMonoid C] [Module R C] [Coalgebra R C]

@[simp]
lemma convOne_comp_coalgHom_gen [AddCommMonoid B] [Module R B] [Coalgebra R B] (h : B →ₗc[R] C) :
    (1 : WithConv (C →ₗ[R] A)).ofConv ∘ₗ (h : B →ₗ[R] C) = (1 : WithConv (B →ₗ[R] A)).ofConv := by
  ext; simp

@[simp] lemma algHom_comp_convOne_gen [Semiring B] [Algebra R B] (h : A →ₐ[R] B) :
    h.toLinearMap ∘ₗ (1 : WithConv (C →ₗ[R] A)).ofConv = (1 : WithConv (C →ₗ[R] B)).ofConv := by
  ext; simp

end LinearMap

open LinearMap

variable {R A B C : Type*} [CommSemiring R]
variable [Semiring A] [Algebra R A] [AddCommMonoid C] [Module R C] [Coalgebra R C]

namespace AlgHom
variable [Semiring B] [Algebra R B]

/-- Post-composition by an algebra homomorphism, as a homomorphism of convolution algebras. -/
@[simps]
def convPostcomp (h : A →ₐ[R] B) : WithConv (C →ₗ[R] A) →ₐ[R] WithConv (C →ₗ[R] B) where
  toFun f := toConv (h.toLinearMap.comp f.ofConv)
  map_one' := WithConv.ext (algHom_comp_convOne_gen h)
  map_mul' f g := WithConv.ext (algHom_comp_convMul_distrib h f g)
  map_zero' := WithConv.ext (by ext; simp)
  map_add' f g := WithConv.ext (by ext; simp)
  commutes' r := WithConv.ext (by ext; simp)

lemma convPostcomp_injective {h : A →ₐ[R] B} (hh : Function.Injective h) :
    Function.Injective (convPostcomp h (C := C)) := fun _ _ e ↦
  WithConv.ext <| (LinearMap.cancel_left hh).1 congr(($e).ofConv)

@[simp] lemma convPostcomp_id : (AlgHom.id R A).convPostcomp (C := C) = AlgHom.id R _ := rfl

lemma convPostcomp_comp {D : Type*} [Semiring D] [Algebra R D] (h₁ : B →ₐ[R] D) (h₂ : A →ₐ[R] B) :
    (h₁.comp h₂).convPostcomp (C := C) = h₁.convPostcomp.comp h₂.convPostcomp := rfl

end AlgHom

namespace CoalgHom
variable [AddCommMonoid B] [Module R B] [Coalgebra R B]

/-- Pre-composition by a coalgebra homomorphism, as a homomorphism of convolution algebras. -/
@[simps]
def convPrecomp (h : B →ₗc[R] C) : WithConv (C →ₗ[R] A) →ₐ[R] WithConv (B →ₗ[R] A) where
  toFun f := toConv (f.ofConv.comp (h : B →ₗ[R] C))
  map_one' := WithConv.ext (convOne_comp_coalgHom_gen h)
  map_mul' f g := WithConv.ext (convMul_comp_coalgHom_distrib f g h)
  map_zero' := WithConv.ext (by ext; simp)
  map_add' f g := WithConv.ext (by ext; simp)
  commutes' r := WithConv.ext (by ext; simp)

lemma convPrecomp_injective {h : B →ₗc[R] C} (hh : Function.Surjective h) :
    Function.Injective (convPrecomp h (A := A)) := fun _ _ e ↦
  WithConv.ext <| (LinearMap.cancel_right hh).1 congr(($e).ofConv)

@[simp] lemma convPrecomp_id : (CoalgHom.id R C).convPrecomp (A := A) = AlgHom.id R _ := rfl

lemma convPrecomp_comp {D : Type*} [AddCommMonoid D] [Module R D] [Coalgebra R D]
    (h₁ : B →ₗc[R] C) (h₂ : D →ₗc[R] B) :
    (h₁.comp h₂).convPrecomp (A := A) = h₂.convPrecomp.comp h₁.convPrecomp := rfl

lemma convPrecomp_comp_convPostcomp {D : Type*} [Semiring D] [Algebra R D] (h : B →ₗc[R] C)
    (φ : A →ₐ[R] D) : h.convPrecomp.comp φ.convPostcomp = φ.convPostcomp.comp h.convPrecomp :=
  rfl

end CoalgHom

namespace BialgHom

section AlgebraCoalgebra
variable {R A C : Type*} [CommSemiring R]
variable [Semiring A] [Algebra R A] [Coalgebra R A] [Semiring C] [Algebra R C] [Coalgebra R C]
  (f : A →ₐc[R] C) {g : C →ₗ[R] C} {g' : A →ₗ[R] A}

lemma convPrecomp_eq_convPostcomp (h : Function.Semiconj f g' g) :
    f.toCoalgHom.convPrecomp (toConv g) = f.toAlgHom.convPostcomp (toConv g') :=
  WithConv.ext <| LinearMap.ext fun a ↦ by simpa [BialgHom.toCoalgHom_apply] using (h a).symm

end AlgebraCoalgebra

end BialgHom
