/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Homomorphisms of `M`-graded rings and algebras

Throughout the `Magnetism` development the grading monoid is written `M`; it is a
*commutative monoid*, not a group, since magnets are submonoids of `M` and the
associated diagonalizable object `𝔸(M)` is a monoid scheme.

## Main definitions

* `Magnetism.GradedHom 𝒜 ℬ`, notation `𝒜 →[M,+,*] ℬ` : a ring homomorphism
  carrying `𝒜 m` into `ℬ m` for every `m : M`.
* `Magnetism.GradedAlgHom R₀ 𝒜 ℬ`, notation `𝒜 →ₐ[M,+,*,R₀] ℬ` : the `R₀`-algebra
  version.

## Design: what is *not* assumed here

A grading, in the usual sense, is two separate things: a family of subobjects
`𝒜 : M → σ`, and the property that it decomposes its ring,
`A = ⨁ m, 𝒜 m` (`DirectSum.Decomposition`). Only the first is needed to say
that a map preserves degrees, so only the first is assumed in this file:

* nothing at all is assumed about the index type `M` — not even `AddCommMonoid`;
* `𝒜` and `ℬ` are arbitrary families of subobjects: no
  `DirectSum.Decomposition`, no `GradedRing`, no `GradedAlgebra`.

Indeed the statement `a ∈ 𝒜 m → f a ∈ ℬ m` uses only the membership relation, and
none of the API below (`FunLike`, `RingHomClass`, `map_mem`, `ext`, `id`, `comp`)
inspects a decomposition. The decomposition is needed only where something is
*computed* from it — the construction of `Θ` and the two round-trips — and it is
assumed there instead: `[AddCommMonoid M]`, `[DecidableEq M]` and `[GradedAlgebra 𝒜]`
appear in `Magnetism.Representability`, not in this file.

This is the one deliberate divergence from the `GradedRingHom` of Mayeux–Zhang,
*Multi-graded Proj construction in Lean4*, on which this file is otherwise modelled:
their variable block carries `[GradedRing 𝒜]` and `[GradedRing ℬ]`, which must then be
discharged by `omit ... in` before each lemma that does not use them.
-/

namespace Magnetism

variable {M : Type*}
variable {σ σ' σ'' : Type*}
variable {A : Type*} [Semiring A] [SetLike σ A]
variable {B : Type*} [Semiring B] [SetLike σ' B]
variable {C : Type*} [Semiring C] [SetLike σ'' C]

/-- A homomorphism of `M`-graded rings: a ring homomorphism sending the degree `m`
part into the degree `m` part, for every `m : M`. -/
structure GradedHom (𝒜 : M → σ) (ℬ : M → σ') extends A →+* B where
  map_mem' : ∀ {m : M} {a : A}, a ∈ 𝒜 m → toFun a ∈ ℬ m

@[inherit_doc]
scoped notation:25 𝒜 " →[" M ",+,*] " ℬ => Magnetism.GradedHom (M := M) 𝒜 ℬ

namespace GradedHom

variable {𝒜 : M → σ} {ℬ : M → σ'} {𝒞 : M → σ''}

instance : FunLike (GradedHom 𝒜 ℬ) A B where
  coe f := f.toFun
  coe_injective := by
    rintro ⟨f, hf⟩ ⟨g, hg⟩ eq
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe, DFunLike.coe_fn_eq] at eq
    subst eq
    rfl

instance : RingHomClass (GradedHom 𝒜 ℬ) A B where
  map_mul f := f.toRingHom.map_mul
  map_one f := f.toRingHom.map_one
  map_add f := f.toRingHom.map_add
  map_zero f := f.toRingHom.map_zero

@[simp] lemma coe_toRingHom (f : GradedHom 𝒜 ℬ) : ⇑f.toRingHom = ⇑f := rfl

@[simp] lemma toRingHom_apply (f : GradedHom 𝒜 ℬ) (a : A) : f.toRingHom a = f a := rfl

/-- A graded ring homomorphism preserves degrees. -/
lemma map_mem (f : GradedHom 𝒜 ℬ) {m : M} {a : A} (ha : a ∈ 𝒜 m) : f a ∈ ℬ m :=
  f.map_mem' ha

@[ext] lemma ext {f g : GradedHom 𝒜 ℬ} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext _ _ h

/-- The identity, as a graded ring homomorphism. -/
protected def id (𝒜 : M → σ) : GradedHom 𝒜 𝒜 where
  __ := RingHom.id A
  map_mem' h := h

@[simp] lemma id_apply (a : A) : GradedHom.id 𝒜 a = a := rfl

/-- Composition of graded ring homomorphisms. -/
protected def comp (g : GradedHom ℬ 𝒞) (f : GradedHom 𝒜 ℬ) : GradedHom 𝒜 𝒞 where
  __ := g.toRingHom.comp f.toRingHom
  map_mem' h := g.map_mem (f.map_mem h)

@[simp] lemma comp_apply (g : GradedHom ℬ 𝒞) (f : GradedHom 𝒜 ℬ) (a : A) :
    g.comp f a = g (f a) := rfl

end GradedHom

section Algebra

variable (R₀ : Type*) [CommSemiring R₀] [Algebra R₀ A] [Algebra R₀ B] [Algebra R₀ C]

/-- A homomorphism of `M`-graded `R₀`-algebras. -/
structure GradedAlgHom (𝒜 : M → σ) (ℬ : M → σ') extends A →ₐ[R₀] B where
  map_mem' : ∀ {m : M} {a : A}, a ∈ 𝒜 m → toFun a ∈ ℬ m

@[inherit_doc]
scoped notation:25 𝒜 " →ₐ[" M ",+,*," R₀ "] " ℬ => Magnetism.GradedAlgHom (M := M) R₀ 𝒜 ℬ

namespace GradedAlgHom

variable {R₀}
variable {𝒜 : M → σ} {ℬ : M → σ'} {𝒞 : M → σ''}

instance : FunLike (GradedAlgHom R₀ 𝒜 ℬ) A B where
  coe f := f.toFun
  coe_injective := by
    rintro ⟨f, hf⟩ ⟨g, hg⟩ eq
    simp only [AlgHom.toRingHom_eq_coe, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
      MonoidHom.toOneHom_coe, MonoidHom.coe_coe, RingHom.coe_coe, DFunLike.coe_fn_eq] at eq
    subst eq
    rfl

instance : AlgHomClass (GradedAlgHom R₀ 𝒜 ℬ) R₀ A B where
  map_mul f := f.toAlgHom.map_mul
  map_one f := f.toAlgHom.map_one
  map_add f := f.toAlgHom.map_add
  map_zero f := f.toAlgHom.map_zero
  commutes f := f.toAlgHom.commutes

@[simp] lemma coe_toAlgHom (f : GradedAlgHom R₀ 𝒜 ℬ) : ⇑f.toAlgHom = ⇑f := rfl

@[simp] lemma toAlgHom_apply (f : GradedAlgHom R₀ 𝒜 ℬ) (a : A) : f.toAlgHom a = f a := rfl

lemma map_mem (f : GradedAlgHom R₀ 𝒜 ℬ) {m : M} {a : A} (ha : a ∈ 𝒜 m) : f a ∈ ℬ m :=
  f.map_mem' ha

@[ext] lemma ext {f g : GradedAlgHom R₀ 𝒜 ℬ} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext _ _ h

/-- The underlying graded ring homomorphism. -/
def toGradedHom (f : GradedAlgHom R₀ 𝒜 ℬ) : GradedHom 𝒜 ℬ where
  __ := f.toAlgHom.toRingHom
  map_mem' := f.map_mem'

@[simp] lemma toGradedHom_apply (f : GradedAlgHom R₀ 𝒜 ℬ) (a : A) : f.toGradedHom a = f a := rfl

end GradedAlgHom

end Algebra

end Magnetism
