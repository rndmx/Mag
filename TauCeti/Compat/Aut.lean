/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Scott Morrison, Yury Kudryashov
-/
import Mathlib.CategoryTheory.Endomorphism

/-!
# Backport (compat, not Tau Ceti code): the `Aut.of` / `Aut.asIso` interface

Mathlib 1b1ccf4 `Mathlib/CategoryTheory/Endomorphism.lean` makes `Aut X` a one-field structure
(`Aut.of`, field `asIso`). On Mathlib 16edf57, `Aut X` is the definition `X ≅ X`; the
constructor and projection are therefore the identity, and the `simps` lemmas of 1b1ccf4
(`one_asIso`, `inv_asIso`, `mul_asIso`) hold by `rfl`.
-/

namespace CategoryTheory.Aut

universe v u
variable {C : Type u} [Category.{v} C] {X : C}

/-- The automorphism given by an isomorphism (1b1ccf4 structure constructor). -/
abbrev of (e : X ≅ X) : Aut X := e

/-- The underlying isomorphism of an automorphism (1b1ccf4 structure field). -/
abbrev asIso (e : Aut X) : X ≅ X := e

lemma asIso_of (e : X ≅ X) : (Aut.of e).asIso = e := rfl
lemma of_asIso (e : Aut X) : Aut.of e.asIso = e := rfl
@[simp] lemma one_asIso : (1 : Aut X).asIso = Iso.refl X := rfl
@[simp] lemma inv_asIso (e : Aut X) : e⁻¹.asIso = e.asIso.symm := rfl
@[simp] lemma mul_asIso (x y : Aut X) : (x * y).asIso = y.asIso.trans x.asIso := rfl

end CategoryTheory.Aut

namespace CategoryTheory.End

universe v u
variable {C : Type u} [Category.{v} C] {X : C}

/-- 1b1ccf4 `End` structure `simps` lemma; on 16edf57 `asHom` is the identity. -/
@[simp] lemma mul_asHom (f g : End X) : (f * g).asHom = g.asHom ≫ f.asHom := rfl

end CategoryTheory.End
