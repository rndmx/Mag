/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Weyl.WeylGroup
import AlgMag.Reductive.TangentRoots
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Split reductive data (setting of §`sec:reductive`, split case)

`G = Spec H` over a field `k`, `T = D(X) ⊆ G` given by the surjection `π : k[G] → k[X]`.
A `SplitReductiveData π` records the Weyl-group input of SGA3 Exp. XXII used in the paper:
* a finite subgroup `W ⊆ Aut(X)` (the Weyl group, acting faithfully on `M = Additive X`),
* for each `w ∈ W` a point `n_w ∈ G(k)` normalizing `T` with automorphism `w`,
* `N_G(T)(k̄) = ⊔_{w ∈ W} n_w T(k̄)`: every `k̄`-point normalizing `T` with automorphism `σ` has
  `σ ∈ W` and lies in `n_σ T(k̄)`,
* `W` preserves the roots `Φ` (`roots π`).
The roots `Φ` are `roots π` (nontrivial weights of `T` on `Lie(G)`).
-/

suppress_compilation

open TensorProduct Magnetism TauCeti WithConv

namespace AlgMag.Reductive

open AlgMag.Weyl

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X]

/-- The `k̄`-point of `T` given by a `k̄`-point `t` of `D(X)`. -/
def torusPointOf (π : H →ₐc[k] MonoidAlgebra k X)
    (t : MonoidAlgebra k X →ₐ[k] AlgebraicClosure k) : WithConv (H →ₐ[k] AlgebraicClosure k) :=
  toConv (t.comp π.toAlgHom)

/-- A `k`-point viewed as a `k̄`-point. -/
def toAlgClosure (g : WithConv (H →ₐ[k] k)) : WithConv (H →ₐ[k] AlgebraicClosure k) :=
  AlgHom.mapValue (Algebra.ofId k (AlgebraicClosure k)) g

/-- **Split reductive data** for `T = D(X) ⊆ G`. -/
structure SplitReductiveData [DecidableEq X] [Module.Finite k (Bialgebra.CotangentSpace k H)]
    (π : H →ₐc[k] MonoidAlgebra k X) where
  /-- `T → G` is a closed immersion. -/
  surjective : Function.Surjective π
  /-- The Weyl group, as a group of automorphisms of `X`. -/
  W : Subgroup (X ≃* X)
  finite : Finite W
  /-- Representatives `n_w ∈ N_G(T)(k)`. -/
  rep : W → WithConv (H →ₐ[k] k)
  rep_normalizing : ∀ w : W, IsNormalizingWith π k (rep w) w
  /-- `N_G(T)(k̄) = ⊔_{w ∈ W} n_w T(k̄)`. -/
  normalizer_cover : ∀ (g : WithConv (H →ₐ[k] AlgebraicClosure k)) (σ : X ≃* X),
    IsNormalizingWith π (AlgebraicClosure k) g σ →
      ∃ hσ : σ ∈ W, ∃ t : MonoidAlgebra k X →ₐ[k] AlgebraicClosure k,
        g = toAlgClosure (rep ⟨σ, hσ⟩) * torusPointOf π t
  /-- `W` preserves the roots. -/
  roots_stable : ∀ w ∈ W, ∀ α ∈ roots π,
    Additive.ofMul (w (Additive.toMul α)) ∈ roots π

end AlgMag.Reductive
