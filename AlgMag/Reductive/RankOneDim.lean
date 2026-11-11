/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.AffineHartogs
import AlgMag.Reductive.ForwardCounting

/-!
# T4, step 6: `dim U⁺ ≤ 1` on each ray, from affine Hartogs

T4 of `equivalence-reductive/T-steps.md`, for `Z = G^{ℤα}` and `U⁺ = U_Z(λ)`. The step proved here
is step 6: if the punctured `U⁺ ∖ {1}` is an affine open, then affine Hartogs
(`not_isAffineOpen_puncturedOpen`, (G2)) forces `dim 𝒪_{U⁺,1} ≤ 1`, hence the root spaces on the
ray of `α` have total dimension `≤ 1`. This is the hypothesis `hT4` of `dimCount_of_reductive'`
(ForwardAssembly.lean).

The inputs that are not formalized are the fields of `RayDimData`:
* `hAff` (**T4 steps 1–5**: big cell `Ω = U⁻·x₀ ≅ U⁻` in the closed orbit `Y = Z·x₀`,
  `Y^T = {x₀, x₁}`, `Y = Ω ∪ nΩ`, so `Ω ∩ nΩ ≅ U⁺ ∖ {1}` is an intersection of affine opens in
  the separated `Y`): `U⁺ ∖ {1}` is an affine open of `Spec k[U⁺]`;
* `hdim` (**(D3) + smoothness of `U⁺`**: `Lie U⁺ = ⊕_{n>0} 𝔤_{nα}` and, `U⁺` being smooth,
  `dim 𝒪_{U⁺,1} = dim Lie U⁺`): if the ray carries dimension `≥ 2`, then `dim 𝒪_{U⁺,1} ≥ 2`.
-/

open AlgebraicGeometry CategoryTheory Magnetism TauCeti WithConv AlgMag.Weyl

universe u

namespace AlgMag.Reductive

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X) [Module.Finite k (Bialgebra.CotangentSpace k H)]

open scoped Classical in
/-- The total root-space dimension of the `f`-positive roots on the ray of `α`
(`= dim Lie U_{Z_α}(λ_f)` by (D3)). -/
noncomputable def rayDim (f : Additive X →+ ℤ) (α : Additive X) : ℕ :=
  ∑ β ∈ (posRoots π f).filter (fun β => SameRayRel β α),
    Module.finrank k (Derivation.adjointWeightSpace π (Additive.toMul β))

/-- **Geometric data for T4 on the ray of `α`.** `U` is `k[U⁺]`, `U⁺ = U_{Z_α}(λ_f)`, and `one` the
identity point of `Spec U`. -/
structure RayDimData (f : Additive X →+ ℤ) (α : Additive X) where
  U : Type u
  [ring : CommRing U]
  [noeth : IsNoetherianRing U]
  one : Spec (CommRingCat.of U)
  closed : IsClosed ({one} : Set (Spec (CommRingCat.of U)))
  /-- T4 steps 1–5: `U⁺ ∖ {1} ≅ Ω ∩ nΩ` is affine. -/
  hAff : IsAffineOpen (puncturedOpen one closed)
  /-- (D3) + smoothness: a ray of dimension `≥ 2` gives `dim 𝒪_{U⁺,1} ≥ 2`. -/
  hdim : 2 ≤ rayDim π f α →
    ¬ Ring.KrullDimLE 1 ((Spec (CommRingCat.of U)).presheaf.stalk one)

attribute [instance] RayDimData.ring RayDimData.noeth

/-- **T4, step 6** (affine Hartogs): `dim Lie U_{Z_α}(λ) ≤ 1`. -/
theorem rayDim_le_one {f : Additive X →+ ℤ} {α : Additive X} (D : RayDimData π f α) :
    rayDim π f α ≤ 1 := by
  by_contra h
  exact not_isAffineOpen_puncturedOpen _ D.one D.closed (D.hdim (by omega)) D.hAff

open scoped Classical in
/-- **The hypothesis `hT4` of `dimCount_of_reductive'`**, from one `RayDimData` per ray. -/
theorem hT4_of_rayDimData
    (hD : ∀ (f : Additive X →+ ℤ), ∀ α ∈ posRoots π f, Nonempty (RayDimData π f α)) :
    ∀ (f : Additive X →+ ℤ), ∀ α ∈ posRoots π f,
      ∑ β ∈ (posRoots π f).filter (fun β => SameRayRel β α),
        Module.finrank k (Derivation.adjointWeightSpace π (Additive.toMul β)) ≤ 1 :=
  fun f α hα => rayDim_le_one π (hD f α hα).some

end AlgMag.Reductive

