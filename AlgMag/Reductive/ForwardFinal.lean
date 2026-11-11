/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.ForwardAssembly
import AlgMag.Reductive.RankOneDim
import AlgMag.Reductive.OpenCellScheme

/-!
# (DC) from the rank-one geometry: `hAff` from the Bruhat-type step, and the plug-in

* `hAff_of_bruhat`: `U⁺ ∖ {1}` is affine as soon as the affine open `Ω ∩ n·Ω` of `Z` maps to it by
  a separated morphism with a section (the Bruhat-type step, item 3:
  `Ω ∩ n·Ω ≅ (U⁻ ∖ {1}) × C × U⁺` for the left translate `n·Ω`: the puncture is on `U(λ⁻)`; to puncture
  `U(λ) = rayU`, use the opposite cocharacter or the right translate `Ω·n` (SL₂ check, BruhatRankOne.lean)). Uses `isAffineOpen_openCell_inf_translate` and `isAffine_of_section`.
* `dimCount_of_reductive''`: `dimCount_of_reductive'` with `hT4` replaced by one `RayDimData` per
  ray (`hT4_of_rayDimData`).
-/

open AlgebraicGeometry CategoryTheory Magnetism TauCeti WithConv AlgMag.Weyl

universe u

namespace AlgMag.Reductive

/-- **`hAff` from the Bruhat-type step.** Here `l` is the cocharacter of `Z` (`k[Z] = HZ`), `n` the
Weyl element, `V = k[U⁺]` with identity point `one`. -/
theorem hAff_of_bruhat {k HZ V : Type u} [Field k] [CommRing HZ] [HopfAlgebra k HZ]
    [Algebra.FiniteType k HZ] [Algebra.Smooth k HZ] [CommRing V]
    (l : HZ →ₐc[k] LaurentPolynomial k) (n : WithConv (HZ →ₐ[k] k))
    (one : Spec (CommRingCat.of V)) (closed : IsClosed ({one} : Set (Spec (CommRingCat.of V))))
    (p : (openCellOpens l ⊓ translateOpenCell l n).toScheme ⟶ (puncturedOpen one closed).toScheme)
    (s : (puncturedOpen one closed).toScheme ⟶ (openCellOpens l ⊓ translateOpenCell l n).toScheme)
    (hs : s ≫ p = 𝟙 _) [IsSeparated p] :
    IsAffineOpen (puncturedOpen one closed) := by
  have : IsAffine (openCellOpens l ⊓ translateOpenCell l n).toScheme :=
    isAffineOpen_openCell_inf_translate l n
  exact isAffine_of_section p s hs

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable [Algebra.FiniteType k H] [Module.Finite k (Bialgebra.CotangentSpace k H)]

/-- **(⇒), (DC)**, same statement as `dimCount_of_reductive`, from (i) at Lie level and one
`RayDimData` per ray. -/
theorem dimCount_of_reductive'' (π : H →ₐc[k] MonoidAlgebra k X)
    (hπ : Function.Surjective π)
    (hT : HopfIdeal.IsMaximalTorus k (CommHopfAlgCat.of k H) (HopfIdeal.kerOfSurjective π hπ))
    (hred : reductiveCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.of k H))
    (hLie0 : Module.finrank k (rootSpace π 0) ≤
      Module.finrank k (Bialgebra.CotangentSpace k (H ⧸ (HopfIdeal.kerOfSurjective π hπ).toIdeal)))
    (hD : ∀ (f : Additive X →+ ℤ), ∀ α ∈ posRoots π f, Nonempty (RayDimData π f α)) :
    ∃ ψ : X →* Multiplicative ℤ, (∀ α ∈ roots π, pairingHom ψ α ≠ 0) ∧
      Module.finrank k (Derivation k H (Bialgebra.CounitAlgebra k H k)) ≤
        Module.finrank k (Bialgebra.CotangentSpace k (H ⧸ (HopfIdeal.kerOfSurjective π hπ).toIdeal)) +
          posRays π (pairingHom ψ) + posRays π (-pairingHom ψ) :=
  dimCount_of_reductive' π hπ hT hred hLie0 (hT4_of_rayDimData π hD)

end AlgMag.Reductive
