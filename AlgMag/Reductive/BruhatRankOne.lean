/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.OpenCellScheme
import AlgMag.Reductive.AffineHartogs

/-!
# The rank-one Bruhat datum for `hAff_of_bruhat`

`BruhatRankOneCore l n one closed` is the geometric core: a separated morphism
`Ω ∩ n·Ω ⟶ V ∖ {one}` with a section. `hAff_of_bruhatCore` discharges `hAff_of_bruhat` from it.

SL₂ check (Ω = U⁻TU⁺ = {a ≠ 0}, n = [[0,1],[-1,0]], left translation):
`n·Ω = {c ≠ 0}`, so `Ω ∩ n·Ω = {a ≠ 0, c ≠ 0} ≅ (U⁻ ∖ {1}) × T × U⁺` via `g = u⁻(c/a) t(a) u⁺(b/a)`.
The natural projection lands in `U⁻ ∖ {1} = U(λ⁻) ∖ {1}` (not `U⁺ ∖ {1}`; `U⁺∖{1}` is what `Ω·n`
gives). The section is `y ↦ u⁻(y)`, and the projection is separated (source affine).
Hence the natural choice is `V = k[U(λ⁻)]`; for `V = k[U(λ)]` compose with conjugation by `n`.
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgMag.Reductive

/-- **Geometric core (remaining).** The Bruhat-type datum on `Ω ∩ n·Ω`. -/
def BruhatRankOneCore {k HZ V : Type u} [Field k] [CommRing HZ] [HopfAlgebra k HZ]
    [Algebra.FiniteType k HZ] [Algebra.Smooth k HZ] [CommRing V]
    (l : HZ →ₐc[k] LaurentPolynomial k) (n : WithConv (HZ →ₐ[k] k))
    (one : Spec (CommRingCat.of V)) (closed : IsClosed ({one} : Set (Spec (CommRingCat.of V)))) :
    Prop :=
  ∃ (p : (openCellOpens l ⊓ translateOpenCell l n).toScheme ⟶ (puncturedOpen one closed).toScheme)
    (s : (puncturedOpen one closed).toScheme ⟶ (openCellOpens l ⊓ translateOpenCell l n).toScheme),
    s ≫ p = 𝟙 _ ∧ IsSeparated p

/-- `hAff` from the geometric core. -/
theorem hAff_of_bruhatCore {k HZ V : Type u} [Field k] [CommRing HZ] [HopfAlgebra k HZ]
    [Algebra.FiniteType k HZ] [Algebra.Smooth k HZ] [CommRing V]
    (l : HZ →ₐc[k] LaurentPolynomial k) (n : WithConv (HZ →ₐ[k] k))
    (one : Spec (CommRingCat.of V)) (closed : IsClosed ({one} : Set (Spec (CommRingCat.of V))))
    (h : BruhatRankOneCore l n one closed) :
    IsAffineOpen (puncturedOpen one closed) := by
  obtain ⟨p, s, hs, hp⟩ := h
  have : IsAffine (openCellOpens l ⊓ translateOpenCell l n).toScheme :=
    isAffineOpen_openCell_inf_translate l n
  exact isAffine_of_section p s hs

/-- Separatedness is automatic: the source `Ω ∩ n·Ω` is affine, so any morphism out of it is
separated. So the core reduces to a morphism with a section. -/
theorem bruhatRankOneCore_of_section {k HZ V : Type u} [Field k] [CommRing HZ] [HopfAlgebra k HZ]
    [Algebra.FiniteType k HZ] [Algebra.Smooth k HZ] [CommRing V]
    (l : HZ →ₐc[k] LaurentPolynomial k) (n : WithConv (HZ →ₐ[k] k))
    (one : Spec (CommRingCat.of V)) (closed : IsClosed ({one} : Set (Spec (CommRingCat.of V))))
    (p : (openCellOpens l ⊓ translateOpenCell l n).toScheme ⟶ (puncturedOpen one closed).toScheme)
    (s : (puncturedOpen one closed).toScheme ⟶ (openCellOpens l ⊓ translateOpenCell l n).toScheme)
    (hs : s ≫ p = 𝟙 _) : BruhatRankOneCore l n one closed := by
  have : IsAffine (openCellOpens l ⊓ translateOpenCell l n).toScheme :=
    isAffineOpen_openCell_inf_translate l n
  refine ⟨p, s, hs, ?_⟩
  have : IsSeparated (p ≫ Limits.terminal.from _) := inferInstance
  exact IsSeparated.of_comp p (Limits.terminal.from _)

end AlgMag.Reductive
