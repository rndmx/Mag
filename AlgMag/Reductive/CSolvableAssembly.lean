/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.CharpolyFinite
import AlgMag.Reductive.ClosurePower
import AlgMag.Reductive.CentralTorusFinite
import TauCeti.Algebra.AlgebraicGroup.Derived.Connected

/-!
# `CSolvable C` from a central maximal torus: assembly

Discharges three of the four inputs of `NoTorusUnipotent.cSolvable_of_centralTorus`:
* `hfin` by `CentralTorusFinite.hfin`;
* `hcl` by `ClosurePower.closurePower`;
* `hstep2` by `CharpolyFinite.hstep2`, from the named leftover `Step2OverFpBar` of `[C, C]`
  (vacuous in characteristic `0`: `cSolvable_of_centralTorus_of_charZero` has no leftover).
-/

open WithConv TauCeti

namespace AlgMag.Reductive.CSolvableAssembly

open AlgMag.Reductive.NoTorusUnipotent

universe u

variable {k H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]

/-- **`CSolvable C`** for `V(C)` connected with a central maximal torus, modulo the named leftover
`Step2OverFpBar` for `[C, C]` (only relevant when `k = F̄_p`). -/
theorem cSolvable_of_centralTorus_of_step2OverFpBar [IsAlgClosed k] [Algebra.FiniteType k H]
    (C : HopfIdeal k H)
    [ConnectedSpace (PrimeSpectrum
      (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C))]
    {T : HopfIdeal k (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C)}
    (hT : HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k
      (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C)) T)
    (hcent : ∀ (A : Type u) [CommRing A] [Algebra k A] (g t : WithConv
      ((FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C) →ₐ[k] A)),
      T.toIdeal ≤ RingHom.ker (ofConv t) → g * t = t * g)
    (hFp : CharpolyFinite.Step2OverFpBar k
      ((FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C) ⧸
        (TauCeti.CommHopfAlgCat.derivedDefiningIdeal (R := k)
          (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C)).toIdeal)) :
    BaseCoreB.CSolvable C := by
  have := TauCeti.CommHopfAlgCat.connectedSpace_derived (k := k)
    (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C)
  exact cSolvable_of_centralTorus C hT hcent (CentralTorusFinite.hfin hT hcent)
    (fun g ↦ ClosurePower.closurePower g) (CharpolyFinite.hstep2 hFp)

/-- **`CSolvable C` in characteristic `0`**: no leftover. -/
theorem cSolvable_of_centralTorus_of_charZero [CharZero k] [IsAlgClosed k]
    [Algebra.FiniteType k H] (C : HopfIdeal k H)
    [ConnectedSpace (PrimeSpectrum
      (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C))]
    {T : HopfIdeal k (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C)}
    (hT : HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k
      (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C)) T)
    (hcent : ∀ (A : Type u) [CommRing A] [Algebra k A] (g t : WithConv
      ((FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C) →ₐ[k] A)),
      T.toIdeal ≤ RingHom.ker (ofConv t) → g * t = t * g) :
    BaseCoreB.CSolvable C :=
  cSolvable_of_centralTorus_of_step2OverFpBar C hT hcent CharpolyFinite.step2OverFpBar_of_charZero

end AlgMag.Reductive.CSolvableAssembly

#print axioms AlgMag.Reductive.CSolvableAssembly.cSolvable_of_centralTorus_of_step2OverFpBar
#print axioms AlgMag.Reductive.CSolvableAssembly.cSolvable_of_centralTorus_of_charZero
