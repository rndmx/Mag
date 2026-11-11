/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.UCandProof
import AlgMag.Reductive.EquivalenceFinal3

/-!
# Classical route to T2: steps (c), (d), and the assembly

Notation (Hopf ideals of `H = k[G]`, inclusions reversed): `T = V(Tq)`, `B ⊇ T` is `B ≤ Tq`,
`μ` is a cocharacter of `T` when `Tq ⊆ ker μ`. `Ru S` is the pullback of `R_u(V(S))`, so
`R_u(Z(μ)) ⊆ B` is `B ≤ Ru (Z μ)`.

* **(c), for Borels inside `P(μ)`: proved** (`stepC_of_le_parabolic`), from L1b (L1bProof) and
  `UCand` (UCandProof) and Tau Ceti `le_unipotentRadicalDefiningIdeal`.
* **(c), for every Borel `B ⊇ T`**: `StepC Tq μ`. It follows (`stepC_of_l1bT`) from `L1bT`
  (Borel 11.15: `B ∩ Z_G(S)` is a Borel of `Z_G(S)` for `S ⊆ T ⊆ B`). `L1bT` with `B ⊆ P(μ)` is
  L1b (proved). The general case reduces to it by the classical trick: for `ν` regular and
  `B`-dominant, `B' = P(Nμ + ν)` (`N ≫ 0`) is a Borel inside `P(μ)` with `B' ∩ Z(μ) = B ∩ Z(μ)`.
  That reduction needs "every Borel `⊇ T` is `P(ν)`" and root combinatorics; not done here.
* **(d)** (Borel 13.17, Cor. 2): `StepD Tq`, named: a connected smooth unipotent closed subgroup
  lying in every Borel `B ⊇ T` lies in `R_u(G)`. True for `GL₃`: `∩_{B ⊇ T} B = T`, so such a
  subgroup is trivial, and `R_u(GL₃) = 1`.
* `ruZ_le_ruG` (proved): (c) + (d) + "`R_u(Z(μ))` is connected smooth unipotent as a subgroup of
  `G`" (`RuZUnip μ`, named transport through `H → H/Z(μ)`) give `R_u(Z(μ)) ⊆ R_u(G)`.
* Assembly (proved): `condI_condII_condIII_of_reductive_classical` is `..._final3` with `hBorMax`
  replaced by a T2 hypothesis plus the T2 ⇒ `BorelZMax` step (`hMaxOfT2`). That step is the
  density argument of finish-plan §2. It uses `T`-transitivity on `U_Z(λ⁻¹)(k) ∖ 1`, the same
  content as `hBruhat`, so it stays a named input.
-/

open Magnetism TauCeti TauCeti.Cocharacter

namespace AlgMag.Reductive.T2Classical

open AlgMag.Reductive AlgMag.Reductive.BorelRoute AlgMag.Reductive.BorelRouteReal

universe u

section Abstract

variable {k : Type u} {H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H]

local notation "Hf" => FiniteTypeCommHopfAlgCat.of k H

/-- **(c) for Borels inside `P(μ)`** (proved): `R_u(Z(μ)) ⊆ B`. -/
theorem stepC_of_le_parabolic [Algebra.Smooth k H] {B : HopfIdeal k H}
    (μ : H →ₐc[k] LaurentPolynomial k) (hB : IsBorelIn ⊥ B) (hPB : P μ ≤ B) :
    B ≤ Ru (Z μ) :=
  le_sup_left.trans (le_Ru' (L1bProof.l1b (fun l => UCandProof.uCand l) μ hB hPB))

/-- **Borel 11.15** (named): for a Borel `B ⊇ T` and a cocharacter `μ` of `T`, `B ∩ Z(μ)` is a
Borel of `Z(μ)`. For `B ⊆ P(μ)` this is L1b (proved, `L1bProof.l1b`). -/
def L1bT (Tq : HopfIdeal k H) : Prop :=
  ∀ {B : HopfIdeal k H} (μ : H →ₐc[k] LaurentPolynomial k), IsBorelIn ⊥ B → B ≤ Tq →
    Tq.toIdeal ≤ RingHom.ker (μ : H →ₐ[k] LaurentPolynomial k) → IsBorelIn (Z μ) (B ⊔ Z μ)

/-- **(c)**: `R_u(Z(μ)) ⊆ ∩_{B ⊇ T} B`. -/
def StepC (Tq : HopfIdeal k H) (μ : H →ₐc[k] LaurentPolynomial k) : Prop :=
  ∀ B : HopfIdeal k H, IsBorelIn ⊥ B → B ≤ Tq → B ≤ Ru (Z μ)

/-- (c) from Borel 11.15 (proved). -/
theorem stepC_of_l1bT {Tq : HopfIdeal k H} (h : L1bT Tq) (μ : H →ₐc[k] LaurentPolynomial k)
    (hμ : Tq.toIdeal ≤ RingHom.ker (μ : H →ₐ[k] LaurentPolynomial k)) : StepC Tq μ :=
  fun _ hB hBT => le_sup_left.trans (le_Ru' (h μ hB hBT hμ))

/-- **(d)** (Borel 13.17, Cor. 2, named): in a reductive `G`, a geometrically connected smooth
unipotent closed subgroup `V(N)` lying in every Borel `B ⊇ T` lies in `R_u(G)`. -/
def StepD (Tq : HopfIdeal k H) : Prop :=
  reductiveCommHopfAlgProperty k Hf → ∀ N : HopfIdeal k H,
    geometricallyConnectedCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient Hf N).obj →
    smoothUnipotentCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient Hf N) →
    (∀ B : HopfIdeal k H, IsBorelIn ⊥ B → B ≤ Tq → B ≤ N) → Ru ⊥ ≤ N

/-- (named, transport) `R_u(Z(μ))`, as a closed subgroup of `G`, is geometrically connected,
smooth and unipotent. -/
def RuZUnip (μ : H →ₐc[k] LaurentPolynomial k) : Prop :=
  geometricallyConnectedCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient Hf (Ru (Z μ))).obj ∧
    smoothUnipotentCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient Hf (Ru (Z μ)))

/-- **(c) + (d) ⇒ `R_u(Z(μ)) ⊆ R_u(G)`** (proved). -/
theorem ruZ_le_ruG {Tq : HopfIdeal k H} {μ : H →ₐc[k] LaurentPolynomial k}
    (hred : reductiveCommHopfAlgProperty k Hf) (hc : StepC Tq μ) (hd : StepD Tq)
    (hU : RuZUnip μ) : Ru ⊥ ≤ Ru (Z μ) :=
  hd hred _ hU.1 hU.2 hc

end Abstract

/-! ### Assembly: final theorem without `hBorMax` -/

open R1Opp R1Build R1Dis Final2 AlgMag.Weyl

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable [Algebra.FiniteType k H]

/-- **(⇒), classical form**: `..._final3` with `hBorMax` replaced by
* `hT2` (**T2**): `Z = G^{ℤδ}` has non-solvable `k`-points when `ℤδ` carries a root; the
  target of (a)–(d);
* `hMaxOfT2`: T2 ⇒ `BorelZMax` (density argument, finish-plan §2; uses `T`-transitivity). -/
theorem condI_condII_condIII_of_reductive_classical [Module.IsTorsionFree ℤ (Additive X)]
    (π : H →ₐc[k] MonoidAlgebra k X)
    (hπ : Function.Surjective π)
    (hT : HopfIdeal.IsMaximalTorus k (CommHopfAlgCat.of k H) (HopfIdeal.kerOfSurjective π hπ))
    (hred : reductiveCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.of k H))
    (hBruhat : letI : Algebra.Smooth k H := hred.smooth
      haveI : IsMulTorsionFree X := ⟨fun n hn =>
        (IsAddTorsionFree.of_isTorsionFree ℤ (Additive X)).nsmul_right_injective hn⟩
      ∀ (ψ : X →* Multiplicative ℤ) (α : Additive X) (hα : 0 < pairingHom ψ α),
        α ∈ roots π → BruhatRayCore π ψ α hα)
    (hT2 : letI : Algebra.Smooth k H := hred.smooth
      ∀ δ : Additive X, δ ≠ 0 →
        (∀ β ∈ roots π, (∃ m n : ℤ, n ≠ 0 ∧ n • β = m • δ) → β ∈ lineMagnet δ) →
        (∃ α ∈ roots π, α ∈ lineMagnet δ) →
        ¬ Group.IsSolvable (WithConv (ZAlg π δ →ₐ[k] k)))
    (hMaxOfT2 : letI : Algebra.Smooth k H := hred.smooth
      ∀ δ : Additive X, δ ≠ 0 →
        (∀ β ∈ roots π, (∃ m n : ℤ, n ≠ 0 ∧ n • β = m • δ) → β ∈ lineMagnet δ) →
        ((∃ α ∈ roots π, α ∈ lineMagnet δ) →
          ¬ Group.IsSolvable (WithConv (ZAlg π δ →ₐ[k] k))) →
        ∃ ψ : X →* Multiplicative ℤ, pairingHom ψ δ ≠ 0 ∧ BorelZMax π δ ψ) :
    CondI π ∧ CondII π ∧ CondIII π :=
  condI_condII_condIII_of_reductive_final3 π hπ hT hred hBruhat
    (fun δ hδ hRay => hMaxOfT2 δ hδ hRay (hT2 δ hδ hRay))

end AlgMag.Reductive.T2Classical

#print axioms AlgMag.Reductive.UCandProof.uCand
#print axioms AlgMag.Reductive.UCandProof.realBridgeSmooth
#print axioms AlgMag.Reductive.T2Classical.stepC_of_le_parabolic
#print axioms AlgMag.Reductive.T2Classical.stepC_of_l1bT
#print axioms AlgMag.Reductive.T2Classical.ruZ_le_ruG
#print axioms AlgMag.Reductive.T2Classical.condI_condII_condIII_of_reductive_classical
