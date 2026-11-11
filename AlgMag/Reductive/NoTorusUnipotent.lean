/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.OpenCell.IrreducibleOfConnected
import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Naturality
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Basic
import TauCeti.Algebra.AlgebraicGroup.Torus.Basic
import TauCeti.Algebra.AlgebraicGroup.Torus.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Basic
import TauCeti.Algebra.AlgebraicGroup.Hopf.Map
import TauCeti.RingTheory.FiniteType.PointSeparation
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.PointAction
import Mathlib.LinearAlgebra.Charpoly.Basic
import AlgMag.Reductive.BaseCoreB
import AlgMag.Reductive.LimitTorus
import TauCeti.Algebra.AlgebraicGroup.Derived.Character
import TauCeti.Algebra.AlgebraicGroup.Representation.JordanDecomposition.ClosedFactors
import TauCeti.Algebra.AlgebraicGroup.Derived.Basic
import TauCeti.Algebra.AlgebraicGroup.Derived.Connected
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Solvable

/-!
# Theorem A (equivalence.tex, Thm 2.1): a connected group without tori is unipotent

Setting: `k = k̄`, `G = Spec H` affine of finite type, connected. Points are `k`-points
`g : WithConv (H →ₐ[k] k)`; the action of `g` on a finite comodule `M` is
`Comodule.endOfPoint M g.ofConv` on `k ⊗[k] M`.

Proved here:
* `isNilpotent_sub_one_of_charpoly` (Step 3, linear algebra): `charpoly f = (X - 1)^n` gives
  `f - 1` nilpotent (Cayley–Hamilton).
* `isUnipotentPoint_of_charpoly`: a point whose characteristic polynomial on every finite
  comodule is `(X - 1)^n` is a unipotent point.
* `exists_eq_of_finite_values` (Step 2, last line, "rigidity"): on an irreducible finite-type
  `k`-algebra, an element taking finitely many values at `k`-points takes one value
  (Nullstellensatz `forall_algHom_apply_eq_zero_iff_isNilpotent` + primality of the nilradical).
* `charpolyRegular`: the characteristic-polynomial coefficients are regular functions.
* `theoremA_of_charpolyValuesFinite`: every point is unipotent once these coefficients take
  finitely many values.
* `commutative_isUnipotentPoint`: Theorem A for reduced connected commutative groups (Tau Ceti
  Jordan factors: the semisimple factor is a torus).
* `noNontrivialTorus_quotient`: no nontrivial torus passes to closed subgroups.
* `exists_pow_isUnipotentPoint` (Step 1): some power of every point is unipotent, from
  `ClosureInput`.
* `theoremA`, `theoremA_smoothUnipotent`: Theorem A from the named inputs below.
* `cSolvable_of_derived_unipotent`: `BaseCoreB.CSolvable C` from unipotence of `[V(C), V(C)]`.

Named inputs (NOT proved here):
* `ClosureInput g` (general, true for every `G`, e.g. `GL₂`): some `g^N`, `N > 0`, lies in a
  reduced commutative connected closed subgroup (`(closure ⟨g⟩)°`; needs the closure of `⟨g⟩`
  to be commutative and the finite component group, `Connected/ComponentGroup` is not in the
  local Tau Ceti).
* `hstep2 : NoNontrivialTorus → SemisimplePartsFiniteOrder → CharpolyValuesFinite` (Step 2
  without its last line); true for every `H`, vacuously for `GL₂`.
-/

open Polynomial WithConv TauCeti TauCeti.HopfAlgebra
open scoped TensorProduct

namespace AlgMag.Reductive.NoTorusUnipotent

universe u

/-! ### Step 3: linear algebra -/

/-- Cayley–Hamilton: `charpoly f = (X - 1)^n` forces `f - 1` nilpotent. -/
theorem isNilpotent_sub_one_of_charpoly {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : Module.End K V)
    (h : f.charpoly = (Polynomial.X - 1) ^ Module.finrank K V) : IsNilpotent (f - 1) := by
  refine ⟨Module.finrank K V, ?_⟩
  have hCH := LinearMap.aeval_self_charpoly f
  rw [h, map_pow, map_sub, aeval_X, map_one] at hCH
  exact hCH

/-! ### Step 2, rigidity: finitely many values on an irreducible variety means one value -/

/-- On an irreducible finite-type algebra over `k = k̄`, an element whose values at `k`-points
form a finite set is constant at `k`-points. -/
theorem exists_eq_of_finite_values {k A : Type u} [Field k] [IsAlgClosed k] [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] [IrreducibleSpace (PrimeSpectrum A)] (c : A)
    (hfin : (Set.range fun f : A →ₐ[k] k ↦ f c).Finite) :
    ∃ a : k, ∀ f : A →ₐ[k] k, f c = a := by
  classical
  have hprime : (nilradical A).IsPrime :=
    PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.1 inferInstance
  set S := hfin.toFinset
  have hprod : ∏ a ∈ S, (c - algebraMap k A a) ∈ nilradical A := by
    rw [mem_nilradical, ← forall_algHom_apply_eq_zero_iff_isNilpotent (k := k) (K := k)]
    intro f
    rw [map_prod]
    refine Finset.prod_eq_zero (i := f c) ?_ ?_
    · simp [S]
    · simp
  obtain ⟨a, -, ha⟩ := Ideal.IsPrime.prod_mem_iff.1 hprod
  refine ⟨a, fun f ↦ ?_⟩
  have := (forall_algHom_apply_eq_zero_iff_isNilpotent (k := k) (K := k) _).2
    (mem_nilradical.1 ha) f
  rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_eq_zero] at this
  exact this

/-! ### Theorem A -/

variable (k : Type u) (H : Type u) [Field k] [CommRing H] [HopfAlgebra k H]

/-- **Named input (general).** The coefficients of the characteristic polynomial of the action
of `k`-points on a finite comodule are regular functions. True for every `H` (matrix
coefficients of the coaction in a basis, `Matrix.charpoly_map`). -/
def CharpolyRegular : Prop :=
  ∀ (M : FGComoduleCat.{u, u, u} k H) (i : ℕ), ∃ c : H, ∀ g : WithConv (H →ₐ[k] k),
    g.ofConv c = (Comodule.endOfPoint M g.ofConv).charpoly.coeff i

/-- **Named input (Steps 1–2 of the paper).** Each characteristic-polynomial coefficient takes
finitely many values on `k`-points. -/
def CharpolyValuesFinite : Prop :=
  ∀ (M : FGComoduleCat.{u, u, u} k H) (i : ℕ),
    (Set.range fun g : WithConv (H →ₐ[k] k) ↦
      (Comodule.endOfPoint M g.ofConv).charpoly.coeff i).Finite

/-- `CharpolyRegular` holds for every `H`: the coefficient is the corresponding coefficient of
the characteristic polynomial of the universal point `id : H → H` (Tau Ceti
`charpoly_endOfPoint_comp`). -/
theorem charpolyRegular : CharpolyRegular k H := by
  intro M i
  refine ⟨((Comodule.endOfPoint M (AlgHom.id k H)).charpoly).coeff i, fun g ↦ ?_⟩
  have h := congrArg (fun p : Polynomial k ↦ p.coeff i)
    (Comodule.charpoly_endOfPoint_comp (M := M) (AlgHom.id k H) g.ofConv)
  simp only [AlgHom.comp_id, Polynomial.coeff_map] at h
  rw [h]
  rfl

/-- `G` has no nontrivial torus: every closed subgroup that is a torus has only the identity as
`k`-point. -/
def NoNontrivialTorus [Algebra.FiniteType k H] : Prop :=
  ∀ J : HopfIdeal k H,
    torusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) J) →
    ∀ g : WithConv (H →ₐ[k] k), (∀ y ∈ J.toIdeal, g.ofConv y = 0) → g = 1

variable {k H}

/-- The action of a point whose characteristic polynomial on every finite comodule is
`(X - 1)^n` is unipotent. -/
theorem isUnipotentPoint_of_charpoly (g : WithConv (H →ₐ[k] k))
    (h : ∀ M : FGComoduleCat.{u, u, u} k H,
      (Comodule.endOfPoint M g.ofConv).charpoly =
        (Polynomial.X - 1) ^ Module.finrank k (k ⊗[k] M)) :
    IsUnipotentPoint g := by
  rw [isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one]
  intro M
  exact isNilpotent_sub_one_of_charpoly _ (h M)

/-- The identity point acts trivially. -/
theorem endOfPoint_one (M : FGComoduleCat.{u, u, u} k H) :
    Comodule.endOfPoint M (1 : WithConv (H →ₐ[k] k)).ofConv = 1 := by
  rw [← Comodule.pointsAction_toLinearMap, map_one]
  rfl

/-- **Theorem A, from the two named inputs.** If `G` is connected and the
characteristic-polynomial coefficients are regular with finitely many values, every `k`-point
is unipotent. -/
theorem theoremA_of_charpolyValuesFinite [IsAlgClosed k] [Algebra.FiniteType k H]
    [ConnectedSpace (PrimeSpectrum H)] (hreg : CharpolyRegular k H)
    (hfin : CharpolyValuesFinite k H) (g : WithConv (H →ₐ[k] k)) : IsUnipotentPoint g := by
  have : IrreducibleSpace (PrimeSpectrum H) :=
    OpenCellNotes.irreducibleSpace_of_connectedSpace k
  refine isUnipotentPoint_of_charpoly g fun M ↦ ?_
  rw [← LinearMap.charpoly_one]
  ext i
  obtain ⟨c, hc⟩ := hreg M i
  have hfin' : (Set.range fun f : H →ₐ[k] k ↦ f c).Finite := by
    refine (hfin M i).subset ?_
    rintro _ ⟨f, rfl⟩
    exact ⟨toConv f, by simpa using (hc (toConv f)).symm⟩
  obtain ⟨a, ha⟩ := exists_eq_of_finite_values c hfin'
  have h1 := hc 1
  have hg := hc g
  rw [endOfPoint_one] at h1
  rw [← hg, ← h1, ha, ha]

/-- **Theorem A for commutative groups** (the core of Step 1, proved): over `k = k̄`, a reduced
connected commutative group without nontrivial torus has only unipotent points. Its closed
semisimple factor `ker(g ↦ g_s)` is a torus (Tau Ceti
`torusCommHopfAlgProperty_semisimpleFactor`), so `g_s = 1`. -/
theorem commutative_isUnipotentPoint [IsAlgClosed k] [Algebra.FiniteType k H] [IsReduced H]
    [Coalgebra.IsCocomm k H]
    (hconn : geometricallyConnectedCommHopfAlgProperty k (CommHopfAlgCat.of k H))
    (htor : NoNontrivialTorus k H) (g : WithConv (H →ₐ[k] k)) : IsUnipotentPoint g := by
  have hT := HopfAlgebra.Point.torusCommHopfAlgProperty_semisimpleFactor k H hconn
  refine (HopfAlgebra.Point.mapDomain_semisimplePartBialgHom_eq_one_iff g).1
    (htor _ hT _ fun y hy ↦ ?_)
  rw [HopfIdeal.ker_toIdeal, RingHom.mem_ker] at hy
  rw [BialgHom.mapDomain_apply_apply]
  have hy' : HopfAlgebra.Point.semisimplePartBialgHom k H y = 0 := hy
  rw [hy', map_zero]

/-- The quotient map `H → H ⧸ J`. -/
noncomputable abbrev qMk (J : HopfIdeal k H) : H →ₐc[k] (H ⧸ J.toIdeal) :=
  Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal

/-- Points of `H ⧸ J` are determined by their pullback to `H`. -/
theorem mapDomain_qMk_injective (J : HopfIdeal k H) :
    Function.Injective (BialgHom.mapDomain (A := k) (qMk J)) := by
  intro a b hab
  apply WithConv.ofConv_injective
  apply Ideal.Quotient.algHom_ext
  ext y
  have := congrArg (fun p : WithConv (H →ₐ[k] k) ↦ p.ofConv y) hab
  simpa [BialgHom.mapDomain_apply_apply] using this

/-- `NoNontrivialTorus` passes to closed subgroups `V(J)`: a torus of `V(J)` is a torus of `G`
(`H ⧸ J'.comap ≅ (H ⧸ J) ⧸ J'`). -/
theorem noNontrivialTorus_quotient [Algebra.FiniteType k H] (J : HopfIdeal k H)
    (htor : NoNontrivialTorus k H) : NoNontrivialTorus k (H ⧸ J.toIdeal) := by
  intro J' hT g' hg'
  have hq : Function.Surjective (qMk J) := Ideal.Quotient.mk_surjective
  let e : FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H)
        (J'.comapOfSurjective (qMk J) hq) ≅
      FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k (H ⧸ J.toIdeal)) J' :=
    CategoryTheory.ObjectProperty.isoMk _
    (_root_.CommHopfAlgCat.Hom.quotientIsoOfSurjective
      (H := _root_.CommHopfAlgCat.of k H)
      (K := _root_.CommHopfAlgCat.of k (H ⧸ J.toIdeal))
      (_root_.CommHopfAlgCat.ofHom (qMk J)) hq J')
  have hT' : torusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H)
        (J'.comapOfSurjective (qMk J) hq)) :=
    (torusCommHopfAlgProperty k).prop_of_iso e.symm hT
  have h1 := htor _ hT' (BialgHom.mapDomain (qMk J) g') fun y hy ↦ by
    rw [BialgHom.mapDomain_apply_apply]
    exact hg' _ (HopfIdeal.mem_comapOfSurjective.1 hy)
  apply mapDomain_qMk_injective J
  rw [h1, map_one]

/-- **Closure input** (general; true for every `G`, e.g. `GL₂`): some power `g^N` lies in a
reduced, commutative, connected closed subgroup `V(J)`. Take `J` the identity component of the
closure of `⟨g⟩` and `N` the order of `g` in its finite component group. -/
def ClosureInput (g : WithConv (H →ₐ[k] k)) : Prop :=
  ∃ (J : HopfIdeal k H) (N : ℕ), 0 < N ∧ IsReduced (H ⧸ J.toIdeal) ∧
    Coalgebra.IsCocomm k (H ⧸ J.toIdeal) ∧
    geometricallyConnectedCommHopfAlgProperty k (CommHopfAlgCat.of k (H ⧸ J.toIdeal)) ∧
    ∀ y ∈ J.toIdeal, (g ^ N).ofConv y = 0

/-- **Step 1, from the closure input** (proved): without nontrivial torus, the semisimple part
of every point has finite order, i.e. some power of the point is unipotent. -/
theorem exists_pow_isUnipotentPoint [IsAlgClosed k] [Algebra.FiniteType k H]
    (htor : NoNontrivialTorus k H) (g : WithConv (H →ₐ[k] k)) (hcl : ClosureInput g) :
    ∃ N : ℕ, 0 < N ∧ IsUnipotentPoint (g ^ N) := by
  obtain ⟨J, N, hN, hred, hcocomm, hconn, hJ⟩ := hcl
  refine ⟨N, hN, ?_⟩
  let g' : WithConv ((H ⧸ J.toIdeal) →ₐ[k] k) :=
    toConv (Ideal.Quotient.liftₐ J.toIdeal (g ^ N).ofConv hJ)
  have hg' : BialgHom.mapDomain (qMk J) g' = g ^ N := by
    apply WithConv.ofConv_injective
    ext y
    simp [g']
    exact Ideal.Quotient.lift_mk _ _ _
  rw [← hg']
  exact (commutative_isUnipotentPoint hconn (noNontrivialTorus_quotient J htor) g').mapDomain _

variable (k H) in
/-- **Step 1 of the paper, as a property**: every point has a power that is unipotent, i.e. its
semisimple part has finite order. -/
def SemisimplePartsFiniteOrder : Prop :=
  ∀ g : WithConv (H →ₐ[k] k), ∃ N : ℕ, 0 < N ∧ IsUnipotentPoint (g ^ N)

/-- **Theorem A** (equivalence.tex Thm 2.1) on `k`-points, from the two named inputs
* `hcl` (`ClosureInput`, general: `(closure ⟨g⟩)°` and the index of `g` in it); Step 1 itself is
  then proved (`exists_pow_isUnipotentPoint`);
* `hstep2` (Step 2 without its last line: size argument in characteristic `0`, transcendence in
  characteristic `p` for `k ≠ F̄_p`, specialization from `K = (k(t))‾` for `k = F̄_p`), an
  implication with antecedent `NoNontrivialTorus k H`, true for every `H` (vacuously for `GL₂`).
-/
theorem theoremA [IsAlgClosed k] [Algebra.FiniteType k H] [ConnectedSpace (PrimeSpectrum H)]
    (hcl : ∀ g : WithConv (H →ₐ[k] k), ClosureInput g)
    (hstep2 : NoNontrivialTorus k H → SemisimplePartsFiniteOrder k H →
      CharpolyValuesFinite k H)
    (htor : NoNontrivialTorus k H) (g : WithConv (H →ₐ[k] k)) : IsUnipotentPoint g :=
  theoremA_of_charpolyValuesFinite (charpolyRegular k H)
    (hstep2 htor fun g ↦ exists_pow_isUnipotentPoint htor g (hcl g)) g

/-- Over `k = k̄`, unipotence of all `k`-points gives unipotence of all `AlgebraicClosure k`-points
(Tau Ceti's `geometricallyUnipotentPointsCommHopfAlgProperty`). -/
theorem geometricallyUnipotent_of_forall_points [IsAlgClosed k]
    (h : ∀ g : WithConv (H →ₐ[k] k), IsUnipotentPoint g) :
    geometricallyUnipotentPointsCommHopfAlgProperty k (CommHopfAlgCat.of k H) := by
  intro g
  let ψ : AlgebraicClosure k →ₐ[k] k := IsAlgClosed.lift
  have hcomp : (Algebra.ofId k (AlgebraicClosure k)).comp ψ = AlgHom.id k _ := by
    ext x
    obtain ⟨a, rfl⟩ :=
      (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := AlgebraicClosure k)).2 x
    simp
  have := (h (AlgHom.mapValue (H := H) ψ g)).mapValue (Algebra.ofId k (AlgebraicClosure k))
  rwa [← MonoidHom.comp_apply, ← AlgHom.mapValue_comp, hcomp, AlgHom.mapValue_id,
    MonoidHom.id_apply] at this

/-- **Theorem A, Tau Ceti form**: a smooth connected group over `k = k̄` without nontrivial
torus is (smooth) unipotent, given the named inputs `hcl`, `hstep2`. -/
theorem theoremA_smoothUnipotent [IsAlgClosed k] [Algebra.FiniteType k H] [Algebra.Smooth k H]
    [ConnectedSpace (PrimeSpectrum H)]
    (hcl : ∀ g : WithConv (H →ₐ[k] k), ClosureInput g)
    (hstep2 : NoNontrivialTorus k H → SemisimplePartsFiniteOrder k H →
      CharpolyValuesFinite k H)
    (htor : NoNontrivialTorus k H) :
    smoothUnipotentCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.of k H) := by
  rw [smoothUnipotentCommHopfAlgProperty_iff]
  exact ⟨‹Algebra.Smooth k H›, geometricallyUnipotent_of_forall_points
    (theoremA hcl hstep2 htor)⟩

/-! ### `CSolvable` from the derived subgroup

For a connected solvable group the derived subgroup is unipotent; conversely, a group whose
derived subgroup has unipotent geometric points has solvable geometric points (Kolchin on the
derived subgroup, abelian quotient). So `CSolvable C` reduces to unipotence of `[C, C]`, which is
Theorem A for `[C, C]` (smooth, connected, and torus-free since `T` is central and maximal). -/

/-- If the derived subgroup has unipotent geometric points, the group has solvable geometric
points. -/
theorem geometricallySolvable_of_derived_unipotent {Q : Type u} [CommRing Q] [HopfAlgebra k Q]
    [Algebra.FiniteType k Q]
    (hD : geometricallyUnipotentPointsCommHopfAlgProperty k
      (CommHopfAlgCat.of k
        (Q ⧸ (TauCeti.CommHopfAlgCat.derivedDefiningIdeal (R := k) Q).toIdeal))) :
    geometricallySolvablePointsCommHopfAlgProperty k (CommHopfAlgCat.of k Q) := by
  set D := TauCeti.CommHopfAlgCat.derivedDefiningIdeal (R := k) Q
  have hs := geometricallyUnipotentPointsCommHopfAlgProperty.geometricallySolvable hD
  rw [geometricallySolvablePointsCommHopfAlgProperty_iff] at hs ⊢
  have hS := (BaseCoreB.isSolvable_quotientPointsSubgroup_iff (k := k) (H := Q) D).2 hs
  have hcomm :=
    TauCeti.CommHopfAlgCat.commutator_le_quotientPointsSubgroup_of_le_derivedDefiningIdeal
      (CommHopfAlgCat.of k Q) D le_rfl (CommAlgCat.of k (AlgebraicClosure k))
  have hab : Group.IsSolvable (Abelianization (WithConv (Q →ₐ[k] AlgebraicClosure k))) :=
    Group.isSolvable_of_comm mul_comm
  exact Group.isSolvable_of_ker_le_range
    (CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of k Q) D
      (CommAlgCat.of k (AlgebraicClosure k))).subtype Abelianization.of
    (by rw [Abelianization.ker_of, Subgroup.range_subtype]; exact hcomm)

/-- **`CSolvable C`** (the named input of `BaseCoreB`) from unipotence of the geometric points of
the derived subgroup of `V(C)`. True for `GL₂`, `C = T` diagonal: the derived subgroup is
trivial. -/
theorem cSolvable_of_derived_unipotent [Algebra.FiniteType k H] (C : HopfIdeal k H)
    (hD : geometricallyUnipotentPointsCommHopfAlgProperty k
      (CommHopfAlgCat.of k
        ((FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C) ⧸
          (TauCeti.CommHopfAlgCat.derivedDefiningIdeal (R := k)
            (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C)).toIdeal))) :
    BaseCoreB.CSolvable C :=
  geometricallySolvable_of_derived_unipotent hD

/-- **Theorem A applied to the derived subgroup.** For a connected `G = Spec Q` over `k = k̄`,
the derived subgroup `[G, G]` is connected (Tau Ceti `connectedSpace_derived`), so if it has no
nontrivial torus its geometric points are unipotent (inputs `hcl`, `hstep2` of `theoremA`, for
`[G, G]`). -/
theorem derived_unipotent_of_noNontrivialTorus [IsAlgClosed k] {Q : Type u} [CommRing Q]
    [HopfAlgebra k Q] [Algebra.FiniteType k Q] [ConnectedSpace (PrimeSpectrum Q)]
    (hcl : ∀ g : WithConv
      ((Q ⧸ (TauCeti.CommHopfAlgCat.derivedDefiningIdeal (R := k) Q).toIdeal) →ₐ[k] k),
      ClosureInput g)
    (hstep2 : NoNontrivialTorus k
        (Q ⧸ (TauCeti.CommHopfAlgCat.derivedDefiningIdeal (R := k) Q).toIdeal) →
      SemisimplePartsFiniteOrder k
        (Q ⧸ (TauCeti.CommHopfAlgCat.derivedDefiningIdeal (R := k) Q).toIdeal) →
      CharpolyValuesFinite k
        (Q ⧸ (TauCeti.CommHopfAlgCat.derivedDefiningIdeal (R := k) Q).toIdeal))
    (htor : NoNontrivialTorus k
      (Q ⧸ (TauCeti.CommHopfAlgCat.derivedDefiningIdeal (R := k) Q).toIdeal)) :
    geometricallyUnipotentPointsCommHopfAlgProperty k
      (CommHopfAlgCat.of k
        (Q ⧸ (TauCeti.CommHopfAlgCat.derivedDefiningIdeal (R := k) Q).toIdeal)) := by
  have := TauCeti.CommHopfAlgCat.connectedSpace_derived (k := k) Q
  exact geometricallyUnipotent_of_forall_points (theoremA hcl hstep2 htor)

/-- **`CSolvable C` from Theorem A on `[C, C]`**: for `V(C)` connected, `CSolvable C` follows
once `[C, C]` has no nontrivial torus (plus the inputs `hcl`, `hstep2` of `theoremA` for
`[C, C]`). For `C = Z_G(T)` the torus-freeness is the remaining named input: a torus `S` of
`[C, C]` commutes with the central `T`, `S·T` is a torus, so `S ⊆ T ∩ [C, C]`, which is finite. -/
theorem cSolvable_of_derived_noNontrivialTorus [IsAlgClosed k] [Algebra.FiniteType k H]
    (C : HopfIdeal k H)
    [ConnectedSpace (PrimeSpectrum
      (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C))]
    (hcl : ∀ g : WithConv
      (((FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C) ⧸
        (TauCeti.CommHopfAlgCat.derivedDefiningIdeal (R := k)
          (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C)).toIdeal) →ₐ[k]
        k), ClosureInput g)
    (hstep2 : NoNontrivialTorus k
        ((FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C) ⧸
          (TauCeti.CommHopfAlgCat.derivedDefiningIdeal (R := k)
            (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C)).toIdeal) →
      SemisimplePartsFiniteOrder k
        ((FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C) ⧸
          (TauCeti.CommHopfAlgCat.derivedDefiningIdeal (R := k)
            (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C)).toIdeal) →
      CharpolyValuesFinite k
        ((FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C) ⧸
          (TauCeti.CommHopfAlgCat.derivedDefiningIdeal (R := k)
            (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C)).toIdeal))
    (htor : NoNontrivialTorus k
      ((FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C) ⧸
        (TauCeti.CommHopfAlgCat.derivedDefiningIdeal (R := k)
          (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C)).toIdeal)) :
    BaseCoreB.CSolvable C :=
  cSolvable_of_derived_unipotent C (derived_unipotent_of_noNontrivialTorus hcl hstep2 htor)

/-! ### Torus-freeness of `[C, C]`, piece (c) -/

omit [Field k] [CommRing H] [HopfAlgebra k H] in
/-- **(c)** Over `k = k̄`, a torus with finitely many `k`-points has only the identity point:
its points are `σ → kˣ` (`SplitTorus.pointsMulEquiv`), and `kˣ` is infinite. -/
theorem torus_points_subsingleton_of_finite {k : Type u} [Field k] [IsAlgClosed k]
    (Q : FiniteTypeCommHopfAlgCat.{u, u} k) (hT : torusCommHopfAlgProperty k Q)
    [hfin : Finite (WithConv (Q →ₐ[k] k))] : Subsingleton (WithConv (Q →ₐ[k] k)) := by
  obtain ⟨n, ⟨e⟩⟩ := (splitTorusCommHopfAlgProperty_iff k Q).1
    (torusCommHopfAlgProperty.split k Q hT)
  let E : WithConv (Q →ₐ[k] k) ≃* (ULift.{u} (Fin n) → kˣ) :=
    (BialgEquiv.mapDomainMulEquiv (A := k)
      (_root_.CommHopfAlgCat.ofIso ((CategoryTheory.ObjectProperty.ι _).mapIso e))).trans
      SplitTorus.pointsMulEquiv
  have hE : Finite (ULift.{u} (Fin n) → kˣ) := Finite.of_equiv _ E.toEquiv
  have : IsEmpty (ULift.{u} (Fin n)) := by
    by_contra h
    rw [not_isEmpty_iff] at h
    have : Infinite {a : k // a ≠ 0} :=
      ((Set.finite_singleton (0 : k)).infinite_compl).to_subtype
    have : Infinite kˣ := Infinite.of_injective _ (unitsEquivNeZero (G₀ := k)).symm.injective
    exact not_finite (ULift.{u} (Fin n) → kˣ)
  exact E.toEquiv.subsingleton

/-! ### Torus-freeness of `[C, C]`, piece (a): a torus commuting with a central maximal torus
lies in it (the `S · T` argument of `LimitTorus.limit_mem_torus'`, without Levi retraction) -/

omit [Field k] [CommRing H] [HopfAlgebra k H] in
/-- Any torus over `k = k̄` is split with explicit character group `ℤ^r` (as
`exists_split_explicit`, for a torus that need not be maximal). -/
theorem exists_split_of_torus {k H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
    [Algebra.FiniteType k H] [IsAlgClosed k] (S : HopfIdeal k H)
    (hS : torusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) S)) :
    ∃ (r : ℕ) (φ : H →ₐc[k] MonoidAlgebra k (SplitTorus.characterGroup (ULift.{u} (Fin r)))),
      Function.Surjective φ ∧
        RingHom.ker (φ : H →ₐ[k] MonoidAlgebra k (SplitTorus.characterGroup (ULift.{u} (Fin r))))
          = S.toIdeal := by
  obtain ⟨r, ⟨i⟩⟩ := (splitTorusCommHopfAlgProperty_iff k _).1
    (torusCommHopfAlgProperty.split k _ hS)
  let G0 := SplitTorus.characterGroup (ULift.{u} (Fin r))
  let m : H →ₐc[k] (H ⧸ S.toIdeal) :=
    (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of k H) S).hom
  let ψ : (H ⧸ S.toIdeal) →ₐc[k] MonoidAlgebra k G0 := i.inv.hom.hom
  let ψ' : MonoidAlgebra k G0 →ₐc[k] (H ⧸ S.toIdeal) := i.hom.hom.hom
  have h1 : ∀ x, ψ' (ψ x) = x := fun x ↦ by
    exact congrArg (fun f ↦ f.hom.hom x) i.inv_hom_id
  have h2 : ∀ x, ψ (ψ' x) = x := fun x ↦ by
    exact congrArg (fun f ↦ f.hom.hom x) i.hom_inv_id
  have hm : ∀ x, m x = Ideal.Quotient.mk _ x := fun _ ↦ rfl
  refine ⟨r, ψ.comp m, fun y ↦ ?_, ?_⟩
  · obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (ψ' y)
    exact ⟨x, by simp [hm, hx, h2]⟩
  · ext x
    rw [RingHom.mem_ker]
    change ψ (m x) = 0 ↔ _
    constructor
    · intro hx
      have : m x = 0 := by rw [← h1 (m x), hx, map_zero]
      rw [hm] at this
      exact Ideal.Quotient.eq_zero_iff_mem.mp this
    · intro hx
      rw [hm, Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

omit [Field k] [CommRing H] [HopfAlgebra k H] in
/-- **(a)** Over `k = k̄`, let `T` be a maximal torus that is central (every point commutes with
every point of `T`, over every test algebra). Then every `k`-point of any torus `S` lies in `T`.
Proof: `S · T` is the image of `D(X × Y)` under the Hopf map `ψ = (ι₁ ∘ π_S) * (ι₂ ∘ π_T)`, a
torus containing `T`, hence equal to `T`; evaluate `ψ` at `(s̄, 1)`. -/
theorem torus_point_mem_of_central {k H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
    [Algebra.FiniteType k H] [IsAlgClosed k] {T : HopfIdeal k H}
    (hT : HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) T)
    (hcent : ∀ (A : Type u) [CommRing A] [Algebra k A] (g t : WithConv (H →ₐ[k] A)),
      T.toIdeal ≤ RingHom.ker (ofConv t) → g * t = t * g)
    (S : HopfIdeal k H)
    (hS : torusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) S))
    (s : WithConv (H →ₐ[k] k)) (hs : S.toIdeal ≤ RingHom.ker s.ofConv) :
    T.toIdeal ≤ RingHom.ker s.ofConv := by
  classical
  obtain ⟨r, πS, hπS, hkS⟩ := exists_split_of_torus S hS
  obtain ⟨r', πT, hπT, hkT⟩ := exists_split_of_torus T hT.1
  let X := SplitTorus.characterGroup (ULift.{u} (Fin r))
  let Y := SplitTorus.characterGroup (ULift.{u} (Fin r'))
  let C := MonoidAlgebra k (X × Y)
  let ι1 : MonoidAlgebra k X →ₐc[k] C := MonoidAlgebra.mapDomainBialgHom k (MonoidHom.inl X Y)
  let ι2 : MonoidAlgebra k Y →ₐc[k] C := MonoidAlgebra.mapDomainBialgHom k (MonoidHom.inr X Y)
  let p1 : C →ₐc[k] MonoidAlgebra k X := MonoidAlgebra.mapDomainBialgHom k (MonoidHom.fst X Y)
  let p2 : C →ₐc[k] MonoidAlgebra k Y := MonoidAlgebra.mapDomainBialgHom k (MonoidHom.snd X Y)
  let a : H →ₐc[k] C := ι1.comp πS
  let b : H →ₐc[k] C := ι2.comp πT
  have hab : Commute
      (toConv ((Algebra.TensorProduct.includeRight : C →ₐ[k] C ⊗[k] C).comp (a : H →ₐ[k] C)))
      (toConv ((Algebra.TensorProduct.includeLeft : C →ₐ[k] C ⊗[k] C).comp (b : H →ₐ[k] C))) := by
    refine hcent (C ⊗[k] C) _ _ ?_
    intro x hx
    rw [← hkT] at hx
    have hx' : πT x = 0 := hx
    simp [b, hx']
  let ψ := commMul a b hab
  have hconv : ∀ (D : Type u) [CommRing D] [Algebra k D] (φ : C →ₐ[k] D),
      toConv (φ.comp (ψ : H →ₐ[k] C)) =
        toConv (φ.comp (a : H →ₐ[k] C)) * toConv (φ.comp (b : H →ₐ[k] C)) := fun D _ _ φ ↦ by
    rw [coe_commMul, AlgHom.comp_convMul_distrib, toConv_ofConv, ofConv_toConv, ofConv_toConv]
  have htor := torus_quotient_ker (H := H) (C := C)
    (TauCeti.MonoidAlgebra.groupLikeSetSpan_eq_top (R := k) (X × Y)) ψ
  have hp2a : toConv ((p2 : C →ₐ[k] MonoidAlgebra k Y).comp (a : H →ₐ[k] C)) = 1 := by
    have e : (p2 : C →ₐ[k] MonoidAlgebra k Y).comp (a : H →ₐ[k] C) =
        ((MonoidAlgebra.mapDomainBialgHom k (1 : X →* Y) : MonoidAlgebra k X →ₐc[k] _) :
          MonoidAlgebra k X →ₐ[k] _).comp ((πS : H →ₐc[k] _) : H →ₐ[k] _) := by
      refine AlgHom.ext fun x ↦ ?_
      change p2 (ι1 (πS x)) = MonoidAlgebra.mapDomainBialgHom k (1 : X →* Y) (πS x)
      rw [MonoidAlgebra.mapDomainBialgHom_mapDomainBialgHom, MonoidHom.snd_comp_inl]
    rw [e, mapDomainBialgHom_one_eq, AlgHom.comp_assoc, counitAlgHom_comp_bialgHom',
      AlgHom.convOne_def]
  have hp2b : (p2 : C →ₐ[k] MonoidAlgebra k Y).comp (b : H →ₐ[k] C) = (πT : H →ₐ[k] _) := by
    refine AlgHom.ext fun x ↦ ?_
    change p2 (ι2 (πT x)) = πT x
    rw [MonoidAlgebra.mapDomainBialgHom_mapDomainBialgHom, MonoidHom.snd_comp_inr,
      MonoidAlgebra.mapDomainBialgHom_id]
    rfl
  have hKT : HopfIdeal.ker ψ ≤ T := by
    intro x hx
    rw [HopfIdeal.mem_ker] at hx
    have e := congrArg (fun f : WithConv (H →ₐ[k] MonoidAlgebra k Y) ↦ f.ofConv x)
      (hconv _ (p2 : C →ₐ[k] MonoidAlgebra k Y))
    simp only [hp2a, hp2b, one_mul, ofConv_toConv, AlgHom.comp_apply] at e
    rw [← HopfIdeal.mem_toIdeal, ← hkT, RingHom.mem_ker]
    change πT x = 0
    refine e.symm.trans ?_
    change (p2 : C →ₐ[k] MonoidAlgebra k Y) (ψ x) = 0
    rw [hx, map_zero]
  have hTK : T ≤ HopfIdeal.ker ψ := hT.2 htor hKT
  have hπS' : Function.Surjective (πS : H →ₐ[k] MonoidAlgebra k X) := hπS
  let eS := Ideal.quotientKerAlgEquivOfSurjective hπS'
  let sbar : MonoidAlgebra k X →ₐ[k] k :=
    (Ideal.Quotient.liftₐ (RingHom.ker (πS : H →ₐ[k] MonoidAlgebra k X)) s.ofConv
      (fun y hy ↦ RingHom.mem_ker.mp (hs (hkS ▸ hy)))).comp eS.symm.toAlgHom
  have hsbar : ∀ y, sbar (πS y) = s.ofConv y := fun y ↦ by
    have : eS.symm (πS y) = Ideal.Quotient.mk _ y := by
      rw [AlgEquiv.symm_apply_eq]
      exact (Ideal.quotientKerAlgEquivOfSurjective_mk hπS' y).symm
    dsimp only [sbar]
    rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, this]
    rfl
  let z : C →ₐ[k] k := sbar.comp (p1 : C →ₐ[k] MonoidAlgebra k X)
  have hza : toConv (z.comp (a : H →ₐ[k] C)) = s := by
    refine WithConv.ext (AlgHom.ext fun x ↦ ?_)
    change sbar (p1 (ι1 (πS x))) = s.ofConv x
    rw [MonoidAlgebra.mapDomainBialgHom_mapDomainBialgHom, MonoidHom.fst_comp_inl,
      MonoidAlgebra.mapDomainBialgHom_id]
    exact hsbar _
  have hzb : toConv (z.comp (b : H →ₐ[k] C)) = 1 := by
    have e : z.comp (b : H →ₐ[k] C) = sbar.comp
        (((MonoidAlgebra.mapDomainBialgHom k (1 : Y →* X) : MonoidAlgebra k Y →ₐc[k] _) :
          MonoidAlgebra k Y →ₐ[k] _).comp (πT : H →ₐ[k] _)) := by
      refine AlgHom.ext fun x ↦ ?_
      change sbar (p1 (ι2 (πT x))) =
        sbar (MonoidAlgebra.mapDomainBialgHom k (1 : Y →* X) (πT x))
      rw [MonoidAlgebra.mapDomainBialgHom_mapDomainBialgHom, MonoidHom.fst_comp_inr]
    rw [e, mapDomainBialgHom_one_eq, ← AlgHom.comp_assoc, ← AlgHom.comp_assoc,
      show sbar.comp (Algebra.ofId k (MonoidAlgebra k X)) = Algebra.ofId k k from
        Subsingleton.elim _ _, AlgHom.comp_assoc, counitAlgHom_comp_bialgHom', AlgHom.convOne_def]
  intro x hx
  have hxK : ψ x = 0 := (HopfIdeal.mem_ker ψ).mp (hTK (HopfIdeal.mem_toIdeal.mp hx))
  rw [RingHom.mem_ker]
  have e := congrArg (fun f : WithConv (H →ₐ[k] k) ↦ f.ofConv x) (hconv k z)
  simp only [hza, hzb, mul_one] at e
  refine e.symm.trans ?_
  change z (ψ x) = 0
  rw [hxK, map_zero]

/-! ### Torus-freeness of `[C, C]` from (a), (b), (c) -/

omit [Field k] [CommRing H] [HopfAlgebra k H] in
/-- **`[Q, Q]` has no nontrivial torus**, for `Q` with a central maximal torus `T`, given
**(b)**: `T ∩ [Q, Q]` has finitely many `k`-points. A torus `S` of `[Q, Q]` is a torus of `Q`
(comap), its points lie in `T` by (a) and in `[Q, Q]`, so they are finitely many, so trivial
by (c). -/
theorem noNontrivialTorus_derived {k Q : Type u} [Field k] [IsAlgClosed k] [CommRing Q]
    [HopfAlgebra k Q] [Algebra.FiniteType k Q] {T : HopfIdeal k Q}
    (hT : HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k Q) T)
    (hcent : ∀ (A : Type u) [CommRing A] [Algebra k A] (g t : WithConv (Q →ₐ[k] A)),
      T.toIdeal ≤ RingHom.ker (ofConv t) → g * t = t * g)
    (hfin : {t : WithConv (Q →ₐ[k] k) | T.toIdeal ≤ RingHom.ker t.ofConv ∧
      (TauCeti.CommHopfAlgCat.derivedDefiningIdeal (R := k) Q).toIdeal ≤
        RingHom.ker t.ofConv}.Finite) :
    NoNontrivialTorus k (Q ⧸ (TauCeti.CommHopfAlgCat.derivedDefiningIdeal (R := k) Q).toIdeal) := by
  set D := TauCeti.CommHopfAlgCat.derivedDefiningIdeal (R := k) Q
  intro J' hT' g' hg'
  have hq : Function.Surjective (qMk D) := Ideal.Quotient.mk_surjective
  set J'' := J'.comapOfSurjective (qMk D) hq
  let e : FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k Q) J'' ≅
      FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k (Q ⧸ D.toIdeal)) J' :=
    CategoryTheory.ObjectProperty.isoMk _
      (_root_.CommHopfAlgCat.Hom.quotientIsoOfSurjective
        (H := _root_.CommHopfAlgCat.of k Q)
        (K := _root_.CommHopfAlgCat.of k (Q ⧸ D.toIdeal))
        (_root_.CommHopfAlgCat.ofHom (qMk D)) hq J')
  have hT'' : torusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k Q) J'') :=
    (torusCommHopfAlgProperty k).prop_of_iso e.symm hT'
  have hDJ : D.toIdeal ≤ J''.toIdeal := fun y hy ↦ by
    rw [HopfIdeal.mem_toIdeal, HopfIdeal.mem_comapOfSurjective]
    have : qMk D y = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hy
    rw [this]
    exact HopfIdeal.mem_toIdeal.mp J'.toIdeal.zero_mem
  -- points of `Q ⧸ J''` land in the finite set
  have hmem : ∀ x : WithConv ((Q ⧸ J''.toIdeal) →ₐ[k] k),
      BialgHom.mapDomain (qMk J'') x ∈ {t : WithConv (Q →ₐ[k] k) |
        T.toIdeal ≤ RingHom.ker t.ofConv ∧ D.toIdeal ≤ RingHom.ker t.ofConv} := by
    intro x
    have hJ : J''.toIdeal ≤ RingHom.ker (BialgHom.mapDomain (qMk J'') x).ofConv := by
      intro y hy
      rw [RingHom.mem_ker, BialgHom.mapDomain_apply_apply]
      have : qMk J'' y = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hy
      rw [this, map_zero]
    exact ⟨torus_point_mem_of_central hT hcent J'' hT'' _ hJ, hDJ.trans hJ⟩
  have : Finite (WithConv ((FiniteTypeCommHopfAlgCat.quotient
      (FiniteTypeCommHopfAlgCat.of k Q) J'') →ₐ[k] k)) := by
    have := hfin.to_subtype
    exact Finite.of_injective (fun x : WithConv ((Q ⧸ J''.toIdeal) →ₐ[k] k) ↦
      (⟨BialgHom.mapDomain (qMk J'') x, hmem x⟩ : {t : WithConv (Q →ₐ[k] k) |
        T.toIdeal ≤ RingHom.ker t.ofConv ∧ D.toIdeal ≤ RingHom.ker t.ofConv}))
      fun x y hxy ↦ mapDomain_qMk_injective J'' (congrArg Subtype.val hxy)
  have hsub := torus_points_subsingleton_of_finite _ hT''
  -- the image `u` of `g'` in `G(k)` comes from a point of `Q ⧸ J''`, hence is `1`
  let u := BialgHom.mapDomain (qMk D) g'
  have hu : ∀ y ∈ J''.toIdeal, u.ofConv y = 0 := fun y hy ↦ by
    rw [BialgHom.mapDomain_apply_apply]
    exact hg' _ (HopfIdeal.mem_comapOfSurjective.1 hy)
  let u' : WithConv ((Q ⧸ J''.toIdeal) →ₐ[k] k) :=
    toConv (Ideal.Quotient.liftₐ J''.toIdeal u.ofConv hu)
  have hu' : BialgHom.mapDomain (qMk J'') u' = u := by
    apply WithConv.ofConv_injective
    ext y
    simp [u']
    exact Ideal.Quotient.lift_mk _ _ _
  have h1 : u' = 1 := hsub.elim _ _
  apply mapDomain_qMk_injective D
  change u = _
  rw [← hu', h1, map_one, map_one]

/-- **`CSolvable C`** for `V(C)` connected with a central maximal torus `T`: from (b) and the
`theoremA` inputs `hcl`, `hstep2` for `[C, C]`. -/
theorem cSolvable_of_centralTorus [IsAlgClosed k] [Algebra.FiniteType k H] (C : HopfIdeal k H)
    [ConnectedSpace (PrimeSpectrum
      (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C))]
    {T : HopfIdeal k (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C)}
    (hT : HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k
      (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C)) T)
    (hcent : ∀ (A : Type u) [CommRing A] [Algebra k A] (g t : WithConv
      ((FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C) →ₐ[k] A)),
      T.toIdeal ≤ RingHom.ker (ofConv t) → g * t = t * g)
    (hfin : {t : WithConv
      ((FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C) →ₐ[k] k) |
        T.toIdeal ≤ RingHom.ker t.ofConv ∧
        (TauCeti.CommHopfAlgCat.derivedDefiningIdeal (R := k)
          (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C)).toIdeal ≤
          RingHom.ker t.ofConv}.Finite)
    (hcl : ∀ g : WithConv
      (((FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C) ⧸
        (TauCeti.CommHopfAlgCat.derivedDefiningIdeal (R := k)
          (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C)).toIdeal) →ₐ[k]
        k), ClosureInput g)
    (hstep2 : NoNontrivialTorus k
        ((FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C) ⧸
          (TauCeti.CommHopfAlgCat.derivedDefiningIdeal (R := k)
            (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C)).toIdeal) →
      SemisimplePartsFiniteOrder k
        ((FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C) ⧸
          (TauCeti.CommHopfAlgCat.derivedDefiningIdeal (R := k)
            (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C)).toIdeal) →
      CharpolyValuesFinite k
        ((FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C) ⧸
          (TauCeti.CommHopfAlgCat.derivedDefiningIdeal (R := k)
            (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C)).toIdeal)) :
    BaseCoreB.CSolvable C :=
  cSolvable_of_derived_noNontrivialTorus C hcl hstep2 (noNontrivialTorus_derived hT hcent hfin)

/-! ### Piece (b): `T ∩ [Q, Q]` is finite, from characters of finite index on `T` -/

/-- **Named input (b')**: the characters of `Q` restrict to a finite-index sublattice of the
character lattice of `T`: in any splitting `π_T : Q ↠ k[ℤ^r]` with kernel `T`, some positive
multiple of each basis character is the restriction of a group-like element of `Q`. True for
`C = Z_G(T)` (determinants of the `T`-weight spaces of the right regular representation, which
are left subcomodules; `T` is central), and for `GL₂`, `C = T` (take `n = 1`). -/
def CharactersFiniteIndex {Q : Type u} [CommRing Q] [HopfAlgebra k Q] (T : HopfIdeal k Q) :
    Prop :=
  ∀ (r : ℕ) (πT : Q →ₐc[k] MonoidAlgebra k (SplitTorus.characterGroup (ULift.{u} (Fin r)))),
    Function.Surjective πT →
    RingHom.ker (πT : Q →ₐ[k] MonoidAlgebra k (SplitTorus.characterGroup (ULift.{u} (Fin r)))) =
      T.toIdeal →
    ∀ i : ULift.{u} (Fin r), ∃ (c : GroupLike k Q) (n : ℕ), 0 < n ∧
      πT (c : Q) = MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single i (n : ℤ))) 1

omit [Field k] [CommRing H] [HopfAlgebra k H] in
/-- A point killing the kernel of a surjection `π` factors through `π`. -/
theorem exists_factor_of_le_ker {k Q B : Type u} [Field k] [CommRing Q] [Algebra k Q]
    [CommRing B] [Algebra k B] (π : Q →ₐ[k] B) (hπ : Function.Surjective π)
    (t : Q →ₐ[k] k) (ht : RingHom.ker π ≤ RingHom.ker t) :
    ∃ tb : B →ₐ[k] k, ∀ x, tb (π x) = t x := by
  let eS := Ideal.quotientKerAlgEquivOfSurjective hπ
  refine ⟨(Ideal.Quotient.liftₐ (RingHom.ker π) t (fun y hy ↦ RingHom.mem_ker.mp (ht hy))).comp
    eS.symm.toAlgHom, fun y ↦ ?_⟩
  have : eS.symm (π y) = Ideal.Quotient.mk _ y := by
    rw [AlgEquiv.symm_apply_eq]
    exact (Ideal.quotientKerAlgEquivOfSurjective_mk hπ y).symm
  rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, this]
  rfl

omit [Field k] [CommRing H] [HopfAlgebra k H] in
/-- **(b)** from (b'): `T ∩ [Q, Q]` has finitely many `k`-points. A point `t` of it is
`t̄ ∘ π_T`; on the `i`-th basis character `t̄` takes a value `u` with `u ^ n = t(c) = 1`
(`c - 1 ∈ [Q, Q]`), so `t̄` ranges over a product of finite sets of roots of unity. -/
theorem finite_torus_inter_derived {k Q : Type u} [Field k] [IsAlgClosed k] [CommRing Q]
    [HopfAlgebra k Q] [Algebra.FiniteType k Q] {T : HopfIdeal k Q}
    (hT : torusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k Q) T))
    (hchar : CharactersFiniteIndex T) :
    {t : WithConv (Q →ₐ[k] k) | T.toIdeal ≤ RingHom.ker t.ofConv ∧
      (TauCeti.CommHopfAlgCat.derivedDefiningIdeal (R := k) Q).toIdeal ≤
        RingHom.ker t.ofConv}.Finite := by
  classical
  obtain ⟨r, πT, hπT, hkT⟩ := exists_split_of_torus T hT
  let σ := ULift.{u} (Fin r)
  let π0 : Q →ₐ[k] MonoidAlgebra k (Multiplicative (σ →₀ ℤ)) := (πT : Q →ₐ[k] _)
  have hπT' : Function.Surjective π0 := hπT
  have hk0 : RingHom.ker π0 = T.toIdeal := hkT
  choose c n hn hc using hchar r πT hπT hkT
  have hc' : ∀ i, π0 (c i : Q) =
      MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single i (n i : ℤ))) (1 : k) := hc
  choose f hf using fun i : σ ↦
    hπT' (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single i (1 : ℤ))) (1 : k))
  set S := {t : WithConv (Q →ₐ[k] k) | T.toIdeal ≤ RingHom.ker t.ofConv ∧
      (TauCeti.CommHopfAlgCat.derivedDefiningIdeal (R := k) Q).toIdeal ≤ RingHom.ker t.ofConv}
  let Φ : WithConv (Q →ₐ[k] k) → (σ → k) := fun t i ↦ t.ofConv (f i)
  -- values on the basis characters are roots of unity
  have hroot : ∀ t ∈ S, ∀ i, Φ t i ^ n i = 1 := by
    rintro t ⟨htT, htD⟩ i
    obtain ⟨tb, htb⟩ := exists_factor_of_le_ker π0 hπT' t.ofConv (by rw [hk0]; exact htT)
    have hc1 : t.ofConv (c i : Q) = 1 := by
      have hmem := htD (HopfIdeal.mem_toIdeal.mpr (GroupLike.sub_one_mem_derivedDefiningIdeal
        (c i)))
      rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at hmem
      exact hmem
    change t.ofConv (f i) ^ n i = 1
    rw [← htb (f i), hf i, ← map_pow, MonoidAlgebra.single_pow, one_pow]
    have he : (Multiplicative.ofAdd (Finsupp.single i (1 : ℤ))) ^ n i =
        Multiplicative.ofAdd (Finsupp.single i (n i : ℤ)) := by
      rw [← ofAdd_nsmul, Finsupp.smul_single, nsmul_eq_mul, mul_one]
    rw [he, ← hc' i, htb, hc1]
  -- `Φ` is injective on `S`
  have hinj : Set.InjOn Φ S := by
    rintro t ⟨htT, -⟩ t' ⟨htT', -⟩ htt'
    obtain ⟨tb, htb⟩ := exists_factor_of_le_ker π0 hπT' t.ofConv (by rw [hk0]; exact htT)
    obtain ⟨tb', htb'⟩ := exists_factor_of_le_ker π0 hπT' t'.ofConv (by rw [hk0]; exact htT')
    have hpts : SplitTorus.pointsMulEquiv (σ := σ) (toConv tb) =
        SplitTorus.pointsMulEquiv (σ := σ) (toConv tb') := by
      funext i
      apply Units.ext
      rw [SplitTorus.pointsMulEquiv_apply_coe, SplitTorus.pointsMulEquiv_apply_coe,
        ofConv_toConv, ofConv_toConv, ← hf i, htb, htb']
      exact congrFun htt' i
    have htb_eq : tb = tb' := by
      have := (SplitTorus.pointsMulEquiv).injective hpts
      simpa using congrArg WithConv.ofConv this
    apply WithConv.ofConv_injective
    ext x
    rw [← htb, ← htb', htb_eq]
  -- the image is finite
  have himg : (Φ '' S).Finite := by
    refine (Set.Finite.pi (t := fun i ↦ ((Polynomial.nthRoots (n i) (1 : k)).toFinset : Set k))
      fun i ↦ Finset.finite_toSet _).subset ?_
    rintro _ ⟨t, ht, rfl⟩ i -
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    exact (Polynomial.mem_nthRoots (hn i)).mpr (hroot t ht i)
  exact himg.of_finite_image hinj

/-- **`CSolvable C`** for `V(C)` connected with a central maximal torus `T`, with (b) replaced by
(b') `CharactersFiniteIndex T`. -/
theorem cSolvable_of_centralTorus' [IsAlgClosed k] [Algebra.FiniteType k H] (C : HopfIdeal k H)
    [ConnectedSpace (PrimeSpectrum
      (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C))]
    {T : HopfIdeal k (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C)}
    (hT : HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k
      (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C)) T)
    (hcent : ∀ (A : Type u) [CommRing A] [Algebra k A] (g t : WithConv
      ((FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C) →ₐ[k] A)),
      T.toIdeal ≤ RingHom.ker (ofConv t) → g * t = t * g)
    (hchar : CharactersFiniteIndex T)
    (hcl : ∀ g : WithConv
      (((FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C) ⧸
        (TauCeti.CommHopfAlgCat.derivedDefiningIdeal (R := k)
          (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C)).toIdeal) →ₐ[k]
        k), ClosureInput g)
    (hstep2 : NoNontrivialTorus k
        ((FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C) ⧸
          (TauCeti.CommHopfAlgCat.derivedDefiningIdeal (R := k)
            (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C)).toIdeal) →
      SemisimplePartsFiniteOrder k
        ((FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C) ⧸
          (TauCeti.CommHopfAlgCat.derivedDefiningIdeal (R := k)
            (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C)).toIdeal) →
      CharpolyValuesFinite k
        ((FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C) ⧸
          (TauCeti.CommHopfAlgCat.derivedDefiningIdeal (R := k)
            (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) C)).toIdeal)) :
    BaseCoreB.CSolvable C :=
  cSolvable_of_centralTorus C hT hcent (finite_torus_inter_derived hT.1 hchar) hcl hstep2

end AlgMag.Reductive.NoTorusUnipotent
