/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.T2Classical
import AlgMag.Reductive.RayGa
import AlgMag.Reductive.CuCandidate
import AlgMag.Reductive.OpenCellGen
import AlgMag.Reductive.PushCocharacter
import AlgMag.Reductive.RootDatumFromGPairing
import AlgMag.Reductive.RootDatumBase
import AlgMag.Reductive.AttractorReflects
import AlgMag.Reductive.RegularSlice
import AlgMag.Reductive.HCTReal
import AlgMag.Reductive.Step2BaseChange
import TauCeti.Algebra.AlgebraicGroup.Derived.Basic
import TauCeti.Algebra.AlgebraicGroup.Torus.Basic
import TauCeti.Algebra.AlgebraicGroup.Torus.Maximal
import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Map

/-!
# Step (d) of the classical route: Borel 13.17, Cor. 2 (`StepD`)

`G = Spec H` reductive over `k = k̄`, `T = V(Tq)` with `Tq = ker π` a maximal torus, `C = G^T =
V(magnetHopfIdeal π ⊥)` its centralizer, `C_u = V(CuIdeal π)` the pullback of `R_u(C)`.
Hopf ideals are ordered by inclusion of ideals, so `I ≤ J` means `V(J) ⊆ V(I)`.

**Statement.** `StepD Tq`: if `V(N)` is geometrically connected, smooth and unipotent, and lies in
every Borel `B ⊇ T`, then `V(N) ⊆ R_u(G)` (`Ru ⊥ ≤ N`).

**Proof (`stepD`).**
1. `C_u = 1` (`cuIdeal_eq_augmentation`, proved). `C(k)` normalises `C_u(k)` (`hnormC_CuIdeal`).
   On the rays of `ψ^{±1}` with `rayDim ≤ 1`, `C_u(k)` centralises the root-group points
   (`hcent_CuIdeal_of_rayDim`). `U(ψ⁻¹)(k) ∪ C(k) ∪ U(ψ)(k)` generates `G(k)` (open cell,
   `closure_openCell_eq_top`, `ψ` regular). Hence `C_u` is normal (`normal_of_centralises_rays`,
   `isNormal_of_points`), so it is a unipotent-radical candidate (`hcand_CuIdeal`), and `R_u(G) = 1`.
   This is the "normality via generation" step. It is done for `C_u`, the group which
   `(∩_{B ⊇ T} B)_u` turns out to be.
2. `C = T` from `C_u = 1`. This is `CentralizerOfCuTrivial`, the project's `hCT`. It is a
   parameter of `stepD`, and it is proved in `centralizerOfCuTrivial`, which `stepD'` uses.
3. `V(N) ⊆ C` (proved from the named `ParabolicBorel`). `P(λ_ψ)` and `P(λ_ψ⁻¹)` contain Borels
   `⊇ T`, so `V(N) ⊆ P(λ) ∩ P(λ⁻¹) = Z(λ_ψ)`, and `Z(λ_ψ) = C` for `ψ` regular
   (`levi_magnet_eq_bot`, at the level of Hopf ideals).
4. `V(N) = 1` (proved). `V(N) ⊆ C = T` is normal in the commutative `C`: the derived subgroup of
   the torus is trivial (`derivedDefiningIdeal_eq_augmentation_iff_isCocomm`). It is also
   connected, smooth and unipotent, so it is a unipotent-radical candidate of `C`. Hence
   `V(N) ⊆ R_u(C) = C_u = 1`.
   Then `Ru ⊥ ≤ augmentation = N`.

**Inputs of the final form `stepD_of_bruhat`:**
* `hBruhat`: the existing input of the final theorem, in the same form. It gives `rayDim ≤ 1` on
  every positive ray (`rayDim_le_one_of_bruhat`), which is (ii′).
* `ParabolicBorel`, the **only new named Prop**: for reductive `G` and a **regular** cocharacter
  `λ` of `T`, `P(λ)` contains a Borel `⊇ T`. This is the regular case of CGP (Pseudo-reductive groups; numbering "Prop. 2.2.9" unverified) (`P(λ)`
  is parabolic) plus conjugacy of maximal tori in `P(λ)`. Since `C = T`, it amounts to "`P(λ)` is
  a Borel for `λ` regular". For `GL₃` and `λ` regular, `P(λ)` is the upper-triangular Borel after
  a permutation.

Proved along the way:
* `CentralizerOfCuTrivial` (`hCT`, `C_u = 1 ⇒ C = T`), in `centralizerOfCuTrivial`. `C` is
  connected and solvable (`hsolvC_of_step2OverFpBar` with the proved `step2OverFpBar`), so
  `HCTReal.hCT` applies.
* The regular cocharacter `ψ`, in `exists_regular_cocharacter`.
`Z_G(T) = T` is not assumed: steps 1–2 prove it, given `hBruhat`.

**Hypothesis `hT` is necessary.** `StepD Tq` is false for an arbitrary `Tq`. Take `G = SL₂` and
`Tq = ⊥` (`V(Tq) = G`). No Borel contains `G`, so the hypothesis on `N` is vacuous. But `N` = the
ideal of the upper unipotent subgroup satisfies `Ru ⊥ = augmentation ≰ N`.
-/

open Magnetism TauCeti TauCeti.Cocharacter WithConv CategoryTheory

namespace AlgMag.Reductive.StepDProof

open AlgMag.Reductive AlgMag.Reductive.BorelRoute AlgMag.Reductive.BorelRouteReal
  AlgMag.Reductive.T2Classical

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable [Algebra.FiniteType k H]
variable (π : H →ₐc[k] MonoidAlgebra k X)

local notation "Hf" => FiniteTypeCommHopfAlgCat.of k H

/-- **Regular parabolics contain Borels** (named). Let `G` be reductive and `φ` a regular
cocharacter of `T = V(ker π)` (nonzero on every root). Then `P(λ_φ)` contains a Borel subgroup
`B ⊇ T`. This is the special case of CGP (Pseudo-reductive groups; numbering "Prop. 2.2.9" unverified) (`P(λ)` is parabolic) with conjugacy of
maximal tori of `P(λ)`. Since `C = T` (proved here from `hBruhat`), it says `P(λ_φ)` is a Borel:
the classical "Borels `⊇ T` ↔ Weyl chambers". -/
def ParabolicBorel (hπ : Function.Surjective π) : Prop :=
  reductiveCommHopfAlgProperty k Hf → ∀ φ : X →* Multiplicative ℤ,
    (∀ α ∈ roots π, pairingHom φ α ≠ 0) → ∃ B : HopfIdeal k H,
      IsBorelIn ⊥ B ∧ B ≤ HopfIdeal.kerOfSurjective π hπ ∧ P (π.cocharacter φ) ≤ B

/-- **`C_u = 1 ⇒ C = T`** (named; the project's `hCT`, Borel port): `C = Z_G(T)` is
`T × R_u(C)`. -/
def CentralizerOfCuTrivial (hπ : Function.Surjective π) : Prop :=
  CuIdeal π = HopfIdeal.augmentation k H → magnetHopfIdeal π ⊥ = HopfIdeal.kerOfSurjective π hπ

/-- **Step 1: `C_u = 1`** for reductive `G`, from `rayDim ≤ 1` on the rays of `ψ^{±1}` (`ψ`
regular). `C_u` is normal by generation of `G(k)` by the open cell, so it is a unipotent-radical
candidate, and `R_u(G) = 1`. -/
theorem cuIdeal_eq_augmentation [IsAlgClosed k] [Algebra.Smooth k H]
    [Module.Finite k (Bialgebra.CotangentSpace k H)] [ConnectedSpace (PrimeSpectrum H)]
    (hred : reductiveCommHopfAlgProperty k Hf)
    (ψ : X →* Multiplicative ℤ) (hψ : ∀ α ∈ roots π, pairingHom ψ α ≠ 0)
    (hray : ∀ φ : X →* Multiplicative ℤ, (φ = ψ ∨ φ = ψ⁻¹) → ∀ α : PosRay φ,
      rayDim π (pairingHom φ) α.1 ≤ 1) :
    CuIdeal π = HopfIdeal.augmentation k H := by
  haveI : IsReduced H := TauCeti.isReduced_of_smooth k H
  haveI : IrreducibleSpace (PrimeSpectrum H) := OpenCellNotes.irreducibleSpace_of_connectedSpace k
  set Np := CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of k H) (CuIdeal π)
    (CommAlgCat.of k k)
  have hmem : ∀ g : WithConv (H →ₐ[k] k), g ∈ Np ↔ ∀ y ∈ CuIdeal π, g.ofConv y = 0 := fun g =>
    CommHopfAlgCat.mem_quotientPointsSubgroup_iff (CommHopfAlgCat.of k H) (CuIdeal π)
      (CommAlgCat.of k k) g
  have hcent := hcent_CuIdeal_of_rayDim π hray
  have hN : Np.Normal := normal_of_centralises_rays π ψ Np
    (fun φ hφ α r hr c hc => hcent φ hφ α r hr c ((hmem c).1 hc))
    (fun z hz c hc => (hmem _).2 (hnormC_CuIdeal π z hz c ((hmem c).1 hc)))
    (closure_openCell_eq_top π ψ (levi_le_attractor_bot π ψ hψ))
  have hnorm : (CuIdeal π).IsNormal := isNormal_of_points (CuIdeal π) fun g c hc y hy =>
    (hmem _).1 (hN.conj_mem c ((hmem c).2 hc) g) y hy
  exact eq_augmentation_of_candidate hred.unipotentRadicalDefiningIdeal_eq_augmentation
    (CuIdeal π) (hcand_CuIdeal π hnorm)

/-- **Step 3: `V(N) ⊆ C`.** If `N` lies in Borels `B₁ ⊆ P(λ_ψ)`, `B₂ ⊆ P(λ_ψ⁻¹)`, then
`V(N) ⊆ Z(λ_ψ) = C` (`ψ` regular). -/
theorem magnet_bot_le [IsAlgClosed k] [Algebra.Smooth k H]
    [Module.Finite k (Bialgebra.CotangentSpace k H)] [IrreducibleSpace (PrimeSpectrum H)]
    (ψ : X →* Multiplicative ℤ) (hψ : ∀ α ∈ roots π, pairingHom ψ α ≠ 0) {N : HopfIdeal k H}
    (h1 : P (π.cocharacter ψ) ≤ N) (h2 : P (π.cocharacter ψ⁻¹) ≤ N) :
    magnetHopfIdeal π ⊥ ≤ N := by
  rw [cocharacter_inv] at h2
  have hZ : Z (π.cocharacter ψ) ≤ N := by rw [Z_eq]; exact sup_le h1 h2
  rw [← levi_magnet_eq_bot π ψ hψ]
  refine le_trans ?_ hZ
  rw [← HopfIdeal.toIdeal_le_toIdeal, magnetHopfIdeal_toIdeal, magnetIdeal_torusGrading_comap_bot]

/-- `H ⧸ J' ≅ (H ⧸ C) ⧸ J` for `J'` the pullback of a Hopf ideal `J` of `H ⧸ C`. -/
noncomputable def quotIso (J : HopfIdeal k (H ⧸ (magnetHopfIdeal π ⊥).toIdeal)) :
    FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H)
        (J.comapOfSurjective (cMk π) (cMk_surjective π)) ≅
      FiniteTypeCommHopfAlgCat.quotient
        (FiniteTypeCommHopfAlgCat.of k (H ⧸ (magnetHopfIdeal π ⊥).toIdeal)) J :=
  ObjectProperty.isoMk _
    (_root_.CommHopfAlgCat.Hom.quotientIsoOfSurjective
      (H := _root_.CommHopfAlgCat.of k H)
      (K := _root_.CommHopfAlgCat.of k (H ⧸ (magnetHopfIdeal π ⊥).toIdeal))
      (_root_.CommHopfAlgCat.ofHom (cMk π)) (cMk_surjective π) J)

/-- Candidate properties descend from `H ⧸ J'` to `(H ⧸ C) ⧸ J`. -/
lemma isCandidate_of_comap (J : HopfIdeal k (H ⧸ (magnetHopfIdeal π ⊥).toIdeal))
    (hJ : J.IsNormal)
    (hgc : geometricallyConnectedCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient Hf (J.comapOfSurjective (cMk π) (cMk_surjective π))).obj)
    (hsu : smoothUnipotentCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient Hf (J.comapOfSurjective (cMk π) (cMk_surjective π)))) :
    HopfIdeal.IsUnipotentRadicalCandidate
      (FiniteTypeCommHopfAlgCat.of k (H ⧸ (magnetHopfIdeal π ⊥).toIdeal)) J :=
  ⟨hJ, (geometricallyConnectedCommHopfAlgProperty k).prop_of_iso
    ((ObjectProperty.ι _).mapIso (quotIso π J)) hgc,
    (smoothUnipotentCommHopfAlgProperty k).prop_of_iso (quotIso π J) hsu⟩

/-- In a cocommutative `H ⧸ C` (here `C = T`), every Hopf ideal is normal. -/
lemma isNormal_of_cocomm (hco : Coalgebra.IsCocomm k (H ⧸ (magnetHopfIdeal π ⊥).toIdeal))
    (J : HopfIdeal k (H ⧸ (magnetHopfIdeal π ⊥).toIdeal)) : J.IsNormal := by
  have hder := (TauCeti.CommHopfAlgCat.derivedDefiningIdeal_eq_augmentation_iff_isCocomm
    (R := k) (H ⧸ (magnetHopfIdeal π ⊥).toIdeal)).2 hco
  apply TauCeti.CommHopfAlgCat.isNormal_of_le_derivedDefiningIdeal
    (_root_.CommHopfAlgCat.of k (H ⧸ (magnetHopfIdeal π ⊥).toIdeal)) J
  rw [hder]
  exact HopfIdeal.le_augmentation k _ J

/-- **Step 4: a connected smooth unipotent `V(N) ⊆ C` with `C` commutative lies in `C_u`.** -/
theorem cuIdeal_le_of_cocomm {N : HopfIdeal k H} (hCN : magnetHopfIdeal π ⊥ ≤ N)
    (hco : Coalgebra.IsCocomm k (H ⧸ (magnetHopfIdeal π ⊥).toIdeal))
    (hgc : geometricallyConnectedCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient Hf N).obj)
    (hsu : smoothUnipotentCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient Hf N)) :
    CuIdeal π ≤ N := by
  have hJN : (N.map (cMk π)).comapOfSurjective (cMk π) (cMk_surjective π) = N :=
    HopfIdeal.comapOfSurjective_map_mkBialgHom hCN
  rw [← hJN] at hgc hsu
  have hRuJ : RuC π ≤ N.map (cMk π) :=
    FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_le _ _
      (isCandidate_of_comap π _ (isNormal_of_cocomm π hco _) hgc hsu)
  intro y hy
  rw [CuIdeal_eq_comapOfSurjective, HopfIdeal.mem_comapOfSurjective] at hy
  rw [← hJN, HopfIdeal.mem_comapOfSurjective]
  exact hRuJ hy

/-- **Step (d), Borel 13.17 Cor. 2: `StepD` for a maximal torus `T = V(ker π)`.** Named inputs:
`hray` ((ii′) on the rays of a regular `ψ^{±1}`), `hCT` (`C_u = 1 ⇒ C = T`), `hPB` (parabolics
contain Borels). -/
theorem stepD [IsAlgClosed k] [Algebra.Smooth k H]
    [Module.Finite k (Bialgebra.CotangentSpace k H)] [ConnectedSpace (PrimeSpectrum H)]
    (hπ : Function.Surjective π)
    (hT : HopfIdeal.IsMaximalTorus k (CommHopfAlgCat.of k H) (HopfIdeal.kerOfSurjective π hπ))
    (ψ : X →* Multiplicative ℤ) (hψ : ∀ α ∈ roots π, pairingHom ψ α ≠ 0)
    (hray : ∀ φ : X →* Multiplicative ℤ, (φ = ψ ∨ φ = ψ⁻¹) → ∀ α : PosRay φ,
      rayDim π (pairingHom φ) α.1 ≤ 1)
    (hCT : CentralizerOfCuTrivial π hπ) (hPB : ParabolicBorel π hπ) :
    StepD (HopfIdeal.kerOfSurjective π hπ) := by
  intro hred N hgc hsu hB
  haveI : IrreducibleSpace (PrimeSpectrum H) := OpenCellNotes.irreducibleSpace_of_connectedSpace k
  -- Step 1: `C_u = 1`; step 2: `C = T`.
  have hCu := cuIdeal_eq_augmentation π hred ψ hψ hray
  have hC := hCT hCu
  -- Step 3: `V(N) ⊆ C`.
  obtain ⟨B₁, hB₁, hB₁T, hPB₁⟩ := hPB hred ψ hψ
  obtain ⟨B₂, hB₂, hB₂T, hPB₂⟩ := hPB hred ψ⁻¹ fun α hα => by simpa using hψ α hα
  have hCN : magnetHopfIdeal π ⊥ ≤ N :=
    magnet_bot_le π ψ hψ (hPB₁.trans (hB B₁ hB₁ hB₁T)) (hPB₂.trans (hB B₂ hB₂ hB₂T))
  -- Step 4: `C = T` is commutative, so `V(N) ⊆ C_u = 1`.
  have hcoT : Coalgebra.IsCocomm k (H ⧸ (HopfIdeal.kerOfSurjective π hπ).toIdeal) :=
    torusCommHopfAlgProperty.isCocomm k _ hT.prop
  have hco : Coalgebra.IsCocomm k (H ⧸ (magnetHopfIdeal π ⊥).toIdeal) := by
    rw [hC]; exact hcoT
  have hCuN := cuIdeal_le_of_cocomm π hCN hco hgc hsu
  rw [hCu] at hCuN
  exact (HopfIdeal.le_augmentation k H (Ru ⊥)).trans hCuN

/-- **A regular cocharacter exists.** `X` is free of finite rank (`k[X]` is a quotient of `H`),
and `roots π` is finite and avoids `0`. -/
theorem exists_regular_cocharacter [Module.IsTorsionFree ℤ (Additive X)]
    [Module.Finite k (Bialgebra.CotangentSpace k H)] (hπ : Function.Surjective π) :
    ∃ ψ : X →* Multiplicative ℤ, ∀ α ∈ roots π, pairingHom ψ α ≠ 0 := by
  have : Algebra.FiniteType k (MonoidAlgebra k X) :=
    Algebra.FiniteType.of_surjective π.toAlgHom hπ
  haveI : Monoid.FG X := MonoidAlgebra.fg_of_finiteType (R := k)
  haveI : Module.Finite ℤ (Additive X) :=
    Module.Finite.iff_addGroup_fg.2 (AddGroup.fg_iff_addMonoid_fg.2
      (Monoid.fg_iff_add_fg.1 inferInstance))
  haveI : Module.Free ℤ (Additive X) := Module.free_of_finite_type_torsion_free'
  haveI : Finite (roots π) := (finite_roots (π := π)).to_subtype
  obtain ⟨f, hf⟩ := AlgMag.RootDatumBase.exists_forall_ne_zero_int
    (fun α : roots π => (Module.Dual.eval ℤ (Additive X) α.1).toAddMonoidHom) fun α => by
      by_contra h
      push_neg at h
      exact ne_zero_of_mem_roots α.2
        ((Module.forall_dual_apply_eq_zero_iff ℤ (α.1 : Additive X)).1 fun g => by simpa using h g)
  refine ⟨{ toFun := fun x => Multiplicative.ofAdd (f (Additive.ofMul x))
            map_one' := by simp
            map_mul' := fun a b => by simp only [ofMul_mul, map_add, ofAdd_add] },
    fun α hα => ?_⟩
  simpa [pairingHom_apply] using hf ⟨α, hα⟩

/-- **`hCT` is proved** (`C_u = 1 ⇒ C = T`). `C = Z_G(T)` is connected, being the Levi of a
generic cocharacter. It is solvable by `hsolvC_of_step2OverFpBar` with the proved
`Step2BaseChange.step2OverFpBar`. Then `HCTReal.hCT` applies: `C` is reductive and solvable,
hence a torus, and `T` is maximal. -/
theorem centralizerOfCuTrivial [IsAlgClosed k] [Module.IsTorsionFree ℤ (Additive X)]
    [Algebra.Smooth k H] [ConnectedSpace (PrimeSpectrum H)] (hπ : Function.Surjective π)
    (hT : HopfIdeal.IsMaximalTorus k (CommHopfAlgCat.of k H) (HopfIdeal.kerOfSurjective π hπ)) :
    CentralizerOfCuTrivial π hπ := by
  haveI : IrreducibleSpace (PrimeSpectrum H) := OpenCellNotes.irreducibleSpace_of_connectedSpace k
  have : Algebra.FiniteType k (MonoidAlgebra k X) :=
    Algebra.FiniteType.of_surjective π.toAlgHom hπ
  haveI : Monoid.FG X := MonoidAlgebra.fg_of_finiteType (R := k)
  haveI : Module.Finite ℤ (Additive X) :=
    Module.Finite.iff_addGroup_fg.2 (AddGroup.fg_iff_addMonoid_fg.2
      (Monoid.fg_iff_add_fg.1 inferInstance))
  haveI : Module.Free ℤ (Additive X) := Module.free_of_finite_type_torsion_free'
  have hconnC : geometricallyConnectedCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient
      (FiniteTypeCommHopfAlgCat.of k H) (magnetHopfIdeal π ⊥)).obj := by
    obtain ⟨ψc, hψc⟩ := Final2.exists_magnetIdeal_bot_eq_levi π
    rw [geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace]
    have h0 := connectedSpace_levi_of_openCell (π.cocharacter ψc) (isOpenEmbedding_openCell _)
    have h' : ConnectedSpace (PrimeSpectrum (H ⧸ (magnetHopfIdeal π ⊥).toIdeal)) := by
      rw [magnetHopfIdeal_toIdeal, hψc, magnetIdeal_torusGrading_comap_bot]; exact h0
    exact h'
  haveI : ConnectedSpace (PrimeSpectrum (FiniteTypeCommHopfAlgCat.quotient
      (FiniteTypeCommHopfAlgCat.of k H) (magnetHopfIdeal π ⊥))) :=
    (geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace k _).1 hconnC
  have hsolvC := hsolvC_of_step2OverFpBar π hπ hT Step2BaseChange.step2OverFpBar
  exact HCTReal.hCT π hπ (CuIdeal π) (smooth_quotient_magnetHopfIdeal π ⊥) hconnC hsolvC
    (Final2.RuC_eq_augmentation π) hT (Final2.magnetHopfIdeal_bot_le_ker π hπ)

/-- **`StepD` for a maximal torus, from (ii′) on all rays and `ParabolicBorel`.** The regular
`ψ` is constructed (`exists_regular_cocharacter`) and `hCT` is proved
(`centralizerOfCuTrivial`). Smoothness and connectedness come from reductivity. -/
theorem stepD' [IsAlgClosed k] [Module.IsTorsionFree ℤ (Additive X)]
    (hπ : Function.Surjective π)
    (hT : HopfIdeal.IsMaximalTorus k (CommHopfAlgCat.of k H) (HopfIdeal.kerOfSurjective π hπ))
    (hray : ∀ φ : X →* Multiplicative ℤ, ∀ α : PosRay φ, rayDim π (pairingHom φ) α.1 ≤ 1)
    (hPB : ParabolicBorel π hπ) :
    StepD (HopfIdeal.kerOfSurjective π hπ) := by
  intro hred
  letI : Algebra.Smooth k H := hred.smooth
  haveI : ConnectedSpace (PrimeSpectrum H) :=
    connectedSpace_of_geometricallyConnected k H hred.geometricallyConnected
  obtain ⟨ψ, hψ⟩ := exists_regular_cocharacter π hπ
  exact stepD π hπ hT ψ hψ (fun φ _ α => hray φ α) (centralizerOfCuTrivial π hπ hT) hPB hred

/-- **(c) + (d) ⇒ `R_u(Z(μ)) ⊆ R_u(G)`** with `StepD` discharged by `stepD'`. -/
theorem ruZ_le_ruG_of [IsAlgClosed k] [Module.IsTorsionFree ℤ (Additive X)]
    (hπ : Function.Surjective π)
    (hT : HopfIdeal.IsMaximalTorus k (CommHopfAlgCat.of k H) (HopfIdeal.kerOfSurjective π hπ))
    (hred : reductiveCommHopfAlgProperty k Hf) {μ : H →ₐc[k] LaurentPolynomial k}
    (hc : StepC (HopfIdeal.kerOfSurjective π hπ) μ) (hU : RuZUnip μ)
    (hray : ∀ φ : X →* Multiplicative ℤ, ∀ α : PosRay φ, rayDim π (pairingHom φ) α.1 ≤ 1)
    (hPB : ParabolicBorel π hπ) :
    Ru ⊥ ≤ Ru (Z μ) :=
  ruZ_le_ruG hred hc (stepD' π hπ hT hray hPB) hU

section Bruhat

open R1Opp R1Build R1Dis Final2 AlgMag.Weyl

/-- **(ii′) on every positive ray from the Bruhat cores on root rays.** This is the `hray`
derivation inside `EquivalenceFinal2`, extracted as a standalone lemma. Rays without a root have
`rayDim = 0`. -/
theorem rayDim_le_one_of_bruhat [IsAlgClosed k] [Module.IsTorsionFree ℤ (Additive X)]
    (hred : reductiveCommHopfAlgProperty k Hf)
    (hBruhat : letI : Algebra.Smooth k H := hred.smooth
      haveI : IsMulTorsionFree X := ⟨fun n hn =>
        (IsAddTorsionFree.of_isTorsionFree ℤ (Additive X)).nsmul_right_injective hn⟩
      ∀ (ψ : X →* Multiplicative ℤ) (α : Additive X) (hα : 0 < pairingHom ψ α),
        α ∈ roots π → BruhatRayCore π ψ α hα) :
    ∀ φ : X →* Multiplicative ℤ, ∀ α : PosRay φ, rayDim π (pairingHom φ) α.1 ≤ 1 := by
  letI : Algebra.Smooth k H := hred.smooth
  haveI : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
  haveI : IsAddTorsionFree (Additive X) := .of_isTorsionFree ℤ (Additive X)
  haveI : IsMulTorsionFree X :=
    ⟨fun n hn => IsAddTorsionFree.nsmul_right_injective (M := Additive X) hn⟩
  haveI : ConnectedSpace (PrimeSpectrum H) :=
    connectedSpace_of_geometricallyConnected k H hred.geometricallyConnected
  haveI : IrreducibleSpace (PrimeSpectrum H) := OpenCellNotes.irreducibleSpace_of_connectedSpace k
  intro ψ ⟨α, hα⟩
  classical
  by_cases hne : ((posRoots π (pairingHom ψ)).filter (fun β => SameRayRel β α)).Nonempty
  · obtain ⟨β, hβ⟩ := hne
    obtain ⟨hβP, hβα⟩ := Finset.mem_filter.1 hβ
    obtain ⟨hβR, hβpos⟩ := Finset.mem_filter.1 hβP
    have heq : rayDim π (pairingHom ψ) α = rayDim π (pairingHom ψ) β := by
      unfold rayDim
      refine Finset.sum_congr (Finset.filter_congr fun γ _ => ?_) fun _ _ => rfl
      exact ⟨fun h => (sameRayRel_equivalence (X := X)).trans h
          ((sameRayRel_equivalence (X := X)).symm hβα),
        fun h => (sameRayRel_equivalence (X := X)).trans h hβα⟩
    change rayDim π (pairingHom ψ) α ≤ 1
    rw [heq]
    letI : Algebra.Smooth k (ZAlg π (rayGen π ψ β hβpos).1) :=
      smooth_quotient_magnetHopfIdeal π _
    have hc := hBruhat ψ β hβpos ((finite_roots (π := π)).mem_toFinset.1 hβR)
    exact rayDim_le_one π (rayDimData_of_hAff π ψ β hβpos
      (hAff_of_bruhatCore _ hc.choose _ _ hc.choose_spec))
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    change rayDim π (pairingHom ψ) α ≤ 1
    unfold rayDim
    rw [hne]
    simp

/-- **`StepD` from the final theorem's own `hBruhat`**, plus `ParabolicBorel`. -/
theorem stepD_of_bruhat [IsAlgClosed k] [Module.IsTorsionFree ℤ (Additive X)]
    (hπ : Function.Surjective π)
    (hT : HopfIdeal.IsMaximalTorus k (CommHopfAlgCat.of k H) (HopfIdeal.kerOfSurjective π hπ))
    (hred : reductiveCommHopfAlgProperty k Hf)
    (hBruhat : letI : Algebra.Smooth k H := hred.smooth
      haveI : IsMulTorsionFree X := ⟨fun n hn =>
        (IsAddTorsionFree.of_isTorsionFree ℤ (Additive X)).nsmul_right_injective hn⟩
      ∀ (ψ : X →* Multiplicative ℤ) (α : Additive X) (hα : 0 < pairingHom ψ α),
        α ∈ roots π → BruhatRayCore π ψ α hα)
    (hPB : ParabolicBorel π hπ) :
    StepD (HopfIdeal.kerOfSurjective π hπ) :=
  stepD' π hπ hT (rayDim_le_one_of_bruhat π hred hBruhat) hPB

end Bruhat

end AlgMag.Reductive.StepDProof

#print axioms AlgMag.Reductive.StepDProof.rayDim_le_one_of_bruhat
#print axioms AlgMag.Reductive.StepDProof.stepD_of_bruhat
#print axioms AlgMag.Reductive.StepDProof.centralizerOfCuTrivial
#print axioms AlgMag.Reductive.StepDProof.exists_regular_cocharacter
#print axioms AlgMag.Reductive.StepDProof.stepD'
#print axioms AlgMag.Reductive.StepDProof.ruZ_le_ruG_of
#print axioms AlgMag.Reductive.StepDProof.cuIdeal_eq_augmentation
#print axioms AlgMag.Reductive.StepDProof.magnet_bot_le
#print axioms AlgMag.Reductive.StepDProof.cuIdeal_le_of_cocomm
#print axioms AlgMag.Reductive.StepDProof.stepD
