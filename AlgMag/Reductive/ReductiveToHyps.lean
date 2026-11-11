/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.Equivalence

/-!
# Theorem D for split reductive groups over any field, from the equivalence

`G = Spec H` over a field `k` with a split torus `π : H → k[X]` (`π` surjective).

**Definitions (SGA3).** As in the paper, which follows SGA3 (Exp. XIX 2.7, XII 1.3), "`G` reductive"
and "`T` a maximal torus" over `k` are geometric notions: `G_{k̄}` is reductive
(`reductiveCommHopfAlgProperty k̄ (k̄ ⊗ H)`) and `T_{k̄}` is a maximal torus of `G_{k̄}`
(`IsMaximalTorus k̄` of `ker π_{k̄}`). These are the hypotheses `hred`, `hT` below. Apply
`condI_condII_condIII_of_reductive` over `k̄` and translate. Its two geometric inputs over `k̄`
(`DimCountInput`, `R1Input`, Equivalence.lean) are explicit hypotheses `hDC`, `hR1` here:

* `hypZ_of_reductive`: (Z) over `k`, descended from (i) over `k̄` (`comap_map_includeRight`);
* `hypR1bar_of_reductive`: (R1) for `G_{k̄}` (`CondIII.r1`);
* `hypR2_of_reductive`: (R2′) (`CondII.monogenic` over `k̄`).

(R1) with `k`-rational Weyl elements (`HypR1 π`) is not needed: the theorems of §13 follow from
split reductive data over `k̄` (`barData`, `*_fieldBar`, DescentToField.lean), with the same
Weyl group `weylGroup π k̄` as the `*_G` theorems of FromR1R2.lean.
-/

suppress_compilation

open TensorProduct Magnetism TauCeti WithConv AlgMag.Weyl

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable [Algebra.FiniteType k H]

local notation "K" => AlgebraicClosure k

variable [Module.IsTorsionFree ℤ (Additive X)]

/-- `G` smooth over `k` from `G_{k̄}` reductive (faithfully flat descent of smoothness). -/
theorem smooth_of_reductive_bar
    (hred : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K (K ⊗[k] H))) :
    Algebra.Smooth k H := by
  haveI : Algebra.Smooth K (K ⊗[k] H) := hred.smooth
  exact Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat (R := k) (S := H) K

/-- (i), (ii′), (iii) for `G_{k̄}`, from the equivalence over `k̄`. -/
theorem conds_bar_of_reductive (π : H →ₐc[k] MonoidAlgebra k X) (hπ : Function.Surjective π)
    (hT : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K (K ⊗[k] H))
      (HopfIdeal.kerOfSurjective (piBar π) (torusBaseChange_surjective (AlgebraicClosure k) hπ)))
    (hred : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K (K ⊗[k] H)))
    (hDC : DimCountInput (piBar π) (torusBaseChange_surjective (AlgebraicClosure k) hπ))
    (hR1 : R1Input (piBar π)) :
    CondI (piBar π) ∧ CondII (piBar π) ∧ CondIII (piBar π) :=
  condI_condII_condIII_of_reductive (piBar π) (torusBaseChange_surjective _ hπ) hT hred hDC hR1

/-! ### Translation into `HypZ`, (R1) over `k̄`, `HypR2` -/

/-- **(Z)** over `k`: descended from (i) over `k̄`. -/
theorem hypZ_of_reductive (π : H →ₐc[k] MonoidAlgebra k X) (hπ : Function.Surjective π)
    (hT : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K (K ⊗[k] H))
      (HopfIdeal.kerOfSurjective (piBar π) (torusBaseChange_surjective (AlgebraicClosure k) hπ)))
    (hred : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K (K ⊗[k] H)))
    (hDC : DimCountInput (piBar π) (torusBaseChange_surjective (AlgebraicClosure k) hπ))
    (hR1 : R1Input (piBar π)) :
    HypZ π := by
  have h := (conds_bar_of_reductive π hπ hT hred hDC hR1).1
  unfold CondI at h
  rw [magnetIdeal_baseChange, ker_torusBaseChange _ _ hπ] at h
  unfold HypZ
  rw [← comap_map_includeRight (k := k) K (magnetIdeal (torusGrading π) ⊥), h,
    comap_map_includeRight (k := k) K]

/-- **(R1) for `G_{k̄}`** (the conclusion of `hypR1_bar`). -/
theorem hypR1bar_of_reductive (π : H →ₐc[k] MonoidAlgebra k X) (hπ : Function.Surjective π)
    (hT : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K (K ⊗[k] H))
      (HopfIdeal.kerOfSurjective (piBar π) (torusBaseChange_surjective (AlgebraicClosure k) hπ)))
    (hred : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K (K ⊗[k] H)))
    (hDC : DimCountInput (piBar π) (torusBaseChange_surjective (AlgebraicClosure k) hπ))
    (hR1 : R1Input (piBar π)) :
    ∀ α ∈ roots (piBar π), ∃ (n : WithConv (K ⊗[k] H →ₐ[K] K)) (σ : X ≃* X),
      IsNormalizingWith (piBar π) K n σ ∧ n ∈ attractorSubgroup (piBar π) (lineMagnet α) K ∧
        σ ≠ 1 :=
  (conds_bar_of_reductive π hπ hT hred hDC hR1).2.2.r1

/-- **(R2′)**: `O(U_α)` of `G_{k̄}` is monogenic. -/
theorem hypR2_of_reductive (π : H →ₐc[k] MonoidAlgebra k X) (hπ : Function.Surjective π)
    (hT : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K (K ⊗[k] H))
      (HopfIdeal.kerOfSurjective (piBar π) (torusBaseChange_surjective (AlgebraicClosure k) hπ)))
    (hred : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K (K ⊗[k] H)))
    (hDC : DimCountInput (piBar π) (torusBaseChange_surjective (AlgebraicClosure k) hπ))
    (hR1 : R1Input (piBar π)) :
    HypR2 π := by
  haveI : Algebra.Smooth k H := smooth_of_reductive_bar hred
  intro α hα
  exact (conds_bar_of_reductive π hπ hT hred hDC hR1).2.1.monogenic hα (nsmul_eq_zero_of_mem_roots hα)

/-! ### Theorem D, unconditional -/

section Unconditional

/-- SGA3: `T = D(X)` is a maximal torus of `G` iff `T_{k̄}` is a maximal torus of `G_{k̄}`. -/
def IsMaximalTorusBar (π : H →ₐc[k] MonoidAlgebra k X) (hπ : Function.Surjective π) : Prop :=
  HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K (K ⊗[k] H))
    (HopfIdeal.kerOfSurjective (piBar π) (torusBaseChange_surjective (AlgebraicClosure k) hπ))

omit [DecidableEq X] [Module.IsTorsionFree ℤ (Additive X)] in
/-- SGA3: `G` is reductive iff `G_{k̄}` is reductive. -/
def IsReductiveBar (k H : Type u) [Field k] [CommRing H] [HopfAlgebra k H]
    [Algebra.FiniteType k H] : Prop :=
  reductiveCommHopfAlgProperty (AlgebraicClosure k)
    (FiniteTypeCommHopfAlgCat.of (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] H))

variable {π : H →ₐc[k] MonoidAlgebra k X} (hπ : Function.Surjective π)
  (hT : IsMaximalTorusBar π hπ) (hred : IsReductiveBar k H)
  (hDC : DimCountInput (piBar π) (torusBaseChange_surjective (AlgebraicClosure k) hπ))
  (hR1 : R1Input (piBar π))
include hπ hT hred hDC hR1

/-- The standing instances of §13, from reductivity and `π` surjective. -/
theorem instances_of_reductive :
    Algebra.Smooth k H ∧ Monoid.FG X ∧ IsMulTorsionFree X ∧ Module.Finite ℤ (Additive X) ∧
      ConnectedSpace (PrimeSpectrum (K ⊗[k] H)) := by
  have : Algebra.FiniteType k (MonoidAlgebra k X) :=
    Algebra.FiniteType.of_surjective π.toAlgHom hπ
  haveI : Monoid.FG X := MonoidAlgebra.fg_of_finiteType (R := k)
  haveI : Module.Finite ℤ (Additive X) :=
    Module.Finite.iff_addGroup_fg.2 (AddGroup.fg_iff_addMonoid_fg.2
      (Monoid.fg_iff_add_fg.1 inferInstance))
  haveI : IsAddTorsionFree (Additive X) := .of_isTorsionFree ℤ (Additive X)
  refine ⟨smooth_of_reductive_bar hred, inferInstance,
    ⟨fun n hn => IsAddTorsionFree.nsmul_right_injective (M := Additive X) hn⟩, inferInstance, ?_⟩
  exact connectedSpace_of_geometricallyConnected (k := K) (A := K ⊗[k] H)
    hred.geometricallyConnected

/-- **Split reductive data over `k̄`** for a reductive `G` with split maximal torus. -/
def barDataOfReductive : SplitReductiveData (piBar π) :=
  haveI : Monoid.FG X := (instances_of_reductive hπ hT hred hDC hR1).2.1
  haveI : Group.FG X := Group.fg_iff_monoid_fg.mpr inferInstance
  barData hπ (hypZ_of_reductive π hπ hT hred hDC hR1)

/-- Split reductive data with one-dimensional root spaces for `G_{k̄}`. -/
def withRootSpacesOfReductive : SplitReductiveData.WithRootSpaces (piBar π) :=
  haveI : Algebra.Smooth k H := smooth_of_reductive_bar hred
  haveI : Monoid.FG X := (instances_of_reductive hπ hT hred hDC hR1).2.1
  haveI : IsMulTorsionFree X := (instances_of_reductive hπ hT hred hDC hR1).2.2.1
  haveI : Module.Finite ℤ (Additive X) := (instances_of_reductive hπ hT hred hDC hR1).2.2.2.1
  haveI : ConnectedSpace (PrimeSpectrum (K ⊗[k] H)) := (instances_of_reductive hπ hT hred hDC hR1).2.2.2.2
  haveI : Group.FG X := Group.fg_iff_monoid_fg.mpr inferInstance
  (barData hπ (hypZ_of_reductive π hπ hT hred hDC hR1)).toWithRootSpacesOfRankOne
    (hypR1bar_of_reductive π hπ hT hred hDC hR1) (hypR2_of_reductive π hπ hT hred hDC hR1)

/-- The root datum of `G_{k̄}`. -/
def withRootDatumOfReductive : SplitReductiveData.WithRootDatum (piBar π) :=
  (withRootSpacesOfReductive hπ hT hred hDC hR1).toWithRootDatum

/-! Theorem D (§13) for `G` reductive with split maximal torus `π`, over any field `k`; the Weyl
group is `weylGroup π k̄`, as in the `*_G` theorems of FromR1R2.lean. -/

/-- **Theorem `thm:red-pure`**, unconditional. -/
theorem red_pure_red (N : AddSubmonoid (Additive X)) :
    Rooted.reductiveHull (roots π) (fun w : weylGroup π K => actW (w : X ≃* X)) N =
      sInf {L | affineY (torusGrading π) L = affineY (torusGrading π) N} := by
  obtain ⟨_, _, _, _, _⟩ := instances_of_reductive hπ hT hred hDC hR1
  exact red_pure_fieldBar (barDataOfReductive hπ hT hred hDC hR1) N

/-- **Theorem `thm:red-classification` (i)**, finiteness of `Π(a)`, unconditional. -/
theorem finite_pure_red : {N | IsPure (affineY (torusGrading π)) N}.Finite := by
  obtain ⟨_, _, _, _, _⟩ := instances_of_reductive hπ hT hred hDC hR1
  exact finite_pure_fieldBar (barDataOfReductive hπ hT hred hDC hR1)

/-- **Theorem `thm:red-classification` (i)**, bijection, unconditional. -/
theorem red_classification_red :
    Set.BijOn (Rooted.pairOf (roots π) (fun w : weylGroup π K => actW (w : X ≃* X)))
        {N | IsPure (affineY (torusGrading π)) N}
        {p | Rooted.IsCompatiblePair (roots π) (fun w : weylGroup π K => actW (w : X ≃* X)) p} ∧
      Set.InvOn (fun p : Set (Additive X) × Set (weylGroup π K) =>
          Rooted.pairMagnet (fun w : weylGroup π K => actW (w : X ≃* X)) p.1 p.2)
        (Rooted.pairOf (roots π) (fun w : weylGroup π K => actW (w : X ≃* X)))
        {N | IsPure (affineY (torusGrading π)) N}
        {p | Rooted.IsCompatiblePair (roots π) (fun w : weylGroup π K => actW (w : X ≃* X)) p} := by
  obtain ⟨_, _, _, _, _⟩ := instances_of_reductive hπ hT hred hDC hR1
  exact red_classification_i_fieldBar (barDataOfReductive hπ hT hred hDC hR1)

/-- **Theorem `thm:red-classification` (ii)**, unconditional. -/
theorem red_classification_ii_red {R : Set (Additive X)} (hRΦ : R ⊆ roots π)
    (hR : (AddSubmonoid.closure R : Set (Additive X)) ∩ roots π = R) :
    IsPure (affineY (torusGrading π))
        (sInf {L | affineY (torusGrading π) L =
          affineY (torusGrading π) (AddSubmonoid.closure R)}) ∧
      ((sInf {L | affineY (torusGrading π) L =
          affineY (torusGrading π) (AddSubmonoid.closure R)} : AddSubmonoid (Additive X)) :
          Set (Additive X)) ∩ roots π = R := by
  obtain ⟨_, _, _, _, _⟩ := instances_of_reductive hπ hT hred hDC hR1
  exact classification_ii_fieldBar (barDataOfReductive hπ hT hred hDC hR1) hRΦ hR

/-- **Theorem `thm:red-rooted`**, unconditional. -/
theorem reductive_joinDense_red :
    Rooted.IsJoinDense (IsPure (affineY (torusGrading π)))
      (Rooted.reductiveRoot (roots π) fun w : weylGroup π K => actW (w : X ≃* X)) := by
  obtain ⟨_, _, _, _, _⟩ := instances_of_reductive hπ hT hred hDC hR1
  exact reductive_joinDense_fieldBar (barDataOfReductive hπ hT hred hDC hR1)

/-- **Theorem `thm:red-SL-Sp`**, unconditional. -/
theorem red_SL_Sp_red :
    List.TFAE [Set.BijOn (fun N : AddSubmonoid (Additive X) => (N : Set (Additive X)) ∩
          roots π)
        {N | IsPure (affineY (torusGrading π)) N} {E | Rooted.IsStableElt (roots π) E},
      Rooted.IsJoinDense (IsPure (affineY (torusGrading π))) (Rooted.mono '' roots π),
      SLSp.JoinIrredWeylGenerated (roots π) (fun w : weylGroup π K => actW (w : X ≃* X))] := by
  obtain ⟨_, _, _, _, _⟩ := instances_of_reductive hπ hT hred hDC hR1
  exact red_SL_Sp_fieldBar (withRootDatumOfReductive hπ hT hred hDC hR1)

/-- **Corollary `cor:red-monogenic`**, unconditional. -/
theorem red_mono_bijOn_red :
    Set.BijOn (fun a : Additive X => AddSubmonoid.closure {a}) (roots π)
      {N | IsPure (affineY (torusGrading π)) N ∧ (∃ x, N = AddSubmonoid.closure {x}) ∧
        N ≠ ⊥} := by
  obtain ⟨_, _, _, _, _⟩ := instances_of_reductive hπ hT hred hDC hR1
  exact red_mono_bijOn_fieldBar (withRootDatumOfReductive hπ hT hred hDC hR1)

/-- **Theorem `thm:red-parabolic`** (pure magnets containing a Weyl conjugate of the base ↔
parabolic sets of roots), unconditional, with the root datum `withRootDatumOfReductive`. -/
theorem parabolic_bijOn_red :
    Set.BijOn (fun N : AddSubmonoid (Additive X) => (N : Set (Additive X)) ∩ roots π)
        {N | IsPure (affineY (torusGrading π)) N ∧ ∃ B' ∈ Set.range
          (fun v : (withRootDatumOfReductive hπ hT hred hDC hR1).P.weylGroup =>
            RootSystem.RootDatum.act (withRootDatumOfReductive hπ hT hred hDC hR1).P v ''
              ((withRootDatumOfReductive hπ hT hred hDC hR1).P.root ''
                (withRootDatumOfReductive hπ hT hred hDC hR1).b.support)), B' ⊆ N}
        {R | RootSystem.RootDatum.IsClosedRoots (roots π) R ∧ R ∪ -R = roots π} ∧
      Set.InvOn AddSubmonoid.closure
        (fun N : AddSubmonoid (Additive X) => (N : Set (Additive X)) ∩ roots π)
        {N | IsPure (affineY (torusGrading π)) N ∧ ∃ B' ∈ Set.range
          (fun v : (withRootDatumOfReductive hπ hT hred hDC hR1).P.weylGroup =>
            RootSystem.RootDatum.act (withRootDatumOfReductive hπ hT hred hDC hR1).P v ''
              ((withRootDatumOfReductive hπ hT hred hDC hR1).P.root ''
                (withRootDatumOfReductive hπ hT hred hDC hR1).b.support)), B' ⊆ N}
        {R | RootSystem.RootDatum.IsClosedRoots (roots π) R ∧ R ∪ -R = roots π} := by
  obtain ⟨_, _, _, _, _⟩ := instances_of_reductive hπ hT hred hDC hR1
  exact parabolic_bijOn_fieldBar (withRootDatumOfReductive hπ hT hred hDC hR1)

/-- **Proposition `prop:root-groups` (i)** for `G_{k̄}`, unconditional. -/
theorem isRootGroup_red {α : Additive X} (hα : α ∈ roots (piBar π)) :
    IsRootGroup (piBar π) α (rootGroupIdeal (piBar π) α (nsmul_eq_zero_of_mem_roots hα)) := by
  obtain ⟨_, _, _, _, _⟩ := instances_of_reductive hπ hT hred hDC hR1
  exact isRootGroup_of_withRootSpaces (D := withRootSpacesOfReductive hπ hT hred hDC hR1) hα

open TauCeti.Cocharacter in
/-- **Theorem `thm:red-parabolic`, `G^N = P_ξ`**, unconditional, with the base `B` of the root
datum `withRootDatumOfReductive` of `G_{k̄}` (proof of `red_parabolic_field`, with
`red_parabolic_hull_lattice` applied over `k̄`). -/
theorem red_parabolic_red (ψ : X →* Multiplicative ℤ) {N : AddSubmonoid (Additive X)}
    (hBN : (withRootDatumOfReductive hπ hT hred hDC hR1).P.root ''
      (withRootDatumOfReductive hπ hT hred hDC hR1).b.support ⊆ N)
    (hξ : ∀ α ∈ Parabolic.xi ((withRootDatumOfReductive hπ hT hred hDC hR1).P.root ''
      (withRootDatumOfReductive hπ hT hred hDC hR1).b.support) N, pairingHom ψ α = 0)
    (hpos : ∀ α ∈ (withRootDatumOfReductive hπ hT hred hDC hR1).P.root ''
        (withRootDatumOfReductive hπ hT hred hDC hR1).b.support,
      α ∉ Parabolic.xi ((withRootDatumOfReductive hπ hT hred hDC hR1).P.root ''
        (withRootDatumOfReductive hπ hT hred hDC hR1).b.support) N → 0 < pairingHom ψ α) :
    magnetIdeal (torusGrading π) N =
      (parabolicDefiningHopfIdeal (π.cocharacter ψ)).toIdeal := by
  obtain ⟨_, _, _, _, _⟩ := instances_of_reductive hπ hT hred hDC hR1
  set D := withRootDatumOfReductive hπ hT hred hDC hR1
  have S := RootSystem.RootDatum.simpleSystem D.P D.b
  have hY : affineY (torusGrading π)
      (sInf {L | affineY (torusGrading π) L = affineY (torusGrading π) N}) =
        affineY (torusGrading π) N := by
    rw [affineY_infPreserving (torusGrading π)]
    apply le_antisymm
    · exact iInf₂_le (f := fun L _ => affineY (torusGrading π) L) N (Set.mem_ofPred.2 rfl)
    · exact le_iInf₂ fun L hL => (Set.mem_ofPred.1 hL).ge
  have hhull : sInf {L | affineY (torusGrading π) L = affineY (torusGrading π) N} =
      AddSubmonoid.closure (D.P.root '' D.b.support ∪
        -Parabolic.xi (D.P.root '' D.b.support) N) := by
    rw [← hull_baseChange (AlgebraicClosure k) π]
    exact red_parabolic_hull_lattice D hBN
  rw [hhull] at hY
  have hI : magnetIdeal (torusGrading π) (AddSubmonoid.closure (D.P.root '' D.b.support ∪
      -Parabolic.xi (D.P.root '' D.b.support) N)) = magnetIdeal (torusGrading π) N := hY
  rw [← hI]
  refine Parabolic.magnetIdeal_basis_neg_eq_parabolic π ψ ?_ hξ hpos
  rw [← roots_piBar π, ← D.range_root]
  exact S.pos_or_neg

end Unconditional

end AlgMag.Reductive

