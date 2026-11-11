/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.ForwardFinal
import AlgMag.Reductive.CuCandidate
import AlgMag.Reductive.RayGa
import AlgMag.Reductive.HCTReal
import AlgMag.Reductive.SmoothKrullDim
import AlgMag.Reductive.BruhatRankOne
import AlgMag.Reductive.RayGenerator
import AlgMag.Reductive.RayBootstrap
import AlgMag.Reductive.R1Discharge
import AlgMag.Reductive.BaseCoreB
import AlgMag.Reductive.ParabolicGenStep

/-!
# (⇒) assembled from the remaining named cores

`condI_condII_condIII_of_reductive_final`: same conclusion as
`condI_condII_condIII_of_reductive` (Equivalence.lean), with no `sorry` in its proof, from the
named inputs:

* `hBruhat` — `BruhatRayCore` on every positive ray (the rank-one Bruhat step, with the
  opposite cocharacter of `Z = G^{ℤδ}` so that the puncture lies on `U(λ)`, the side of `rayU`);
  gives `RayDimData` (`rayDimData_of_hAff`), hence T4, hence `hcent`, and `hD`.
* `hsolvC` — `C = Z_G(T)` geometrically solvable (= `BaseCoreB.CSolvable C`; input of
  `HCTReal.hCT`; `hsm`, `hRuC`, `hTC` and connectedness of `C` are proved here, the last via
  `exists_magnetIdeal_bot_eq_levi`: `C = Z(ψ)` for a generic `ψ`).
* `hBorSide` — `hT2` and `hBorStab` of `r1Geom_of_opposite''` (Bor± now derived from `hsolvC`) at
  every `δ ≠ 0` whose line contains all proportional roots in `ℤδ`, for some `ψ` with
  `⟨ψ, δ⟩ ≠ 0`.
-/

open AlgebraicGeometry CategoryTheory Magnetism TauCeti TauCeti.Comodule WithConv AlgMag.Weyl TauCeti.Cocharacter

universe u

namespace AlgMag.Reductive

open R1Opp R1Build

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable [Algebra.FiniteType k H]

section Defs

variable (π : H →ₐc[k] MonoidAlgebra k X)

/-- **Bruhat core on the ray of `α`** (named input): for `Z = G^{ℤδ}` (`δ` the ray generator),
the cocharacter `λ⁻¹` of `Z` and some `n`, `BruhatRankOneCore` with target `k[U_(δ)] ∖ {1}`. -/
def BruhatRayCore [Algebra.Smooth k H] [IsMulTorsionFree X] (ψ : X →* Multiplicative ℤ)
    (α : Additive X) (hα : 0 < pairingHom ψ α) : Prop :=
  letI : Algebra.Smooth k (ZAlg π (rayGen π ψ α hα).1) := smooth_quotient_magnetHopfIdeal π _
  ∃ n : WithConv (ZAlg π (rayGen π ψ α hα).1 →ₐ[k] k),
    BruhatRankOneCore (zCochar π (rayGen π ψ α hα).1 ψ).oppositeCocharacter n
      (Bialgebra.augmentationPoint k (rayU π ψ α hα)) (isClosed_rayU_one π ψ α hα)

/-- **Borel-side inputs at `δ`, `ψ`** (named input): `hT2` and `hBorStab` of
`r1Geom_of_opposite''` (Bor± are derived from `hsolvC`: `isSolvable_BAlg`, `isSolvable_BmAlg`). -/
def BorelSide [Algebra.Smooth k H] (δ : Additive X) (ψ : X →* Multiplicative ℤ) : Prop :=
  ¬ Group.IsSolvable (WithConv (ZAlg π δ →ₐ[k] k)) ∧
  (∀ (M : Type u) [AddCommGroup M] [Module k M] [Comodule k (ZAlg π δ) M]
      [Module.Finite k M] (m : M) (hm : Module.IsUnimodular k m) (S : HopfIdeal k (ZAlg π δ)),
      IsClosed (Set.range (projectiveOrbitMap (H := ZAlg π δ) m hm)) →
      (∀ a : WithConv (ZAlg π δ →ₐ[k] k),
        a ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k (ZAlg π δ)) S
            (CommAlgCat.of k k) ↔
          projectiveOrbitMap (H := ZAlg π δ) m hm (AlgHom.kernelPoint a.ofConv) =
            projectiveOrbitMap (H := ZAlg π δ) m hm
              (AlgHom.kernelPoint (Bialgebra.counitAlgHom k (ZAlg π δ)))) →
      (∀ b : WithConv (BAlg π δ ψ →ₐ[k] k), BialgHom.mapDomain (fB π δ ψ) b ∈
        CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k (ZAlg π δ)) S
          (CommAlgCat.of k k)) →
      Group.IsSolvable (CommHopfAlgCat.quotientPointsSubgroup
        (_root_.CommHopfAlgCat.of k (ZAlg π δ)) S (CommAlgCat.of k k)) →
      ∀ a : WithConv (ZAlg π δ →ₐ[k] k),
        a ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k (ZAlg π δ)) S
          (CommAlgCat.of k k) → a ∈ Set.range (BialgHom.mapDomain (fB π δ ψ)))

end Defs

/-- `T ⊆ C` (`hTC` of `HCTReal.hCT`), proved. -/
theorem magnetHopfIdeal_bot_le_ker (π : H →ₐc[k] MonoidAlgebra k X)
    (hπ : Function.Surjective π) :
    magnetHopfIdeal π ⊥ ≤ HopfIdeal.kerOfSurjective π hπ := by
  have hkerI : (HopfIdeal.kerOfSurjective π hπ).toIdeal = RingHom.ker π.toAlgHom := by
    ext x; rw [HopfIdeal.mem_toIdeal, HopfIdeal.mem_kerOfSurjective, RingHom.mem_ker]; rfl
  rw [← HopfIdeal.toIdeal_le_toIdeal, magnetHopfIdeal_toIdeal, hkerI]
  exact magnetIdeal_le_ker_torus π ⊥

/-- `C_u = 1 ⇒ R_u(C) = 1` (`hRuC` of `HCTReal.hCT`), proved from the definition of `CuIdeal`. -/
theorem RuC_eq_augmentation (π : H →ₐc[k] MonoidAlgebra k X)
    (hCu : CuIdeal π = HopfIdeal.augmentation k H) :
    FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal (FiniteTypeCommHopfAlgCat.quotient
      (FiniteTypeCommHopfAlgCat.of k H) (magnetHopfIdeal π ⊥)) =
      HopfIdeal.augmentation k _ := by
  refine le_antisymm (HopfIdeal.le_augmentation k _ _) ?_
  intro y hy
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hh : h ∈ CuIdeal π := by
    rw [hCu, HopfIdeal.mem_augmentation]
    rw [HopfIdeal.mem_augmentation] at hy
    exact hy
  exact (mem_CuIdeal π).1 hh



/-! ### Bridges: `k̄`-points to `k`-points, and `Z_Z(λ)` inside `C` -/

/-- **`k ↪ k̄` transport**: solvable `k̄`-points give solvable `k`-points. -/
theorem isSolvable_points_of_bar {A : Type u} [CommRing A] [HopfAlgebra k A]
    (h : Group.IsSolvable (WithConv (A →ₐ[k] AlgebraicClosure k))) :
    Group.IsSolvable (WithConv (A →ₐ[k] k)) := by
  refine Group.isSolvable_of_isSolvable_injective
    (f := AlgHom.mapValue (IsScalarTower.toAlgHom k k (AlgebraicClosure k))) ?_
  intro a b hab
  apply WithConv.ofConv_injective
  ext x
  have := congrArg (fun z => z.ofConv x) hab
  exact (algebraMap k (AlgebraicClosure k)).injective (by simpa [AlgHom.mapValue] using this)

/-- `G^{ℤδ} ∩ Z(ψ) ⊆ C` on ideals, when `⟨ψ,δ⟩ ≠ 0`. -/
theorem magnetIdeal_bot_le_sup (π : H →ₐc[k] MonoidAlgebra k X)
    [Module.IsTorsionFree ℤ (Additive X)] {δ : Additive X} {ψ : X →* Multiplicative ℤ}
    (hδψ : pairingHom ψ δ ≠ 0) :
    magnetIdeal (torusGrading π) ⊥ ≤ magnetIdeal (torusGrading π) (lineMagnet δ) ⊔
      magnetIdeal (torusGrading π) ((⊥ : Magnet ℤ).comap (pairingHom ψ)) := by
  refine Ideal.span_le.2 ?_
  intro a ha
  simp only [Set.mem_iUnion, SetLike.mem_coe] at ha
  obtain ⟨m, hm, ha⟩ := ha
  have hm0 : m ≠ 0 := by simpa [AddSubmonoid.mem_bot] using hm
  by_cases hl : m ∈ lineMagnet δ
  · refine Ideal.mem_sup_right (mem_magnetIdeal_of_notMem ?_ ha)
    simp only [AddSubmonoid.mem_comap, AddSubmonoid.mem_bot]
    obtain ⟨n, rfl⟩ := hl
    have hn : n ≠ 0 := by rintro rfl; exact hm0 (by simp)
    rw [map_zsmul]
    exact smul_ne_zero hn hδψ
  · exact Ideal.mem_sup_left (mem_magnetIdeal_of_notMem hl ha)

open scoped Classical in
/-- **`Z_Z(λ)` solvable from `C` solvable** (`k̄`-points), `λ = zCochar π δ ψ`, `⟨ψ,δ⟩ ≠ 0`. -/
theorem isSolvable_levi_zCochar (π : H →ₐc[k] MonoidAlgebra k X)
    [Module.IsTorsionFree ℤ (Additive X)] [Algebra.Smooth k H] {δ : Additive X}
    {ψ : X →* Multiplicative ℤ} (hδψ : pairingHom ψ δ ≠ 0)
    (hsolvC : geometricallySolvablePointsCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient
      (FiniteTypeCommHopfAlgCat.of k H) (magnetHopfIdeal π ⊥)).obj) :
    Group.IsSolvable (levi (AlgebraicClosure k) (zCochar π δ ψ)) := by
  set S := CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H)
    (magnetHopfIdeal π ⊥) (CommAlgCat.of k (AlgebraicClosure k))
  have hS : Group.IsSolvable S :=
    (BaseCoreB.isSolvable_quotientPointsSubgroup_iff (magnetHopfIdeal π ⊥)).2 hsolvC
  have hmem : ∀ g ∈ levi (AlgebraicClosure k) (zCochar π δ ψ),
      BialgHom.mapDomain (zMk π δ) g ∈ S := by
    intro g hg
    set x := BialgHom.mapDomain (zMk π δ) g
    have h1 : magnetIdeal (torusGrading π) (lineMagnet δ) ≤ RingHom.ker x.ofConv := by
      intro y hy
      have : zMk π δ y = 0 := by
        change Ideal.Quotient.mk _ y = 0
        rw [Ideal.Quotient.eq_zero_iff_mem, magnetHopfIdeal_toIdeal]; exact hy
      rw [RingHom.mem_ker]
      change g.ofConv (zMk π δ y) = 0
      rw [this, map_zero]
    have hx : x ∈ levi (AlgebraicClosure k) (π.cocharacter ψ) := by
      rw [mem_levi_iff, conjugate_mapDomain (π.cocharacter ψ) (zMk π δ) (zCochar π δ ψ)
        (R1Dis.zCochar_comp π δ ψ), (mem_levi_iff).1 hg]
      apply WithConv.ofConv_injective
      rw [BialgHom.mapDomain_apply, WithConv.ofConv_toConv]
      rfl
    have h2 := (magnetIdeal_torusGrading_comap_bot_le_ker_iff (π := π) (ψ := ψ) x).2 hx
    refine (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).2 fun h hh => ?_
    have hh' : h ∈ magnetIdeal (torusGrading π) ⊥ := by
      rw [← magnetHopfIdeal_toIdeal]; exact HopfIdeal.mem_toIdeal.2 hh
    exact (sup_le h1 h2) (magnetIdeal_bot_le_sup π hδψ hh')
  let f : levi (AlgebraicClosure k) (zCochar π δ ψ) →* S :=
    ((BialgHom.mapDomain (zMk π δ)).comp (Subgroup.subtype _)).codRestrict S
      (fun g => hmem g.1 g.2)
  refine Group.isSolvable_of_isSolvable_injective (f := f) ?_
  intro a b hab
  have hab' := congrArg Subtype.val hab
  apply Subtype.ext
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro z
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  have := congrArg (fun w => w.ofConv y) hab'
  exact this

/-- **`B⁺(k)` solvable** from `C` solvable. -/
theorem isSolvable_BAlg (π : H →ₐc[k] MonoidAlgebra k X)
    [Module.IsTorsionFree ℤ (Additive X)] [Algebra.Smooth k H] {δ : Additive X}
    {ψ : X →* Multiplicative ℤ} (hδψ : pairingHom ψ δ ≠ 0)
    (hsolvC : geometricallySolvablePointsCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient
      (FiniteTypeCommHopfAlgCat.of k H) (magnetHopfIdeal π ⊥)).obj) :
    Group.IsSolvable (WithConv (BAlg π δ ψ →ₐ[k] k)) := by
  refine isSolvable_points_of_bar ?_
  have hP := BaseCoreB.isSolvable_parabolic (k := k) (H := ZAlg π δ) (zCochar π δ ψ) (isSolvable_levi_zCochar π hδψ hsolvC)
  rw [← quotientPointsSubgroup_parabolicDefiningHopfIdeal] at hP
  exact (BaseCoreB.isSolvable_quotientPointsSubgroup_iff _).1 hP

/-- **`B⁻(k)` solvable** from `C` solvable. -/
theorem isSolvable_BmAlg (π : H →ₐc[k] MonoidAlgebra k X)
    [Module.IsTorsionFree ℤ (Additive X)] [Algebra.Smooth k H] {δ : Additive X}
    {ψ : X →* Multiplicative ℤ} (hδψ : pairingHom ψ δ ≠ 0)
    (hsolvC : geometricallySolvablePointsCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient
      (FiniteTypeCommHopfAlgCat.of k H) (magnetHopfIdeal π ⊥)).obj) :
    Group.IsSolvable (WithConv (BmAlg π δ ψ →ₐ[k] k)) := by
  refine isSolvable_points_of_bar ?_
  have hL := isSolvable_levi_zCochar π hδψ hsolvC
  rw [← levi_oppositeCocharacter] at hL
  have hP := BaseCoreB.isSolvable_parabolic (k := k) (H := ZAlg π δ) _ hL
  rw [← quotientPointsSubgroup_parabolicDefiningHopfIdeal] at hP
  exact (BaseCoreB.isSolvable_quotientPointsSubgroup_iff _).1 hP

open scoped Classical in
/-- **`C = Z(ψ)` for a generic `ψ`**: `magnetIdeal ⊥ = magnetIdeal (ψ⁻¹(0))` once `ψ` is nonzero
on the finitely many nonzero weights of the components of a finite generating set. -/
theorem exists_magnetIdeal_bot_eq_levi [Module.Free ℤ (Additive X)]
    (π : H →ₐc[k] MonoidAlgebra k X) :
    ∃ ψ : X →* Multiplicative ℤ, magnetIdeal (torusGrading π) ⊥ =
      magnetIdeal (torusGrading π) ((⊥ : Magnet ℤ).comap (pairingHom ψ)) := by
  obtain ⟨S, hS⟩ := (‹Algebra.FiniteType k H›).out
  let W : Set (Additive X) := ⋃ s ∈ S,
    {m | m ≠ 0 ∧ (DirectSum.decompose (torusGrading π) s m : H) ≠ 0}
  have hW : W.Finite := by
    refine Set.Finite.biUnion S.finite_toSet fun s _ => ?_
    refine (DFinsupp.support (DirectSum.decompose (torusGrading π) s)).finite_toSet.subset ?_
    intro m hm
    simp only [Set.mem_setOf_eq] at hm
    simp only [Finset.mem_coe, DFinsupp.mem_support_toFun]
    intro h; exact hm.2 (by rw [h]; rfl)
  obtain ⟨ψ, hψ⟩ := exists_generic_cocharacter W hW (fun m hm => by
    simp only [W, Set.mem_iUnion, Set.mem_setOf_eq] at hm
    obtain ⟨_, _, h, _⟩ := hm; exact h)
  refine ⟨ψ, le_antisymm ?_ (magnetIdeal_anti _ ?_)⟩
  · set J := magnetIdeal (torusGrading π) ((⊥ : Magnet ℤ).comap (pairingHom ψ))
    have hJ : ∀ m : Additive X, pairingHom ψ m ≠ 0 → ∀ a ∈ torusGrading π m, a ∈ J :=
      fun m hm a ha => mem_magnetIdeal_of_notMem (by
        simp only [AddSubmonoid.mem_comap, AddSubmonoid.mem_bot]; exact hm) ha
    have key : ∀ x : H, ∀ m : Additive X, m ≠ 0 →
        (DirectSum.decompose (torusGrading π) x m : H) ∈ J := by
      intro x
      have hx : x ∈ Algebra.adjoin k (S : Set H) := by rw [hS]; trivial
      induction hx using Algebra.adjoin_induction with
      | mem s hs =>
        intro m hm
        by_cases h0 : (DirectSum.decompose (torusGrading π) s m : H) = 0
        · rw [h0]; exact J.zero_mem
        · refine hJ m (hψ m ?_) _ (SetLike.coe_mem _)
          simp only [W, Set.mem_iUnion, Set.mem_setOf_eq]
          exact ⟨s, hs, hm, h0⟩
      | algebraMap r =>
        intro m hm
        rw [DirectSum.decompose_of_mem_ne (torusGrading π)
          (SetLike.algebraMap_mem_graded (torusGrading π) r) (Ne.symm hm)]
        exact J.zero_mem
      | add x y _ _ hx hy =>
        intro m hm
        rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add]
        exact J.add_mem (hx m hm) (hy m hm)
      | mul x y _ _ hx hy =>
        intro m hm
        rw [DirectSum.decompose_mul, DirectSum.coe_mul_apply]
        refine J.sum_mem fun ij hij => ?_
        rw [Finset.mem_filter] at hij
        by_cases hi : ij.1 = 0
        · have hj : ij.2 ≠ 0 := by
            intro hj; apply hm; rw [← hij.2, hi, hj, add_zero]
          exact J.mul_mem_left _ (hy _ hj)
        · exact J.mul_mem_right _ (hx _ hi)
    refine Ideal.span_le.2 ?_
    intro a ha
    simp only [Set.mem_iUnion, SetLike.mem_coe] at ha
    obtain ⟨m, hm, ha⟩ := ha
    have hm' : m ≠ 0 := by simpa [AddSubmonoid.mem_bot] using hm
    have := key a m hm'
    rwa [DirectSum.decompose_of_mem_same (torusGrading π) ha] at this
  · intro m hm
    simp only [AddSubmonoid.mem_bot] at hm
    simp [AddSubmonoid.mem_comap, hm]

/-- **(⇒) assembled**, from the named cores only. -/
theorem condI_condII_condIII_of_reductive_final [Module.IsTorsionFree ℤ (Additive X)]
    (π : H →ₐc[k] MonoidAlgebra k X)
    (hπ : Function.Surjective π)
    (hT : HopfIdeal.IsMaximalTorus k (CommHopfAlgCat.of k H) (HopfIdeal.kerOfSurjective π hπ))
    (hred : reductiveCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.of k H))
    (hBruhat : letI : Algebra.Smooth k H := hred.smooth
      haveI : IsMulTorsionFree X := ⟨fun n hn =>
        (IsAddTorsionFree.of_isTorsionFree ℤ (Additive X)).nsmul_right_injective hn⟩
      ∀ (ψ : X →* Multiplicative ℤ) (α : Additive X) (hα : 0 < pairingHom ψ α),
        BruhatRayCore π ψ α hα)
    (hsolvC : geometricallySolvablePointsCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient
      (FiniteTypeCommHopfAlgCat.of k H) (magnetHopfIdeal π ⊥)).obj)
    (hBorSide : letI : Algebra.Smooth k H := hred.smooth
      ∀ δ : Additive X, δ ≠ 0 →
        (∀ β ∈ roots π, (∃ m n : ℤ, n ≠ 0 ∧ n • β = m • δ) → β ∈ lineMagnet δ) →
        ∃ ψ : X →* Multiplicative ℤ, pairingHom ψ δ ≠ 0 ∧ BorelSide π δ ψ) :
    CondI π ∧ CondII π ∧ CondIII π := by
  letI : Algebra.Smooth k H := hred.smooth
  haveI : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
  haveI : Module.Finite k (Bialgebra.CotangentSpace k H) := inferInstance
  have : Algebra.FiniteType k (MonoidAlgebra k X) :=
    Algebra.FiniteType.of_surjective π.toAlgHom hπ
  haveI : Monoid.FG X := MonoidAlgebra.fg_of_finiteType (R := k)
  haveI : Group.FG X := Group.fg_iff_monoid_fg.mpr inferInstance
  haveI : Module.Finite ℤ (Additive X) :=
    Module.Finite.iff_addGroup_fg.2 (AddGroup.fg_iff_addMonoid_fg.2
      (Monoid.fg_iff_add_fg.1 inferInstance))
  haveI : Module.Free ℤ (Additive X) := Module.free_of_finite_type_torsion_free'
  haveI : IsAddTorsionFree (Additive X) := .of_isTorsionFree ℤ (Additive X)
  haveI : IsMulTorsionFree X :=
    ⟨fun n hn => IsAddTorsionFree.nsmul_right_injective (M := Additive X) hn⟩
  haveI : ConnectedSpace (PrimeSpectrum H) :=
    connectedSpace_of_geometricallyConnected k H hred.geometricallyConnected
  haveI : IrreducibleSpace (PrimeSpectrum H) := OpenCellNotes.irreducibleSpace_of_connectedSpace k
  -- hconnC: C = Z(ψc) for a generic ψc, and Levis are connected
  have hconnC : geometricallyConnectedCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient
      (FiniteTypeCommHopfAlgCat.of k H) (magnetHopfIdeal π ⊥)).obj := by
    obtain ⟨ψc, hψc⟩ := exists_magnetIdeal_bot_eq_levi π
    rw [geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace]
    have h0 := connectedSpace_levi_of_openCell (π.cocharacter ψc) (isOpenEmbedding_openCell _)
    have h' : ConnectedSpace (PrimeSpectrum (H ⧸ (magnetHopfIdeal π ⊥).toIdeal)) := by
      rw [magnetHopfIdeal_toIdeal, hψc, magnetIdeal_torusGrading_comap_bot]; exact h0
    exact h'
  -- T4 via the Bruhat core
  have hRDD : ∀ (ψ : X →* Multiplicative ℤ) (α : Additive X) (hα : 0 < pairingHom ψ α),
      RayDimData π (pairingHom ψ) α := fun ψ α hα => by
    letI : Algebra.Smooth k (ZAlg π (rayGen π ψ α hα).1) := smooth_quotient_magnetHopfIdeal π _
    exact rayDimData_of_hAff π ψ α hα
      (hAff_of_bruhatCore _ (hBruhat ψ α hα).choose _ _ (hBruhat ψ α hα).choose_spec)
  let toψ : (Additive X →+ ℤ) → (X →* Multiplicative ℤ) := fun f =>
    { toFun := fun x => Multiplicative.ofAdd (f (Additive.ofMul x))
      map_one' := by simp
      map_mul' := fun a b => by simp [ofAdd_add] }
  have htoψ : ∀ f, pairingHom (toψ f) = f := fun f => by ext χ; rfl
  have hD : ∀ (f : Additive X →+ ℤ), ∀ α ∈ posRoots π f, Nonempty (RayDimData π f α) := by
    intro f α hα
    have hpos : 0 < pairingHom (toψ f) α := by
      rw [htoψ]; exact (Finset.mem_filter.1 hα).2
    have := hRDD (toψ f) α hpos
    rw [htoψ] at this
    exact ⟨this⟩
  have hT4 : ∀ (g : Additive X →+ ℤ), ∀ γ ∈ posRoots π g, rayDim π g γ ≤ 1 :=
    fun g γ hγ => rayDim_le_one π (hD g γ hγ).some
  -- hLie0
  obtain ⟨ψ₀, hψ₀⟩ := exists_generic_cocharacter (roots π) finite_roots
    (fun α hα => ne_zero_of_mem_roots hα)
  have hcent := hcent_CuIdeal_of_rayDim π (ψ := ψ₀)
    (fun φ _ α => rayDim_le_one π (hRDD φ α.1 α.2))
  have hCT' := HCTReal.hCT π hπ (CuIdeal π) (smooth_quotient_magnetHopfIdeal π ⊥) hconnC hsolvC
    (RuC_eq_augmentation π) hT (magnetHopfIdeal_bot_le_ker π hπ)
  have hLie0 := finrank_rootSpace_zero_le_of_reductive_Cu π hπ ψ₀ hψ₀ hred hcent hCT'
  -- (DC), (i), counts
  obtain ⟨ψ, hψ, hDC⟩ := dimCount_of_reductive'' π hπ hT hred hLie0 hD
  obtain ⟨h1, h2, h3⟩ := condI_and_counts_of_dimCount π hπ ψ hψ hDC
  -- (R1) via line generator + bootstrap
  have hR1at : ∀ δ : Additive X, δ ≠ 0 →
      (∀ β ∈ roots π, (∃ m n : ℤ, n ≠ 0 ∧ n • β = m • δ) → β ∈ lineMagnet δ) →
      ∃ (n : WithConv (H →ₐ[k] k)) (σ : X ≃* X), IsNormalizingWith π k n σ ∧
        n ∈ attractorSubgroup π (lineMagnet δ) k ∧ σ ≠ 1 := by
    intro δ hδ hRay
    obtain ⟨φ, hφ, hT2, hBorStab⟩ := hBorSide δ hδ hRay
    haveI := isSolvable_BAlg π hφ hsolvC
    haveI := isSolvable_BmAlg π hφ hsolvC
    obtain ⟨G⟩ := r1Geom_of_opposite'' π δ φ hπ hT hδ hRay hT2 hBorStab
    exact r1_of_r1Datum π hπ (G.toR1Datum π δ φ hT hφ)
  have hR1 : ∀ α ∈ roots π, ∃ (n : WithConv (H →ₐ[k] k)) (σ : X ≃* X),
      IsNormalizingWith π k n σ ∧ n ∈ attractorSubgroup π (lineMagnet α) k ∧ σ ≠ 1 := by
    intro α hα
    obtain ⟨δ, hδ0, hαδ, hRayδ⟩ := exists_line_generator π hα
    obtain ⟨n, σ, hn, hmem, hσ⟩ := hR1at δ hδ0 hRayδ
    have hfin := isOfFinOrder_of_isNormalizingWith π hπ hn
    have hα0 := ne_zero_of_mem_roots hα
    obtain ⟨f, hf⟩ : ∃ f : Additive X →+ ℤ, 0 < f α := by
      rcases lt_or_gt_of_ne (hψ α hα) with h | h
      · exact ⟨-pairingHom ψ, by rw [AddMonoidHom.neg_apply]; omega⟩
      · exact ⟨pairingHom ψ, h⟩
    have hRayα := hRay_of_bootstrap π hπ hn hδ0 hmem hσ hfin hα hαδ f hf hT4
    exact hR1at α hα0 hRayα
  -- (iii)
  let D := algClosedData π hπ h1
  have h3' : CondIII π := by
    intro α hα
    obtain ⟨n, σ, hn, hnα, hσ⟩ := hR1 α hα
    have hrefl := isReflectionOn_of_mem_lineAttractor D hα hn hnα hσ
    refine ⟨n, σ, hn, hnα, ?_⟩
    have := congrArg Additive.toMul hrefl.1
    simpa [actW] using this
  -- (ii′)
  have h2' : CondII π := by
    refine condII_of_counting π (pairingHom ψ) hψ h2 h3 ?_
    intro α hα
    obtain ⟨n, σ, hn, -, hσ⟩ := h3' α hα
    exact ⟨n, σ, hn, hσ⟩
  exact ⟨h1, h2', h3'⟩

end AlgMag.Reductive

#print axioms AlgMag.Reductive.condI_condII_condIII_of_reductive_final
