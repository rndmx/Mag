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
import AlgMag.Reductive.BorSideFinal
import AlgMag.Reductive.CSolvableAssembly

/-!
# (⇒) assembled, second version: `hsolvC` and `hBorSide` discharged

`condI_condII_condIII_of_reductive_final2`: same conclusion as
`condI_condII_condIII_of_reductive_final` (EquivalenceFinal.lean), from the named inputs

* `hBruhat` — `BruhatRayCore` on every positive ray (unchanged);
* `hBorMax` — `BorelZMax π δ ψ` (BorSideFinal.lean) at every line generator `δ ≠ 0`, for some
  `ψ` with `⟨ψ, δ⟩ ≠ 0`: `P_Z(λ_ψ^{±1})` minimal among Borel candidates of `Z = G^{ℤδ}`;
* `hFp` — `Step2OverFpBar` for `[C, C]`, `C = Z_G(T)` (CharpolyFinite.lean; vacuous in
  characteristic `0`: `condI_condII_condIII_of_reductive_final2_charZero` has no such input).

Discharged here:
* `hsolvC` (`C = Z_G(T)` geometrically solvable): `CSolvableAssembly` from the central maximal
  torus `T ⊆ C` (`piC`, `isMaximalTorus_of_comapOfSurjective`, `commute_torusPt_of_mem_bot`);
* `hBorSide`: replaced by `hBorMax` through `r1_of_borelZMax`, with `ZZSolvable` proved from
  `hsolvC` (`zzSolvable_of_hsolvC`, the Levi analogue of `isSolvable_BAlg`).

This file does not import `EquivalenceFinal` (its `.olean` cannot currently be built: a Stacks
`.olean.private` is missing); the lemmas of EquivalenceFinal it uses are reproduced verbatim in
the namespace `Final2`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open AlgebraicGeometry CategoryTheory Magnetism TauCeti TauCeti.Comodule WithConv AlgMag.Weyl
  TauCeti.Cocharacter

universe u

namespace AlgMag.Reductive

open R1Opp R1Build R1Dis

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable [Algebra.FiniteType k H]

/-! ### Lemmas of EquivalenceFinal.lean (verbatim copies) -/

namespace Final2

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

end Final2

open Final2

/-! ### `ZZSolvable` from `hsolvC` -/

/-- **`Z_Z(λ_ψ)` solvable from `C` solvable** (`ZZSolvable` of BorSideFinal), `⟨ψ, δ⟩ ≠ 0`. -/
theorem zzSolvable_of_hsolvC (π : H →ₐc[k] MonoidAlgebra k X)
    [Module.IsTorsionFree ℤ (Additive X)] [Algebra.Smooth k H] {δ : Additive X}
    {ψ : X →* Multiplicative ℤ} (hδψ : pairingHom ψ δ ≠ 0)
    (hsolvC : geometricallySolvablePointsCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient
      (FiniteTypeCommHopfAlgCat.of k H) (magnetHopfIdeal π ⊥)).obj) :
    ZZSolvable π δ ψ := by
  have hL := isSolvable_levi_zCochar π hδψ hsolvC
  have hL' : Group.IsSolvable (CommHopfAlgCat.quotientPointsSubgroup
      (_root_.CommHopfAlgCat.of k (ZAlg π δ)) (leviDefiningHopfIdeal (zCochar π δ ψ))
      (CommAlgCat.of k (AlgebraicClosure k))) := by
    rw [quotientPointsSubgroup_leviDefiningHopfIdeal]; exact hL
  exact (BaseCoreB.isSolvable_quotientPointsSubgroup_iff _).1 hL'

/-! ### The central maximal torus of `C = Z_G(T)` -/

section CTorus

variable (π : H →ₐc[k] MonoidAlgebra k X)

/-- `k[C]`, `C = Z_G(T) = G^{0}`. -/
abbrev CAlg : Type u := H ⧸ (magnetHopfIdeal π ⊥).toIdeal

/-- `O(G) ↠ O(C)`. -/
noncomputable abbrev cQMk : H →ₐc[k] CAlg π := Bialgebra.Quotient.mkBialgHom (magnetHopfIdeal π ⊥).toIdeal

omit [IsAlgClosed k] [Algebra.FiniteType k H] in
lemma cQMk_surjective : Function.Surjective (cQMk π) := Ideal.Quotient.mk_surjective

omit [IsAlgClosed k] [Algebra.FiniteType k H] in
lemma ker_cQMk_le_ker_torus :
    RingHom.ker (cQMk π : H →ₐ[k] CAlg π) ≤ RingHom.ker (π : H →ₐ[k] MonoidAlgebra k X) := by
  intro x hx
  have hx' : x ∈ (magnetHopfIdeal π ⊥).toIdeal := by
    simpa [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] using hx
  rw [magnetHopfIdeal_toIdeal] at hx'
  exact magnetIdeal_le_ker_torus π _ hx'

/-- The torus `T ⊆ C`: `π` factored through `O(C)`. -/
noncomputable def piC : CAlg π →ₐc[k] MonoidAlgebra k X :=
  descBialgHom (cQMk π) Ideal.Quotient.mk_surjective π (ker_cQMk_le_ker_torus π)

omit [IsAlgClosed k] [Algebra.FiniteType k H] in
lemma piC_apply (x : H) : piC π (cQMk π x) = π x :=
  congrArg (fun f : H →ₐc[k] MonoidAlgebra k X => f x)
    (descBialgHom_comp (cQMk π) Ideal.Quotient.mk_surjective π (ker_cQMk_le_ker_torus π))

omit [IsAlgClosed k] [Algebra.FiniteType k H] in
lemma piC_surjective (hπ : Function.Surjective π) : Function.Surjective (piC π) := by
  intro y
  obtain ⟨x, rfl⟩ := hπ y
  exact ⟨cQMk π x, piC_apply π x⟩

/-- The Hopf ideal of `T` in `O(C)`. -/
noncomputable def torusC (hπ : Function.Surjective π) : HopfIdeal k (CAlg π) :=
  HopfIdeal.kerOfSurjective (piC π) (piC_surjective π hπ)

omit [IsAlgClosed k] [Algebra.FiniteType k H] in
lemma torusC_comap (hπ : Function.Surjective π) :
    (torusC π hπ).comapOfSurjective (cQMk π) (cQMk_surjective π) =
      HopfIdeal.kerOfSurjective π hπ := by
  ext x
  rw [HopfIdeal.mem_comapOfSurjective, torusC, HopfIdeal.mem_kerOfSurjective,
    HopfIdeal.mem_kerOfSurjective, piC_apply]

/-- **`T` is a maximal torus of `C`.** -/
theorem isMaximalTorus_torusC (hπ : Function.Surjective π)
    (hT : HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H)
      (HopfIdeal.kerOfSurjective π hπ)) :
    HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k (CAlg π)) (torusC π hπ) := by
  refine isMaximalTorus_of_comapOfSurjective (cQMk π) (cQMk_surjective π) _ ?_
  rw [torusC_comap]; exact hT

omit [Algebra.FiniteType k H] in
/-- **`T` is central in `C`** (the `hcent` input of `CSolvableAssembly`). -/
theorem commute_torusC (hπ : Function.Surjective π) (A : Type u) [CommRing A] [Algebra k A]
    (g t : WithConv (CAlg π →ₐ[k] A))
    (ht : (torusC π hπ).toIdeal ≤ RingHom.ker (ofConv t)) : g * t = t * g := by
  have hinj : Function.Injective (BialgHom.mapDomain (cQMk π) (A := A)) := by
    intro a b hab
    apply WithConv.ofConv_injective
    ext y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    have := congrArg (fun z => z.ofConv x) hab
    simpa [BialgHom.mapDomain_apply] using this
  have hker : RingHom.ker π.toAlgHom ≤ RingHom.ker (BialgHom.mapDomain (cQMk π) t).ofConv := by
    intro x hx
    rw [RingHom.mem_ker, BialgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply]
    apply ht
    rw [HopfIdeal.mem_toIdeal, torusC, HopfIdeal.mem_kerOfSurjective]
    change piC π (cQMk π x) = 0
    rw [piC_apply]; exact hx
  let e := Ideal.quotientKerAlgEquivOfSurjective (f := π.toAlgHom) hπ
  let τ : MonoidAlgebra k X →ₐ[k] A := (Ideal.Quotient.liftₐ (RingHom.ker π.toAlgHom)
    (BialgHom.mapDomain (cQMk π) t).ofConv fun a ha => hker ha).comp e.symm.toAlgHom
  have hτ : toConv (τ.comp π.toAlgHom) = BialgHom.mapDomain (cQMk π) t := by
    apply WithConv.ofConv_injective
    ext x
    rw [ofConv_toConv]
    show (Ideal.Quotient.liftₐ (RingHom.ker π.toAlgHom) (BialgHom.mapDomain (cQMk π) t).ofConv
      fun a ha => hker ha) (e.symm (π.toAlgHom x)) = _
    rw [show e.symm (π.toAlgHom x) = Ideal.Quotient.mk _ x from e.symm_apply_eq.2 rfl]
    rfl
  have hbot : magnetIdeal (torusGrading π) ⊥ ≤
      RingHom.ker (BialgHom.mapDomain (cQMk π) g).ofConv := by
    intro x hx
    rw [RingHom.mem_ker, BialgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply]
    have h0 : cQMk π x = 0 := by
      change Ideal.Quotient.mk _ x = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, magnetHopfIdeal_toIdeal]; exact hx
    change g.ofConv (cQMk π x) = 0
    rw [h0, map_zero]
  have hc := commute_torusPt_of_mem_bot π τ _ hbot
  rw [hτ] at hc
  apply hinj
  rw [map_mul, map_mul]
  exact hc.symm.eq

/-- **`hsolvC` from `Step2OverFpBar`**: `C = Z_G(T)` has solvable geometric points, given that
`C` is connected (proved in the final theorem) and the named leftover `Step2OverFpBar` for
`[C, C]`. -/
theorem hsolvC_of_step2OverFpBar (hπ : Function.Surjective π)
    (hT : HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H)
      (HopfIdeal.kerOfSurjective π hπ))
    [ConnectedSpace (PrimeSpectrum (FiniteTypeCommHopfAlgCat.quotient
      (FiniteTypeCommHopfAlgCat.of k H) (magnetHopfIdeal π ⊥)))]
    (hFp : CharpolyFinite.Step2OverFpBar k
      ((FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H)
        (magnetHopfIdeal π ⊥)) ⧸
        (TauCeti.CommHopfAlgCat.derivedDefiningIdeal (R := k)
          (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H)
            (magnetHopfIdeal π ⊥))).toIdeal)) :
    geometricallySolvablePointsCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient
      (FiniteTypeCommHopfAlgCat.of k H) (magnetHopfIdeal π ⊥)).obj :=
  CSolvableAssembly.cSolvable_of_centralTorus_of_step2OverFpBar (magnetHopfIdeal π ⊥)
    (T := torusC π hπ) (isMaximalTorus_torusC π hπ hT) (commute_torusC π hπ) hFp

end CTorus

/-! ### The final theorem -/

/-- **(⇒) assembled, version 2**: `hsolvC` discharged by `CSolvableAssembly` (leftover
`Step2OverFpBar` for `[C, C]`, only relevant for `k = F̄_p`), `hBorSide` replaced by `BorelZMax`. -/
theorem condI_condII_condIII_of_reductive_final2 [Module.IsTorsionFree ℤ (Additive X)]
    (π : H →ₐc[k] MonoidAlgebra k X)
    (hπ : Function.Surjective π)
    (hT : HopfIdeal.IsMaximalTorus k (CommHopfAlgCat.of k H) (HopfIdeal.kerOfSurjective π hπ))
    (hred : reductiveCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.of k H))
    (hBruhat : letI : Algebra.Smooth k H := hred.smooth
      haveI : IsMulTorsionFree X := ⟨fun n hn =>
        (IsAddTorsionFree.of_isTorsionFree ℤ (Additive X)).nsmul_right_injective hn⟩
      ∀ (ψ : X →* Multiplicative ℤ) (α : Additive X) (hα : 0 < pairingHom ψ α),
        α ∈ roots π → BruhatRayCore π ψ α hα)
    (hFp : CharpolyFinite.Step2OverFpBar k
      ((FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H)
        (magnetHopfIdeal π ⊥)) ⧸
        (TauCeti.CommHopfAlgCat.derivedDefiningIdeal (R := k)
          (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H)
            (magnetHopfIdeal π ⊥))).toIdeal))
    (hBorMax : letI : Algebra.Smooth k H := hred.smooth
      ∀ δ : Additive X, δ ≠ 0 →
        (∀ β ∈ roots π, (∃ m n : ℤ, n ≠ 0 ∧ n • β = m • δ) → β ∈ lineMagnet δ) →
        ∃ ψ : X →* Multiplicative ℤ, pairingHom ψ δ ≠ 0 ∧ BorelZMax π δ ψ) :
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
  -- hsolvC: C solvable, from the central maximal torus T ⊆ C
  haveI : ConnectedSpace (PrimeSpectrum (FiniteTypeCommHopfAlgCat.quotient
      (FiniteTypeCommHopfAlgCat.of k H) (magnetHopfIdeal π ⊥))) :=
    (geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace k _).1 hconnC
  have hsolvC : geometricallySolvablePointsCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H)
        (magnetHopfIdeal π ⊥)).obj :=
    hsolvC_of_step2OverFpBar π hπ hT hFp
  -- T4 via the Bruhat core
  have hray : ∀ (ψ : X →* Multiplicative ℤ) (α : Additive X) (_ : 0 < pairingHom ψ α),
      rayDim π (pairingHom ψ) α ≤ 1 := by
    intro ψ α hα
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
      rw [heq]
      letI : Algebra.Smooth k (ZAlg π (rayGen π ψ β hβpos).1) :=
        smooth_quotient_magnetHopfIdeal π _
      have hc := hBruhat ψ β hβpos ((finite_roots (π := π)).mem_toFinset.1 hβR)
      exact rayDim_le_one π (rayDimData_of_hAff π ψ β hβpos
        (hAff_of_bruhatCore _ hc.choose _ _ hc.choose_spec))
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      unfold rayDim
      rw [hne]
      simp
  let toψ : (Additive X →+ ℤ) → (X →* Multiplicative ℤ) := fun f =>
    { toFun := fun x => Multiplicative.ofAdd (f (Additive.ofMul x))
      map_one' := by simp
      map_mul' := fun a b => by simp [ofAdd_add] }
  have htoψ : ∀ f, pairingHom (toψ f) = f := fun f => by ext χ; rfl
  have hD : ∀ (f : Additive X →+ ℤ), ∀ α ∈ posRoots π f, Nonempty (RayDimData π f α) := by
    intro f α hα
    have hpos : 0 < pairingHom (toψ f) α := by
      rw [htoψ]; exact (Finset.mem_filter.1 hα).2
    letI : Algebra.Smooth k (ZAlg π (rayGen π (toψ f) α hpos).1) :=
      smooth_quotient_magnetHopfIdeal π _
    have hc := hBruhat (toψ f) α hpos
      ((finite_roots (π := π)).mem_toFinset.1 (Finset.mem_filter.1 hα).1)
    have := rayDimData_of_hAff π (toψ f) α hpos
      (hAff_of_bruhatCore _ hc.choose _ _ hc.choose_spec)
    rw [htoψ] at this
    exact ⟨this⟩
  have hT4 : ∀ (g : Additive X →+ ℤ), ∀ γ ∈ posRoots π g, rayDim π g γ ≤ 1 :=
    fun g γ hγ => rayDim_le_one π (hD g γ hγ).some
  -- hLie0
  obtain ⟨ψ₀, hψ₀⟩ := exists_generic_cocharacter (roots π) finite_roots
    (fun α hα => ne_zero_of_mem_roots hα)
  have hcent := hcent_CuIdeal_of_rayDim π (ψ := ψ₀)
    (fun φ _ α => hray φ α.1 α.2)
  have hCT' := HCTReal.hCT π hπ (CuIdeal π) (smooth_quotient_magnetHopfIdeal π ⊥) hconnC hsolvC
    (RuC_eq_augmentation π) hT (magnetHopfIdeal_bot_le_ker π hπ)
  have hLie0 := finrank_rootSpace_zero_le_of_reductive_Cu π hπ ψ₀ hψ₀ hred hcent hCT'
  -- (DC), (i), counts
  obtain ⟨ψ, hψ, hDC⟩ := dimCount_of_reductive'' π hπ hT hred hLie0 hD
  obtain ⟨h1, h2, h3⟩ := condI_and_counts_of_dimCount π hπ ψ hψ hDC
  -- (R1) via line generator + bootstrap; Borel side from `BorelZMax` and `ZZSolvable`
  have hR1at : ∀ δ : Additive X, δ ≠ 0 →
      (∀ β ∈ roots π, (∃ m n : ℤ, n ≠ 0 ∧ n • β = m • δ) → β ∈ lineMagnet δ) →
      (∃ α ∈ roots π, α ∈ lineMagnet δ) →
      ∃ (n : WithConv (H →ₐ[k] k)) (σ : X ≃* X), IsNormalizingWith π k n σ ∧
        n ∈ attractorSubgroup π (lineMagnet δ) k ∧ σ ≠ 1 := by
    intro δ hδ hRay hroot
    obtain ⟨α, hα, hαδ⟩ := hroot
    obtain ⟨φ, hφ, hmax⟩ := hBorMax δ hδ hRay
    exact r1_of_borelZMax π hπ hT δ hδ hRay φ hφ hα hαδ (zzSolvable_of_hsolvC π hφ hsolvC) hmax
  have hR1 : ∀ α ∈ roots π, ∃ (n : WithConv (H →ₐ[k] k)) (σ : X ≃* X),
      IsNormalizingWith π k n σ ∧ n ∈ attractorSubgroup π (lineMagnet α) k ∧ σ ≠ 1 := by
    intro α hα
    obtain ⟨δ, hδ0, hαδ, hRayδ⟩ := exists_line_generator π hα
    obtain ⟨n, σ, hn, hmem, hσ⟩ := hR1at δ hδ0 hRayδ ⟨α, hα, hαδ⟩
    have hfin := isOfFinOrder_of_isNormalizingWith π hπ hn
    have hα0 := ne_zero_of_mem_roots hα
    obtain ⟨f, hf⟩ : ∃ f : Additive X →+ ℤ, 0 < f α := by
      rcases lt_or_gt_of_ne (hψ α hα) with h | h
      · exact ⟨-pairingHom ψ, by rw [AddMonoidHom.neg_apply]; omega⟩
      · exact ⟨pairingHom ψ, h⟩
    have hRayα := hRay_of_bootstrap π hπ hn hδ0 hmem hσ hfin hα hαδ f hf hT4
    exact hR1at α hα0 hRayα ⟨α, hα, mem_lineMagnet.2 (AddSubgroup.mem_zmultiples α)⟩
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

/-- **(⇒) in characteristic `0`**: no `Step2OverFpBar` input. -/
theorem condI_condII_condIII_of_reductive_final2_charZero [CharZero k]
    [Module.IsTorsionFree ℤ (Additive X)]
    (π : H →ₐc[k] MonoidAlgebra k X)
    (hπ : Function.Surjective π)
    (hT : HopfIdeal.IsMaximalTorus k (CommHopfAlgCat.of k H) (HopfIdeal.kerOfSurjective π hπ))
    (hred : reductiveCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.of k H))
    (hBruhat : letI : Algebra.Smooth k H := hred.smooth
      haveI : IsMulTorsionFree X := ⟨fun n hn =>
        (IsAddTorsionFree.of_isTorsionFree ℤ (Additive X)).nsmul_right_injective hn⟩
      ∀ (ψ : X →* Multiplicative ℤ) (α : Additive X) (hα : 0 < pairingHom ψ α),
        α ∈ roots π → BruhatRayCore π ψ α hα)
    (hBorMax : letI : Algebra.Smooth k H := hred.smooth
      ∀ δ : Additive X, δ ≠ 0 →
        (∀ β ∈ roots π, (∃ m n : ℤ, n ≠ 0 ∧ n • β = m • δ) → β ∈ lineMagnet δ) →
        ∃ ψ : X →* Multiplicative ℤ, pairingHom ψ δ ≠ 0 ∧ BorelZMax π δ ψ) :
    CondI π ∧ CondII π ∧ CondIII π :=
  condI_condII_condIII_of_reductive_final2 π hπ hT hred hBruhat
    CharpolyFinite.step2OverFpBar_of_charZero hBorMax

end AlgMag.Reductive

#print axioms AlgMag.Reductive.condI_condII_condIII_of_reductive_final2
#print axioms AlgMag.Reductive.condI_condII_condIII_of_reductive_final2_charZero
#print axioms AlgMag.Reductive.zzSolvable_of_hsolvC
#print axioms AlgMag.Reductive.hsolvC_of_step2OverFpBar
