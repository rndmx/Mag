/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.ClosedOrbit
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Points
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Translation
import TauCeti.Algebra.AlgebraicGroup.Representation.Stabilizer
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.FiniteType
import TauCeti.AlgebraicGeometry.AugmentationPoint.ClosedPoints
import Mathlib.RingTheory.Spectrum.Prime.Jacobson
import AlgMag.Reductive.FlagComodule

/-!
# (Y_Z): a closed projective orbit with solvable stabiliser

G1-plan.md, Section 3, step (Y_Z). Let `H` be the coordinate Hopf algebra of an affine group of
finite type over an algebraically closed field `k`. Then there are a finite-dimensional comodule
`M`, a line `[m] ∈ P(M)` whose orbit is closed, and a Hopf ideal `S` (the stabiliser of `[m]`)
whose rational points are exactly the rational points fixing `[m]` and form a solvable group.

Neither smoothness nor connectedness is needed (the plan's hypotheses are dropped).

Proof route. `M = ⨂_{i=1}^{n} ⋀^i W` for a faithful finite-dimensional `W`; the flag locus
`F ⊆ P(M)` (Segre minors, Plücker equations, incidence equations) is closed, nonempty and
`G`-stable; Tau Ceti's `exists_isClosed_range_projectiveOrbitMap_subset_of_isClosed` gives a
closed orbit in `F`; the rational stabiliser of a point of `F` fixes a full flag of `W`, so it
embeds into the upper-triangular group and is solvable.

The linear algebra of the flag locus is in `FlagLocus.lean`, and the comodule structure on the
flag tensor space is in `FlagComodule.lean`. `F` is the closure of the orbit of the standard
flag tensor. It lies in the zero locus `Z` of the quadratic flag equations: every point of `Spec H`
specializes from closed points, which are rational points.
-/

open AlgebraicGeometry

namespace AlgMag.Reductive.FlagOrbit

open TauCeti TauCeti.Comodule

universe u

variable {k H : Type u} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H]

/-- The rational points fixing the line `[m]`, as a Hopf-ideal stabiliser. -/
noncomputable abbrev lineStabilizer {M : Type u} [AddCommGroup M] [Module k M]
    [Comodule k H M] (m : M) : HopfIdeal k H :=
  (k ∙ m).stabilizerHopfIdeal H

/-- `hstab` for the line stabiliser: a rational point lies in the stabiliser Hopf ideal of
`k ∙ m` iff it fixes the point `[m]` of the orbit map. Proved from Tau Ceti. -/
theorem mem_lineStabilizer_iff {M : Type u} [AddCommGroup M] [Module k M] [Comodule k H M]
    [Module.Finite k M] (m : M) (hm : Module.IsUnimodular k m) (a : WithConv (H →ₐ[k] k)) :
    a ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H)
        (lineStabilizer (H := H) m) (CommAlgCat.of k k) ↔
      projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint a.ofConv) =
        projectiveOrbitMap (H := H) m hm
          (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) := by
  rw [Submodule.mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff, Submodule.map_span,
    Set.image_singleton]
  have h1 := projectiveOrbitMap_kernelPoint_eq_iff_span_eq (H := H) m hm m hm a 1
  have hone : (1 : WithConv (H →ₐ[k] k)).ofConv = Bialgebra.counitAlgHom k H := rfl
  rw [hone] at h1
  rw [h1, map_one]
  rfl

theorem isUnimodular_of_ne_zero {M : Type u} [AddCommGroup M] [Module k M] {m : M} (hm : m ≠ 0) :
    Module.IsUnimodular k m := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero k hm
  exact Module.isUnimodular_of_apply_eq_one (f := (φ m)⁻¹ • φ) (by simp [hφ])

theorem ne_zero_of_isUnimodular {M : Type u} [AddCommGroup M] [Module k M] {m : M}
    (hm : Module.IsUnimodular k m) : m ≠ 0 := by
  obtain ⟨f, hf⟩ := hm
  rintro rfl
  simp at hf

section Generic

variable {M : Type u} [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

/-- The common zero locus of the diagonals `v ↦ B v v` of a family of bilinear forms. -/
def quadZero (S : Set (M →ₗ[k] M →ₗ[k] k)) :
    Set (Proj (SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k M))) :=
  {x | ∀ B ∈ S, FlagLocus.quadPoly B ∈ x.asHomogeneousIdeal}

theorem isClosed_quadZero (S : Set (M →ₗ[k] M →ₗ[k] k)) : IsClosed (quadZero S) := by
  have : (quadZero S : Set (ProjectiveSpectrum
      (SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k M)))) = ⋂ B ∈ S,
      ProjectiveSpectrum.zeroLocus
        (SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k M)) {FlagLocus.quadPoly B} := by
    ext (x : ProjectiveSpectrum _)
    refine ⟨fun hx ↦ Set.mem_iInter₂.2 fun B hB ↦ ?_, fun hx B hB ↦ ?_⟩
    · show ({FlagLocus.quadPoly B} : Set _) ⊆ (x.asHomogeneousIdeal : Set _)
      exact Set.singleton_subset_iff.2 (hx B hB)
    · have h1 : ({FlagLocus.quadPoly B} : Set _) ⊆ (x.asHomogeneousIdeal : Set _) :=
        Set.mem_iInter₂.1 hx B hB
      exact Set.singleton_subset_iff.1 h1
  exact this ▸ isClosed_biInter fun B _ ↦ ProjectiveSpectrum.isClosed_zeroLocus _ _

/-- The base point of an orbit lying in `quadZero S` is a common zero. -/
theorem forall_eq_zero_of_mem_quadZero (S : Set (M →ₗ[k] M →ₗ[k] k)) (m : M)
    (hm : Module.IsUnimodular k m)
    (hx : projectiveOrbitMap (H := H) m hm
      (AlgHom.kernelPoint ((1 : WithConv (H →ₐ[k] k)).ofConv)) ∈ quadZero S) :
    ∀ B ∈ S, B m m = 0 := by
  intro B hB
  have := hx B hB
  rw [mem_projectiveOrbitMap_kernelPoint_iff m hm 1 (by norm_num : 0 < 2)
    (FlagLocus.quadPoly_mem B), FlagLocus.lift_eval_quadPoly, map_one] at this
  exact this

/-- If every rational translate of `t₀` is a common zero, the whole orbit lies in `quadZero S`. -/
theorem range_subset_quadZero (S : Set (M →ₗ[k] M →ₗ[k] k)) (t₀ : M)
    (hu₀ : Module.IsUnimodular k t₀)
    (h : ∀ g : WithConv (H →ₐ[k] k), ∀ B ∈ S,
      B (basePointsRepresentation (H := H) M g t₀) (basePointsRepresentation (H := H) M g t₀) = 0) :
    Set.range (projectiveOrbitMap (H := H) t₀ hu₀) ⊆ quadZero S := by
  rintro _ ⟨x, rfl⟩ B hB
  rw [mem_projectiveOrbitMap_iff t₀ hu₀ x (by norm_num : 0 < 2) (FlagLocus.quadPoly_mem B)]
  set e := orbitCoordinates (H := H) t₀ (FlagLocus.quadPoly B)
  have hcl : closedPoints (PrimeSpectrum H) ⊆ PrimeSpectrum.zeroLocus ({e} : Set H) := by
    intro y hy
    have hy' : y ∈ closedPoints (Spec (.of H)) := hy
    rw [← range_kernelPoint_eq_closedPoints (k := k)] at hy'
    obtain ⟨f, rfl⟩ := hy'
    show ({e} : Set H) ⊆ ((AlgHom.kernelPoint f).asIdeal : Set H)
    rw [Set.singleton_subset_iff, SetLike.mem_coe, AlgHom.kernelPoint_asIdeal, RingHom.mem_ker]
    have hcomp := congrArg (fun φ : _ →ₐ[k] k ↦ φ (FlagLocus.quadPoly B))
      (comp_orbitCoordinates (H := H) t₀ (WithConv.toConv f))
    simp only [AlgHom.comp_apply, WithConv.ofConv_toConv] at hcomp
    change f e = 0
    rw [hcomp, FlagLocus.lift_eval_quadPoly]
    exact h _ B hB
  haveI : IsJacobsonRing H := isJacobsonRing_of_finiteType (A := k)
  have huniv := closure_minimal hcl (PrimeSpectrum.isClosed_zeroLocus _)
  rw [closure_closedPoints] at huniv
  have : ({e} : Set H) ⊆ (x.asIdeal : Set H) := huniv (Set.mem_univ (x : PrimeSpectrum H))
  exact Set.singleton_subset_iff.mp this

end Generic

set_option maxHeartbeats 800000 in
/-- **The flag locus.** There are a finite-dimensional comodule `M` and a
closed, nonempty, `G(k)`-stable subset `F ⊆ P(M)` such that the rational stabiliser of every
line whose orbit lies in `F` is solvable.

Intended proof: `M = ⨂_{i=1}^{n} ⋀^i W` with `W` faithful (`exists_coordinateBialgHom_surjective`,
Representation/Embedding.lean); `F` = zero locus of Segre 2×2 minors, Plücker relations
`ι(contract η θ_i) * θ_i = 0` (`mem_range_ιMulti_iff_forall_ι_contract_mul_eq_zero`,
LinearAlgebra/ExteriorPower/Decomposable.lean) and incidences `θ_{i+1} ∧ ι_η θ_i = 0`;
closed points of `F` = full flags; stabiliser of a flag ⊆ upper-triangular group in a
flag-adapted basis (`GeneralLinear.UpperTriangular.isSolvable_points`), injective by
faithfulness. -/
theorem exists_flagLocus :
    ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module k M) (_ : Comodule k H M)
      (_ : Module.Finite k M)
      (F : Set (Proj (SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k M)))),
      IsClosed F ∧ F.Nonempty ∧
      (∀ g : WithConv (H →ₐ[k] k), Set.MapsTo (projectivePointTranslation (M := M) g).hom F F) ∧
      ∀ (m : M) (hm : Module.IsUnimodular k m),
        Set.range (projectiveOrbitMap (H := H) m hm) ⊆ F →
        Group.IsSolvable (CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H)
          (lineStabilizer (H := H) m) (CommAlgCat.of k k)) := by
  classical
  obtain ⟨W₀, hfin, htop⟩ :=
    Comodule.exists_finite_subcomodule_matrixCoefficientSubalgebra_eq_top (k := k) (C := H)
  haveI : FiniteDimensional k W₀ := hfin
  let n := Module.finrank k W₀
  letI cM := FlagLocus.ftComodule k H W₀ n
  let b := Module.finBasis k W₀
  let t₀ : FlagLocus.FT k W₀ n := FlagLocus.pureT (FlagLocus.stdFlag b) n
  have ht₀ : t₀ ≠ 0 :=
    FlagLocus.pureT_ne_zero _ fun r _ h2 ↦ FlagLocus.stdFlag_ne_zero b h2
  have hu₀ : Module.IsUnimodular k t₀ := isUnimodular_of_ne_zero ht₀
  let ρW : WithConv (H →ₐ[k] k) →* (W₀ →ₗ[k] W₀)ˣ :=
    (basePointsRepresentation (R := k) (H := H) W₀).toHomUnits
  have hact : ∀ g, basePointsRepresentation (H := H) (FlagLocus.FT k W₀ n) g =
      FlagLocus.actT (FlagLocus.wedgeAct (ρW g)) n :=
    fun g ↦ FlagLocus.bpr_ft n g (ρW g) rfl
  have hsub := range_subset_quadZero (FlagLocus.flagForms k W₀ n) t₀ hu₀
    fun g B hB ↦ by
      rw [hact]
      exact (FlagLocus.flagEqs_iff_forms _).mp
        ((FlagLocus.flagEqs_pureT_stdFlag b).wedge (ρW g)) B hB
  refine ⟨FlagLocus.FT k W₀ n, inferInstance, inferInstance, cM, inferInstance,
    closure (Set.range (projectiveOrbitMap (H := H) t₀ hu₀)), isClosed_closure,
    ⟨_, subset_closure ⟨AlgHom.kernelPoint (Bialgebra.counitAlgHom k H), rfl⟩⟩,
    fun g ↦ ?_, fun m hm hrange ↦ ?_⟩
  · refine Set.MapsTo.closure (fun y hy ↦ ?_) (projectivePointTranslation (M := FlagLocus.FT k W₀ n) g).hom.continuous
    rw [← image_projectivePointTranslation_range_projectiveOrbitMap (H := H) g t₀ hu₀]
    exact ⟨y, hy, rfl⟩
  · -- the base point of the closed orbit satisfies the flag equations
    have hmZ : projectiveOrbitMap (H := H) m hm
        (AlgHom.kernelPoint ((1 : WithConv (H →ₐ[k] k)).ofConv)) ∈ quadZero _ :=
      closure_minimal hsub (isClosed_quadZero _) (hrange ⟨_, rfl⟩)
    have heq : FlagLocus.FlagEqs k W₀ n m :=
      (FlagLocus.flagEqs_iff_forms m).mpr (forall_eq_zero_of_mem_quadZero _ m hm hmZ)
    -- the stabiliser acts faithfully on `W₀` and fixes the line of `m`
    let G := CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H)
      (lineStabilizer (H := H) m) (CommAlgCat.of k k)
    have hinj : Function.Injective (ρW.comp G.subtype) := by
      intro x y hxy
      apply Subtype.val_injective
      apply FlagLocus.basePointsRepresentation_injective htop
      have := congrArg (fun u : (W₀ →ₗ[k] W₀)ˣ ↦ (u : W₀ →ₗ[k] W₀)) hxy
      exact this
    refine FlagLocus.isSolvable_of_flagEqs (ρW.comp G.subtype) hinj rfl m
      (ne_zero_of_isUnimodular hm) heq fun g ↦ ?_
    have hg := (Submodule.mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff (H := H) (k ∙ m)
      (g : WithConv (H →ₐ[k] k))).mp g.2
    have hmem : basePointsRepresentation (H := H) _ (g : WithConv (H →ₐ[k] k)) m ∈ k ∙ m := by
      rw [← hg]
      exact Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self m)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    refine ⟨c, ?_⟩
    rw [MonoidHom.comp_apply, ← hact, Subgroup.coe_subtype]
    exact hc.symm

/-- **(Y_Z).** Every affine group of finite type over an algebraically closed field has a closed
projective orbit whose stabiliser `S` satisfies `hstab` (in the exact form of Tau Ceti's
`isBorelOverAlgClosed_iff_exists_eq_conjugate_of_isClosed_projectiveOrbit`) and has a solvable
group of rational points. -/
theorem exists_isClosed_projectiveOrbit_solvable_stabilizer :
    ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module k M) (_ : Comodule k H M)
      (_ : Module.Finite k M) (m : M) (hm : Module.IsUnimodular k m) (S : HopfIdeal k H),
      IsClosed (Set.range (projectiveOrbitMap (H := H) m hm)) ∧
      (∀ a : WithConv (H →ₐ[k] k),
        a ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) S
            (CommAlgCat.of k k) ↔
          projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint a.ofConv) =
            projectiveOrbitMap (H := H) m hm
              (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H))) ∧
      Group.IsSolvable (CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) S
        (CommAlgCat.of k k)) := by
  obtain ⟨M, _, _, _, _, F, hF, hne, hinv, hsolv⟩ := exists_flagLocus (k := k) (H := H)
  obtain ⟨m, hm, hclosed, hsub⟩ :=
    exists_isClosed_range_projectiveOrbitMap_subset_of_isClosed (H := H) hF hne hinv
  exact ⟨M, _, _, _, _, m, hm, lineStabilizer (H := H) m, hclosed,
    mem_lineStabilizer_iff m hm, hsolv m hm hsub⟩

end AlgMag.Reductive.FlagOrbit
