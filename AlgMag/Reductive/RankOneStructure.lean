/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.BruhatRankOneProof
import AlgMag.Reductive.OpenCellGen
import AlgMag.Reductive.PointsDensity
import AlgMag.Reductive.BorSideFinal

/-!
# Rank-one structure: T2 and `T`-transitivity give `BorelZMax`

This is the density argument of finish-plan §2, proved for an arbitrary smooth connected affine
group `G = Spec H` over `k = k̄` and a cocharacter `λ`.

Let `V(J)` be a Borel candidate (smooth, connected, solvable) with `P(λ) ⊆ V(J)`, and let
`K = V(J)(k)`.
* If `K` contains some `u ≠ 1` of `U(λ⁻¹)(k)`, then `T`-transitivity on `U(λ⁻¹)(k) ∖ 1` (with
  conjugating elements in `P(λ)(k) ⊆ K`) gives `U(λ⁻¹)(k) ⊆ K`. So `K` contains the points
  `U(λ⁻¹)(k)·P(λ)(k)` of the open cell `Ω`, which form a nonempty open subset of the
  irreducible `G(k)` (`points_eq_top`). Hence `K = G(k)` and `G(k)` is solvable.
* Otherwise `K ∩ Ω(k) ⊆ P(λ)(k)`, which is open and nonempty in the irreducible `K`, so
  `K ⊆ P(λ)(k)` (`points_le_parabolic`). The Nullstellensatz (`J` is radical) then gives
  `V(J) ⊆ P(λ)`.

Main results:
* `le_parabolic_of_isBorelCandidate` (generic): if `G(k)` is not solvable and `T`-transitivity
  holds on `U(λ⁻¹)(k) ∖ 1`, then `P(λ)` is a minimal Borel-candidate Hopf ideal.
* `borelZMax_of_trans`: `BorelZMax π δ ψ` for `Z = G^{ℤδ}` from T2 (`Z(k)` not solvable) and
  `T`-transitivity on `U_Z(λ^{∓1})(k) ∖ 1`. No reductivity is used. The counterexample
  `SL₂ ⋉ 𝔰𝔩₂` satisfies T2 but not `BorelZMax`; there `U_Z(λ⁻¹)` is 2-dimensional and
  transitivity fails.
* `uTrans_of_coord`: transitivity from a `𝔾_a`-coordinate on which `T` acts by a character onto
  `kˣ` (`htrans_of_coordinate`).
-/

suppress_compilation

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory Magnetism TauCeti TauCeti.Cocharacter WithConv

universe u

namespace AlgMag.Reductive.RankOneStructure

open AlgMag.Reductive

section Generic

variable {k : Type u} {H : Type u} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H]

/-- **Nullstellensatz.** For a radical ideal `J` of `H` (finite type over `k = k̄`), an ideal `I`
killed by every `k`-point of `V(J)` is contained in `J`. -/
theorem le_of_forall_points {J I : Ideal H} (hJ : J.IsRadical)
    (h : ∀ x : H →ₐ[k] k, J ≤ RingHom.ker x → I ≤ RingHom.ker x) : I ≤ J := by
  intro f hf
  have hJR : IsJacobsonRing H := isJacobsonRing_of_finiteType (A := k)
  have hrad : J.radical.jacobson = J.radical :=
    IsJacobsonRing.out hJR (Ideal.radical_isRadical J)
  have hfj : f ∈ J.radical.jacobson := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro m ⟨hJm, hm⟩
    obtain ⟨φ, hφ⟩ := OpenCellNotes.exists_algHom_ker_eq (K := k) m
    rw [← hφ]
    exact h φ (by rw [hφ]; exact Ideal.le_radical.trans hJm) hf
  rwa [hrad, hJ.radical] at hfj

open scoped Zariski

/-- **`V(J)(k)` is irreducible** when `Spec (H ⧸ J)` is (Zariski topology on `k`-points). -/
theorem irreducibleSpace_points_of_quot (J : Ideal H) [IrreducibleSpace (PrimeSpectrum (H ⧸ J))]
    (K : Set (WithConv (H →ₐ[k] k))) (hK : ∀ x, x ∈ K ↔ J ≤ RingHom.ker x.ofConv) :
    IrreducibleSpace K := by
  have hq : Function.Surjective (Ideal.Quotient.mk J) := Ideal.Quotient.mk_surjective
  have hZ : IsIrreducible (PrimeSpectrum.zeroLocus (J : Set H)) := by
    have h := (IrreducibleSpace.isIrreducible_univ (PrimeSpectrum (H ⧸ J))).image
      (PrimeSpectrum.comap (Ideal.Quotient.mk J)) (PrimeSpectrum.continuous_comap _).continuousOn
    rwa [Set.image_univ, range_comap_of_surjective _ _ hq, Ideal.mk_ker] at h
  set S : Set (PrimeSpectrum H) := Set.range fun x : K => kerPt (x : WithConv (H →ₐ[k] k))
  have hcl : closure S = PrimeSpectrum.zeroLocus (J : Set H) := by
    apply le_antisymm
    · rw [(PrimeSpectrum.isClosed_zeroLocus _).closure_subset_iff]
      rintro _ ⟨x, rfl⟩
      exact ((hK x).1 x.2 : _)
    · rw [← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
      intro p hp f hf
      rw [PrimeSpectrum.mem_zeroLocus] at hp
      have hJR : IsJacobsonRing H := isJacobsonRing_of_finiteType (A := k)
      have hrad : J.radical.jacobson = J.radical :=
        IsJacobsonRing.out hJR (Ideal.radical_isRadical J)
      have hfj : f ∈ J.radical.jacobson := by
        rw [Ideal.jacobson, Ideal.mem_sInf]
        rintro m ⟨hcm, hm⟩
        obtain ⟨φ, hφ⟩ := OpenCellNotes.exists_algHom_ker_eq (K := k) m
        have hφK : toConv φ ∈ K := (hK _).2 (by
          rw [ofConv_toConv, hφ]; exact Ideal.le_radical.trans hcm)
        have := (PrimeSpectrum.mem_vanishingIdeal _ _).1 hf _ ⟨⟨_, hφK⟩, rfl⟩
        rw [← hφ]; exact this
      rw [hrad] at hfj
      exact (Ideal.IsPrime.radical_le_iff p.isPrime).2 hp hfj
  have hSirr : IsIrreducible S := isIrreducible_iff_closure.1 (hcl ▸ hZ)
  have : Nonempty K := by
    obtain ⟨_, ⟨x, rfl⟩⟩ := hSirr.nonempty
    exact ⟨x⟩
  exact irreducibleSpace_of_isInducing (f := fun x : K => kerPt (x : WithConv (H →ₐ[k] k)))
    (isInducing_kerPt.comp Topology.IsInducing.subtypeVal) hSirr.isPreirreducible

variable [Algebra.Smooth k H]

/-- The `k`-points of the open cell `Ω = U(λ⁻¹)·P(λ)`: those whose kernel lies in the image of
`Spec` of the open-cell ring. -/
def cellSet (l : H →ₐc[k] LaurentPolynomial k) : Set (WithConv (H →ₐ[k] k)) :=
  {x | kerPt x ∈ Set.range (PrimeSpectrum.comap (R := H) (S := OpenCellRing l) (openCellRingHom l))}

theorem isOpen_cellSet (l : H →ₐc[k] LaurentPolynomial k) : IsOpen (cellSet l) :=
  (isOpenEmbedding_openCell l).isOpen_range.preimage isInducing_kerPt.continuous

/-- A `k`-point of the open-cell ring gives a `k`-point of `Ω`. -/
theorem mem_cellSet_of_point (l : H →ₐc[k] LaurentPolynomial k) (χ : OpenCellRing l →ₐ[k] k) :
    toConv (χ.comp (openCellMap l)) ∈ cellSet l := by
  refine ⟨⟨RingHom.ker χ, RingHom.ker_isPrime _⟩, ?_⟩
  ext a
  change openCellMap l a ∈ RingHom.ker χ ↔ χ (openCellMap l a) = 0
  exact RingHom.mem_ker

/-- `U(λ⁻¹)(k)·P(λ)(k) ⊆ Ω(k)` (`cellPointsSurj`). -/
theorem mul_mem_cellSet (l : H →ₐc[k] LaurentPolynomial k) {v p : WithConv (H →ₐ[k] k)}
    (hv : v ∈ unipotent k l.oppositeCocharacter) (hp : p ∈ parabolic k l) :
    v * p ∈ cellSet l := by
  obtain ⟨χ, hχ⟩ := cellPointsSurj l v hv p hp
  rw [← hχ]
  exact mem_cellSet_of_point l χ

theorem one_mem_cellSet (l : H →ₐc[k] LaurentPolynomial k) :
    (1 : WithConv (H →ₐ[k] k)) ∈ cellSet l := by
  have h := mul_mem_cellSet l (one_mem (unipotent k l.oppositeCocharacter))
    (one_mem (parabolic k l))
  rwa [mul_one] at h

/-- `Ω(k) ⊆ U(λ⁻¹)(k)·P(λ)(k)`. -/
theorem exists_mul_of_mem_cellSet (l : H →ₐc[k] LaurentPolynomial k)
    {x : WithConv (H →ₐ[k] k)} (hx : x ∈ cellSet l) :
    ∃ v ∈ unipotent k l.oppositeCocharacter, ∃ p ∈ parabolic k l, x = v * p := by
  obtain ⟨q, hq⟩ := hx
  have hemb := isOpenEmbedding_openCell l
  have hmaxx : (kerPt x).asIdeal.IsMaximal := RingHom.ker_isMaximal_of_surjective _
    (fun c => ⟨algebraMap k H c, by simp⟩)
  have hqmax : q.asIdeal.IsMaximal := by
    rw [← PrimeSpectrum.isClosed_singleton_iff_isMaximal]
    have hc : IsClosed ({kerPt x} : Set (PrimeSpectrum H)) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 hmaxx
    have := hc.preimage hemb.continuous
    convert this using 1
    ext q'
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact ⟨fun h => h ▸ hq, fun h => hemb.injective (h.trans hq.symm)⟩
  obtain ⟨f, hf⟩ := OpenCellNotes.exists_algHom_ker_eq (K := k) (A := OpenCellRing l) q.asIdeal
  have key : ∀ a, f (openCellMap l a) = 0 ↔ x.ofConv a = 0 := by
    intro a
    have e1 : f (openCellMap l a) = 0 ↔ openCellMap l a ∈ q.asIdeal := by rw [← hf]; rfl
    have e2 : x.ofConv a = 0 ↔ a ∈ (kerPt x).asIdeal := Iff.rfl
    rw [e1, e2, ← hq]
    rfl
  have hx : toConv (f.comp (openCellMap l)) = x := by
    apply WithConv.ofConv_injective
    apply eq_of_ker_eq
    ext a
    exact key a
  refine ⟨cellPt1 l f, cellPt1_mem l f, cellPt2 l f * cellPt3 l f,
    mul_mem (cellPt2_mem l f) (unipotent_le_parabolic (cellPt3_mem l f)), ?_⟩
  rw [← hx, openCellMap_point, mul_assoc]

/-- **Case "no `u ≠ 1`".** A subgroup `K` of `G(k)`, irreducible for the Zariski topology, with
`P(λ)(k) ⊆ K` and `K ∩ U(λ⁻¹)(k) = 1`, is contained in `P(λ)(k)`. -/
theorem points_le_parabolic (l : H →ₐc[k] LaurentPolynomial k)
    (K : Subgroup (WithConv (H →ₐ[k] k))) [IrreducibleSpace (K : Set (WithConv (H →ₐ[k] k)))]
    (hPK : parabolic k l ≤ K)
    (hU : ∀ v ∈ unipotent k l.oppositeCocharacter, v ∈ K → v = 1) :
    K ≤ parabolic k l := by
  let O : Set (K : Set (WithConv (H →ₐ[k] k))) := Subtype.val ⁻¹' cellSet l
  have hO : IsOpen O := (isOpen_cellSet l).preimage continuous_subtype_val
  have hOn : O.Nonempty := ⟨⟨1, K.one_mem⟩, one_mem_cellSet l⟩
  have hOS : ∀ x ∈ O, (x : WithConv (H →ₐ[k] k)) ∈ parabolic k l := by
    intro x hx
    obtain ⟨v, hv, p, hp, hxe⟩ := exists_mul_of_mem_cellSet l hx
    have hvK : v ∈ K := by
      have : v = (x : WithConv (H →ₐ[k] k)) * p⁻¹ := by rw [hxe]; group
      rw [this]; exact K.mul_mem x.2 (K.inv_mem (hPK hp))
    rw [hxe, hU v hv hvK, one_mul]; exact hp
  intro g hg
  exact subset_of_isOpen_subset (K : Set (WithConv (H →ₐ[k] k)))
    (fun x hx y hy => K.mul_mem hx hy) (fun x hx => K.inv_mem hx)
    (parabolic k l) O hO hOn hOS g hg

/-- **Case "some `u ≠ 1`".** A subgroup containing `U(λ⁻¹)(k)` and `P(λ)(k)` is all of `G(k)`
(`G` irreducible). -/
theorem points_eq_top [IrreducibleSpace (PrimeSpectrum H)] (l : H →ₐc[k] LaurentPolynomial k)
    (K : Subgroup (WithConv (H →ₐ[k] k)))
    (hPK : parabolic k l ≤ K) (hUK : unipotent k l.oppositeCocharacter ≤ K) : K = ⊤ := by
  set Ks := (Set.univ : Set (WithConv (H →ₐ[k] k)))
  haveI : IrreducibleSpace Ks := irreducibleSpace_points_univ
  let O : Set Ks := Subtype.val ⁻¹' cellSet l
  have hO : IsOpen O := (isOpen_cellSet l).preimage continuous_subtype_val
  have hOn : O.Nonempty := ⟨⟨1, Set.mem_univ _⟩, one_mem_cellSet l⟩
  have hOS : ∀ x ∈ O, (x : WithConv (H →ₐ[k] k)) ∈ K := by
    intro x hx
    obtain ⟨v, hv, p, hp, hxe⟩ := exists_mul_of_mem_cellSet l hx
    rw [hxe]; exact K.mul_mem (hUK hv) (hPK hp)
  exact eq_top_iff.2 fun g _ => subset_of_isOpen_subset Ks (fun _ _ _ _ => Set.mem_univ _)
    (fun _ _ => Set.mem_univ _) K O hO hOn hOS g (Set.mem_univ _)

/-- **`T`-transitivity on `U(λ⁻¹)(k) ∖ 1`**, with conjugating elements in `P(λ)(k)` (named).
True for `SL₂`: `diag(a, a⁻¹)` conjugates `u⁻(x)` to `u⁻(a⁻²x)`, and `a⁻²` runs over `kˣ`. -/
def UTrans (l : H →ₐc[k] LaurentPolynomial k) : Prop :=
  ∀ u ∈ unipotent k l.oppositeCocharacter, ∀ v ∈ unipotent k l.oppositeCocharacter,
    u ≠ 1 → v ≠ 1 → ∃ t ∈ parabolic k l, v = t * u * t⁻¹

/-- **The density argument (generic).** Let `G` be smooth and connected with `G(k)` not solvable,
and suppose `T`-transitivity holds on `U(λ⁻¹)(k) ∖ 1`. Then `P(λ)` is minimal among Borel-candidate
Hopf ideals: every smooth, connected, solvable `V(J) ⊇ P(λ)` equals `P(λ)`. -/
theorem le_parabolic_of_isBorelCandidate [IrreducibleSpace (PrimeSpectrum H)]
    (l : H →ₐc[k] LaurentPolynomial k)
    (hns : ¬ Group.IsSolvable (WithConv (H →ₐ[k] k))) (htrans : UTrans l)
    (J : HopfIdeal k H) (hJ : HopfIdeal.IsBorelCandidate k (FiniteTypeCommHopfAlgCat.of k H) J)
    (hJP : J ≤ parabolicDefiningHopfIdeal l) :
    parabolicDefiningHopfIdeal l ≤ J := by
  obtain ⟨hsm, hgc, hgs⟩ := (HopfIdeal.isBorelCandidate_iff k (FiniteTypeCommHopfAlgCat.of k H) J).1 hJ
  haveI : Algebra.Smooth k (H ⧸ J.toIdeal) := hsm
  haveI : IsReduced (H ⧸ J.toIdeal) := isReduced_of_smooth k _
  set K := CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) J
    (CommAlgCat.of k k) with hKdef
  have hmemK : ∀ x : WithConv (H →ₐ[k] k), x ∈ K ↔ ∀ h ∈ J, x.ofConv h = 0 := by
    intro x
    first
    | exact CommHopfAlgCat.mem_quotientPointsSubgroup_iff (_root_.CommHopfAlgCat.of k H) J
        (CommAlgCat.of k k) x
    | (rw [hKdef]; exact CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ x)
    | simp [hKdef]
  have hmemP : ∀ x : WithConv (H →ₐ[k] k),
      x ∈ parabolic k l ↔ ∀ h ∈ parabolicDefiningHopfIdeal l, x.ofConv h = 0 := by
    intro x
    rw [← quotientPointsSubgroup_parabolicDefiningHopfIdeal (A := k) l,
      CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
  have hPK : parabolic k l ≤ K := fun x hx =>
    (hmemK x).2 fun h hh => (hmemP x).1 hx h (hJP hh)
  by_cases hex : ∃ u ∈ unipotent k l.oppositeCocharacter, u ∈ K ∧ u ≠ 1
  · exfalso
    obtain ⟨u, hu, huK, hu1⟩ := hex
    have hUK : unipotent k l.oppositeCocharacter ≤ K := by
      intro v hv
      by_cases hv1 : v = 1
      · rw [hv1]; exact K.one_mem
      obtain ⟨t, ht, rfl⟩ := htrans u hu v hv hu1 hv1
      exact K.mul_mem (K.mul_mem (hPK ht) huK) (K.inv_mem (hPK ht))
    have htop := points_eq_top l K hPK hUK
    apply hns
    have hsolvQ : Group.IsSolvable (WithConv ((FiniteTypeCommHopfAlgCat.quotient
        (FiniteTypeCommHopfAlgCat.of k H) J) →ₐ[k] k)) :=
      ((FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H)
        J).obj.isSolvable_points_iff_exists_derivedSeriesDefiningIdeal_eq_augmentation).mpr
        ((geometricallySolvablePointsCommHopfAlgProperty.iff_exists_derivedSeriesDefiningIdeal_eq_augmentation
          (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) J).obj).mp hgs)
    have hsurj : Function.Surjective
        (CommHopfAlgCat.quotientPointsHom (_root_.CommHopfAlgCat.of k H) J
          (CommAlgCat.of k k)).hom := by
      rw [← MonoidHom.range_eq_top]
      exact htop
    exact Group.isSolvable_of_surjective hsurj
  · push_neg at hex
    haveI : ConnectedSpace (PrimeSpectrum (H ⧸ J.toIdeal)) :=
      (geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace k _).1 hgc
    haveI : IrreducibleSpace (PrimeSpectrum (H ⧸ J.toIdeal)) :=
      OpenCellNotes.irreducibleSpace_of_connectedSpace k
    haveI : IrreducibleSpace (K : Set (WithConv (H →ₐ[k] k))) :=
      irreducibleSpace_points_of_quot J.toIdeal (K : Set (WithConv (H →ₐ[k] k))) fun x => by
        change x ∈ K ↔ _
        rw [hmemK]
        exact ⟨fun h y hy => RingHom.mem_ker.2 (h y (HopfIdeal.mem_toIdeal.1 hy)),
          fun h y hy => RingHom.mem_ker.1 (h (HopfIdeal.mem_toIdeal.2 hy))⟩
    have hKP := points_le_parabolic l K hPK fun v hv hvK => hex v hv hvK
    have hrad : J.toIdeal.IsRadical := (Ideal.isRadical_iff_quotient_reduced _).2 inferInstance
    have hle := le_of_forall_points hrad (I := (parabolicDefiningHopfIdeal l).toIdeal)
      fun x hx y hy => by
        have hxK : toConv x ∈ K := (hmemK _).2 fun h hh => by
          have := hx (HopfIdeal.mem_toIdeal.2 hh)
          rwa [RingHom.mem_ker] at this
        exact RingHom.mem_ker.2 ((hmemP _).1 (hKP hxK) y (HopfIdeal.mem_toIdeal.1 hy))
    exact HopfIdeal.toIdeal_le_toIdeal.mp hle

/-- **Transitivity from a `𝔾_a`-coordinate.** If `T ≤ P(λ)(k)` normalises `U(λ⁻¹)(k)` and acts on
an injective coordinate `e` (with `e v = 0 ↔ v = 1`) through a character `χ` hitting all of
`kˣ`, then `UTrans l` holds. This is the content of `RankOneTorusData` without the Weyl element. -/
theorem uTrans_of_coord (l : H →ₐc[k] LaurentPolynomial k)
    (T : Subgroup (WithConv (H →ₐ[k] k))) (hTP : T ≤ parabolic k l)
    (e χ : WithConv (H →ₐ[k] k) → k)
    (he0 : ∀ v ∈ unipotent k l.oppositeCocharacter, e v = 0 ↔ v = 1)
    (hinj : ∀ v ∈ unipotent k l.oppositeCocharacter, ∀ w ∈ unipotent k l.oppositeCocharacter,
      e v = e w → v = w)
    (hχ : ∀ c : k, c ≠ 0 → ∃ t ∈ T, χ t = c)
    (hact : ∀ t ∈ T, ∀ v ∈ unipotent k l.oppositeCocharacter, e (t * v * t⁻¹) = χ t * e v)
    (hTU : ∀ t ∈ T, ∀ v ∈ unipotent k l.oppositeCocharacter,
      t * v * t⁻¹ ∈ unipotent k l.oppositeCocharacter) :
    UTrans l := by
  intro u hu v hv hu1 hv1
  obtain ⟨t, ht, he⟩ := htrans_of_coordinate (unipotent k l.oppositeCocharacter) T e he0 hinj χ hχ
    hact hTU u hu v hv hu1 hv1
  exact ⟨t, hTP ht, he⟩

end Generic

/-! ### Specialisation to `Z = G^{ℤδ}` -/

section Levi

open R1Build R1Dis

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X)

local instance zDecRO (α : Additive X) : DecidableEq (ZAlg π α) := Classical.decEq _
local instance zSmoothRO [Algebra.FiniteType k H] [Algebra.Smooth k H] (α : Additive X) :
    Algebra.Smooth k (ZAlg π α) := smooth_quotient_magnetHopfIdeal π _

/-- **`BorelZMax` from T2 and `T`-transitivity** on `U_Z(λ⁻¹)(k) ∖ 1` and `U_Z(λ)(k) ∖ 1`, for
`G` smooth connected and `δ` a line generator. No reductivity hypothesis. -/
theorem borelZMax_of_trans [Algebra.FiniteType k H] [Algebra.Smooth k H]
    [ConnectedSpace (PrimeSpectrum H)] [Module.Free ℤ (Additive X)]
    (δ : Additive X) (hδ0 : δ ≠ 0)
    (hRay : ∀ β ∈ roots π, (∃ m n : ℤ, n ≠ 0 ∧ n • β = m • δ) → β ∈ lineMagnet δ)
    (ψ : X →* Multiplicative ℤ)
    (hns : ¬ Group.IsSolvable (WithConv (ZAlg π δ →ₐ[k] k)))
    (htrans : UTrans (zCochar π δ ψ)) (htrans' : UTrans (zCochar π δ ψ).oppositeCocharacter) :
    BorelZMax π δ ψ := by
  haveI : ConnectedSpace (PrimeSpectrum (ZAlg π δ)) := connectedSpace_lineAttractor π hδ0 hRay
  haveI : IrreducibleSpace (PrimeSpectrum (ZAlg π δ)) :=
    OpenCellNotes.irreducibleSpace_of_connectedSpace k
  exact ⟨fun J hJ hle => le_parabolic_of_isBorelCandidate _ hns htrans J hJ hle,
    fun J hJ hle => le_parabolic_of_isBorelCandidate _ hns htrans' J hJ hle⟩

end Levi

end AlgMag.Reductive.RankOneStructure

#print axioms AlgMag.Reductive.RankOneStructure.le_parabolic_of_isBorelCandidate
#print axioms AlgMag.Reductive.RankOneStructure.borelZMax_of_trans
#print axioms AlgMag.Reductive.RankOneStructure.uTrans_of_coord
