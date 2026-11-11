/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.LieCentralizer
import AlgMag.Reductive.PointsDensity
import AlgMag.Reductive.OpenCellEpi
import AlgMag.Reductive.OpenCell.OpenCellFlatness
import AlgMag.Reductive.OpenCellFlat
import AlgMag.Reductive.RegularConjugatesOpen
import AlgMag.Reductive.SubgroupFullLie
import AlgMag.Reductive.OpenCellLevi
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.RationalPoint
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Construction
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Reductive.Basic
import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Comap

/-!
# `hcell`: `U(-ν)(k) ∪ C(k) ∪ U(ν)(k)` generates `G(k)` (open cell dense, `G` connected)
-/

suppress_compilation

open Magnetism TauCeti TauCeti.Cocharacter WithConv

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X)

/-- **(H1)** `λ_{ψ⁻¹} = λ_ψ⁻¹`. -/
theorem cocharacter_inv (ψ : X →* Multiplicative ℤ) :
    π.cocharacter ψ⁻¹ = (π.cocharacter ψ).oppositeCocharacter := by
  have key : ∀ c : MonoidAlgebra k X,
      (BialgHom.id k (MonoidAlgebra k X)).cocharacter ψ⁻¹ c =
        LaurentPolynomial.invert ((BialgHom.id k (MonoidAlgebra k X)).cocharacter ψ c) := by
    intro c
    induction c using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]
    | single χ r =>
      rw [BialgHom.cocharacter_id_single, BialgHom.cocharacter_id_single]
      rw [LaurentPolynomial.single_eq_C_mul_T, LaurentPolynomial.single_eq_C_mul_T, map_mul,
        LaurentPolynomial.invert_C, LaurentPolynomial.invert_T]
      simp
  apply DFunLike.ext
  intro h
  rw [BialgHom.oppositeCocharacter_apply, ← BialgHom.cocharacter_id_comp π ψ⁻¹,
    ← BialgHom.cocharacter_id_comp π ψ, BialgHom.comp_apply, BialgHom.comp_apply, key]

section Cell

open scoped Zariski

variable {k' : Type u} {H' : Type u} [Field k'] [CommRing H'] [HopfAlgebra k' H']

omit [CommGroup X] [DecidableEq X] in
/-- Two `k`-points with the same kernel are equal. -/
lemma eq_of_ker_eq {x y : H' →ₐ[k'] k'} (h : RingHom.ker x = RingHom.ker y) : x = y := by
  ext a
  have hx : a - algebraMap k' H' (x a) ∈ RingHom.ker x := by
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes]; simp
  rw [h, RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero] at hx
  exact hx.symm

/-- **(H2)** `G(k)` is irreducible when `Spec H` is. -/
theorem irreducibleSpace_points_univ [IsAlgClosed k'] [Algebra.FiniteType k' H']
    [IrreducibleSpace (PrimeSpectrum H')] :
    IrreducibleSpace (Set.univ : Set (WithConv (H' →ₐ[k'] k'))) := by
  set K := (Set.univ : Set (WithConv (H' →ₐ[k'] k')))
  set S : Set (PrimeSpectrum H') := Set.range fun x : K => kerPt (x : WithConv (H' →ₐ[k'] k'))
  have hcl : closure S = Set.univ := by
    apply Set.eq_univ_of_forall
    intro p
    rw [← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    intro f hf
    have hJR : IsJacobsonRing H' := isJacobsonRing_of_finiteType (A := k')
    have hrad : (⊥ : Ideal H').radical.jacobson = (⊥ : Ideal H').radical :=
      IsJacobsonRing.out hJR (Ideal.radical_isRadical ⊥)
    have hfj : f ∈ (⊥ : Ideal H').radical.jacobson := by
      rw [Ideal.jacobson, Ideal.mem_sInf]
      rintro m ⟨_, hm⟩
      obtain ⟨φ, hφ⟩ := OpenCellNotes.exists_algHom_ker_eq (K := k') m
      have := (PrimeSpectrum.mem_vanishingIdeal _ _).1 hf _ ⟨⟨toConv φ, Set.mem_univ _⟩, rfl⟩
      rw [← hφ]; exact this
    rw [hrad] at hfj
    exact (Ideal.IsPrime.radical_le_iff p.isPrime).2 bot_le hfj
  have hSirr : IsIrreducible S := isIrreducible_iff_closure.1 (hcl ▸ IrreducibleSpace.isIrreducible_univ _)
  have : Nonempty K := by
    obtain ⟨_, ⟨x, rfl⟩⟩ := hSirr.nonempty
    exact ⟨x⟩
  exact irreducibleSpace_of_isInducing (f := fun x : K => kerPt (x : WithConv (H' →ₐ[k'] k')))
    (isInducing_kerPt.comp Topology.IsInducing.subtypeVal) hSirr.isPreirreducible

end Cell

/-- **(H4) `Z(ν) = C` for regular `ν`** (no root pairs to zero with `ψ`): `C ⊆ Z(ν)`, both
smooth, `Z(ν)` connected (open cell), equal Lie algebras `𝔤_0`. -/
theorem levi_magnet_eq_bot [IsAlgClosed k] [Algebra.FiniteType k H] [Algebra.Smooth k H]
    [Module.Finite k (Bialgebra.CotangentSpace k H)]
    [IrreducibleSpace (PrimeSpectrum H)] (ψ : X →* Multiplicative ℤ)
    (hψ : ∀ α ∈ roots π, pairingHom ψ α ≠ 0) :
    magnetHopfIdeal π ((⊥ : Magnet ℤ).comap (pairingHom ψ)) = magnetHopfIdeal π ⊥ := by
  set N := (⊥ : Magnet ℤ).comap (pairingHom ψ)
  have hle : magnetHopfIdeal π N ≤ magnetHopfIdeal π ⊥ := by
    rw [← HopfIdeal.toIdeal_le_toIdeal, magnetHopfIdeal_toIdeal, magnetHopfIdeal_toIdeal]
    exact magnetIdeal_anti _ bot_le
  haveI : Algebra.Smooth k (H ⧸ (magnetHopfIdeal π N).toIdeal) :=
    smooth_quotient_magnetHopfIdeal π N
  haveI : Algebra.Smooth k (H ⧸ (magnetHopfIdeal π ⊥).toIdeal) :=
    smooth_quotient_magnetHopfIdeal π ⊥
  haveI : ConnectedSpace (PrimeSpectrum (H ⧸ (magnetHopfIdeal π N).toIdeal)) := by
    rw [magnetHopfIdeal_toIdeal, magnetIdeal_torusGrading_comap_bot]
    exact connectedSpace_levi_of_openCell _ (isOpenEmbedding_openCell _)
  have hlie : ((magnetHopfIdeal π N).lieSubalgebra (B := k)).toSubmodule = rootSpace π 0 := by
    apply le_antisymm _ (rootSpace_zero_le_lieMagnet π N)
    intro d hd
    change d ∈ (magnetHopfIdeal π N).lieSubalgebra (B := k) at hd
    rw [mem_lieSubalgebra_magnetHopfIdeal_iff] at hd
    intro χ hχ h hh
    by_cases hN : χ ∈ N
    · by_contra hne
      have hW : χ ∈ tangentWeights π k := ⟨d, h, hh, hne⟩
      rcases tangentWeights_subset_insert_roots hW with h0 | hr
      · exact hχ h0
      · exact hψ χ hr hN
    · exact hd χ hN h hh
  refine (eq_of_le_of_finrank_cotangent_eq hle ?_)
  rw [OpenCellNotes.finrank_quotient_eq_lieSubalgebra, OpenCellNotes.finrank_quotient_eq_lieSubalgebra,
    hlie, rootSpace_zero_eq_lieBot]

/-- `Z(ν)(k) ⊆ C(k)` for regular `ν` (the hypothesis `hreg`). -/
theorem levi_le_attractor_bot [IsAlgClosed k] [Algebra.FiniteType k H] [Algebra.Smooth k H]
    [Module.Finite k (Bialgebra.CotangentSpace k H)]
    [IrreducibleSpace (PrimeSpectrum H)] (ψ : X →* Multiplicative ℤ)
    (hψ : ∀ α ∈ roots π, pairingHom ψ α ≠ 0) :
    ∀ z ∈ levi k (π.cocharacter ψ), z ∈ attractorSubgroup π ⊥ k := by
  intro z hz
  have h := quotientPointsSubgroup_leviDefiningHopfIdeal (π.cocharacter ψ) (CommAlgCat.of k k)
  change z ∈ levi (CommAlgCat.of k k) (π.cocharacter ψ) at hz
  rw [← h, CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at hz
  rw [mem_attractorSubgroup]
  have e := congrArg HopfIdeal.toIdeal (levi_magnet_eq_bot π ψ hψ)
  rw [magnetHopfIdeal_toIdeal, magnetHopfIdeal_toIdeal, magnetIdeal_torusGrading_comap_bot] at e
  rw [← e]
  intro y hy
  exact hz y (HopfIdeal.mem_toIdeal.1 hy)

open scoped Zariski in
/-- **`hcell`**: for `G` connected, `U(-ν)(k) ∪ Z(ν)(k) ∪ U(ν)(k)` generates `G(k)`; with
`Z(ν)(k) ⊆ C(k)` (regularity, `hreg`) the generators may be taken in `C(k)`. -/
theorem closure_openCell_eq_top [IsAlgClosed k] [Algebra.FiniteType k H] [Algebra.Smooth k H]
    [ConnectedSpace (PrimeSpectrum H)] (ψ : X →* Multiplicative ℤ)
    (hreg : ∀ z ∈ levi k (π.cocharacter ψ), z ∈ attractorSubgroup π ⊥ k) :
    Subgroup.closure (SetLike.coe (unipotent k (π.cocharacter ψ⁻¹)) ∪
      SetLike.coe (attractorSubgroup π ⊥ k) ∪ SetLike.coe (unipotent k (π.cocharacter ψ))) = ⊤ := by
  classical
  haveI : IrreducibleSpace (PrimeSpectrum H) := OpenCellNotes.irreducibleSpace_of_connectedSpace k
  set l := π.cocharacter ψ
  set S := Subgroup.closure (SetLike.coe (unipotent k (π.cocharacter ψ⁻¹)) ∪
      SetLike.coe (attractorSubgroup π ⊥ k) ∪ SetLike.coe (unipotent k l))
  set K := (Set.univ : Set (WithConv (H →ₐ[k] k)))
  haveI : IrreducibleSpace K := irreducibleSpace_points_univ
  let O : Set K := {x | kerPt (x : WithConv (H →ₐ[k] k)) ∈
    Set.range (PrimeSpectrum.comap (R := H) (S := OpenCellRing l) (openCellRingHom l))}
  have hemb := isOpenEmbedding_openCell l
  have hO : IsOpen O :=
    hemb.isOpen_range.preimage (isInducing_kerPt.continuous.comp continuous_subtype_val)
  have lift : ∀ (x : WithConv (H →ₐ[k] k)) (q : PrimeSpectrum (OpenCellRing l)),
      PrimeSpectrum.comap (R := H) (S := OpenCellRing l) (openCellRingHom l) q = kerPt x →
      q.asIdeal.IsMaximal → x ∈ S := by
    intro x q hq hqmax
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
    rw [← hx, toConv_comp_openCellMap]
    refine S.mul_mem (S.mul_mem (Subgroup.subset_closure (Or.inl (Or.inl ?_)))
      (Subgroup.subset_closure (Or.inl (Or.inr (hreg _ (openCellPoint₂_mem l f))))))
      (Subgroup.subset_closure (Or.inr (openCellPoint₃_mem l f)))
    rw [SetLike.mem_coe, cocharacter_inv]
    exact openCellPoint₁_mem l f
  have hmax : ∀ (x : WithConv (H →ₐ[k] k)) (q : PrimeSpectrum (OpenCellRing l)),
      PrimeSpectrum.comap (R := H) (S := OpenCellRing l) (openCellRingHom l) q = kerPt x →
      q.asIdeal.IsMaximal := by
    intro x q hq
    have hmaxx : (kerPt x).asIdeal.IsMaximal := RingHom.ker_isMaximal_of_surjective _
      (fun c => ⟨algebraMap k H c, by simp⟩)
    rw [← PrimeSpectrum.isClosed_singleton_iff_isMaximal]
    have hc : IsClosed ({kerPt x} : Set (PrimeSpectrum H)) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 hmaxx
    have := hc.preimage hemb.continuous
    convert this using 1
    ext q'
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact ⟨fun h => h ▸ hq, fun h => hemb.injective (h.trans hq.symm)⟩
  have hOS : ∀ x ∈ O, (x : WithConv (H →ₐ[k] k)) ∈ S := by
    intro x hx
    obtain ⟨q, hq⟩ := hx
    exact lift x q hq (hmax x q hq)
  have hOn : O.Nonempty := by
    haveI : Nontrivial (OpenCellRing l) :=
      (Bialgebra.counitAlgHom k (OCRing l)).toRingHom.domain_nontrivial
    obtain ⟨q⟩ : Nonempty (PrimeSpectrum (OpenCellRing l)) := inferInstance
    obtain ⟨m, hm, -⟩ := Ideal.exists_le_maximal q.asIdeal q.isPrime.ne_top
    obtain ⟨f, hf⟩ := OpenCellNotes.exists_algHom_ker_eq (K := k) (A := OpenCellRing l) m
    refine ⟨⟨toConv (f.comp (openCellMap l)), Set.mem_univ _⟩, ⟨m, hm.isPrime⟩, ?_⟩
    ext a
    change openCellMap l a ∈ m ↔ f (openCellMap l a) = 0
    rw [← hf]; rfl
  have := subset_of_isOpen_subset K (fun _ _ _ _ => Set.mem_univ _) (fun _ _ => Set.mem_univ _)
    S O hO hOn hOS
  exact eq_top_iff.2 fun g _ => this g (Set.mem_univ _)

section Final

variable {k' : Type u} {H' : Type u} [Field k'] [CommRing H'] [HopfAlgebra k' H']

omit [CommGroup X] [DecidableEq X] in
/-- **(F-a) points criterion.** Over `k̄`, a closed subgroup with reduced coordinate ring whose
`k`-points are stable under conjugation by `G(k)` is normal. -/
theorem isNormal_of_points [IsAlgClosed k'] [Algebra.FiniteType k' H'] [IsReduced H']
    (I : HopfIdeal k' H') [IsReduced (H' ⧸ I.toIdeal)]
    (hN : ∀ g c : WithConv (H' →ₐ[k'] k'), (∀ y ∈ I, c.ofConv y = 0) →
      ∀ y ∈ I, (g * c * g⁻¹).ofConv y = 0) : I.IsNormal := by
  apply HopfIdeal.isNormal_of_forall_le_conjugate
  intro g x hx
  rw [HopfIdeal.mem_conjugate, ← HopfIdeal.mem_toIdeal]
  have hrad : I.toIdeal.IsRadical := (Ideal.isRadical_iff_quotient_reduced _).2 inferInstance
  have hJR : IsJacobsonRing H' := isJacobsonRing_of_finiteType (A := k')
  have hjac : I.toIdeal.jacobson = I.toIdeal := IsJacobsonRing.out hJR hrad
  rw [← hjac, Ideal.jacobson, Ideal.mem_sInf]
  rintro m ⟨hIm, hm⟩
  obtain ⟨φ, hφ⟩ := OpenCellNotes.exists_algHom_ker_eq (K := k') m
  rw [← hφ, RingHom.mem_ker]
  set c : WithConv (H' →ₐ[k'] k') := toConv φ
  have hc : ∀ y ∈ I, c.ofConv y = 0 := fun y hy => by
    have : y ∈ m := hIm (HopfIdeal.mem_toIdeal.2 hy)
    rw [← hφ, RingHom.mem_ker] at this; exact this
  have hpoint := HopfAlgebra.comp_pointConjugationAlgHom g c
  rw [Algebra.ofId_self, AlgHom.mapValue_id, MonoidHom.id_apply] at hpoint
  have e : (g * c * g⁻¹).ofConv x = c.ofConv (HopfAlgebra.pointConjugationAlgHom g x) := by
    rw [← hpoint, WithConv.ofConv_toConv, AlgHom.comp_apply]
  have := hN g c hc x hx
  rw [e] at this
  exact this

omit [CommGroup X] [DecidableEq X] in
/-- **(F-b)** If `R_u(G) = 1` (reductivity over `k̄`: Tau Ceti
`reductiveCommHopfAlgProperty.unipotentRadicalDefiningIdeal_eq_augmentation`, in a module that
does not build in this repo yet), a unipotent-radical candidate is trivial. -/
theorem eq_augmentation_of_candidate [Algebra.FiniteType k' H']
    (hRu : FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal
      (FiniteTypeCommHopfAlgCat.of k' H') = HopfIdeal.augmentation k' _)
    (I : HopfIdeal k' (FiniteTypeCommHopfAlgCat.of k' H'))
    (hI : HopfIdeal.IsUnipotentRadicalCandidate (FiniteTypeCommHopfAlgCat.of k' H') I) :
    I = HopfIdeal.augmentation k' (FiniteTypeCommHopfAlgCat.of k' H') :=
  le_antisymm (HopfIdeal.le_augmentation k' _ I) (by
    rw [← hRu]
    exact FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_le _ I hI)

end Final

/-- **`hLie0` with the port-free facts discharged.** `C_u = V(Cu)` with reduced quotient. Remaining
named inputs: `hreg` (`Z(ν) = C`, regularity), `hcent` (steps 2–3), `hnormC` (C_u char. in C),
`hcand` (normal ⇒ candidate: `V(Cu)` smooth, connected, unipotent), `hRu` (`R_u(G) = 1`,
reductivity; Tau Ceti module not building yet), `hCT` (Borel port: `C_u = 1` ⇒ `C = T`). -/
theorem finrank_rootSpace_zero_le_of_Cu [IsAlgClosed k] [Algebra.FiniteType k H]
    [Algebra.Smooth k H] [Module.Finite k (Bialgebra.CotangentSpace k H)]
    [ConnectedSpace (PrimeSpectrum H)] (hπ : Function.Surjective π) (ψ : X →* Multiplicative ℤ)
    (hreg : ∀ z ∈ levi k (π.cocharacter ψ), z ∈ attractorSubgroup π ⊥ k)
    (Cu : HopfIdeal k H) [IsReduced (H ⧸ Cu.toIdeal)]
    (hcent : ∀ φ : X →* Multiplicative ℤ, (φ = ψ ∨ φ = ψ⁻¹) → ∀ α : PosRay φ,
      ∀ r ∈ rayPoints π φ α, ∀ c : WithConv (H →ₐ[k] k), (∀ y ∈ Cu, c.ofConv y = 0) →
        c * r = r * c)
    (hnormC : ∀ z ∈ attractorSubgroup π ⊥ k, ∀ c : WithConv (H →ₐ[k] k),
      (∀ y ∈ Cu, c.ofConv y = 0) → ∀ y ∈ Cu, (z * c * z⁻¹).ofConv y = 0)
    (hcand : Cu.IsNormal →
      HopfIdeal.IsUnipotentRadicalCandidate (FiniteTypeCommHopfAlgCat.of k H) Cu)
    (hRu : FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal
      (FiniteTypeCommHopfAlgCat.of k H) = HopfIdeal.augmentation k _)
    (hCT : Cu = HopfIdeal.augmentation k H →
      magnetHopfIdeal π ⊥ = HopfIdeal.kerOfSurjective π hπ) :
    Module.finrank k (rootSpace π 0) ≤
      Module.finrank k (Bialgebra.CotangentSpace k
        (H ⧸ (HopfIdeal.kerOfSurjective π hπ).toIdeal)) := by
  haveI : IsReduced H := TauCeti.isReduced_of_smooth k H
  set N := CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of k H) Cu (CommAlgCat.of k k)
  have hmem : ∀ g : WithConv (H →ₐ[k] k), g ∈ N ↔ ∀ y ∈ Cu, g.ofConv y = 0 := fun g =>
    CommHopfAlgCat.mem_quotientPointsSubgroup_iff (CommHopfAlgCat.of k H) Cu (CommAlgCat.of k k) g
  refine finrank_rootSpace_zero_le_of_centralizer π hπ ψ N
    (fun φ hφ α r hr c hc => hcent φ hφ α r hr c ((hmem c).1 hc))
    (fun z hz c hc => (hmem _).2 (hnormC z hz c ((hmem c).1 hc)))
    (closure_openCell_eq_top π ψ hreg) (fun hN => hCT ?_)
  have hnorm : Cu.IsNormal := isNormal_of_points Cu fun g c hc y hy =>
    (hmem _).1 (hN.conj_mem c ((hmem c).2 hc) g) y hy
  exact eq_augmentation_of_candidate hRu Cu (hcand hnorm)

section NormC

variable {k' : Type u} {Q : Type u} [Field k'] [CommRing Q] [HopfAlgebra k' Q]

omit [CommGroup X] [DecidableEq X] in
/-- Points killing a normal Hopf ideal are stable under conjugation (unbundled). -/
lemma conj_kills_of_isNormal (J : HopfIdeal k' Q) (hJ : J.IsNormal)
    (z c : WithConv (Q →ₐ[k'] k')) (hc : ∀ y ∈ J, c.ofConv y = 0) :
    ∀ y ∈ J, (z * c * z⁻¹).ofConv y = 0 := by
  intro x hx
  rw [← HopfAlgebra.productMap_comp_conjugationAlgHom (R := k') (H := Q) z c]
  have hker : Ideal.rightTensorIdeal (R := k') (A := Q) J.toIdeal ≤
      RingHom.ker (Algebra.TensorProduct.productMap z.ofConv c.ofConv).toRingHom := by
    rw [Ideal.rightTensorIdeal_le_iff]
    intro y hy
    rw [Ideal.mem_comap, RingHom.mem_ker]
    simpa using hc y ((HopfIdeal.mem_toIdeal (I := J)).mp hy)
  exact RingHom.mem_ker.mp (hker (hJ.conjugation_mem hx))

end NormC

omit [CommGroup X] [DecidableEq X] in
/-- **`hnormC` from normality in `C`** (unbundled): if `J` is a normal Hopf ideal of `H ⧸ C` and
`C_u = V(J)` in `G`, then `C(k)` normalises `C_u(k)`. With `J = R_u(C)` (normal by
`isUnipotentRadicalCandidate_unipotentRadicalDefiningIdeal`) this is `hnormC`. -/
theorem normC_of_normal (C : HopfIdeal k H) (J : HopfIdeal k (H ⧸ C.toIdeal)) (hJ : J.IsNormal)
    (z : WithConv (H →ₐ[k] k)) (hz : ∀ y ∈ C, z.ofConv y = 0)
    (c : WithConv (H →ₐ[k] k))
    (hc : ∀ y : H, Ideal.Quotient.mk C.toIdeal y ∈ J → c.ofConv y = 0) :
    ∀ y : H, Ideal.Quotient.mk C.toIdeal y ∈ J → (z * c * z⁻¹).ofConv y = 0 := by
  let mk := Bialgebra.Quotient.mkBialgHom (R := k) C.toIdeal
  have hCle : ∀ y ∈ C, Ideal.Quotient.mk C.toIdeal y ∈ J := fun y hy => by
    have : Ideal.Quotient.mk C.toIdeal y = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (HopfIdeal.mem_toIdeal.2 hy)
    rw [this]; exact J.toIdeal.zero_mem
  let lift : ∀ v : WithConv (H →ₐ[k] k), (∀ y ∈ C, v.ofConv y = 0) →
      WithConv ((H ⧸ C.toIdeal) →ₐ[k] k) := fun v hv =>
    toConv (Ideal.Quotient.liftₐ _ v.ofConv fun a ha => hv a (HopfIdeal.mem_toIdeal.1 ha))
  have hlift : ∀ v hv, BialgHom.mapDomain mk (lift v hv) = v := by
    intro v hv
    apply WithConv.ofConv_injective
    rw [BialgHom.mapDomain_apply, WithConv.ofConv_toConv]
    exact AlgHom.ext fun x => by
      simp only [lift, AlgHom.comp_apply]
      rfl
  have hcC : ∀ y ∈ C, c.ofConv y = 0 := fun y hy => hc y (hCle y hy)
  have hcQ : ∀ j ∈ J, (lift c hcC).ofConv j = 0 := by
    intro j hj
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective j
    exact hc y hj
  have hconj := conj_kills_of_isNormal J hJ (lift z hz) (lift c hcC) hcQ
  intro y hy
  have e : z * c * z⁻¹ = BialgHom.mapDomain mk (lift z hz * lift c hcC * (lift z hz)⁻¹) := by
    rw [map_mul, map_mul, map_inv, hlift, hlift]
  rw [e, BialgHom.mapDomain_apply, WithConv.ofConv_toConv, AlgHom.comp_apply]
  exact hconj _ hy

/-- **`hLie0` for reductive `G`, regular `ν`.** `hreg` from `levi_le_attractor_bot`, `hRu` from
reductivity (Tau Ceti). Remaining named inputs: `hcent`, `hnormC` (see `normC_of_normal`), `hcand`,
`hCT`. -/
theorem finrank_rootSpace_zero_le_of_reductive [IsAlgClosed k] [Algebra.FiniteType k H]
    [Algebra.Smooth k H] [Module.Finite k (Bialgebra.CotangentSpace k H)]
    [ConnectedSpace (PrimeSpectrum H)] (hπ : Function.Surjective π) (ψ : X →* Multiplicative ℤ)
    (hψ : ∀ α ∈ roots π, pairingHom ψ α ≠ 0)
    (hred : reductiveCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.of k H))
    (Cu : HopfIdeal k H) [IsReduced (H ⧸ Cu.toIdeal)]
    (hcent : ∀ φ : X →* Multiplicative ℤ, (φ = ψ ∨ φ = ψ⁻¹) → ∀ α : PosRay φ,
      ∀ r ∈ rayPoints π φ α, ∀ c : WithConv (H →ₐ[k] k), (∀ y ∈ Cu, c.ofConv y = 0) →
        c * r = r * c)
    (hnormC : ∀ z ∈ attractorSubgroup π ⊥ k, ∀ c : WithConv (H →ₐ[k] k),
      (∀ y ∈ Cu, c.ofConv y = 0) → ∀ y ∈ Cu, (z * c * z⁻¹).ofConv y = 0)
    (hcand : Cu.IsNormal →
      HopfIdeal.IsUnipotentRadicalCandidate (FiniteTypeCommHopfAlgCat.of k H) Cu)
    (hCT : Cu = HopfIdeal.augmentation k H →
      magnetHopfIdeal π ⊥ = HopfIdeal.kerOfSurjective π hπ) :
    Module.finrank k (rootSpace π 0) ≤
      Module.finrank k (Bialgebra.CotangentSpace k
        (H ⧸ (HopfIdeal.kerOfSurjective π hπ).toIdeal)) := by
  haveI : IrreducibleSpace (PrimeSpectrum H) := OpenCellNotes.irreducibleSpace_of_connectedSpace k
  exact finrank_rootSpace_zero_le_of_Cu π hπ ψ (levi_le_attractor_bot π ψ hψ) Cu hcent hnormC
    hcand hred.unipotentRadicalDefiningIdeal_eq_augmentation hCT

section Ru

variable [Algebra.FiniteType k H]

/-- `R_u(C)` for `C = G^0`, as a Hopf ideal of `H ⧸ C`. -/
noncomputable abbrev RuC : HopfIdeal k (H ⧸ (magnetHopfIdeal π ⊥).toIdeal) :=
  FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal
    (FiniteTypeCommHopfAlgCat.of k (H ⧸ (magnetHopfIdeal π ⊥).toIdeal))

lemma RuC_isNormal : (RuC π).IsNormal :=
  (FiniteTypeCommHopfAlgCat.isUnipotentRadicalCandidate_unipotentRadicalDefiningIdeal _).1

/-- `C_u ⊆ G`: the pullback of `R_u(C)`. -/
noncomputable def CuIdeal : HopfIdeal k H :=
  (RuC π).comap (Bialgebra.Quotient.mkBialgHom (R := k) (magnetHopfIdeal π ⊥).toIdeal)

lemma mem_CuIdeal {y : H} :
    y ∈ CuIdeal π ↔ Ideal.Quotient.mk (magnetHopfIdeal π ⊥).toIdeal y ∈ RuC π :=
  HopfIdeal.mem_comap

/-- **`hnormC` for `C_u`.** -/
theorem hnormC_CuIdeal : ∀ z ∈ attractorSubgroup π ⊥ k, ∀ c : WithConv (H →ₐ[k] k),
    (∀ y ∈ CuIdeal π, c.ofConv y = 0) → ∀ y ∈ CuIdeal π, (z * c * z⁻¹).ofConv y = 0 := by
  intro z hz c hc y hy
  have hz' : ∀ y ∈ magnetHopfIdeal π ⊥, z.ofConv y = 0 := by
    intro y hy
    rw [mem_attractorSubgroup] at hz
    exact hz (by rw [← magnetHopfIdeal_toIdeal]; exact HopfIdeal.mem_toIdeal.2 hy)
  exact normC_of_normal (magnetHopfIdeal π ⊥) (RuC π) (RuC_isNormal π) z hz' c
    (fun y hy => hc y ((mem_CuIdeal π).2 hy)) y ((mem_CuIdeal π).1 hy)

end Ru

end AlgMag.Reductive
