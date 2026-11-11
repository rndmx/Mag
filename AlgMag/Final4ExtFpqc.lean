/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Prop337General
import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Subcanonical
import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.SheafConditionAffine
import AlgMag.Sec8Representability

/-!
# Every point of `D(Z)` extends fpqc locally to `D(M)`, for any abelian group `M`

Used for Proposition 3.35 (Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026)) without
finite generation: `D(M) → D(Z)` is faithfully flat and affine (`ℤ[M]` is free over `ℤ[Z]`), so the
sieve of extensions is fpqc covering, and a scheme is an fpqc sheaf (subcanonicity).
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Cardinal
universe u

namespace AlgMag.Final4Ext

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
local notation "SCH" => BigFppfOver.toScheme B S hS
attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

variable {M : Type u} [AddCommGroup M] [hM : Fact (#M < B.cutoff)]

lemma contains_AZ : B.Contains (GB.AZ M) := by
  refine P337.contains_iff.2 ?_
  have ha := B.aleph0_lt_cutoff
  have e : #(AddMonoidAlgebra ℤ M) ≤ #(Finset (M × ULift.{u} ℤ)) := by
    classical
    refine mk_le_of_injective (f := fun x : AddMonoidAlgebra ℤ M =>
      (Finsupp.graph x.coeff).map (Function.Embedding.prodMap (Function.Embedding.refl M)
        ⟨ULift.up, ULift.up_injective⟩)) ?_
    intro x y h
    refine AddMonoidAlgebra.coeff_injective (Finsupp.graph_injective M ℤ ?_)
    exact Finset.map_injective _ h
  refine e.trans_lt ?_
  by_cases hf : Finite (M × ULift.{u} ℤ)
  · exact (lt_aleph0_of_finite _).trans ha
  · have : Infinite (M × ULift.{u} ℤ) := not_finite_iff_infinite.1 hf
    rw [mk_finset_of_infinite, mk_prod, lift_id, lift_id]
    refine mul_lt_of_lt ha.le hM.out ?_
    rw [mk_uLift, mk_int, lift_aleph0]
    exact ha

/-- A flat surjective quasi-compact morphism is an fpqc family with one member. -/
lemma ofArrows_unit_mem_fpqc' {Z T : Scheme.{u}} (q : Z ⟶ T) (hf : Flat q) (hs : Surjective q)
    (hq : QuasiCompact q) :
    Presieve.ofArrows (fun _ : Unit => Z) (fun _ => q) ∈ Scheme.fpqcPrecoverage T := by
  have hcov : ∀ x : T, ∃ i : Unit, x ∈ Set.range q := fun x => ⟨(), q.surjective x⟩
  let 𝒰 : T.Cover (Scheme.precoverage @Flat) :=
    Scheme.Cover.mkOfCovers Unit (fun _ => Z) (fun _ => q) hcov (fun _ => hf)
  have := Scheme.jointlySurjective_precoverage_flat
  have hfin : Finite 𝒰.I₀ := inferInstanceAs (Finite Unit)
  have hc : ∀ i, QuasiCompact (𝒰.f i) := fun _ => hq
  have hqc : QuasiCompactCover 𝒰.toPreZeroHypercover := QuasiCompactCover.of_finite
  exact ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.2 hqc,
    (Scheme.ofArrows_mem_precoverage_iff _).2 ⟨hcov, fun _ => hf⟩⟩

/-- **Proposition 3.35, the covering step, for any abelian group `M`**: a scheme `U` satisfies the
sheaf condition for every pullback of the sieve of extensions of a point of `D(Z)` to `D(M)`. -/
theorem isSheafFor_extSieve (U : BigFppfOver B S hS) (Z : AddSubgroup M) {T T' : BigFppfOver B S hS}
    (a : APt (fppfO B S hS) Z.toAddSubmonoid (op T)) (r : T' ⟶ T) :
    Presieve.IsSheafFor (yoneda.obj U) ((extSieve (fppfO B S hS) Z a).pullback r).arrows := by
  let φ := Z.toAddSubmonoid.subtype
  let a' := APt.res r.op a
  let f : (SCH).obj T' ⟶ GB.AZ Z.toAddSubmonoid := (GB.ptsZ _).symm a'
  let W : Scheme.{u} := pullback f (GB.AZmap φ)
  have hW : B.Contains W := lt_of_le_of_lt (Scheme.size_pullback_le _ _)
    (max_lt T'.left.2 contains_AZ)
  let T'' : BigFppfOver B S hS := siteObject B S hS hW (pullback.fst f (GB.AZmap φ) ≫ structMap T')
  let q : T'' ⟶ T' := Over.homMk (ObjectProperty.homMk (pullback.fst f (GB.AZmap φ))) rfl
  have hfl : Flat (GB.AZmap φ) := GB.flat_AZmap φ (flat_of_isFreeAlong ℤ (isFreeAlong_subtype Z))
  have hsu : Surjective (GB.AZmap φ) := ⟨comap_mapDomain_surjective Z ℤ⟩
  have hqf : Flat ((SCH).map q) := inferInstanceAs (Flat (pullback.fst f (GB.AZmap φ)))
  have hqs : Surjective ((SCH).map q) := inferInstanceAs (Surjective (pullback.fst f (GB.AZmap φ)))
  have hqq : QuasiCompact ((SCH).map q) := inferInstanceAs (QuasiCompact (pullback.fst f (GB.AZmap φ)))
  have hR : Presieve.ofArrows (fun _ : Unit => T'') (fun _ => q) ∈
      Scheme.fpqcPrecoverage.comap (SCH) T' := by
    rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows]
    exact ofArrows_unit_mem_fpqc' _ hqf hqs hqq
  have hsh := BigFppfOver.isSheaf_fpqc_yoneda_obj B S hS U
  rw [isSheaf_iff_isSheaf_of_type,
    Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange] at hsh
  have hle : Sieve.generate (Presieve.ofArrows (fun _ : Unit => T'') (fun _ => q)) ≤
      Sieve.generate ((extSieve (fppfO B S hS) Z a).pullback r).arrows := by
    rw [Sieve.generate_sieve, Sieve.generate_le_iff]
    rintro _ _ ⟨⟩
    refine ⟨GB.ptsZ _ (pullback.snd f (GB.AZmap φ)), ?_⟩
    have e := GB.ptsZ_AZmap φ (pullback.snd f (GB.AZmap φ))
    rw [← pullback.condition, GB.ptsZ_comp] at e
    have hf : GB.ptsZ _ f = a' := (GB.ptsZ _).apply_symm_apply a'
    rw [hf] at e
    rw [op_comp, APt.res_comp]
    exact e.symm
  exact (isAlgebraicSpace_yoneda B S hS U).isSheafFor_fpqc_of_isSheafFor_refinement hR hle (hsh _ hR)

end AlgMag.Final4Ext
