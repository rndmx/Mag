/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.RootSpaceDimAlt
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Basic
import AlgMag.Weyl.WeylGroup
import AlgMag.Reductive.FromR1R2

/-!
# A root group whose Lie algebra meets a homogeneous subgroup lies in it

Let `J` cut out a closed subgroup `U_α ≅ G_a` of `G`: `J` is homogeneous for the torus grading,
contained in the augmentation ideal, and `H ⧸ J = k[ȳ]` for some `y ∈ H_α` (`α` of infinite
order). Let `I` be a homogeneous ideal contained in the augmentation ideal, with `H ⧸ (I ⊔ J)`
reduced, and suppose some nonzero tangent vector `d` at `e` vanishes on `I` and on `J`. Then
`I ≤ J`, i.e. `U_α ⊆ V(I)`.

Proof: a homogeneous `f ∈ I` of weight `χ` maps to `c ȳⁿ` in `k[ȳ]` with `nα = χ`; if `c ≠ 0`
and `n ≥ 1`, then `ȳ` is nilpotent mod `I ⊔ J`, hence `y ∈ I ⊔ J` (reduced), hence `d y = 0`
and `d = 0` (`H = k[y] + J`); if `n = 0`, the counit gives `c = 0`.

This is step "𝔤_α ⊆ Lie U ⇒ U_α ⊆ U" of equivalence.tex Theorem 5.1.
-/

open Magnetism TauCeti WithConv
open scoped TensorProduct

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable {π : H →ₐc[k] MonoidAlgebra k X} {α : Additive X}

section RootGroupInNormal

variable (hα : ∀ n : ℕ, n • α = 0 → n = 0)
variable {J : Ideal H} (hJ : J.IsHomogeneous (torusGrading π))
variable (hJε : ∀ x ∈ J, Coalgebra.counit (R := k) x = 0)
variable {y : H} (hy : y ∈ torusGrading π α)
variable (hφ : Function.Bijective (Polynomial.aeval (R := k) (Ideal.Quotient.mk J y)))
variable {I : Ideal H} (hI : I.IsHomogeneous (torusGrading π))
variable (hIε : ∀ x ∈ I, Coalgebra.counit (R := k) x = 0)

omit [DecidableEq X] in
include hφ in
/-- If a tangent vector vanishes on `J` and on `y`, it vanishes (`H = k[y] + J`). -/
lemma derivation_eq_zero_of_root
    (d : Derivation k H (Bialgebra.CounitAlgebra k H k)) (hdJ : ∀ x ∈ J, d x = 0)
    (hdy : d y = 0) : d = 0 := by
  ext h
  obtain ⟨p, hp⟩ := hφ.2 (Ideal.Quotient.mk J h)
  have hmk : Ideal.Quotient.mk J (Polynomial.aeval y p) = Ideal.Quotient.mk J h := by
    rw [← hp, ← Ideal.Quotient.mkₐ_eq_mk k, Polynomial.aeval_algHom_apply]
  have hg : h - Polynomial.aeval y p ∈ J := by
    rw [← Ideal.Quotient.eq]; exact hmk.symm
  have hpoly : d (Polynomial.aeval y p) = 0 := by
    rw [Polynomial.aeval_eq_sum_range, map_sum]
    refine Finset.sum_eq_zero fun n _ => ?_
    rw [Derivation.map_smul, Derivation.leibniz_pow, hdy]
    simp
  have := hdJ _ hg
  rw [map_sub, hpoly, sub_zero] at this
  rw [this]
  rfl

include hα hJ hJε hy hφ hIε in
/-- A homogeneous element of `I` maps to `0` in `H ⧸ J`, unless `y ∈ I ⊔ J`. -/
lemma mk_eq_zero_of_homogeneous [IsReduced (H ⧸ (I ⊔ J))] (hyIJ : y ∉ I ⊔ J)
    {χ : Additive X} {f : H} (hf : f ∈ torusGrading π χ) (hfI : f ∈ I) :
    Ideal.Quotient.mk J f = 0 := by
  obtain ⟨p, hp⟩ := hφ.2 (Ideal.Quotient.mk J f)
  have hmk : Ideal.Quotient.mk J (Polynomial.aeval y p) = Ideal.Quotient.mk J f := by
    rw [← hp, ← Ideal.Quotient.mkₐ_eq_mk k, Polynomial.aeval_algHom_apply]
  have hg : f - Polynomial.aeval y p ∈ J := by
    rw [← Ideal.Quotient.eq]; exact hmk.symm
  -- the weight-`nα` component of `aeval y p` is `p.coeff n • yⁿ`
  have hproj : ∀ n : ℕ, GradedAlgebra.proj (torusGrading π) (n • α) (Polynomial.aeval y p) =
      p.coeff n • y ^ n := by
    intro n
    rw [Polynomial.aeval_eq_sum_range, map_sum]
    rw [Finset.sum_eq_single n]
    · rw [map_smul, GradedAlgebra.proj_apply,
        DirectSum.decompose_of_mem_same _ (SetLike.pow_mem_graded n hy)]
    · intro m _ hmn
      rw [map_smul, GradedAlgebra.proj_apply,
        DirectSum.decompose_of_mem_ne _ (SetLike.pow_mem_graded m hy)
          (fun h => hmn (nsmul_injective_of hα h)), smul_zero]
    · intro hn
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa using hn), zero_smul, map_zero]
  -- coefficients away from `χ` vanish
  have hcoeff : ∀ n : ℕ, n • α ≠ χ → p.coeff n = 0 := by
    intro n hn
    have hJn : GradedAlgebra.proj (torusGrading π) (n • α) (f - Polynomial.aeval y p) ∈ J := by
      rw [GradedAlgebra.proj_apply]; exact hJ (n • α) hg
    rw [map_sub, hproj, GradedAlgebra.proj_apply,
      DirectSum.decompose_of_mem_ne _ hf (Ne.symm hn), zero_sub, neg_mem_iff] at hJn
    have h0 : Polynomial.aeval (Ideal.Quotient.mk J y) (Polynomial.C (p.coeff n) *
        Polynomial.X ^ n) = 0 := by
      rw [← Ideal.Quotient.mkₐ_eq_mk k, Polynomial.aeval_algHom_apply,
        Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      simpa [Polynomial.aeval_def, Algebra.smul_def] using hJn
    have := hφ.1 (h0.trans (map_zero _).symm)
    simpa using congrArg (fun q => Polynomial.coeff q n) this
  by_cases hex : ∃ n : ℕ, n • α = χ
  · obtain ⟨n0, hn0⟩ := hex
    have hpC : p = Polynomial.C (p.coeff n0) * Polynomial.X ^ n0 := by
      ext m
      rw [Polynomial.coeff_C_mul_X_pow]
      split_ifs with hm
      · rw [hm]
      · exact hcoeff m (fun h => hm (nsmul_injective_of hα (h.trans hn0.symm)))
    set c := p.coeff n0
    have hfc : f - c • y ^ n0 ∈ J := by
      have : Polynomial.aeval y p = c • y ^ n0 := by
        rw [hpC]; simp [Algebra.smul_def]
      rw [← this]; exact hg
    rcases Nat.eq_zero_or_pos n0 with h0 | hpos
    · -- weight zero: the counit forces `c = 0`
      subst h0
      have hε := hJε _ hfc
      rw [map_sub, hIε f hfI, pow_zero, map_smul, Bialgebra.counit_one, smul_eq_mul,
        mul_one, zero_sub, neg_eq_zero] at hε
      rw [← hmk, hpC]
      simp [hε]
    · by_cases hc : c = 0
      · rw [← hmk, hpC, hc]; simp
      · exfalso
        apply hyIJ
        have hmem : c • y ^ n0 ∈ I ⊔ J := by
          have : c • y ^ n0 = f - (f - c • y ^ n0) := by ring
          rw [this]
          exact sub_mem (Ideal.mem_sup_left hfI) (Ideal.mem_sup_right hfc)
        have hmem' : y ^ n0 ∈ I ⊔ J := by
          have := Submodule.smul_mem (I ⊔ J) (algebraMap k H c⁻¹) hmem
          rwa [smul_eq_mul, ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hc, one_smul] at this
        have hnil : IsNilpotent (Ideal.Quotient.mk (I ⊔ J) y) :=
          ⟨n0, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact hmem'⟩
        rw [← Ideal.Quotient.eq_zero_iff_mem]
        exact hnil.eq_zero
  · push Not at hex
    have hp0 : p = 0 := by
      ext m; rw [hcoeff m (hex m), Polynomial.coeff_zero]
    rw [← hp, hp0, map_zero]

include hα hJ hJε hy hφ hI hIε in
/-- **`U_α ⊆ V(I)`** when a nonzero tangent vector vanishes on `I` and on `J`. -/
theorem le_of_root_group [IsReduced (H ⧸ (I ⊔ J))]
    (d : Derivation k H (Bialgebra.CounitAlgebra k H k)) (hdI : ∀ x ∈ I, d x = 0)
    (hdJ : ∀ x ∈ J, d x = 0) (hd : d ≠ 0) : I ≤ J := by
  classical
  have hyIJ : y ∉ I ⊔ J := by
    intro hyIJ
    apply hd
    refine derivation_eq_zero_of_root hφ d hdJ ?_
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hyIJ
    rw [← hab, map_add, hdI a ha, hdJ b hb, add_zero]
  intro f hf
  rw [← DirectSum.sum_support_decompose (torusGrading π) f]
  refine Ideal.sum_mem _ fun χ _ => ?_
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact mk_eq_zero_of_homogeneous hα hJ hJε hy hφ hIε hyIJ (SetLike.coe_mem _) (hI χ hf)

end RootGroupInNormal

section PrescribedUnit

variable (π) in
omit [DecidableEq X] in
/-- The weight-`0` part of `J_⊥` (the ideal of `G^0`) lies in `J_N` for every pointed magnet. -/
lemma proj_zero_mem_magnetIdeal [DecidableEq X] {N : Magnet (Additive X)}
    (hN : ∀ a ∈ N, ∀ b ∈ N, a + b = 0 → a = 0) {b : H}
    (hb : b ∈ magnetIdeal (torusGrading π) ⊥) :
    (DirectSum.decompose (torusGrading π) b 0 : H) ∈ magnetIdeal (torusGrading π) N := by
  suffices key : ∀ r : H,
      (DirectSum.decompose (torusGrading π) (r * b) 0 : H) ∈ magnetIdeal (torusGrading π) N by
    simpa using key 1
  rw [magnetIdeal] at hb
  refine Submodule.span_induction (p := fun x _ => ∀ r : H,
      (DirectSum.decompose (torusGrading π) (r * x) 0 : H) ∈ magnetIdeal (torusGrading π) N)
    ?_ ?_ ?_ ?_ hb
  · intro x hx r
    obtain ⟨χ, hχ, hx⟩ := Set.mem_iUnion₂.mp hx
    have hχ0 : χ ≠ 0 := fun h => hχ (h ▸ (⊥ : Magnet (Additive X)).zero_mem)
    have e : (DirectSum.decompose (torusGrading π) (r * x) 0 : H) =
        (DirectSum.decompose (torusGrading π) r (-χ) : H) * x := by
      rw [← DirectSum.coe_decompose_mul_add_of_right_mem (torusGrading π) (i := -χ) hx,
        neg_add_cancel]
    rw [e]
    by_cases hχN : χ ∈ N
    · have hnχ : -χ ∉ N := fun h => hχ0 (hN χ hχN (-χ) h (add_neg_cancel χ))
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_iUnion₂.mpr
        ⟨-χ, hnχ, SetLike.coe_mem _⟩))
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_iUnion₂.mpr ⟨χ, hχN, hx⟩))
  · intro r; simp
  · intro x y _ _ hx hy r
    rw [mul_add, DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add]
    exact add_mem (hx r) (hy r)
  · intro a x _ hx r
    rw [smul_eq_mul, ← mul_assoc]
    exact hx (r * a)

variable (π) in
omit [DecidableEq X] in
/-- **`V(I) ∩ G^N_e = V(I) ∩ G^N` when `V(I) ∩ G^0 = e`**: if `x - ε(x) ∈ I ⊔ J_⊥` for all
`x ∈ H_0`, and `I` is homogeneous, then `I ⊔ (equations of G^N_e) = I ⊔ J_N`. -/
theorem sup_prescribedUnitIdeal_eq [DecidableEq X] {N : Magnet (Additive X)}
    (hN : ∀ a ∈ N, ∀ b ∈ N, a + b = 0 → a = 0) {I : Ideal H}
    (hI : I.IsHomogeneous (torusGrading π))
    (h0 : ∀ x ∈ torusGrading π 0,
      x - algebraMap k H (Coalgebra.counit (R := k) x) ∈ I ⊔ magnetIdeal (torusGrading π) ⊥) :
    I ⊔ prescribedUnitIdeal π N = I ⊔ magnetIdeal (torusGrading π) N := by
  apply le_antisymm
  · refine sup_le le_sup_left (sup_le le_sup_right ?_)
    rw [Ideal.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have hz0 : x - algebraMap k H (Coalgebra.counit (R := k) x) ∈ torusGrading π 0 := by
      refine sub_mem hx ?_
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ SetLike.GradedOne.one_mem
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (h0 x hx)
    have e : x - algebraMap k H (Coalgebra.counit (R := k) x) =
        (DirectSum.decompose (torusGrading π) a 0 : H) +
          (DirectSum.decompose (torusGrading π) b 0 : H) := by
      rw [← Submodule.coe_add, ← DirectSum.add_apply, ← DirectSum.decompose_add, hab,
        DirectSum.decompose_of_mem_same _ hz0]
    rw [SetLike.mem_coe, e]
    exact add_mem (Ideal.mem_sup_left (hI 0 ha))
      (Ideal.mem_sup_right (proj_zero_mem_magnetIdeal π hN hb))
  · exact sup_le_sup_left le_sup_left _

end PrescribedUnit

section NormalizingInNormal

open AlgMag.Weyl

variable (π) in
omit [DecidableEq X] in
/-- **Step 5 core (points).** Let `U = V(I)` be a normal subgroup with `U ∩ T = e` (on points over
`k ⊗ k[X]`). A `k`-point `v ∈ U(k)` normalizing `T` acts trivially on `X`.

Proof: `t v t⁻¹ = v · (σ⁻¹/id)(t)` (`orbitHom_normalizing`), so `(σ⁻¹/id)(t) = v⁻¹ (t v t⁻¹)` lies
in `U ∩ T = e`; evaluating at a preimage of `χ` gives `σ⁻¹ χ = χ`. -/
theorem eq_one_of_isNormalizingWith_of_mem (hπ : Function.Surjective π) {I : HopfIdeal k H}
    (hI : I.IsNormal)
    (hUT : ∀ g : WithConv (H →ₐ[k] k ⊗[k] MonoidAlgebra k X), (∀ h ∈ I, g.ofConv h = 0) →
      (∀ h ∈ RingHom.ker π.toAlgHom, g.ofConv h = 0) → g = 1)
    {v : WithConv (H →ₐ[k] k)} (hv : ∀ h ∈ I, v.ofConv h = 0) {σ : X ≃* X}
    (hn : IsNormalizingWith π k v σ) : σ = 1 := by
  set B := k ⊗[k] MonoidAlgebra k X
  set gg : WithConv (H →ₐ[k] B) := AlgHom.mapValue
    (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := k) (B := MonoidAlgebra k X)) v
  set ρ : X →* X := σ.symm.toMonoidHom / MonoidHom.id X
  set S := CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of k H) I (CommAlgCat.of k B)
  have hmem : ∀ g : WithConv (H →ₐ[k] B), g ∈ S ↔ ∀ h ∈ I, g.ofConv h = 0 := fun g =>
    CommHopfAlgCat.mem_quotientPointsSubgroup_iff (CommHopfAlgCat.of k H) I (CommAlgCat.of k B) g
  have hnorm : S.Normal :=
    CommHopfAlgCat.quotientPointsSubgroup_normal (CommHopfAlgCat.of k H) I hI (CommAlgCat.of k B)
  have hgg : gg ∈ S := by
    rw [hmem]
    intro h hh
    simp [gg, AlgHom.mapValue_apply, hv h hh]
  have ho := orbitHom_normalizing π hn
  have hconj : torusPoint π k * gg * (torusPoint π k)⁻¹ ∈ S := hnorm.conj_mem gg hgg _
  have htw : twistPoint π k ρ = gg⁻¹ * (torusPoint π k * gg * (torusPoint π k)⁻¹) := by
    have : orbitHom π k v = torusPoint π k * gg * (torusPoint π k)⁻¹ := rfl
    rw [← this, ho]
    exact (inv_mul_cancel_left gg _).symm
  have htwS : twistPoint π k ρ ∈ S := by
    rw [htw]; exact S.mul_mem (S.inv_mem hgg) hconj
  have htw1 : twistPoint π k ρ = 1 := by
    refine hUT _ ((hmem _).1 htwS) fun h hh => ?_
    rw [RingHom.mem_ker] at hh
    have hh' : π h = 0 := hh
    simp [twistPoint, hh']
  apply MulEquiv.ext
  intro χ
  obtain ⟨h, hh⟩ := hπ (MonoidAlgebra.single χ 1)
  have hval := congrArg (fun g : WithConv (H →ₐ[k] B) => g.ofConv h) htw1
  have hε : Coalgebra.counit (R := k) h = 1 := by
    rw [← CoalgHomClass.counit_comp_apply π h, hh, MonoidAlgebra.counit_single]
    simp
  simp only [twistPoint, ofConv_toConv, AlgHom.comp_apply, AlgHom.convOne_apply, hε,
    map_one] at hval
  have hh' : π.toAlgHom h = MonoidAlgebra.single χ 1 := hh
  rw [hh', MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_single] at hval
  have hval' : MonoidAlgebra.single (ρ χ) (1 : k) = MonoidAlgebra.single 1 1 := by
    have hinj := Algebra.TensorProduct.includeRight_injective (R := k) (A := k)
      (B := MonoidAlgebra k X) (algebraMap k k).injective
    apply hinj
    rw [hval, ← MonoidAlgebra.one_def, map_one]
  have hρ : ρ χ = 1 := MonoidAlgebra.single_left_injective one_ne_zero hval'
  have : σ.symm χ = χ := by
    have hρχ : ρ χ = σ.symm χ / χ := rfl
    rw [hρχ, div_eq_one] at hρ
    exact hρ
  simpa using (congrArg σ this).symm

end NormalizingInNormal

section LieTransport

open AlgMag.Weyl

variable (π) in
omit [DecidableEq X] in
/-- **Root spaces of a normal subgroup are permuted by `N_G(T)`.** If `d ∈ Lie V(I) ∩ 𝔤_α`,
`d ≠ 0`, `I` normal and `n` normalizes `T` with `σ`, then `Lie V(I) ∩ 𝔤_{σα} ≠ 0`. -/
theorem exists_lie_rootSpace_conj [DecidableEq X] {I : HopfIdeal k H} (hI : I.IsNormal)
    {n : WithConv (H →ₐ[k] k)} {σ : X ≃* X} (hn : IsNormalizingWith π k n σ)
    {α : Additive X} {d : Derivation k H (Bialgebra.CounitAlgebra k H k)}
    (hdI : ∀ x ∈ I.toIdeal, d x = 0) (hdα : d ∈ rootSpace π α) (hd0 : d ≠ 0) :
    ∃ d' : Derivation k H (Bialgebra.CounitAlgebra k H k), (∀ x ∈ I.toIdeal, d' x = 0) ∧
      d' ∈ rootSpace π (Additive.ofMul (σ (Additive.toMul α))) ∧ d' ≠ 0 := by
  have hinv := hn.inv π
  refine ⟨derivationComp (HopfAlgebra.pointConjugationBialgEquiv n⁻¹ : H →ₐc[k] H) d,
    fun x hx => ?_, fun χ hχ h hh => ?_, fun h0 => hd0 ?_⟩
  · rw [derivationComp_apply, HopfAlgebra.pointConjugationBialgEquiv_toAlgHom]
    exact hdI _ (HopfIdeal.mem_conjugate.1 (hI.le_conjugate n⁻¹ (HopfIdeal.mem_toIdeal.2 hx)))
  · rw [derivationComp_apply, HopfAlgebra.pointConjugationBialgEquiv_toAlgHom]
    refine hdα _ ?_ _ (pointConjugation_mem_torusGrading π hinv hh)
    intro he
    apply hχ
    have : σ⁻¹ (Additive.toMul χ) = Additive.toMul α := by
      have := congrArg Additive.toMul he
      simpa using this
    rw [← this]
    simp
  · ext h
    have hc : HopfAlgebra.pointConjugationAlgHom n⁻¹ (HopfAlgebra.pointConjugationAlgHom n h) = h := by
      have := AlgHom.congr_fun (HopfAlgebra.pointConjugationAlgHom_mul n n⁻¹) h
      simpa using this.symm
    have := congrArg (fun D : Derivation k H (Bialgebra.CounitAlgebra k H k) =>
      D (HopfAlgebra.pointConjugationAlgHom n h)) h0
    simp only [derivationComp_apply, HopfAlgebra.pointConjugationBialgEquiv_toAlgHom, hc] at this
    rw [this]
    rfl

end LieTransport

end AlgMag.Reductive
