/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.CuUnipotent
import AlgMag.Reductive.RootGroupGaLie
import AlgMag.Reductive.GradedNakayamaBigraded
import AlgMag.Reductive.SmoothKrullDim
import AlgMag.Reductive.ConverseCore
import AlgMag.Reductive.OpenCell.CotangentTensor

/-!
# `hGa` from T4 (`rayDim ≤ 1`)

`O(U_(α)) = H/J_U` is smooth, graded by the weights with positive `⟨·,φ⟩` off degree `0` and
`O_0 = k`; graded Nakayama gives `O ≅ k[x_1, …, x_r]` on homogeneous `x_i`. The `r` derivations
`∂/∂x_i` at `e` lie in `Lie U_(α)`, and `Lie U_(α) ⊆ ⊕_{β root, β ∈ ℕ_{>0}α} 𝔤_β`, of dimension
`≤ rayDim`. So `r ≤ 1`: either `U_(α)` is trivial (`r = 0`) or `O = k[ȳ]`, `y ∈ H_γ` (`r = 1`).
-/

suppress_compilation

open Magnetism TauCeti WithConv AlgMag.Sec12Printed DirectSum
open scoped TensorProduct

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X)

local notation "τ" => TauCeti.Bialgebra.CounitAlgebra.algEquivSelf

lemma derivation_sum_apply {ι : Type*} (s : Finset ι)
    (g : ι → Derivation k H (TauCeti.Bialgebra.CounitAlgebra k H k)) (h : H) :
    (∑ i ∈ s, g i) h = ∑ i ∈ s, g i h := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih => rw [Finset.sum_insert has, Finset.sum_insert has, Derivation.add_apply, ih]

omit [DecidableEq X] in
lemma der_eq_zero_of_homog (d : Derivation k H (TauCeti.Bialgebra.CounitAlgebra k H k))
    (hd : ∀ χ : Additive X, ∀ x ∈ torusGrading π χ, d x = 0) : d = 0 := by
  classical
  ext x
  induction x using induction_torusGrading (π := π) with
  | h0 => simp
  | hadd a b ha hb => simp only [map_add, ha, hb, Derivation.zero_apply, add_zero]
  | hmem χ a ha => simp [hd χ a ha]

variable [Module.Finite k (Bialgebra.CotangentSpace k H)]

lemma iSup_rootSpace_eq_top : (⨆ α : Additive X, rootSpace π α) = ⊤ := by
  have htop := DirectSum.IsInternal.submodule_iSup_eq_top (dec_ι := Classical.decEq X)
    (Derivation.isInternal_adjointWeightSpace π)
  simp_rw [rootSpace_eq_map_adjointWeightSpace]
  rw [← Submodule.map_iSup,
    Additive.toMul.surjective.iSup_comp (fun x => Derivation.adjointWeightSpace π x), htop,
    Submodule.map_top, LinearEquiv.range]

open scoped Classical in
/-- **`Lie U_(α) ⊆ ⊕ 𝔤_β`**, `β` roots in `ℕ_{>0} α`. -/
theorem mem_biSup_rootSpace_of_mem_lie (α : Additive X) (hα : ∀ n : ℕ, n • α = 0 → n = 0)
    (d : Derivation k H (TauCeti.Bialgebra.CounitAlgebra k H k))
    (hd : d ∈ (rootGroupIdeal π α hα).lieSubalgebra (B := k)) :
    d ∈ ⨆ β ∈ (finite_roots (π := π)).toFinset.filter (fun β => ∃ n : ℕ, 0 < n ∧ β = n • α),
      rootSpace π β := by
  rw [mem_lieSubalgebra_rootGroupIdeal_iff_ray π α hα d] at hd
  have hmem : d ∈ ⨆ χ, rootSpace π χ := by rw [iSup_rootSpace_eq_top]; trivial
  obtain ⟨f, hf, hfd⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hmem
  have heval : ∀ χ : Additive X, ∀ h ∈ torusGrading π χ, d h = f χ h := by
    intro χ h hh
    rw [← hfd, Finsupp.sum, derivation_sum_apply]
    by_cases hχ : χ ∈ f.support
    · rw [Finset.sum_eq_single χ]
      · intro ψ _ hψ; exact hf ψ χ (Ne.symm hψ) h hh
      · intro h'; exact absurd hχ h'
    · rw [Finsupp.notMem_support_iff.1 hχ]
      refine Finset.sum_eq_zero fun ψ hψ => ?_
      exact hf ψ χ (fun e => hχ (e ▸ hψ)) h hh
  rw [← hfd, Finsupp.sum]
  refine Submodule.sum_mem _ fun χ _ => ?_
  by_cases hχ : ∃ n : ℕ, 0 < n ∧ χ = n • α
  · by_cases h0 : f χ = 0
    · rw [h0]; exact Submodule.zero_mem _
    have hχ0 : χ ≠ 0 := by
      obtain ⟨n, hn, rfl⟩ := hχ
      intro e; have := hα n e; omega
    have hr : χ ∈ roots π := mem_roots_of_mem_rootSpace π hχ0 (hf χ) h0
    refine Submodule.mem_iSup_of_mem χ (Submodule.mem_iSup_of_mem ?_ (hf χ))
    rw [Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨hr, hχ⟩
  · have : f χ = 0 := der_eq_zero_of_homog π _ (fun ν x hx => by
      by_cases hν : ν = χ
      · subst hν
        rw [← heval _ x hx]
        exact hd ν (fun n hn e => hχ ⟨n, hn, e⟩) x hx
      · exact hf χ ν hν x hx)
    rw [this]; exact Submodule.zero_mem _

open scoped Classical in
/-- **`dim Lie U_(α) ≤ rayDim`.** -/
theorem finrank_lie_le_rayDim (φ : X →* Multiplicative ℤ) (α : PosRay φ) :
    Module.finrank k ((rootGroupIdeal π α.1 (PosRay.torsionFree φ α)).lieSubalgebra
      (B := k)).toSubmodule ≤ rayDim π (pairingHom φ) α.1 := by
  set t := (finite_roots (π := π)).toFinset.filter (fun β => ∃ n : ℕ, 0 < n ∧ β = n • α.1)
  calc Module.finrank k ((rootGroupIdeal π α.1 (PosRay.torsionFree φ α)).lieSubalgebra
          (B := k)).toSubmodule
      ≤ Module.finrank k (⨆ β ∈ t, rootSpace π β : Submodule k _) :=
        Submodule.finrank_mono fun d hd =>
          mem_biSup_rootSpace_of_mem_lie π α.1 (PosRay.torsionFree φ α) d hd
    _ = ∑ β ∈ t, Module.finrank k (rootSpace π β) := finrank_biSup_rootSpace π t
    _ = ∑ β ∈ t, Module.finrank k (Derivation.adjointWeightSpace π (Additive.toMul β)) :=
        Finset.sum_congr rfl fun β _ => finrank_rootSpace_eq_finrank_adjointWeightSpace β
    _ ≤ rayDim π (pairingHom φ) α.1 := by
        unfold rayDim
        apply Finset.sum_le_sum_of_subset
        intro β hβ
        rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hβ
        obtain ⟨hr, n, hn, rfl⟩ := hβ
        rw [Finset.mem_filter]
        refine ⟨?_, ⟨1, n, one_pos, hn, one_smul _ _⟩⟩
        unfold posRoots
        rw [Finset.mem_filter, Set.Finite.mem_toFinset]
        refine ⟨hr, ?_⟩
        rw [map_nsmul, nsmul_eq_mul]
        exact mul_pos (by exact_mod_cast hn) α.2

/-- **`r ≤ dim Lie U_(α)`** for `O(U_(α)) ≅ k[x_1, …, x_r]` with `ε(x_i) = 0`. -/
theorem card_le_finrank_lie (α : Additive X) (hα : ∀ n : ℕ, n • α = 0 → n = 0) {r : ℕ}
    (x : Fin r → H ⧸ JU π α) (hx0 : ∀ i, counitO π α (x i) = 0)
    (hbij : Function.Bijective (MvPolynomial.aeval (R := k) x)) :
    r ≤ Module.finrank k ((rootGroupIdeal π α hα).lieSubalgebra (B := k)).toSubmodule := by
  classical
  set L := ((rootGroupIdeal π α hα).lieSubalgebra (B := k)).toSubmodule
  have hI : (rootGroupIdeal π α hα).toIdeal = JU π α := by
    rw [rootGroupIdeal, prescribedUnitHopfIdeal_toIdeal]
  let e : MvPolynomial (Fin r) k ≃ₐ[k] (H ⧸ JU π α) := AlgEquiv.ofBijective _ hbij
  have hcc0 : (MvPolynomial.aeval (0 : Fin r → k)) =
      (counitO π α).comp (MvPolynomial.aeval (R := k) x) :=
    MvPolynomial.algHom_ext fun i => by simp [hx0]
  have hcc : ∀ b, MvPolynomial.aeval (0 : Fin r → k) (e.symm b) = counitO π α b := by
    intro b
    obtain ⟨p, rfl⟩ := e.surjective b
    rw [AlgEquiv.symm_apply_apply, hcc0]
    rfl
  let q := Ideal.Quotient.mkₐ k (JU π α)
  let f : Fin r → H →ₗ[k] k := fun i =>
    (MvPolynomial.aeval (0 : Fin r → k)).toLinearMap ∘ₗ (MvPolynomial.pderiv i).toLinearMap ∘ₗ
      e.symm.toLinearMap ∘ₗ q.toLinearMap
  have hf : ∀ i a, f i a = MvPolynomial.aeval (0 : Fin r → k)
      (MvPolynomial.pderiv i (e.symm (Ideal.Quotient.mk (JU π α) a))) := fun _ _ => rfl
  have hleib : ∀ i a b, f i (a * b) = Coalgebra.counit (R := k) a * f i b +
      Coalgebra.counit (R := k) b * f i a := by
    intro i a b
    rw [hf, hf, hf, map_mul, map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add,
      map_mul, map_mul, hcc, hcc, counitO_mk, counitO_mk]
  let D : Fin r → Derivation k H (TauCeti.Bialgebra.CounitAlgebra k H k) := fun i =>
    OpenCellNotes.mkPt (f i) (hleib i)
  have hDf : ∀ i a, τ k H k (D i a) = f i a := fun _ _ => rfl
  have hDL : ∀ i, D i ∈ L := by
    intro i
    change D i ∈ (rootGroupIdeal π α hα).lieSubalgebra (B := k)
    rw [HopfIdeal.mem_lieSubalgebra_iff]
    intro z hz
    have hz' : z ∈ JU π α := hI ▸ hz
    apply (τ k H k).injective
    rw [hDf, map_zero, hf, Ideal.Quotient.eq_zero_iff_mem.2 hz', map_zero, map_zero, map_zero]
  choose y hy using fun j => Ideal.Quotient.mk_surjective (I := JU π α) (x j)
  have hfy : ∀ i j, f i (y j) = if i = j then 1 else 0 := by
    intro i j
    rw [hf, hy]
    have : e.symm (x j) = MvPolynomial.X j := by
      apply e.injective
      rw [AlgEquiv.apply_symm_apply]
      simp [e]
    rw [this, MvPolynomial.pderiv_X]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Pi.single_apply, Ne.symm hij, hij]
  let v : Fin r → L := fun i => ⟨D i, hDL i⟩
  have hli : LinearIndependent k v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have h1 := congrArg (fun w : L => τ k H k ((w : Derivation k H _) (y j))) hc
    simp only [Submodule.coe_sum, Submodule.coe_smul, ZeroMemClass.coe_zero] at h1
    rw [derivation_sum_apply, map_sum, Derivation.zero_apply, map_zero] at h1
    have hterm : ∀ i, τ k H k ((c i • (v i : Derivation k H (TauCeti.Bialgebra.CounitAlgebra k H k))) (y j)) =
        c i * f i (y j) :=
      fun i => by rw [← hDf]; rfl
    have h2 : ∑ i, c i * f i (y j) = 0 := by
      convert h1 using 2 with i
      exact (hterm i).symm
    simpa [hfy] using h2
  have := hli.fintype_card_le_finrank
  simpa using this

variable [Algebra.FiniteType k H] [Algebra.Smooth k H]

/-- **`hGa` from T4.** For `α` on the positive side of `φ` with `rayDim ≤ 1`, either `U_(α)` is
trivial or `O(U_(α)) = k[ȳ]` with `y ∈ H_γ`, `⟨γ, φ⟩ ≠ 0`. -/
theorem hGa_of_rayDim (φ : X →* Multiplicative ℤ) (α : PosRay φ)
    (hray : rayDim π (pairingHom φ) α.1 ≤ 1) :
    (∀ r ∈ rayPoints π φ α, r = 1) ∨ ∃ γ : Additive X, pairingHom φ γ ≠ 0 ∧
      ∃ y ∈ torusGrading π γ, Function.Bijective (Polynomial.aeval (R := k)
        (Ideal.Quotient.mk (rootGroupIdeal π α.1 (PosRay.torsionFree φ α)).toIdeal y)) := by
  classical
  set hα := PosRay.torsionFree φ α
  have hI : (rootGroupIdeal π α.1 hα).toIdeal = JU π α.1 := by
    rw [rootGroupIdeal, prescribedUnitHopfIdeal_toIdeal]
  letI := quotGradedAlgebra (isHomogeneousIdeal_JU (π := π) hα)
  haveI : Algebra.Smooth k (H ⧸ JU π α.1) := by
    have := smooth_rootGroupIdeal π φ α; rwa [hI] at this
  haveI : Algebra.FiniteType k (H ⧸ JU π α.1) :=
    Algebra.FiniteType.trans (S := H) inferInstance inferInstance
  haveI : Nontrivial (H ⧸ JU π α.1) := nontrivial_of_ne 0 1 fun h => by
    have := congrArg (counitO π α.1) h
    rw [map_zero, map_one] at this
    exact zero_ne_one this
  have hpos : GradedNakayamaBigraded.Pos (gradO π α.1) (pairingHom φ) 1 := by
    intro y b hb hb0 hy0
    have hyR : y ∈ rayMagnet α.1 := by
      by_contra h; exact hb0 (eq_zero_of_mem_gradO h hb)
    obtain ⟨m, rfl⟩ := AddSubmonoid.mem_closure_singleton.1 hyR
    have hm : m ≠ 0 := by rintro rfl; exact hy0 (zero_smul _ _)
    rw [map_nsmul, nsmul_eq_mul]
    have h1 : (1 : ℤ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hm
    have h2 : (1 : ℤ) ≤ pairingHom φ α.1 := α.2
    exact ⟨by nlinarith, by push_cast; nlinarith⟩
  have h0 : gradO π α.1 0 = LinearMap.range (Algebra.linearMap k (H ⧸ JU π α.1)) := by
    ext b
    constructor
    · intro hb
      exact ⟨counitO π α.1 b, (eq_algebraMap_of_mem_gradO_zero hb).symm⟩
    · rintro ⟨c, rfl⟩
      have := mk_mem_gradO (π := π) (α := α.1) (SetLike.algebraMap_mem_graded (torusGrading π) c)
      simpa using this
  obtain ⟨r, x, μ, hxμ, hbij⟩ :=
    GradedNakayamaBigraded.exists_mvPolynomial_equiv_of_graded_smooth_weight hpos h0
  have hμ0 : ∀ i, μ i ≠ 0 := fun i e => by
    have := (hxμ i).1; rw [e, map_zero] at this; exact lt_irrefl _ this
  have hx0 : ∀ i, counitO π α.1 (x i) = 0 := fun i =>
    counitO_eq_zero_of_mem (hμ0 i) (hxμ i).2.2
  have hr : r ≤ 1 :=
    ((card_le_finrank_lie π α.1 hα x hx0 hbij).trans (finrank_lie_le_rayDim π φ α)).trans hray
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hr with rfl | rfl
  · left
    intro p hp
    apply WithConv.ofConv_injective
    ext h
    obtain ⟨P, hP⟩ := hbij.2 (Ideal.Quotient.mk (JU π α.1) h)
    rw [P.eq_C_of_isEmpty, MvPolynomial.aeval_C] at hP
    set c := P.coeff 0
    have hd : h - algebraMap k H c ∈ JU π α.1 := by
      rw [← Ideal.Quotient.eq, ← hP]; rfl
    have hp' : ∀ z ∈ JU π α.1, p.ofConv z = 0 := fun z hz => hp (hI ▸ hz)
    have e1 : p.ofConv h = c := by
      have := hp' _ hd; rw [map_sub, AlgHom.commutes, sub_eq_zero] at this; exact this
    have e2 : Coalgebra.counit (R := k) h = c := by
      have := congrArg (counitO π α.1) hP
      rw [counitO_mk, AlgHom.commutes] at this
      exact this.symm
    rw [e1, AlgHom.convOne_apply, e2]
    rfl
  · right
    refine ⟨μ 0, ne_of_gt (hxμ 0).1, ?_⟩
    obtain ⟨y, hy, hyx⟩ := (hxμ 0).2.2
    refine ⟨y, hy, ?_⟩
    suffices key : Function.Bijective (Polynomial.aeval (R := k)
        (Ideal.Quotient.mkₐ k (JU π α.1) y)) by
      first | exact key | exact hI ▸ key
    rw [Ideal.Quotient.mkₐ_eq_mk, show Ideal.Quotient.mk (JU π α.1) y = x 0 from hyx]
    let ι : Polynomial k →ₐ[k] MvPolynomial (Fin 1) k := Polynomial.aeval (MvPolynomial.X 0)
    let κ : MvPolynomial (Fin 1) k →ₐ[k] Polynomial k := MvPolynomial.aeval fun _ => Polynomial.X
    have hcomp : (MvPolynomial.aeval (R := k) x).comp ι = Polynomial.aeval (x 0) :=
      Polynomial.algHom_ext (by simp [ι])
    have hκι : κ.comp ι = AlgHom.id k _ := Polynomial.algHom_ext (by simp [ι, κ])
    have hικ : ι.comp κ = AlgHom.id k _ := MvPolynomial.algHom_ext fun i => by
      rw [Subsingleton.elim i 0]; simp [ι, κ]
    have hιb : Function.Bijective ι := Function.bijective_iff_has_inverse.2
      ⟨κ, fun p => AlgHom.congr_fun hκι p, fun p => AlgHom.congr_fun hικ p⟩
    rw [← hcomp, AlgHom.coe_comp]
    exact hbij.comp hιb

/-- **`hcent` for `C_u` from T4** (`rayDim ≤ 1` on the rays of `±ψ`). -/
theorem hcent_CuIdeal_of_rayDim [IsAlgClosed k] {ψ : X →* Multiplicative ℤ}
    (hray : ∀ φ : X →* Multiplicative ℤ, (φ = ψ ∨ φ = ψ⁻¹) → ∀ α : PosRay φ,
      rayDim π (pairingHom φ) α.1 ≤ 1) :
    ∀ φ : X →* Multiplicative ℤ, (φ = ψ ∨ φ = ψ⁻¹) → ∀ α : PosRay φ,
      ∀ r ∈ rayPoints π φ α, ∀ c : WithConv (H →ₐ[k] k), (∀ y ∈ CuIdeal π, c.ofConv y = 0) →
        c * r = r * c :=
  hcent_CuIdeal' π fun φ hφ α => hGa_of_rayDim π φ α (hray φ hφ α)

end AlgMag.Reductive
