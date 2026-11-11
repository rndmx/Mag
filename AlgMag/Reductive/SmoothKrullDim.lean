/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.RootSpaceDim
import AlgMag.Reductive.ParabolicGenRay
import AlgMag.Reductive.RankOneDim
import AlgMag.Reductive.SmoothKrullDimCore
import TauCeti.AlgebraicGeometry.AugmentationPoint.ClosedPoints
import AlgMag.Reductive.OpenCell.LieDimension

/-!
# The field `hdim` of `RayDimData`: (D3) + smoothness

* `ringKrullDim_augmentationStalk_eq_finrank_lie`: for a smooth affine group `U` of finite type
  over `k = k̄`, `dim 𝒪_{U,1} = dim_k Lie U` (regular local ring at the identity).
* `sum_rootSpace_ray_le_finrank_lie_rootGroup` ((D3), lower bound): the root spaces `𝔤_β` on the
  ray of `α` lie in `Lie U_(α)` and are independent, so `rayDim ≤ dim Lie U_(α)`, provided every
  `f`-positive root on the ray of `α` is a positive multiple of `α`.
* `hdim_rootGroup`: the conclusion of `RayDimData.hdim` for `U = k[U_(α)]`, `one = 1`.
-/

suppress_compilation

open AlgebraicGeometry CategoryTheory Magnetism TauCeti WithConv

namespace AlgMag.Reductive

universe u



variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X) [Module.Finite k (Bialgebra.CotangentSpace k H)]

/-- The root spaces are independent. -/
lemma iSupIndep_rootSpace : iSupIndep (rootSpace π) := by
  have hind := (Derivation.isInternal_adjointWeightSpace π).submodule_iSupIndep
    (dec_ι := Classical.decEq X)
  have h2 := (hind.map_orderIso (Submodule.orderIsoMapComap
    (Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k)))).comp
      (Additive.toMul (α := X)).injective
  convert h2 using 1
  funext α
  exact rootSpace_eq_map_adjointWeightSpace (π := π) α

lemma finrank_biSup_rootSpace (t : Finset (Additive X)) :
    Module.finrank k (⨆ i ∈ t, rootSpace π i : Submodule k _) =
      ∑ i ∈ t, Module.finrank k (rootSpace π i) := by
  classical
  have hind := iSupIndep_rootSpace π
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t hat ih =>
    rw [Finset.iSup_insert, Finset.sum_insert hat, ← ih]
    have hdis : Disjoint (rootSpace π a) (⨆ i ∈ t, rootSpace π i) := by
      have := hind.disjoint_biSup (y := (t : Set (Additive X))) (x := a) hat
      simpa only [Finset.mem_coe] using this
    have h := Submodule.finrank_sup_add_finrank_inf_eq (rootSpace π a) (⨆ i ∈ t, rootSpace π i)
    rw [disjoint_iff.1 hdis, finrank_bot, add_zero] at h
    exact h

/-- **(D3), lower bound**: for a finset `t` of positive multiples of `α`,
`∑_{β ∈ t} dim 𝔤_β ≤ dim Lie U_(α)`. With `t` the `f`-positive roots on the ray of `α`
(when these are multiples of `α`), the left side is `rayDim π f α` (RankOneDim.lean). -/
theorem sum_finrank_le_finrank_lie_rootGroup (α : Additive X)
    (hα : ∀ n : ℕ, n • α = 0 → n = 0) (t : Finset (Additive X))
    (hprim : ∀ β ∈ t, ∃ n : ℕ, 0 < n ∧ β = n • α) :
    (∑ β ∈ t, Module.finrank k (Derivation.adjointWeightSpace π (Additive.toMul β))) ≤
      Module.finrank k (Derivation k (H ⧸ (rootGroupIdeal π α hα).toIdeal)
        (Bialgebra.CounitAlgebra k (H ⧸ (rootGroupIdeal π α hα).toIdeal) k)) := by
  rw [Derivation.finrank_eq_finrank_cotangentSpace,
    OpenCellNotes.finrank_quotient_eq_lieSubalgebra]
  have e : (∑ β ∈ t, Module.finrank k (Derivation.adjointWeightSpace π (Additive.toMul β))) =
      ∑ β ∈ t, Module.finrank k (rootSpace π β) :=
    Finset.sum_congr rfl fun β _ => (finrank_rootSpace_eq_finrank_adjointWeightSpace (π := π) β).symm
  rw [e, ← finrank_biSup_rootSpace π t]
  apply Submodule.finrank_mono
  refine iSup₂_le fun β hβ d hd => ?_
  obtain ⟨n, hn, rfl⟩ := hprim β hβ
  change d ∈ (rootGroupIdeal π α hα).lieSubalgebra (B := k)
  rw [mem_lieSubalgebra_rootGroupIdeal_iff_ray π α hα d]
  intro χ hχ h hh
  exact hd χ (hχ n hn) h hh

open scoped Classical in
/-- **The field `hdim` of `RayDimData`** for `U = k[U_(α)]` and `one` the identity point.
`hprim`: `α` is primitive on its ray (every `f`-positive root on the ray is a multiple of `α`).
The hypothesis `2 ≤ ∑ …` is `2 ≤ rayDim π (pairingHom ψ) α.1` by definition (RankOneDim.lean). -/
theorem hdim_rootGroup [IsAlgClosed k] [Algebra.FiniteType k H] [Algebra.Smooth k H]
    (ψ : X →* Multiplicative ℤ) (α : PosRay ψ)
    (hprim : ∀ β ∈ posRoots π (pairingHom ψ), SameRayRel β α.1 →
      ∃ n : ℕ, 0 < n ∧ β = n • α.1) :
    2 ≤ (∑ β ∈ (posRoots π (pairingHom ψ)).filter (fun β => SameRayRel β α.1),
      Module.finrank k (Derivation.adjointWeightSpace π (Additive.toMul β))) →
      ¬ Ring.KrullDimLE 1
        ((Spec (CommRingCat.of
          (H ⧸ (rootGroupIdeal π α.1 (PosRay.torsionFree ψ α)).toIdeal))).presheaf.stalk
          (Bialgebra.augmentationPoint k
            (H ⧸ (rootGroupIdeal π α.1 (PosRay.torsionFree ψ α)).toIdeal))) := by
  intro h2
  haveI := smooth_rootGroupIdeal π ψ α
  haveI : Algebra.FiniteType k (H ⧸ (rootGroupIdeal π α.1 (PosRay.torsionFree ψ α)).toIdeal) :=
    Algebra.FiniteType.trans (S := H) inferInstance inferInstance
  exact not_krullDimLE_one_of_two_le_finrank_lie (k := k)
    (h2.trans (sum_finrank_le_finrank_lie_rootGroup π α.1 _ _
      fun β hβ => hprim β (Finset.mem_filter.1 hβ).1 (Finset.mem_filter.1 hβ).2))

/-! ### `α` primitive on its ray, and `RayDimData` up to `hAff` -/

section RayGenerator

variable {X : Type u} [CommGroup X] [IsMulTorsionFree X]

omit [IsMulTorsionFree X] in
lemma exists_common_generator_coprime (γ β : Additive X) (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hco : Nat.Coprime m n) (h : m • β = n • γ) :
    ∃ δ : Additive X, γ = m • δ ∧ β = n • δ := by
  set u := Int.gcdA m n
  set v := Int.gcdB m n
  have hb : (1 : ℤ) = m * u + n * v := by
    have := Int.gcd_eq_gcd_ab (m : ℤ) n
    rw [Int.gcd_natCast_natCast, hco] at this
    exact_mod_cast this
  have h' : (m : ℤ) • β = (n : ℤ) • γ := by rw [natCast_zsmul, natCast_zsmul]; exact h
  refine ⟨v • β + u • γ, ?_, ?_⟩
  · rw [← natCast_zsmul, smul_add, smul_smul, smul_smul, mul_comm (m : ℤ) v, ← smul_smul v, h',
      smul_smul, ← add_smul, show v * n + m * u = 1 by linear_combination -hb, one_smul]
  · rw [← natCast_zsmul, smul_add, smul_smul, smul_smul, mul_comm (n : ℤ) u, ← smul_smul u, ← h',
      smul_smul, ← add_smul, show n * v + u * m = 1 by linear_combination -hb, one_smul]

lemma exists_common_generator (γ β : Additive X) (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (h : m • β = n • γ) :
    ∃ δ : Additive X, ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ γ = a • δ ∧ β = b • δ := by
  set d := Nat.gcd m n
  have hd : 0 < d := Nat.gcd_pos_of_pos_left _ hm
  set m' := m / d
  set n' := n / d
  have hm' : m = d * m' := (Nat.mul_div_cancel' (Nat.gcd_dvd_left m n)).symm
  have hn' : n = d * n' := (Nat.mul_div_cancel' (Nat.gcd_dvd_right m n)).symm
  have hm0 : 0 < m' := Nat.div_pos (Nat.gcd_le_left n hm) hd
  have hn0 : 0 < n' := Nat.div_pos (Nat.le_of_dvd hn (Nat.gcd_dvd_right m n)) hd
  have hco : Nat.Coprime m' n' := Nat.coprime_div_gcd_div_gcd hd
  have h' : m' • β = n' • γ := by
    apply nsmul_right_injective (M := Additive X) hd.ne'
    simp only [smul_smul]
    rw [← hm', ← hn']
    exact h
  obtain ⟨δ, h1, h2⟩ := exists_common_generator_coprime γ β m' n' hm0 hn0 hco h'
  exact ⟨δ, m', n', hm0, hn0, h1, h2⟩

/-- **Rays are cyclic.** A finite set of elements on the ray of `α` (with `⟨α, λ⟩ > 0`) consists of
positive multiples of a single `δ` with `⟨δ, λ⟩ > 0`. -/
theorem exists_ray_generator (ψ : X →* Multiplicative ℤ) (α : Additive X)
    (hα : 0 < pairingHom ψ α) (t : Finset (Additive X)) (ht : ∀ β ∈ t, SameRayRel β α) :
    ∃ δ : Additive X, 0 < pairingHom ψ δ ∧ (∃ c : ℕ, 0 < c ∧ α = c • δ) ∧
      ∀ β ∈ t, ∃ n : ℕ, 0 < n ∧ β = n • δ := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨α, hα, ⟨1, one_pos, (one_smul _ _).symm⟩, by simp⟩
  | insert β t _ ih =>
    obtain ⟨δ, hδ, ⟨c, hc, hαc⟩, hall⟩ := ih fun b hb => ht b (Finset.mem_insert_of_mem hb)
    obtain ⟨m, n, hm, hn, hmn⟩ := ht β (Finset.mem_insert_self _ _)
    have h1 : m • β = (n * c) • δ := by rw [hmn, hαc, smul_smul]
    obtain ⟨ε, a, b, ha, hb, hδε, hβε⟩ :=
      exists_common_generator δ β m (n * c) hm (Nat.mul_pos hn hc) h1
    have hε : 0 < pairingHom ψ ε := by
      rw [hδε, map_nsmul] at hδ
      rcases lt_trichotomy (pairingHom ψ ε) 0 with h | h | h
      · exfalso
        have : a • pairingHom ψ ε < 0 := by
          rw [nsmul_eq_mul]; exact mul_neg_of_pos_of_neg (by exact_mod_cast ha) h
        omega
      · rw [h, smul_zero] at hδ; exact absurd hδ (lt_irrefl _)
      · exact h
    refine ⟨ε, hε, ⟨c * a, Nat.mul_pos hc ha, by rw [hαc, hδε, smul_smul]⟩, ?_⟩
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact ⟨b, hb, hβε⟩
    · obtain ⟨k, hk, rfl⟩ := hall x hx
      exact ⟨k * a, Nat.mul_pos hk ha, by rw [hδε, smul_smul]⟩

end RayGenerator

section Build

variable [IsMulTorsionFree X] [IsAlgClosed k] [Algebra.FiniteType k H] [Algebra.Smooth k H]

open scoped Classical in
lemma rayGen_exists (ψ : X →* Multiplicative ℤ) (α : Additive X) (hα : 0 < pairingHom ψ α) :
    ∃ δ : Additive X, 0 < pairingHom ψ δ ∧ (∃ c : ℕ, 0 < c ∧ α = c • δ) ∧
      ∀ β ∈ (posRoots π (pairingHom ψ)).filter (fun β => SameRayRel β α),
        ∃ n : ℕ, 0 < n ∧ β = n • δ :=
  exists_ray_generator ψ α hα _ (fun β hβ => (Finset.mem_filter.1 hβ).2)

/-- The generator `δ` of the ray of `α` (all positive roots on it are multiples of `δ`). -/
noncomputable def rayGen (ψ : X →* Multiplicative ℤ) (α : Additive X)
    (hα : 0 < pairingHom ψ α) : PosRay ψ :=
  ⟨(rayGen_exists π ψ α hα).choose, (rayGen_exists π ψ α hα).choose_spec.1⟩

open scoped Classical in
lemma rayGen_spec (ψ : X →* Multiplicative ℤ) (α : Additive X) (hα : 0 < pairingHom ψ α) :
    ∀ β ∈ (posRoots π (pairingHom ψ)).filter (fun β => SameRayRel β α),
      ∃ n : ℕ, 0 < n ∧ β = n • (rayGen π ψ α hα).1 :=
  (rayGen_exists π ψ α hα).choose_spec.2.2

/-- `k[U_(δ)]` for the ray generator `δ` of `α`. -/
abbrev rayU (ψ : X →* Multiplicative ℤ) (α : Additive X) (hα : 0 < pairingHom ψ α) : Type u :=
  H ⧸ (rootGroupIdeal π (rayGen π ψ α hα).1 (PosRay.torsionFree ψ (rayGen π ψ α hα))).toIdeal

lemma isClosed_rayU_one (ψ : X →* Multiplicative ℤ) (α : Additive X) (hα : 0 < pairingHom ψ α) :
    IsClosed ({Bialgebra.augmentationPoint k (rayU π ψ α hα)} :
      Set (Spec (CommRingCat.of (rayU π ψ α hα)))) :=
  AlgHom.isClosed_singleton_kernelPoint _

/-- **`RayDimData` from the single input `hAff`** (T4 steps 1–5); `hdim` and `closed` are proved. -/
noncomputable def rayDimData_of_hAff (ψ : X →* Multiplicative ℤ) (α : Additive X)
    (hα : 0 < pairingHom ψ α)
    (hAff : IsAffineOpen (puncturedOpen (Bialgebra.augmentationPoint k (rayU π ψ α hα))
      (isClosed_rayU_one π ψ α hα))) :
    RayDimData π (pairingHom ψ) α where
  U := rayU π ψ α hα
  noeth := Algebra.FiniteType.isNoetherianRing k _
  one := Bialgebra.augmentationPoint k (rayU π ψ α hα)
  closed := isClosed_rayU_one π ψ α hα
  hAff := hAff
  hdim := by
    classical
    intro h2
    haveI := smooth_rootGroupIdeal π ψ (rayGen π ψ α hα)
    haveI : Algebra.FiniteType k (rayU π ψ α hα) :=
      Algebra.FiniteType.trans (S := H) inferInstance inferInstance
    refine not_krullDimLE_one_of_two_le_finrank_lie (k := k) (h2.trans ?_)
    unfold rayDim
    convert sum_finrank_le_finrank_lie_rootGroup π (rayGen π ψ α hα).1 _ _
      (rayGen_spec π ψ α hα)

end Build

end AlgMag.Reductive