/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import TauCeti.LinearAlgebra.ExteriorPower.Decomposable
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Solvable
import Mathlib.LinearAlgebra.Basis.Flag
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Algebra.Category.ModuleCat.Basic
import TauCeti.LinearAlgebra.SymmetricAlgebra.Homogeneous

/-!
# The flag locus: linear algebra (part A of `exists_flagLocus`)

Field `K`, vector space `V`, `n = finrank V`. The flag tensor space is
`FT n = ((K ⊗ ⋀¹V) ⊗ ⋀²V) ⊗ ⋯ ⊗ ⋀ⁿV`. For a tensor `t` we use the *factor contractions*
`IsContr n i L` (`L : FT n → ⋀^(i+1) V`, apply linear forms to all the other factors) and three
families of quadratic equations:
* (E1) rank one: `ψ(L t) ψ'(L' t) = ψ'(L t) ψ(L' t)`;
* (E2) Plücker: `χ(ι(contract η (L t)) * L t) = 0` (Tau Ceti `Decomposable.lean`);
* (E3) incidence: `χ(ι(contract η (L t)) * L' t) = 0`, `L` on factor `i`, `L'` on factor `i+1`.

Main result here: `flagStab_isSolvable`. A nonzero solution `t` of (E1)–(E3) determines a full flag,
and the automorphisms `g` of `V` with `(⨂ ⋀g) t ∈ K t` form a solvable group.
-/

open TensorProduct Module

namespace AlgMag.Reductive.FlagLocus

universe u

variable {K : Type u} [Field K] {V : Type u} [AddCommGroup V] [Module K V]

/-! ### Annihilator subspace of an exterior vector -/

/-- `annihSub ω = {v | v ∧ ω = 0}`. -/
noncomputable def annihSub {r : ℕ} (ω : ⋀[K]^r V) : Submodule K V :=
  LinearMap.ker ((LinearMap.mulRight K (ω : ExteriorAlgebra K V)) ∘ₗ ExteriorAlgebra.ι K)

theorem mem_annihSub {r : ℕ} (ω : ⋀[K]^r V) (v : V) :
    v ∈ annihSub ω ↔ ExteriorAlgebra.ι K v * (ω : ExteriorAlgebra K V) = 0 := Iff.rfl

theorem annihSub_ιMulti {r : ℕ} {v : Fin r → V} (hv : LinearIndependent K v) :
    annihSub (exteriorPower.ιMulti K r v) = Submodule.span K (Set.range v) := by
  ext w
  rw [mem_annihSub, TauCeti.exteriorPower.mem_span_range_iff_ι_mul_ιMulti_eq_zero hv]

theorem annihSub_smul {r : ℕ} (ω : ⋀[K]^r V) {c : K} (hc : c ≠ 0) :
    annihSub (c • ω) = annihSub ω := by
  ext w
  simp only [mem_annihSub, Submodule.coe_smul, mul_smul_comm, smul_eq_zero, hc, false_or]

theorem annihSub_map {r : ℕ} (ω : ⋀[K]^r V) (f : V ≃ₗ[K] V) :
    annihSub (exteriorPower.map r (f : V →ₗ[K] V) ω) = (annihSub ω).map (f : V →ₗ[K] V) := by
  ext w
  rw [Submodule.mem_map_equiv, mem_annihSub, mem_annihSub, exteriorPower.coe_map]
  have hinj : Function.Injective (ExteriorAlgebra.map (f : V →ₗ[K] V)) := by
    intro x y hxy
    have h := congrArg (ExteriorAlgebra.map (f.symm : V →ₗ[K] V)) hxy
    simpa only [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, ← LinearEquiv.coe_trans,
      LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap, ExteriorAlgebra.map_id,
      AlgHom.id_apply] using h
  have key : ExteriorAlgebra.ι K w * ExteriorAlgebra.map (f : V →ₗ[K] V) (ω : ExteriorAlgebra K V) =
      ExteriorAlgebra.map (f : V →ₗ[K] V)
        (ExteriorAlgebra.ι K (f.symm w) * (ω : ExteriorAlgebra K V)) := by
    rw [map_mul, ExteriorAlgebra.map_apply_ι]
    simp
  rw [key, map_eq_zero_iff _ hinj]

/-- Decomposable nonzero vectors of `⋀^r V` have an `r`-dimensional annihilator. -/
theorem finrank_annihSub_of_ne_zero {r : ℕ} {v : Fin r → V}
    (h : exteriorPower.ιMulti K r v ≠ 0) :
    finrank K (annihSub (exteriorPower.ιMulti K r v)) = r := by
  have hv := (_root_.exteriorPower.ιMulti_ne_zero_iff v).mp h
  rw [annihSub_ιMulti hv, finrank_span_eq_card hv, Fintype.card_fin]

/-! ### Proportionality from 2×2 minors -/

theorem mem_span_of_minors {E : Type u} [AddCommGroup E] [Module K E] {α β : E} (hα : α ≠ 0)
    (h : ∀ ψ ψ' : Dual K E, ψ α * ψ' β = ψ' α * ψ β) : β ∈ K ∙ α := by
  obtain ⟨ψ, hψ⟩ := Module.Projective.exists_dual_ne_zero K hα
  rw [Submodule.mem_span_singleton]
  refine ⟨(ψ α)⁻¹ * ψ β, ?_⟩
  rw [← sub_eq_zero, ← forall_dual_apply_eq_zero_iff K]
  intro ψ'
  have := h ψ ψ'
  rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero]
  field_simp
  linear_combination -this

/-! ### The flag tensor space -/

variable (K V) in
/-- `FT n = ((K ⊗ ⋀¹V) ⊗ ⋀²V) ⊗ ⋯ ⊗ ⋀ⁿV`. -/
noncomputable def FT : ℕ → ModuleCat.{u} K
  | 0 => ModuleCat.of K K
  | j + 1 => ModuleCat.of K (FT j ⊗[K] ⋀[K]^(j + 1) V)

variable (K V) in
/-- The defining identification `FT (j+1) = FT j ⊗ ⋀^(j+1) V`. -/
noncomputable def ftSucc (j : ℕ) : FT K V (j + 1) ≃ₗ[K] FT K V j ⊗[K] ⋀[K]^(j + 1) V :=
  LinearEquiv.refl K (FT K V j ⊗[K] ⋀[K]^(j + 1) V)

/-- Induction principle on `FT (j+1)` through `ftSucc`. -/
theorem ft_induction {j : ℕ} {P : FT K V (j + 1) → Prop} (t : FT K V (j + 1)) (h0 : P 0)
    (ht : ∀ x y, P ((ftSucc K V j).symm (x ⊗ₜ[K] y))) (ha : ∀ a b, P a → P b → P (a + b)) :
    P t := by
  have key : ∀ s, P ((ftSucc K V j).symm s) := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simpa using h0
    | tmul x y => exact ht x y
    | add x y hx hy => simpa using ha _ _ hx hy
  simpa using key (ftSucc K V j t)

/-- Recursive tensor action of a family of endomorphisms of the exterior powers. -/
noncomputable def actT (A : ∀ r : ℕ, ⋀[K]^r V →ₗ[K] ⋀[K]^r V) :
    (n : ℕ) → (FT K V n →ₗ[K] FT K V n)
  | 0 => LinearMap.id
  | j + 1 => (ftSucc K V j).symm.toLinearMap ∘ₗ TensorProduct.map (actT A j) (A (j + 1)) ∘ₗ
      (ftSucc K V j).toLinearMap

theorem actT_succ (A : ∀ r : ℕ, ⋀[K]^r V →ₗ[K] ⋀[K]^r V) (j : ℕ) :
    actT A (j + 1) = (ftSucc K V j).symm.toLinearMap ∘ₗ TensorProduct.map (actT A j) (A (j + 1))
      ∘ₗ (ftSucc K V j).toLinearMap := rfl

theorem actT_comp (A B : ∀ r : ℕ, ⋀[K]^r V →ₗ[K] ⋀[K]^r V) (n : ℕ) :
    actT A n ∘ₗ actT B n = actT (fun r ↦ A r ∘ₗ B r) n := by
  induction n with
  | zero => rfl
  | succ j ih =>
    rw [actT_succ, actT_succ, actT_succ, ← ih, TensorProduct.map_comp]
    refine LinearMap.ext fun t ↦ ?_
    simp

theorem actT_id (n : ℕ) : actT (fun r ↦ (LinearMap.id : ⋀[K]^r V →ₗ[K] ⋀[K]^r V)) n =
    LinearMap.id := by
  induction n with
  | zero => rfl
  | succ j ih =>
    rw [actT_succ, ih, TensorProduct.map_id]
    refine LinearMap.ext fun t ↦ ?_
    simp

variable (K V) in
/-- Contraction of the last factor by `φ`. -/
noncomputable def contrLast (j : ℕ) (φ : Dual K (FT K V j)) :
    FT K V (j + 1) →ₗ[K] ⋀[K]^(j + 1) V :=
  (TensorProduct.lid K (⋀[K]^(j + 1) V)).toLinearMap ∘ₗ TensorProduct.map φ LinearMap.id ∘ₗ
    (ftSucc K V j).toLinearMap

variable (K V) in
/-- Contraction of the last factor by `ψ`, keeping the others. -/
noncomputable def dropLast (j : ℕ) (ψ : Dual K (⋀[K]^(j + 1) V)) : FT K V (j + 1) →ₗ[K] FT K V j :=
  (TensorProduct.rid K (FT K V j)).toLinearMap ∘ₗ TensorProduct.map LinearMap.id ψ ∘ₗ
    (ftSucc K V j).toLinearMap

/-- Factor contractions `FT n → ⋀^(i+1) V`. -/
inductive IsContr : (n i : ℕ) → (FT K V n →ₗ[K] ⋀[K]^(i + 1) V) → Prop
  | last (j : ℕ) (φ : Dual K (FT K V j)) : IsContr (j + 1) j (contrLast K V j φ)
  | inner (j i : ℕ) (L₀ : FT K V j →ₗ[K] ⋀[K]^(i + 1) V) (h : IsContr j i L₀)
      (ψ : Dual K (⋀[K]^(j + 1) V)) : IsContr (j + 1) i (L₀ ∘ₗ dropLast K V j ψ)

theorem IsContr.lt {n i : ℕ} {L : FT K V n →ₗ[K] ⋀[K]^(i + 1) V} (h : IsContr n i L) : i < n := by
  induction h with
  | last j φ => omega
  | inner j i L₀ _ ψ ih => omega

theorem contrLast_comp_actT (A : ∀ r : ℕ, ⋀[K]^r V →ₗ[K] ⋀[K]^r V) (j : ℕ)
    (φ : Dual K (FT K V j)) :
    contrLast K V j φ ∘ₗ actT A (j + 1) = A (j + 1) ∘ₗ contrLast K V j (φ ∘ₗ actT A j) := by
  refine LinearMap.ext fun t ↦ ?_
  induction t using ft_induction with
  | h0 => simp
  | ha a b ha hb => simp only [map_add, LinearMap.comp_apply] at *; rw [ha, hb]
  | ht x y => simp [contrLast, actT_succ]

theorem dropLast_comp_actT (A : ∀ r : ℕ, ⋀[K]^r V →ₗ[K] ⋀[K]^r V) (j : ℕ)
    (ψ : Dual K (⋀[K]^(j + 1) V)) :
    dropLast K V j ψ ∘ₗ actT A (j + 1) = actT A j ∘ₗ dropLast K V j (ψ ∘ₗ A (j + 1)) := by
  refine LinearMap.ext fun t ↦ ?_
  induction t using ft_induction with
  | h0 => simp
  | ha a b ha hb => simp only [map_add, LinearMap.comp_apply] at *; rw [ha, hb]
  | ht x y => simp [dropLast, actT_succ]

/-- Equivariance of contractions. -/
theorem IsContr.comp_actT (A : ∀ r : ℕ, ⋀[K]^r V →ₗ[K] ⋀[K]^r V) {n i : ℕ}
    {L : FT K V n →ₗ[K] ⋀[K]^(i + 1) V} (h : IsContr n i L) :
    ∃ L', IsContr n i L' ∧ L ∘ₗ actT A n = A (i + 1) ∘ₗ L' := by
  induction h with
  | last j φ => exact ⟨_, IsContr.last j (φ ∘ₗ actT A j), contrLast_comp_actT A j φ⟩
  | inner j i L₀ _ ψ ih =>
    obtain ⟨L₀', h₀', heq⟩ := ih
    refine ⟨_, IsContr.inner j i L₀' h₀' (ψ ∘ₗ A (j + 1)), ?_⟩
    rw [LinearMap.comp_assoc, dropLast_comp_actT, ← LinearMap.comp_assoc, heq,
      LinearMap.comp_assoc]

/-- A tensor killed by all `φ ⊗ ψ` is zero. -/
theorem tensor_eq_zero_of_dual {A B : Type u} [AddCommGroup A] [Module K A] [AddCommGroup B]
    [Module K B] (t : A ⊗[K] B)
    (h : ∀ (φ : Dual K A) (ψ : Dual K B), TensorProduct.lid K K (TensorProduct.map φ ψ t) = 0) :
    t = 0 := by
  let b := Module.Free.chooseBasis K A
  let c := Module.Free.chooseBasis K B
  have hrepr : ∀ s : A ⊗[K] B, ∀ p q, (b.tensorProduct c).repr s (p, q) =
      TensorProduct.lid K K (TensorProduct.map (b.coord p) (c.coord q) s) := by
    intro s p q
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      rw [Basis.tensorProduct_repr_tmul_apply]
      simp [mul_comm]
    | add x y hx hy => simp [hx, hy]
  apply (b.tensorProduct c).repr.injective
  ext ⟨p, q⟩
  rw [hrepr, h]
  simp

theorem lid_map_eq_dropLast (j : ℕ) (φ : Dual K (FT K V j)) (ψ : Dual K (⋀[K]^(j + 1) V))
    (t : FT K V (j + 1)) :
    TensorProduct.lid K K (TensorProduct.map φ ψ (ftSucc K V j t)) = φ (dropLast K V j ψ t) := by
  induction t using ft_induction with
  | h0 => simp
  | ha a b ha hb => simp only [map_add, ha, hb]
  | ht x y => simp [dropLast, mul_comm]

theorem lid_map_eq_contrLast (j : ℕ) (φ : Dual K (FT K V j)) (ψ : Dual K (⋀[K]^(j + 1) V))
    (t : FT K V (j + 1)) :
    TensorProduct.lid K K (TensorProduct.map φ ψ (ftSucc K V j t)) = ψ (contrLast K V j φ t) := by
  induction t using ft_induction with
  | h0 => simp
  | ha a b ha hb => simp only [map_add, ha, hb]
  | ht x y => simp [contrLast]

/-- Contractions on a fixed factor separate tensors. -/
theorem eq_zero_of_forall_isContr {n i : ℕ} (hi : i < n) (t : FT K V n)
    (h : ∀ L, IsContr n i L → L t = 0) : t = 0 := by
  induction n with
  | zero => omega
  | succ j ih =>
    have := tensor_eq_zero_of_dual (ftSucc K V j t) fun φ ψ ↦ ?_
    · exact (ftSucc K V j).map_eq_zero_iff.mp this
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hij | rfl
    · rw [lid_map_eq_dropLast, ih hij _ fun L₀ hL₀ ↦ h _ (IsContr.inner j i L₀ hL₀ ψ), map_zero]
    · rw [lid_map_eq_contrLast, h _ (IsContr.last i φ), map_zero]

/-! ### The flag equations -/

section FiniteDim

variable [FiniteDimensional K V]

variable (K V) in
/-- The quadratic flag equations (E1)–(E3) on `FT n`. -/
structure FlagEqs (n : ℕ) (t : FT K V n) : Prop where
  minor : ∀ i L L', IsContr n i L → IsContr n i L' → ∀ ψ ψ' : Dual K (⋀[K]^(i + 1) V),
    ψ (L t) * ψ' (L' t) = ψ' (L t) * ψ (L' t)
  plucker : ∀ i L, IsContr n i L → ∀ (η : ⋀[K]^i (Dual K V)) (χ : Dual K (ExteriorAlgebra K V)),
    χ (ExteriorAlgebra.ι K (exteriorPower.contract K V i η (L t)) * (L t : ExteriorAlgebra K V)) = 0
  incid : ∀ i L L', IsContr n i L → IsContr n (i + 1) L' →
    ∀ (η : ⋀[K]^i (Dual K V)) (χ : Dual K (ExteriorAlgebra K V)),
    χ (ExteriorAlgebra.ι K (exteriorPower.contract K V i η (L t)) * (L' t : ExteriorAlgebra K V)) = 0

/-- On each factor `i < n`, a nonzero solution has a nonzero decomposable contraction `L₀ t`
spanning all the others. -/
theorem FlagEqs.exists_factor {n : ℕ} {t : FT K V n} (heq : FlagEqs K V n t) (ht : t ≠ 0)
    {i : ℕ} (hi : i < n) :
    ∃ L₀, IsContr n i L₀ ∧ ∃ v : Fin (i + 1) → V, LinearIndependent K v ∧
      L₀ t = exteriorPower.ιMulti K (i + 1) v ∧ ∀ L, IsContr n i L → L t ∈ K ∙ L₀ t := by
  obtain ⟨L₀, hL₀, hne⟩ : ∃ L₀, IsContr n i L₀ ∧ L₀ t ≠ 0 := by
    by_contra! h
    exact ht (eq_zero_of_forall_isContr hi t h)
  have hdec : L₀ t ∈ Set.range (exteriorPower.ιMulti K (i + 1)) := by
    rw [exteriorPower.mem_range_ιMulti_iff_forall_ι_contract_mul_eq_zero]
    intro η
    rw [← forall_dual_apply_eq_zero_iff K]
    exact heq.plucker i L₀ hL₀ η
  obtain ⟨v, hv⟩ := hdec
  refine ⟨L₀, hL₀, v, (_root_.exteriorPower.ιMulti_ne_zero_iff v).mp (hv ▸ hne), hv.symm,
    fun L hL ↦ mem_span_of_minors hne (heq.minor i L₀ L hL₀ hL)⟩

/-- The term preceding `Fl i` in a flag (`⊥` for `i = 0`). -/
def preFl {n : ℕ} (Fl : Fin n → Submodule K V) (i : Fin n) : Submodule K V :=
  if h : (i : ℕ) = 0 then ⊥ else Fl ⟨i - 1, by omega⟩

theorem le_preFl {n : ℕ} {Fl : Fin n → Submodule K V} (hmono : Monotone Fl) {i j : Fin n}
    (hji : j < i) : Fl j ≤ preFl Fl i := by
  have h : (i : ℕ) ≠ 0 := by simp only [Fin.lt_def] at hji; omega
  simp only [preFl, h, dite_false]
  exact hmono (by simp only [Fin.le_def]; simp only [Fin.lt_def] at hji; omega)

theorem preFl_lt {n : ℕ} {Fl : Fin n → Submodule K V} (hdim : ∀ i, finrank K (Fl i) = i + 1)
    (hmono : Monotone Fl) (i : Fin n) : preFl Fl i < Fl i := by
  by_cases h : (i : ℕ) = 0
  · simp only [preFl, h, dite_true]
    rw [bot_lt_iff_ne_bot]
    intro hb; have := hdim i; rw [hb, finrank_bot] at this; omega
  · simp only [preFl, h, dite_false]
    refine lt_of_le_of_ne (hmono (by simp [Fin.le_def])) fun he ↦ ?_
    have h1 := hdim ⟨i - 1, by omega⟩; rw [he, hdim i] at h1; simp at h1; omega

/-- Adapted basis of a full flag: `Fl j` is spanned by the first `j + 1` basis vectors. -/
theorem exists_basis_of_flag {n : ℕ} (hn : finrank K V = n) (Fl : Fin n → Submodule K V)
    (hdim : ∀ i, finrank K (Fl i) = i + 1) (hmono : Monotone Fl) :
    ∃ b : Basis (Fin n) K V, ∀ j, Fl j = Submodule.span K (b '' {m | m ≤ j}) := by
  classical
  have hex : ∀ i, ∃ e ∈ Fl i, e ∉ preFl Fl i := fun i ↦ SetLike.exists_of_lt (preFl_lt hdim hmono i)
  choose e he hnot using hex
  have hli : LinearIndependent K e := by
    rw [linearIndependent_iff']
    intro s g hsum i hi
    by_contra hgi
    let T := s.filter (fun j ↦ g j ≠ 0)
    have hT : T.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hgi⟩⟩
    set m := T.max' hT
    have hm : m ∈ T := T.max'_mem hT
    have hms : m ∈ s := (Finset.mem_filter.mp hm).1
    have hgm : g m ≠ 0 := (Finset.mem_filter.mp hm).2
    have hrest : ∑ j ∈ s.erase m, g j • e j ∈ preFl Fl m := by
      refine Submodule.sum_mem _ fun j hj ↦ ?_
      by_cases hgj : g j = 0
      · simp [hgj]
      · have hjT : j ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase hj, hgj⟩
        have hjm : j < m := lt_of_le_of_ne (T.le_max' j hjT) (Finset.ne_of_mem_erase hj)
        exact Submodule.smul_mem _ _ (le_preFl hmono hjm (he j))
    have hsplit := Finset.add_sum_erase s (fun j ↦ g j • e j) hms
    rw [hsum] at hsplit
    have : g m • e m ∈ preFl Fl m := by
      rw [eq_neg_of_add_eq_zero_left hsplit]
      exact Submodule.neg_mem _ hrest
    exact hnot m ((Submodule.smul_mem_iff _ hgm).mp this)
  have htop : Submodule.span K (Set.range e) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hli, Fintype.card_fin, hn]
  let b : Basis (Fin n) K V := Basis.mk hli htop.ge
  have hb : ∀ i, b i = e i := fun i ↦ Basis.mk_apply _ _ i
  refine ⟨b, fun j ↦ ?_⟩
  have himg : b '' {m | m ≤ j} = e '' {m | m ≤ j} := by
    ext x; simp [hb]
  rw [himg]
  symm
  apply Submodule.eq_of_le_of_finrank_le
  · rw [Submodule.span_le]
    rintro _ ⟨m, hm, rfl⟩
    exact hmono hm (he m)
  · rw [hdim j]
    have hli' : LinearIndependent K (fun x : {m // m ≤ j} ↦ e x) :=
      hli.comp _ Subtype.val_injective
    have hrange : Set.range (fun x : {m // m ≤ j} ↦ e x) = e '' {m | m ≤ j} := by
      ext x; simp
    rw [← hrange, finrank_span_eq_card hli']
    rw [Fintype.card_subtype]
    have : (Finset.univ.filter fun x : Fin n ↦ x ≤ j) = Finset.Iic j := by ext; simp
    rw [this, Fin.card_Iic]

/-- A group acting faithfully on `V` and preserving a full flag is solvable. -/
theorem isSolvable_of_preserves_flag {G : Type*} [Group G] (ρ : G →* (V →ₗ[K] V)ˣ)
    (hρ : Function.Injective ρ) {n : ℕ} (hn : finrank K V = n) (Fl : Fin n → Submodule K V)
    (hdim : ∀ i, finrank K (Fl i) = i + 1) (hmono : Monotone Fl)
    (hpres : ∀ g i, ∀ v ∈ Fl i, (ρ g : V →ₗ[K] V) v ∈ Fl i) : Group.IsSolvable G := by
  classical
  obtain ⟨b, hb⟩ := exists_basis_of_flag hn Fl hdim hmono
  let ψ : G →* GL (Fin n) K :=
    (Units.map (LinearMap.toMatrixAlgEquiv b).toAlgHom.toMonoidHom).comp ρ
  have hψ : Function.Injective ψ := by
    intro x y hxy
    apply hρ
    apply Units.ext
    have := congrArg (fun u : GL (Fin n) K ↦ (u : Matrix (Fin n) (Fin n) K)) hxy
    exact (LinearMap.toMatrixAlgEquiv b).injective this
  have hmem : ∀ g, ψ g ∈ TauCeti.upperTriangularGroup (Fin n) K := by
    intro g
    rw [TauCeti.UpperTriangularGroup.mem_iff]
    intro l j hjl
    change LinearMap.toMatrixAlgEquiv b (ρ g : V →ₗ[K] V) l j = 0
    rw [LinearMap.toMatrixAlgEquiv_apply]
    have hv : (ρ g : V →ₗ[K] V) (b j) ∈ Fl j :=
      hpres g j _ (by rw [hb j]; exact Submodule.subset_span ⟨j, by simp, rfl⟩)
    rw [hb j] at hv
    have hker : Submodule.span K (b '' {m | m ≤ j}) ≤ LinearMap.ker (b.coord l) := by
      rw [Submodule.span_le]
      rintro _ ⟨m, hm, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, Basis.coord_apply, Basis.repr_self]
      exact Finsupp.single_eq_of_ne (by intro h; subst h; exact absurd hm (not_le.mpr hjl))
    exact hker hv
  exact Group.isSolvable_of_isSolvable_injective (f := ψ.codRestrict _ hmem)
    (fun x y h ↦ hψ (congrArg Subtype.val h))

theorem unit_comp_inv (u : (V →ₗ[K] V)ˣ) :
    (u : V →ₗ[K] V) ∘ₗ ((u⁻¹ : (V →ₗ[K] V)ˣ) : V →ₗ[K] V) = LinearMap.id := by
  rw [← Module.End.mul_eq_comp, Units.mul_inv]; rfl

theorem inv_comp_unit (u : (V →ₗ[K] V)ˣ) :
    ((u⁻¹ : (V →ₗ[K] V)ˣ) : V →ₗ[K] V) ∘ₗ (u : V →ₗ[K] V) = LinearMap.id := by
  rw [← Module.End.mul_eq_comp, Units.inv_mul]; rfl

/-- The linear equivalence of a unit. -/
noncomputable def unitEquiv (u : (V →ₗ[K] V)ˣ) : V ≃ₗ[K] V :=
  LinearEquiv.ofLinear u ((u⁻¹ : (V →ₗ[K] V)ˣ) : V →ₗ[K] V) (unit_comp_inv u) (inv_comp_unit u)

/-- Exterior-power action of a family of units. -/
noncomputable def wedgeAct (u : (V →ₗ[K] V)ˣ) : ∀ r : ℕ, ⋀[K]^r V →ₗ[K] ⋀[K]^r V :=
  fun r ↦ exteriorPower.map r (u : V →ₗ[K] V)

theorem wedgeAct_inv_comp (u : (V →ₗ[K] V)ˣ) (r : ℕ) :
    wedgeAct u⁻¹ r ∘ₗ wedgeAct u r = LinearMap.id := by
  simp only [wedgeAct, ← exteriorPower.map_comp, inv_comp_unit, exteriorPower.map_id]

theorem wedgeAct_comp_inv (u : (V →ₗ[K] V)ˣ) (r : ℕ) :
    wedgeAct u r ∘ₗ wedgeAct u⁻¹ r = LinearMap.id := by
  simp only [wedgeAct, ← exteriorPower.map_comp, unit_comp_inv, exteriorPower.map_id]

/-- **Part A, main theorem.** A group acting faithfully on `V` such that every element fixes the
line of a nonzero solution `t` of the flag equations is solvable. -/
theorem isSolvable_of_flagEqs {G : Type*} [Group G] (ρ : G →* (V →ₗ[K] V)ˣ)
    (hρ : Function.Injective ρ) {n : ℕ} (hn : finrank K V = n) (t : FT K V n) (ht : t ≠ 0)
    (heq : FlagEqs K V n t)
    (hstab : ∀ g, ∃ c : K, actT (wedgeAct (ρ g)) _ t = c • t) : Group.IsSolvable G := by
  classical
  have hfac := fun i : Fin n ↦ heq.exists_factor ht i.2
  choose L₀ hL₀ v hv hLv hspan using hfac
  let Fl : Fin n → Submodule K V := fun i ↦ annihSub (L₀ i t)
  have hFl : ∀ i, Fl i = Submodule.span K (Set.range (v i)) := fun i ↦ by
    simp only [Fl, hLv i, annihSub_ιMulti (hv i)]
  have hdim : ∀ i, finrank K (Fl i) = i + 1 := fun i ↦ by
    rw [hFl i, finrank_span_eq_card (hv i), Fintype.card_fin]
  -- incidence between consecutive terms
  have hinc : ∀ (i : ℕ) (hi : i + 1 < n), Fl ⟨i, by omega⟩ ≤ Fl ⟨i + 1, hi⟩ := by
    intro i hi
    rw [hFl, ← exteriorPower.range_contract_flip_ιMulti (hv ⟨i, by omega⟩)]
    rintro _ ⟨η, rfl⟩
    show ExteriorAlgebra.ι K _ * _ = 0
    rw [← forall_dual_apply_eq_zero_iff K]
    intro χ
    have := heq.incid i _ _ (hL₀ ⟨i, by omega⟩) (hL₀ ⟨i + 1, hi⟩) η χ
    rwa [hLv ⟨i, by omega⟩] at this
  have hmono : Monotone Fl := by
    let FlN : ℕ → Submodule K V := fun i ↦ if h : i < n then Fl ⟨i, h⟩ else ⊤
    have hN : Monotone FlN := by
      refine monotone_nat_of_le_succ fun i ↦ ?_
      by_cases h1 : i + 1 < n
      · simp only [FlN, h1, dite_true, show i < n by omega]
        exact hinc i h1
      · simp only [FlN, h1, dite_false]
        exact le_top
    intro a b hab
    have := hN (show (a : ℕ) ≤ b from hab)
    simpa [FlN, a.2, b.2] using this
  refine isSolvable_of_preserves_flag ρ hρ hn Fl hdim hmono fun g i w hw ↦ ?_
  obtain ⟨c, hc⟩ := hstab g
  -- `⋀g (L₀ t) ∈ K ∙ L₀ t`
  obtain ⟨L', hL', hcomp⟩ := (hL₀ i).comp_actT (wedgeAct (ρ g)⁻¹)
  have hinvt : actT (wedgeAct (ρ g)⁻¹) n (actT (wedgeAct (ρ g)) n t) = t := by
    rw [← LinearMap.comp_apply, actT_comp]
    simp only [wedgeAct_inv_comp, actT_id, LinearMap.id_apply]
  have h1 : L₀ i t = c • wedgeAct (ρ g)⁻¹ (i + 1) (L' t) := by
    have := congrArg (fun F ↦ F (actT (wedgeAct (ρ g)) n t)) hcomp
    simp only [LinearMap.comp_apply] at this
    rw [hinvt, hc, map_smul, map_smul] at this
    exact this
  have h2 : wedgeAct (ρ g) (i + 1) (L₀ i t) = c • L' t := by
    rw [h1, map_smul, ← LinearMap.comp_apply, wedgeAct_comp_inv, LinearMap.id_apply]
  have hinj : Function.Injective (wedgeAct (ρ g) (i + 1)) := by
    intro x y hxy
    have := congrArg (wedgeAct (ρ g)⁻¹ (i + 1)) hxy
    simpa only [← LinearMap.comp_apply, wedgeAct_inv_comp, LinearMap.id_apply] using this
  have hne : L₀ i t ≠ 0 := by
    rw [hLv i]; exact (_root_.exteriorPower.ιMulti_ne_zero_iff _).mpr (hv i)
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp (hspan i L' hL')
  have hd0 : wedgeAct (ρ g) (i + 1) (L₀ i t) = (c * d) • L₀ i t := by
    rw [h2, ← hd, smul_smul]
  have hcd : c * d ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hd0
    exact hne (hinj (hd0.trans (map_zero _).symm))
  have hmap : annihSub (wedgeAct (ρ g) (i + 1) (L₀ i t)) =
      (Fl i).map (unitEquiv (ρ g) : V →ₗ[K] V) := annihSub_map _ (unitEquiv (ρ g))
  rw [hd0, annihSub_smul _ hcd] at hmap
  have : (unitEquiv (ρ g) : V →ₗ[K] V) w ∈ (Fl i).map (unitEquiv (ρ g) : V →ₗ[K] V) :=
    Submodule.mem_map_of_mem hw
  rw [← hmap] at this
  exact this

/-! ### Invariance of the flag equations -/

theorem wedgeAct_ιMulti (u : (V →ₗ[K] V)ˣ) {r : ℕ} (v : Fin r → V) :
    wedgeAct u r (exteriorPower.ιMulti K r v) = exteriorPower.ιMulti K r ((u : V →ₗ[K] V) ∘ v) :=
  exteriorPower.map_apply_ιMulti _ _

/-- Plücker condition for a (possibly zero) decomposable vector. -/
theorem plucker_of_mem_range {i : ℕ} {x : ⋀[K]^(i + 1) V}
    (hx : x ∈ Set.range (exteriorPower.ιMulti K (i + 1))) (η : ⋀[K]^i (Dual K V)) :
    ExteriorAlgebra.ι K (exteriorPower.contract K V i η x) * (x : ExteriorAlgebra K V) = 0 := by
  obtain ⟨v, rfl⟩ := hx
  exact exteriorPower.ι_contract_mul_ιMulti_eq_zero η v

/-- Incidence for decomposable vectors with nested spans. -/
theorem incid_of_span_le {i : ℕ} {v : Fin (i + 1) → V} {y : ⋀[K]^(i + 2) V}
    (h : Submodule.span K (Set.range v) ≤ annihSub y) (η : ⋀[K]^i (Dual K V)) :
    ExteriorAlgebra.ι K (exteriorPower.contract K V i η (exteriorPower.ιMulti K (i + 1) v)) *
      (y : ExteriorAlgebra K V) = 0 :=
  h (exteriorPower.contract_ιMulti_mem_span η v)

theorem FlagEqs.wedge {n : ℕ} {t : FT K V n} (heq : FlagEqs K V n t) (u : (V →ₗ[K] V)ˣ) :
    FlagEqs K V n (actT (wedgeAct u) n t) := by
  have hL : ∀ {i} {L : FT K V n →ₗ[K] ⋀[K]^(i + 1) V}, IsContr n i L →
      ∃ L', IsContr n i L' ∧ L (actT (wedgeAct u) n t) = wedgeAct u (i + 1) (L' t) := by
    intro i L hL
    obtain ⟨L', hL', hc⟩ := hL.comp_actT (wedgeAct u)
    exact ⟨L', hL', by rw [← LinearMap.comp_apply, hc, LinearMap.comp_apply]⟩
  have hdec : ∀ {i} {L : FT K V n →ₗ[K] ⋀[K]^(i + 1) V}, IsContr n i L →
      L t ∈ Set.range (exteriorPower.ιMulti K (i + 1)) := by
    intro i L hL
    rw [exteriorPower.mem_range_ιMulti_iff_forall_ι_contract_mul_eq_zero]
    intro η
    rw [← forall_dual_apply_eq_zero_iff K]
    exact heq.plucker i L hL η
  refine ⟨fun i L L₂ hLc hL₂ ψ ψ' ↦ ?_, fun i L hLc η χ ↦ ?_, fun i L L₂ hLc hL₂ η χ ↦ ?_⟩
  · obtain ⟨L', hL', h1⟩ := hL hLc
    obtain ⟨L₂', hL₂', h2⟩ := hL hL₂
    rw [h1, h2]
    exact heq.minor i L' L₂' hL' hL₂' (ψ ∘ₗ wedgeAct u (i + 1)) (ψ' ∘ₗ wedgeAct u (i + 1))
  · obtain ⟨L', hL', h1⟩ := hL hLc
    obtain ⟨v, hv⟩ := hdec hL'
    rw [h1, ← hv, wedgeAct_ιMulti, plucker_of_mem_range ⟨_, rfl⟩, map_zero]
  · obtain ⟨L', hL', h1⟩ := hL hLc
    obtain ⟨L₂', hL₂', h2⟩ := hL hL₂
    rw [h1, h2]
    obtain ⟨v, hv⟩ := hdec hL'
    by_cases hli : LinearIndependent K v
    · -- `span v ≤ annihSub (L₂' t)`
      have hle : Submodule.span K (Set.range v) ≤ annihSub (L₂' t) := by
        rw [← exteriorPower.range_contract_flip_ιMulti hli]
        rintro _ ⟨η', rfl⟩
        show ExteriorAlgebra.ι K _ * _ = 0
        rw [← forall_dual_apply_eq_zero_iff K]
        intro χ'
        have := heq.incid i L' L₂' hL' hL₂' η' χ'
        rwa [← hv] at this
      have hle' : Submodule.span K (Set.range ((u : V →ₗ[K] V) ∘ v)) ≤
          annihSub (wedgeAct u (i + 1 + 1) (L₂' t)) := by
        have hm := annihSub_map (L₂' t) (unitEquiv u)
        change annihSub (exteriorPower.map _ (u : V →ₗ[K] V) (L₂' t)) =
          (annihSub (L₂' t)).map (u : V →ₗ[K] V) at hm
        rw [wedgeAct, hm, Set.range_comp, ← Submodule.map_span]
        exact Submodule.map_mono hle
      rw [← hv, wedgeAct_ιMulti, incid_of_span_le hle', map_zero]
    · have h0 : exteriorPower.ιMulti K (i + 1) v = 0 := by
        by_contra h; exact hli ((_root_.exteriorPower.ιMulti_ne_zero_iff v).mp h)
      rw [← hv, h0, map_zero, map_zero, map_zero, zero_mul, map_zero]

/-! ### The standard flag tensor -/

/-- Pure tensor of a family of exterior vectors. -/
noncomputable def pureT (ω : ∀ r : ℕ, ⋀[K]^r V) : (n : ℕ) → FT K V n
  | 0 => (show FT K V 0 from (1 : K))
  | j + 1 => (ftSucc K V j).symm (pureT ω j ⊗ₜ[K] ω (j + 1))

theorem isContr_pureT (ω : ∀ r : ℕ, ⋀[K]^r V) {n i : ℕ} {L : FT K V n →ₗ[K] ⋀[K]^(i + 1) V}
    (h : IsContr n i L) : ∃ c : K, L (pureT ω n) = c • ω (i + 1) := by
  induction h with
  | last j φ => exact ⟨φ (pureT ω j), by simp [contrLast, pureT]⟩
  | inner j i L₀ _ ψ ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨ψ (ω (j + 1)) * c, ?_⟩
    simp [dropLast, pureT, hc, smul_smul]

/-- The standard flag of a basis: `stdFlag b r = b₀ ∧ ⋯ ∧ b_{r-1}` for `r ≤ n`. -/
noncomputable def stdFlag {n : ℕ} (b : Basis (Fin n) K V) (r : ℕ) : ⋀[K]^r V :=
  if h : r ≤ n then exteriorPower.ιMulti K r (b ∘ Fin.castLE h) else 0

theorem stdFlag_of_le {n : ℕ} (b : Basis (Fin n) K V) {r : ℕ} (h : r ≤ n) :
    stdFlag b r = exteriorPower.ιMulti K r (b ∘ Fin.castLE h) := by
  simp [stdFlag, h]

theorem linearIndependent_castLE {n : ℕ} (b : Basis (Fin n) K V) {r : ℕ} (h : r ≤ n) :
    LinearIndependent K (b ∘ Fin.castLE h) :=
  b.linearIndependent.comp _ (Fin.castLE_injective h)

theorem stdFlag_ne_zero {n : ℕ} (b : Basis (Fin n) K V) {r : ℕ} (h : r ≤ n) :
    stdFlag b r ≠ 0 := by
  rw [stdFlag_of_le b h]
  exact (_root_.exteriorPower.ιMulti_ne_zero_iff _).mpr (linearIndependent_castLE b h)

theorem tmul_ne_zero_of_ne_zero {A B : Type u} [AddCommGroup A] [Module K A] [AddCommGroup B]
    [Module K B] {x : A} {y : B} (hx : x ≠ 0) (hy : y ≠ 0) : x ⊗ₜ[K] y ≠ 0 := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero K hx
  obtain ⟨ψ, hψ⟩ := Module.Projective.exists_dual_ne_zero K hy
  intro h0
  have := congrArg (fun z ↦ TensorProduct.lid K K (TensorProduct.map φ ψ z)) h0
  simp only [map_tmul, TensorProduct.lid_tmul, smul_eq_mul, map_zero] at this
  exact mul_ne_zero hφ hψ this

theorem pureT_ne_zero (ω : ∀ r : ℕ, ⋀[K]^r V) {n : ℕ} (hω : ∀ r, 1 ≤ r → r ≤ n → ω r ≠ 0) :
    pureT ω n ≠ 0 := by
  induction n with
  | zero => exact one_ne_zero (α := K)
  | succ j ih =>
    simp only [pureT, ne_eq, LinearEquiv.map_eq_zero_iff]
    exact tmul_ne_zero_of_ne_zero (ih fun r h1 h2 ↦ hω r h1 (by omega)) (hω (j + 1) (by omega) le_rfl)

/-- The standard flag tensor satisfies the flag equations. -/
theorem flagEqs_pureT_stdFlag {n : ℕ} (b : Basis (Fin n) K V) :
    FlagEqs K V n (pureT (stdFlag b) n) := by
  refine ⟨fun i L L' hL hL' ψ ψ' ↦ ?_, fun i L hL η χ ↦ ?_, fun i L L' hL hL' η χ ↦ ?_⟩
  · obtain ⟨c, hc⟩ := isContr_pureT (stdFlag b) hL
    obtain ⟨c', hc'⟩ := isContr_pureT (stdFlag b) hL'
    rw [hc, hc']
    simp only [map_smul, smul_eq_mul]
    ring
  · obtain ⟨c, hc⟩ := isContr_pureT (stdFlag b) hL
    have hi := hL.lt
    have h0 := plucker_of_mem_range
      (Set.mem_range_self (f := exteriorPower.ιMulti K (i + 1))
        (b ∘ Fin.castLE (by omega : i + 1 ≤ n))) η
    rw [hc, stdFlag_of_le b (by omega : i + 1 ≤ n)]
    simp only [map_smul, Submodule.coe_smul, smul_mul_assoc, mul_smul_comm, h0, smul_zero,
      map_zero]
  · obtain ⟨c, hc⟩ := isContr_pureT (stdFlag b) hL
    obtain ⟨c', hc'⟩ := isContr_pureT (stdFlag b) hL'
    have hi := hL'.lt
    have hle : Submodule.span K (Set.range (b ∘ Fin.castLE (by omega : i + 1 ≤ n))) ≤
        annihSub (stdFlag b (i + 1 + 1)) := by
      rw [stdFlag_of_le b (by omega : i + 1 + 1 ≤ n), annihSub_ιMulti (linearIndependent_castLE b _)]
      apply Submodule.span_mono
      rintro _ ⟨j, rfl⟩
      exact ⟨Fin.castSucc j, by simp⟩
    have := incid_of_span_le hle η
    rw [hc, hc', stdFlag_of_le b (by omega : i + 1 ≤ n)]
    simp only [map_smul, LinearMap.smul_apply, Submodule.coe_smul, smul_mul_assoc, mul_smul_comm,
      this, smul_zero, map_zero]

/-! ### The flag equations as quadratic forms -/

/-- The bilinear form `(s, t) ↦ f s * g t`. -/
noncomputable def mulForm {M : Type u} [AddCommGroup M] [Module K M] (f g : Dual K M) :
    M →ₗ[K] M →ₗ[K] K :=
  (LinearMap.mul K K).compl₁₂ f g

@[simp] theorem mulForm_apply {M : Type u} [AddCommGroup M] [Module K M] (f g : Dual K M)
    (s t : M) : mulForm f g s t = f s * g t := rfl

/-- The bilinear form `(s, t) ↦ χ (ι (contract η (L s)) * L' t)`. -/
noncomputable def wedgeForm {M : Type u} [AddCommGroup M] [Module K M] {i : ℕ}
    (L : M →ₗ[K] ⋀[K]^(i + 1) V) {r : ℕ} (L' : M →ₗ[K] ⋀[K]^r V) (η : ⋀[K]^i (Dual K V))
    (χ : Dual K (ExteriorAlgebra K V)) : M →ₗ[K] M →ₗ[K] K :=
  ((LinearMap.mul K (ExteriorAlgebra K V)).compl₁₂
    (ExteriorAlgebra.ι K ∘ₗ exteriorPower.contract K V i η ∘ₗ L)
    ((⋀[K]^r V).subtype ∘ₗ L')).compr₂ χ

@[simp] theorem wedgeForm_apply {M : Type u} [AddCommGroup M] [Module K M] {i : ℕ}
    (L : M →ₗ[K] ⋀[K]^(i + 1) V) {r : ℕ} (L' : M →ₗ[K] ⋀[K]^r V) (η : ⋀[K]^i (Dual K V))
    (χ : Dual K (ExteriorAlgebra K V)) (s t : M) :
    wedgeForm L L' η χ s t =
      χ (ExteriorAlgebra.ι K (exteriorPower.contract K V i η (L s)) * (L' t : ExteriorAlgebra K V)) :=
  rfl

variable (K V) in
/-- The bilinear forms whose diagonals are the flag equations. -/
def flagForms (n : ℕ) : Set (FT K V n →ₗ[K] FT K V n →ₗ[K] K) :=
  {B | (∃ i L L', IsContr n i L ∧ IsContr n i L' ∧ ∃ ψ ψ' : Dual K (⋀[K]^(i + 1) V),
        B = mulForm (ψ ∘ₗ L) (ψ' ∘ₗ L') - mulForm (ψ' ∘ₗ L) (ψ ∘ₗ L')) ∨
    (∃ i L, IsContr n i L ∧ ∃ η χ, B = wedgeForm L L η χ) ∨
    (∃ i L L', IsContr n i L ∧ IsContr n (i + 1) L' ∧ ∃ η χ, B = wedgeForm L L' η χ)}

theorem flagEqs_iff_forms {n : ℕ} (t : FT K V n) :
    FlagEqs K V n t ↔ ∀ B ∈ flagForms K V n, B t t = 0 := by
  constructor
  · rintro heq B (⟨i, L, L', hL, hL', ψ, ψ', rfl⟩ | ⟨i, L, hL, η, χ, rfl⟩ |
      ⟨i, L, L', hL, hL', η, χ, rfl⟩)
    · simp [heq.minor i L L' hL hL' ψ ψ']
    · exact heq.plucker i L hL η χ
    · exact heq.incid i L L' hL hL' η χ
  · intro h
    refine ⟨fun i L L' hL hL' ψ ψ' ↦ ?_, fun i L hL η χ ↦ ?_, fun i L L' hL hL' η χ ↦ ?_⟩
    · have := h _ (Or.inl ⟨i, L, L', hL, hL', ψ, ψ', rfl⟩)
      simpa [sub_eq_zero] using this
    · exact h _ (Or.inr (Or.inl ⟨i, L, hL, η, χ, rfl⟩))
    · exact h _ (Or.inr (Or.inr ⟨i, L, L', hL, hL', η, χ, rfl⟩))

/-! ### Quadratic polynomials -/

/-- The degree-two polynomial `v ↦ B v v` on a finite-dimensional space. -/
noncomputable def quadPoly {M : Type u} [AddCommGroup M] [Module K M] [Module.Finite K M]
    (B : M →ₗ[K] M →ₗ[K] K) : SymmetricAlgebra K (Dual K M) :=
  let e := Module.Free.chooseBasis K M
  ∑ a, ∑ b, B (e a) (e b) •
    (SymmetricAlgebra.ι K (Dual K M) (e.coord a) * SymmetricAlgebra.ι K (Dual K M) (e.coord b))

theorem quadPoly_mem {M : Type u} [AddCommGroup M] [Module K M] [Module.Finite K M]
    (B : M →ₗ[K] M →ₗ[K] K) :
    quadPoly B ∈ TauCeti.SymmetricAlgebra.homogeneousSubmodule K (Dual K M) 2 := by
  refine Submodule.sum_mem _ fun a _ ↦ Submodule.sum_mem _ fun b _ ↦ Submodule.smul_mem _ _ ?_
  exact SetLike.mul_mem_graded (TauCeti.SymmetricAlgebra.ι_mem_homogeneousSubmodule K _ _)
    (TauCeti.SymmetricAlgebra.ι_mem_homogeneousSubmodule K _ _)

theorem lift_eval_quadPoly {M : Type u} [AddCommGroup M] [Module K M] [Module.Finite K M]
    (B : M →ₗ[K] M →ₗ[K] K) (v : M) :
    SymmetricAlgebra.lift (Module.Dual.eval K M v) (quadPoly B) = B v v := by
  set e := Module.Free.chooseBasis K M
  have hv : v = ∑ a, e.repr v a • e a := (e.sum_repr v).symm
  conv_rhs => rw [hv]
  simp only [quadPoly, map_sum, map_smul, map_mul, SymmetricAlgebra.lift_ι_apply,
    Module.Dual.eval_apply, Basis.coord_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, e]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ by ring

end FiniteDim

end AlgMag.Reductive.FlagLocus
