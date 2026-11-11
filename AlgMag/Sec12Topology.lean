/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import StacksFrontier.AlgebraicGeometry.Size.Cutoff
import StacksFrontier.AlgebraicGeometry.Spaces.Points
import AlgMag.AlgebraicSpace
import AlgMag.Representation
import AlgMag.Sec3Functorial
import AlgMag.Cutoff

/-!
# Topology and geometry of attractors

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026) 126–201, §12.
-/

open CategoryTheory Opposite

universe u v w

namespace AlgMag

/-! ### Weights on fine monoids -/

section Gordan

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- Gordan's alternative over `ℚ`: vectors without a nontrivial nonnegative relation are all
positive for some linear form. -/
theorem exists_dual_pos {ι : Type*} (s : Finset ι) :
    ∀ v : ι → V, (∀ c : ι → ℚ, (∀ i ∈ s, 0 ≤ c i) → ∑ i ∈ s, c i • v i = 0 → ∀ i ∈ s, c i = 0) →
      ∃ φ : V →ₗ[ℚ] ℚ, ∀ i ∈ s, 0 < φ (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact fun _ _ => ⟨0, by simp⟩
  | insert k s hk ih =>
    intro v hv
    have hsub : ∀ c : ι → ℚ, (∀ i ∈ s, 0 ≤ c i) → ∑ i ∈ s, c i • v i = 0 → ∀ i ∈ s, c i = 0 := by
      intro c hc hsum i hi
      have := hv (fun j => if j = k then 0 else c j) (fun j hj => by
          by_cases e : j = k
          · simp [e]
          · simpa [e] using hc j ((Finset.mem_insert.mp hj).resolve_left e))
        (by
          rw [Finset.sum_insert hk]
          simp only [↓reduceIte, zero_smul, zero_add]
          rw [← hsum]
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [if_neg (ne_of_mem_of_not_mem hj hk)]) i (Finset.mem_insert_of_mem hi)
      simpa [ne_of_mem_of_not_mem hi hk] using this
    obtain ⟨φ, hφ⟩ := ih v hsub
    have hw : v k ≠ 0 := by
      intro h0
      have := hv (fun j => if j = k then 1 else 0) (fun j _ => by split_ifs <;> norm_num)
        (by
          rw [Finset.sum_insert hk]
          simp only [↓reduceIte, h0, smul_zero, zero_add]
          refine Finset.sum_eq_zero fun j hj => ?_
          rw [if_neg (ne_of_mem_of_not_mem hj hk), zero_smul]) k (Finset.mem_insert_self _ _)
      simp at this
    -- `θ = ψ + β φ` handles the new vector, for `β` in a suitable interval
    have combine : ∀ (ψ : V →ₗ[ℚ] ℚ) (β : ℚ), (∀ i ∈ s, -ψ (v i) / φ (v i) < β) →
        β * φ (v k) + ψ (v k) > 0 → ∃ θ : V →ₗ[ℚ] ℚ, ∀ i ∈ insert k s, 0 < θ (v i) := by
      intro ψ β hβ hk'
      refine ⟨ψ + β • φ, fun i hi => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl | hi
      · simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]; linarith
      · have h1 := hφ i hi
        have h2 := (div_lt_iff₀ h1).mp (hβ i hi)
        simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]; linarith
    have exists_upper : ∀ (ψ : V →ₗ[ℚ] ℚ), ∃ β₀ : ℚ, ∀ i ∈ s, -ψ (v i) / φ (v i) ≤ β₀ := by
      intro ψ
      obtain ⟨b, hb⟩ := (s.image fun i => -ψ (v i) / φ (v i)).bddAbove
      exact ⟨b, fun i hi => hb (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hi))⟩
    rcases lt_trichotomy (φ (v k)) 0 with hneg | hzero | hpos
    · -- the case `φ (v k) < 0`: apply the induction hypothesis to the projections on `ker φ`
      set d : ℚ := -φ (v k) with hd
      have hdpos : 0 < d := by simpa [hd] using hneg
      let u : ι → V := fun i => v i + (φ (v i) / d) • v k
      have hu : ∀ c : ι → ℚ, (∀ i ∈ s, 0 ≤ c i) → ∑ i ∈ s, c i • u i = 0 →
          ∀ i ∈ s, c i = 0 := by
        intro c hc hsum i hi
        let e : ℚ := ∑ j ∈ s, c j * (φ (v j) / d)
        have he : 0 ≤ e := Finset.sum_nonneg fun j hj =>
          mul_nonneg (hc j hj) (div_nonneg (hφ j hj).le hdpos.le)
        have hrel : ∑ j ∈ s, c j • u j = ∑ j ∈ s, c j • v j + e • v k := by
          simp only [u, e, smul_add, Finset.sum_add_distrib, Finset.sum_smul, mul_smul]
        have := hv (fun j => if j = k then e else c j) (fun j hj => by
            by_cases e' : j = k
            · simpa [e'] using he
            · simpa [e'] using hc j ((Finset.mem_insert.mp hj).resolve_left e'))
          (by
            rw [Finset.sum_insert hk]
            simp only [↓reduceIte]
            have : ∑ x ∈ s, (if x = k then e else c x) • v x = ∑ j ∈ s, c j • v j :=
              Finset.sum_congr rfl fun j hj => by rw [if_neg (ne_of_mem_of_not_mem hj hk)]
            rw [this, add_comm, ← hrel, hsum]) i (Finset.mem_insert_of_mem hi)
        simpa [ne_of_mem_of_not_mem hi hk] using this
      obtain ⟨ψ, hψ⟩ := ih u hu
      -- the admissible interval for `β` is nonempty
      have hlt : ∀ i ∈ s, -ψ (v i) / φ (v i) < ψ (v k) / d := by
        intro i hi
        have h1 := hφ i hi
        have h2 := hψ i hi
        simp only [u, map_add, map_smul, smul_eq_mul] at h2
        rw [div_lt_div_iff₀ h1 hdpos]
        have : 0 < (ψ (v i) + φ (v i) / d * ψ (v k)) * d := mul_pos h2 hdpos
        have e2 : (ψ (v i) + φ (v i) / d * ψ (v k)) * d = ψ (v i) * d + φ (v i) * ψ (v k) := by
          field_simp
        rw [e2] at this
        linarith
      obtain ⟨β₀, hβ₀⟩ : ∃ β₀ : ℚ, β₀ < ψ (v k) / d ∧ ∀ i ∈ s, -ψ (v i) / φ (v i) < β₀ := by
        by_cases hs : s.Nonempty
        · let m := s.sup' hs fun i => -ψ (v i) / φ (v i)
          have hm : m < ψ (v k) / d := (Finset.sup'_lt_iff hs).mpr hlt
          obtain ⟨β, h1, h2⟩ := exists_between hm
          exact ⟨β, h2, fun i hi => lt_of_le_of_lt (Finset.le_sup' (fun i => -ψ (v i) / φ (v i)) hi) h1⟩
        · rw [Finset.not_nonempty_iff_eq_empty] at hs
          exact ⟨ψ (v k) / d - 1, by linarith, by simp [hs]⟩
      refine combine ψ β₀ hβ₀.2 ?_
      have := (lt_div_iff₀ hdpos).mp hβ₀.1
      simp only [hd] at this ⊢
      linarith
    · -- the case `φ (v k) = 0`: perturb by a form positive on `v k`
      obtain ⟨ψ, hψ⟩ : ∃ ψ : V →ₗ[ℚ] ℚ, 0 < ψ (v k) := by
        obtain ⟨f, hf⟩ : ∃ f : V →ₗ[ℚ] ℚ, f (v k) ≠ 0 := by
          by_contra hcon
          push Not at hcon
          exact hw ((Module.forall_dual_apply_eq_zero_iff ℚ (v k)).mp hcon)
        rcases lt_or_gt_of_ne hf with h | h
        · exact ⟨-f, by simpa using h⟩
        · exact ⟨f, h⟩
      obtain ⟨β₀, hβ₀⟩ := exists_upper ψ
      exact combine ψ (β₀ + 1) (fun i hi => lt_of_le_of_lt (hβ₀ i hi) (by linarith))
        (by rw [hzero]; simpa using hψ)
    · exact ⟨φ, fun i hi => by
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hpos
        · exact hφ i hi⟩

end Gordan

variable {M : Type*} [AddCommGroup M]

/-- The fact from Ogus cited in Proposition 12.1, Proposition 12.3 and Theorem 12.4 ([27, Prop. 2.2.1,
Prop. 3.3.1]): a face `F` of a finitely generated submonoid `N` of an abelian group is the zero
locus of a morphism of monoids `N → ℕ`. -/
theorem exists_weight_of_isFace {F N : AddSubmonoid M} (hF : IsFace F N) (hN : N.FG) :
    ∃ w : N →+ ℕ, ∀ n : N, w n = 0 ↔ (n : M) ∈ F := by
  classical
  obtain ⟨g, hg⟩ := hN
  -- the rationalization of `M / F^gp`
  let G : AddSubgroup M := AddSubgroup.closure F
  let V := TensorProduct ℤ ℚ (M ⧸ G)
  let ι : (M ⧸ G) →ₗ[ℤ] V := TensorProduct.mk ℤ ℚ (M ⧸ G) 1
  have hloc : IsLocalizedModule (nonZeroDivisors ℤ) ι :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ ι).mpr
      (TensorProduct.isBaseChange ℤ _ ℚ)
  let q : M → V := fun m => ι (m : M ⧸ G)
  have hq_add : ∀ a b, q (a + b) = q a + q b := fun a b => by simp [q]
  have hq_zero : q 0 = 0 := by simp [q]
  have hq_F : ∀ f ∈ F, q f = 0 := fun f hf => by
    have : (f : M ⧸ G) = 0 := (QuotientAddGroup.eq_zero_iff f).mpr (AddSubgroup.subset_closure hf)
    simp [q, this]
  -- an element of `F^gp` is a difference of elements of `F`
  have hG : ∀ x ∈ G, ∃ a ∈ F, ∃ b ∈ F, x + b = a := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx => exact ⟨x, hx, 0, F.zero_mem, by simp⟩
    | zero => exact ⟨0, F.zero_mem, 0, F.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, b, hb, e⟩ := hx
      obtain ⟨a', ha', b', hb', e'⟩ := hy
      refine ⟨a + a', F.add_mem ha ha', b + b', F.add_mem hb hb', ?_⟩
      rw [← e, ← e']; abel
    | neg x _ hx =>
      obtain ⟨a, ha, b, hb, e⟩ := hx
      exact ⟨b, hb, a, ha, by rw [← e]; abel⟩
  -- the elements of `g` outside of `F`
  let s : Finset M := g.filter (· ∉ F)
  have hgN : ∀ i ∈ s, i ∈ N := fun i hi => by
    rw [← hg]; exact AddSubmonoid.subset_closure (by simpa using (Finset.mem_filter.mp hi).1)
  have hterm : ∀ (m : ℕ) (y : M), y ∈ N → m ≠ 0 → m • y ∈ F → y ∈ F := by
    intro m y hyN hm hmy
    obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    rw [succ_nsmul] at hmy
    exact (hF.mem_of_add_mem (N.nsmul_mem hyN _) hyN hmy).2
  have hclear : ∀ (r : ℚ) (t : ℕ), 0 ≤ r → r.den ∣ t → ∃ k : ℕ, (t : ℚ) * r = k := by
    intro r t hr ⟨e, he⟩
    refine ⟨e * r.num.toNat, ?_⟩
    have hnum : (0 : ℤ) ≤ r.num := Rat.num_nonneg.mpr hr
    have hc' : (r.num.toNat : ℚ) = r.num := by exact_mod_cast Int.toNat_of_nonneg hnum
    have hden : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_nz
    have h2 : (r.den : ℚ) * r = r.num := by rw [mul_comm]; exact Rat.mul_den_eq_num r
    rw [Nat.cast_mul, hc', he, Nat.cast_mul, ← h2]
    ring
  have hrel : ∀ c : M → ℚ, (∀ i ∈ s, 0 ≤ c i) → ∑ i ∈ s, c i • q i = 0 → ∀ i ∈ s, c i = 0 := by
    intro c hc hsum
    by_contra hcon
    push Not at hcon
    obtain ⟨i₀, hi₀, hci₀⟩ := hcon
    let D : ℕ := ∏ i ∈ s, (c i).den
    have hDpos : 0 < D := Finset.prod_pos fun i _ => (c i).pos
    have hint : ∀ i ∈ s, ∃ k : ℕ, (D : ℚ) * c i = k := fun i hi =>
      hclear _ _ (hc i hi) (Finset.dvd_prod_of_mem _ hi)
    choose! k hk using hint
    let x : M := ∑ i ∈ s, k i • i
    have hx_mem_N : x ∈ N := N.sum_mem fun i hi => N.nsmul_mem (hgN i hi) _
    have hqx : ι (x : M ⧸ G) = 0 := by
      have hnsmul : ∀ (m : ℕ) (a : M), q (m • a) = (m : ℚ) • q a := by
        intro m a
        induction m with
        | zero => simp [hq_zero]
        | succ m ihm =>
          rw [succ_nsmul, hq_add, ihm]
          push_cast
          rw [add_smul, one_smul]
      have h1 : ∀ (t : Finset M), q (∑ i ∈ t, k i • i) = ∑ i ∈ t, (k i : ℚ) • q i := by
        intro t
        induction t using Finset.induction_on with
        | empty => simp [hq_zero]
        | insert a t ha iht =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha, hq_add, iht, hnsmul]
      have h2 : ∑ i ∈ s, (k i : ℚ) • q i = (D : ℚ) • ∑ i ∈ s, c i • q i := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [← hk i hi, mul_smul]
      change q x = 0
      rw [h1 s, h2, hsum, smul_zero]
    obtain ⟨⟨n, hn⟩, hnx⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ) ι).mp hqx
    have hn0 : n ≠ 0 := nonZeroDivisors.ne_zero hn
    have hnx' : ((n • x : M) : M ⧸ G) = 0 := by simpa using hnx
    have hnxG : n • x ∈ G := (QuotientAddGroup.eq_zero_iff _).mp hnx'
    have hnat : n.natAbs • x ∈ G := by
      rcases Int.natAbs_eq n with h | h
      · have h2 : n • x = n.natAbs • x := by
          conv_lhs => rw [h]
          exact natCast_zsmul x _
        rwa [h2] at hnxG
      · have h2 : n • x = -(n.natAbs • x) := by
          conv_lhs => rw [h]
          rw [neg_smul, natCast_zsmul]
        rw [h2] at hnxG
        exact G.neg_mem_iff.mp hnxG
    obtain ⟨a, ha, b, hb, e⟩ := hG _ hnat
    have hy : n.natAbs • x ∈ N := N.nsmul_mem hx_mem_N _
    have hyF : n.natAbs • x ∈ F := (hF.mem_of_add_mem hy (hF.le hb) (e ▸ ha)).1
    have hxF : x ∈ F := hterm _ _ hx_mem_N (Int.natAbs_ne_zero.mpr hn0) hyF
    have hsplit : x = k i₀ • i₀ + ∑ j ∈ s.erase i₀, k j • j :=
      (Finset.add_sum_erase s (fun j => k j • j) hi₀).symm
    have hki₀ : k i₀ ≠ 0 := by
      intro h0
      have := hk i₀ hi₀
      rw [h0] at this
      simp only [Nat.cast_zero, mul_eq_zero, Nat.cast_eq_zero] at this
      exact this.elim (fun h => hDpos.ne' h) hci₀
    have h₁ : k i₀ • i₀ ∈ F := by
      have hrest : ∑ j ∈ s.erase i₀, k j • j ∈ N := N.sum_mem fun j hj =>
        N.nsmul_mem (hgN j (Finset.mem_of_mem_erase hj)) _
      exact (hF.mem_of_add_mem (N.nsmul_mem (hgN _ hi₀) _) hrest (hsplit ▸ hxF)).1
    exact (Finset.mem_filter.mp hi₀).2 (hterm _ _ (hgN _ hi₀) hki₀ h₁)
  obtain ⟨φ, hφ⟩ := exists_dual_pos s q hrel
  -- clear the denominators of the values of `φ`
  let D : ℕ := ∏ i ∈ s, (φ (q i)).den
  have hDpos : 0 < D := Finset.prod_pos fun i _ => (φ (q i)).pos
  have hφadd : ∀ a b, φ (q (a + b)) = φ (q a) + φ (q b) := fun a b => by rw [hq_add, map_add]
  have hstruct : ∀ n ∈ N, (n ∈ F ∧ φ (q n) = 0) ∨
      (0 < φ (q n) ∧ ∃ k : ℕ, (D : ℚ) * φ (q n) = k) := by
    intro n hn
    rw [← hg] at hn
    induction hn using AddSubmonoid.closure_induction with
    | mem x hx =>
      by_cases hxF : x ∈ F
      · exact Or.inl ⟨hxF, by rw [hq_F x hxF, map_zero]⟩
      · have hxs : x ∈ s := Finset.mem_filter.mpr ⟨by simpa using hx, hxF⟩
        exact Or.inr ⟨hφ x hxs, hclear _ _ (hφ x hxs).le (Finset.dvd_prod_of_mem _ hxs)⟩
    | zero => exact Or.inl ⟨F.zero_mem, by rw [hq_zero, map_zero]⟩
    | add a b _ _ ha hb =>
      rw [hφadd]
      rcases ha with ⟨ha, ha0⟩ | ⟨ha, k, hk⟩ <;> rcases hb with ⟨hb, hb0⟩ | ⟨hb, l, hl⟩
      · exact Or.inl ⟨F.add_mem ha hb, by rw [ha0, hb0, add_zero]⟩
      · exact Or.inr ⟨by rw [ha0, zero_add]; exact hb, l, by rw [ha0, zero_add]; exact hl⟩
      · exact Or.inr ⟨by rw [hb0, add_zero]; exact ha, k, by rw [hb0, add_zero]; exact hk⟩
      · exact Or.inr ⟨add_pos ha hb, k + l, by rw [mul_add, hk, hl]; push_cast; rfl⟩
  have hnonneg : ∀ n : N, ∃ k : ℕ, (D : ℚ) * φ (q n) = k := fun n => by
    rcases hstruct n n.2 with ⟨_, h0⟩ | ⟨_, k, hk⟩
    · exact ⟨0, by rw [h0]; simp⟩
    · exact ⟨k, hk⟩
  choose wf hwf using hnonneg
  refine ⟨{ toFun := wf, map_zero' := ?_, map_add' := ?_ }, fun n => ?_⟩
  · have := hwf 0
    simp only [ZeroMemClass.coe_zero, hq_zero, map_zero, mul_zero] at this
    exact_mod_cast this.symm
  · intro a b
    have h := hwf (a + b)
    rw [AddSubmonoid.coe_add, hφadd, mul_add, hwf a, hwf b] at h
    exact_mod_cast h.symm
  · change wf n = 0 ↔ _
    have hD : (D : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
    constructor
    · intro h0
      have := hwf n
      rw [h0] at this
      simp only [Nat.cast_zero, mul_eq_zero, hD, false_or] at this
      rcases hstruct n n.2 with ⟨h, _⟩ | ⟨h, _⟩
      · exact h
      · exact absurd this h.ne'
    · intro hn
      have := hwf n
      rw [hq_F _ hn, map_zero, mul_zero] at this
      exact_mod_cast this.symm

/-! ### Proposition 12.3 -/

section Deformation

variable {C : Type*} [Category.{v} C] {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}}
variable {M : Type*} [AddCommMonoid M] {F : Cᵒᵖ ⥤ Type u} (act : AAction 𝒪 M F)
variable {N L : AddSubmonoid M}

/-- The morphism `f : 𝔸(N) × 𝔸¹ → 𝔸(N)`, `(a, c) ↦ (n ↦ c ^ w(n) * a(n))`, attached to a weight
`w : N → ℕ` ([27, Prop. 3.3.1 (iii)]). -/
def APt.scale (w : N →+ ℕ) {U : Cᵒᵖ} (c : 𝒪.obj U) (a : APt 𝒪 N U) : APt 𝒪 N U where
  toFun n := c ^ w (Multiplicative.toAdd n) * a n
  map_one' := by
    have h0 : w (Multiplicative.toAdd (1 : Multiplicative N)) = 0 := map_zero w
    rw [h0, pow_zero, one_mul, map_one]
  map_mul' x y := by
    rw [toAdd_mul, map_add, pow_add, map_mul]
    ring

@[simp] lemma APt.scale_apply (w : N →+ ℕ) {U : Cᵒᵖ} (c : 𝒪.obj U) (a : APt 𝒪 N U)
    (n : Multiplicative N) : APt.scale w c a n = c ^ w (Multiplicative.toAdd n) * a n := rfl

lemma APt.res_scale (w : N →+ ℕ) {U V : Cᵒᵖ} (f : U ⟶ V) (c : 𝒪.obj U) (a : APt 𝒪 N U) :
    APt.res f (APt.scale w c a) = APt.scale w ((𝒪.map f).hom c) (APt.res f a) := by
  refine MonoidHom.ext fun n => ?_
  simp [map_mul, map_pow]

lemma APt.scale_mul_toMagnet (w : N →+ ℕ) {U : Cᵒᵖ} (c : 𝒪.obj U) (h : APt 𝒪 M U)
    (a : APt 𝒪 N U) :
    APt.scale w c (APt.toMagnet N h * a) = APt.toMagnet N h * APt.scale w c a := by
  refine MonoidHom.ext fun n => ?_
  simp only [APt.scale_apply, MonoidHom.mul_apply]
  ring

lemma APt.scale_one (w : N →+ ℕ) {U : Cᵒᵖ} (a : APt 𝒪 N U) : APt.scale w 1 a = a := by
  refine MonoidHom.ext fun n => ?_
  simp

/-- The composition of `f` with a point of `X^N`: the morphism `Ψ` of Proposition 12.3 on points. -/
def AttractorPt.deform {act : AAction 𝒪 M F} (w : N →+ ℕ) {T : C} (φ : AttractorPt act N T)
    (c : 𝒪.obj (op T)) : AttractorPt act N T where
  app t a := φ.app t (APt.scale w ((𝒪.map t.op).hom c) a)
  naturality s t a := by
    rw [← φ.naturality, APt.res_scale, ← CommRingCat.comp_apply, ← 𝒪.map_comp]
    rfl
  equivariant t h a := by
    rw [APt.scale_mul_toMagnet, φ.equivariant]

/-- The functor `X^N ×_S 𝔸¹_S`. -/
def deformSource (N : AddSubmonoid M) : Cᵒᵖ ⥤ Type _ where
  obj T := (attractor act N).obj T × 𝒪.obj T
  map f := ↾ fun p => ((attractor act N).map f p.1, (𝒪.map f).hom p.2)
  map_id T := by
    ext p
    · exact congrFun (congrArg (fun k => k.hom) ((attractor act N).map_id T)) p.1
    · simp
  map_comp f g := by
    ext p
    · exact congrFun (congrArg (fun k => k.hom) ((attractor act N).map_comp f g)) p.1
    · simp

/-- The morphism `Ψ : X^N ×_S 𝔸¹_S → X^N` of Proposition 12.3, for a weight `w`. -/
def deformation (w : N →+ ℕ) : deformSource act N ⟶ attractor act N where
  app T := ↾ fun p => AttractorPt.deform w p.1 p.2
  naturality T T' f := by
    ext p
    refine AttractorPt.ext ?_
    funext Z t a
    change p.1.app (t ≫ f.unop) (APt.scale w ((𝒪.map t.op).hom ((𝒪.map f).hom p.2)) a) =
      p.1.app (t ≫ f.unop) (APt.scale w ((𝒪.map (t ≫ f.unop).op).hom p.2) a)
    congr 2
    symm
    rw [← CommRingCat.comp_apply, ← 𝒪.map_comp]
    rfl

/-- The section `j_c : X^N → X^N ×_S 𝔸¹_S` given by a global constant `0` or `1`. -/
def sectionZero (N : AddSubmonoid M) : attractor act N ⟶ deformSource act N where
  app T := ↾ fun φ => (φ, 0)
  naturality T T' f := by
    ext p
    exact Prod.ext rfl (map_zero (𝒪.map f).hom).symm

/-- The section `j_1 : X^N → X^N ×_S 𝔸¹_S`. -/
def sectionOne (N : AddSubmonoid M) : attractor act N ⟶ deformSource act N where
  app T := ↾ fun φ => (φ, 1)
  naturality T T' f := by
    ext p
    exact Prod.ext rfl (map_one (𝒪.map f).hom).symm

/-- `ι × Id_{𝔸¹}`. -/
def deformSourceMap (h : L ≤ N) : deformSource act L ⟶ deformSource act N where
  app T := ↾ fun p => ((magnetMap act h).app T p.1, p.2)
  naturality _ _ _ := rfl

/-- The projection `pr₁ : X^N ×_S 𝔸¹_S → X^N`. -/
def deformSourceFst (N : AddSubmonoid M) : deformSource act N ⟶ attractor act N where
  app T := ↾ fun p => p.1
  naturality _ _ _ := rfl

/-- **Proposition 12.3.** Let `F` be a face of a magnet `N` of `M`, with `w : N → ℕ` vanishing
exactly on `F`. Then `ι : X^F → X^N` and `r : X^N → X^F` form a strong deformation retract: the
morphism `Ψ = deformation act w` satisfies (i) `Ψ ∘ j₀ = ι ∘ r`, (ii) `Ψ ∘ j₁ = Id` and (iii)
`Ψ ∘ (ι × Id) = ι ∘ pr₁`. Moreover `Ψ` lies over `X^F`: `r ∘ Ψ = r ∘ pr₁`. This holds for any
functor `X` with an action on any site. -/
theorem deformation_spec (hL : IsFace L N) (w : N →+ ℕ)
    (hw : ∀ n : N, w n = 0 ↔ (n : M) ∈ L) :
    sectionZero act N ≫ deformation act w = faceMap act hL ≫ magnetMap act hL.le ∧
    sectionOne act N ≫ deformation act w = 𝟙 _ ∧
    deformSourceMap act hL.le ≫ deformation act w = deformSourceFst act L ≫ magnetMap act hL.le ∧
    deformation act w ≫ faceMap act hL = deformSourceFst act N ≫ faceMap act hL := by
  have hw0 : ∀ {n : Multiplicative N}, ((Multiplicative.toAdd n : N) : M) ∈ L →
      w (Multiplicative.toAdd n) = 0 := fun h => (hw _).mpr h
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext T φ
    refine AttractorPt.ext ?_
    funext Z t a
    change φ.app t (APt.scale w ((𝒪.map t.op).hom 0) a) =
      φ.app t (APt.faceExt hL (APt.restrict hL.le a))
    congr 1
    refine MonoidHom.ext fun n => ?_
    rw [map_zero, APt.scale_apply]
    by_cases hn : ((Multiplicative.toAdd n : N) : M) ∈ L
    · rw [hw0 hn, APt.faceExt_pos hL _ hn, pow_zero, one_mul]
      rfl
    · have : w (Multiplicative.toAdd n) ≠ 0 := fun h => hn ((hw _).mp h)
      rw [zero_pow this, zero_mul, APt.faceExt_neg hL _ hn]
  · ext T φ
    refine AttractorPt.ext ?_
    funext Z t a
    change φ.app t (APt.scale w ((𝒪.map t.op).hom 1) a) = φ.app t a
    rw [map_one, APt.scale_one]
  · ext T p
    refine AttractorPt.ext ?_
    funext Z t a
    change p.1.app t (APt.restrict hL.le (APt.scale w ((𝒪.map t.op).hom p.2) a)) =
      p.1.app t (APt.restrict hL.le a)
    congr 1
    refine MonoidHom.ext fun n => ?_
    change ((𝒪.map t.op).hom p.2) ^ w (AddSubmonoid.inclusion hL.le (Multiplicative.toAdd n)) *
      a (AddMonoidHom.toMultiplicative (AddSubmonoid.inclusion hL.le) n) = _
    have : w (AddSubmonoid.inclusion hL.le (Multiplicative.toAdd n)) = 0 :=
      (hw _).mpr (Multiplicative.toAdd n).2
    rw [this, pow_zero, one_mul]
    rfl
  · ext T p
    refine AttractorPt.ext ?_
    funext Z t a
    change p.1.app t (APt.scale w ((𝒪.map t.op).hom p.2) (APt.faceExt hL a)) =
      p.1.app t (APt.faceExt hL a)
    congr 1
    refine MonoidHom.ext fun n => ?_
    rw [APt.scale_apply]
    by_cases hn : ((Multiplicative.toAdd n : N) : M) ∈ L
    · rw [hw0 hn, pow_zero, one_mul]
    · rw [APt.faceExt_neg hL _ hn, mul_zero]

end Deformation

/-- **Proposition 12.3**, with the weight provided by `AlgMag.exists_weight_of_isFace`: for `N`
finitely generated in an abelian group (so fine), a morphism `Ψ` with the required properties
exists. -/
theorem exists_strong_deformation_retract {C : Type*} [Category.{v} C] {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}}
    {M : Type*} [AddCommGroup M] {F : Cᵒᵖ ⥤ Type u} (act : AAction 𝒪 M F) {L N : AddSubmonoid M}
    (hL : IsFace L N) (hN : N.FG) :
    ∃ Ψ : deformSource act N ⟶ attractor act N,
      sectionZero act N ≫ Ψ = faceMap act hL ≫ magnetMap act hL.le ∧
      sectionOne act N ≫ Ψ = 𝟙 _ ∧
      deformSourceMap act hL.le ≫ Ψ = deformSourceFst act L ≫ magnetMap act hL.le ∧
      Ψ ≫ faceMap act hL = deformSourceFst act N ≫ faceMap act hL := by
  obtain ⟨w, hw⟩ := exists_weight_of_isFace hL hN
  exact ⟨deformation act w, deformation_spec act hL w hw⟩

/-! ### Affine schemes of monoid algebras in the site -/

section Spec

open AlgebraicGeometry

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- A morphism of schemes over `S` between objects of the site is a morphism of the site. -/
def overHom {U V : BigFppfOver B S hS} (f : (SCH).obj U ⟶ (SCH).obj V)
    (w : f ≫ V.hom.hom = U.hom.hom) : U ⟶ V :=
  Over.homMk (ObjectProperty.homMk f) (by ext; exact w)

@[simp] lemma map_overHom {U V : BigFppfOver B S hS} (f : (SCH).obj U ⟶ (SCH).obj V)
    (w : f ≫ V.hom.hom = U.hom.hom) : (SCH).map (overHom f w) = f := rfl

/-- A morphism of the site is determined by the underlying morphism of schemes. -/
lemma toScheme_map_injective {U V : BigFppfOver B S hS} {f g : U ⟶ V}
    (h : (SCH).map f = (SCH).map g) : f = g :=
  (SCH).map_injective h

variable (P : Type u) [AddCommMonoid P] [Fact (Cardinal.mk P < B.cutoff)]

/-- `Γ(V, 𝒪)[P]` for an object `V` of the site. -/
abbrev gRing (V : BigFppfOver B S hS) : Type u := AddMonoidAlgebra Γ((SCH).obj V, ⊤) P

/-- `𝔸(P)_V` is an object of the site, for `V` affine and `#P` below the cutoff. -/
theorem contains_spec (V : BigFppfOver B S hS) [IsAffine ((SCH).obj V)] :
    B.Contains (Spec (.of (gRing P V))) := by
  refine contains_addMonoidAlgebra (Fact.out : Cardinal.mk P < B.cutoff) (contains_iff_card.2 ?_)
  exact (Scheme.mk_sections_le_size _ ⟨⊤, isAffineOpen_top _⟩).trans_lt V.left.2

/-- The morphism `𝔸(P)_V → V` of schemes. -/
noncomputable def specPrS (V : BigFppfOver B S hS) [IsAffine ((SCH).obj V)] :
    Spec (.of (gRing P V)) ⟶ (SCH).obj V :=
  Spec.map (CommRingCat.ofHom (algebraMap _ _)) ≫ ((SCH).obj V).isoSpec.inv

/-- `𝔸(P)_V` as an object of the site. -/
noncomputable def specObj (V : BigFppfOver B S hS) [IsAffine ((SCH).obj V)] : BigFppfOver B S hS :=
  siteObject B S hS (contains_spec P V) (specPrS P V ≫ V.hom.hom)

instance (V : BigFppfOver B S hS) [IsAffine ((SCH).obj V)] : IsAffine ((SCH).obj (specObj P V)) :=
  inferInstanceAs (IsAffine (Spec _))

/-- The structure morphism `𝔸(P)_V → V`. -/
noncomputable def specPr (V : BigFppfOver B S hS) [IsAffine ((SCH).obj V)] : specObj P V ⟶ V :=
  overHom (specPrS P V) rfl

/-- The universal point of `𝔸(P)` on `𝔸(P)_V`. -/
noncomputable def specPt (V : BigFppfOver B S hS) [IsAffine ((SCH).obj V)] :
    APt (fppfO B S hS) P (op (specObj P V)) where
  toFun n := (Scheme.ΓSpecIso (.of (gRing P V))).inv
    (AddMonoidAlgebra.single (Multiplicative.toAdd n) 1)
  map_one' := by
    exact (map_one (Scheme.ΓSpecIso (.of (gRing P V))).inv.hom)
  map_mul' x y := by
    refine Eq.trans ?_ (map_mul (Scheme.ΓSpecIso (.of (gRing P V))).inv.hom _ _)
    rw [AddMonoidAlgebra.single_mul_single, mul_one]
    rfl

variable {P}

/-- The ring morphism `Γ(V)[P] → Γ(T')` classifying a point of `𝔸(P)` over `t : T' ⟶ V`. -/
noncomputable def specRing {V T' : BigFppfOver B S hS} (t : T' ⟶ V)
    (a : APt (fppfO B S hS) P (op T')) : gRing P V →+* Γ((SCH).obj T', ⊤) :=
  AddMonoidAlgebra.liftNCRingHom ((SCH).map t).appTop.hom a (fun _ _ => mul_comm _ _)

omit [Fact (Cardinal.mk P < B.cutoff)] in
lemma specRing_single {V T' : BigFppfOver B S hS} (t : T' ⟶ V)
    (a : APt (fppfO B S hS) P (op T')) (n : P) (r : Γ((SCH).obj V, ⊤)) :
    specRing t a (AddMonoidAlgebra.single n r) =
      ((SCH).map t).appTop.hom r * (show Γ((SCH).obj T', ⊤) from a (Multiplicative.ofAdd n)) := by
  simp [specRing, AddMonoidAlgebra.liftNCRingHom, AddMonoidAlgebra.liftNC_single]
  rfl

lemma appTop_toSpec_comp {X : Scheme.{u}} {A : Type u} [CommRing A] (φ : A →+* Γ(X, ⊤)) (x : A) :
    (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)).appTop.hom ((Scheme.ΓSpecIso (.of A)).inv.hom x) =
      φ x := by
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)
  have h2 : (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)).appTop =
      (Spec.map (CommRingCat.ofHom φ)).appTop ≫ X.toSpecΓ.appTop := by
    simp
  rw [h2, Scheme.toSpecΓ_appTop]
  have h3 := congrArg (fun k => (k ≫ (Scheme.ΓSpecIso Γ(X, ⊤)).hom).hom x) h
  simpa using h3.symm

omit [Fact (Cardinal.mk P < B.cutoff)] in
lemma specPrS_appTop (V : BigFppfOver B S hS) [IsAffine ((SCH).obj V)] (r : Γ((SCH).obj V, ⊤)) :
    (specPrS P V).appTop.hom r = (Scheme.ΓSpecIso (.of (gRing P V))).inv.hom
      (AddMonoidAlgebra.single 0 r) := by
  have hk : ((SCH).obj V).isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ((SCH).obj V, ⊤)).inv := by
    have h := congrArg (fun k => k.appTop) (Scheme.toSpecΓ_isoSpec_inv ((SCH).obj V))
    simp only [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Scheme.Hom.id_appTop] at h
    exact (Iso.comp_hom_eq_id _).mp h
  have h3 := Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (algebraMap Γ((SCH).obj V, ⊤) (gRing P V)))
  have h5 := congrArg (fun k => k.hom r) h3
  have h6 : (specPrS P V).appTop = (Scheme.ΓSpecIso Γ((SCH).obj V, ⊤)).inv ≫
      (Spec.map (CommRingCat.ofHom (algebraMap Γ((SCH).obj V, ⊤) (gRing P V)))).appTop := by
    rw [specPrS, Scheme.Hom.comp_appTop, hk]
  rw [h6]
  exact h5.symm

/-- The classifying morphism of a point of `𝔸(P)`. -/
noncomputable def specLiftS {V T' : BigFppfOver B S hS} [IsAffine ((SCH).obj V)] (t : T' ⟶ V)
    (a : APt (fppfO B S hS) P (op T')) : (SCH).obj T' ⟶ Spec (.of (gRing P V)) :=
  ((SCH).obj T').toSpecΓ ≫ Spec.map (CommRingCat.ofHom (specRing t a))

lemma specLiftS_pr {V T' : BigFppfOver B S hS} [IsAffine ((SCH).obj V)] (t : T' ⟶ V)
    (a : APt (fppfO B S hS) P (op T')) : specLiftS t a ≫ specPrS P V = (SCH).map t := by
  have h : CommRingCat.ofHom (algebraMap Γ((SCH).obj V, ⊤) (gRing P V)) ≫
      CommRingCat.ofHom (specRing t a) = ((SCH).map t).appTop := by
    ext r
    change specRing t a (AddMonoidAlgebra.single 0 r) = _
    rw [specRing_single]
    have : (show Γ((SCH).obj T', ⊤) from a (Multiplicative.ofAdd (0 : P))) = 1 := map_one a
    rw [this, mul_one]
  simp only [specLiftS, specPrS, Category.assoc]
  rw [← Category.assoc (Spec.map _), ← Spec.map_comp, h]
  rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc]
  simp

/-- The classifying morphism of a point of `𝔸(P)`, in the site. -/
noncomputable def specLift {V T' : BigFppfOver B S hS} [IsAffine ((SCH).obj V)] (t : T' ⟶ V)
    (a : APt (fppfO B S hS) P (op T')) : T' ⟶ specObj P V :=
  overHom (specLiftS t a) (by
    change specLiftS t a ≫ specPrS P V ≫ V.hom.hom = _
    rw [← Category.assoc, specLiftS_pr]
    exact congrArg (fun k => k.hom) (Over.w t) )

lemma specLift_pr {V T' : BigFppfOver B S hS} [IsAffine ((SCH).obj V)] (t : T' ⟶ V)
    (a : APt (fppfO B S hS) P (op T')) : specLift t a ≫ specPr P V = t :=
  toScheme_map_injective (by
    rw [Functor.map_comp]; exact specLiftS_pr t a)

lemma res_specLift {V T' : BigFppfOver B S hS} [IsAffine ((SCH).obj V)] (t : T' ⟶ V)
    (a : APt (fppfO B S hS) P (op T')) : APt.res (specLift t a).op (specPt P V) = a := by
  refine MonoidHom.ext fun n => ?_
  refine (appTop_toSpec_comp (specRing t a)
    (AddMonoidAlgebra.single (Multiplicative.toAdd n) 1)).trans ?_
  rw [specRing_single, map_one, one_mul]
  rfl

lemma specLift_uniq {V T' : BigFppfOver B S hS} [IsAffine ((SCH).obj V)] (t : T' ⟶ V)
    (a : APt (fppfO B S hS) P (op T')) (s : T' ⟶ specObj P V) (h₁ : s ≫ specPr P V = t)
    (h₂ : APt.res s.op (specPt P V) = a) : s = specLift t a := by
  have key : ((SCH).map s).appTop.hom.comp (Scheme.ΓSpecIso (.of (gRing P V))).inv.hom =
      specRing t a := by
    refine AddMonoidAlgebra.ringHom_ext (fun r => ?_) (fun n => ?_)
    · rw [specRing_single]
      change ((SCH).map s).appTop.hom ((Scheme.ΓSpecIso (.of (gRing P V))).inv.hom
        (AddMonoidAlgebra.single 0 r)) = _
      rw [← specPrS_appTop]
      have : (show Γ((SCH).obj T', ⊤) from a (Multiplicative.ofAdd (0 : P))) = 1 := map_one a
      rw [this, mul_one, ← h₁, Functor.map_comp, Scheme.Hom.comp_appTop]
      rfl
    · rw [specRing_single, map_one, one_mul, ← h₂]
      rfl
  refine toScheme_map_injective (ext_of_isAffine ?_)
  have hiso : Function.Surjective (Scheme.ΓSpecIso (.of (gRing P V))).inv.hom := fun y =>
    ⟨(Scheme.ΓSpecIso (.of (gRing P V))).hom.hom y, by
      simpa using congrArg (fun k => k.hom y) (Scheme.ΓSpecIso (.of (gRing P V))).hom_inv_id⟩
  refine CommRingCat.hom_ext (RingHom.ext fun y => ?_)
  obtain ⟨x, rfl⟩ := hiso y
  refine (congrArg (fun k => k x) key).trans ?_
  exact (appTop_toSpec_comp (specRing t a) x).symm

/-- `𝔸(N)_V` is universal: **Definition 3.1** applies over an affine object `V`. -/
noncomputable def specUniversal {M : Type u} [AddCommMonoid M] [Fact (Cardinal.mk M < B.cutoff)] (N : AddSubmonoid M)
    (V : BigFppfOver B S hS) [IsAffine ((SCH).obj V)] :
    UniversalPoint (fppfO B S hS) N V where
  P := specObj N V
  π := specPr N V
  u := specPt N V
  lift t a := specLift t a
  lift_π := specLift_pr
  res_lift := res_specLift
  uniq t a s h₁ h₂ := specLift_uniq t a s h₁ h₂

/-- `R[N] → R[M]` is injective, i.e. `𝔸(M)_V → 𝔸(N)_V` is schematically dominant. -/
lemma specMagnet_injective {M : Type u} [AddCommMonoid M] [Fact (Cardinal.mk M < B.cutoff)] (N : AddSubmonoid M)
    (V : BigFppfOver B S hS) [IsAffine ((SCH).obj V)] :
    Function.Injective ((SCH).map (specLift (specPr M V)
      (APt.toMagnet N (specPt M V)))).appTop.hom := by
  have hsurj : Function.Surjective (Scheme.ΓSpecIso (.of (gRing N V))).inv.hom := fun y =>
    ⟨(Scheme.ΓSpecIso (.of (gRing N V))).hom.hom y, by
      simpa using congrArg (fun k => k.hom y) (Scheme.ΓSpecIso (.of (gRing N V))).hom_inv_id⟩
  have hinj : Function.Injective (Scheme.ΓSpecIso (.of (gRing M V))).inv.hom :=
    fun y y' h => by
      have e := congrArg (Scheme.ΓSpecIso (.of (gRing M V))).hom.hom h
      simpa using e
  let j : gRing N V →+* gRing M V :=
    AddMonoidAlgebra.mapDomainRingHom _ N.subtype
  have hj : Function.Injective j := AddMonoidAlgebra.mapDomain_injective Subtype.val_injective
  have hjs : ∀ (n : N) (r : Γ((SCH).obj V, ⊤)), j (AddMonoidAlgebra.single n r) =
      AddMonoidAlgebra.single (n : M) r := fun n r => AddMonoidAlgebra.mapDomain_single
  have key : specRing (specPr M V) (APt.toMagnet N (specPt M V)) =
      (Scheme.ΓSpecIso (.of (gRing M V))).inv.hom.comp j := by
    refine AddMonoidAlgebra.ringHom_ext (fun r => ?_) (fun n => ?_)
    · rw [specRing_single]
      change _ = (Scheme.ΓSpecIso (.of (gRing M V))).inv.hom (j (AddMonoidAlgebra.single 0 r))
      rw [hjs]
      have : (show Γ((SCH).obj (specObj M V), ⊤) from
          APt.toMagnet N (specPt M V) (Multiplicative.ofAdd (0 : N))) = 1 :=
        map_one (APt.toMagnet N (specPt M V))
      rw [this, mul_one]
      exact specPrS_appTop V r
    · rw [specRing_single, map_one, one_mul]
      change _ = (Scheme.ΓSpecIso (.of (gRing M V))).inv.hom (j (AddMonoidAlgebra.single n 1))
      rw [hjs]
      rfl
  intro x y h
  obtain ⟨x, rfl⟩ := hsurj x
  obtain ⟨y, rfl⟩ := hsurj y
  have e := (appTop_toSpec_comp (specRing (specPr M V) (APt.toMagnet N (specPt M V))) x).symm.trans
    (h.trans (appTop_toSpec_comp (specRing (specPr M V) (APt.toMagnet N (specPt M V))) y))
  rw [key] at e
  rw [hj (hinj e)]

end Spec

/-! ### Proposition 12.2 (ii) -/

section ClosedImmersion

open AlgebraicGeometry

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- The presheaf morphism `f` is a closed immersion, tested after every representable base
change, as in `AlgMag.AttractorIsClosedSubspace`. -/
abbrev IsClosedImm {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) : Prop :=
  (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) (SCH))) f

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}

/-- If the pullback of `f` along `y` is an isomorphism, then `y` comes from `X`. -/
lemma mem_range_of_isIso_snd (hf : IsClosedImm f) {P : BigFppfOver B S hS} (y : Y.obj (op P))
    (h : IsIso ((SCH).map (hf.rep.snd (yonedaEquiv.symm y)))) :
    ∃ x, f.app (op P) x = y := by
  set g := yonedaEquiv.symm y
  set W := hf.rep.pullback g
  set snd := hf.rep.snd g
  have hp := hf.rep.isPullback g
  have hover : inv ((SCH).map snd) ≫ W.hom.hom = P.hom.hom := by
    rw [IsIso.inv_comp_eq]
    exact (congrArg (fun k => k.hom) (Over.w snd)).symm
  let k : P ⟶ W := overHom (inv ((SCH).map snd)) hover
  have hk : k ≫ snd = 𝟙 P := toScheme_map_injective (by
    rw [Functor.map_comp, map_overHom, IsIso.inv_hom_id, CategoryTheory.Functor.map_id])
  refine ⟨yonedaEquiv (yoneda.map k ≫ hf.rep.fst g), ?_⟩
  have e : yoneda.map k ≫ hf.rep.fst g ≫ f = g := by
    rw [hp.w, ← Category.assoc, ← Functor.map_comp, hk, CategoryTheory.Functor.map_id, Category.id_comp]
  have := congrArg yonedaEquiv e
  rw [Equiv.apply_symm_apply] at this
  rw [← this]
  simp [yonedaEquiv]

/-- Closed immersions of affine schemes through which a schematically dominant morphism factors
are isomorphisms. -/
lemma isIso_of_isClosedImmersion_of_dominant {W P Q : Scheme.{u}} [IsAffine P] (i : W ⟶ P)
    [IsClosedImmersion i] (e : Q ⟶ W) (hinj : Function.Injective (e ≫ i).appTop.hom) : IsIso i := by
  obtain ⟨hW, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine i
  have hbij : Function.Bijective i.appTop.hom := by
    refine ⟨fun x y h => hinj ?_, hsurj⟩
    rw [Scheme.Hom.comp_appTop]
    simp [h]
  have : IsIso i.appTop := (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  have : IsIso (Spec.map i.appTop) := inferInstance
  have h := Scheme.isoSpec_hom_naturality i
  have : IsIso (i ≫ P.isoSpec.hom) := by rw [← h]; infer_instance
  exact IsIso.of_isIso_comp_right i P.isoSpec.hom

/-- A point of `Y` on an affine `P` that lies in `X` after pullback along a
schematically dominant morphism `Q → P`, lies in `X`. -/
lemma mem_range_of_dominant (hf : IsClosedImm f) {P Q : BigFppfOver B S hS} [IsAffine ((SCH).obj P)]
    (ϖ : Q ⟶ P) (hinj : Function.Injective ((SCH).map ϖ).appTop.hom) (y : Y.obj (op P))
    (hy : ∃ x, f.app (op Q) x = Y.map ϖ.op y) : ∃ x, f.app (op P) x = y := by
  obtain ⟨x, hx⟩ := hy
  set g := yonedaEquiv.symm y
  have hp := hf.rep.isPullback g
  have heq : yonedaEquiv.symm x ≫ f = yoneda.map ϖ ≫ g := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_comp]
    simp [g, hx]
    rw [show yonedaEquiv (yoneda.map ϖ) = ϖ from Category.id_comp ϖ]
  let l := hp.lift _ _ heq
  let e : Q ⟶ hf.rep.pullback g := yoneda.preimage l
  have he : e ≫ hf.rep.snd g = ϖ := by
    apply yoneda.map_injective
    rw [Functor.map_comp, Functor.map_preimage]
    exact hp.lift_snd _ _ heq
  have hcl : IsClosedImmersion ((SCH).map (hf.rep.snd g)) := hf.property_snd g
  refine mem_range_of_isIso_snd hf y ?_
  refine isIso_of_isClosedImmersion_of_dominant _ ((SCH).map e) ?_
  rw [← Functor.map_comp, he]
  exact hinj

/-- Being in `X` is local on the source for the Zariski topology. -/
lemma mem_range_of_local (hf : IsClosedImm f) {T : BigFppfOver B S hS} (y : Y.obj (op T))
    (h : ∀ (U : BigFppfOver B S hS) [IsAffine ((SCH).obj U)] (u : U ⟶ T),
      ∃ x, f.app (op U) x = Y.map u.op y) : ∃ x, f.app (op T) x = y := by
  set g := yonedaEquiv.symm y
  have hp := hf.rep.isPullback g
  have hcl : IsClosedImmersion ((SCH).map (hf.rep.snd g)) := hf.property_snd g
  refine mem_range_of_isIso_snd hf y ?_
  let 𝒰 := ((SCH).obj T).affineCover
  have key := (IsZariskiLocalAtTarget.iff_of_openCover
    (P := MorphismProperty.isomorphisms Scheme.{u}) (f := (SCH).map (hf.rep.snd g)) 𝒰).mpr
    (fun i => ?_)
  · exact key
  · let U : BigFppfOver B S hS := siteObject B S hS
      (Scheme.size_lt_of_isOpenImmersion (𝒰.f i) T.left.2) (𝒰.f i ≫ T.hom.hom)
    have : IsAffine ((SCH).obj U) := inferInstanceAs (IsAffine (𝒰.X i))
    let u : U ⟶ T := overHom (𝒰.f i) rfl
    obtain ⟨x, hx⟩ := h U u
    have heq : yonedaEquiv.symm x ≫ f = yoneda.map u ≫ g := by
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, yonedaEquiv_comp]
      simp [g, hx]
      rw [show yonedaEquiv (yoneda.map u) = u from Category.id_comp u]
    let e : U ⟶ hf.rep.pullback g := yoneda.preimage (hp.lift _ _ heq)
    have he : e ≫ hf.rep.snd g = u := by
      apply yoneda.map_injective
      rw [Functor.map_comp, Functor.map_preimage]
      exact hp.lift_snd _ _ heq
    have he' : (SCH).map e ≫ (SCH).map (hf.rep.snd g) = 𝒰.f i := by
      rw [← Functor.map_comp, he]; rfl
    have hsec : IsSplitEpi (Limits.pullback.snd ((SCH).map (hf.rep.snd g)) (𝒰.f i)) :=
      IsSplitEpi.mk' ⟨Limits.pullback.lift ((SCH).map e) (𝟙 _) (by rw [he', Category.id_comp]),
        Limits.pullback.lift_snd _ _ _⟩
    exact (show IsIso (Limits.pullback.snd ((SCH).map (hf.rep.snd g)) (𝒰.f i)) from
      isIso_of_mono_of_isSplitEpi _)

/-- A closed immersion is injective on points. -/
lemma isClosedImm_injective (hf : IsClosedImm f) {P : BigFppfOver B S hS} {x x' : X.obj (op P)}
    (h : f.app (op P) x = f.app (op P) x') : x = x' := by
  set g := yonedaEquiv.symm (f.app (op P) x)
  have hp := hf.rep.isPullback g
  have hcl : IsClosedImmersion ((SCH).map (hf.rep.snd g)) := hf.property_snd g
  have mk : ∀ z : X.obj (op P), f.app (op P) z = f.app (op P) x →
      yonedaEquiv.symm z ≫ f = yoneda.map (𝟙 P) ≫ g := by
    intro z hz
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, CategoryTheory.Functor.map_id, Category.id_comp]
    simp [g, hz]
  let e₁ : P ⟶ hf.rep.pullback g := yoneda.preimage (hp.lift _ _ (mk x rfl))
  let e₂ : P ⟶ hf.rep.pullback g := yoneda.preimage (hp.lift _ _ (mk x' h.symm))
  have h₁ : e₁ ≫ hf.rep.snd g = 𝟙 P := by
    apply yoneda.map_injective
    rw [Functor.map_comp, Functor.map_preimage]
    exact hp.lift_snd _ _ _
  have h₂ : e₂ ≫ hf.rep.snd g = 𝟙 P := by
    apply yoneda.map_injective
    rw [Functor.map_comp, Functor.map_preimage]
    exact hp.lift_snd _ _ _
  have h₃ : e₁ = e₂ := toScheme_map_injective ((cancel_mono ((SCH).map (hf.rep.snd g))).mp (by
    rw [← Functor.map_comp, ← Functor.map_comp, h₁, h₂]))
  have f₁ : yoneda.map e₁ ≫ hf.rep.fst g = yonedaEquiv.symm x := by
    rw [Functor.map_preimage]; exact hp.lift_fst _ _ _
  have f₂ : yoneda.map e₂ ≫ hf.rep.fst g = yonedaEquiv.symm x' := by
    rw [Functor.map_preimage]; exact hp.lift_fst _ _ _
  exact yonedaEquiv.symm.injective (by rw [← f₁, ← f₂, h₃])

variable {M : Type u} [AddCommMonoid M] [Fact (Cardinal.mk M < B.cutoff)]
variable {aX : AAction (fppfO B S hS) M X} {aY : AAction (fppfO B S hS) M Y}

/-- A point of `Y^N` whose value at the unit section lies in `X` has all its values in `X`: the
orbit of the unit section is schematically dense in `𝔸(N)`. -/
theorem mem_range_app_of_toPoint (hg : EquivariantHom aX aY) (hf : IsClosedImm hg.hom)
    (N : AddSubmonoid M) {T : BigFppfOver B S hS} (φ : AttractorPt aY N T) (x : X.obj (op T))
    (hx : hg.hom.app _ x = φ.toPoint) {T' : BigFppfOver B S hS} (t : T' ⟶ T)
    (a : APt (fppfO B S hS) N (op T')) : ∃ x', hg.hom.app _ x' = φ.app t a := by
  refine mem_range_of_local hf _ fun U _ u => ?_
  rw [← φ.naturality]
  set c := u ≫ t
  set a' := APt.res u.op a
  -- the point on `𝔸(N)_U`
  let y' := φ.app (specPr N U ≫ c) (specPt N U)
  let ϖ : specObj M U ⟶ specObj N U := specLift (specPr M U) (APt.toMagnet N (specPt M U))
  have hϖ : ϖ ≫ specPr N U = specPr M U := specLift_pr _ _
  have hy' : ∃ x', hg.hom.app _ x' = y' := by
    refine mem_range_of_dominant hf ϖ (specMagnet_injective N U) y' ?_
    let q := specPr M U ≫ c
    have h1 : Y.map ϖ.op y' = φ.app q (APt.toMagnet N (specPt M U)) := by
      have := φ.naturality ϖ (specPr N U ≫ c) (specPt N U)
      rw [res_specLift] at this
      rw [← this]
      congr 1
      rw [← Category.assoc, hϖ]
    have h2 : φ.app q (APt.toMagnet N (specPt M U) * 1) =
        aY.smul (specPt M U) (φ.app q 1) := φ.equivariant q _ _
    rw [mul_one] at h2
    have h3 : φ.app q 1 = Y.map q.op φ.toPoint := by
      have := φ.naturality q (𝟙 T) 1
      rw [Category.comp_id] at this
      rw [AttractorPt.toPoint, ← this]
      congr 1
      exact (MonoidHom.ext fun _ => by simp [map_one])
    refine ⟨aX.smul (specPt M U) (X.map q.op x), ?_⟩
    rw [hg.map_smul, hom_naturality_apply, hx, ← h3, ← h2, h1]
  obtain ⟨x', hx'⟩ := hy'
  refine ⟨X.map (specLift (𝟙 U) a').op x', ?_⟩
  rw [hom_naturality_apply, hx']
  have := φ.naturality (specLift (𝟙 U) a') (specPr N U ≫ c) (specPt N U)
  rw [res_specLift] at this
  rw [← this]
  congr 1
  rw [← Category.assoc, specLift_pr, Category.id_comp]

/-- **Proposition 12.2 (ii)**, on points. Let `f : X → Y` be an equivariant closed immersion. Then
`X^N = Y^N ×_Y X`: a point of `Y^N` together with a point of `X` having the same image in `Y`
comes from a unique point of `X^N`. The assumptions (b), (c) of the paper are not needed. -/
theorem existsUnique_attractorPt_of_isClosedImm (hg : EquivariantHom aX aY)
    (hf : IsClosedImm hg.hom) (N : AddSubmonoid M) {T : BigFppfOver B S hS}
    (φ : AttractorPt aY N T) (x : X.obj (op T)) (hx : hg.hom.app _ x = φ.toPoint) :
    ∃! ψ : AttractorPt aX N T, ψ.push hg = φ ∧ ψ.toPoint = x := by
  choose v hv using fun (T' : BigFppfOver B S hS) (t : T' ⟶ T)
    (a : APt (fppfO B S hS) N (op T')) => mem_range_app_of_toPoint hg hf N φ x hx t a
  let ψ : AttractorPt aX N T :=
    { app := fun {T'} t a => v T' t a
      naturality := fun s t a => isClosedImm_injective hf (by
        rw [hv, hom_naturality_apply, hv, φ.naturality])
      equivariant := fun t h a => isClosedImm_injective hf (by
        rw [hv, hg.map_smul, hv, φ.equivariant]) }
  refine ⟨ψ, ⟨AttractorPt.ext ?_, isClosedImm_injective hf ?_⟩, ?_⟩
  · funext T' t a
    exact hv T' t a
  · exact (hv T (𝟙 T) 1).trans hx.symm
  · rintro ψ' ⟨h₁, -⟩
    refine AttractorPt.ext ?_
    funext T' t a
    refine isClosedImm_injective hf ?_
    exact (congrArg (fun p : AttractorPt aY N T => p.app t a) h₁).trans (hv T' t a).symm

omit [Fact (Cardinal.mk M < B.cutoff)] in
lemma rep_symm_naturality {act : AAction (fppfO B S hS) M X} {N : AddSubmonoid M}
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (r : RepresentsAttractor act N Z)
    {T T' : BigFppfOver B S hS} (s : T' ⟶ T) (φ : AttractorPt act N T) :
    Z.map s.op ((r.equiv T).symm φ) = (r.equiv T').symm (φ.baseChange s) := by
  refine (r.equiv T').injective ?_
  rw [r.naturality, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

omit [Fact (Cardinal.mk M < B.cutoff)] in
/-- The canonical morphism `Z_X → Z_Y` on representing presheaves (the morphism `f^N`). -/
noncomputable def repAttractorMap (hg : EquivariantHom aX aY) (N : AddSubmonoid M)
    {ZX ZY : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (rX : RepresentsAttractor aX N ZX) (rY : RepresentsAttractor aY N ZY) : ZX ⟶ ZY where
  app T := ↾ fun z => (rY.equiv (unop T)).symm ((rX.equiv (unop T) z).push hg)
  naturality T T' s := by
    ext z
    change (rY.equiv (unop T')).symm ((rX.equiv (unop T') (ZX.map s.unop.op z)).push hg) =
      ZY.map s.unop.op ((rY.equiv (unop T)).symm ((rX.equiv (unop T) z).push hg))
    rw [rep_symm_naturality, rX.naturality]
    rfl

omit [Fact (Cardinal.mk M < B.cutoff)] in
/-- The canonical morphism `Z → X` from a presheaf representing `X^N`. -/
noncomputable def repToPoint {aX : AAction (fppfO B S hS) M X} {N : AddSubmonoid M}
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (r : RepresentsAttractor aX N Z) : Z ⟶ X where
  app T := ↾ fun z => (r.equiv (unop T) z).toPoint
  naturality T T' s := by
    ext z
    change (r.equiv (unop T') (Z.map s.unop.op z)).toPoint =
      X.map s.unop.op (r.equiv (unop T) z).toPoint
    rw [r.naturality, AttractorPt.toPoint_baseChange]

/-- **Proposition 12.2 (ii).** Let `f : X → Y` be an equivariant closed immersion and suppose that
`X^N`, `Y^N` are represented. Then the square relating `f^N` and `f` is cartesian, that is
`X^N = Y^N ×_Y X`. Assumptions (b), (c) of the paper are not needed. -/
theorem isPullback_repAttractorMap (hg : EquivariantHom aX aY) (hf : IsClosedImm hg.hom)
    (N : AddSubmonoid M) {ZX ZY : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (rX : RepresentsAttractor aX N ZX) (rY : RepresentsAttractor aY N ZY) :
    IsPullback (repAttractorMap hg N rX rY) (repToPoint rX) (repToPoint rY) hg.hom := by
  have w : repAttractorMap hg N rX rY ≫ repToPoint rY = repToPoint rX ≫ hg.hom := by
    ext T z
    change ((rY.equiv (unop T)) ((rY.equiv (unop T)).symm _)).toPoint = _
    rw [Equiv.apply_symm_apply]
    rfl
  refine IsPullback.of_forall_isPullback_app fun T => ?_
  rw [Limits.Types.isPullback_iff]
  refine ⟨congrArg (fun k => k.app T) w, ?_, ?_⟩
  · rintro z z' ⟨h₁, h₂⟩
    refine (rX.equiv (unop T)).injective ?_
    obtain ⟨ψ, -, hu⟩ := existsUnique_attractorPt_of_isClosedImm hg hf N
      ((rX.equiv (unop T) z).push hg) ((rX.equiv (unop T) z).toPoint) rfl
    have hpush : (rX.equiv (unop T) z').push hg = (rX.equiv (unop T) z).push hg :=
      ((rY.equiv (unop T)).symm.injective h₁).symm
    rw [hu _ ⟨rfl, rfl⟩, hu _ ⟨hpush, h₂.symm⟩]
  · intro y x hxy
    have hxy' : hg.hom.app _ x = (rY.equiv (unop T) y).toPoint := hxy.symm
    obtain ⟨ψ, ⟨h₁, h₂⟩, -⟩ := existsUnique_attractorPt_of_isClosedImm hg hf N
      (rY.equiv (unop T) y) x hxy'
    refine ⟨(rX.equiv (unop T)).symm ψ, ?_, ?_⟩
    · change (rY.equiv (unop T)).symm ((rX.equiv (unop T) ((rX.equiv (unop T)).symm ψ)).push hg) = y
      rw [Equiv.apply_symm_apply, h₁, Equiv.symm_apply_apply]
    · change (rX.equiv (unop T) ((rX.equiv (unop T)).symm ψ)).toPoint = x
      rw [Equiv.apply_symm_apply, h₂]

/-- **Proposition 12.2 (ii)**, last assertion: `f^N` is a closed immersion. -/
theorem isClosedImm_repAttractorMap (hg : EquivariantHom aX aY) (hf : IsClosedImm hg.hom)
    (N : AddSubmonoid M) {ZX ZY : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (rX : RepresentsAttractor aX N ZX) (rY : RepresentsAttractor aY N ZY) :
    IsClosedImm (repAttractorMap hg N rX rY) :=
  (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
    (isPullback_repAttractorMap hg hf N rX rY).flip hf

end ClosedImmersion

/-! ### Proposition 12.1 -/

section Connected

open AlgebraicGeometry AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

variable {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The point of `|G|` at the residue field of a point `s` of `U`, for `g ∈ G(U)`. -/
noncomputable def residuePt {U : BigFppfOver B S hS} (g : G.obj (op U)) (s : (SCH).obj U) :
    FieldValuedPoint B S hS G where
  carrier := ((SCH).obj U).residueField s
  contained := BigFppfSite.residueField_spec_contains B U.left.2 s
  toBase := ((SCH).obj U).fromSpecResidueField s ≫ U.hom.hom
  value := G.map (overHom (U := Over.mk (⟨((SCH).obj U).fromSpecResidueField s ≫ U.hom.hom⟩ :
      B.obj (BigFppfSite.residueField_spec_contains B U.left.2 s) ⟶ B.obj hS)) (V := U)
    (((SCH).obj U).fromSpecResidueField s) rfl).op g

/-- A topology on `|G|` such that every scheme-valued point `U → G` induces a continuous map
`|U| → |G|`. The topology of Stacks Tag 03BY is of this form (it is the finest one). -/
def SchemeContinuous (τ : TopologicalSpace (points B S hS G)) : Prop :=
  ∀ (U : BigFppfOver B S hS) (g : G.obj (op U)),
    Continuous fun s : (SCH).obj U => (residuePt g s).class B S hS G

/-- A field-valued point obtained from a section over `U` by restriction is the class of a
residue-field point. -/
lemma class_eq_residuePt {U : BigFppfOver B S hS} (g : G.obj (op U))
    (p : FieldValuedPoint B S hS G) (k : p.siteObject ⟶ U) (hk : G.map k.op g = p.value) :
    ∃ s : (SCH).obj U, p.class B S hS G = (residuePt g s).class B S hS G := by
  obtain ⟨x, h⟩ : ∃ x : Σ s : (SCH).obj U, ((SCH).obj U).residueField s ⟶ .of p.carrier,
      Spec.map x.2 ≫ ((SCH).obj U).fromSpecResidueField x.1 = (SCH).map k :=
    ⟨Scheme.SpecToEquivOfField p.carrier ((SCH).obj U) ((SCH).map k),
      (Scheme.SpecToEquivOfField p.carrier ((SCH).obj U)).symm_apply_apply _⟩
  refine ⟨x.1, FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS G ⟨p,
    FieldValuedPoint.dominates_refl B S hS G p, ?_⟩⟩
  have hw : Spec.map x.2 ≫ ((SCH).obj U).fromSpecResidueField x.1 ≫ U.hom.hom = p.toBase := by
    rw [← Category.assoc, h]
    exact congrArg (fun k => k.hom) (Over.w k)
  let ρ : (residuePt g x.1).siteObject ⟶ U :=
    overHom (((SCH).obj U).fromSpecResidueField x.1) rfl
  let f : p.siteObject ⟶ (residuePt g x.1).siteObject := overHom (Spec.map x.2) hw
  refine ⟨f, ?_⟩
  change G.map f.op (G.map ρ.op g) = p.value
  rw [← Functor.map_comp_apply, ← op_comp]
  have hfk : f ≫ ρ = k := toScheme_map_injective (by
    rw [Functor.map_comp]; exact h)
  rw [hfk, hk]

/-- The affine line over a field point, as an object of the site. -/
noncomputable def lineObj (p : FieldValuedPoint B S hS G) : BigFppfOver B S hS :=
  siteObject B S hS
    (Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
      p.carrier (Polynomial p.carrier) p.contained)
    (Spec.map (CommRingCat.ofHom Polynomial.C) ≫ p.toBase)

instance (p : FieldValuedPoint B S hS G) : PreconnectedSpace ((SCH).obj (lineObj p)) := by
  have : IrreducibleSpace (Spec (.of (Polynomial p.carrier))) := inferInstance
  exact inferInstanceAs (PreconnectedSpace (Spec (.of (Polynomial p.carrier))))

/-- The projection of the line to its base. -/
noncomputable def linePr (p : FieldValuedPoint B S hS G) : lineObj p ⟶ p.siteObject :=
  overHom (Spec.map (CommRingCat.ofHom Polynomial.C)) rfl

/-- The section of the line at `c`. -/
noncomputable def lineSec (p : FieldValuedPoint B S hS G) (c : p.carrier) :
    p.siteObject ⟶ lineObj p :=
  overHom (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom c))) (by
    change _ ≫ Spec.map (CommRingCat.ofHom Polynomial.C) ≫ p.toBase = p.toBase
    rw [← Category.assoc, ← Spec.map_comp]
    have : CommRingCat.ofHom Polynomial.C ≫ CommRingCat.ofHom (Polynomial.evalRingHom c) = 𝟙 _ := by
      ext r
      simp
    rw [this]
    simp)

lemma lineSec_pr (p : FieldValuedPoint B S hS G) (c : p.carrier) :
    lineSec p c ≫ linePr p = 𝟙 _ := by
  refine toScheme_map_injective ?_
  rw [Functor.map_comp, CategoryTheory.Functor.map_id]
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  have : CommRingCat.ofHom Polynomial.C ≫ CommRingCat.ofHom (Polynomial.evalRingHom c) = 𝟙 _ := by
    ext r
    simp
  rw [this]
  simp
  rfl

/-- The coordinate of the line. -/
noncomputable def lineCoord (p : FieldValuedPoint B S hS G) : (fppfO B S hS).obj (op (lineObj p)) :=
  (Scheme.ΓSpecIso (.of (Polynomial p.carrier))).inv.hom Polynomial.X

/-- **The connectedness argument of Proposition 12.1**: two points of `|G|` on a common `𝔸¹` over a
field lie in the same connected component. -/
theorem class_mem_connectedComponent_of_line (τ : TopologicalSpace (points B S hS G))
    (hτ : SchemeContinuous τ) (p q₀ q₁ : FieldValuedPoint B S hS G) (γ : G.obj (op (lineObj p)))
    (k₀ : q₀.siteObject ⟶ lineObj p) (k₁ : q₁.siteObject ⟶ lineObj p)
    (h₀ : G.map k₀.op γ = q₀.value) (h₁ : G.map k₁.op γ = q₁.value) :
    q₀.class B S hS G ∈ connectedComponent (q₁.class B S hS G) := by
  obtain ⟨s₀, e₀⟩ := class_eq_residuePt γ q₀ k₀ h₀
  obtain ⟨s₁, e₁⟩ := class_eq_residuePt γ q₁ k₁ h₁
  rw [e₀, e₁]
  exact (isPreconnected_range (hτ _ γ)).subset_connectedComponent
    ⟨s₁, rfl⟩ ⟨s₀, rfl⟩

lemma lineCoord_res (p : FieldValuedPoint B S hS G) (c : p.carrier) :
    ((fppfO B S hS).map (lineSec p c).op).hom (lineCoord p) =
      (Scheme.ΓSpecIso (.of p.carrier)).inv.hom c := by
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Polynomial.evalRingHom c))
  have h' := congrArg (fun k => k.hom (Polynomial.X : Polynomial p.carrier)) h
  have e : (Polynomial.evalRingHom c) Polynomial.X = c := by simp
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, e] at h'
  exact h'.symm

variable {M : Type*} [AddCommMonoid M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {act : AAction (fppfO B S hS) M X} {N L : AddSubmonoid M}
  {ZN ZL : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

lemma rep_symm_naturality' (r : RepresentsAttractor act N ZN)
    {T T' : BigFppfOver B S hS} (s : T' ⟶ T) (φ : AttractorPt act N T) :
    ZN.map s.op ((r.equiv T).symm φ) = (r.equiv T').symm (φ.baseChange s) := by
  refine (r.equiv T').injective ?_
  rw [r.naturality, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

lemma AttractorPt.baseChange_deform (w : N →+ ℕ) {T T' : BigFppfOver B S hS} (s : T' ⟶ T)
    (φ : AttractorPt act N T) (c : (fppfO B S hS).obj (op T)) :
    (φ.deform w c).baseChange s = (φ.baseChange s).deform w (((fppfO B S hS).map s.op).hom c) := by
  refine AttractorPt.ext ?_
  funext Z t a
  change φ.app (t ≫ s) (APt.scale w (((fppfO B S hS).map (t ≫ s).op).hom c) a) =
    φ.app (t ≫ s) (APt.scale w (((fppfO B S hS).map t.op).hom (((fppfO B S hS).map s.op).hom c)) a)
  congr 2

/-- `r : X^N → X^L` on representing presheaves. -/
noncomputable def repFace (rN : RepresentsAttractor act N ZN) (rL : RepresentsAttractor act L ZL)
    (hL : IsFace L N) : ZN ⟶ ZL where
  app T := ↾ fun z => (rL.equiv (unop T)).symm ((rN.equiv (unop T) z).ofFace hL)
  naturality T T' s := by
    ext z
    change (rL.equiv (unop T')).symm ((rN.equiv (unop T') (ZN.map s.unop.op z)).ofFace hL) =
      ZL.map s.unop.op ((rL.equiv (unop T)).symm ((rN.equiv (unop T) z).ofFace hL))
    rw [rep_symm_naturality', rN.naturality]
    congr 1

/-- `ι : X^L → X^N` on representing presheaves. -/
noncomputable def repMagnet (rN : RepresentsAttractor act N ZN) (rL : RepresentsAttractor act L ZL)
    (h : L ≤ N) : ZL ⟶ ZN where
  app T := ↾ fun z => (rN.equiv (unop T)).symm ((rL.equiv (unop T) z).ofLE h)
  naturality T T' s := by
    ext z
    change (rN.equiv (unop T')).symm ((rL.equiv (unop T') (ZL.map s.unop.op z)).ofLE h) =
      ZN.map s.unop.op ((rN.equiv (unop T)).symm ((rL.equiv (unop T) z).ofLE h))
    rw [rep_symm_naturality', rL.naturality]
    congr 1

lemma repMagnet_comp_repFace (rN : RepresentsAttractor act N ZN)
    (rL : RepresentsAttractor act L ZL) (hL : IsFace L N) :
    repMagnet rN rL hL.le ≫ repFace rN rL hL = 𝟙 ZL := by
  ext T z
  change (rL.equiv (unop T)).symm ((rN.equiv (unop T) ((rN.equiv (unop T)).symm
    ((rL.equiv (unop T) z).ofLE hL.le))).ofFace hL) = z
  rw [Equiv.apply_symm_apply]
  have := hom_app_congr (magnetMap_comp_faceMap act hL) T (rL.equiv (unop T) z)
  refine ((rL.equiv (unop T)).symm_apply_eq).mpr ?_
  exact this

/-- The morphism `𝔸¹ → Z_N` obtained from `Ψ` and a point `z` over a field. -/
noncomputable def curve (rN : RepresentsAttractor act N ZN) (w : N →+ ℕ)
    (p : FieldValuedPoint B S hS G) (z : ZN.obj (op p.siteObject)) : ZN.obj (op (lineObj p)) :=
  (rN.equiv _).symm ((rN.equiv _ (ZN.map (linePr p).op z)).deform w (lineCoord p))

lemma curve_res (rN : RepresentsAttractor act N ZN) (w : N →+ ℕ)
    (p : FieldValuedPoint B S hS G) (z : ZN.obj (op p.siteObject)) (c : p.carrier) :
    ZN.map (lineSec p c).op (curve rN w p z) = (rN.equiv _).symm ((rN.equiv _ z).deform w
      ((Scheme.ΓSpecIso (.of p.carrier)).inv.hom c)) := by
  rw [curve, rep_symm_naturality', AttractorPt.baseChange_deform, lineCoord_res, ← rN.naturality,
    ← Functor.map_comp_apply, ← op_comp, lineSec_pr]
  simp

variable (hL : IsFace L N) (w : N →+ ℕ) (hw : ∀ n : N, w n = 0 ↔ (n : M) ∈ L)
variable (rN : RepresentsAttractor act N ZN) (rL : RepresentsAttractor act L ZL)

include hL hw in
lemma curve_res_one (p : FieldValuedPoint B S hS G) (z : ZN.obj (op p.siteObject)) :
    ZN.map (lineSec p 1).op (curve rN w p z) = z := by
  rw [curve_res, map_one]
  have := hom_app_congr (deformation_spec act hL w hw).2.1 (op p.siteObject) (rN.equiv _ z)
  refine ((rN.equiv _).symm_apply_eq).mpr ?_
  exact this

include hL hw in
lemma curve_res_zero (p : FieldValuedPoint B S hS G) (z : ZN.obj (op p.siteObject)) :
    ZN.map (lineSec p 0).op (curve rN w p z) =
      (repMagnet rN rL hL.le).app _ ((repFace rN rL hL).app _ z) := by
  rw [curve_res, map_zero]
  have := hom_app_congr (deformation_spec act hL w hw).1 (op p.siteObject) (rN.equiv _ z)
  change _ = (rN.equiv _).symm ((rL.equiv _ ((rL.equiv _).symm ((rN.equiv _ z).ofFace hL))).ofLE hL.le)
  rw [Equiv.apply_symm_apply]
  congr 1

include hL hw in
lemma repFace_curve (p : FieldValuedPoint B S hS G) (z : ZN.obj (op p.siteObject)) :
    (repFace rN rL hL).app _ (curve rN w p z) = ZL.map (linePr p).op ((repFace rN rL hL).app _ z) := by
  rw [← hom_naturality_apply]
  change (rL.equiv _).symm ((rN.equiv _ ((rN.equiv _).symm _)).ofFace hL) =
    (rL.equiv _).symm ((rN.equiv _ (ZN.map (linePr p).op z)).ofFace hL)
  rw [Equiv.apply_symm_apply]
  congr 1
  exact hom_app_congr (deformation_spec act hL w hw).2.2.2 (op (lineObj p))
    (rN.equiv _ (ZN.map (linePr p).op z), lineCoord p)

end Connected

section Prop121

open AlgebraicGeometry AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {M : Type*} [AddCommGroup M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {act : AAction (fppfO B S hS) M X} {N L : AddSubmonoid M}
  {ZN ZL : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The group `N^×` of units of a magnet `N`. -/
def unitsSubmonoid (N : AddSubmonoid M) : AddSubmonoid M where
  carrier := {x | x ∈ N ∧ -x ∈ N}
  zero_mem' := ⟨N.zero_mem, by simp⟩
  add_mem' := fun ha hb => ⟨N.add_mem ha.1 hb.1, by
    rw [neg_add]; exact N.add_mem ha.2 hb.2⟩

/-- `N^×` is a face of `N`. -/
theorem isFace_unitsSubmonoid (N : AddSubmonoid M) : IsFace (unitsSubmonoid N) N where
  le := fun _ h => h.1
  mem_of_add_mem := fun {x y} hx hy h => by
    have h2 := h.2
    rw [neg_add] at h2
    exact ⟨⟨hx, by
      have := N.add_mem h2 hy
      simpa using this⟩, ⟨hy, by
      have := N.add_mem h2 hx
      simpa [add_comm, add_left_comm] using this⟩⟩

variable (hL : IsFace L N) (hN : N.FG) (rN : RepresentsAttractor act N ZN)
  (rL : RepresentsAttractor act L ZL)

include hL hN in
/-- **Proposition 12.1**, the key step: a point `z` of `|X^N|` lies in the connected component of
`ι(r(z))`. -/
theorem mem_connectedComponent_repMagnet_repFace (τ : TopologicalSpace (points B S hS ZN))
    (hτ : SchemeContinuous τ) (z : points B S hS ZN) :
    pointsMap B S hS _ (repMagnet rN rL hL.le) (pointsMap B S hS _ (repFace rN rL hL) z) ∈
      connectedComponent z := by
  obtain ⟨w, hw⟩ := exists_weight_of_isFace hL hN
  induction z using Quot.ind with
  | mk p =>
    exact class_mem_connectedComponent_of_line τ hτ p _ p (curve rN w p p.value)
      (lineSec p 0) (lineSec p 1) (curve_res_zero hL w hw rN rL p p.value)
      (curve_res_one hL w hw rN p p.value)

include hL hN in
/-- **Proposition 12.1**: `X^N → X^L` induces a bijection on sets of connected components, for a
face `L` of `N` (for instance `L = N^×`, `AlgMag.isFace_unitsSubmonoid`). -/
theorem bijective_connectedComponents_repFace (τN : TopologicalSpace (points B S hS ZN))
    (τL : TopologicalSpace (points B S hS ZL)) (hτ : SchemeContinuous τN)
    (hr : Continuous (pointsMap B S hS _ (repFace rN rL hL)))
    (hi : Continuous (pointsMap B S hS _ (repMagnet rN rL hL.le))) :
    Function.Bijective hr.connectedComponentsMap := by
  have hsec : ∀ y, pointsMap B S hS _ (repFace rN rL hL)
      (pointsMap B S hS _ (repMagnet rN rL hL.le) y) = y := fun y => by
    have := congrFun (pointsMap_comp B S hS _ (repMagnet rN rL hL.le) (repFace rN rL hL)) y
    rw [repMagnet_comp_repFace, pointsMap_id] at this
    exact this.symm
  have hcomp : ∀ z, ConnectedComponents.mk (pointsMap B S hS _ (repMagnet rN rL hL.le)
      (pointsMap B S hS _ (repFace rN rL hL) z)) = ConnectedComponents.mk z := fun z =>
    ConnectedComponents.coe_eq_coe.mpr
      (connectedComponent_eq (mem_connectedComponent_repMagnet_repFace hL hN rN rL τN hτ z)).symm
  constructor
  · intro c c' h
    obtain ⟨z, rfl⟩ := ConnectedComponents.surjective_coe c
    obtain ⟨z', rfl⟩ := ConnectedComponents.surjective_coe c'
    have h' : ConnectedComponents.mk (pointsMap B S hS _ (repFace rN rL hL) z) =
      ConnectedComponents.mk (pointsMap B S hS _ (repFace rN rL hL) z') := h
    rw [← hcomp z, ← hcomp z']
    exact congrArg hi.connectedComponentsMap h'
  · intro c
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe c
    exact ⟨ConnectedComponents.mk (pointsMap B S hS _ (repMagnet rN rL hL.le) y),
      congrArg ConnectedComponents.mk (hsec y)⟩

/-- The fibre of `r : X^N → X^L` over a field-valued point `q` of `X^L`. -/
noncomputable abbrev faceFibre (q : FieldValuedPoint B S hS ZL) :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  fibreProduct (repFace rN rL hL) (yonedaEquiv.symm q.value)

include hL hN in
/-- **Proposition 12.1**: the fibres of `r : X^N → X^L` over field-valued points are connected.
Since the field is arbitrary (within the size cutoff of the site), this says the fibres are
geometrically connected. -/
theorem connectedSpace_faceFibre (q : FieldValuedPoint B S hS ZL)
    (τ : TopologicalSpace (points B S hS (faceFibre hL rN rL q))) (hτ : SchemeContinuous τ) :
    @ConnectedSpace _ τ := by
  obtain ⟨w, hw⟩ := exists_weight_of_isFace hL hN
  let E := faceFibre hL rN rL q
  have hsv : (repFace rN rL hL).app _ ((repMagnet rN rL hL.le).app _ q.value) = q.value :=
    hom_app_congr (repMagnet_comp_repFace rN rL hL) _ q.value
  let σv : E.obj (op q.siteObject) := ⟨((repMagnet rN rL hL.le).app _ q.value, 𝟙 _), by
    refine hsv.trans ?_
    change q.value = ZL.map (𝟙 _).op q.value
    simp⟩
  let σ : FieldValuedPoint B S hS E :=
    { carrier := q.carrier, contained := q.contained, toBase := q.toBase, value := σv }
  refine connectedSpace_iff_connectedComponent.mpr ⟨σ.class B S hS E, ?_⟩
  refine Set.eq_univ_of_forall fun e => ?_
  induction e using Quot.ind with
  | mk e =>
    let z : ZN.obj (op e.siteObject) := e.value.1.1
    let k : e.siteObject ⟶ q.siteObject := e.value.1.2
    have hzk : (repFace rN rL hL).app _ z = ZL.map k.op q.value := e.value.2
    let γ : E.obj (op (lineObj e)) := ⟨(curve rN w e z, linePr e ≫ k), by
      refine (repFace_curve hL w hw rN rL e z).trans ?_
      rw [hzk, ← Functor.map_comp_apply]
      rfl⟩
    let q₀ : FieldValuedPoint B S hS E :=
      { carrier := e.carrier, contained := e.contained, toBase := e.toBase,
        value := E.map k.op σv }
    have hk : ∀ c, lineSec e c ≫ linePr e ≫ k = k := fun c => by
      rw [← Category.assoc, lineSec_pr, Category.id_comp]
    have h₁ : E.map (lineSec e 1).op γ = e.value :=
      Subtype.ext (Prod.ext (curve_res_one hL w hw rN e z) (hk 1))
    have h₀ : E.map (lineSec e 0).op γ = q₀.value :=
      Subtype.ext (Prod.ext (by
        refine (curve_res_zero hL w hw rN rL e z).trans ?_
        rw [hzk]
        exact (hom_naturality_apply (repMagnet rN rL hL.le) k.op q.value)) ((hk 0).trans (Category.comp_id k).symm))
    have hmem := class_mem_connectedComponent_of_line τ hτ e q₀ e γ (lineSec e 0) (lineSec e 1)
      h₀ h₁
    have hcl : q₀.class B S hS E = σ.class B S hS E :=
      FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS E
        ⟨q₀, FieldValuedPoint.dominates_refl B S hS E q₀, ⟨k, rfl⟩⟩
    rw [hcl] at hmem
    rw [← connectedComponent_eq hmem]
    exact mem_connectedComponent

end Prop121

end AlgMag

#print axioms AlgMag.exists_weight_of_isFace
#print axioms AlgMag.exists_strong_deformation_retract
#print axioms AlgMag.isPullback_repAttractorMap
#print axioms AlgMag.isClosedImm_repAttractorMap
#print axioms AlgMag.bijective_connectedComponents_repFace
#print axioms AlgMag.connectedSpace_faceFibre
