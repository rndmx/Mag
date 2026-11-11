/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Torsion.Char33
import AlgMag.Torsion.Prop41Full

/-!
# Proposition 3.3 / Corollary 3.4 in elementwise form

Fix a prime `p` and `b`. For a subgroup `Z ⊆ M` whose torsion in `M/Z` is killed by `p^b`
(`Prim p b Z`), and `v ∈ W ∩ W_Z`:
* `prop33_exp`: some `v^(p^k) ∈ W(Φ ∩ Z)`  (so `W_Z / W(Φ∩Z)` is a `p`-group);
* `prop33_notTP`: if `p` is not a torsion prime, `v ∈ W(Φ ∩ Z)`.
Proof: Noetherian induction on `Z` (peeling a character of order `p` modulo `Z`, `Char33`,
`Step33`), base case Lemma 3.1.
Hypotheses: `HypR1`, `HypR2`, `M` free of finite rank, `Fintype ι`.
-/

namespace AlgMag.Torsion

open Set RD Classical

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N] [Fintype ι] {P : RootPairing ι ℤ M N}

namespace RD

/-- The torsion of `M / Z` is killed by `p^b`. -/
def Prim (p b : ℕ) (Z : AddSubgroup M) : Prop :=
  ∀ (m : M) (n : ℤ), n ≠ 0 → n • m ∈ Z → ((p ^ b : ℕ) : ℤ) • m ∈ Z

lemma ptOf_mem_iff (Ψ : Set M) (c : N) : ptOf P c ∈ corootLattR P Ψ ↔ c ∈ corootLatt P Ψ := by
  constructor
  · intro h
    let K : AddSubgroup (M →+ ℝ) := (corootLatt P Ψ).toAddSubgroup.map (ptOf P)
    have hK : corootLattR P Ψ ≤ K := by
      refine (AddSubgroup.closure_le K).2 ?_
      rintro y ⟨i, hi, rfl⟩
      exact ⟨P.coroot i, Submodule.subset_span ⟨i, hi, rfl⟩, rfl⟩
    obtain ⟨n, hn, hn2⟩ := hK h
    exact ptOf_injective P hn2 ▸ hn
  · intro hn
    induction hn using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      exact corootR_mem hi
    | zero => simpa using zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul a x _ hx => rw [map_zsmul]; exact zsmul_mem hx a

lemma exists_ptOf [Module.Free ℤ M] [Module.Finite ℤ M] {μ : M →+ ℝ}
    (hμ : μ ∈ (intPts : AddSubgroup (M →+ ℝ))) : ∃ c : N, ptOf P c = μ := by
  choose k hk using hμ
  let φ : M →+ ℤ :=
    { toFun := k
      map_zero' := by
        have := hk 0; simp only [map_zero] at this; exact_mod_cast this.symm
      map_add' := by
        intro a b
        have h1 := hk (a + b); have h2 := hk a; have h3 := hk b
        rw [map_add, h2, h3] at h1
        exact_mod_cast h1.symm }
  obtain ⟨c, hc⟩ := (P.isPerfPair_toLinearMap).bijective_right.2 φ.toIntLinearMap
  refine ⟨c, ?_⟩
  ext m
  have := LinearMap.congr_fun hc m
  simp only [ptOf, AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.coe_comp,
    Function.comp_apply, LinearMap.toAddMonoidHom_coe, LinearMap.flip_apply, Int.coe_castAddHom]
  rw [hk m]
  have h2 : P.toLinearMap m c = k m := by simpa [φ] using this
  rw [h2]

lemma isIntClosed_inter (Y : AddSubgroup M) : IsIntClosed P (range P.root ∩ (Y : Set M)) := by
  unfold IsIntClosed
  apply Set.Subset.antisymm
  · intro m hm
    exact ⟨hm.1, Submodule.subset_span hm⟩
  · rintro m ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have : Submodule.span ℤ (range P.root ∩ (Y : Set M)) ≤ AddSubgroup.toIntSubmodule Y :=
      Submodule.span_le.2 inter_subset_right
    exact this h2

/-- If `p` is not a torsion prime, `p^j μ ∈ ℤΨ^∨` and `μ ∈ M^∨` imply `μ ∈ ℤΨ^∨`. -/
lemma notTP_lift [Module.Free ℤ M] [Module.Finite ℤ M] {p : ℕ} (hp : p.Prime) (hnt : ¬ IsTP P p)
    {Ψ : Set M} (hΨ : IsIntClosed P Ψ) (j : ℕ) :
    ∀ μ ∈ (intPts : AddSubgroup (M →+ ℝ)), ((p ^ j : ℕ) : ℤ) • μ ∈ corootLattR P Ψ →
      μ ∈ corootLattR P Ψ := by
  induction j with
  | zero => intro μ _ h; simpa using h
  | succ j ih =>
    intro μ hμ h
    have h1 : (p : ℤ) • μ ∈ (intPts : AddSubgroup (M →+ ℝ)) := zsmul_mem hμ _
    have h2 : (p : ℤ) • μ ∈ corootLattR P Ψ := by
      apply ih _ h1
      have : ((p ^ j : ℕ) : ℤ) • ((p : ℤ) • μ) = ((p ^ (j + 1) : ℕ) : ℤ) • μ := by
        rw [← mul_smul]; congr 1
      rw [this]; exact h
    by_contra hμL
    obtain ⟨c, rfl⟩ := exists_ptOf (P := P) hμ
    apply hnt
    refine ⟨hp, Ψ, hΨ, c, fun hc => hμL ((ptOf_mem_iff Ψ c).2 hc), ?_⟩
    rw [← ptOf_mem_iff, map_zsmul]
    exact h2

variable [Module.Free ℤ M] [Module.Finite ℤ M]

theorem prop33 (hR1 : HypR1 P) (hR2 : HypR2 P) {p : ℕ} (hp : p.Prime) {b : ℕ} :
    ∀ Z : AddSubgroup M, Prim p b Z → ∀ v ∈ W P (range P.root), v ∈ WZ Z →
      (∃ k : ℕ, v ^ (p ^ k) ∈ W P (range P.root ∩ (Z : Set M))) ∧
      (¬ IsTP P p → v ∈ W P (range P.root ∩ (Z : Set M))) := by
  have wf : WellFoundedGT (AddSubgroup M) := by
    have : IsNoetherian ℤ M := inferInstance
    exact (AddSubgroup.toIntSubmodule (M := M)).toOrderEmbedding.wellFoundedGT
  intro Z
  induction Z using WellFoundedGT.induction with
  | _ Z ih =>
  intro hZ v hvW hvZ
  by_cases hsat : ∀ (m : M) (n : ℤ), n ≠ 0 → n • m ∈ Z → m ∈ Z
  · have hΦ : IsSubsystem P (range P.root) :=
      ⟨subset_rfl, fun i j _ _ => ⟨P.reflectionPerm i j, P.root_reflectionPerm i j⟩⟩
    have h := (lemma31 hR1 hΦ Z hsat hvW).1 hvZ
    have h' : v ∈ W P (range P.root ∩ (Z : Set M)) := h
    exact ⟨⟨0, by simpa using h'⟩, fun _ => h'⟩
  · push Not at hsat
    obtain ⟨m, n, hn, hnm, hm⟩ := hsat
    have hex : ∃ j : ℕ, ((p ^ j : ℕ) : ℤ) • m ∈ Z := ⟨b, hZ m n hn hnm⟩
    have hj0 : Nat.find hex ≠ 0 := by
      intro h0
      have := Nat.find_spec hex
      rw [h0] at this; simp at this; exact hm this
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hj0
    set z : M := ((p ^ j : ℕ) : ℤ) • m with hzdef
    have hz : z ∉ Z := by
      have := Nat.find_min hex (show j < Nat.find hex by omega)
      exact this
    have hpz : (p : ℤ) • z ∈ Z := by
      have := Nat.find_spec hex
      rw [hj] at this
      have e : (p : ℤ) • z = ((p ^ (j + 1) : ℕ) : ℤ) • m := by
        rw [hzdef, ← mul_smul]; congr 1; push_cast; ring
      rw [e]; exact this
    obtain ⟨x, hxint, hYx⟩ := exists_char hp (b := b) Z hZ hz hpz
    set Y : AddSubgroup M := Z ⊔ AddSubgroup.zmultiples z with hY
    have hZY : Z ≤ Y := le_sup_left
    have hZYlt : Z < Y := by
      refine lt_of_le_of_ne hZY fun h => hz ?_
      rw [h]; exact AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples z)
    have hpY : ∀ y ∈ Y, (p : ℤ) • y ∈ Z := by
      intro y hy
      obtain ⟨a, ha, w, hw, rfl⟩ := AddSubgroup.mem_sup.1 hy
      obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hw
      rw [smul_add, smul_comm]
      exact Z.add_mem (Z.zsmul_mem ha _) (Z.zsmul_mem hpz _)
    have hPrimY : Prim p b Y := by
      intro m' n' hn' h'
      apply hZY
      apply hZ m' ((p : ℤ) * n') (mul_ne_zero (by exact_mod_cast hp.ne_zero) hn')
      rw [mul_smul]
      exact hpY _ h'
    have hvY : v ∈ WZ Y := fun m' => hZY (hvZ m')
    obtain ⟨⟨k, hk⟩, hN⟩ := ih Y hZYlt hPrimY v hvW hvY
    have hvY' : v ^ (p ^ k) ∈ WZ Z := pow_mem hvZ _
    have hst := step33 hR2 (p := p ^ b) Y Z hZY x hxint hYx hk hvY'
    refine ⟨⟨k + b, ?_⟩, fun hnt => ?_⟩
    · rw [pow_add, pow_mul]
      exact hst.2.2.1
    · have hvk := hN hnt
      have hst2 := step33 hR2 (p := p ^ b) Y Z hZY x hxint hYx hvk hvZ
      refine hst2.2.2.2 ?_
      exact notTP_lift hp hnt (isIntClosed_inter Y) b _ hst2.1 hst2.2.1

end RD

end AlgMag.Torsion
