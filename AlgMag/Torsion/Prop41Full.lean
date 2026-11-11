/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Torsion.Lemma12dD

/-!
# Proposition 4.1 (full): `IsTP p ⇒` existence of a `p`-candidate `w`

`prop41`: for `[Fintype ι]` (finitely many roots), if `p` is a torsion prime (`IsTP`), there are
`w ∈ Aut M` and `b > 0` with `orderOf w = p ^ b` and `w ∉ W(R_w)`, `R_w = Φ ∩ (1 - w)M`.
No hypothesis (R1)/(R2) is used.
-/

namespace AlgMag.Torsion

open Set RD Classical

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N] [Fintype ι]
  (P : RootPairing ι ℤ M N)

namespace RD

/-- `n ∈ N` as a point of `M^∨ ⊗ ℝ`. -/
noncomputable def ptOf : N →+ (M →+ ℝ) where
  toFun n := (Int.castAddHom ℝ).comp (P.toLinearMap.flip n).toAddMonoidHom
  map_zero' := by ext m; simp
  map_add' a b := by ext m; simp

lemma ptOf_coroot (i : ι) : ptOf P (P.coroot i) = corootR P i := rfl

lemma ptOf_injective : Function.Injective (ptOf P) := by
  rw [injective_iff_map_eq_zero]
  intro n hn
  have h : ∀ m : M, P.toLinearMap m n = 0 := by
    intro m
    have := DFunLike.congr_fun hn m
    simpa [ptOf] using this
  have hb := (P.isPerfPair_toLinearMap).bijective_right.1
  apply hb
  ext m
  simpa using h m

end RD

theorem prop41' {p : ℕ} (hTP : IsTP P p) :
    ∃ w : M ≃ₗ[ℤ] M, ∃ b : ℕ, w ∈ W P (range P.root) ∧ 0 < b ∧ orderOf w = p ^ b ∧
      w ∉ W P (range P.root ∩ Zset w) := by
  obtain ⟨hp, Ψ, hΨ, c0, hc0, hpc0⟩ := hTP
  have hΨsub : Ψ ⊆ range P.root := by
    rw [hΨ]; exact inter_subset_left
  set lam : M →+ ℝ := ptOf P c0 with hlam
  have hlamint : lam ∈ (intPts : AddSubgroup (M →+ ℝ)) := fun m => ⟨P.toLinearMap m c0, rfl⟩
  have hln : lam ∉ corootLattR P Ψ := by
    intro h
    let K : AddSubgroup (M →+ ℝ) := (corootLatt P Ψ).toAddSubgroup.map (ptOf P)
    have hK : corootLattR P Ψ ≤ K := by
      refine (AddSubgroup.closure_le K).2 ?_
      rintro y ⟨i, hi, rfl⟩
      exact ⟨P.coroot i, Submodule.subset_span ⟨i, hi, rfl⟩, rfl⟩
    obtain ⟨n, hn, hn2⟩ := hK h
    exact hc0 (ptOf_injective P hn2 ▸ hn)
  have hpl : (p : ℤ) • lam ∈ corootLattR P Ψ := by
    have key : ∀ n ∈ corootLatt P Ψ, ptOf P n ∈ corootLattR P Ψ := by
      intro n hn
      induction hn using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i, hi, rfl⟩ := hy
        exact corootR_mem hi
      | zero => simpa using zero_mem _
      | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
      | smul a x _ hx => rw [map_zsmul]; exact zsmul_mem hx a
    have := key _ hpc0
    simpa [hlam, map_zsmul] using this
  obtain ⟨c, hc, x, hx⟩ := exists_c_x P Ψ p hp.pos lam hpl
  have hpos := orderOf_pos_of_mem P hΨsub hc
  obtain ⟨b, m, hpm, hord⟩ := Nat.exists_eq_pow_mul_and_not_dvd hpos.ne' p hp.ne_one
  have hl : x - actPt c x ∈ (intPts : AddSubgroup (M →+ ℝ)) := hx ▸ hlamint
  have hln' : x - actPt c x ∉ corootLattR P Ψ := hx ▸ hln
  have hpl' : (p : ℤ) • (x - actPt c x) ∈ corootLattR P Ψ := hx ▸ hpl
  obtain ⟨h1, h2, h3⟩ := prop41_core hΨ hc x hl hln' hp hpl' hord hpm
  refine ⟨c ^ m, b, Subgroup.pow_mem _ (W_mono (P := P) hΨsub hc) m, ?_, h1, h3⟩
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · exfalso; apply h2; rw [← orderOf_eq_one_iff]; simpa using h1
  · exact hb

theorem prop41 {p : ℕ} (hTP : IsTP P p) :
    ∃ w : M ≃ₗ[ℤ] M, ∃ b : ℕ, 0 < b ∧ orderOf w = p ^ b ∧
      w ∉ W P (range P.root ∩ Zset w) := by
  obtain ⟨hp, Ψ, hΨ, c0, hc0, hpc0⟩ := hTP
  have hΨsub : Ψ ⊆ range P.root := by
    rw [hΨ]; exact inter_subset_left
  -- the point λ
  set lam : M →+ ℝ := ptOf P c0 with hlam
  have hlamint : lam ∈ (intPts : AddSubgroup (M →+ ℝ)) := fun m => ⟨P.toLinearMap m c0, rfl⟩
  have hln : lam ∉ corootLattR P Ψ := by
    intro h
    let K : AddSubgroup (M →+ ℝ) := (corootLatt P Ψ).toAddSubgroup.map (ptOf P)
    have hK : corootLattR P Ψ ≤ K := by
      refine (AddSubgroup.closure_le K).2 ?_
      rintro y ⟨i, hi, rfl⟩
      exact ⟨P.coroot i, Submodule.subset_span ⟨i, hi, rfl⟩, rfl⟩
    obtain ⟨n, hn, hn2⟩ := hK h
    exact hc0 (ptOf_injective P hn2 ▸ hn)
  have hpl : (p : ℤ) • lam ∈ corootLattR P Ψ := by
    have key : ∀ n ∈ corootLatt P Ψ, ptOf P n ∈ corootLattR P Ψ := by
      intro n hn
      induction hn using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i, hi, rfl⟩ := hy
        exact corootR_mem hi
      | zero => simpa using zero_mem _
      | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
      | smul a x _ hx => rw [map_zsmul]; exact zsmul_mem hx a
    have := key _ hpc0
    simpa [hlam, map_zsmul] using this
  obtain ⟨c, hc, x, hx⟩ := exists_c_x P Ψ p hp.pos lam hpl
  have hpos := orderOf_pos_of_mem P hΨsub hc
  obtain ⟨b, m, hpm, hord⟩ := Nat.exists_eq_pow_mul_and_not_dvd hpos.ne' p hp.ne_one
  have hl : x - actPt c x ∈ (intPts : AddSubgroup (M →+ ℝ)) := hx ▸ hlamint
  have hln' : x - actPt c x ∉ corootLattR P Ψ := hx ▸ hln
  have hpl' : (p : ℤ) • (x - actPt c x) ∈ corootLattR P Ψ := hx ▸ hpl
  obtain ⟨h1, h2, h3⟩ := prop41_core hΨ hc x hl hln' hp hpl' hord hpm
  refine ⟨c ^ m, b, ?_, h1, h3⟩
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · exfalso; apply h2; rw [← orderOf_eq_one_iff]; simpa using h1
  · exact hb

end AlgMag.Torsion
