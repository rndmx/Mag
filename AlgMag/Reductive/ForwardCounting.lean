/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.FromR1R2
import AlgMag.Reductive.AttractorReflects
import AlgMag.Reductive.RegularSlice

/-!
# (ii′) from Weyl elements and a dimension count (S-proof.md, Prop 6.1′, counting part)

Fix a cocharacter-like additive map `f : X → ℤ`, nonzero on every root. Write `posDim f` for the
dimension `∑_{α ∈ Φ, f α > 0} dim 𝔤_α` of `Lie U(λ_f)` and `posRays f` for the number of rays
(positive-rational proportionality classes) of `f`-positive roots.

In S-proof.md Prop 6.1′, `M_u = 1` gives `dim Y = dim U(±λ)` and `dim Y = |Ψ^±|`, i.e.
`posDim (±f) ≤ posRays (±f)`; together with Weyl elements (iii) this gives (ii′). This file
proves that implication (`condII_of_counting`). The dimension inequality is the only geometric
input, isolated as a hypothesis.
-/

suppress_compilation

open Magnetism TauCeti WithConv AlgMag.Weyl

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable [Module.Finite k (Bialgebra.CotangentSpace k H)]

/-- Same ray: `m α = n β` for some positive integers. -/
def SameRayRel (α β : Additive X) : Prop := ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ m • α = n • β

omit [DecidableEq X] [Module.Finite k (Bialgebra.CotangentSpace k H)] in
lemma sameRayRel_equivalence : Equivalence (SameRayRel (X := X)) where
  refl α := ⟨1, 1, one_pos, one_pos, rfl⟩
  symm := fun ⟨m, n, hm, hn, h⟩ => ⟨n, m, hn, hm, h.symm⟩
  trans := fun ⟨m, n, hm, hn, h⟩ ⟨p, q, hp, hq, h'⟩ =>
    ⟨p * m, n * q, Nat.mul_pos hp hm, Nat.mul_pos hn hq, by
      rw [mul_smul, h, ← mul_smul, mul_comm p n, mul_smul, h', ← mul_smul]⟩

/-- The setoid of rays. -/
def raySetoid : Setoid (Additive X) := ⟨SameRayRel, sameRayRel_equivalence⟩

variable (π : H →ₐc[k] MonoidAlgebra k X)

/-- The `f`-positive roots, as a finset. -/
noncomputable def posRoots (f : Additive X →+ ℤ) : Finset (Additive X) :=
  (finite_roots (π := π)).toFinset.filter (fun α => 0 < f α)

/-- `dim Lie U(λ_f) = ∑_{f α > 0} dim 𝔤_α`. -/
noncomputable def posDim (f : Additive X →+ ℤ) : ℕ :=
  ∑ α ∈ posRoots π f, Module.finrank k (Derivation.adjointWeightSpace π (Additive.toMul α))

/-- The number of rays of `f`-positive roots. -/
noncomputable def posRays (f : Additive X →+ ℤ) : ℕ := by
  classical
  exact ((posRoots π f).image (Quotient.mk (raySetoid (X := X)))).card

omit [DecidableEq X] in
lemma finrank_pos_of_mem_roots {α : Additive X} (hα : α ∈ roots π) :
    0 < Module.finrank k (Derivation.adjointWeightSpace π (Additive.toMul α)) :=
  Module.finrank_pos_iff.2 (Submodule.nontrivial_iff_ne_bot.2 hα.2)

omit [DecidableEq X] in
/-- **Counting.** If `posDim f ≤ posRays f`, every `f`-positive root space is a line and each
ray contains a single `f`-positive root. -/
theorem count_of_posDim_le (f : Additive X →+ ℤ) (hD : posDim π f ≤ posRays π f) :
    (∀ α ∈ posRoots π f,
        Module.finrank k (Derivation.adjointWeightSpace π (Additive.toMul α)) = 1) ∧
      ∀ α ∈ posRoots π f, ∀ β ∈ posRoots π f, SameRayRel α β → α = β := by
  classical
  set S := posRoots π f
  set d : Additive X → ℕ := fun α =>
    Module.finrank k (Derivation.adjointWeightSpace π (Additive.toMul α))
  have hd1 : ∀ α ∈ S, 1 ≤ d α := fun α hα =>
    finrank_pos_of_mem_roots π (by
      simp only [S, posRoots, Finset.mem_filter, Set.Finite.mem_toFinset] at hα
      exact hα.1)
  have hsum : S.card ≤ ∑ α ∈ S, d α := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum hd1
  have himg : (S.image (Quotient.mk (raySetoid (X := X)))).card ≤ S.card := Finset.card_image_le
  have hD' : ∑ α ∈ S, d α ≤ (S.image (Quotient.mk (raySetoid (X := X)))).card := by
    have := hD
    simp only [posDim, posRays] at this
    convert this
  have hcard : (S.image (Quotient.mk (raySetoid (X := X)))).card = S.card := by omega
  have hinj := Finset.card_image_iff.1 hcard
  have hsumeq : ∑ α ∈ S, d α = ∑ α ∈ S, 1 := by
    rw [← Finset.card_eq_sum_ones]; omega
  have heach := (Finset.sum_eq_sum_iff_of_le hd1).1 hsumeq.symm
  refine ⟨fun α hα => (heach α hα).symm, fun α hα β hβ hr => ?_⟩
  exact hinj hα hβ (Quotient.sound hr)

omit [DecidableEq X] [Module.Finite k (Bialgebra.CotangentSpace k H)] in
lemma pos_of_sameRay {f : Additive X →+ ℤ} {α β : Additive X} (h : SameRayRel α β)
    (hα : 0 < f α) : 0 < f β := by
  obtain ⟨m, n, hm, hn, h⟩ := h
  have := congrArg f h
  rw [map_nsmul, map_nsmul, nsmul_eq_mul, nsmul_eq_mul] at this
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  nlinarith

omit [DecidableEq X] [Module.Finite k (Bialgebra.CotangentSpace k H)] in
/-- From `n β = m α` with `n m > 0`, the same ray. -/
lemma sameRay_of_zsmul {α β : Additive X} {m n : ℤ} (h : n • β = m • α) (hmn : 0 < n * m) :
    SameRayRel β α := by
  rcases lt_or_gt_of_ne (show n ≠ 0 by rintro rfl; simp at hmn) with hn | hn
  · have hm : m < 0 := by nlinarith
    refine ⟨n.natAbs, m.natAbs, by omega, by omega, ?_⟩
    have h' : (-n) • β = (-m) • α := by rw [neg_smul, neg_smul, h]
    have e1 : ((n.natAbs : ℤ)) = -n := by omega
    have e2 : ((m.natAbs : ℤ)) = -m := by omega
    rw [← natCast_zsmul, ← natCast_zsmul, e1, e2, h']
  · have hm : 0 < m := by nlinarith
    refine ⟨n.natAbs, m.natAbs, by omega, by omega, ?_⟩
    have e1 : ((n.natAbs : ℤ)) = n := by omega
    have e2 : ((m.natAbs : ℤ)) = m := by omega
    rw [← natCast_zsmul, ← natCast_zsmul, e1, e2, h]

/-- **(ii′) from Weyl elements and the dimension count** (Prop 6.1′ of S-proof.md, counting
part). The hypotheses `hD`, `hD'` say `dim U(±λ_f) ≤ #rays`; geometrically they are
`dim Y = dim U(±λ) = |Ψ^±|`. -/
theorem condII_of_counting [Module.IsTorsionFree ℤ (Additive X)] (f : Additive X →+ ℤ)
    (hf : ∀ α ∈ roots π, f α ≠ 0) (hD : posDim π f ≤ posRays π f)
    (hD' : posDim π (-f) ≤ posRays π (-f))
    (hW : ∀ α ∈ roots π, ∃ (n : WithConv (H →ₐ[k] k)) (σ : X ≃* X),
      IsNormalizingWith π k n σ ∧ σ (Additive.toMul α) = (Additive.toMul α)⁻¹) :
    ∀ α ∈ roots π,
      Module.finrank k (Derivation.adjointWeightSpace π (Additive.toMul α)) = 1 ∧
      ∀ β ∈ roots π, (∃ m n : ℤ, n ≠ 0 ∧ n • β = m • α) → β = α ∨ β = -α := by
  -- the two signs
  have key : ∀ g : Additive X →+ ℤ, posDim π g ≤ posRays π g → ∀ α ∈ roots π, 0 < g α →
      Module.finrank k (Derivation.adjointWeightSpace π (Additive.toMul α)) = 1 ∧
      ∀ β ∈ roots π, SameRayRel α β → α = β := by
    intro g hg α hα hgα
    obtain ⟨h1, h2⟩ := count_of_posDim_le π g hg
    have hαS : α ∈ posRoots π g := by
      simp only [posRoots, Finset.mem_filter, Set.Finite.mem_toFinset]; exact ⟨hα, hgα⟩
    refine ⟨h1 α hαS, fun β hβ hr => h2 α hαS β ?_ hr⟩
    simp only [posRoots, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨hβ, pos_of_sameRay hr hgα⟩
  have both : ∀ α ∈ roots π, Module.finrank k (Derivation.adjointWeightSpace π
      (Additive.toMul α)) = 1 ∧ ∀ β ∈ roots π, SameRayRel α β → α = β := by
    intro α hα
    rcases lt_or_gt_of_ne (hf α hα) with h | h
    · exact key (-f) hD' α hα (by simpa using h)
    · exact key f hD α hα h
  intro α hα
  refine ⟨(both α hα).1, fun β hβ ⟨m, n, hn, hnm⟩ => ?_⟩
  have hβ0 : β ≠ 0 := ne_zero_of_mem_roots hβ
  have hm : m ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hnm
    exact hβ0 ((smul_eq_zero_iff_right hn).1 hnm)
  rcases lt_or_gt_of_ne (mul_ne_zero hn hm) with hs | hs
  · -- opposite rays: `β` is on the ray of `-α`, a root by the Weyl element
    right
    obtain ⟨w, σ, hw, hσ⟩ := hW α hα
    have hneg : -α ∈ roots π := by
      have := mem_roots_of_isNormalizingWith π hw hα
      rwa [hσ] at this
    have hnm' : n • β = (-m) • (-α) := by rw [neg_smul_neg]; exact hnm
    have hr : SameRayRel β (-α) := sameRay_of_zsmul hnm' (by nlinarith)
    exact ((both β hβ).2 (-α) hneg hr)
  · left
    exact (both β hβ).2 α hα (sameRay_of_zsmul hnm hs)

/-- **(ii′) from Weyl elements and the dimension count, for every regular form.** The single
geometric input `hD` is `dim U(λ) ≤ #{λ-positive root rays}` for every regular `λ` (in S-proof.md:
`dim Y = dim U(λ)`, i.e. `V = 1`, and `dim Y = |Ψ⁺|`). -/
theorem condII_of_counting_of_forall [Module.IsTorsionFree ℤ (Additive X)]
    [Module.Finite ℤ (Additive X)]
    (hD : ∀ f : Additive X →+ ℤ, (∀ α ∈ roots π, f α ≠ 0) → posDim π f ≤ posRays π f)
    (hW : ∀ α ∈ roots π, ∃ (n : WithConv (H →ₐ[k] k)) (σ : X ≃* X),
      IsNormalizingWith π k n σ ∧ σ (Additive.toMul α) = (Additive.toMul α)⁻¹) :
    ∀ α ∈ roots π,
      Module.finrank k (Derivation.adjointWeightSpace π (Additive.toMul α)) = 1 ∧
      ∀ β ∈ roots π, (∃ m n : ℤ, n ≠ 0 ∧ n • β = m • α) → β = α ∨ β = -α := by
  have : Module.Free ℤ (Additive X) := Module.free_of_finite_type_torsion_free'
  obtain ⟨ψ, hψ⟩ := exists_generic_cocharacter (roots π) (finite_roots (π := π))
    (fun α hα => ne_zero_of_mem_roots hα)
  set f := pairingHom ψ
  have hf : ∀ α ∈ roots π, f α ≠ 0 := hψ
  have hf' : ∀ α ∈ roots π, (-f) α ≠ 0 := fun α hα => by simpa using hf α hα
  exact condII_of_counting π f hf (hD f hf) (hD (-f) hf') hW

end AlgMag.Reductive
