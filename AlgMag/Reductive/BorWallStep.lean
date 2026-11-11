/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.BorBase
import AlgMag.Reductive.FromR1R2
import AlgMag.Weyl.WeylGroup
import TauCeti.Algebra.AlgebraicGroup.Borel.Conjugation
import TauCeti.Algebra.AlgebraicGroup.Torus.Maximal
import AlgMag.Reductive.ForwardAssembly
import AlgMag.Reductive.RankOneReflectionAlt
import AlgMag.Reductive.R1Discharge
import TauCeti.Algebra.AlgebraicGroup.Borel.Conjugacy.Existence

/-!
# The wall step `WallStepπ` (Bor-plan §2, W5 + S0), modulo the wall-crossing Weyl element

* **W5, ideal form, weight-restricted by construction** (`parabolic_comp_eq_conjugate`, proved):
  for `n ∈ G(k)` normalizing `T` with automorphism `σ` of `X`,
  `P(λ_{ψ∘σ}) = n⁻¹ P(λ_ψ) n` as Hopf ideals (`(P ψ).conjugate n`), for **every** `ψ`.
  No condition on `ψ` is needed: both sides are attractors `G^{ψ⁻¹ℕ}`, `G^{(ψσ)⁻¹ℕ}` of the
  torus grading (`magnetIdeal_torusGrading_comap_nat`), and point conjugation by `n` moves the
  weight space `H_χ` into `H_{σχ}` (`pointConjugation_mem_torusGrading`). Only the weights of
  `k[G]` enter, so this is the weight-restricted form (the all-`χ` hypothesis `hσψ` of
  `conj_mem_parabolic_inv` is not used).
* `borInv_comp`: `BorInv ψ ⇒ BorInv (ψ∘σ)` (conjugate of a Borel is Borel, Tau Ceti).
* `borInv_of_sign_eq`: `BorInv` depends only on the signs on the tangent weights (S0).
* `wallStepπ_of_wallRefl` (proved): `WallStepπ` from `ParConn` (discharged by `parConn`) and the
  named `WallReflπ` (W1–W4 output: a point `n_β ∈ N_G(T)(k)` acting by `σ` with `σ` fixing the wall
  cocharacter `μ` and `σ = -1` on the line `ℚχ₀`, for `T = D(X)` a maximal torus). The sign
  analysis W4 and the choice `ν = Mμ + ψ`, `M ≫ 0`, `σν ∈ 𝒞'` are proved here, with the explicit
  wall cocharacter `μ = -⟨ψ',χ₀⟩⟨ψ,χ₀⟩ ψ + ⟨ψ,χ₀⟩² ψ'`.
* `wallRefl_of_wallGeom` (proved): `WallReflπ` from `WallGeomπ` (an `R1Geom` at `(χ₀, ψ)`) via
  T1-dyn/D6 (`r1_of_r1Datum`) and `isReflectionOn_of_mem_lineAttractor'` (`W(k)` finite by
  rigidity of tori; no `SplitReductiveData`, no (R1)).
* `wallGeom_of_borelZ` (proved): `WallGeomπ` from the named `BorelZπ` (L1b in `Z = G^{ℤχ₀}`:
  `P_Z(λ^{±1})` Borel in `Z`), with `P_Z(λ⁻¹) ≠ P_Z(λ)` proved (`parZ_ne`, via the Lie algebras
  of the attractors `G^{ψ^{±1}⁻¹ℕ ∩ ℤχ₀}` and an adjoint weight vector), by Borel conjugacy in `Z` (Tau Ceti),
  `exists_SQ`, `hCB_proof` and `parZ_eq_of_conjugate_eq`. `wallStepπ_of_borelZ` assembles.
* Maximality of `T` is needed in `WallReflπ`: for `G = SL₃` and `T' = λ(𝔾_m)`, `λ = (2,1,-3)`,
  `WallStepπ` holds but no `n` normalizes `T'` with `σ = -1`.
-/

suppress_compilation

open Magnetism TauCeti TauCeti.Cocharacter AlgMag.Weyl
open scoped TensorProduct

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X)

local notation "Hf" => FiniteTypeCommHopfAlgCat.of k H

omit [DecidableEq X] in
theorem pairingHom_comp (ψ : X →* Multiplicative ℤ) (σ : X ≃* X) (χ : Additive X) :
    pairingHom (ψ.comp σ.toMonoidHom) χ =
      pairingHom ψ (Additive.ofMul (σ (Additive.toMul χ))) := rfl

/-- **W5, one inclusion.** `P(λ_{ψ∘σ}) ≤ n⁻¹ P(λ_ψ) n` as Hopf ideals. -/
theorem parabolic_comp_le_conjugate {n : WithConv (H →ₐ[k] k)} {σ : X ≃* X}
    (hn : IsNormalizingWith π k n σ) (ψ : X →* Multiplicative ℤ) :
    parabolicDefiningHopfIdeal (π.cocharacter (ψ.comp σ.toMonoidHom)) ≤
      (parabolicDefiningHopfIdeal (π.cocharacter ψ)).conjugate n := by
  intro x hx
  rw [HopfIdeal.mem_conjugate]
  have hx' : x ∈ (parabolicDefiningHopfIdeal (π.cocharacter (ψ.comp σ.toMonoidHom))).toIdeal := hx
  change HopfAlgebra.pointConjugationAlgHom n x ∈
    (parabolicDefiningHopfIdeal (π.cocharacter ψ)).toIdeal
  rw [← magnetIdeal_torusGrading_comap_nat] at hx' ⊢
  have hle : magnetIdeal (torusGrading π) (natMagnet.comap (pairingHom (ψ.comp σ.toMonoidHom))) ≤
      Ideal.comap (HopfAlgebra.pointConjugationAlgHom n)
        (magnetIdeal (torusGrading π) (natMagnet.comap (pairingHom ψ))) := by
    rw [magnetIdeal, Ideal.span_le]
    simp only [Set.iUnion_subset_iff]
    intro χ hχ a ha
    have hmem := pointConjugation_mem_torusGrading π hn ha
    have hnot : Additive.ofMul (σ (Additive.toMul χ)) ∉ natMagnet.comap (pairingHom ψ) := hχ
    exact mem_magnetIdeal_of_notMem hnot hmem
  exact hle hx'

/-- **W5, ideal form.** For `n` normalizing `T` with `σ`, `P(λ_{ψ∘σ}) = n⁻¹ P(λ_ψ) n`. -/
theorem parabolic_comp_eq_conjugate {n : WithConv (H →ₐ[k] k)} {σ : X ≃* X}
    (hn : IsNormalizingWith π k n σ) (ψ : X →* Multiplicative ℤ) :
    parabolicDefiningHopfIdeal (π.cocharacter (ψ.comp σ.toMonoidHom)) =
      (parabolicDefiningHopfIdeal (π.cocharacter ψ)).conjugate n := by
  refine le_antisymm (parabolic_comp_le_conjugate π hn ψ) ?_
  have hinv := parabolic_comp_le_conjugate π (hn.inv π) (ψ.comp σ.toMonoidHom)
  have hψ : (ψ.comp σ.toMonoidHom).comp (σ⁻¹ : X ≃* X).toMonoidHom = ψ := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact congrArg ψ (σ.apply_symm_apply x)
  rw [hψ] at hinv
  have := HopfIdeal.conjugate_mono n hinv
  rwa [HopfIdeal.conjugate_conjugate_inv] at this

omit [DecidableEq X] in
theorem comp_inv (ψ : X →* Multiplicative ℤ) (σ : X ≃* X) :
    (ψ.comp σ.toMonoidHom)⁻¹ = ψ⁻¹.comp σ.toMonoidHom := by
  ext x; rfl

/-- `BorInv` is transported by a normalizing point: `BorInv ψ ⇒ BorInv (ψ∘σ)`. -/
theorem borInv_comp [Algebra.FiniteType k H] {n : WithConv (H →ₐ[k] k)} {σ : X ≃* X}
    (hn : IsNormalizingWith π k n σ) {ψ : X →* Multiplicative ℤ} (h : BorInv π ψ) :
    BorInv π (ψ.comp σ.toMonoidHom) := by
  refine ⟨?_, ?_⟩
  · rw [parabolic_comp_eq_conjugate π hn ψ]; exact h.1.conjugate n
  · rw [comp_inv, parabolic_comp_eq_conjugate π hn ψ⁻¹]; exact h.2.conjugate n

omit [DecidableEq X] in
theorem nonneg_iff_of_sign_eq {a b : ℤ} (h : Int.sign a = Int.sign b) : (0 ≤ a ↔ 0 ≤ b) := by
  rw [← Int.sign_nonneg_iff, h, Int.sign_nonneg_iff]

/-- `BorInv` only depends on the signs on the tangent weights (S0, twice). -/
theorem borInv_of_sign_eq [Algebra.FiniteType k H] [Algebra.Smooth k H] (hC : ParConn π)
    {φ φ' : X →* Multiplicative ℤ}
    (hs : ∀ χ ∈ tangentWeights π k, Int.sign (pairingHom φ' χ) = Int.sign (pairingHom φ χ))
    (hI : BorInv π φ) : BorInv π φ' := by
  have s1 : ∀ χ ∈ tangentWeights π k, (0 ≤ pairingHom φ χ ↔ 0 ≤ pairingHom φ' χ) := fun χ hχ =>
    (nonneg_iff_of_sign_eq (hs χ hχ)).symm
  have s2 : ∀ χ ∈ tangentWeights π k, (0 ≤ pairingHom φ⁻¹ χ ↔ 0 ≤ pairingHom φ'⁻¹ χ) := by
    intro χ hχ
    rw [borPairingHom_inv, borPairingHom_inv]
    refine (nonneg_iff_of_sign_eq ?_).symm
    rw [Int.sign_neg, Int.sign_neg, hs χ hχ]
  refine ⟨?_, ?_⟩
  · rw [← parabolic_eq_of_sameSigns π _ φ' s1 (hC _) (hC _)]; exact hI.1
  · rw [← parabolic_eq_of_sameSigns π _ φ'⁻¹ s2 (hC _) (hC _)]; exact hI.2

/-! ### W4 + "`σν ∈ 𝒞'` for `M ≫ 0`": reduction to the reflection `n_β` -/

/-- `χ` lies on the line `ℚ χ₀`. -/
def OnLine (χ₀ χ : Additive X) : Prop := ∃ a b : ℤ, a ≠ 0 ∧ a • χ = b • χ₀

omit [DecidableEq X] in
theorem onLine_zero (χ₀ : Additive X) : OnLine χ₀ 0 := ⟨1, 0, one_ne_zero, by simp⟩

omit [DecidableEq X] in
theorem OnLine.pairing {χ₀ χ : Additive X} (h : OnLine χ₀ χ) (φ : X →* Multiplicative ℤ) :
    ∃ a b : ℤ, a ≠ 0 ∧ a * pairingHom φ χ = b * pairingHom φ χ₀ := by
  obtain ⟨a, b, ha, hab⟩ := h
  refine ⟨a, b, ha, ?_⟩
  have := congrArg (pairingHom φ) hab
  rwa [map_zsmul, map_zsmul, smul_eq_mul, smul_eq_mul] at this

omit [DecidableEq X] in
theorem pairingHom_mul' (φ φ' : X →* Multiplicative ℤ) (χ : Additive X) :
    pairingHom (φ * φ') χ = pairingHom φ χ + pairingHom φ' χ := rfl

omit [DecidableEq X] in
theorem pairingHom_zpow' (φ : X →* Multiplicative ℤ) (z : ℤ) (χ : Additive X) :
    pairingHom (φ ^ z) χ = z * pairingHom φ χ := by
  rw [pairingHom_apply, pairingHom_apply, MonoidHom.zpow_apply, toAdd_zpow, smul_eq_mul]

omit [DecidableEq X] in
theorem sign_eq_of_order {x y : ℤ} (h1 : 0 < x ↔ 0 < y) (h2 : x < 0 ↔ y < 0) :
    Int.sign x = Int.sign y := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rw [Int.sign_eq_neg_one_of_neg hx, Int.sign_eq_neg_one_of_neg (h2.1 hx)]
  · have hy : y = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have := h2.2 h; omega
      · have := h1.2 h; omega
    rw [hx, hy]
  · rw [Int.sign_eq_one_of_pos hx, Int.sign_eq_one_of_pos (h1.1 hx)]

omit [DecidableEq X] in
theorem order_dom {M m e : ℤ} (hm : m ≠ 0) (he : |e| < M) :
    (0 < M * m + e ↔ 0 < m) ∧ (M * m + e < 0 ↔ m < 0) := by
  have h1 := abs_lt.mp he
  rcases lt_or_gt_of_ne hm with h | h
  · have ht : M * m ≤ -M := by nlinarith
    generalize M * m = t at *
    constructor <;> constructor <;> intro <;> omega
  · have ht : M ≤ M * m := by nlinarith
    generalize M * m = t at *
    constructor <;> constructor <;> intro <;> omega

/-- **W1–W4 (named), reflection form.** For `G` reductive, a regular `ψ` with `BorInv ψ`, a nonzero
tangent weight `χ₀`, and `μ ⊥ χ₀` on the wall of the chamber of `ψ` (same signs as `ψ` off the
line `ℚχ₀`, in particular generic on that wall), there is `n ∈ N_G(T)(k)` acting by `σ` with
`σ` fixing `μ` and `σ = -1` on the line `ℚχ₀` (for `ψ`): the wall-crossing Weyl element
`n_β ∈ Z_G(μ) = G^{ℤβ}` of Bor-plan §2 (Levi, L1b, Borel conjugacy in `Z`, T1-dyn, `σ ≠ 1`).
Only the tangent weights enter (weight-restricted form). -/
def WallReflπ [Algebra.FiniteType k H] (hπ : Function.Surjective π) : Prop :=
  reductiveCommHopfAlgProperty k Hf →
    HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) (HopfIdeal.kerOfSurjective π hπ) →
    ∀ (ψ μ : X →* Multiplicative ℤ) (χ₀ : Additive X),
    RegCochar π ψ → BorInv π ψ → χ₀ ∈ tangentWeights π k → χ₀ ≠ 0 → pairingHom μ χ₀ = 0 →
    (∀ χ ∈ tangentWeights π k, ¬ OnLine χ₀ χ →
      pairingHom μ χ ≠ 0 ∧ Int.sign (pairingHom μ χ) = Int.sign (pairingHom ψ χ)) →
    ∃ (n : WithConv (H →ₐ[k] k)) (σ : X ≃* X), IsNormalizingWith π k n σ ∧
      (∀ χ ∈ tangentWeights π k,
        pairingHom μ (Additive.ofMul (σ (Additive.toMul χ))) = pairingHom μ χ) ∧
      (∀ χ ∈ tangentWeights π k, OnLine χ₀ χ →
        pairingHom ψ (Additive.ofMul (σ (Additive.toMul χ))) = - pairingHom ψ χ)

/-- **The wall step from the reflection** (W4 sign analysis, `ν = Mμ + ψ` with `M ≫ 0`,
`σν ∈ 𝒞'`, W5, S0). -/
theorem wallStepπ_of_wallRefl [Algebra.FiniteType k H] [Algebra.Smooth k H]
    (hπ : Function.Surjective π)
    (hmax : HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) (HopfIdeal.kerOfSurjective π hπ))
    (hC : ParConn π) (hW : WallReflπ π hπ) : WallStepπ π := by
  intro hred ψ ψ' hψ hψ' hadj hI
  rcases (diffSet π ψ ψ').eq_empty_or_nonempty with he | ⟨χ₀, hχ₀⟩
  · obtain ⟨s1, s2⟩ := sameSigns_of_diffSet_empty π hψ hψ' he
    exact ⟨by rw [← parabolic_eq_of_sameSigns π ψ ψ' s1 (hC _) (hC _)]; exact hI.1,
      by rw [← parabolic_eq_of_sameSigns π ψ⁻¹ ψ'⁻¹ s2 (hC _) (hC _)]; exact hI.2⟩
  obtain ⟨β, hβ⟩ := hadj
  have hΦ0 := hχ₀.1
  have hd0 := hχ₀.2
  have hne0 : χ₀ ≠ 0 := by rintro rfl; apply hd0; simp
  have ha0 : pairingHom ψ χ₀ ≠ 0 := hψ χ₀ hΦ0 hne0
  have hb0 : pairingHom ψ' χ₀ ≠ 0 := hψ' χ₀ hΦ0 hne0
  set a0 := pairingHom ψ χ₀ with ha0def
  set b0 := pairingHom ψ' χ₀ with hb0def
  have hab : a0 * b0 < 0 := by
    rcases lt_or_gt_of_ne ha0 with h1 | h1 <;> rcases lt_or_gt_of_ne hb0 with h2 | h2
    · exact absurd ⟨fun _ => by omega, fun _ => by omega⟩ hd0
    · exact mul_neg_of_neg_of_pos h1 h2
    · exact mul_neg_of_pos_of_neg h1 h2
    · exact absurd ⟨fun _ => by omega, fun _ => by omega⟩ hd0
  -- every sign change lies on the line `ℚ χ₀`
  obtain ⟨c, d, -, hd, hcd⟩ := hβ χ₀ hχ₀
  have hF1 : ∀ χ ∈ diffSet π ψ ψ', OnLine χ₀ χ := by
    intro χ hχ
    obtain ⟨a, b, ha, -, hab'⟩ := hβ χ hχ
    refine ⟨d * a, b * c, mul_ne_zero hd ha, ?_⟩
    rw [mul_smul, hab', mul_smul, hcd, smul_comm]
  -- off the line, `ψ` and `ψ'` have the same strict signs
  have hoff : ∀ χ ∈ tangentWeights π k, ¬ OnLine χ₀ χ →
      pairingHom ψ χ ≠ 0 ∧ (0 < pairingHom ψ χ ↔ 0 < pairingHom ψ' χ) ∧
        (pairingHom ψ χ < 0 ↔ pairingHom ψ' χ < 0) := by
    intro χ hχ hl
    have h0 : χ ≠ 0 := by rintro rfl; exact hl (onLine_zero χ₀)
    have hs : (0 ≤ pairingHom ψ χ ↔ 0 ≤ pairingHom ψ' χ) := by
      by_contra hc; exact hl (hF1 χ ⟨hχ, hc⟩)
    have a := hψ χ hχ h0
    have b := hψ' χ hχ h0
    exact ⟨a, by constructor <;> intro <;> omega, by constructor <;> intro <;> omega⟩
  -- the wall cocharacter `μ = (-b₀a₀) ψ + a₀² ψ'`
  set μ : X →* Multiplicative ℤ := ψ ^ (-(b0 * a0)) * ψ' ^ (a0 * a0) with hμdef
  have hμ : ∀ χ, pairingHom μ χ = -(b0 * a0) * pairingHom ψ χ + a0 * a0 * pairingHom ψ' χ :=
    fun χ => by rw [hμdef, pairingHom_mul', pairingHom_zpow', pairingHom_zpow']
  have hμ0 : pairingHom μ χ₀ = 0 := by rw [hμ]; ring
  have hc1 : 0 < -(b0 * a0) := by nlinarith
  have hc2 : 0 < a0 * a0 := mul_self_pos.mpr ha0
  have hμon : ∀ χ, OnLine χ₀ χ → pairingHom μ χ = 0 := by
    intro χ hl
    obtain ⟨a, b, ha, hab'⟩ := hl.pairing μ
    rw [hμ0, mul_zero] at hab'
    exact (mul_eq_zero.1 hab').resolve_left ha
  have hμoff : ∀ χ ∈ tangentWeights π k, ¬ OnLine χ₀ χ →
      pairingHom μ χ ≠ 0 ∧ (0 < pairingHom μ χ ↔ 0 < pairingHom ψ χ) ∧
        (pairingHom μ χ < 0 ↔ pairingHom ψ χ < 0) := by
    intro χ hχ hl
    obtain ⟨hx0, h1, h2⟩ := hoff χ hχ hl
    rw [hμ]
    rcases lt_or_gt_of_ne hx0 with hx | hx
    · have hy := h2.1 hx
      have e1 := mul_neg_of_pos_of_neg hc1 hx
      have e2 := mul_neg_of_pos_of_neg hc2 hy
      exact ⟨by linarith, ⟨fun _ => by linarith, fun _ => by linarith⟩,
        ⟨fun _ => hx, fun _ => by linarith⟩⟩
    · have hy := h1.1 hx
      have e1 := mul_pos hc1 hx
      have e2 := mul_pos hc2 hy
      exact ⟨by linarith, ⟨fun _ => hx, fun _ => by linarith⟩,
        ⟨fun _ => by linarith, fun _ => by linarith⟩⟩
  obtain ⟨n, σ, hn, hσμ, hσψ⟩ := hW hred hmax ψ μ χ₀ hψ hI hΦ0 hne0 hμ0 (fun χ hχ hl => by
    obtain ⟨h0, h1, h2⟩ := hμoff χ hχ hl
    exact ⟨h0, sign_eq_of_order h1 h2⟩)
  -- the bound `M`
  obtain ⟨B, hB⟩ := ((finite_tangentWeights π).image (fun χ =>
    |pairingHom ψ χ| + |pairingHom ψ (Additive.ofMul (σ (Additive.toMul χ)))|)).bddAbove
  have hbd : ∀ χ ∈ tangentWeights π k, |pairingHom ψ χ| < |B| + 1 ∧
      |pairingHom ψ (Additive.ofMul (σ (Additive.toMul χ)))| < |B| + 1 := by
    intro χ hχ
    have h1 : |pairingHom ψ χ| + |pairingHom ψ (Additive.ofMul (σ (Additive.toMul χ)))| ≤ B :=
      hB ⟨χ, hχ, rfl⟩
    have h2 := le_abs_self B
    have h3 := abs_nonneg (pairingHom ψ χ)
    have h4 := abs_nonneg (pairingHom ψ (Additive.ofMul (σ (Additive.toMul χ))))
    constructor <;> linarith
  set M : ℤ := |B| + 1 with hMdef
  set ν : X →* Multiplicative ℤ := μ ^ M * ψ with hνdef
  have hν : ∀ χ, pairingHom ν χ = M * pairingHom μ χ + pairingHom ψ χ :=
    fun χ => by rw [hνdef, pairingHom_mul', pairingHom_zpow']
  -- `ν` is in the chamber of `ψ`
  have hE1 : ∀ χ ∈ tangentWeights π k, Int.sign (pairingHom ν χ) = Int.sign (pairingHom ψ χ) := by
    intro χ hχ
    by_cases hl : OnLine χ₀ χ
    · rw [hν, hμon χ hl, mul_zero, zero_add]
    · obtain ⟨h0, h1, h2⟩ := hμoff χ hχ hl
      obtain ⟨d1, d2⟩ := order_dom h0 (hbd χ hχ).1
      rw [hν]
      exact sign_eq_of_order (d1.trans h1) (d2.trans h2)
  -- `ν ∘ σ` is in the chamber of `ψ'`
  have hsb : Int.sign b0 = - Int.sign a0 := by
    rcases lt_or_gt_of_ne ha0 with h | h
    · have : 0 < b0 := by
        by_contra hc; replace hc := not_lt.1 hc
        have := mul_nonneg_of_nonpos_of_nonpos h.le hc; linarith
      rw [Int.sign_eq_neg_one_of_neg h, Int.sign_eq_one_of_pos this]; rfl
    · have : b0 < 0 := by
        by_contra hc; replace hc := not_lt.1 hc
        have := mul_nonneg h.le hc; linarith
      rw [Int.sign_eq_one_of_pos h, Int.sign_eq_neg_one_of_neg this]
  have hE2 : ∀ χ ∈ tangentWeights π k,
      Int.sign (pairingHom ψ' χ) = Int.sign (pairingHom (ν.comp σ.toMonoidHom) χ) := by
    intro χ hχ
    rw [pairingHom_comp, hν, hσμ χ hχ]
    by_cases hl : OnLine χ₀ χ
    · rw [hμon χ hl, mul_zero, zero_add, hσψ χ hχ hl, Int.sign_neg]
      obtain ⟨a, b, ha, e⟩ := hl
      have ex : a * pairingHom ψ χ = b * a0 := by
        have := congrArg (pairingHom ψ) e
        rwa [map_zsmul, map_zsmul, smul_eq_mul, smul_eq_mul] at this
      have ey : a * pairingHom ψ' χ = b * b0 := by
        have := congrArg (pairingHom ψ') e
        rwa [map_zsmul, map_zsmul, smul_eq_mul, smul_eq_mul] at this
      have sx := congrArg Int.sign ex
      have sy := congrArg Int.sign ey
      rw [Int.sign_mul, Int.sign_mul] at sx sy
      rw [hsb] at sy
      have hsa : Int.sign a ≠ 0 := by
        intro h; exact ha (Int.sign_eq_zero_iff_zero.1 h)
      have hsum : Int.sign a * (Int.sign (pairingHom ψ' χ) + Int.sign (pairingHom ψ χ)) = 0 := by
        rw [mul_add, sy, sx]; ring
      have := (mul_eq_zero.1 hsum).resolve_left hsa
      linarith
    · obtain ⟨h0, h1, h2⟩ := hμoff χ hχ hl
      obtain ⟨-, g1, g2⟩ := hoff χ hχ hl
      obtain ⟨d1, d2⟩ := order_dom h0 (hbd χ hχ).2
      exact sign_eq_of_order (g1.symm.trans (h1.symm.trans d1.symm))
        (g2.symm.trans (h2.symm.trans d2.symm))
  have hIν : BorInv π ν := borInv_of_sign_eq π hC hE1 hI
  exact borInv_of_sign_eq π hC hE2 (borInv_comp π hn hIν)

/-- **The wall step from the reflection**, `G` smooth and geometrically connected. -/
theorem wallStepπ_of_wallRefl' [Algebra.FiniteType k H] [Algebra.Smooth k H]
    [ConnectedSpace (PrimeSpectrum (AlgebraicClosure k ⊗[k] H))]
    (hπ : Function.Surjective π)
    (hmax : HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) (HopfIdeal.kerOfSurjective π hπ))
    (hW : WallReflπ π hπ) : WallStepπ π :=
  wallStepπ_of_wallRefl π hπ hmax (parConn π) hW

/-! ### Optional discharge of `WallReflπ` from `SplitReductiveData.WithReflections`

CAUTION (circularity): `WithReflections` is built from (R1) (`WithReflections.ofLineAttractor`),
while Bor-plan §1.3 wants (R1) as a by-product of (Base±) ⇒ (Bor). Use this only where (R1) is
already available. -/

theorem wallRefl_of_withReflections [Algebra.FiniteType k H] [Module.IsTorsionFree ℤ (Additive X)]
    (D : SplitReductiveData.WithReflections π) (hπ : Function.Surjective π) :
    WallReflπ π hπ := by
  intro _ _ ψ μ χ₀ _ _ hΦ hne hμ0 _
  have hα : χ₀ ∈ roots π := (mem_tangentWeights_iff_mem_roots hne).1 hΦ
  let α : roots π := ⟨χ₀, hα⟩
  refine ⟨D.rep (D.refl α), (D.refl α : X ≃* X), D.rep_normalizing _, ?_, ?_⟩
  · intro χ _
    have h := D.refl_smul α χ
    change pairingHom μ ((D.refl α) • χ) = _
    rw [h, map_sub, map_zsmul, show pairingHom μ (α : Additive X) = 0 from hμ0, smul_zero,
      sub_zero]
  · rintro χ _ ⟨a, b, ha, hab⟩
    have h1 : a • ((D.refl α) • χ) = b • (-(α : Additive X)) := by
      rw [← D.smul_zsmul', hab, D.smul_zsmul', D.refl_smul_self]
    have h2 := congrArg (pairingHom ψ) h1
    rw [map_zsmul, map_zsmul, map_neg, smul_eq_mul, smul_eq_mul] at h2
    have h3 := congrArg (pairingHom ψ) hab
    rw [map_zsmul, map_zsmul, smul_eq_mul, smul_eq_mul] at h3
    change pairingHom ψ ((D.refl α) • χ) = _
    have h4 : a * (pairingHom ψ ((D.refl α) • χ) + pairingHom ψ χ) = 0 := by
      rw [mul_add, h2, h3]; simp [α]
    have := (mul_eq_zero.1 h4).resolve_left ha
    linarith

/-! ### W1–W4 via the (R1) machinery: `R1Geom` (named W1–W3) + rank-one reflection

`R1Geom π χ₀ ψ hπ` (ForwardAssembly) packages, inside `Z = G^{ℤχ₀}` and `B⁺ = P_Z(λ_ψ)`, the
element `g ∈ Z(k)` with `g T g⁻¹ ⊆ B⁺` a maximal torus and `b g ∉ C(k)`: in Bor-plan terms,
`g = z` from Borel conjugacy in `Z` (`P_Z(-λ) = z P_Z(λ) z⁻¹`, needs L1b) and `notC` from
`P_Z(λ) ≠ P_Z(-λ)`. Then T1-dyn (`r1_of_r1Datum`) gives `n = u z ∈ N_Z(T)(k)`, `σ ≠ 1`, and the
rank-one lemma `isReflectionOn_of_mem_lineAttractor` (`W` finite) makes `σ` the reflection at
`χ₀`, which fixes `μ ⊥ χ₀` and is `-1` on `ℚχ₀`. -/

section R1Route

variable [IsAlgClosed k]

local instance zDec' (α : Additive X) : DecidableEq (ZAlg π α) := Classical.decEq _
local instance zSmooth' [Algebra.FiniteType k H] [Algebra.Smooth k H] (α : Additive X) :
    Algebra.Smooth k (ZAlg π α) := smooth_quotient_magnetHopfIdeal π _

/-- **W1–W3 (named)**: for `G` reductive, `ψ` regular with `BorInv ψ` and a root `χ₀`, the
(R1) geometric datum `R1Geom` at `(χ₀, ψ)` (Levi `Z = G^{ℤχ₀}`, L1b, Borel conjugacy in `Z`). -/
def WallGeomπ [Algebra.FiniteType k H] [Algebra.Smooth k H] (hπ : Function.Surjective π) : Prop :=
  reductiveCommHopfAlgProperty k Hf → ∀ (ψ : X →* Multiplicative ℤ) (χ₀ : Additive X),
    RegCochar π ψ → BorInv π ψ → χ₀ ∈ roots π → Nonempty (R1Geom π χ₀ ψ hπ)

omit [IsAlgClosed k] in
/-- **Rank-one reflection without `SplitReductiveData`**: `W(k) = weylGroup π k` is finite by
rigidity of tori (`finite_weylImage`), so a point of `N_G(T)(k) ∩ G^{ℤα}(k)` with `σ ≠ 1` acts by
a reflection at the root `α`. -/
theorem isReflectionOn_of_mem_lineAttractor' [Algebra.FiniteType k H]
    [Module.IsTorsionFree ℤ (Additive X)] (hπ : Function.Surjective π) {α : Additive X}
    (hα : α ∈ roots π) {n : WithConv (H →ₐ[k] k)} {σ : X ≃* X}
    (hn : IsNormalizingWith π k n σ) (hnα : n ∈ attractorSubgroup π (lineMagnet α) k)
    (hσ : σ ≠ 1) : IsReflectionOn σ α := by
  have hrefl := (mem_lineAttractor_iff hπ hn α).1 hnα
  have : Algebra.FiniteType k (MonoidAlgebra k X) :=
    Algebra.FiniteType.of_surjective π.toAlgHom hπ
  have : Monoid.FG X := MonoidAlgebra.fg_of_finiteType (R := k)
  have : Group.FG X := Group.fg_iff_monoid_fg.mpr inferInstance
  have hσW : σ ∈ weylGroup π k := ⟨n, hn⟩
  have : Finite (weylGroup π k) := (finite_weylImage π hπ k).to_subtype
  have hne : (⟨σ, hσW⟩ : weylGroup π k) ≠ 1 := fun h1 => hσ (congrArg Subtype.val h1)
  exact ⟨LatticeReflection.smul_self_eq_neg (G := weylGroup π k) (w := ⟨σ, hσW⟩)
    (fun _ _ h => weyl_ext h)
    (ne_zero_of_mem_roots hα) hrefl hne, hrefl⟩

/-- **`WallReflπ` from `WallGeomπ`** (T1-dyn + D6 via `r1_of_r1Datum`, then the rank-one
reflection, `W(k)` finite by rigidity). -/
theorem wallRefl_of_wallGeom [Algebra.FiniteType k H] [Algebra.Smooth k H]
    [Module.IsTorsionFree ℤ (Additive X)]
    (hπ : Function.Surjective π) (hG : WallGeomπ π hπ) : WallReflπ π hπ := by
  intro hred hmax ψ μ χ₀ hψ hI hΦ hne hμ0 _
  have hα : χ₀ ∈ roots π := (mem_tangentWeights_iff_mem_roots hne).1 hΦ
  obtain ⟨G⟩ := hG hred ψ χ₀ hψ hI hα
  obtain ⟨n, σ, hn, hnα, hσ⟩ :=
    r1_of_r1Datum π hπ (G.toR1Datum π χ₀ ψ hmax (hψ χ₀ hΦ hne))
  have hR := isReflectionOn_of_mem_lineAttractor' π hπ hα hn hnα hσ
  refine ⟨n, σ, hn, ?_, ?_⟩
  · intro χ _
    obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.1 (hR.2 χ)
    have h := congrArg (pairingHom μ) hm
    rw [map_zsmul, hμ0, smul_zero, map_sub] at h
    change pairingHom μ (actW σ χ) = _
    linarith
  · rintro χ _ ⟨a, b, ha, hab⟩
    have h1 : a • actW σ χ = b • (-χ₀) := by
      rw [← map_zsmul, hab, map_zsmul, hR.1]
    have h2 := congrArg (pairingHom ψ) h1
    rw [map_zsmul, map_zsmul, map_neg, smul_eq_mul, smul_eq_mul] at h2
    have h3 := congrArg (pairingHom ψ) hab
    rw [map_zsmul, map_zsmul, smul_eq_mul, smul_eq_mul] at h3
    change pairingHom ψ (actW σ χ) = _
    have h4 : a * (pairingHom ψ (actW σ χ) + pairingHom ψ χ) = 0 := by
      rw [mul_add, h2, h3]; ring
    have := (mul_eq_zero.1 h4).resolve_left ha
    linarith

/-- **`WallStepπ` from `WallGeomπ`** (`G` smooth, geometrically connected, `T` maximal). -/
theorem wallStepπ_of_wallGeom [Algebra.FiniteType k H] [Algebra.Smooth k H]
    [ConnectedSpace (PrimeSpectrum (AlgebraicClosure k ⊗[k] H))]
    [Module.IsTorsionFree ℤ (Additive X)]
    (hπ : Function.Surjective π)
    (hmax : HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) (HopfIdeal.kerOfSurjective π hπ))
    (hG : WallGeomπ π hπ) : WallStepπ π :=
  wallStepπ_of_wallRefl' π hπ hmax (wallRefl_of_wallGeom π hπ hG)

omit [IsAlgClosed k] in
lemma mem_points_of_mem_range_mk {Q : Type u} [CommRing Q] [HopfAlgebra k Q] (I : HopfIdeal k Q)
    {x : WithConv (Q →ₐ[k] k)}
    (hx : x ∈ Set.range (BialgHom.mapDomain (A := k) (Bialgebra.Quotient.mkBialgHom I.toIdeal))) :
    x ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k Q) I
      (CommAlgCat.of k k) := by
  obtain ⟨s, rfl⟩ := hx
  rw [TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
  intro y hy
  rw [BialgHom.mapDomain_apply, WithConv.ofConv_toConv, AlgHom.comp_apply]
  have : (Bialgebra.Quotient.mkBialgHom (R := k) I.toIdeal : Q →ₐ[k] Q ⧸ I.toIdeal) y = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 hy
  rw [this, map_zero]

omit [IsAlgClosed k] in
lemma mem_range_mk_of_mem_points {Q : Type u} [CommRing Q] [HopfAlgebra k Q] (I : HopfIdeal k Q)
    {x : WithConv (Q →ₐ[k] k)}
    (hx : x ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k Q) I
      (CommAlgCat.of k k)) :
    x ∈ Set.range (BialgHom.mapDomain (A := k) (Bialgebra.Quotient.mkBialgHom I.toIdeal)) := by
  have hle : I.toIdeal ≤ RingHom.ker x.ofConv := fun y hy =>
    (TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).1 hx y hy
  refine ⟨WithConv.toConv (Ideal.Quotient.liftₐ _ x.ofConv fun a ha => hle ha), ?_⟩
  apply WithConv.ofConv_injective
  ext a
  rw [BialgHom.mapDomain_apply, WithConv.ofConv_toConv]
  rfl

open R1Build in
/-- If a point `z` of `P_Z(λ)` conjugates `P_Z(λ⁻¹)` onto `P_Z(λ)`, then `P_Z(λ⁻¹) = P_Z(λ)`
(same `k`-points, both quotients smooth hence reduced; separation by points). -/
theorem parZ_eq_of_conjugate_eq [Algebra.FiniteType k H] [Algebra.Smooth k H] (α : Additive X)
    (ψ : X →* Multiplicative ℤ) (z : WithConv (ZAlg π α →ₐ[k] k))
    (hzr : z ∈ Set.range (BialgHom.mapDomain (A := k) (fB π α ψ)))
    (hz : (parabolicDefiningHopfIdeal (zCochar π α ψ).oppositeCocharacter).conjugate z =
      parabolicDefiningHopfIdeal (zCochar π α ψ)) :
    parabolicDefiningHopfIdeal (zCochar π α ψ).oppositeCocharacter =
      parabolicDefiningHopfIdeal (zCochar π α ψ) := by
  have hzP := mem_points_of_mem_range_mk _ hzr
  have key : ∀ x, x ∈ CommHopfAlgCat.quotientPointsSubgroup
        (_root_.CommHopfAlgCat.of k (ZAlg π α))
        (parabolicDefiningHopfIdeal (zCochar π α ψ).oppositeCocharacter) (CommAlgCat.of k k) ↔
      x ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k (ZAlg π α))
        (parabolicDefiningHopfIdeal (zCochar π α ψ)) (CommAlgCat.of k k) := by
    intro x
    have h := TauCeti.CommHopfAlgCat.pointConjugation_mem_conjugate_iff
      (parabolicDefiningHopfIdeal (zCochar π α ψ).oppositeCocharacter) z (CommAlgCat.of k k) x
    rw [hz, R1Geometry.mapValue_ofId_self] at h
    rw [← h]
    constructor
    · intro hx
      have h1 := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hzP) hx) hzP
      have e : z⁻¹ * (z * x * z⁻¹) * z = x := by group
      rwa [e] at h1
    · intro hx
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hzP hx) (Subgroup.inv_mem _ hzP)
  have : Algebra.Smooth k (BAlg π α ψ) := smooth_parQuot (zCochar π α ψ)
  have : IsReduced (BAlg π α ψ) := isReduced_of_smooth k _
  have : Algebra.Smooth k (R1Opp.BmAlg π α ψ) :=
    smooth_parQuot (zCochar π α ψ).oppositeCocharacter
  have : IsReduced (R1Opp.BmAlg π α ψ) := isReduced_of_smooth k _
  refine le_antisymm ?_ ?_
  · exact HopfIdeal.le_of_quotientPointsSubgroup_le (k := k) (K := k)
      (H := _root_.CommHopfAlgCat.of k (ZAlg π α)) fun x hx => (key x).2 hx
  · exact HopfIdeal.le_of_quotientPointsSubgroup_le (k := k) (K := k)
      (H := _root_.CommHopfAlgCat.of k (ZAlg π α)) fun x hx => (key x).1 hx

open R1Build R1Opp R1Dis in
/-- **W2–W3: `R1Geom` from Borel conjugacy in `Z`.** If `P_Z(λ)`, `P_Z(λ⁻¹)` are Borel in
`Z = G^{ℤα}` (L1b), Tau Ceti Borel conjugacy gives `z ∈ Z(k)` with `P_Z(λ⁻¹)^z = P_Z(λ)`, so
`z T z⁻¹ ⊆ P_Z(λ)` (as `T ⊆ P_Z(λ⁻¹)`), a maximal torus (`exists_SQ`); `notC` holds as soon as no
`P_Z(λ) ≠ P_Z(λ⁻¹)` (`hne`; a point of `P_Z(λ)` conjugating `P_Z(λ⁻¹)` onto `P_Z(λ)` would force
equality, `parZ_eq_of_conjugate_eq`). -/
theorem r1Geom_of_borelZ [Algebra.FiniteType k H] [Algebra.Smooth k H] (α : Additive X)
    (ψ : X →* Multiplicative ℤ) (hπ : Function.Surjective π)
    (hT : HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H)
      (HopfIdeal.kerOfSurjective π hπ))
    (hBp : HopfIdeal.IsBorelOverAlgClosed k (FiniteTypeCommHopfAlgCat.of k (ZAlg π α))
      (parabolicDefiningHopfIdeal (zCochar π α ψ)))
    (hBm : HopfIdeal.IsBorelOverAlgClosed k (FiniteTypeCommHopfAlgCat.of k (ZAlg π α))
      (parabolicDefiningHopfIdeal (zCochar π α ψ).oppositeCocharacter))
    (hne : parabolicDefiningHopfIdeal (zCochar π α ψ).oppositeCocharacter ≠
      parabolicDefiningHopfIdeal (zCochar π α ψ)) :
    Nonempty (R1Geom π α ψ hπ) := by
  obtain ⟨z, hz⟩ := HopfIdeal.IsBorelOverAlgClosed.exists_conjugate_eq hBm hBp
  have hin : ∀ t ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k (ZAlg π α))
      (TZ π α ψ hπ) (CommAlgCat.of k k),
      z * t * z⁻¹ ∈ Set.range (BialgHom.mapDomain (A := k) (fB π α ψ)) := by
    intro t ht
    have h1 := mem_points_of_mem_range_mk _ (hTB_opp π α ψ hπ t ht)
    have h2 :=
      (TauCeti.CommHopfAlgCat.pointConjugation_mem_conjugate_iff _ z (CommAlgCat.of k k) t).2 h1
    rw [hz, R1Geometry.mapValue_ofId_self] at h2
    exact mem_range_mk_of_mem_points _ h2
  obtain ⟨SQ, hSQ, hmax⟩ := R1Geometry.exists_SQ (TZ π α ψ hπ) (TZ_isMaximalTorus π α ψ hπ hT)
    (fB π α ψ) (fB_surjective π α ψ) z hin
  refine ⟨{ g := BialgHom.mapDomain (zMk π α) z
            g_mem := zMk_mem_attractor π α z
            SQ := SQ
            hSQ := isMaximalTorus_of_comapOfSurjective (fB π α ψ) (fB_surjective π α ψ) SQ hmax
            hS := ?_
            notC := ?_ }⟩
  · have h1 : SQ.comapOfSurjective (bMk π α ψ) (bMk_surjective π α ψ) =
        (SQ.comapOfSurjective (fB π α ψ) (fB_surjective π α ψ)).comapOfSurjective (zMk π α)
          (zMk_surjective π α) := by
      rw [HopfIdeal.comapOfSurjective_comapOfSurjective]; rfl
    rw [h1, hSQ, ← HopfIdeal.conjugate_comapOfSurjective, TZ_comap]
    rfl
  · intro b hb
    obtain ⟨c, hc⟩ := hCB_proof π α ψ (BialgHom.mapDomain (fB π α ψ) b * z)
      (by rw [map_mul, ← mapDomain_bMk]; exact hb)
    exact hne (parZ_eq_of_conjugate_eq π α ψ z ⟨b⁻¹ * c, by rw [map_mul, map_inv, hc]; group⟩ hz)

omit [IsAlgClosed k] in
/-- **Two attractors differing on a tangent weight are different.** If `χ₀` is a tangent weight,
`χ₀ ∈ N` and `χ₀ ∉ N'`, then `G^N ≠ G^{N'}`: an adjoint weight vector `D` of weight `χ₀` lies in
`Lie(G^N)` but not in `Lie(G^{N'})` (`mem_lieSubalgebra_magnetHopfIdeal_iff`). -/
theorem magnetIdeal_ne_of_tangentWeight [Algebra.FiniteType k H] {χ₀ : Additive X}
    (hχ : χ₀ ∈ tangentWeights π k) {N N' : Magnet (Additive X)} (h1 : χ₀ ∈ N) (h2 : χ₀ ∉ N') :
    magnetIdeal (torusGrading π) N ≠ magnetIdeal (torusGrading π) N' := by
  intro heq
  obtain ⟨x, hx, hx0⟩ :=
    (Submodule.ne_bot_iff _).1 ((mem_tangentWeights_iff_adjointWeightSpace_ne_bot χ₀).1 hχ)
  set D := Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k) x with hDdef
  have hvan : ∀ χ : Additive X, χ ≠ χ₀ → ∀ h ∈ torusGrading π χ, D h = 0 := by
    intro χ hne h hh
    refine cotangentLinearEquiv_eq_zero_of_mem_adjointWeightSpace hx ?_ hh
    intro e
    apply hne
    simpa using congrArg Additive.ofMul e
  have hD : D ∈ (magnetHopfIdeal π N).lieSubalgebra (B := k) := by
    rw [mem_lieSubalgebra_magnetHopfIdeal_iff]
    intro χ hχN h hh
    exact hvan χ (fun e => hχN (e ▸ h1)) h hh
  have hD' : D ∈ (magnetHopfIdeal π N').lieSubalgebra (B := k) := by
    rwa [lieSubalgebra_eq_of_toIdeal_eq (by rw [magnetHopfIdeal_toIdeal, magnetHopfIdeal_toIdeal,
      heq] : (magnetHopfIdeal π N).toIdeal = (magnetHopfIdeal π N').toIdeal)] at hD
  rw [mem_lieSubalgebra_magnetHopfIdeal_iff] at hD'
  have hall : ∀ a : H, D a = 0 := by
    intro a
    induction a using DirectSum.Decomposition.inductionOn (torusGrading π) with
    | zero => exact map_zero D
    | @homogeneous χ m =>
      obtain ⟨a, ha⟩ := m
      by_cases e : χ = χ₀
      · subst e; exact hD' χ h2 a ha
      · exact hvan χ e a ha
    | add a b ha hb => rw [map_add, ha, hb, add_zero]
  have hD0 : D = 0 := by ext a; exact hall a
  apply hx0
  apply (Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k)).injective
  rw [← hDdef, hD0, map_zero]

omit [IsAlgClosed k] in
/-- The dynamic parabolic of `l_Q` with `l_Q ∘ f = l`, `f` surjective, is the image of `P(l)`. -/
theorem parabolic_toIdeal_eq_map [Algebra.FiniteType k H] [Algebra.Smooth k H] {Q : Type u}
    [CommRing Q] [HopfAlgebra k Q] (f : H →ₐc[k] Q)
    (hf : Function.Surjective f) (l : H →ₐc[k] LaurentPolynomial k)
    (lQ : Q →ₐc[k] LaurentPolynomial k) (hl : lQ.comp f = l) :
    (parabolicDefiningHopfIdeal lQ).toIdeal =
      Ideal.map (f : H →ₐ[k] Q) (parabolicDefiningHopfIdeal l).toIdeal := by
  classical
  rw [parabolicDefiningHopfIdeal_toIdeal, parabolicDefiningHopfIdeal_toIdeal, Ideal.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨q, n, hn, rfl⟩
    obtain ⟨x, rfl⟩ := hf q
    refine ⟨(conjugationAlgHom l x).coeff n, ⟨x, n, hn, rfl⟩, ?_⟩
    rw [conjugationAlgHom_natural l f lQ hl x, AddMonoidAlgebra.coeff_mapAlgHom]
  · rintro ⟨_, ⟨x, n, hn, rfl⟩, rfl⟩
    refine ⟨f x, n, hn, ?_⟩
    rw [conjugationAlgHom_natural l f lQ hl x, AddMonoidAlgebra.coeff_mapAlgHom]

/-- **(b) `P_Z(λ⁻¹) ≠ P_Z(λ)`** for a tangent weight `α` with `⟨ψ, α⟩ ≠ 0`: pulled back to `G`,
both are attractors `G^{N±}`, `N± = ψ^{±1}⁻¹(ℕ) ∩ ℤα`, which differ on `α`. -/
theorem parZ_ne [Algebra.FiniteType k H] [Algebra.Smooth k H] (α : Additive X)
    (ψ : X →* Multiplicative ℤ) (hα : α ∈ tangentWeights π k) (hψα : pairingHom ψ α ≠ 0) :
    parabolicDefiningHopfIdeal (zCochar π α ψ).oppositeCocharacter ≠
      parabolicDefiningHopfIdeal (zCochar π α ψ) := by
  intro heq
  have hs := R1Build.zMk_surjective π α
  have e1 := parabolic_toIdeal_eq_map (zMk π α) hs _ (zCochar π α ψ) (R1Dis.zCochar_comp π α ψ)
  have hop : (zCochar π α ψ).oppositeCocharacter = zCochar π α ψ⁻¹ := by
    unfold zCochar; rw [cocharacter_inv]
  have e2 := parabolic_toIdeal_eq_map (zMk π α) hs _ (zCochar π α ψ⁻¹)
    (R1Dis.zCochar_comp π α ψ⁻¹)
  rw [← hop] at e2
  have h3 := congrArg (Ideal.comap (zMk π α : H →ₐ[k] ZAlg π α))
    (e2.symm.trans ((congrArg HopfIdeal.toIdeal heq).trans e1))
  have hK : Ideal.comap (zMk π α : H →ₐ[k] ZAlg π α) ⊥ =
      magnetIdeal (torusGrading π) (lineMagnet α) := by
    ext x
    rw [Ideal.mem_comap, Ideal.mem_bot, ← magnetHopfIdeal_toIdeal]
    exact Ideal.Quotient.eq_zero_iff_mem
  rw [Ideal.comap_map_of_surjective (zMk π α : H →ₐ[k] ZAlg π α) hs,
    Ideal.comap_map_of_surjective (zMk π α : H →ₐ[k] ZAlg π α) hs, hK,
    ← magnetIdeal_torusGrading_comap_nat, ← magnetIdeal_torusGrading_comap_nat,
    ← magnetIdeal_inf, ← magnetIdeal_inf] at h3
  have hαl : α ∈ lineMagnet α := mem_lineMagnet.2 (AddSubgroup.mem_zmultiples α)
  rcases lt_or_gt_of_ne hψα with hneg | hpos
  · refine magnetIdeal_ne_of_tangentWeight π hα (N := natMagnet.comap (pairingHom ψ⁻¹) ⊓
      lineMagnet α) (N' := natMagnet.comap (pairingHom ψ) ⊓ lineMagnet α) ⟨?_, hαl⟩ ?_ h3
    · change pairingHom ψ⁻¹ α ∈ natMagnet
      rw [mem_natMagnet, borPairingHom_inv]; omega
    · rintro ⟨h, -⟩
      change pairingHom ψ α ∈ natMagnet at h
      rw [mem_natMagnet] at h; omega
  · refine magnetIdeal_ne_of_tangentWeight π hα (N := natMagnet.comap (pairingHom ψ) ⊓
      lineMagnet α) (N' := natMagnet.comap (pairingHom ψ⁻¹) ⊓ lineMagnet α) ⟨?_, hαl⟩ ?_ h3.symm
    · change pairingHom ψ α ∈ natMagnet
      rw [mem_natMagnet]; omega
    · rintro ⟨h, -⟩
      change pairingHom ψ⁻¹ α ∈ natMagnet at h
      rw [mem_natMagnet, borPairingHom_inv] at h; omega

/-- **L1b in `Z` (named).** For `G` reductive, `ψ` regular with `BorInv ψ` and a root `χ₀`:
`P_Z(λ_ψ)` and `P_Z(λ_ψ⁻¹)` are Borel subgroups of `Z = G^{ℤχ₀}` (from `P(±ψ)` Borel in `G`).
The other half, `P_Z(λ⁻¹) ≠ P_Z(λ)`, is proved (`parZ_ne`). -/
def BorelZπ [Algebra.FiniteType k H] [Algebra.Smooth k H] : Prop :=
  reductiveCommHopfAlgProperty k Hf → ∀ (ψ : X →* Multiplicative ℤ) (χ₀ : Additive X),
    RegCochar π ψ → BorInv π ψ → χ₀ ∈ roots π →
    HopfIdeal.IsBorelOverAlgClosed k (FiniteTypeCommHopfAlgCat.of k (ZAlg π χ₀))
      (parabolicDefiningHopfIdeal (zCochar π χ₀ ψ)) ∧
    HopfIdeal.IsBorelOverAlgClosed k (FiniteTypeCommHopfAlgCat.of k (ZAlg π χ₀))
      (parabolicDefiningHopfIdeal (zCochar π χ₀ ψ).oppositeCocharacter)

theorem wallGeom_of_borelZ [Algebra.FiniteType k H] [Algebra.Smooth k H]
    (hπ : Function.Surjective π)
    (hT : HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H)
      (HopfIdeal.kerOfSurjective π hπ))
    (hB : BorelZπ π) : WallGeomπ π hπ := by
  intro hred ψ χ₀ hψ hI hα
  obtain ⟨h1, h2⟩ := hB hred ψ χ₀ hψ hI hα
  have h0 : χ₀ ≠ 0 := ne_zero_of_mem_roots hα
  have hΦ : χ₀ ∈ tangentWeights π k := (mem_tangentWeights_iff_mem_roots h0).2 hα
  exact r1Geom_of_borelZ π χ₀ ψ hπ hT h1 h2 (parZ_ne π χ₀ ψ hΦ (hψ χ₀ hΦ h0))

/-- **`WallStepπ` from `BorelZπ`** (`G` smooth, geometrically connected, `T` maximal). -/
theorem wallStepπ_of_borelZ [Algebra.FiniteType k H] [Algebra.Smooth k H]
    [ConnectedSpace (PrimeSpectrum (AlgebraicClosure k ⊗[k] H))]
    [Module.IsTorsionFree ℤ (Additive X)]
    (hπ : Function.Surjective π)
    (hmax : HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H)
      (HopfIdeal.kerOfSurjective π hπ))
    (hB : BorelZπ π) : WallStepπ π :=
  wallStepπ_of_wallGeom π hπ hmax (wallGeom_of_borelZ π hπ hmax hB)

end R1Route

end AlgMag.Reductive

#print axioms AlgMag.Reductive.wallStepπ_of_borelZ
#print axioms AlgMag.Reductive.parZ_ne
