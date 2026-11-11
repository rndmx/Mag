/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.BorGallery
import AlgMag.Reductive.RegularSlice

/-!
# W6: the gallery step (proved for `X` free)

Perturb `ψ` inside its chamber to `ψ₂ = ψ^K · ε` (`ε` generic on the finite set of the
`q₂χ₁ - q₁χ₂`, `K` large), so that two sign changes on the segment `[ψ₂, φ]` at the same
time are collinear. Then go to `ψ' = ψ₂^A φ^B` with `A/B` just below the largest crossing
slope `s(χ) = -⟨φ,χ⟩/⟨ψ₂,χ⟩`: only the weights of maximal slope flip.
-/

open Magnetism TauCeti TauCeti.Cocharacter

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X)

omit [DecidableEq X] in
theorem pairingHom_pow_mul (ψ φ : X →* Multiplicative ℤ) (A B : ℕ) (χ : Additive X) :
    pairingHom (ψ ^ A * φ ^ B) χ = A * pairingHom ψ χ + B * pairingHom φ χ := by
  simp [pairingHom_apply]

theorem large_mul_add (K : ℕ) (p e : ℤ) (hp : p ≠ 0) (he : |e| < K) :
    (K * p + e ≠ 0) ∧ (0 ≤ K * p + e ↔ 0 ≤ p) := by
  obtain ⟨h1, h2⟩ := abs_lt.1 he
  have hK : (0 : ℤ) ≤ K := by positivity
  rcases lt_or_gt_of_ne hp with h | h
  · have : (K : ℤ) * p ≤ -K := by nlinarith
    exact ⟨ne_of_lt (by linarith), ⟨fun h' => by linarith, fun h' => by linarith⟩⟩
  · have : (K : ℤ) ≤ K * p := by nlinarith
    exact ⟨ne_of_gt (by linarith), ⟨fun _ => h.le, fun _ => by linarith⟩⟩

/-- Sign of `A p + B q` in terms of the slope `s = -q/p` and `x = A/B`. -/
theorem slope_sign (p q : ℤ) (A B : ℕ) (hp : p ≠ 0) (hB : 0 < B)
    (hx : (A : ℚ) / B ≠ -(q : ℚ) / p) :
    ((A : ℤ) * p + B * q ≠ 0) ∧
    (-(q : ℚ) / p < A / B → (0 ≤ (A : ℤ) * p + B * q ↔ 0 ≤ p)) ∧
    ((A : ℚ) / B < -(q : ℚ) / p → (0 ≤ (A : ℤ) * p + B * q ↔ 0 ≤ q)) := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  have hBq : (0 : ℚ) < B := by exact_mod_cast hB
  have hid : (((A : ℤ) * p + B * q : ℤ) : ℚ) = B * p * ((A : ℚ) / B - (-(q : ℚ) / p)) := by
    push_cast; field_simp; ring
  have hd : (A : ℚ) / B - (-(q : ℚ) / p) ≠ 0 := sub_ne_zero.2 hx
  refine ⟨fun h0 => ?_, fun hlt => ?_, fun hlt => ?_⟩
  · have : (((A : ℤ) * p + B * q : ℤ) : ℚ) = 0 := by exact_mod_cast h0
    rw [hid] at this
    exact hd ((mul_eq_zero.1 this).resolve_left (mul_ne_zero hBq.ne' hpq))
  · have hpos : 0 < (A : ℚ) / B - (-(q : ℚ) / p) := by linarith
    rw [show (0 ≤ (A : ℤ) * p + B * q) ↔ (0 : ℚ) ≤ (((A : ℤ) * p + B * q : ℤ) : ℚ) from
      (by norm_cast), hid]
    rw [show (0 ≤ p) ↔ (0 : ℚ) ≤ (p : ℚ) from (by norm_cast)]
    constructor
    · intro h
      by_contra hn
      push Not at hn
      have : (B : ℚ) * p < 0 := mul_neg_of_pos_of_neg hBq hn
      nlinarith
    · intro h; exact mul_nonneg (mul_nonneg hBq.le h) hpos.le
  · have hneg : (A : ℚ) / B - (-(q : ℚ) / p) < 0 := by linarith
    have hsl : 0 < -(q : ℚ) / p := by
      have : (0 : ℚ) ≤ A / B := by positivity
      linarith
    rw [show (0 ≤ (A : ℤ) * p + B * q) ↔ (0 : ℚ) ≤ (((A : ℤ) * p + B * q : ℤ) : ℚ) from
      (by norm_cast), hid]
    have hqp : (q : ℚ) / p < 0 := by rw [neg_div] at hsl; linarith
    rw [show (0 ≤ q) ↔ (0 : ℚ) ≤ (q : ℚ) from (by norm_cast)]
    rcases lt_or_gt_of_ne hpq with hp' | hp'
    · have hq : 0 < (q : ℚ) := by
        by_contra hn; push Not at hn
        have : 0 ≤ (q : ℚ) / p := div_nonneg_of_nonpos hn hp'.le
        linarith
      have : 0 < (B : ℚ) * p * ((A : ℚ) / B - (-(q : ℚ) / p)) := by
        have : (B : ℚ) * p < 0 := mul_neg_of_pos_of_neg hBq hp'
        nlinarith
      exact ⟨fun _ => hq.le, fun _ => this.le⟩
    · have hq : (q : ℚ) < 0 := by
        by_contra hn; push Not at hn
        have : 0 ≤ (q : ℚ) / p := div_nonneg hn hp'.le
        linarith
      have : (B : ℚ) * p * ((A : ℚ) / B - (-(q : ℚ) / p)) < 0 := by
        have : 0 < (B : ℚ) * p := mul_pos hBq hp'
        nlinarith
      exact ⟨fun h => by linarith, fun h => by linarith⟩

/-- Positive slope iff opposite signs. -/
theorem slope_pos_iff (p q : ℤ) (hp : p ≠ 0) (hq : q ≠ 0) :
    0 < -(q : ℚ) / p ↔ ¬ (0 ≤ p ↔ 0 ≤ q) := by
  rw [neg_div, neg_pos, div_neg_iff]
  rcases lt_or_gt_of_ne hp with h | h <;> rcases lt_or_gt_of_ne hq with h' | h'
  · have : (p : ℚ) < 0 := by exact_mod_cast h
    have : (q : ℚ) < 0 := by exact_mod_cast h'
    constructor
    · rintro (⟨a, b⟩ | ⟨a, b⟩) <;> linarith
    · intro hn; exact absurd ⟨fun a => by omega, fun a => by omega⟩ hn
  · have : (p : ℚ) < 0 := by exact_mod_cast h
    have : (0 : ℚ) < q := by exact_mod_cast h'
    exact ⟨fun _ hn => by have := hn.2 h'.le; omega, fun _ => Or.inl ⟨by assumption, by assumption⟩⟩
  · have : (0 : ℚ) < p := by exact_mod_cast h
    have : (q : ℚ) < 0 := by exact_mod_cast h'
    exact ⟨fun _ hn => by have := hn.1 h.le; omega, fun _ => Or.inr ⟨by assumption, by assumption⟩⟩
  · have : (0 : ℚ) < p := by exact_mod_cast h
    have : (0 : ℚ) < q := by exact_mod_cast h'
    constructor
    · rintro (⟨a, b⟩ | ⟨a, b⟩) <;> linarith
    · intro hn; exact absurd ⟨fun a => by omega, fun a => by omega⟩ hn

theorem exists_between_finset (F : Finset ℚ) (s : ℚ) (hs : 0 < s) :
    ∃ x : ℚ, 0 < x ∧ x < s ∧ ∀ y ∈ F, y < s → y < x := by
  classical
  let G := insert 0 (F.filter (· < s))
  have hG : G.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  have hlo : G.max' hG < s := by
    rw [Finset.max'_lt_iff]
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact hs
    · exact (Finset.mem_filter.1 hy).2
  have h0 : 0 ≤ G.max' hG := G.le_max' 0 (Finset.mem_insert_self _ _)
  refine ⟨(G.max' hG + s) / 2, by linarith, by linarith, fun y hy hys => ?_⟩
  have : y ≤ G.max' hG :=
    G.le_max' y (Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hy, hys⟩))
  linarith

omit [DecidableEq X] in
theorem diffSet_congr_left {a b : X →* Multiplicative ℤ}
    (h : ∀ χ ∈ tangentWeights π k, (0 ≤ pairingHom a χ ↔ 0 ≤ pairingHom b χ))
    (c : X →* Multiplicative ℤ) : diffSet π a c = diffSet π b c := by
  ext χ
  simp only [diffSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [← h χ h1]⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [h χ h1]⟩

/-- **W6, proved** (for `X` free with finitely many tangent weights). -/
theorem galleryStep [Module.Free ℤ (Additive X)] (hfin : (tangentWeights π k).Finite) :
    GalleryStep π := by
  classical
  intro ψ φ hψ hφ hne
  set D := diffSet π ψ φ with hDdef
  have hD : D.Finite := hfin.subset (diffSet_subset π ψ φ)
  have hD0 : ∀ χ ∈ D, χ ≠ 0 := by
    rintro χ ⟨-, h⟩ rfl
    exact h (by simp)
  let q : Additive X → ℤ := fun χ => pairingHom φ χ
  let f : Additive X × Additive X → Additive X := fun c => q c.2 • c.1 - q c.1 • c.2
  let V : Set (Additive X) := (f '' (D ×ˢ D)) \ {0}
  have hV : V.Finite := ((hD.prod hD).image f).diff
  obtain ⟨ε, hε⟩ := exists_generic_cocharacter V hV (fun v hv => hv.2)
  obtain ⟨M, hM⟩ := ((hV.union hfin).image fun w => |pairingHom ε w|).bddAbove
  let K : ℕ := M.toNat + 1
  have hK : ∀ w ∈ V ∪ tangentWeights π k, |pairingHom ε w| < K := by
    intro w hw
    have := hM ⟨w, hw, rfl⟩
    simp only at this
    have := Int.self_le_toNat M
    simp only [K]; push_cast; omega
  let ψ₂ := ψ ^ K * ε ^ (1 : ℕ)
  have hψ₂ : ∀ χ, pairingHom ψ₂ χ = K * pairingHom ψ χ + pairingHom ε χ := by
    intro χ; rw [pairingHom_pow_mul]; push_cast; ring
  have hsign : ∀ χ ∈ tangentWeights π k, (0 ≤ pairingHom ψ₂ χ ↔ 0 ≤ pairingHom ψ χ) := by
    intro χ hχ
    by_cases h0 : χ = 0
    · subst h0; simp
    rw [hψ₂]
    exact (large_mul_add K _ _ (hψ χ hχ h0) (hK χ (Or.inr hχ))).2
  have hreg₂ : RegCochar π ψ₂ := by
    intro χ hχ h0
    rw [hψ₂]
    exact (large_mul_add K _ _ (hψ χ hχ h0) (hK χ (Or.inr hχ))).1
  have hD₂ : diffSet π ψ₂ φ = D := diffSet_congr_left π hsign φ
  let p : Additive X → ℤ := fun χ => pairingHom ψ₂ χ
  have hgen : ∀ χ₁ ∈ D, ∀ χ₂ ∈ D, p χ₁ * q χ₂ = p χ₂ * q χ₁ →
      q χ₂ • χ₁ = q χ₁ • χ₂ := by
    intro χ₁ h₁ χ₂ h₂ he
    by_contra hn
    have hv : f (χ₁, χ₂) ∈ V := ⟨⟨(χ₁, χ₂), ⟨h₁, h₂⟩, rfl⟩, sub_ne_zero.2 hn⟩
    have hval : pairingHom ψ₂ (f (χ₁, χ₂)) = 0 := by
      simp only [f, map_sub, map_zsmul, smul_eq_mul]
      change q χ₂ * p χ₁ - q χ₁ * p χ₂ = 0
      linarith
    rw [hψ₂] at hval
    have he0 := hε _ hv
    by_cases hz : pairingHom ψ (f (χ₁, χ₂)) = 0
    · rw [hz] at hval; exact he0 (by simpa using hval)
    · exact (large_mul_add K _ _ hz (hK _ (Or.inl hv))).1 hval
  let s : Additive X → ℚ := fun χ => -(q χ : ℚ) / p χ
  have hpq : ∀ χ ∈ tangentWeights π k, χ ≠ 0 → p χ ≠ 0 ∧ q χ ≠ 0 :=
    fun χ hχ h0 => ⟨hreg₂ χ hχ h0, hφ χ hχ h0⟩
  have hmemD : ∀ χ ∈ tangentWeights π k, χ ≠ 0 → (χ ∈ D ↔ 0 < s χ) := by
    intro χ hχ h0
    rw [← hD₂, slope_pos_iff _ _ (hpq χ hχ h0).1 (hpq χ hχ h0).2]
    exact ⟨fun h => h.2, fun h => ⟨hχ, h⟩⟩
  let Df := hD.toFinset
  have hDf : (Df.image s).Nonempty := by
    obtain ⟨χ, hχ⟩ := hne
    exact ⟨s χ, Finset.mem_image_of_mem _ (hD.mem_toFinset.2 hχ)⟩
  let sm := (Df.image s).max' hDf
  obtain ⟨χs, hχsD, hχs⟩ := Finset.mem_image.1 ((Df.image s).max'_mem hDf)
  rw [Set.Finite.mem_toFinset] at hχsD
  have hle : ∀ χ ∈ D, s χ ≤ sm :=
    fun χ hχ => (Df.image s).le_max' _ (Finset.mem_image_of_mem _ (hD.mem_toFinset.2 hχ))
  have hsm : 0 < sm := by
    show 0 < (Df.image s).max' hDf
    rw [← hχs]; exact (hmemD χs hχsD.1 (hD0 χs hχsD)).1 hχsD
  obtain ⟨x, hx0, hxs, hxlt⟩ := exists_between_finset (Df.image s) sm hsm
  let A : ℕ := x.num.toNat
  let B : ℕ := x.den
  have hAB : (A : ℚ) / B = x := by
    have h1 : ((A : ℤ) : ℚ) = (x.num : ℚ) := by
      rw [Int.toNat_of_nonneg (Rat.num_pos.2 hx0).le]
    rw [← Int.cast_natCast, h1]
    exact Rat.num_div_den x
  have hB : 0 < B := x.den_pos
  have hxne : ∀ χ ∈ tangentWeights π k, χ ≠ 0 →
      (s χ < x ∨ x < s χ) ∧ (χ ∈ D → x < s χ → s χ = sm) := by
    intro χ hχ h0
    refine ⟨?_, fun hD' hlt => ?_⟩
    · by_cases hD' : χ ∈ D
      · rcases (hle χ hD').lt_or_eq with h | h
        · exact Or.inl (hxlt _ (Finset.mem_image_of_mem _ (hD.mem_toFinset.2 hD')) h)
        · exact Or.inr (h ▸ hxs)
      · have : ¬ 0 < s χ := fun h => hD' ((hmemD χ hχ h0).2 h)
        exact Or.inl (by push Not at this; linarith)
    · rcases (hle χ hD').lt_or_eq with h | h
      · exact absurd (hxlt _ (Finset.mem_image_of_mem _ (hD.mem_toFinset.2 hD')) h) (by linarith)
      · exact h
  let ψ' := ψ₂ ^ A * φ ^ B
  have hψ' : ∀ χ, pairingHom ψ' χ = A * p χ + B * q χ :=
    fun χ => pairingHom_pow_mul _ _ _ _ _
  have hsl : ∀ χ ∈ tangentWeights π k, χ ≠ 0 →
      ((A : ℤ) * p χ + B * q χ ≠ 0) ∧
      (-(q χ : ℚ) / p χ < A / B → (0 ≤ (A : ℤ) * p χ + B * q χ ↔ 0 ≤ p χ)) ∧
      ((A : ℚ) / B < -(q χ : ℚ) / p χ → (0 ≤ (A : ℤ) * p χ + B * q χ ↔ 0 ≤ q χ)) :=
    fun χ hχ h0 => slope_sign (p χ) (q χ) A B (hpq χ hχ h0).1 hB (by
      rw [hAB]; rcases (hxne χ hχ h0).1 with h | h
      · exact ne_of_gt h
      · exact ne_of_lt h)
  have hreg' : RegCochar π ψ' := fun χ hχ h0 => by rw [hψ']; exact (hsl χ hχ h0).1
  refine ⟨ψ', hreg', ?_, ?_⟩
  · refine ⟨χs, fun χ hχ => ?_⟩
    rw [← diffSet_congr_left π hsign ψ'] at hχ
    obtain ⟨hχT, hdiff⟩ := hχ
    have h0 : χ ≠ 0 := by rintro rfl; exact hdiff (by simp)
    have hlt : x < s χ := by
      rcases (hxne χ hχT h0).1 with h | h
      · refine absurd ?_ hdiff
        rw [hψ']; exact ((hsl χ hχT h0).2.1 (hAB ▸ h)).symm
      · exact h
    have hχD : χ ∈ D := (hmemD χ hχT h0).2 (by linarith)
    have heq : s χ = s χs := by rw [hχs]; exact (hxne χ hχT h0).2 hχD hlt
    obtain ⟨hp1, hq1⟩ := hpq χ hχT h0
    obtain ⟨hp2, hq2⟩ := hpq χs hχsD.1 (hD0 χs hχsD)
    refine ⟨q χs, q χ, hq2, hq1, hgen χ hχD χs hχsD ?_⟩
    have hp1' : (p χ : ℚ) ≠ 0 := by exact_mod_cast hp1
    have hp2' : (p χs : ℚ) ≠ 0 := by exact_mod_cast hp2
    simp only [s] at heq
    rw [div_eq_div_iff hp1' hp2'] at heq
    have : ((p χ * q χs : ℤ) : ℚ) = ((p χs * q χ : ℤ) : ℚ) := by push_cast; linarith
    exact_mod_cast this
  · have hsub : diffSet π ψ' φ ⊆ D := by
      rintro χ ⟨hχT, hdiff⟩
      have h0 : χ ≠ 0 := by rintro rfl; exact hdiff (by simp)
      by_contra hn
      have hs : s χ < x := by
        rcases (hxne χ hχT h0).1 with h | h
        · exact h
        · exact absurd ((hmemD χ hχT h0).2 (by linarith)) hn
      have h1 := (hsl χ hχT h0).2.1 (hAB ▸ hs)
      rw [← hψ'] at h1
      have h2 : (0 ≤ p χ ↔ 0 ≤ q χ) := by
        by_contra hc; exact hn (hD₂ ▸ ⟨hχT, hc⟩)
      exact hdiff (h1.trans h2)
    refine (Set.ssubset_iff_of_subset hsub).2 ⟨χs, hχsD, fun hm => ?_⟩
    have h0 := hD0 χs hχsD
    have hlt : x < s χs := by rw [hχs]; exact hxs
    have h1 := (hsl χs hχsD.1 h0).2.2 (hAB ▸ hlt)
    rw [← hψ'] at h1
    exact hm.2 h1

end AlgMag.Reductive
