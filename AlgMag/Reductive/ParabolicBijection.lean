/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Rooted.ReductiveRooted
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Group.Submonoid.BigOperators
import AlgMag.Reductive.OpenCell.OpenCellFlatness
import AlgMag.Reductive.RootSystemCombinatorics

/-!
# Pure magnets containing a basis and parabolic subsets (Theorem `thm:red-parabolic`)

`G` split reductive over a field, `T = D(M)`, roots `Φ ⊆ M`, a basis `B ⊆ Φ` with positive
roots `Φ⁺ = Φ ∩ ℕB`, Weyl group acting by `act`. For a magnet `N ⊇ B` put
`ξ_N = {α ∈ B | -α ∈ N}`.

Combinatorial part (no hypothesis beyond `Φ ⊆ ℕB ∪ -ℕB`):
* `inter_roots_eq`: `N ∩ Φ = Φ⁺ ∪ (Φ ∩ -ℕξ_N)`;
* `closure_inter_roots_eq`: `[N ∩ Φ⟩ = ℕB + ℕ(-ξ_N)`.

Weyl part: from the inversion sets (`InversionData`, the facts of Bourbaki VI §1 no. 10
recorded as data: `2ρ - w(2ρ) = 2 Σ_{γ ∈ Φ⁺ ∩ wΦ⁻} γ` and `(1-w)M ⊆ ℤ(Φ⁺ ∩ wΦ⁻)`),
`weylMagnet_le_closure_inter`: `Z_w ⊆ N` forces `Z_w ⊆ [N ∩ Φ⟩`. Hence
* `reductiveHull_eq_of_basis`: `E(G^N) = ℕB + ℕ(-ξ_N)`;
* with `ReductiveInput` (Theorem `thm:red-pure`, an explicit hypothesis):
  `pure_iff_of_basis_le`, and the bijection `bijOn_parabolic` from pure magnets containing `B`
  onto additively stable `R ⊇ Φ⁺` (these are the parabolic subsets containing `Φ⁺`,
  `union_neg_eq_of_parabolic`), inverse `R ↦ [R⟩`; `bijOn_parabolic_someBasis` for
  "some basis" (Bourbaki VI §1 Prop. 20 identifies its target with all parabolic subsets).

Geometric part over a field: `magnetIdeal_basis_neg_eq_parabolic`, `G^{[B ∪ -ξ⟩} = P(λ)` for a
cocharacter `λ` vanishing on `ξ` and positive on `B \ ξ`, i.e. `G^{[B ∪ -ξ⟩} = P_ξ`.
-/

namespace AlgMag.Reductive.Parabolic

open AlgMag.Rooted
open scoped Pointwise

section Combinatorial

variable {M : Type*} [AddCommGroup M] {Φ B : Set M}

lemma mem_weylMagnet {w : M →+ M} {z : M} :
    z ∈ Rooted.weylMagnet w ↔ ∃ x, x - w x = z := by
  simp [Rooted.weylMagnet]

/-- `ξ_N = {α ∈ B | -α ∈ N}`. -/
def xi (B : Set M) (N : AddSubmonoid M) : Set M := {α | α ∈ B ∧ -α ∈ N}

/-- Elements of `N` coming from `-ℕS` with `S ⊆ N` stay in `N`. -/
lemma neg_mem_of_mem_closure {S : Set M} {N : AddSubmonoid M} (hS : ∀ α ∈ S, -α ∈ N) {δ : M}
    (hδ : δ ∈ AddSubmonoid.closure S) : -δ ∈ N := by
  induction hδ using AddSubmonoid.closure_induction with
  | mem x hx => exact hS x hx
  | zero => simp
  | add x y _ _ hx hy => rw [neg_add]; exact add_mem hx hy

/-- If `-δ ∈ N` with `δ ∈ ℕB` and `B ⊆ N`, then `δ ∈ ℕξ_N`. -/
theorem mem_closure_xi {N : AddSubmonoid M} (hBN : B ⊆ N) {δ : M}
    (hδ : δ ∈ AddSubmonoid.closure B) (hn : -δ ∈ N) : δ ∈ AddSubmonoid.closure (xi B N) := by
  have hBN' : AddSubmonoid.closure B ≤ N := AddSubmonoid.closure_le.2 hBN
  induction hδ using AddSubmonoid.closure_induction with
  | mem x hx => exact AddSubmonoid.subset_closure ⟨hx, hn⟩
  | zero => exact zero_mem _
  | add x y hx' hy' hx hy =>
    refine add_mem (hx ?_) (hy ?_)
    · have : -x = -(x + y) + y := by abel
      rw [this]; exact add_mem hn (hBN' hy')
    · have : -y = -(x + y) + x := by abel
      rw [this]; exact add_mem hn (hBN' hx')

/-- **`N ∩ Φ = Φ⁺ ∪ (Φ ∩ -ℕξ_N)`** for a magnet `N ⊇ B`. -/
theorem inter_roots_eq (hΦ : ∀ α ∈ Φ, α ∈ AddSubmonoid.closure B ∨ -α ∈ AddSubmonoid.closure B)
    {N : AddSubmonoid M} (hBN : B ⊆ N) :
    (N : Set M) ∩ Φ = (Φ ∩ AddSubmonoid.closure B) ∪
      {α | α ∈ Φ ∧ -α ∈ AddSubmonoid.closure (xi B N)} := by
  have hBN' : AddSubmonoid.closure B ≤ N := AddSubmonoid.closure_le.2 hBN
  ext α
  constructor
  · rintro ⟨hαN, hα⟩
    rcases hΦ α hα with h | h
    · exact Or.inl ⟨hα, h⟩
    · exact Or.inr ⟨hα, mem_closure_xi hBN h (by simpa using hαN)⟩
  · rintro (⟨hα, h⟩ | ⟨hα, h⟩)
    · exact ⟨hBN' h, hα⟩
    · refine ⟨?_, hα⟩
      have := neg_mem_of_mem_closure (S := xi B N) (N := N) (fun β hβ => hβ.2) h
      simpa using this

/-- **`[N ∩ Φ⟩ = ℕB + ℕ(-ξ_N)`** for a magnet `N ⊇ B` (`B ⊆ Φ`, `Φ = -Φ`). -/
theorem closure_inter_roots_eq (hΦ : ∀ α ∈ Φ, α ∈ AddSubmonoid.closure B ∨
      -α ∈ AddSubmonoid.closure B) (hneg : ∀ α ∈ Φ, -α ∈ Φ) (hBΦ : B ⊆ Φ)
    {N : AddSubmonoid M} (hBN : B ⊆ N) :
    AddSubmonoid.closure ((N : Set M) ∩ Φ) = AddSubmonoid.closure (B ∪ -xi B N) := by
  apply le_antisymm
  · rw [AddSubmonoid.closure_le, inter_roots_eq hΦ hBN]
    rintro α (⟨_, h⟩ | ⟨_, h⟩)
    · exact AddSubmonoid.closure_mono Set.subset_union_left h
    · have := neg_mem_of_mem_closure (S := xi B N)
        (N := AddSubmonoid.closure (B ∪ -xi B N))
        (fun β hβ => AddSubmonoid.subset_closure (Or.inr (by simpa using hβ))) h
      simpa using this
  · rw [AddSubmonoid.closure_le]
    rintro α (hα | hα)
    · exact AddSubmonoid.subset_closure ⟨hBN hα, hBΦ hα⟩
    · have hα' : -α ∈ xi B N := by simpa using hα
      exact AddSubmonoid.subset_closure ⟨by simpa using hα'.2, by simpa using hneg _ (hBΦ hα'.1)⟩

/-- Bourbaki VI §1 no. 10 as data: for each `w`, a finite inversion set `Inv(w) ⊆ Φ⁺` with
`2ρ - w(2ρ) = Σ_{γ ∈ Inv(w)} 2γ` and `(1 - w)M ⊆ ℤ Inv(w)`. -/
structure InversionData (Φ B : Set M) {W : Type*} (act : W → M →+ M) where
  twoRho : M
  inv : W → Finset M
  inv_pos : ∀ w, ((inv w : Finset M) : Set M) ⊆ Φ ∩ AddSubmonoid.closure B
  rho_eq : ∀ w, twoRho - act w twoRho = ∑ γ ∈ inv w, 2 • γ
  range_le : ∀ w m, m - act w m ∈ AddSubgroup.closure ((inv w : Finset M) : Set M)

variable {W : Type*} {act : W → M →+ M}

/-- If `Z_w ⊆ N ⊇ B`, every inversion `γ` of `w` has `-γ ∈ N` (the `2ρ` argument). -/
theorem neg_inv_mem (D : InversionData Φ B act) {N : AddSubmonoid M} (hBN : B ⊆ N) {w : W}
    (hw : Rooted.weylMagnet (act w) ≤ N) {γ : M} (hγ : γ ∈ D.inv w) : -γ ∈ N := by
  classical
  have hBN' : AddSubmonoid.closure B ≤ N := AddSubmonoid.closure_le.2 hBN
  set d := D.twoRho - act w D.twoRho
  have hnd : -d ∈ N := hw (mem_weylMagnet.2 ⟨-D.twoRho, by simp [d]; abel⟩)
  have hd : d = 2 • γ + ∑ γ' ∈ (D.inv w).erase γ, 2 • γ' := by
    show D.twoRho - act w D.twoRho = _
    rw [D.rho_eq, Finset.add_sum_erase _ _ hγ]
  have hrest : ∑ γ' ∈ (D.inv w).erase γ, 2 • γ' ∈ N :=
    sum_mem fun γ' hγ' => nsmul_mem (hBN' (D.inv_pos w (Finset.mem_of_mem_erase hγ')).2) _
  have : -γ = -d + (γ + ∑ γ' ∈ (D.inv w).erase γ, 2 • γ') := by rw [hd]; abel
  rw [this]
  exact add_mem hnd (add_mem (hBN' (D.inv_pos w hγ).2) hrest)

/-- If `Z_w ⊆ N ⊇ B`, then `Z_w ⊆ [N ∩ Φ⟩` (paper: `W_N = W_ξ` and `Λ_N ⊆ ℤξ ⊆ [R(N)⟩`). -/
theorem weylMagnet_le_closure_inter (D : InversionData Φ B act) (hneg : ∀ α ∈ Φ, -α ∈ Φ)
    {N : AddSubmonoid M} (hBN : B ⊆ N) {w : W} (hw : Rooted.weylMagnet (act w) ≤ N) :
    Rooted.weylMagnet (act w) ≤ AddSubmonoid.closure ((N : Set M) ∩ Φ) := by
  have hBN' : AddSubmonoid.closure B ≤ N := AddSubmonoid.closure_le.2 hBN
  intro z hz
  obtain ⟨m, rfl⟩ := mem_weylMagnet.1 hz
  have h := D.range_le w m
  rw [← AddSubgroup.mem_toAddSubmonoid, AddSubgroup.closure_toAddSubmonoid] at h
  refine AddSubmonoid.closure_mono ?_ h
  rintro γ (hγ | hγ)
  · exact ⟨hBN' (D.inv_pos w hγ).2, (D.inv_pos w hγ).1⟩
  · have hγ' : -γ ∈ D.inv w := Set.mem_neg.1 hγ
    refine ⟨?_, ?_⟩
    · simpa using neg_inv_mem D hBN hw hγ'
    · simpa using hneg _ (D.inv_pos w hγ').1

/-- `E(G^N) = [N ∩ Φ⟩` for `N ⊇ B`. -/
theorem reductiveHull_eq_closure_of_basis (D : InversionData Φ B act) (hneg : ∀ α ∈ Φ, -α ∈ Φ)
    {N : AddSubmonoid M} (hBN : B ⊆ N) :
    reductiveHull Φ act N = AddSubmonoid.closure ((N : Set M) ∩ Φ) :=
  le_antisymm (sup_le le_rfl (iSup₂_le fun _ hw => weylMagnet_le_closure_inter D hneg hBN hw))
    le_sup_left

/-- **Theorem `thm:red-parabolic`: `E(G^N) = ℕB + ℕ(-ξ_N)`** for every magnet `N ⊇ B`. -/
theorem reductiveHull_eq_of_basis (D : InversionData Φ B act)
    (hΦ : ∀ α ∈ Φ, α ∈ AddSubmonoid.closure B ∨ -α ∈ AddSubmonoid.closure B)
    (hneg : ∀ α ∈ Φ, -α ∈ Φ) (hBΦ : B ⊆ Φ) {N : AddSubmonoid M} (hBN : B ⊆ N) :
    reductiveHull Φ act N = AddSubmonoid.closure (B ∪ -xi B N) := by
  rw [reductiveHull_eq_closure_of_basis D hneg hBN, closure_inter_roots_eq hΦ hneg hBΦ hBN]

variable {P : AddSubmonoid M → Prop}

/-- A magnet `N ⊇ B` is pure iff `N = [N ∩ Φ⟩`, iff `N = ℕB + ℕ(-ξ_N)`. -/
theorem pure_iff_of_basis_le (H : ReductiveInput P Φ act) (D : InversionData Φ B act)
    (hneg : ∀ α ∈ Φ, -α ∈ Φ) {N : AddSubmonoid M} (hBN : B ⊆ N) :
    P N ↔ N = AddSubmonoid.closure ((N : Set M) ∩ Φ) := by
  rw [H.pure_iff, reductiveHull_eq_closure_of_basis D hneg hBN]

/-- `R ⊇ Φ⁺` with `Φ ⊆ ℕB ∪ -ℕB` satisfies `R ∪ -R = Φ`: it is parabolic once closed. -/
theorem union_neg_eq_of_parabolic
    (hΦ : ∀ α ∈ Φ, α ∈ AddSubmonoid.closure B ∨ -α ∈ AddSubmonoid.closure B)
    (hneg : ∀ α ∈ Φ, -α ∈ Φ) {R : Set M} (hR : R ⊆ Φ)
    (hpos : Φ ∩ AddSubmonoid.closure B ⊆ R) : R ∪ -R = Φ := by
  ext α
  constructor
  · rintro (h | h)
    · exact hR h
    · simpa using hneg _ (hR (Set.mem_neg.1 h))
  · intro hα
    rcases hΦ α hα with h | h
    · exact Or.inl (hpos ⟨hα, h⟩)
    · exact Or.inr (Set.mem_neg.2 (hpos ⟨hneg _ hα, h⟩))

/-- **Theorem `thm:red-parabolic`, bijection (fixed basis).** `N ↦ N ∩ Φ` is a bijection from
the pure magnets containing `B` onto the additively stable `R ⊆ Φ` containing `Φ⁺`, with
inverse `R ↦ [R⟩`. -/
theorem bijOn_parabolic (H : ReductiveInput P Φ act) (D : InversionData Φ B act)
    (hneg : ∀ α ∈ Φ, -α ∈ Φ) (hBΦ : B ⊆ Φ) :
    Set.BijOn (fun N : AddSubmonoid M => (N : Set M) ∩ Φ) {N | P N ∧ B ⊆ N}
        {R | IsStableElt Φ R ∧ Φ ∩ AddSubmonoid.closure B ⊆ R} ∧
      Set.InvOn AddSubmonoid.closure (fun N : AddSubmonoid M => (N : Set M) ∩ Φ)
        {N | P N ∧ B ⊆ N} {R | IsStableElt Φ R ∧ Φ ∩ AddSubmonoid.closure B ⊆ R} := by
  have hp := fun (N : AddSubmonoid M) (hBN : B ⊆ (N : Set M)) => pure_iff_of_basis_le H D hneg hBN
  refine ⟨⟨fun N hN => ⟨⟨Set.inter_subset_right, ?_⟩, ?_⟩, fun N hN L hL h => ?_,
    fun R hR => ?_⟩, fun N hN => ((hp N hN.2).1 hN.1).symm, fun R hR => hR.1.2⟩
  · show _ = _
    rw [← (hp N hN.2).1 hN.1]
  · exact fun α hα => ⟨AddSubmonoid.closure_le.2 hN.2 hα.2, hα.1⟩
  · rw [(hp N hN.2).1 hN.1, (hp L hL.2).1 hL.1]; exact congrArg _ h
  · have hBR : B ⊆ R := fun α hα => hR.2 ⟨hBΦ hα, AddSubmonoid.subset_closure hα⟩
    have hBN : B ⊆ AddSubmonoid.closure R := fun α hα => AddSubmonoid.subset_closure (hBR hα)
    refine ⟨AddSubmonoid.closure R, ⟨?_, hBN⟩, hR.1.2⟩
    rw [hp _ hBN, hR.1.2]

/-- **Theorem `thm:red-parabolic`, bijection ("some basis").** For a family `𝔅` of bases, each
with its inversion data, `N ↦ N ∩ Φ` is a bijection from the pure magnets containing some
`B ∈ 𝔅` onto the additively stable `R` containing `Φ⁺_B` for some `B ∈ 𝔅`. With `𝔅` the set of
all bases, Bourbaki VI §1 Prop. 20 identifies the target with the parabolic subsets. -/
theorem bijOn_parabolic_someBasis (H : ReductiveInput P Φ act) (𝔅 : Set (Set M))
    (D : ∀ B ∈ 𝔅, InversionData Φ B act) (hneg : ∀ α ∈ Φ, -α ∈ Φ) (hBΦ : ∀ B ∈ 𝔅, B ⊆ Φ) :
    Set.BijOn (fun N : AddSubmonoid M => (N : Set M) ∩ Φ) {N | P N ∧ ∃ B ∈ 𝔅, B ⊆ N}
        {R | IsStableElt Φ R ∧ ∃ B ∈ 𝔅, Φ ∩ AddSubmonoid.closure B ⊆ R} ∧
      Set.InvOn AddSubmonoid.closure (fun N : AddSubmonoid M => (N : Set M) ∩ Φ)
        {N | P N ∧ ∃ B ∈ 𝔅, B ⊆ N}
        {R | IsStableElt Φ R ∧ ∃ B ∈ 𝔅, Φ ∩ AddSubmonoid.closure B ⊆ R} := by
  have key : ∀ N, P N → (∃ B ∈ 𝔅, B ⊆ N) → N = AddSubmonoid.closure ((N : Set M) ∩ Φ) := by
    rintro N hN ⟨B, hB, hBN⟩
    exact (pure_iff_of_basis_le H (D B hB) hneg hBN).1 hN
  refine ⟨⟨fun N hN => ⟨⟨Set.inter_subset_right, ?_⟩, ?_⟩, fun N hN L hL h => ?_,
    fun R hR => ?_⟩, fun N hN => (key N hN.1 hN.2).symm, fun R hR => hR.1.2⟩
  · show _ = _
    rw [← key N hN.1 hN.2]
  · obtain ⟨B, hB, hBN⟩ := hN.2
    exact ⟨B, hB, fun α hα => ⟨AddSubmonoid.closure_le.2 hBN hα.2, hα.1⟩⟩
  · rw [key N hN.1 hN.2, key L hL.1 hL.2]; exact congrArg _ h
  · obtain ⟨B, hB, hpos⟩ := hR.2
    have hRmem := (bijOn_parabolic H (D B hB) hneg (hBΦ B hB)).1.surjOn ⟨hR.1, hpos⟩
    obtain ⟨N, ⟨hN, hBN⟩, hNR⟩ := hRmem
    exact ⟨N, ⟨hN, B, hB, hBN⟩, hNR⟩

/-- A functional `λ ≥ 0` on `B`, `> 0` on `B \ ξ`: `δ ∈ ℕB` with `λ(δ) ≤ 0` lies in `ℕξ`. -/
lemma mem_closure_of_pairing_nonpos (f : M →+ ℤ) {ξ : Set M}
    (hf : ∀ α ∈ B, 0 ≤ f α) (hfpos : ∀ α ∈ B, α ∉ ξ → 0 < f α) {δ : M}
    (hδ : δ ∈ AddSubmonoid.closure B) (h : f δ ≤ 0) : δ ∈ AddSubmonoid.closure ξ := by
  have hnn : ∀ x ∈ AddSubmonoid.closure B, 0 ≤ f x := fun x hx => by
    induction hx using AddSubmonoid.closure_induction with
    | mem x hx => exact hf x hx
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_nonneg hx hy
  induction hδ using AddSubmonoid.closure_induction with
  | mem x hx =>
    by_cases hξ : x ∈ ξ
    · exact AddSubmonoid.subset_closure hξ
    · exact absurd h (not_le.2 (hfpos x hx hξ))
  | zero => exact zero_mem _
  | add x y hx' hy' hx hy =>
    rw [map_add] at h
    have := hnn x hx'; have := hnn y hy'
    exact add_mem (hx (by omega)) (hy (by omega))

end Combinatorial

/-! ### Inversion data from simple reflections -/

section Inversion

variable {M : Type*} [AddCommGroup M] {Φ B : Set M} {W : Type*} [Group W] {act : W → M →+ M}

/-- Root-system input for `InversionData`: `Φ` finite, `Φ = Φ⁺ ⊔ -Φ⁺` with `Φ⁺ = Φ ∩ ℕB`,
`B ⊆ Φ`, `W` acts on `M` preserving `Φ`, each `α ∈ B` has a reflection `s_α` (involution,
`s_α α = -α`, permuting `Φ⁺ \ {α}`, `(1 - s_α)M ⊆ ℤα`), and **`coxeter`**: an element of `W`
preserving `Φ⁺` is trivial (simple transitivity of `W` on positive systems). -/
structure SimpleSystem (Φ B : Set M) (act : W → M →+ M) : Prop where
  finite : Φ.Finite
  basis_sub : B ⊆ Φ
  pos_or_neg : ∀ α ∈ Φ, α ∈ AddSubmonoid.closure B ∨ -α ∈ AddSubmonoid.closure B
  pointed : ∀ α ∈ Φ, α ∈ AddSubmonoid.closure B → -α ∉ AddSubmonoid.closure B
  neg_mem : ∀ α ∈ Φ, -α ∈ Φ
  act_mul : ∀ v w m, act (v * w) m = act v (act w m)
  act_one : ∀ m, act 1 m = m
  act_mem : ∀ w α, α ∈ Φ → act w α ∈ Φ
  simple : ∀ α ∈ B, ∃ s : W, s * s = 1 ∧ act s α = -α ∧
    (∀ β ∈ Φ, β ∈ AddSubmonoid.closure B → β ≠ α → act s β ∈ AddSubmonoid.closure B) ∧
    ∀ m, m - act s m ∈ AddSubgroup.closure {α}
  coxeter : ∀ w, (∀ γ ∈ Φ, γ ∈ AddSubmonoid.closure B → act w γ ∈ AddSubmonoid.closure B) →
    ∀ m, act w m = m

/-- **`coxeter` is a theorem for a Weyl group generated by simple reflections** with
`W`-equivariant coroots (`RootSystem.WeylSystem.act_eq_of_pos`). -/
theorem SimpleSystem.ofWeyl {refl : M → W} {coroot : M → M →+ ℤ}
    (S : RootSystem.WeylSystem Φ B act refl coroot) (finite : Φ.Finite)
    (pos_or_neg : ∀ α ∈ Φ, α ∈ AddSubmonoid.closure B ∨ -α ∈ AddSubmonoid.closure B)
    (neg_mem : ∀ α ∈ Φ, -α ∈ Φ) : SimpleSystem Φ B act where
  finite := finite
  basis_sub := S.basis_sub
  pos_or_neg := pos_or_neg
  pointed := S.pointed
  neg_mem := neg_mem
  act_mul := S.act_mul
  act_one := S.act_one
  act_mem := S.act_mem
  simple α hα := by
    refine ⟨refl α, S.refl_sq α hα, S.act_refl_self hα, S.refl_pos α hα, fun m => ?_⟩
    rw [S.refl_act α hα, sub_sub_cancel]
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_singleton α)) _
  coxeter := S.act_eq_of_pos

namespace SimpleSystem

variable (S : SimpleSystem Φ B act)
include S

/-- `Φ⁺` as a finset. -/
noncomputable def pos : Finset M := by
  classical exact S.finite.toFinset.filter (fun β => β ∈ AddSubmonoid.closure B)

lemma mem_pos {β : M} : β ∈ S.pos ↔ β ∈ Φ ∧ β ∈ AddSubmonoid.closure B := by
  classical
  unfold pos; rw [Finset.mem_filter, Set.Finite.mem_toFinset]

/-- `Inv(w) = Φ⁺ ∩ w(-Φ⁺)`. -/
noncomputable def inv (w : W) : Finset M := by
  classical exact S.pos.filter (fun γ => act w⁻¹ γ ∉ AddSubmonoid.closure B)

lemma mem_inv {w : W} {γ : M} : γ ∈ S.inv w ↔
    (γ ∈ Φ ∧ γ ∈ AddSubmonoid.closure B) ∧ act w⁻¹ γ ∉ AddSubmonoid.closure B := by
  classical
  unfold inv; rw [Finset.mem_filter, S.mem_pos]

lemma act_inv_act (w : W) (m : M) : act w⁻¹ (act w m) = m := by
  rw [← S.act_mul, inv_mul_cancel, S.act_one]

lemma act_act_inv (w : W) (m : M) : act w (act w⁻¹ m) = m := by
  rw [← S.act_mul, mul_inv_cancel, S.act_one]

lemma neg_mem_of_not {β : M} (hβ : β ∈ Φ) (h : β ∉ AddSubmonoid.closure B) :
    -β ∈ AddSubmonoid.closure B := (S.pos_or_neg β hβ).resolve_left h

/-- `2ρ = Σ_{Φ⁺} β`. -/
noncomputable def twoRho : M := ∑ β ∈ S.pos, β

/-- **`2ρ - w(2ρ) = Σ_{γ ∈ Inv(w)} 2γ`** (Bourbaki VI §1 no. 10), for any `w` permuting `Φ`. -/
theorem rho_eq (w : W) : S.twoRho - act w S.twoRho = ∑ γ ∈ S.inv w, 2 • γ := by
  classical
  have hA : ∑ β ∈ S.pos.filter (fun β => act w β ∈ AddSubmonoid.closure B), act w β =
      ∑ γ ∈ S.pos.filter (fun γ => act w⁻¹ γ ∈ AddSubmonoid.closure B), γ := by
    refine Finset.sum_nbij' (act w) (act w⁻¹) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
    · intro β hβ
      simp only [Finset.mem_filter, S.mem_pos] at hβ ⊢
      exact ⟨⟨S.act_mem w β hβ.1.1, hβ.2⟩, by rw [S.act_inv_act]; exact hβ.1.2⟩
    · intro γ hγ
      simp only [Finset.mem_filter, S.mem_pos] at hγ ⊢
      exact ⟨⟨S.act_mem _ γ hγ.1.1, hγ.2⟩, by rw [S.act_act_inv]; exact hγ.1.2⟩
    · intro β _; exact S.act_inv_act w β
    · intro γ _; exact S.act_act_inv w γ
  have hC : ∑ β ∈ S.pos.filter (fun β => act w β ∉ AddSubmonoid.closure B), act w β =
      ∑ γ ∈ S.inv w, -γ := by
    refine Finset.sum_nbij' (fun β => -act w β) (fun γ => -act w⁻¹ γ) ?_ ?_ ?_ ?_ ?_
    · intro β hβ
      simp only [Finset.mem_filter, S.mem_pos] at hβ
      rw [S.mem_inv]
      have h1 := S.act_mem w β hβ.1.1
      refine ⟨⟨S.neg_mem _ h1, S.neg_mem_of_not h1 hβ.2⟩, ?_⟩
      rw [map_neg, S.act_inv_act]; exact S.pointed β hβ.1.1 hβ.1.2
    · intro γ hγ
      rw [S.mem_inv] at hγ
      simp only [Finset.mem_filter, S.mem_pos]
      have h1 := S.act_mem w⁻¹ γ hγ.1.1
      refine ⟨⟨S.neg_mem _ h1, S.neg_mem_of_not h1 hγ.2⟩, ?_⟩
      rw [map_neg, S.act_act_inv]; exact S.pointed γ hγ.1.1 hγ.1.2
    · intro β _; simp [S.act_inv_act]
    · intro γ _; simp [S.act_act_inv]
    · intro β _; simp
  have hP : ∑ γ ∈ S.pos, γ = ∑ γ ∈ S.pos.filter (fun γ => act w⁻¹ γ ∈ AddSubmonoid.closure B), γ +
      ∑ γ ∈ S.inv w, γ := by
    rw [← Finset.sum_filter_add_sum_filter_not S.pos
      (fun γ => act w⁻¹ γ ∈ AddSubmonoid.closure B)]
    rfl
  have hw : act w S.twoRho = ∑ β ∈ S.pos, act w β := by rw [twoRho, map_sum]
  rw [hw, ← Finset.sum_filter_add_sum_filter_not S.pos
    (fun β => act w β ∈ AddSubmonoid.closure B), hA, hC, twoRho, hP, Finset.sum_neg_distrib]
  rw [← Finset.smul_sum]
  abel

/-- **`(1 - w)M ⊆ ℤ Inv(w)`**, by induction on `|Inv(w)|` using simple reflections. -/
theorem range_le : ∀ n (w : W), (S.inv w).card = n →
    ∀ m, m - act w m ∈ AddSubgroup.closure ((S.inv w : Finset M) : Set M) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w hn m
  rcases (S.inv w).eq_empty_or_nonempty with he | ⟨γ0, hγ0⟩
  · have hfix := S.coxeter w⁻¹ (fun γ hγ hγB => by
      by_contra h
      have : γ ∈ S.inv w := S.mem_inv.2 ⟨⟨hγ, hγB⟩, h⟩
      rw [he] at this; simp at this)
    have : act w m = m := by
      conv_lhs => rw [← hfix m]
      exact S.act_act_inv w m
    rw [this, sub_self]; exact zero_mem _
  · obtain ⟨α, hαB, hα⟩ : ∃ α ∈ B, α ∈ S.inv w := by
      by_contra h
      push Not at h
      have hle : AddSubmonoid.closure B ≤
          (AddSubmonoid.closure B).comap (act w⁻¹) := by
        rw [AddSubmonoid.closure_le]
        intro α hαB
        by_contra hn
        exact h α hαB (S.mem_inv.2 ⟨⟨S.basis_sub hαB, AddSubmonoid.subset_closure hαB⟩, hn⟩)
      have h0 := S.mem_inv.1 hγ0
      exact h0.2 (hle h0.1.2)
    obtain ⟨s, hss, hsα, hspos, hsM⟩ := S.simple α hαB
    have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
    have hαinv := S.mem_inv.1 hα
    set w' := s * w
    have hsub : ∀ γ ∈ S.inv w', act s γ ∈ (S.inv w).erase α := by
      intro γ hγ
      have hγ' := S.mem_inv.1 hγ
      have hw'inv : w'⁻¹ = w⁻¹ * s := by rw [mul_inv_rev, hsinv]
      rw [hw'inv, S.act_mul] at hγ'
      have hγα : γ ≠ α := by
        rintro rfl
        rw [hsα, map_neg] at hγ'
        exact hγ'.2 (S.neg_mem_of_not (S.act_mem _ _ hαinv.1.1) hαinv.2)
      have hsγ := hspos γ hγ'.1.1 hγ'.1.2 hγα
      refine Finset.mem_erase.2 ⟨?_, S.mem_inv.2 ⟨⟨S.act_mem s γ hγ'.1.1, hsγ⟩, hγ'.2⟩⟩
      intro heq
      have : γ = -α := by
        have := congrArg (act s) heq
        rw [← S.act_mul, hss, S.act_one, hsα] at this
        exact this
      exact S.pointed α hαinv.1.1 hαinv.1.2 (this ▸ hγ'.1.2)
    have hcard : (S.inv w').card < n := by
      calc (S.inv w').card ≤ (((S.inv w).erase α).image (act s)).card := by
            refine Finset.card_le_card fun γ hγ => Finset.mem_image.2 ⟨act s γ, hsub γ hγ, ?_⟩
            rw [← S.act_mul, hss, S.act_one]
        _ ≤ ((S.inv w).erase α).card := Finset.card_image_le
        _ < n := by rw [Finset.card_erase_of_mem hα, ← hn]; exact Nat.sub_lt
                      (Finset.card_pos.2 ⟨α, hα⟩) one_pos
    have hIH := ih _ hcard w' rfl m
    have hww : act w m = act s (act w' m) := by
      rw [← S.act_mul, ← mul_assoc, hss, one_mul]
    have hdec : m - act w m = (m - act s m) + act s (m - act w' m) := by
      rw [hww, map_sub]; abel
    rw [hdec]
    refine add_mem ?_ ?_
    · exact AddSubgroup.closure_mono (Set.singleton_subset_iff.2 (Finset.mem_coe.2 hα)) (hsM m)
    · have hmap : (AddSubgroup.closure ((S.inv w' : Finset M) : Set M)).map (act s) ≤
          AddSubgroup.closure ((S.inv w : Finset M) : Set M) := by
        rw [AddMonoidHom.map_closure, AddSubgroup.closure_le]
        rintro _ ⟨γ, hγ, rfl⟩
        exact AddSubgroup.subset_closure (Finset.mem_of_mem_erase (hsub γ hγ))
      exact hmap (AddSubgroup.mem_map_of_mem _ hIH)

/-- **`InversionData` from the root system** (no longer an input). -/
noncomputable def toInversionData : InversionData Φ B act where
  twoRho := S.twoRho
  inv := S.inv
  inv_pos _ _ hγ := (S.mem_inv.1 hγ).1
  rho_eq := S.rho_eq
  range_le w m := S.range_le _ w rfl m

lemma mem_closure_translate (v : W) (x : M) :
    x ∈ AddSubmonoid.closure (act v '' B) ↔ act v⁻¹ x ∈ AddSubmonoid.closure B := by
  rw [← AddMonoidHom.map_mclosure, AddSubmonoid.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩; rwa [S.act_inv_act]
  · intro h; exact ⟨_, h, S.act_act_inv v x⟩

/-- The `W`-translate `vB` of the basis is again a simple system (`s_{vα} = v s_α v⁻¹`). -/
theorem translate (v : W) : SimpleSystem Φ (act v '' B) act where
  finite := S.finite
  basis_sub := by rintro _ ⟨α, hα, rfl⟩; exact S.act_mem v α (S.basis_sub hα)
  pos_or_neg α hα := by
    rw [S.mem_closure_translate, S.mem_closure_translate, map_neg]
    exact S.pos_or_neg _ (S.act_mem _ α hα)
  pointed α hα := by
    rw [S.mem_closure_translate, S.mem_closure_translate, map_neg]
    exact S.pointed _ (S.act_mem _ α hα)
  neg_mem := S.neg_mem
  act_mul := S.act_mul
  act_one := S.act_one
  act_mem := S.act_mem
  simple := by
    rintro _ ⟨α, hα, rfl⟩
    obtain ⟨s, hss, hsα, hspos, hsM⟩ := S.simple α hα
    have hconj : ∀ m, act (v * s * v⁻¹) m = act v (act s (act v⁻¹ m)) := fun m => by
      rw [S.act_mul, S.act_mul]
    refine ⟨v * s * v⁻¹, ?_, ?_, ?_, ?_⟩
    · rw [show v * s * v⁻¹ * (v * s * v⁻¹) = v * (s * s) * v⁻¹ by group, hss, mul_one,
        mul_inv_cancel]
    · rw [hconj, S.act_inv_act, hsα, map_neg]
    · intro β hβ hβB hne
      rw [S.mem_closure_translate] at hβB ⊢
      rw [hconj, S.act_inv_act]
      exact hspos _ (S.act_mem _ _ hβ) hβB (fun h => hne (by rw [← h, S.act_act_inv]))
    · intro m
      have : m - act (v * s * v⁻¹) m = act v (act v⁻¹ m - act s (act v⁻¹ m)) := by
        rw [map_sub, S.act_act_inv, hconj]
      rw [this, ← Set.image_singleton, ← AddMonoidHom.map_closure]
      exact AddSubgroup.mem_map_of_mem _ (hsM _)
  coxeter := by
    intro w hw m
    have h := S.coxeter (v⁻¹ * w * v) (fun γ hγ hγB => by
      have h1 := hw (act v γ) (S.act_mem _ _ hγ)
        (by rw [S.mem_closure_translate, S.act_inv_act]; exact hγB)
      rw [S.mem_closure_translate] at h1
      rwa [S.act_mul, S.act_mul]) (act v⁻¹ m)
    rw [S.act_mul, S.act_mul, S.act_act_inv] at h
    have h2 := congrArg (act v) h
    rwa [S.act_act_inv, S.act_act_inv] at h2

/-- `Φ⁺ ∩ v⁻¹(Φ \ R)`: positive roots that `v` sends outside `R`. -/
noncomputable def bad (R : Set M) (v : W) : Finset M := by
  classical exact S.pos.filter (fun β => act v β ∉ R)

lemma mem_bad {R : Set M} {v : W} {β : M} :
    β ∈ S.bad R v ↔ (β ∈ Φ ∧ β ∈ AddSubmonoid.closure B) ∧ act v β ∉ R := by
  classical
  unfold bad; rw [Finset.mem_filter, S.mem_pos]

/-- **Bourbaki VI §1 Prop. 20.** An additively stable `R ⊆ Φ` with `R ∪ -R = Φ` contains the
positive system `Φ ∩ ℕ(vB)` of some `W`-translate `vB` of the basis (minimise `|vΦ⁺ \ R|`: if
it is nonzero, some `vα ∉ R` with `α ∈ B`, and `v s_α` does better). -/
theorem exists_translate_pos_sub_of {R : Set M}
    (hstep : ∀ v : W, (∀ α ∈ B, act v α ∈ R) →
      ∀ β ∈ Φ, β ∈ AddSubmonoid.closure B → act v β ∈ R) (hu : R ∪ -R = Φ) :
    ∃ v : W, Φ ∩ AddSubmonoid.closure (act v '' B) ⊆ R := by
  classical
  suffices h : ∀ n (v : W), (S.bad R v).card = n → ∃ v' : W, (S.bad R v').card = 0 by
    obtain ⟨v, hv⟩ := h _ 1 rfl
    refine ⟨v, fun γ ⟨hγ, hγB⟩ => ?_⟩
    rw [SetLike.mem_coe, S.mem_closure_translate] at hγB
    by_contra hγR
    have hmem : act v⁻¹ γ ∈ S.bad R v := by
      rw [S.mem_bad, S.act_act_inv]; exact ⟨⟨S.act_mem _ _ hγ, hγB⟩, hγR⟩
    rw [Finset.card_eq_zero] at hv
    rw [hv] at hmem
    simp at hmem
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro v hv
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨v, hv⟩
  obtain ⟨α, hαB, hαR⟩ : ∃ α ∈ B, act v α ∉ R := by
    by_contra hall
    push Not at hall
    obtain ⟨β, hβ⟩ := Finset.card_pos.1 (hv ▸ hn)
    rw [S.mem_bad] at hβ
    exact hβ.2 (hstep v hall β hβ.1.1 hβ.1.2)
  obtain ⟨s, hss, hsα, hspos, -⟩ := S.simple α hαB
  have hαmem : α ∈ S.bad R v := by
    rw [S.mem_bad]
    exact ⟨⟨S.basis_sub hαB, AddSubmonoid.subset_closure hαB⟩, hαR⟩
  have hss' : ∀ m, act s (act s m) = m := fun m => by rw [← S.act_mul, hss, S.act_one]
  have hlt : (S.bad R (v * s)).card < n := by
    rw [← hv]
    calc (S.bad R (v * s)).card ≤ ((S.bad R v).erase α).card := by
          refine Finset.card_le_card_of_injOn (act s) ?_ ?_
          · intro β hβ
            have hβ' := S.mem_bad.1 (Finset.mem_coe.1 hβ)
            have hβα : β ≠ α := by
              rintro rfl
              rw [S.act_mul, hsα, map_neg] at hβ'
              have hvα := S.act_mem v β (S.basis_sub hαB)
              rw [← hu] at hvα
              rcases hvα with h | h
              · exact hαR h
              · exact hβ'.2 (Set.mem_neg.1 h)
            refine Finset.mem_coe.2 (Finset.mem_erase.2 ⟨fun h => ?_, S.mem_bad.2
              ⟨⟨S.act_mem _ _ hβ'.1.1, hspos β hβ'.1.1 hβ'.1.2 hβα⟩, by
                rw [← S.act_mul]; exact hβ'.2⟩⟩)
            have : β = -α := by rw [← hss' β, h, hsα]
            exact S.pointed α (S.basis_sub hαB) (AddSubmonoid.subset_closure hαB)
              (this ▸ hβ'.1.2)
          · intro x _ y _ h
            simpa [hss'] using congrArg (act s) h
      _ < (S.bad R v).card := Finset.card_erase_lt_of_mem hαmem
  exact ih _ hlt (v * s) rfl


/-- **Bourbaki VI §1 Prop. 20** (additively stable form). -/
theorem exists_translate_pos_sub {R : Set M} (hR : IsStableElt Φ R) (hu : R ∪ -R = Φ) :
    ∃ v : W, Φ ∩ AddSubmonoid.closure (act v '' B) ⊆ R := by
  refine S.exists_translate_pos_sub_of (fun v hall β hβ hβB => ?_) hu
  have hle : AddSubmonoid.closure B ≤ (AddSubmonoid.closure R).comap (act v) := by
    rw [AddSubmonoid.closure_le]
    intro α hα
    exact AddSubmonoid.subset_closure (hall α hα)
  rw [← hR.2]
  exact ⟨hle hβB, S.act_mem _ _ hβ⟩

end SimpleSystem

variable {P : AddSubmonoid M → Prop}

/-- **Theorem `thm:red-parabolic`, bijection, from the root system.** -/
theorem bijOn_parabolic_of_simpleSystem (H : ReductiveInput P Φ act) (S : SimpleSystem Φ B act)
    (hneg : ∀ α ∈ Φ, -α ∈ Φ) :
    Set.BijOn (fun N : AddSubmonoid M => (N : Set M) ∩ Φ) {N | P N ∧ B ⊆ N}
        {R | IsStableElt Φ R ∧ Φ ∩ AddSubmonoid.closure B ⊆ R} ∧
      Set.InvOn AddSubmonoid.closure (fun N : AddSubmonoid M => (N : Set M) ∩ Φ)
        {N | P N ∧ B ⊆ N} {R | IsStableElt Φ R ∧ Φ ∩ AddSubmonoid.closure B ⊆ R} :=
  bijOn_parabolic H S.toInversionData hneg S.basis_sub

/-- **Theorem `thm:red-parabolic`, bijection onto all parabolic subsets.** `𝔅` a family of bases
with simple systems; `hProp20` is Bourbaki VI §1 Prop. 20 (a parabolic subset contains a
positive system `Φ⁺_B`, `B ∈ 𝔅`). Target: additively stable `R` with `R ∪ -R = Φ`. -/
theorem bijOn_parabolic_all_of_prop20 (H : ReductiveInput P Φ act) (𝔅 : Set (Set M))
    (S : ∀ B ∈ 𝔅, SimpleSystem Φ B act) (hneg : ∀ α ∈ Φ, -α ∈ Φ)
    (hProp20 : ∀ R, IsStableElt Φ R → R ∪ -R = Φ →
      ∃ B ∈ 𝔅, Φ ∩ AddSubmonoid.closure B ⊆ R) :
    Set.BijOn (fun N : AddSubmonoid M => (N : Set M) ∩ Φ) {N | P N ∧ ∃ B ∈ 𝔅, B ⊆ N}
        {R | IsStableElt Φ R ∧ R ∪ -R = Φ} ∧
      Set.InvOn AddSubmonoid.closure (fun N : AddSubmonoid M => (N : Set M) ∩ Φ)
        {N | P N ∧ ∃ B ∈ 𝔅, B ⊆ N} {R | IsStableElt Φ R ∧ R ∪ -R = Φ} := by
  have hT : {R | IsStableElt Φ R ∧ ∃ B ∈ 𝔅, Φ ∩ AddSubmonoid.closure B ⊆ R} =
      {R | IsStableElt Φ R ∧ R ∪ -R = Φ} := by
    ext R
    refine ⟨fun ⟨hR, B, hB, hpos⟩ => ⟨hR, union_neg_eq_of_parabolic (S B hB).pos_or_neg hneg
      hR.1 hpos⟩, fun ⟨hR, hu⟩ => ⟨hR, hProp20 R hR hu⟩⟩
  rw [← hT]
  exact bijOn_parabolic_someBasis H 𝔅 (fun B hB => (S B hB).toInversionData) hneg
    (fun B hB => (S B hB).basis_sub)

/-- **Theorem `thm:red-parabolic`, bijection onto all parabolic subsets, hypothesis-free.**
`N ↦ N ∩ Φ` is a bijection from the pure magnets containing some basis `vB` (`v ∈ W`) onto the
additively stable `R ⊆ Φ` with `R ∪ -R = Φ`, with inverse `R ↦ [R⟩` (Bourbaki VI §1 Prop. 20
is `SimpleSystem.exists_translate_pos_sub`). -/
theorem bijOn_parabolic_all (H : ReductiveInput P Φ act) (S : SimpleSystem Φ B act) :
    Set.BijOn (fun N : AddSubmonoid M => (N : Set M) ∩ Φ)
        {N | P N ∧ ∃ B' ∈ Set.range (fun v : W => act v '' B), B' ⊆ N}
        {R | IsStableElt Φ R ∧ R ∪ -R = Φ} ∧
      Set.InvOn AddSubmonoid.closure (fun N : AddSubmonoid M => (N : Set M) ∩ Φ)
        {N | P N ∧ ∃ B' ∈ Set.range (fun v : W => act v '' B), B' ⊆ N}
        {R | IsStableElt Φ R ∧ R ∪ -R = Φ} :=
  bijOn_parabolic_all_of_prop20 H _ (fun _ hB => by obtain ⟨v, rfl⟩ := hB; exact S.translate v)
    S.neg_mem (fun R hR hu => by
      obtain ⟨v, hv⟩ := S.exists_translate_pos_sub hR hu
      exact ⟨_, ⟨v, rfl⟩, hv⟩)

end Inversion

section Geometric

open Magnetism TauCeti TauCeti.Cocharacter
open scoped TensorProduct

universe u

variable {k : Type u} {H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]

/-- **Theorem `thm:red-parabolic`, last assertion, over a field: `G^{[B ∪ -ξ⟩} = P_ξ`.**
`G` smooth of finite type, geometrically connected, `T = D(X)` acting, roots `Φ = roots π`,
`B ⊆ ℕ`-basis with `Φ ⊆ ℕB ∪ -ℕB`, `ξ ⊆ B`, and `λ = ψ` a cocharacter with `⟨λ, ξ⟩ = 0`,
`⟨λ, B \ ξ⟩ > 0`. Then the attractor of `ℕB + ℕ(-ξ)` is the parabolic `P(λ) = P_ξ`. -/
theorem magnetIdeal_basis_neg_eq_parabolic {X : Type u} [CommGroup X] [DecidableEq X]
    [Algebra.FiniteType k H] [Algebra.Smooth k H]
    [ConnectedSpace (PrimeSpectrum (AlgebraicClosure k ⊗[k] H))]
    (π : H →ₐc[k] MonoidAlgebra k X) (ψ : X →* Multiplicative ℤ) {B ξ : Set (Additive X)}
    (hΦ : ∀ α ∈ AlgMag.Reductive.roots π, α ∈ AddSubmonoid.closure B ∨ -α ∈ AddSubmonoid.closure B)
    (hξ : ∀ α ∈ ξ, pairingHom ψ α = 0) (hpos : ∀ α ∈ B, α ∉ ξ → 0 < pairingHom ψ α) :
    magnetIdeal (torusGrading π) (AddSubmonoid.closure (B ∪ -ξ)) =
      (parabolicDefiningHopfIdeal (π.cocharacter ψ)).toIdeal := by
  have hB0 : ∀ α ∈ B, 0 ≤ pairingHom ψ α := fun α hα => by
    by_cases h : α ∈ ξ
    · rw [hξ α h]
    · exact (hpos α hα h).le
  have hle : AddSubmonoid.closure (B ∪ -ξ) ≤ natMagnet.comap (pairingHom ψ) := by
    rw [AddSubmonoid.closure_le]
    rintro α (h | h)
    · exact mem_natMagnet.2 (hB0 α h)
    · have := hξ _ (Set.mem_neg.1 h)
      show 0 ≤ pairingHom ψ α
      rw [map_neg] at this; omega
  refine OpenCell.magnetIdeal_eq_parabolic_of_field π ψ hle ?_
  ext α
  constructor
  · rintro ⟨hα, hr⟩; exact ⟨hle hα, hr⟩
  · rintro ⟨hα, hr⟩
    refine ⟨?_, hr⟩
    have hα' : 0 ≤ pairingHom ψ α := hα
    rcases hΦ α hr with h | h
    · exact AddSubmonoid.closure_mono Set.subset_union_left h
    · have h' := mem_closure_of_pairing_nonpos (pairingHom ψ) hB0 hpos h (by rw [map_neg]; omega)
      have := neg_mem_of_mem_closure (S := ξ) (N := AddSubmonoid.closure (B ∪ -ξ))
        (fun β hβ => AddSubmonoid.subset_closure (Or.inr (by simpa using hβ))) h'
      simpa using this

end Geometric

end AlgMag.Reductive.Parabolic
