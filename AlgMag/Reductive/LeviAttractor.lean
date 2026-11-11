/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.ComponentsMeetNormalizerProof

/-!
# The Levi subgroup as the attractor of the group magnet `ℤζ`

`G` split reductive over an algebraically closed field `k` with root datum
(`SplitReductiveData.WithRootDatum`), `T = D(X)`, `X` a lattice, base `B`, `ζ ⊆ B`, and a
cocharacter `λ = ψ` with `⟨λ, α⟩ = 0` for `α ∈ ζ` and `⟨λ, α⟩ > 0` for `α ∈ B \ ζ`. Then
`G^{[ζ ∪ -ζ⟩} = G^{f⁻¹(0)} = Z_G(λ)` (`f = ⟨·, λ⟩`), the Levi subgroup of `P_ζ`.

Proof: `hdet_lattice` (Theorem `thm:red-attractors`) for `ℤζ = [ζ ∪ -ζ⟩ ⊆ f⁻¹(0)`.
* roots (`mem_closure_symm_of_root`): a root `α` with `⟨λ, α⟩ = 0` lies in `ℕζ` or `-ℕζ`
  (coefficients in `B` all of one sign, and those off `ζ` vanish);
* Weyl part: if `Z_w ⊆ f⁻¹(0) ⊆ f⁻¹(ℕ) ⊇ B`, then `Z_w ⊆ [f⁻¹(ℕ) ∩ Φ⟩`
  (`Parabolic.weylMagnet_le_closure_inter`, the inversion-set argument), and an element of
  `[f⁻¹(ℕ) ∩ Φ⟩` with `f = 0` is a sum of roots killed by `f`, hence lies in `ℤζ`
  (`mem_of_mem_closure_of_eq_zero`).
The Levi identification is `magnetIdeal_torusGrading_comap_bot` (`PushCocharacter.lean`).
The hypothesis `ζ ⊆ B` is not used.
-/

suppress_compilation

open Magnetism TauCeti TauCeti.Cocharacter WithConv

namespace AlgMag.Reductive

section Combinatorial

variable {M : Type*} [AddCommGroup M]

/-- If every generator `s ∈ S` has `f s ≥ 0`, and `f s = 0` forces `s ∈ T`, then every
`z ∈ [S⟩` has `f z ≥ 0`, and `f z = 0` forces `z ∈ T`. -/
lemma mem_of_mem_closure_of_eq_zero (f : M →+ ℤ) {S : Set M} {T : AddSubmonoid M}
    (hS : ∀ s ∈ S, 0 ≤ f s ∧ (f s = 0 → s ∈ T)) {z : M} (hz : z ∈ AddSubmonoid.closure S) :
    0 ≤ f z ∧ (f z = 0 → z ∈ T) := by
  induction hz using AddSubmonoid.closure_induction with
  | mem x hx => exact hS x hx
  | zero => exact ⟨by simp, fun _ => zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    rw [map_add]
    exact ⟨add_nonneg hx1 hy1, fun h => add_mem (hx2 (by omega)) (hy2 (by omega))⟩

/-- **Roots of `ℤζ`.** With `Φ ⊆ ℕB ∪ -ℕB`, `f = 0` on `ζ` and `f > 0` on `B \ ζ`: a root
`α` with `f α = 0` lies in `[ζ ∪ -ζ⟩`. -/
lemma mem_closure_symm_of_root (f : M →+ ℤ) {Φ B ζ : Set M}
    (hΦ : ∀ α ∈ Φ, α ∈ AddSubmonoid.closure B ∨ -α ∈ AddSubmonoid.closure B)
    (hζ : ∀ α ∈ ζ, f α = 0) (hpos : ∀ α ∈ B, α ∉ ζ → 0 < f α) {α : M} (hα : α ∈ Φ)
    (h0 : f α = 0) : α ∈ AddSubmonoid.closure (ζ ∪ -ζ) := by
  have hB0 : ∀ β ∈ B, 0 ≤ f β := fun β hβ => by
    by_cases h : β ∈ ζ
    · rw [hζ β h]
    · exact (hpos β hβ h).le
  rcases hΦ α hα with h | h
  · exact AddSubmonoid.closure_mono Set.subset_union_left
      (Parabolic.mem_closure_of_pairing_nonpos f hB0 hpos h h0.le)
  · have h' := Parabolic.mem_closure_of_pairing_nonpos f hB0 hpos h (by rw [map_neg]; omega)
    have := Parabolic.neg_mem_of_mem_closure (S := ζ) (N := AddSubmonoid.closure (ζ ∪ -ζ))
      (fun β hβ => AddSubmonoid.subset_closure (Or.inr (by simpa using hβ))) h'
    simpa using this

end Combinatorial

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable {π : H →ₐc[k] MonoidAlgebra k X}
variable [IsAlgClosed k] [Algebra.FiniteType k H] [Algebra.Smooth k H]
  [Module.Finite k (Bialgebra.CotangentSpace k H)] [Monoid.FG X] [IsMulTorsionFree X]

/-- **`G^{[ζ ∪ -ζ⟩} = G^{f⁻¹(0)}`.** `G` split reductive with root datum and base `B`,
`f = ⟨·, λ⟩` vanishing on `ζ` and positive on `B \ ζ`. -/
theorem magnetIdeal_closure_symm_eq_comap_bot (D : SplitReductiveData.WithRootDatum π)
    (ψ : X →* Multiplicative ℤ) {ζ : Set (Additive X)}
    (hζ : ∀ α ∈ ζ, pairingHom ψ α = 0)
    (hpos : ∀ α ∈ D.P.root '' D.b.support, α ∉ ζ → 0 < pairingHom ψ α) :
    magnetIdeal (torusGrading π) (AddSubmonoid.closure (ζ ∪ -ζ)) =
      magnetIdeal (torusGrading π) ((⊥ : Magnet ℤ).comap (pairingHom ψ)) := by
  set f := pairingHom ψ
  have S := RootSystem.RootDatum.simpleSystem D.P D.b
  have hB0 : ∀ α ∈ D.P.root '' D.b.support, 0 ≤ f α := fun α hα => by
    by_cases h : α ∈ ζ
    · rw [hζ α h]
    · exact (hpos α hα h).le
  have hΦ : ∀ α ∈ roots π, α ∈ AddSubmonoid.closure (D.P.root '' D.b.support) ∨
      -α ∈ AddSubmonoid.closure (D.P.root '' D.b.support) := by
    rw [← D.range_root]; exact S.pos_or_neg
  have hroot : ∀ α ∈ roots π, f α = 0 → α ∈ AddSubmonoid.closure (ζ ∪ -ζ) :=
    fun α hα h0 => mem_closure_symm_of_root f hΦ hζ hpos hα h0
  have hmem0 : ∀ x, x ∈ (⊥ : Magnet ℤ).comap f ↔ f x = 0 := fun x => by
    rw [AddSubmonoid.mem_comap, AddSubmonoid.mem_bot]
  have hle : AddSubmonoid.closure (ζ ∪ -ζ) ≤ (⊥ : Magnet ℤ).comap f := by
    rw [AddSubmonoid.closure_le]
    rintro α (h | h)
    · exact (hmem0 α).2 (hζ α h)
    · have := hζ _ (Set.mem_neg.1 h)
      rw [map_neg, neg_eq_zero] at this
      exact (hmem0 α).2 this
  have h0nat : (⊥ : Magnet ℤ).comap f ≤ natMagnet.comap f := fun x hx => by
    have := (hmem0 x).1 hx
    show f x ∈ natMagnet
    rw [mem_natMagnet]; omega
  have hBN : D.P.root '' D.b.support ⊆ natMagnet.comap f := fun α hα => by
    show f α ∈ natMagnet
    exact mem_natMagnet.2 (hB0 α hα)
  refine ((affineY_eq_iff _).1 (hdet_lattice D.toSplitReductiveData _ _ hle
    (fun a ha haN => hroot a ha ((hmem0 a).1 haN)) fun w hw => ?_))
  obtain ⟨g, hg⟩ : actW (w : X ≃* X) ∈
      Set.range (fun g : D.P.weylGroup => RootSystem.RootDatum.act D.P g) := by
    rw [D.weyl_eq]; exact ⟨w, rfl⟩
  simp only at hg
  rw [← hg] at hw ⊢
  have hcl := Parabolic.weylMagnet_le_closure_inter S.toInversionData S.neg_mem hBN
    (hw.trans h0nat)
  intro z hz
  refine (mem_of_mem_closure_of_eq_zero f (fun s hs => ⟨hs.1, fun h0 => hroot s
    (D.range_root ▸ hs.2) h0⟩) (hcl hz)).2 ((hmem0 z).1 (hw hz))

/-- **`G^{[ζ ∪ -ζ⟩} = Z_G(λ)`**, the Levi subgroup: for `G` split reductive with root datum
over `k = k̄`, `X` a lattice, `ζ` a set of simple roots (more generally any `ζ`) and a
cocharacter `λ` with `⟨λ, ζ⟩ = 0`, `⟨λ, B \ ζ⟩ > 0`, the attractor of the group magnet
`ℤζ = [ζ ∪ -ζ⟩` is the centralizer `Z_G(λ)`. -/
theorem magnetIdeal_closure_symm_eq_levi (D : SplitReductiveData.WithRootDatum π)
    (ψ : X →* Multiplicative ℤ) {ζ : Set (Additive X)}
    (hζ : ∀ α ∈ ζ, pairingHom ψ α = 0)
    (hpos : ∀ α ∈ D.P.root '' D.b.support, α ∉ ζ → 0 < pairingHom ψ α) :
    magnetIdeal (torusGrading π) (AddSubmonoid.closure (ζ ∪ -ζ)) =
      (leviDefiningHopfIdeal (π.cocharacter ψ)).toIdeal := by
  rw [magnetIdeal_closure_symm_eq_comap_bot D ψ hζ hpos, magnetIdeal_torusGrading_comap_bot]

/-- Points form: `G^{[ζ ∪ -ζ⟩}(A) = Z_G(λ)(A)` for every `k`-algebra `A`. -/
theorem magnetIdeal_closure_symm_le_ker_iff (D : SplitReductiveData.WithRootDatum π)
    (ψ : X →* Multiplicative ℤ) {ζ : Set (Additive X)}
    (hζ : ∀ α ∈ ζ, pairingHom ψ α = 0)
    (hpos : ∀ α ∈ D.P.root '' D.b.support, α ∉ ζ → 0 < pairingHom ψ α)
    {A : Type*} [CommRing A] [Algebra k A] (g : WithConv (H →ₐ[k] A)) :
    magnetIdeal (torusGrading π) (AddSubmonoid.closure (ζ ∪ -ζ)) ≤ RingHom.ker g.ofConv ↔
      g ∈ levi A (π.cocharacter ψ) := by
  rw [magnetIdeal_closure_symm_eq_comap_bot D ψ hζ hpos]
  exact magnetIdeal_torusGrading_comap_bot_le_ker_iff g

end AlgMag.Reductive
