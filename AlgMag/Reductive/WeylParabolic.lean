/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.ComponentsMeetNormalizerProof

/-!
# `W_N = W_ξ` for a magnet `N ⊇ B`

`Φ` a reduced crystallographic root system with base `B`, `W = ⟨s_α : α ∈ B⟩`, `N ⊇ B` a
magnet and `ξ = {α ∈ B | -α ∈ N}`. Then

  `W_N := {w | (1 - w)M ⊆ N} = W_ξ := ⟨s_α : α ∈ ξ⟩`.

* `sub_mem_of_mem_closure_xi` (`⊇`): `(1 - s_α)M ⊆ ℤα ⊆ N` for `α ∈ ξ` (`±α ∈ N`);
* `exists_mem_closure_xi` (`⊆`): induction on `|Inv(w)|`; a simple root `α ∈ Inv(w)` has
  `-α ∈ N` (the `2ρ` argument, `neg_inv_mem`), so `α ∈ ξ`, and `s_α w` has a smaller inversion
  set and still `(1 - s_α w)M ⊆ N`;
* `weylMagnet_le_iff`, `weylN_eq_closure_xi` (faithful action);
* `RootDatum.weylN_eq_closure_xi`: for a Mathlib root datum;
* `WithRootDatum.parabolic_weyl`: for `G`, `G^N = P(λ)` and `W_N = W_ξ`.
-/

suppress_compilation

namespace AlgMag.Reductive.Parabolic

open AlgMag.Rooted

section Combinatorial

variable {M : Type*} [AddCommGroup M] {Φ B : Set M} {W : Type*} [Group W]
  {act : W → M →+ M} {refl : M → W} {coroot : M → M →+ ℤ}

lemma zsmul_mem_of_neg_mem {N : AddSubmonoid M} {α : M} (h1 : α ∈ N) (h2 : -α ∈ N) (n : ℤ) :
    n • α ∈ N := by
  rcases n with n | n
  · rw [Int.ofNat_eq_natCast, natCast_zsmul]; exact nsmul_mem h1 n
  · rw [negSucc_zsmul, ← neg_nsmul]; exact nsmul_mem h2 _

/-- **`W_ξ ⊆ W_N`**: `(1 - v)M ⊆ N` (and `(v - 1)M ⊆ N`) for `v ∈ ⟨s_α : α ∈ ξ⟩`. -/
theorem sub_mem_of_mem_closure_xi (S : RootSystem.WeylSystem Φ B act refl coroot)
    {N : AddSubmonoid M} (hBN : B ⊆ N) {v : W} (hv : v ∈ Subgroup.closure (refl '' xi B N)) :
    ∀ m, m - act v m ∈ N ∧ act v m - m ∈ N := by
  induction hv using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hα, rfl⟩ := hx
    intro m
    rw [S.refl_act α hα.1]
    constructor
    · rw [sub_sub_cancel]; exact zsmul_mem_of_neg_mem (hBN hα.1) hα.2 _
    · rw [sub_sub_cancel_left, ← neg_zsmul]; exact zsmul_mem_of_neg_mem (hBN hα.1) hα.2 _
  | one => intro m; simp [S.act_one]
  | mul x y _ _ hx hy =>
    intro m
    rw [S.act_mul]
    constructor
    · have : m - act x (act y m) = (m - act y m) + (act y m - act x (act y m)) := by abel
      rw [this]; exact add_mem (hy m).1 (hx _).1
    · have : act x (act y m) - m = (act x (act y m) - act y m) + (act y m - m) := by abel
      rw [this]; exact add_mem (hx _).2 (hy m).2
  | inv x _ hx =>
    intro m
    have hm : act x (act x⁻¹ m) = m := by rw [← S.act_mul, mul_inv_cancel, S.act_one]
    obtain ⟨h1, h2⟩ := hx (act x⁻¹ m)
    rw [hm] at h1 h2
    exact ⟨h2, h1⟩

/-- **`W_N ⊆ W_ξ`**, by induction on `|Inv(w)|`: if `(1 - w)M ⊆ N` then `w` acts as an element
of `⟨s_α : α ∈ ξ⟩`. -/
theorem exists_mem_closure_xi (S : RootSystem.WeylSystem Φ B act refl coroot)
    (hfin : Φ.Finite)
    (hpn : ∀ α ∈ Φ, α ∈ AddSubmonoid.closure B ∨ -α ∈ AddSubmonoid.closure B)
    (hneg : ∀ α ∈ Φ, -α ∈ Φ) {N : AddSubmonoid M} (hBN : B ⊆ N) :
    ∀ n (w : W), ((SimpleSystem.ofWeyl S hfin hpn hneg).inv w).card = n →
      Rooted.weylMagnet (act w) ≤ N →
      ∃ v ∈ Subgroup.closure (refl '' xi B N), ∀ m, act v m = act w m := by
  classical
  have T := SimpleSystem.ofWeyl S hfin hpn hneg
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w hn hw
  rcases ((SimpleSystem.ofWeyl S hfin hpn hneg).inv w).eq_empty_or_nonempty with he | ⟨γ0, hγ0⟩
  · refine ⟨1, one_mem _, fun m => ?_⟩
    have hfix := T.coxeter w⁻¹ (fun γ hγ hγB => by
      by_contra h
      have : γ ∈ (SimpleSystem.ofWeyl S hfin hpn hneg).inv w :=
        (SimpleSystem.ofWeyl S hfin hpn hneg).mem_inv.2 ⟨⟨hγ, hγB⟩, h⟩
      rw [he] at this; simp at this)
    rw [S.act_one]
    conv_rhs => rw [← hfix m]
    exact ((SimpleSystem.ofWeyl S hfin hpn hneg).act_act_inv w m).symm
  · set T := SimpleSystem.ofWeyl S hfin hpn hneg with hT
    obtain ⟨α, hαB, hα⟩ : ∃ α ∈ B, α ∈ T.inv w := by
      by_contra h
      push Not at h
      have hle : AddSubmonoid.closure B ≤
          (AddSubmonoid.closure B).comap (act w⁻¹) := by
        rw [AddSubmonoid.closure_le]
        intro α hαB
        by_contra hn
        exact h α hαB (T.mem_inv.2 ⟨⟨S.basis_sub hαB, AddSubmonoid.subset_closure hαB⟩, hn⟩)
      have h0 := T.mem_inv.1 hγ0
      exact h0.2 (hle h0.1.2)
    have hαinv := T.mem_inv.1 hα
    have hαξ : α ∈ xi B N := ⟨hαB, neg_inv_mem T.toInversionData hBN hw hα⟩
    have hss : refl α * refl α = 1 := S.refl_sq α hαB
    have hsinv : (refl α)⁻¹ = refl α := inv_eq_of_mul_eq_one_right hss
    have hsα : act (refl α) α = -α := S.act_refl_self hαB
    have hspos := S.refl_pos α hαB
    have hsub : ∀ γ ∈ T.inv (refl α * w), act (refl α) γ ∈ (T.inv w).erase α := by
      intro γ hγ
      have hγ' := T.mem_inv.1 hγ
      have hw'inv : (refl α * w)⁻¹ = w⁻¹ * refl α := by rw [mul_inv_rev, hsinv]
      rw [hw'inv, S.act_mul] at hγ'
      have hγα : γ ≠ α := by
        rintro rfl
        rw [hsα, map_neg] at hγ'
        exact hγ'.2 (T.neg_mem_of_not (S.act_mem _ _ hαinv.1.1) hαinv.2)
      have hsγ := hspos γ hγ'.1.1 hγ'.1.2 hγα
      refine Finset.mem_erase.2 ⟨?_, T.mem_inv.2 ⟨⟨S.act_mem _ γ hγ'.1.1, hsγ⟩, hγ'.2⟩⟩
      intro heq
      have : γ = -α := by
        have := congrArg (act (refl α)) heq
        rw [← S.act_mul, hss, S.act_one, hsα] at this
        exact this
      exact S.pointed α hαinv.1.1 hαinv.1.2 (this ▸ hγ'.1.2)
    have hcard : (T.inv (refl α * w)).card < n := by
      calc (T.inv (refl α * w)).card ≤ (((T.inv w).erase α).image (act (refl α))).card := by
            refine Finset.card_le_card fun γ hγ =>
              Finset.mem_image.2 ⟨act (refl α) γ, hsub γ hγ, ?_⟩
            rw [← S.act_mul, hss, S.act_one]
        _ ≤ ((T.inv w).erase α).card := Finset.card_image_le
        _ < n := by rw [Finset.card_erase_of_mem hα, ← hn]; exact Nat.sub_lt
                      (Finset.card_pos.2 ⟨α, hα⟩) one_pos
    have hw' : Rooted.weylMagnet (act (refl α * w)) ≤ N := by
      intro z hz
      obtain ⟨m, rfl⟩ := mem_weylMagnet.1 hz
      have h1 : m - act w m ∈ N := hw (mem_weylMagnet.2 ⟨m, rfl⟩)
      have h2 : act w m - act (refl α) (act w m) ∈ N := by
        rw [S.refl_act α hαB, sub_sub_cancel]
        exact zsmul_mem_of_neg_mem (hBN hαB) hαξ.2 _
      have : m - act (refl α * w) m = (m - act w m) + (act w m - act (refl α) (act w m)) := by
        rw [S.act_mul]; abel
      rw [this]; exact add_mem h1 h2
    obtain ⟨v', hv', hv'w⟩ := ih _ hcard (refl α * w) rfl hw'
    refine ⟨refl α * v', mul_mem (Subgroup.subset_closure ⟨α, hαξ, rfl⟩) hv', fun m => ?_⟩
    rw [S.act_mul, hv'w, S.act_mul, ← S.act_mul (refl α) (refl α), hss, S.act_one]

/-- **`W_N = W_ξ`** (in the action): `(1 - w)M ⊆ N` iff `w` acts as an element of
`⟨s_α : α ∈ ξ⟩`, for a magnet `N ⊇ B`. -/
theorem weylMagnet_le_iff (S : RootSystem.WeylSystem Φ B act refl coroot)
    (hfin : Φ.Finite)
    (hpn : ∀ α ∈ Φ, α ∈ AddSubmonoid.closure B ∨ -α ∈ AddSubmonoid.closure B)
    (hneg : ∀ α ∈ Φ, -α ∈ Φ) {N : AddSubmonoid M} (hBN : B ⊆ N) (w : W) :
    Rooted.weylMagnet (act w) ≤ N ↔
      ∃ v ∈ Subgroup.closure (refl '' xi B N), ∀ m, act v m = act w m := by
  constructor
  · exact exists_mem_closure_xi S hfin hpn hneg hBN _ w rfl
  · rintro ⟨v, hv, hvw⟩ z hz
    obtain ⟨m, rfl⟩ := mem_weylMagnet.1 hz
    rw [← hvw]
    exact (sub_mem_of_mem_closure_xi S hBN hv m).1

/-- **`W_N = W_ξ`** as subsets of `W`, for a faithful action. -/
theorem weylN_eq_closure_xi (S : RootSystem.WeylSystem Φ B act refl coroot)
    (hfin : Φ.Finite)
    (hpn : ∀ α ∈ Φ, α ∈ AddSubmonoid.closure B ∨ -α ∈ AddSubmonoid.closure B)
    (hneg : ∀ α ∈ Φ, -α ∈ Φ) (hfaith : ∀ v w : W, (∀ m, act v m = act w m) → v = w)
    {N : AddSubmonoid M} (hBN : B ⊆ N) :
    {w : W | Rooted.weylMagnet (act w) ≤ N} = (Subgroup.closure (refl '' xi B N) : Set W) := by
  ext w
  rw [Set.mem_ofPred_eq, weylMagnet_le_iff S hfin hpn hneg hBN w, SetLike.mem_coe]
  constructor
  · rintro ⟨v, hv, hvw⟩
    rwa [← hfaith v w hvw]
  · intro hw
    exact ⟨w, hw, fun _ => rfl⟩

end Combinatorial

end AlgMag.Reductive.Parabolic

namespace AlgMag.Reductive.RootSystem.RootDatum

open Set RootPairing

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) (b : P.Base)

/-- The Weyl group of a root pairing acts faithfully on `M`. -/
lemma act_injective {v w : P.weylGroup} (h : ∀ m, act P v m = act P w m) : v = w := by
  apply Subtype.ext
  apply Equiv.weightHom_injective P
  exact LinearEquiv.ext h

variable [Finite ι] [P.IsCrystallographic] [P.IsReduced]

/-- **`W_N = W_ξ` for a Mathlib root datum**: for a magnet `N ⊇ B`,
`{w | (1 - w)M ⊆ N} = ⟨s_α : α ∈ ξ⟩`, `ξ = {α ∈ B | -α ∈ N}`. -/
theorem weylN_eq_closure_xi {L : AddSubmonoid M} (hBL : P.root '' b.support ⊆ L) :
    {w : P.weylGroup | Rooted.weylMagnet (act P w) ≤ L} =
      (Subgroup.closure (refl P '' Parabolic.xi (P.root '' b.support) L) : Set P.weylGroup) :=
  Parabolic.weylN_eq_closure_xi (weylSystem P b) (finite_range _)
    (by rintro _ ⟨i, rfl⟩; exact b.root_mem_or_neg_mem i)
    (by rintro _ ⟨i, rfl⟩; exact P.neg_mem_range_root_iff.2 ⟨i, rfl⟩)
    (fun _ _ h => act_injective P h) hBL

end AlgMag.Reductive.RootSystem.RootDatum

namespace AlgMag.Reductive

open Magnetism TauCeti WithConv TauCeti.Cocharacter
open scoped TensorProduct

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable [IsAlgClosed k] [Algebra.FiniteType k H] [Algebra.Smooth k H]
  [Module.Finite k (Bialgebra.CotangentSpace k H)]
variable [Monoid.FG X] [IsMulTorsionFree X]
variable {π : H →ₐc[k] MonoidAlgebra k X}

namespace SplitReductiveData.WithRootDatum

omit [IsAlgClosed k] [Algebra.FiniteType k H] [Algebra.Smooth k H] [Monoid.FG X]
  [IsMulTorsionFree X] in
/-- **`W_N = W_ξ` for `G`**: for a magnet `N ⊇ B`, `w ∈ W` has `(1 - w)X ⊆ N` iff `w` acts on
`X` as an element of `⟨s_α : α ∈ ξ⟩ ⊆ W(P)`. -/
theorem weylMagnet_le_iff (D : SplitReductiveData.WithRootDatum π)
    {N : AddSubmonoid (Additive X)} (hBN : D.P.root '' D.b.support ⊆ N) (w : D.W) :
    Rooted.weylMagnet (actW (w : X ≃* X)) ≤ N ↔
      ∃ v ∈ Subgroup.closure
          (RootSystem.RootDatum.refl D.P '' Parabolic.xi (D.P.root '' D.b.support) N),
        RootSystem.RootDatum.act D.P v = actW (w : X ≃* X) := by
  obtain ⟨g, hg⟩ : actW (w : X ≃* X) ∈
      Set.range (fun g : D.P.weylGroup => RootSystem.RootDatum.act D.P g) := by
    rw [D.weyl_eq]; exact ⟨w, rfl⟩
  simp only at hg
  rw [← hg, Parabolic.weylMagnet_le_iff (RootSystem.RootDatum.weylSystem D.P D.b)
    (Set.finite_range _) (by rintro _ ⟨i, rfl⟩; exact D.b.root_mem_or_neg_mem i)
    (by rintro _ ⟨i, rfl⟩; exact D.P.neg_mem_range_root_iff.2 ⟨i, rfl⟩) hBN g]
  exact ⟨fun ⟨v, hv, h⟩ => ⟨v, hv, AddMonoidHom.ext h⟩,
    fun ⟨v, hv, h⟩ => ⟨v, hv, fun m => by rw [h]⟩⟩

/-- **Theorem `thm:red-parabolic` with the Weyl part**: for a magnet `N ⊇ B`,
`ξ = {α ∈ B | -α ∈ N}` and `λ` vanishing on `ξ`, positive on `B \ ξ`: `G^N = P(λ)` and
`W_N = W_ξ` (`W_N = {w | (1 - w)X ⊆ N}`, `W_ξ = ⟨s_α : α ∈ ξ⟩`). -/
theorem parabolic_weyl (D : SplitReductiveData.WithRootDatum π)
    [ConnectedSpace (PrimeSpectrum (AlgebraicClosure k ⊗[k] H))]
    (ψ : X →* Multiplicative ℤ) {N : AddSubmonoid (Additive X)}
    (hBN : D.P.root '' D.b.support ⊆ N)
    (hξ : ∀ α ∈ Parabolic.xi (D.P.root '' D.b.support) N, pairingHom ψ α = 0)
    (hpos : ∀ α ∈ D.P.root '' D.b.support,
      α ∉ Parabolic.xi (D.P.root '' D.b.support) N → 0 < pairingHom ψ α) :
    magnetIdeal (torusGrading π) N =
        (parabolicDefiningHopfIdeal (π.cocharacter ψ)).toIdeal ∧
      (∀ w : D.W, Rooted.weylMagnet (actW (w : X ≃* X)) ≤ N ↔
        ∃ v ∈ Subgroup.closure
            (RootSystem.RootDatum.refl D.P '' Parabolic.xi (D.P.root '' D.b.support) N),
          RootSystem.RootDatum.act D.P v = actW (w : X ≃* X)) ∧
      {v : D.P.weylGroup | Rooted.weylMagnet (RootSystem.RootDatum.act D.P v) ≤ N} =
        (Subgroup.closure (RootSystem.RootDatum.refl D.P ''
          Parabolic.xi (D.P.root '' D.b.support) N) : Set D.P.weylGroup) :=
  ⟨red_parabolic_lattice D ψ hBN hξ hpos, D.weylMagnet_le_iff hBN,
    RootSystem.RootDatum.weylN_eq_closure_xi D.P D.b hBN⟩

end SplitReductiveData.WithRootDatum

end AlgMag.Reductive
