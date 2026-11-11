/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.OpenCell.OpenCellFlatness
import AlgMag.Reductive.ComponentsMeetNormalizerProof
import AlgMag.Reductive.RootDatumFromGPairing
import AlgMag.Reductive.RegularSlice

/-!
# An element of `W` fixing a Weyl chamber is trivial, magnetically

`G` smooth, connected, of finite type over an algebraically closed field `k`, with split
reductive data `D` (`T = D(X)`, `X` a lattice, `W = N_G(T)/T`). For a magnet map
`f : X → ℤ` which is *regular* (`f α ≠ 0` for every root `α`):

* `compIdeal_levi`: the Levi subgroup `G^{f⁻¹(0)} = Z_G(λ_f)` is connected (open cell,
  `isOpenEmbedding_openCell`), so it equals its identity component;
* `mem_bot_of_mem_levi`: `G^{f⁻¹(0)}(k) ⊆ G^0(k)`: `f⁻¹(0)` contains no root, so
  `(G^{f⁻¹(0)})° = (G^0)° = T` (`compIdeal_eq_of_roots`, `hT_lattice`);
* `eq_one_of_pairing_invariant`: if `w ∈ W` fixes `f` (`f ∘ w = f`), then `w = 1`: `n_w` lies in
  `G^{f⁻¹(0)}` since `(1 - w)X ⊆ f⁻¹(0)` (`mem_attractorSubgroup_iff_joinIrredWeylMagnets`), hence in
  `G^0`, hence `(1 - w)X ⊆ 0`;
* `eq_one_of_preserves_pos` (**key lemma**): if `w ∈ W` preserves the positive system
  `Φ⁺_f = {α ∈ Φ | f α > 0}`, then `w = 1`. Replace `f` by `f' = Σ_{j < ord w} f ∘ w^j`: it is
  `w`-invariant, and regular with `Φ⁺_{f'} = Φ⁺_f` since every `w^j` preserves `Φ⁺_f`.

Generation (`D : WithReflections π`, `rootPairing` reduced, a base `b`):
* `exists_pos_comp`: `W(Φ)` is transitive on chambers (`exists_translate_pos_sub_of`);
* `exists_weylGroup_rootPairing`: every `w ∈ W` acts as an element of `W(Φ)`, the input `hW` of
  `WithReflections.toWithRootDatum`; `WeylAlt.toWithRootDatum` assembles `WithRootDatum`.
-/

suppress_compilation

open Magnetism TauCeti WithConv TauCeti.Cocharacter AlgMag.Weyl
open scoped TensorProduct

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable [IsAlgClosed k] [Algebra.FiniteType k H] [Algebra.Smooth k H]
  [Module.Finite k (Bialgebra.CotangentSpace k H)]
variable {π : H →ₐc[k] MonoidAlgebra k X}

namespace WeylAlt

/-- The cocharacter `ψ` with `⟨·, ψ⟩ = f`. -/
def cochar (f : Additive X →+ ℤ) : X →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (f (Additive.ofMul x))
  map_one' := by simp
  map_mul' x y := by rw [ofMul_mul, map_add, ofAdd_add]

omit [DecidableEq X] in
lemma pairingHom_cochar (f : Additive X →+ ℤ) : pairingHom (cochar f) = f := by
  ext χ
  rfl

variable [ConnectedSpace (PrimeSpectrum H)]

omit [DecidableEq X] [Module.Finite k (Bialgebra.CotangentSpace k H)] in
/-- **The Levi subgroup `Z(λ)` of a connected `G` is connected** (open cell). -/
lemma connectedSpace_levi (ψ : X →* Multiplicative ℤ) :
    ConnectedSpace (PrimeSpectrum (H ⧸ (leviDefiningHopfIdeal (π.cocharacter ψ)).toIdeal)) := by
  have : IrreducibleSpace (PrimeSpectrum H) := OpenCellNotes.irreducibleSpace_of_connectedSpace k
  exact connectedSpace_levi_of_openCell _ (isOpenEmbedding_openCell _)

omit [Module.Finite k (Bialgebra.CotangentSpace k H)] in
/-- **`G^{f⁻¹(0)}` is connected**: `(G^{f⁻¹(0)})° = G^{f⁻¹(0)}`. -/
lemma compIdeal_levi (ψ : X →* Multiplicative ℤ) :
    compIdeal π ((⊥ : Magnet ℤ).comap (pairingHom ψ)) =
      magnetIdeal (torusGrading π) ((⊥ : Magnet ℤ).comap (pairingHom ψ)) := by
  set Z := (⊥ : Magnet ℤ).comap (pairingHom ψ)
  set B := H ⧸ (magnetHopfIdeal π Z).toIdeal
  have hJ : (magnetHopfIdeal π Z).toIdeal =
      (leviDefiningHopfIdeal (π.cocharacter ψ)).toIdeal := by
    rw [magnetHopfIdeal_toIdeal, magnetIdeal_torusGrading_comap_bot]
  have : Algebra.FiniteType k B :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k _) (Ideal.Quotient.mkₐ_surjective k _)
  let e : B ≃ₐ[k] H ⧸ (leviDefiningHopfIdeal (π.cocharacter ψ)).toIdeal :=
    Ideal.quotientEquivAlgOfEq k hJ
  have hL := connectedSpace_levi (π := π) ψ
  have hB : ConnectedSpace (PrimeSpectrum B) :=
    (PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv).symm.connectedSpace_iff.mp hL
  have hbot : attrComp π Z = ⊥ :=
    (HopfAlgebra.identityComponentHopfIdeal_eq_bot_iff_connectedSpace (k := k) (H := B)).2 hB
  ext x
  show Ideal.Quotient.mk _ (Ideal.Quotient.mk _ x) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, hbot, HopfIdeal.bot_toIdeal, Ideal.mem_bot,
    Ideal.Quotient.eq_zero_iff_mem, magnetHopfIdeal_toIdeal]

variable [Monoid.FG X] [IsMulTorsionFree X]

/-- **`Z_G(λ_f)(k) = T(k)` for `f` regular**: `G^{f⁻¹(0)}(k) ⊆ G^0(k)`. -/
theorem mem_bot_of_mem_levi (D : SplitReductiveData π) (f : Additive X →+ ℤ)
    (hreg : ∀ α ∈ roots π, f α ≠ 0) {g : WithConv (H →ₐ[k] k)}
    (hg : g ∈ attractorSubgroup π ((⊥ : Magnet ℤ).comap f) k) :
    g ∈ attractorSubgroup π ⊥ k := by
  have hZ := compIdeal_levi (π := π) (cochar f)
  rw [pairingHom_cochar] at hZ
  have hroots : compIdeal π ⊥ = compIdeal π ((⊥ : Magnet ℤ).comap f) :=
    compIdeal_eq_of_roots π bot_le fun α hα =>
      ⟨fun h => (bot_le : (⊥ : Magnet (Additive X)) ≤ _) h, fun h =>
        absurd (AddSubmonoid.mem_bot.1 (AddSubmonoid.mem_comap.1 h)) (hreg α hα)⟩
  rw [mem_attractorSubgroup] at hg ⊢
  intro x hx
  rw [magnetIdeal_bot_eq_ker π D, RingHom.mem_ker] at hx
  have hx1 : x ∈ compIdeal π ⊥ := (hT_lattice D x).2 hx
  rw [hroots, hZ] at hx1
  exact hg hx1

/-- **An element of `W` fixing a regular `f` is trivial.** -/
theorem eq_one_of_pairing_invariant (D : SplitReductiveData π) (f : Additive X →+ ℤ)
    (hreg : ∀ α ∈ roots π, f α ≠ 0) (w : D.W) (hw : ∀ χ : Additive X, f (w • χ) = f χ) :
    w = 1 := by
  have hn := D.rep_normalizing w
  have h1 : D.rep w ∈ attractorSubgroup π ((⊥ : Magnet ℤ).comap f) k := by
    rw [mem_attractorSubgroup_iff_joinIrredWeylMagnets π D.surjective hn]
    rintro _ ⟨χ, rfl⟩
    rw [SetLike.mem_coe, AddSubmonoid.mem_comap, AddSubmonoid.mem_bot, map_sub]
    exact sub_eq_zero.2 (hw χ).symm
  have h2 := mem_bot_of_mem_levi D f hreg h1
  rw [mem_attractorSubgroup_iff_joinIrredWeylMagnets π D.surjective hn] at h2
  refine weyl_ext fun χ => ?_
  have h3 := h2 ⟨χ, rfl⟩
  rw [SetLike.mem_coe, AddSubmonoid.mem_bot, sub_eq_zero] at h3
  rw [one_smul]
  exact h3.symm

/-- **Key lemma: an element of `W` preserving a positive system is trivial.** For `f` regular
and `w ∈ W` with `w(Φ⁺_f) = Φ⁺_f` (`Φ⁺_f = {α ∈ Φ | f α > 0}`), `w = 1`. -/
theorem eq_one_of_preserves_pos (D : SplitReductiveData π) (f : Additive X →+ ℤ)
    (hreg : ∀ α ∈ roots π, f α ≠ 0) (w : D.W)
    (hw : ∀ α ∈ roots π, 0 < f (w • α) ↔ 0 < f α) : w = 1 := by
  have : Finite D.W := D.finite
  obtain ⟨m, hm⟩ : ∃ m, orderOf w = m + 1 :=
    Nat.exists_eq_succ_of_ne_zero (orderOf_pos w).ne'
  let f' : Additive X →+ ℤ :=
    ∑ j ∈ Finset.range (m + 1), f.comp (DistribSMul.toAddMonoidHom (Additive X) (w ^ j))
  have hf' : ∀ χ, f' χ = ∑ j ∈ Finset.range (m + 1), f ((w ^ j) • χ) := by
    intro χ
    simp [f', DistribSMul.toAddMonoidHom_apply]
  have hmem : ∀ (v : D.W) {α : Additive X}, α ∈ roots π → v • α ∈ roots π :=
    fun v α hα => D.roots_stable (v : X ≃* X) v.2 α hα
  refine eq_one_of_pairing_invariant D f' ?_ w ?_
  · intro α hα
    have hpow : ∀ j : ℕ, (w ^ j) • α ∈ roots π ∧ (0 < f ((w ^ j) • α) ↔ 0 < f α) := by
      intro j
      induction j with
      | zero => simp [hα]
      | succ j ih =>
        rw [pow_succ', mul_smul]
        exact ⟨hmem w ih.1, (hw _ ih.1).trans ih.2⟩
    rw [hf']
    rcases lt_or_gt_of_ne (hreg α hα) with h | h
    · refine (Finset.sum_neg (fun j _ => ?_) ⟨0, by simp⟩).ne
      have h1 := hreg _ (hpow j).1
      have h2 : ¬ 0 < f ((w ^ j) • α) := fun h' => absurd ((hpow j).2.1 h') (not_lt.2 h.le)
      omega
    · exact (Finset.sum_pos (fun j _ => (hpow j).2.2 h) ⟨0, by simp⟩).ne'
  · intro χ
    rw [hf', hf']
    simp_rw [← mul_smul, ← pow_succ]
    rw [Finset.sum_range_succ, Finset.sum_range_succ', ← hm, pow_orderOf_eq_one, pow_zero]

/-! ### `W(Φ)` is transitive on chambers -/

section Chambers

variable {M : Type*} [AddCommGroup M] {Φ B : Set M} {W : Type*} [Group W] {act : W → M →+ M}

/-- **`W(Φ)` is transitive on chambers.** For `g` nonzero on `Φ` there is `v ∈ W(Φ)` with
`g ∘ v > 0` on `Φ⁺ = Φ ∩ ℕB` (Bourbaki VI §1 Prop. 20, `exists_translate_pos_sub_of`, for the
additively stable `R = {β ∈ Φ | g β > 0}`). -/
theorem exists_pos_comp (S : Parabolic.SimpleSystem Φ B act) (h0 : (0 : M) ∉ Φ) (g : M →+ ℤ)
    (hg : ∀ β ∈ Φ, g β ≠ 0) :
    ∃ v : W, ∀ γ ∈ Φ, γ ∈ AddSubmonoid.closure B → 0 < g (act v γ) := by
  set R : Set M := {β | β ∈ Φ ∧ 0 < g β}
  have hstep : ∀ v : W, (∀ α ∈ B, act v α ∈ R) →
      ∀ β ∈ Φ, β ∈ AddSubmonoid.closure B → act v β ∈ R := by
    intro v hv β hβ hβB
    have key : ∀ x ∈ AddSubmonoid.closure B, x = 0 ∨ 0 < g (act v x) := by
      intro x hx
      induction hx using AddSubmonoid.closure_induction with
      | mem x hx => exact Or.inr (hv x hx).2
      | zero => exact Or.inl rfl
      | add x y _ _ hx hy =>
        rcases hx with rfl | hx
        · rw [zero_add]; exact hy
        · right
          rcases hy with rfl | hy
          · rw [add_zero]; exact hx
          · rw [map_add, map_add]; exact add_pos hx hy
    rcases key β hβB with rfl | h
    · exact absurd hβ h0
    · exact ⟨S.act_mem v β hβ, h⟩
  have hu : R ∪ -R = Φ := by
    ext β
    simp only [Set.mem_union, Set.mem_neg, R, Set.mem_ofPred_eq]
    constructor
    · rintro (h | h)
      · exact h.1
      · simpa using S.neg_mem _ h.1
    · intro hβ
      rcases lt_or_gt_of_ne (hg β hβ) with h | h
      · right; exact ⟨S.neg_mem β hβ, by rw [map_neg]; omega⟩
      · left; exact ⟨hβ, h⟩
  obtain ⟨v, hv⟩ := S.exists_translate_pos_sub_of hstep hu
  refine ⟨v, fun γ hγ hγB => (hv ⟨S.act_mem v γ hγ, ?_⟩).2⟩
  have : act v γ ∈ AddSubmonoid.closure (act v '' B) := by
    rw [← AddMonoidHom.map_mclosure]
    exact AddSubmonoid.mem_map_of_mem _ hγB
  exact this

end Chambers

/-! ### `W = W(Φ)` -/

section Generation

variable [Module.IsTorsionFree ℤ (Additive X)] [Module.Finite ℤ (Additive X)]
variable (D : SplitReductiveData.WithReflections π)

/-- **`W ⊆ W(Φ)`: the Weyl group `N_G(T)/T` of a connected `G` is generated by the reflections
`s_α`.** Every `w ∈ W` acts on `X` as an element of the Weyl group of `rootPairing`.
Proof: `f₁ = f₀ ∘ v₁` dominant regular (`exists_generic_cocharacter`, `exists_pos_comp`);
`v₂ ∈ W(Φ)` with `f₁ ∘ w⁻¹ ∘ v₂ > 0` on `Φ⁺` (`exists_pos_comp`); `u = w⁻¹ v₂` preserves the
chamber of `f₁`, so `u = 1` (`eq_one_of_preserves_pos`). -/
theorem exists_weylGroup_rootPairing [D.rootPairing.IsReduced] (b : D.rootPairing.Base)
    (w : D.W) : ∃ g : D.rootPairing.weylGroup,
      ∀ m : Additive X, (g : D.rootPairing.Aut) • m = w • m := by
  classical
  have S := RootSystem.RootDatum.simpleSystem D.rootPairing b
  rw [D.range_root_rootPairing] at S
  have h0 : (0 : Additive X) ∉ roots π := fun h => ne_zero_of_mem_roots h rfl
  have : Module.Free ℤ (Additive X) := Module.free_of_finite_type_torsion_free'
  obtain ⟨ψ, hψ⟩ := exists_generic_cocharacter (roots π) (finite_roots (π := π))
    (fun α hα => ne_zero_of_mem_roots hα)
  have hmem : ∀ (v : D.W) {α : Additive X}, α ∈ roots π → v • α ∈ roots π :=
    fun v α hα => D.roots_stable (v : X ≃* X) v.2 α hα
  obtain ⟨v1, hv1⟩ := exists_pos_comp S h0 (pairingHom ψ) hψ
  set f1 := (pairingHom ψ).comp (RootSystem.RootDatum.act D.rootPairing v1)
  have hf1 : ∀ γ ∈ roots π, f1 γ ≠ 0 := fun γ hγ => hψ _ (S.act_mem v1 γ hγ)
  obtain ⟨v2, hv2⟩ := exists_pos_comp S h0
    (f1.comp (DistribSMul.toAddMonoidHom (Additive X) w⁻¹)) (fun β hβ => hf1 _ (hmem w⁻¹ hβ))
  obtain ⟨w2, hw2⟩ := D.exists_weyl_of_weylGroup_rootPairing v2
  have hu : ∀ γ ∈ roots π, γ ∈ AddSubmonoid.closure (D.rootPairing.root '' b.support) →
      0 < f1 ((w⁻¹ * w2) • γ) := by
    intro γ hγ hγB
    have h := hv2 γ hγ hγB
    rw [mul_smul, ← hw2]
    exact h
  have hpos : ∀ α ∈ roots π, 0 < f1 ((w⁻¹ * w2) • α) ↔ 0 < f1 α := by
    intro α hα
    rcases S.pos_or_neg α hα with h | h
    · exact ⟨fun _ => hv1 α hα h, fun _ => hu α hα h⟩
    · have hn := S.neg_mem α hα
      have h1 : 0 < f1 (-α) := hv1 _ hn h
      have h2 : 0 < f1 ((w⁻¹ * w2) • -α) := hu _ hn h
      rw [map_neg] at h1
      rw [smul_neg, map_neg] at h2
      constructor <;> intro h' <;> omega
  have h1 := eq_one_of_preserves_pos D.toSplitReductiveData f1 hf1 (w⁻¹ * w2) hpos
  have h2 : w = w2 := inv_mul_eq_one.mp h1
  exact ⟨v2, fun m => by rw [hw2, h2]⟩

/-- **`WithRootDatum` from `G`** connected, given reducedness and a base: the input `hW` of
`toWithRootDatum` is `exists_weylGroup_rootPairing`. -/
noncomputable def toWithRootDatum [D.rootPairing.IsReduced] (b : D.rootPairing.Base) :
    SplitReductiveData.WithRootDatum π :=
  D.toWithRootDatum b (exists_weylGroup_rootPairing D b)

end Generation

end WeylAlt

end AlgMag.Reductive
