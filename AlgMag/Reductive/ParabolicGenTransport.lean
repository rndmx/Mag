/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.ParabolicGenStep

/-!
# Transport of the λ-filtration to a closed subgroup `P(λ) ⊇ Spec (H ⧸ I) ⊇ λ`

For a Hopf ideal `I` with `I_{P(λ)} ≤ I ≤ ker λ`, the cocharacter descends to `λ_I` on `H ⧸ I`,
`P(λ_I)` is everything, and `J_n(λ_I)` pulls back to `J_n(λ) ⊔ I`. With TorusConjDyn
`unipotentFiltrationPoints_surjective` on `H ⧸ I` this gives `qLift_surjective`: every functional
on `λ`-degree-`n` coordinates killing `J_n ⊔ I` is the restriction of a point of
`V(I) ∩ U_{≥n}`. (ParabolicGenStep is the case `I = I_P`.)
-/

suppress_compilation

open TensorProduct Magnetism TauCeti TauCeti.Cocharacter WithConv

namespace AlgMag.Reductive

universe u

variable {k : Type u} [Field k] {H : Type u} [CommRing H] [HopfAlgebra k H] [DecidableEq H]
  [Algebra.FiniteType k H] [Algebra.Smooth k H]
variable (l : H →ₐc[k] LaurentPolynomial k) (I : HopfIdeal k H)

/-- The quotient map `H → H ⧸ I`. -/
abbrev qMk : H →ₐc[k] H ⧸ I.toIdeal := Bialgebra.Quotient.mkBialgHom I.toIdeal

variable {I} in
/-- The induced cocharacter `λ_I` on `H ⧸ I`. -/
noncomputable def qCochar (hIl : I.toIdeal ≤ RingHom.ker (l : H →ₐ[k] LaurentPolynomial k)) :
    (H ⧸ I.toIdeal) →ₐc[k] LaurentPolynomial k :=
  descBialgHom (qMk I) Ideal.Quotient.mk_surjective l (by
    intro x hx
    have : x ∈ I.toIdeal := by
      simpa [qMk, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] using hx
    exact hIl this)

variable {I} (hIl : I.toIdeal ≤ RingHom.ker (l : H →ₐ[k] LaurentPolynomial k))
  (hIP : (parabolicDefiningHopfIdeal l).toIdeal ≤ I.toIdeal)

lemma qCochar_comp : (qCochar l hIl).comp (qMk I) = l := descBialgHom_comp _ _ _ _

lemma coeff_conj_qMk (x : H) (m : ℤ) :
    (conjugationAlgHom (qCochar l hIl) (qMk I x)).coeff m =
      qMk I ((conjugationAlgHom l x).coeff m) := by
  rw [conjugationAlgHom_natural l (qMk I) (qCochar l hIl) (qCochar_comp l hIl),
    AddMonoidAlgebra.coeff_mapAlgHom]
  rfl

include hIP in
theorem parabolic_qCochar_eq_bot [DecidableEq (H ⧸ I.toIdeal)] :
    parabolicDefiningHopfIdeal (qCochar l hIl) = ⊥ := by
  apply HopfIdeal.ext
  intro y
  rw [HopfIdeal.mem_bot]
  refine ⟨fun hy => ?_, fun hy => hy ▸ (parabolicDefiningHopfIdeal (qCochar l hIl)).toIdeal.zero_mem⟩
  have hy' : y ∈ (parabolicDefiningHopfIdeal (qCochar l hIl)).toIdeal := HopfIdeal.mem_toIdeal.2 hy
  rw [parabolicDefiningHopfIdeal_toIdeal (qCochar l hIl)] at hy'
  have hle : Ideal.span {x | ∃ h, ∃ n : ℤ, n < 0 ∧ (conjugationAlgHom (qCochar l hIl) h).coeff n = x}
      ≤ ⊥ := by
    rw [Ideal.span_le]
    rintro _ ⟨h, n, hn, rfl⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective h
    change (conjugationAlgHom (qCochar l hIl) ((qMk I) x)).coeff n ∈ (⊥ : Ideal _)
    rw [coeff_conj_qMk, Ideal.mem_bot]
    have hm : (conjugationAlgHom l x).coeff n ∈ (parabolicDefiningHopfIdeal l).toIdeal := by
      rw [parabolicDefiningHopfIdeal_toIdeal l]
      exact Ideal.subset_span ⟨x, n, hn, rfl⟩
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hIP hm)
  exact (Ideal.mem_bot).1 (hle hy')

lemma qMk_mem_lineGrading {m : ℤ} {x : H} (hx : x ∈ lineGrading l m) :
    qMk I x ∈ lineGrading (qCochar l hIl) m := by
  have h := coeff_mem_lineGrading (l := qCochar l hIl) (qMk I x) m
  rw [coeff_conj_qMk, coeff_of_mem_lineGrading (l := l) hx] at h
  simpa using h

lemma exists_lift_lineGrading_q {m : ℤ} {y : H ⧸ I.toIdeal}
    (hy : y ∈ lineGrading (qCochar l hIl) m) : ∃ x ∈ lineGrading l m, qMk I x = y := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨_, coeff_mem_lineGrading (l := l) x m, ?_⟩
  have h := coeff_conj_qMk l hIl x m
  have hy' : qMk I x ∈ lineGrading (qCochar l hIl) m := hy
  rw [coeff_of_mem_lineGrading (l := qCochar l hIl) hy'] at h
  simpa using h.symm

include hIP in
theorem filtrationIdeal_comap_q [DecidableEq (H ⧸ I.toIdeal)] (n : ℕ) :
    (filtrationIdeal (qCochar l hIl) n).comap (Ideal.Quotient.mk I.toIdeal) =
      filtrationIdeal l n ⊔ I.toIdeal := by
  set f := Ideal.Quotient.mk I.toIdeal
  have hgen : ∀ h : H, f ((conjugationAlgHom l h).coeff 0 -
      algebraMap k H (Coalgebra.counit (R := k) h)) =
      (conjugationAlgHom (qCochar l hIl) (f h)).coeff 0 -
        algebraMap k _ (Coalgebra.counit (R := k) (f h)) := by
    intro h
    have e1 := coeff_conj_qMk l hIl h 0
    have e2 : Coalgebra.counit (R := k) (qMk I h) = Coalgebra.counit (R := k) h :=
      CoalgHomClass.counit_comp_apply (qMk I) h
    change qMk I _ = (conjugationAlgHom (qCochar l hIl) (qMk I h)).coeff 0 -
      algebraMap k _ (Coalgebra.counit (R := k) (qMk I h))
    rw [e1, e2, map_sub]
    congr 1
  have hPbot : Ideal.map f (parabolicDefiningHopfIdeal l).toIdeal = ⊥ := by
    rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]; exact hIP
  have hunip : Ideal.map f (BialgHom.unipotentDefiningHopfIdeal l).toIdeal =
      (BialgHom.unipotentDefiningHopfIdeal (qCochar l hIl)).toIdeal := by
    rw [BialgHom.unipotentDefiningHopfIdeal_toIdeal l,
      BialgHom.unipotentDefiningHopfIdeal_toIdeal (qCochar l hIl), Ideal.map_sup, Ideal.map_span,
      hPbot, parabolic_qCochar_eq_bot l hIl hIP, HopfIdeal.bot_toIdeal, bot_sup_eq, bot_sup_eq]
    congr 1
    ext y
    constructor
    · rintro ⟨_, ⟨h, rfl⟩, rfl⟩
      exact ⟨f h, (hgen h).symm⟩
    · rintro ⟨y', rfl⟩
      obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective y'
      exact ⟨_, ⟨h, rfl⟩, hgen h⟩
  have hspan : Ideal.map f (Ideal.span (⋃ (m : ℕ) (_ : 0 < m ∧ m < n),
        (lineGrading l (m : ℤ) : Set H))) =
      Ideal.span (⋃ (m : ℕ) (_ : 0 < m ∧ m < n),
        (lineGrading (qCochar l hIl) (m : ℤ) : Set _)) := by
    rw [Ideal.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨m, hm, hx⟩ := Set.mem_iUnion₂.1 hx
      exact Set.mem_iUnion₂.2 ⟨m, hm, qMk_mem_lineGrading l hIl hx⟩
    · intro hy
      obtain ⟨m, hm, hy⟩ := Set.mem_iUnion₂.1 hy
      obtain ⟨x, hx, rfl⟩ := exists_lift_lineGrading_q l hIl hy
      exact ⟨x, Set.mem_iUnion₂.2 ⟨m, hm, hx⟩, rfl⟩
  have hmap : Ideal.map f (filtrationIdeal l n) = filtrationIdeal (qCochar l hIl) n := by
    simp only [filtrationIdeal]
    rw [Ideal.map_sup, hunip, hspan]
  rw [← hmap, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]

include hIl hIP in
/-- **Points of `V(I) ∩ U_{≥n}` realize every admissible functional on degree-`n` coordinates.** -/
theorem qLift_surjective [Algebra.Smooth k (H ⧸ I.toIdeal)] {n : ℕ} (hn : 0 < n)
    (f : lineGrading l (n : ℤ) →ₗ[k] k)
    (hf : ∀ w : lineGrading l (n : ℤ), (w : H) ∈ filtrationIdeal l n ⊔ I.toIdeal → f w = 0) :
    ∃ u : WithConv (H →ₐ[k] k), filtrationIdeal l n ⊔ I.toIdeal ≤ RingHom.ker u.ofConv ∧
      ∀ w : lineGrading l (n : ℤ), u.ofConv w = f w := by
  classical
  let ρ : lineGrading l (n : ℤ) →ₗ[k] lineGrading (qCochar l hIl) (n : ℤ) :=
    LinearMap.codRestrict _ ((qMk I : H →ₐ[k] H ⧸ I.toIdeal).toLinearMap ∘ₗ
      (lineGrading l (n : ℤ)).subtype) fun w => qMk_mem_lineGrading l hIl w.2
  have hρ : Function.Surjective ρ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := exists_lift_lineGrading_q l hIl hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : LinearMap.ker ρ ≤ LinearMap.ker f := by
    intro w hw
    rw [LinearMap.mem_ker] at hw ⊢
    apply hf
    have h0 : qMk I (w : H) = 0 := congrArg Subtype.val hw
    exact Ideal.mem_sup_right (Ideal.Quotient.eq_zero_iff_mem.1 h0)
  let φ := ((LinearMap.ker ρ).liftQ f hker).comp
    (LinearMap.quotKerEquivOfSurjective ρ hρ).symm.toLinearMap
  have hφρ : ∀ w, φ (ρ w) = f w := by
    intro w
    have : (LinearMap.quotKerEquivOfSurjective ρ hρ).symm (ρ w) = (LinearMap.ker ρ).mkQ w := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    show (LinearMap.ker ρ).liftQ f hker ((LinearMap.quotKerEquivOfSurjective ρ hρ).symm (ρ w)) = f w
    rw [this]
    rfl
  have hcomap := filtrationIdeal_comap_q l hIl hIP n
  have hφ : ∀ w : lineGrading (qCochar l hIl) (n : ℤ),
      (w : H ⧸ I.toIdeal) ∈ filtrationIdeal (qCochar l hIl) n → φ w = 0 := by
    intro w hw
    obtain ⟨w', rfl⟩ := hρ w
    rw [hφρ]
    apply hf
    rw [← hcomap]
    exact hw
  obtain ⟨ub, hub, hubv⟩ := unipotentFiltrationPoints_surjective (qCochar l hIl)
    (parabolic_qCochar_eq_bot l hIl hIP) hn φ hφ
  refine ⟨toConv (ub.ofConv.comp (qMk I : H →ₐ[k] H ⧸ I.toIdeal)), ?_, ?_⟩
  · intro y hy
    rw [← hcomap] at hy
    exact hub hy
  · intro w
    have := hubv (ρ w)
    rw [hφρ] at this
    exact this

end AlgMag.Reductive
