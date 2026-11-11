/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.TuStep
import TauCeti.Algebra.AlgebraicGroup.Dynamic.Smooth
import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Comap
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Basic

/-!
# (a): transporting the λ-filtration to the parabolic quotient `H ⧸ I_{P(λ)}`

TuStep's `exists_vecQuotient` assumes `P(λ) = G` (`DynHyp.hP`). For general `G` it is applied to
`P(λ) = Spec (H ⧸ I_P)` with the induced cocharacter `λ̄`.
-/

suppress_compilation

open TensorProduct Magnetism TauCeti TauCeti.Cocharacter WithConv

namespace AlgMag.Reductive

universe u

variable {k : Type u} [Field k] {H : Type u} [CommRing H] [HopfAlgebra k H] [DecidableEq H]
  [Algebra.FiniteType k H] [Algebra.Smooth k H]
variable (l : H →ₐc[k] LaurentPolynomial k)

/-- `λ` lands in `P(λ)`: `I_{P(λ)} ⊆ ker λ` (the generic point lies in the Levi). -/
theorem parabolic_le_ker_cocharacter :
    (parabolicDefiningHopfIdeal l).toIdeal ≤ RingHom.ker (l : H →ₐ[k] LaurentPolynomial k) := by
  intro x hx
  have hmem : genericPoint k l ∈ parabolic (LaurentPolynomial k) l :=
    levi_le_parabolic (genericPoint_mem_levi (A := k) l)
  have hle := (TauCeti.Cocharacter.negativeCoefficientIdeal_le_ker_iff l _).2 hmem
  rw [parabolicDefiningHopfIdeal, HopfIdeal.ofIdealOfPointsSubgroup_toIdeal] at hx
  have hx' := hle hx
  rw [RingHom.mem_ker, genericPoint_ofConv] at hx'
  rw [RingHom.mem_ker]
  have hid : Algebra.ofId k k = AlgHom.id k k := Subsingleton.elim _ _
  rw [AlgHom.comp_apply, hid] at hx'
  have h2 : ∀ y : LaurentPolynomial k, AddMonoidAlgebra.mapAlgHom ℤ (AlgHom.id k k) y = y := by
    intro y; ext n; simp [AddMonoidAlgebra.mapAlgHom]
  rw [h2] at hx'
  exact hx' 

/-- The parabolic quotient map `H → H ⧸ I_{P(λ)}`. -/
abbrev parMk : H →ₐc[k] H ⧸ (parabolicDefiningHopfIdeal l).toIdeal :=
  Bialgebra.Quotient.mkBialgHom (parabolicDefiningHopfIdeal l).toIdeal

/-- The induced cocharacter `λ̄` of `P(λ)`. -/
noncomputable def parCochar :
    (H ⧸ (parabolicDefiningHopfIdeal l).toIdeal) →ₐc[k] LaurentPolynomial k :=
  descBialgHom (parMk l) Ideal.Quotient.mk_surjective l (by
    intro x hx
    have : x ∈ (parabolicDefiningHopfIdeal l).toIdeal := by
      simpa [parMk, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] using hx
    exact parabolic_le_ker_cocharacter l this)

/-- **Conjugation is natural along a bialgebra map compatible with the cocharacters.** -/
theorem conjugate_mapDomain {Q : Type u} [CommRing Q] [HopfAlgebra k Q] (f : H →ₐc[k] Q)
    (lQ : Q →ₐc[k] LaurentPolynomial k) (hl : lQ.comp f = l) {A : Type u} [CommRing A]
    [Algebra k A] (g : WithConv (Q →ₐ[k] A)) :
    conjugate A l (BialgHom.mapDomain f g) = BialgHom.mapDomain f (conjugate A lQ g) := by
  have hgen : genericPoint A l = BialgHom.mapDomain f (genericPoint A lQ) := by
    apply WithConv.ofConv_injective
    rw [BialgHom.mapDomain_apply, WithConv.ofConv_toConv, genericPoint_ofConv,
      genericPoint_ofConv, ← hl]
    rfl
  have hconst : constPoint A (BialgHom.mapDomain f g) = BialgHom.mapDomain f (constPoint A g) := by
    apply WithConv.ofConv_injective
    rw [BialgHom.mapDomain_apply, WithConv.ofConv_toConv]
    rfl
  rw [conjugate_apply, conjugate_apply, hgen, hconst, map_mul, map_mul, map_inv]

/-- **The universal conjugation is natural**: `conj_{λ_Q} ∘ f = f_* ∘ conj_λ`. -/
theorem conjugationAlgHom_natural {Q : Type u} [CommRing Q] [HopfAlgebra k Q] (f : H →ₐc[k] Q)
    (lQ : Q →ₐc[k] LaurentPolynomial k) (hl : lQ.comp f = l) (x : H) :
    conjugationAlgHom lQ (f x) =
      AddMonoidAlgebra.mapAlgHom ℤ (f : H →ₐ[k] Q) (conjugationAlgHom l x) := by
  have h1 := mapValue_conjugate_mapAlgHom (f : H →ₐ[k] Q) l (toConv (AlgHom.id k H))
  have h2 : AlgHom.mapValue (f : H →ₐ[k] Q) (toConv (AlgHom.id k H)) =
      BialgHom.mapDomain f (toConv (AlgHom.id k Q)) := by
    apply WithConv.ofConv_injective
    rw [BialgHom.mapDomain_apply]
    rfl
  rw [h2, conjugate_mapDomain l f lQ hl] at h1
  have h3 := congrArg (fun z => z.ofConv x) h1
  simp only [BialgHom.mapDomain_apply, WithConv.ofConv_toConv] at h3
  exact h3.symm

/-- **(a-i)** `P(λ̄) = P(λ)`: the dynamic parabolic of `λ̄` is everything. -/
theorem parabolic_parCochar_eq_bot [DecidableEq (H ⧸ (parabolicDefiningHopfIdeal l).toIdeal)] :
    parabolicDefiningHopfIdeal (parCochar l) = ⊥ := by
  have hl : (parCochar l).comp (parMk l) = l := descBialgHom_comp _ _ _ _
  apply HopfIdeal.ext
  intro y
  rw [HopfIdeal.mem_bot]
  refine ⟨fun hy => ?_, fun hy => hy ▸ (parabolicDefiningHopfIdeal (parCochar l)).toIdeal.zero_mem⟩
  have hy' : y ∈ (parabolicDefiningHopfIdeal (parCochar l)).toIdeal := HopfIdeal.mem_toIdeal.2 hy
  rw [parabolicDefiningHopfIdeal_toIdeal (parCochar l)] at hy'
  have hle : Ideal.span {x | ∃ h, ∃ n : ℤ, n < 0 ∧ (conjugationAlgHom (parCochar l) h).coeff n = x}
      ≤ ⊥ := by
    rw [Ideal.span_le]
    rintro _ ⟨h, n, hn, rfl⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective h
    have e := conjugationAlgHom_natural l (parMk l) (parCochar l) hl x
    change (conjugationAlgHom (parCochar l) ((parMk l) x)).coeff n ∈ (⊥ : Ideal _)
    rw [e, AddMonoidAlgebra.coeff_mapAlgHom, Ideal.mem_bot]
    have hm : (conjugationAlgHom l x).coeff n ∈ (parabolicDefiningHopfIdeal l).toIdeal := by
      rw [parabolicDefiningHopfIdeal_toIdeal l]
      exact Ideal.subset_span ⟨x, n, hn, rfl⟩
    exact Ideal.Quotient.eq_zero_iff_mem.2 hm
  exact (Ideal.mem_bot).1 (hle hy')

lemma parCochar_comp : (parCochar l).comp (parMk l) = l := descBialgHom_comp _ _ _ _

lemma coeff_conj_parMk (x : H) (m : ℤ) :
    (conjugationAlgHom (parCochar l) (parMk l x)).coeff m =
      parMk l ((conjugationAlgHom l x).coeff m) := by
  rw [conjugationAlgHom_natural l (parMk l) (parCochar l) (parCochar_comp l),
    AddMonoidAlgebra.coeff_mapAlgHom]
  rfl

lemma parMk_mem_lineGrading {m : ℤ} {x : H} (hx : x ∈ lineGrading l m) :
    parMk l x ∈ lineGrading (parCochar l) m := by
  have h := coeff_mem_lineGrading (l := parCochar l) (parMk l x) m
  rw [coeff_conj_parMk, coeff_of_mem_lineGrading (l := l) hx] at h
  simpa using h

lemma exists_lift_lineGrading {m : ℤ} {y : H ⧸ (parabolicDefiningHopfIdeal l).toIdeal}
    (hy : y ∈ lineGrading (parCochar l) m) : ∃ x ∈ lineGrading l m, parMk l x = y := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨_, coeff_mem_lineGrading (l := l) x m, ?_⟩
  have h := coeff_conj_parMk l x m
  have hy' : parMk l x ∈ lineGrading (parCochar l) m := hy
  rw [coeff_of_mem_lineGrading (l := parCochar l) hy'] at h
  simpa using h.symm

/-- **(a-ii)** the filtration pulls back: `J_n(λ̄) ∘ mk = J_n(λ)` (since `J_n(λ) ⊇ I_P`). -/
theorem filtrationIdeal_comap_parabolicQuotient
    [DecidableEq (H ⧸ (parabolicDefiningHopfIdeal l).toIdeal)] (n : ℕ) :
    (filtrationIdeal (parCochar l) n).comap
        (Ideal.Quotient.mk (parabolicDefiningHopfIdeal l).toIdeal) =
      filtrationIdeal l n := by
  set f := Ideal.Quotient.mk (parabolicDefiningHopfIdeal l).toIdeal
  have hgen : ∀ h : H, f ((conjugationAlgHom l h).coeff 0 -
      algebraMap k H (Coalgebra.counit (R := k) h)) =
      (conjugationAlgHom (parCochar l) (f h)).coeff 0 -
        algebraMap k _ (Coalgebra.counit (R := k) (f h)) := by
    intro h
    have e1 := coeff_conj_parMk l h 0
    have e2 : Coalgebra.counit (R := k) (parMk l h) = Coalgebra.counit (R := k) h :=
      CoalgHomClass.counit_comp_apply (parMk l) h
    change parMk l _ = (conjugationAlgHom (parCochar l) (parMk l h)).coeff 0 -
      algebraMap k _ (Coalgebra.counit (R := k) (parMk l h))
    rw [e1, e2, map_sub]
    congr 1
  have hunip : Ideal.map f (BialgHom.unipotentDefiningHopfIdeal l).toIdeal =
      (BialgHom.unipotentDefiningHopfIdeal (parCochar l)).toIdeal := by
    rw [BialgHom.unipotentDefiningHopfIdeal_toIdeal l,
      BialgHom.unipotentDefiningHopfIdeal_toIdeal (parCochar l), Ideal.map_sup, Ideal.map_span,
      Ideal.map_quotient_self, parabolic_parCochar_eq_bot, HopfIdeal.bot_toIdeal, bot_sup_eq,
      bot_sup_eq]
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
        (lineGrading (parCochar l) (m : ℤ) : Set _)) := by
    rw [Ideal.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨m, hm, hx⟩ := Set.mem_iUnion₂.1 hx
      exact Set.mem_iUnion₂.2 ⟨m, hm, parMk_mem_lineGrading l hx⟩
    · intro hy
      obtain ⟨m, hm, hy⟩ := Set.mem_iUnion₂.1 hy
      obtain ⟨x, hx, rfl⟩ := exists_lift_lineGrading l hy
      exact ⟨x, Set.mem_iUnion₂.2 ⟨m, hm, hx⟩, rfl⟩
  have hmap : Ideal.map f (filtrationIdeal l n) = filtrationIdeal (parCochar l) n := by
    simp only [filtrationIdeal]
    rw [Ideal.map_sup, hunip, hspan]
  rw [← hmap, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
  refine sup_eq_left.2 ?_
  rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  exact le_trans (HopfIdeal.toIdeal_le_toIdeal.2
    (BialgHom.parabolicDefiningHopfIdeal_le_unipotentDefiningHopfIdeal l)) le_sup_left

/-- `P(λ)` is smooth. -/
theorem smooth_parQuot : Algebra.Smooth k (H ⧸ (parabolicDefiningHopfIdeal l).toIdeal) :=
  let Hc : FiniteTypeCommHopfAlgCat.{u, u} k := FiniteTypeCommHopfAlgCat.of (R := k) H
  haveI : Algebra.Smooth k Hc := ‹Algebra.Smooth k H›
  BialgHom.smoothCommHopfAlgProperty_quotient_parabolicDefiningHopfIdeal (H := Hc) l

/-- **(P1-grp)** for general `G`: `U_{≥n}(A)` is a subgroup. From (a-i), (a-ii) and the Hopf
ideal `filtrationHopfIdeal` of `P(λ)`, pulled back along `H → H ⧸ I_P`. -/
theorem filtrationPoints_mul_inv (n : ℕ) {A : Type u} [CommRing A] [Algebra k A]
    {g h : WithConv (H →ₐ[k] A)} (hg : filtrationIdeal l n ≤ RingHom.ker g.ofConv)
    (hh : filtrationIdeal l n ≤ RingHom.ker h.ofConv) :
    filtrationIdeal l n ≤ RingHom.ker (g⁻¹ * h).ofConv := by
  classical
  haveI := smooth_parQuot l
  let Jb := filtrationHopfIdeal (parCochar l) (parabolic_parCochar_eq_bot l) n
  let J : HopfIdeal k H := Jb.comap (parMk l)
  have hJ : J.toIdeal = filtrationIdeal l n := by
    rw [HopfIdeal.comap_toIdeal]
    exact filtrationIdeal_comap_parabolicQuotient l n
  let S := TauCeti.CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) J
    (CommAlgCat.of k A)
  have mem : ∀ x : WithConv (H →ₐ[k] A), filtrationIdeal l n ≤ RingHom.ker x.ofConv → x ∈ S :=
    fun x hx => (TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff
      (_root_.CommHopfAlgCat.of k H) J (CommAlgCat.of k A) x).2 fun y hy =>
      hx (by rw [← hJ]; exact HopfIdeal.mem_toIdeal.2 hy)
  have hm := S.mul_mem (S.inv_mem (mem g hg)) (mem h hh)
  intro y hy
  exact (TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff
    (_root_.CommHopfAlgCat.of k H) J (CommAlgCat.of k A) _).1 hm y
    (HopfIdeal.mem_toIdeal.1 (by rw [hJ]; exact hy))

/-- Points of `G` killing `I_P` as points of `P(λ)`. -/
noncomputable def parLift {A : Type u} [CommRing A] [Algebra k A] (u : WithConv (H →ₐ[k] A))
    (hu : (parabolicDefiningHopfIdeal l).toIdeal ≤ RingHom.ker u.ofConv) :
    WithConv ((H ⧸ (parabolicDefiningHopfIdeal l).toIdeal) →ₐ[k] A) :=
  toConv (Ideal.Quotient.liftₐ _ u.ofConv fun a ha => hu ha)

lemma mapDomain_parLift {A : Type u} [CommRing A] [Algebra k A] (u : WithConv (H →ₐ[k] A))
    (hu : (parabolicDefiningHopfIdeal l).toIdeal ≤ RingHom.ker u.ofConv) :
    BialgHom.mapDomain (parMk l) (parLift l u hu) = u := by
  apply WithConv.ofConv_injective
  rw [BialgHom.mapDomain_apply, WithConv.ofConv_toConv]
  ext x
  rfl

lemma parabolic_le_filtrationIdeal (n : ℕ) :
    (parabolicDefiningHopfIdeal l).toIdeal ≤ filtrationIdeal l n :=
  le_trans (HopfIdeal.toIdeal_le_toIdeal.2
    (BialgHom.parabolicDefiningHopfIdeal_le_unipotentDefiningHopfIdeal l)) le_sup_left

/-- **(P1-vec, additivity) for general `G`**: on `U_{≥n}`, `n ≥ 1`, multiplication is additive on
`λ`-degree-`n` coordinates. Via `P(λ)` and TorusConjDyn `unipotentFiltrationPoints_map_mul`. -/
theorem filtrationPoints_map_mul {n : ℕ} (hn : 0 < n) {A : Type u} [CommRing A] [Algebra k A]
    {u u' : WithConv (H →ₐ[k] A)} (hu : filtrationIdeal l n ≤ RingHom.ker u.ofConv)
    (hu' : filtrationIdeal l n ≤ RingHom.ker u'.ofConv) {w : H} (hw : w ∈ lineGrading l (n : ℤ)) :
    (u * u').ofConv w = u.ofConv w + u'.ofConv w := by
  classical
  haveI := smooth_parQuot l
  have hP := parabolic_le_filtrationIdeal l n
  set ub := parLift l u (le_trans hP hu)
  set ub' := parLift l u' (le_trans hP hu')
  have hb : ∀ (v : WithConv (H →ₐ[k] A)) (hv : filtrationIdeal l n ≤ RingHom.ker v.ofConv),
      filtrationIdeal (parCochar l) n ≤ RingHom.ker (parLift l v (le_trans hP hv)).ofConv := by
    intro v hv y hy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hx : x ∈ filtrationIdeal l n := by
      rw [← filtrationIdeal_comap_parabolicQuotient l n]
      exact hy
    exact hv hx
  have key := unipotentFiltrationPoints_map_mul (parCochar l) (parabolic_parCochar_eq_bot l) hn
    (hb u hu) (hb u' hu') (parMk_mem_lineGrading l hw)
  have hmul : u * u' = BialgHom.mapDomain (parMk l) (ub * ub') := by
    rw [map_mul, mapDomain_parLift, mapDomain_parLift]
  rw [hmul, BialgHom.mapDomain_apply, WithConv.ofConv_toConv]
  exact key

end AlgMag.Reductive
