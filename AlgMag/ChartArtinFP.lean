/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartArtin
import AlgMag.ChartConclude
import AlgMag.ChartS5Trunc

/-!
# Artin approximation in the form used in §5 of the chart-lemma proof

`artinApproxFP`: `AlgMag.ChartConclude.ArtinApproxFP`, from
`AlgMag.ChartArtin.artinApprox_of_finiteType_int` for the functor `Hom_A(B₀, -)`.
-/

open CategoryTheory IsLocalRing StacksDraft.ArtinApproximation

universe u

namespace AlgMag.ChartArtin

section

variable {A : Type u} [CommRing A] (B₀ : Type u) [CommRing B₀] [Algebra A B₀]

/-- `Hom_A(B₀, -)`. -/
def homF : Under (CommRingCat.of A) ⥤ Type u where
  obj R := {f : B₀ →+* R.right // f.comp (algebraMap A B₀) = R.hom.hom}
  map {R R'} t := TypeCat.ofHom fun f => ⟨t.right.hom.comp f.1, by
    rw [RingHom.comp_assoc, f.2, ← CommRingCat.hom_comp, Under.w t]⟩

lemma homF_map_val {R R' : Under (CommRingCat.of A)} (t : R ⟶ R') (f : (homF (A := A) B₀).obj R) :
    ((homF B₀).map t f).1 = t.right.hom.comp f.1 := rfl

lemma homF_isLimitPreserving [Algebra.FinitePresentation A B₀] :
    IsLimitPreserving.{u, u} (homF (A := A) B₀) := fun B _ g ξ =>
  ⟨B₀, inferInstance, inferInstance, inferInstance, ξ.1, ξ.2, ⟨RingHom.id _, RingHom.id_comp _⟩,
    Subtype.ext (RingHom.ext fun _ => rfl)⟩

end

variable {A : Type u} [CommRing A]

/-- `Â → (A_𝔭)^∧`. -/
noncomputable def toLocCompletion (p : Ideal A) [p.IsPrime] :
    AdicCompletion p A →+* Completion p :=
  Stacks.Nagata.PthRootDescent.mapAdicCompletion p (maximalIdeal (Localization.AtPrime p))
    (by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      )

lemma toLocCompletion_of (p : Ideal A) [p.IsPrime] (x : A) :
    toLocCompletion p (algebraMap A (AdicCompletion p A) x) = toCompletion p x :=
  Stacks.Nagata.PthRootDescent.mapAdicCompletion_of _ x

/-- The comparison on truncations of the local rings. -/
lemma eval_comparison {A' : Type u} [CommRing A'] (p : Ideal A) [p.IsPrime] (q : Ideal A') [q.IsPrime]
    (g : A →+* A') (hq : p = q.comap g) (n : ℕ) (a : A) (x : AdicCompletion p A)
    (hx : AdicCompletion.evalₐ p n x = Ideal.Quotient.mk _ a) :
    AdicCompletion.evalₐ (maximalIdeal (Localization.AtPrime q)) n
        (completionComparison p q g hq (toLocCompletion p x)) =
      Ideal.Quotient.mk _ (algebraMap A' (Localization.AtPrime q) (g a)) := by
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    (Localization.localRingHom p q g hq).toAlgebra
  have h1 := Stacks.Nagata.PthRootDescent.evalₐ_mapAdicCompletion
    (I := maximalIdeal (Localization.AtPrime p)) (J := maximalIdeal (Localization.AtPrime q))
    (by
      let := Localization.isLocalHom_localRingHom p q g hq
      exact IsLocalRing.map_maximalIdeal_le (Localization.localRingHom p q g hq)) n
    (toLocCompletion p x)
  have h2 := Stacks.Nagata.PthRootDescent.evalₐ_mapAdicCompletion
    (I := p) (J := maximalIdeal (Localization.AtPrime p))
    (by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      ) n x
  refine h1.trans ?_
  rw [show AdicCompletion.evalₐ (maximalIdeal (Localization.AtPrime p)) n (toLocCompletion p x) = _ from h2,
    hx, Ideal.quotientMap_mk, Ideal.quotientMap_mk]
  congr 1
  exact Localization.localRingHom_to_map p q g hq a

/-- In a truncation at a maximal ideal the localization changes nothing. -/
lemma mem_pow_of_map_mem {R : Type u} [CommRing R] (q : Ideal R) [hq : q.IsMaximal] (n : ℕ) (x : R)
    (h : algebraMap R (Localization.AtPrime q) x ∈ maximalIdeal (Localization.AtPrime q) ^ n) :
    x ∈ q ^ n := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow,
    IsLocalization.mem_map_algebraMap_iff q.primeCompl] at h
  obtain ⟨⟨a, s⟩, hs⟩ := h
  have hs' := (IsLocalization.eq_iff_exists q.primeCompl _).1 (by simpa [map_mul] using hs :
    algebraMap R (Localization.AtPrime q) (x * s) = algebraMap R _ (a : R))
  obtain ⟨c, hc⟩ := hs'
  have hmem : ((c : R) * s) * x ∈ q ^ n := by
    have : (c : R) * (x * s) = c * a := hc
    rw [show ((c : R) * s) * x = (c : R) * (x * s) by ring, this]
    exact Ideal.mul_mem_left _ _ a.2
  have hcs : ((c : R) * s) ∉ q := fun hm =>
    (hq.isPrime.mem_or_mem hm).elim c.2 s.2
  obtain ⟨y, i, hi, hy⟩ := hq.exists_inv hcs
  obtain ⟨w, hw⟩ := sub_dvd_pow_sub_pow (1 : R) i n
  have e1 : 1 - i = y * ((c : R) * s) := by rw [← hy]; ring
  have e2 : x = x * i ^ n + (y * w) * (((c : R) * s) * x) := by
    have : 1 - i ^ n = y * ((c : R) * s) * w := by rw [one_pow] at hw; rw [hw, e1]
    linear_combination x * this
  rw [e2]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hi n)) (Ideal.mul_mem_left _ _ hmem)

lemma isMaximal_of_residue {A' : Type u} [CommRing A'] (p : Ideal A) [hp : p.IsMaximal] (q : Ideal A')
    [q.IsPrime] (g : A →+* A') (hq : p = q.comap g)
    (hres : Function.Bijective (Ideal.ResidueField.map p q g hq)) :
    q.IsMaximal ∧ Function.Surjective ((Ideal.Quotient.mk q).comp g) := by
  have hs : Function.Surjective ((Ideal.Quotient.mk q).comp g) := by
    intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨w, hw⟩ := hres.2 (algebraMap A' q.ResidueField z)
    obtain ⟨a, rfl⟩ := (Ideal.bijective_algebraMap_quotient_residueField p).2 w
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    refine ⟨a, ?_⟩
    have e : algebraMap A' q.ResidueField (g a) = algebraMap A' q.ResidueField z :=
      (Ideal.ResidueField.map_algebraMap p q g hq a).symm.trans hw
    rw [RingHom.comp_apply, Ideal.Quotient.eq, ← Ideal.algebraMap_residueField_eq_zero, map_sub, e,
      sub_self]
  refine ⟨?_, hs⟩
  have hk : RingHom.ker ((Ideal.Quotient.mk q).comp g) = p := by
    ext a
    rw [hq, RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_comap]
  let e := (Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective hs)
  haveI : IsField (A ⧸ p) := Ideal.Quotient.maximal_ideal_iff_isField_quotient p |>.1 hp
  exact Ideal.Quotient.maximal_of_isField q (e.symm.toMulEquiv.isField ‹_›)

/-- **Artin 1969, Cor 2.2**, in the form of §5. -/
theorem artinApproxFP : ChartConclude.ArtinApproxFP.{u} := by
  intro A _ _ 𝔭 _ B₀ _ _ _ h N
  haveI : 𝔭.IsPrime := Ideal.IsMaximal.isPrime ‹_›
  let ξ : (homF (A := A) B₀).obj (algObj (toCompletion 𝔭)) :=
    ⟨(toLocCompletion 𝔭).comp h.toRingHom, RingHom.ext fun a => by
      change toLocCompletion 𝔭 (h (algebraMap A B₀ a)) = toCompletion 𝔭 a
      rw [h.commutes, toLocCompletion_of]⟩
  obtain ⟨A', _, _, _, q, _, hq, hres, ξ', e, hξ⟩ :=
    artinApprox_of_finiteType_int 𝔭 (homF (A := A) B₀) (homF_isLimitPreserving B₀) ξ N
  obtain ⟨hqm, hs⟩ := isMaximal_of_residue 𝔭 q (algebraMap A A') hq hres
  haveI := hqm
  obtain ⟨hc, hsj⟩ := ChartS5.quot_pow_bijective_of_etale 𝔭 q hq.symm hs N
  let f := (Ideal.Quotient.mk (q ^ N)).comp (algebraMap A A')
  have hk : RingHom.ker f = 𝔭 ^ N := by
    rw [← hc]
    ext a
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_comap]
  let E : (A ⧸ 𝔭 ^ N) ≃+* A' ⧸ q ^ N :=
    (Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective hsj)
  have hE : ∀ a, E (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (algebraMap A A' a) := fun _ => rfl
  let σr : A' →+* A ⧸ 𝔭 ^ N := (E.symm : _ →+* _).comp (Ideal.Quotient.mk (q ^ N))
  have hσ : ∀ a, σr (algebraMap A A' a) = Ideal.Quotient.mk _ a := fun a => by
    change E.symm _ = _
    rw [← hE, E.symm_apply_apply]
  let σ : A' →ₐ[A] A ⧸ 𝔭 ^ N := { σr with commutes' := hσ }
  let θ : B₀ →ₐ[A] A' := { ξ'.1 with commutes' := fun a => RingHom.congr_fun ξ'.2 a }
  refine ⟨A', inferInstance, inferInstance, inferInstance, σ, θ, fun b => ?_⟩
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ 𝔭 N (h b))
  rw [← hy]
  -- the identity in `(A'_q)^∧ / 𝔪^N`
  have hb : completionTruncation 𝔭 q (algebraMap A A') hq N (toLocCompletion 𝔭 (h b)) =
      truncation q N (ξ'.1 b) := RingHom.congr_fun (congrArg Subtype.val hξ) b
  -- apply evaluation
  let Φ : Completion q ⧸ completionIdeal q N →+* Localization.AtPrime q ⧸ maximalIdeal (Localization.AtPrime q) ^ N :=
    Ideal.Quotient.lift _ (AdicCompletion.evalₐ (maximalIdeal (Localization.AtPrime q)) N).toRingHom (by
      intro z hz
      have hle : completionIdeal q N ≤ RingHom.ker
          (AdicCompletion.evalₐ (maximalIdeal (Localization.AtPrime q)) N).toRingHom := by
        refine Ideal.map_le_iff_le_comap.2 fun w hw => ?_
        rw [Ideal.mem_comap, RingHom.mem_ker]
        change AdicCompletion.evalₐ _ N (AdicCompletion.of _ _ w) = 0
        rw [AdicCompletion.evalₐ_of]
        exact Ideal.Quotient.eq_zero_iff_mem.2 hw
      exact hle hz)
  have h1 := congrArg Φ hb
  have h2 : Φ (completionTruncation 𝔭 q (algebraMap A A') hq N (toLocCompletion 𝔭 (h b))) =
      Ideal.Quotient.mk _ (algebraMap A' (Localization.AtPrime q) (algebraMap A A' y)) :=
    eval_comparison 𝔭 q _ hq N y (h b) hy.symm
  have h3 : Φ (truncation q N (ξ'.1 b)) =
      Ideal.Quotient.mk _ (algebraMap A' (Localization.AtPrime q) (ξ'.1 b)) := by
    change AdicCompletion.evalₐ _ N (AdicCompletion.of _ _ _) = _
    rw [AdicCompletion.evalₐ_of]
    rfl
  rw [h2, h3, Ideal.Quotient.eq, ← map_sub] at h1
  have h4 := mem_pow_of_map_mem q N _ h1
  change E.symm (Ideal.Quotient.mk _ (ξ'.1 b)) = _
  rw [E.symm_apply_eq, hE]
  exact (Ideal.Quotient.eq.2 h4).symm

end AlgMag.ChartArtin

#print axioms AlgMag.ChartArtin.artinApproxFP
