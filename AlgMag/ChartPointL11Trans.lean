/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartPointL11Local
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# "`G` is transitive on `O`", in the form used by Lemma 1.1 (chart-lemma proof, step C)

For `φ : k[N] → R`, the map `evAt φ : k[N] → R[M]`, `z ↦ φ(z) z` is the action of the universal point
on `R`-points of `O`. If `h ∈ k[N]` is not nilpotent, every prime of `R` is the contraction of a
prime of `R[M]` not containing `evAt φ h`: homogeneous elements of `k[N]` are units or zero.
-/

universe u

namespace AlgMag.ChartPoint

open ChartMain

variable {k R : Type u} [CommRing k] [CommRing R] {M : Type u} [AddCommGroup M]
  {N : AddSubgroup M}

/-- `z ↦ φ(z) z`. -/
noncomputable def chiAt (φ : AddMonoidAlgebra k N →+* R) :
    Multiplicative N →* AddMonoidAlgebra R M where
  toFun z := AddMonoidAlgebra.single ((Multiplicative.toAdd z : N) : M)
    (φ (AddMonoidAlgebra.single (Multiplicative.toAdd z) 1))
  map_one' := by
    change AddMonoidAlgebra.single ((0 : N) : M) (φ (AddMonoidAlgebra.single 0 1)) = 1
    have : (AddMonoidAlgebra.single (0 : N) (1 : k)) = 1 := rfl
    rw [this, map_one]
    rfl
  map_mul' a b := by
    rw [AddMonoidAlgebra.single_mul_single, ← map_mul, AddMonoidAlgebra.single_mul_single, mul_one]
    rfl

/-- The action of the universal point on functions of `O`. -/
noncomputable def evAt (φ : AddMonoidAlgebra k N →+* R) :
    AddMonoidAlgebra k N →+* AddMonoidAlgebra R M :=
  evalAt ((AddMonoidAlgebra.singleZeroRingHom : R →+* AddMonoidAlgebra R M).comp
    (φ.comp AddMonoidAlgebra.singleZeroRingHom)) (chiAt φ)

lemma evAt_single (φ : AddMonoidAlgebra k N →+* R) (y : N) (b : k) :
    evAt (M := M) φ (AddMonoidAlgebra.single y b) = AddMonoidAlgebra.single (y : M)
      (φ (AddMonoidAlgebra.singleZeroRingHom b) * φ (AddMonoidAlgebra.single y 1)) := by
  rw [evAt, evalAt_single]
  change AddMonoidAlgebra.single 0 _ * AddMonoidAlgebra.single (y : M) _ = _
  rw [AddMonoidAlgebra.single_mul_single, zero_add]
  rfl

lemma coeff_map_evAt {K : Type u} [CommRing K] (res : R →+* K) (φ : AddMonoidAlgebra k N →+* R)
    (w : AddMonoidAlgebra k N) (z : N) :
    (AddMonoidAlgebra.mapRingHom M res (evAt (M := M) φ w)).coeff (z : M) =
      res (φ (AddMonoidAlgebra.singleZeroRingHom (w.coeff z)) *
        φ (AddMonoidAlgebra.single z 1)) := by
  classical
  induction w using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq =>
    have e1 : (AddMonoidAlgebra.mapRingHom M res (evAt (M := M) φ (p + q))).coeff (z : M) =
        (AddMonoidAlgebra.mapRingHom M res (evAt (M := M) φ p)).coeff (z : M) +
        (AddMonoidAlgebra.mapRingHom M res (evAt (M := M) φ q)).coeff (z : M) := by
      rw [map_add, map_add]; rfl
    have e2 : (p + q).coeff z = p.coeff z + q.coeff z := rfl
    rw [e1, e2, hp, hq, map_add, map_add, add_mul, map_add]
  | single y b =>
    rw [evAt_single, AddMonoidAlgebra.mapRingHom_single]
    by_cases h : y = z
    · subst h; simp
    · have h' : (y : M) ≠ z := fun e => h (Subtype.ext e)
      simp [h, h', AddMonoidAlgebra.coeff_single]

/-- **§1, "`G` is transitive on `O`".** -/
theorem exists_prime_evAt (hk : IsField k) (φ : AddMonoidAlgebra k N →+* R)
    (h : AddMonoidAlgebra k N) (hn : ¬ IsNilpotent h) (v : Ideal R) [hv : v.IsPrime] :
    ∃ Q : Ideal (AddMonoidAlgebra R M), Q.IsPrime ∧
      Q.comap (AddMonoidAlgebra.singleZeroRingHom : R →+* AddMonoidAlgebra R M) = v ∧
      evAt φ h ∉ Q := by
  classical
  letI : Field k := hk.toField
  let K := v.ResidueField
  let res : R →+* K := algebraMap R K
  let τ : AddMonoidAlgebra R M →+* AddMonoidAlgebra K M := AddMonoidAlgebra.mapRingHom M res
  have hnn : ¬ IsNilpotent (τ (evAt φ h)) := by
    rintro ⟨e, he⟩
    apply hn
    refine ⟨e, ?_⟩
    ext z
    by_contra hne
    have hne' : (h ^ e).coeff z ≠ 0 := hne
    rw [← map_pow, ← map_pow] at he
    have hc := coeff_map_evAt (M := M) res φ (h ^ e) z
    change (τ (evAt φ (h ^ e))).coeff (z : M) = _ at hc
    rw [he] at hc
    have hu1 : IsUnit (AddMonoidAlgebra.singleZeroRingHom ((h ^ e).coeff z) :
        AddMonoidAlgebra k N) :=
      (IsUnit.mk0 _ hne').map _
    have hu2 : IsUnit (AddMonoidAlgebra.single z (1 : k)) :=
      IsUnit.of_mul_eq_one (AddMonoidAlgebra.single (-z) 1) (by
        rw [AddMonoidAlgebra.single_mul_single, add_neg_cancel, mul_one]; rfl)
    have hu := ((hu1.map φ).mul (hu2.map φ)).map res
    exact hu.ne_zero hc.symm
  have : ∃ P : Ideal (AddMonoidAlgebra K M), P.IsPrime ∧ τ (evAt φ h) ∉ P := by
    by_contra hcon
    push_neg at hcon
    apply hnn
    rw [← mem_nilradical, nilradical_eq_sInf, Submodule.mem_sInf]
    exact fun (P : Ideal _) hP => hcon P hP
  obtain ⟨P, hP, hc⟩ := this
  refine ⟨P.comap τ, Ideal.comap_isPrime _ _, ?_, hc⟩
  ext r
  rw [Ideal.mem_comap, Ideal.mem_comap]
  have e : τ (AddMonoidAlgebra.singleZeroRingHom r) =
      AddMonoidAlgebra.singleZeroRingHom (res r) := AddMonoidAlgebra.mapRingHom_single ..
  rw [e]
  constructor
  · intro hr
    by_contra hrv
    have hne : res r ≠ 0 := fun h0 => hrv (Ideal.algebraMap_residueField_eq_zero.1 h0)
    exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hr ((IsUnit.mk0 _ hne).map _))
  · intro hr
    have : res r = 0 := Ideal.algebraMap_residueField_eq_zero.2 hr
    rw [this, map_zero]
    exact P.zero_mem

end AlgMag.ChartPoint
