/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# `R[G]` is reduced (affine stratum lemma, step 1)

For `R` reduced and `G` a finitely generated abelian group whose torsion is killed by a unit of `R`,
the ring `R[G]` is reduced: `D(G)` is smooth over `R`.
-/

universe u v

namespace AlgMag.ChartStratum

/-- Reducedness of `R[G]` can be checked at the residue fields of `R`. -/
theorem isReduced_of_residue {R : Type u} [CommRing R] [IsReduced R] {G : Type v} [AddCommGroup G]
    (h : ∀ (p : Ideal R) [p.IsPrime], IsReduced (AddMonoidAlgebra p.ResidueField G)) :
    IsReduced (AddMonoidAlgebra R G) := by
  refine ⟨fun f hf => ?_⟩
  ext m
  have hmem : ∀ (p : Ideal R) [p.IsPrime], f.coeff m ∈ p := by
    intro p _
    have hnil : IsNilpotent (AddMonoidAlgebra.mapRingHom G (algebraMap R p.ResidueField) f) :=
      hf.map _
    have h0 := (h p).eq_zero _ hnil
    have h1 := congrArg (fun g => (AddMonoidAlgebra.coeff g) m) h0
    simp only [AddMonoidAlgebra.coeff_mapRingHom] at h1
    exact (Ideal.algebraMap_residueField_eq_zero).1 (by simpa using h1)
  have hn : f.coeff m ∈ nilradical R := by
    rw [nilradical_eq_sInf, Ideal.mem_sInf]
    intro p hp
    haveI : p.IsPrime := hp
    exact hmem p
  rw [nilradical_eq_zero] at hn
  simpa using hn

/-- A commutative semisimple ring is reduced. -/
lemma isReduced_of_semisimple (R : Type u) [CommRing R] [IsSemisimpleRing R] : IsReduced R := by
  rw [← nilradical_eq_bot_iff]
  exact le_bot_iff.1 ((nilradical_le_jacobson R).trans (IsSemisimpleRing.jacobson_eq_bot R).le)

/-- `K[T]` is reduced for a finite group of invertible order. -/
theorem isReduced_finite {K : Type u} [Field K] {T : Type v} [AddCommGroup T] [Finite T]
    (N : ℕ) (hN : (N : K) ≠ 0) (ht : ∀ x : T, N • x = 0) :
    IsReduced (AddMonoidAlgebra K T) := by
  haveI : NeZero (Nat.card T : K) := by
    refine ⟨fun h0 => ?_⟩
    obtain ⟨q, hq⟩ := CharP.exists K
    have hq0 : q ≠ 0 := by
      rintro rfl
      haveI := hq
      haveI : CharZero K := CharP.charP_to_charZero K
      have : Nat.card T = 0 := by exact_mod_cast h0
      exact Nat.card_pos.ne' this
    have hdvd : q ∣ Nat.card T := (CharP.cast_eq_zero_iff K q _).1 h0
    have hqp : q.Prime := (CharP.char_is_prime_or_zero K q).resolve_right hq0
    haveI : Fact q.Prime := ⟨hqp⟩
    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' q hdvd
    have : q ∣ N := by rw [← hx]; exact addOrderOf_dvd_of_nsmul_eq_zero (ht x)
    exact hN ((CharP.cast_eq_zero_iff K q _).2 this)
  exact isReduced_of_semisimple _

/-- **`R[G]` is reduced**. -/
theorem isReduced_addMonoidAlgebra {R : Type u} [CommRing R] [IsReduced R] {G : Type v}
    [AddCommGroup G] [AddGroup.FG G] (N : ℕ) (hN : IsUnit (N : R))
    (ht : ∀ x : G, IsOfFinAddOrder x → N • x = 0) : IsReduced (AddMonoidAlgebra R G) := by
  refine isReduced_of_residue fun p _ => ?_
  obtain ⟨n, ι, _, q, hq, e, ⟨φ⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod G
  let K := p.ResidueField
  let T := DirectSum ι fun i => ZMod (q i ^ e i)
  let F := Fin n →₀ ℤ
  haveI : ∀ i, NeZero (q i ^ e i) := fun i => ⟨pow_ne_zero _ (hq i).ne_zero⟩
  haveI hTf : Finite T :=
    Finite.of_injective (fun f : T => (fun i => f i : ∀ i, ZMod (q i ^ e i))) DFunLike.coe_injective
  have hNK : (N : K) ≠ 0 := by
    have := hN.map (algebraMap R K)
    rw [map_natCast] at this
    exact this.ne_zero
  have htT : ∀ x : T, N • x = 0 := by
    intro x
    let g : T →+ G := φ.symm.toAddMonoidHom.comp (AddMonoidHom.inr F T)
    have h1 := ht (g x) (g.isOfFinAddOrder (isOfFinAddOrder_of_finite x))
    have h2 : g (N • x) = 0 := by rw [map_nsmul]; exact h1
    have hg : Function.Injective g := fun a b hab => by
      have := φ.symm.injective hab
      exact (Prod.mk.inj this).2
    exact hg (h2.trans (map_zero g).symm)
  haveI : IsReduced (AddMonoidAlgebra K T) := isReduced_finite N hNK htT
  have h3 : IsReduced (AddMonoidAlgebra (AddMonoidAlgebra K T) F) := by
    refine isReduced_of_residue fun P _ => ?_
    exact inferInstance
  let e1 : AddMonoidAlgebra K G ≃+* AddMonoidAlgebra K (F × T) :=
    (AddMonoidAlgebra.domCongr K K φ).toRingEquiv
  let e2 : AddMonoidAlgebra K (F × T) ≃+* AddMonoidAlgebra (AddMonoidAlgebra K T) F :=
    AddMonoidAlgebra.curryRingEquiv
  exact isReduced_of_injective (e1.trans e2).toRingHom (e1.trans e2).injective

end AlgMag.ChartStratum
