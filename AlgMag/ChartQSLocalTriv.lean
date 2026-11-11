/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartQSEffective
import AlgMag.ChartQSAlg

/-!
# Noetherian algebraization as Theorem 4.1 for the trivial group

`M = PUnit`: the only character is `1`, every element is homogeneous of degree `0`, a complete pair is an
adically complete noetherian ring, and `ChartMain.Effective` is `NoetherianAlgebraization`. This lets the
non-graded forms of Lemmas 3.4, 4.3, 4.4 be read off the graded ones.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Space

universe u

namespace AlgMag.ChartMain.DeligneQS.ChartQSLocal

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- The trivial group's character group. -/
abbrev Mt : Type u := PUnit.{u + 1}

instance : AddMonoid.FG Mt.{u} := AddMonoid.fg_of_finite

lemma char_eq_one {R : Type*} [CommRing R] (h : Multiplicative Mt.{u} →* R) : h = 1 := by
  ext x
  exact h.map_one

variable {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]

lemma coact_triv (actT : AAction (fppfO B S hS) Mt.{u} (yoneda.obj T)) (a : Γ((SCH).obj T, ⊤)) :
    coact actT a = AddMonoidAlgebra.single (0 : Mt.{u}) a := by
  have h := sum_coact actT a
  have hs : (coact actT a).coeff = Finsupp.single (0 : Mt.{u}) ((coact actT a).coeff 0) := by
    refine Finsupp.ext fun d => ?_
    have hd : d = 0 := Subsingleton.elim _ _
    subst hd
    simp
  rw [hs, Finsupp.sum_single_index rfl] at h
  have hc := coact_coeff actT a 0
  rw [h] at hc
  exact hc

lemma mem_homog (actT : AAction (fppfO B S hS) Mt.{u} (yoneda.obj T)) (a : Γ((SCH).obj T, ⊤)) (d : Mt.{u}) :
    a ∈ homog actT d := by
  have : d = 0 := Subsingleton.elim _ _
  subst this
  exact coact_triv actT a

lemma coeff_mem (actT : AAction (fppfO B S hS) Mt.{u} (yoneda.obj T)) {J : Ideal Γ((SCH).obj T, ⊤)}
    (a) (ha : a ∈ J) (d : Mt.{u}) : (coact actT a).coeff d ∈ J := by
  have hd : d = 0 := Subsingleton.elim _ _
  subst hd
  rw [coact_triv]
  simpa using ha

/-- A noetherian adically complete ring is a complete pair for the trivial group. -/
theorem isCompletePair_of_complete (actT : AAction (fppfO B S hS) Mt.{u} (yoneda.obj T))
    (I : Ideal Γ((SCH).obj T, ⊤)) [IsNoetherianRing Γ((SCH).obj T, ⊤)]
    [hc : IsAdicComplete I Γ((SCH).obj T, ⊤)] :
    letI := gradedRingOfAction actT; ChartGraded.IsCompletePair (homog actT) I := by
  letI := gradedRingOfAction actT
  refine ⟨inferInstance, fun i r hr => ?_, fun d y hy hsucc => ?_, fun d c _ h => ?_⟩
  · rw [DirectSum.decompose_of_mem_same (homog actT) (mem_homog actT r i)]
    exact hr
  · have hle : ∀ m n, m ≤ n → y n - y m ∈ I ^ m := by
      intro m n hmn
      induction n, hmn using Nat.le_induction with
      | base => simp
      | succ n hmn ih =>
        have := Ideal.add_mem _ ih (Ideal.pow_le_pow_right hmn (hsucc n))
        convert this using 1
        ring
    obtain ⟨c, hc'⟩ := hc.toIsPrecomplete.prec (f := y) (fun {m n} hmn => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      have := Ideal.neg_mem_iff _ |>.2 (hle m n hmn)
      simpa using this)
    refine ⟨c, mem_homog actT c d, fun n => ?_⟩
    have := hc' n
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
    have h' := Ideal.neg_mem_iff _ |>.2 this
    simpa using h'
  · refine hc.toIsHausdorff.haus c fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    exact h n

/-- A complete pair for the trivial group is noetherian adically complete. -/
theorem isAdicComplete_of_completePair (actT : AAction (fppfO B S hS) Mt.{u} (yoneda.obj T))
    (I : Ideal Γ((SCH).obj T, ⊤))
    (hP : letI := gradedRingOfAction actT; ChartGraded.IsCompletePair (homog actT) I) :
    IsAdicComplete I Γ((SCH).obj T, ⊤) := by
  letI := gradedRingOfAction actT
  refine { toIsHausdorff := ⟨fun c h => ?_⟩, toIsPrecomplete := ⟨fun {y} hy => ?_⟩ }
  · refine hP.sep 0 c (mem_homog actT c 0) fun n => ?_
    have := h n
    rwa [SModEq.zero, smul_eq_mul, Ideal.mul_top] at this
  · obtain ⟨c, _, hc⟩ := hP.exists_lim 0 y (fun n => mem_homog actT _ 0) (fun n => by
      have := hy (Nat.le_succ n)
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
      have h' := Ideal.neg_mem_iff _ |>.2 this
      simpa using h')
    refine ⟨c, fun n => ?_⟩
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    have h' := Ideal.neg_mem_iff _ |>.2 (hc n)
    simpa using h'

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

lemma smul_triv (actX : AAction (fppfO B S hS) Mt.{u} X) {W : BigFppfOver B S hS}
    (h : Multiplicative Mt.{u} →* Γ((SCH).obj W, ⊤)) (x : X.obj (op W)) :
    actX.smul (F := X) (U := op W) h x = x := by
  have : h = 1 := char_eq_one h
  subst this
  exact actX.one_smul (U := op W) x

lemma smulAt_triv (actT : AAction (fppfO B S hS) Mt.{u} (yoneda.obj T)) {W : BigFppfOver B S hS}
    (h : Multiplicative Mt.{u} →* Γ((SCH).obj W, ⊤)) (t : W ⟶ T) : smulAt actT h t = t := by
  have : h = 1 := char_eq_one h
  subst this
  exact smulAt_one actT t

/-- All points are equivariant for the trivial group. -/
lemma equivAlong_triv (actT : AAction (fppfO B S hS) Mt.{u} (yoneda.obj T))
    (actX : AAction (fppfO B S hS) Mt.{u} X) {E : BigFppfOver B S hS} (i : E ⟶ T) [Mono i]
    (x : X.obj (op E)) : EquivAlong actT actX i x := by
  intro W t t' h e
  rw [smulAt_triv] at e
  rw [smul_triv, (cancel_mono i).1 e]

lemma isEquivariant_triv {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (actY : AAction (fppfO B S hS) Mt.{u} Y)
    (actX : AAction (fppfO B S hS) Mt.{u} X) (f : Y ⟶ X) : IsEquivariant actY actX f := by
  intro W h x
  obtain ⟨W⟩ := W
  exact (congrArg (f.app (op W)) (smul_triv actY h x)).trans (smul_triv actX h _).symm

/-- **`Effective` from noetherian algebraization**, for the trivial group. -/
theorem effective_of_alg (actX : AAction (fppfO B S hS) Mt.{u} X) (h : NoetherianAlgebraization X) :
    Effective actX := by
  intro T _ actT m hP x hx
  letI := gradedRingOfAction actT
  haveI : IsNoetherianRing Γ((SCH).obj T, ⊤) := hP.noeth
  haveI := isAdicComplete_of_completePair actT m hP
  obtain ⟨φ, hφ, -⟩ := h T m x (fun n k e he => hx.compat n k e he)
  refine ⟨φ, hφ, fun t r => ?_⟩
  rw [smulAt_triv, smul_triv]

end AlgMag.ChartMain.DeligneQS.ChartQSLocal
