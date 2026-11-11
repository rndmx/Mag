/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec12PrintedRing
import AlgMag.GeneralBaseGrading

/-!
# Theorem 12.4: reduction to a graded algebra with sharp support

Mayeux, *Algebraic Magnetism*, proof of Theorem 12.4, the steps "Using Proposition 3.31 (to
`M → Z = M/N^×` and `Y = N/N^×`) we reduce to `N` sharp" and "`X⁰ = (X^N)⁰`, `A/I = A₀`, closed
immersion `X⁰ → X^N`". `A` is `Z`-graded, `I₁ = J_Y`, `I₀ = J_0`, and `B = A/I₁`, `B₀ = A/I₀`.
Since `Y` is sharp, `a ↦ a₀` gives a map `B₀ → B`, section of `B → B₀`.
-/

open Magnetism DirectSum

universe u

namespace AlgMag.Sec12Printed

section

variable {R A Z : Type u} [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup Z] [DecidableEq Z]
  (𝒢 : Z → Submodule R A) [GradedAlgebra 𝒢] (Y : AddSubmonoid Z)
  {I₁ I₀ : Ideal A} (hI₁ : I₁ = magnetIdeal 𝒢 Y) (hI₀ : I₀ = magnetIdeal 𝒢 (⊥ : AddSubmonoid Z))
  (hsharp : ∀ y ∈ Y, ∀ y' ∈ Y, y + y' = 0 → y = 0)

/-- The degree zero component. -/
noncomputable abbrev pr0 : A →+ A := GradedRing.proj 𝒢 0

include hI₁ in
lemma mem_I₁ {z : Z} (hz : z ∉ Y) {a : A} (ha : a ∈ 𝒢 z) :
    a ∈ I₁ := hI₁ ▸ mem_magnetIdeal_of_notMem hz ha

lemma pr0_of_mem {z : Z} {a : A} (ha : a ∈ 𝒢 z) : pr0 𝒢 a = if z = 0 then a else 0 := by
  rw [GradedRing.proj_apply]
  split_ifs with h
  · subst h
    rw [DirectSum.decompose_of_mem_same 𝒢 ha]
  · exact DirectSum.decompose_of_mem_ne 𝒢 ha h

include hI₁ hsharp in
lemma pr0_mul (a b : A) :
    Ideal.Quotient.mk I₁ (pr0 𝒢 (a * b)) =
      Ideal.Quotient.mk I₁ (pr0 𝒢 a) * Ideal.Quotient.mk I₁ (pr0 𝒢 b) := by
  induction a using DirectSum.Decomposition.inductionOn 𝒢 with
  | zero => simp
  | add a a' h h' => simp only [add_mul, map_add, h, h']
  | @homogeneous u a =>
    induction b using DirectSum.Decomposition.inductionOn 𝒢 with
    | zero => simp
    | add b b' h h' => simp only [mul_add, map_add, h, h']
    | @homogeneous v b =>
      have hab := SetLike.mul_mem_graded a.2 b.2
      rw [pr0_of_mem 𝒢 hab, pr0_of_mem 𝒢 a.2, pr0_of_mem 𝒢 b.2]
      by_cases huv : u + v = 0
      · rw [if_pos huv]
        by_cases hu : u = 0
        · subst hu
          have hv : v = 0 := by simpa using huv
          subst hv
          simp
        · rw [if_neg hu, map_zero, zero_mul, Ideal.Quotient.eq_zero_iff_mem]
          by_cases huY : u ∈ Y
          · have hvY : v ∉ Y := fun hvY => hu (hsharp u huY v hvY huv)
            exact Ideal.mul_mem_left _ _ (mem_I₁ 𝒢 Y hI₁ hvY b.2)
          · exact Ideal.mul_mem_right _ _ (mem_I₁ 𝒢 Y hI₁ huY a.2)
      · rw [if_neg huv, map_zero]
        by_cases hu : u = 0
        · subst hu
          have hv : v ≠ 0 := by simpa using huv
          rw [if_neg hv, map_zero, mul_zero]
        · rw [if_neg hu, map_zero, zero_mul]

/-- `a ↦ a₀ mod J_Y`, a morphism of algebras because `Y` is sharp. -/
noncomputable def rhoT : A →ₐ[R] A ⧸ I₁ :=
  { toFun := fun a => Ideal.Quotient.mk I₁ (pr0 𝒢 a)
    map_one' := by
      rw [pr0_of_mem 𝒢 (SetLike.GradedOne.one_mem : (1 : A) ∈ 𝒢 0), if_pos rfl, map_one]
    map_mul' := pr0_mul 𝒢 Y hI₁ hsharp
    map_zero' := by simp
    map_add' := fun a b => by simp
    commutes' := fun r => by
      rw [pr0_of_mem 𝒢 (SetLike.algebraMap_mem_graded 𝒢 r), if_pos rfl]
      rfl }

lemma rhoT_apply (a : A) : rhoT 𝒢 Y hI₁ hsharp a = Ideal.Quotient.mk I₁ (pr0 𝒢 a) := rfl

/-- The morphism `B₀ → B` of the printed proof (`X^N → X⁰`). -/
noncomputable def rho : (A ⧸ I₀) →ₐ[R] (A ⧸ I₁) :=
  Ideal.Quotient.liftₐ I₀ (rhoT 𝒢 Y hI₁ hsharp) (by
    intro a ha
    rw [hI₀, magnetIdeal] at ha
    have hle : Ideal.span (⋃ (m : Z) (_ : m ∉ (⊥ : AddSubmonoid Z)), (𝒢 m : Set A)) ≤
        RingHom.ker (rhoT 𝒢 Y hI₁ hsharp).toRingHom := by
      refine Ideal.span_le.2 ?_
      simp only [Set.iUnion_subset_iff]
      intro m hm x hx
      have hm0 : m ≠ 0 := fun e => hm (e ▸ AddSubmonoid.zero_mem _)
      change Ideal.Quotient.mk I₁ (pr0 𝒢 x) = 0
      rw [pr0_of_mem 𝒢 hx, if_neg hm0, map_zero]
    exact hle ha)

lemma rho_mk (a : A) : rho 𝒢 Y hI₁ hI₀ hsharp (Ideal.Quotient.mk I₀ a) =
    Ideal.Quotient.mk I₁ (pr0 𝒢 a) := rfl

include hI₁ hI₀ in
lemma I₁_le_I₀ : I₁ ≤ I₀ := by
  rw [hI₁, hI₀, magnetIdeal, Ideal.span_le]
  simp only [Set.iUnion_subset_iff]
  intro m hm x hx
  have hm0 : m ∉ (⊥ : AddSubmonoid Z) := fun e => hm (by
    have : m = 0 := e
    rw [this]
    exact Y.zero_mem)
  exact mem_magnetIdeal_of_notMem hm0 hx

/-- `B → B₀`. -/
noncomputable def piR : (A ⧸ I₁) →ₐ[R] (A ⧸ I₀) :=
  Ideal.Quotient.factorₐ R (I₁_le_I₀ 𝒢 Y hI₁ hI₀)

lemma piR_mk (a : A) : piR 𝒢 Y hI₁ hI₀ (Ideal.Quotient.mk I₁ a) = Ideal.Quotient.mk I₀ a := rfl

include hI₀ in
lemma mk0_pr0 (a : A) : Ideal.Quotient.mk I₀ (pr0 𝒢 a) = Ideal.Quotient.mk I₀ a := by
  induction a using DirectSum.Decomposition.inductionOn 𝒢 with
  | zero => simp
  | add a a' h h' => simp only [map_add, h, h']
  | @homogeneous u a =>
    rw [pr0_of_mem 𝒢 a.2]
    split_ifs with hu
    · rfl
    · rw [map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem, hI₀]
      exact mem_magnetIdeal_of_notMem (fun e => hu e) a.2

lemma piR_rho (x : A ⧸ I₀) : piR 𝒢 Y hI₁ hI₀ (rho 𝒢 Y hI₁ hI₀ hsharp x) = x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [rho_mk, piR_mk]
  exact mk0_pr0 𝒢 hI₀ a

/-- The grading of `B` as a family of `B₀`-submodules. -/
noncomputable def gradB (z : Z) :
    letI := (rho 𝒢 Y hI₁ hI₀ hsharp).toRingHom.toAlgebra
    Submodule (A ⧸ I₀) (A ⧸ I₁) :=
  letI := (rho 𝒢 Y hI₁ hI₀ hsharp).toRingHom.toAlgebra
  { carrier := quotGrading 𝒢 I₁ z
    add_mem' := fun ha hb => (quotGrading 𝒢 I₁ z).add_mem ha hb
    zero_mem' := (quotGrading 𝒢 I₁ z).zero_mem
    smul_mem' := by
      rintro c _ ⟨x, hx, rfl⟩
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
      rw [Algebra.smul_def]
      change rho 𝒢 Y hI₁ hI₀ hsharp (Ideal.Quotient.mk I₀ a) * _ ∈ quotGrading 𝒢 I₁ z
      rw [rho_mk]
      refine ⟨pr0 𝒢 a * x, ?_, rfl⟩
      have h0 : pr0 𝒢 a ∈ 𝒢 0 := by
        rw [GradedRing.proj_apply]
        exact SetLike.coe_mem _
      have := SetLike.mul_mem_graded h0 hx
      rwa [zero_add] at this }

lemma mem_gradB {z : Z} {x : A ⧸ I₁} : x ∈ gradB 𝒢 Y hI₁ hI₀ hsharp z ↔ x ∈ quotGrading 𝒢 I₁ z :=
  Iff.rfl

include hI₁ in
lemma homog_I₁ : IsHomogeneousIdeal 𝒢 I₁ := hI₁ ▸ isHomogeneous_magnetIdeal 𝒢 Y

/-- The grading of `B` over `B₀`. -/
noncomputable def gradedB :
    letI := (rho 𝒢 Y hI₁ hI₀ hsharp).toRingHom.toAlgebra
    GradedAlgebra (gradB 𝒢 Y hI₁ hI₀ hsharp) := by
  letI := (rho 𝒢 Y hI₁ hI₀ hsharp).toRingHom.toAlgebra
  letI G : GradedAlgebra (quotGrading 𝒢 I₁) := quotGradedAlgebra (homog_I₁ 𝒢 Y hI₁)
  let ι : ∀ z, quotGrading 𝒢 I₁ z →+ gradB 𝒢 Y hI₁ hI₀ hsharp z := fun z =>
    { toFun := fun x => ⟨x.1, x.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let dec : (A ⧸ I₁) →+ DirectSum Z fun z => gradB 𝒢 Y hI₁ hI₀ hsharp z :=
    (DirectSum.toAddMonoid fun z =>
      (DirectSum.of (fun z => gradB 𝒢 Y hI₁ hI₀ hsharp z) z).comp (ι z)).comp
      (DirectSum.decomposeAddEquiv (quotGrading 𝒢 I₁)).toAddMonoidHom
  have hdec : ∀ (z : Z) (x : A ⧸ I₁) (hx : x ∈ quotGrading 𝒢 I₁ z),
      dec x = DirectSum.of (fun z => gradB 𝒢 Y hI₁ hI₀ hsharp z) z ⟨x, hx⟩ := by
    intro z x hx
    change DirectSum.toAddMonoid _ (DirectSum.decompose (quotGrading 𝒢 I₁) x) = _
    rw [DirectSum.decompose_of_mem _ hx, DirectSum.toAddMonoid_of]
    rfl
  exact
    { one_mem := (G.one_mem : (1 : A ⧸ I₁) ∈ quotGrading 𝒢 I₁ 0)
      mul_mem := fun i j x y hx hy => (G.mul_mem hx hy : x * y ∈ quotGrading 𝒢 I₁ (i + j))
      toDecomposition := DirectSum.Decomposition.ofAddHom _ dec
        (by
          refine AddMonoidHom.ext fun x => ?_
          induction x using DirectSum.Decomposition.inductionOn (quotGrading 𝒢 I₁) with
          | zero => simp
          | @homogeneous z x =>
            change DirectSum.coeAddMonoidHom _ (dec x) = _
            rw [hdec z x x.2, DirectSum.coeAddMonoidHom_of]
            rfl
          | add a b ha hb =>
            simp only [map_add, AddMonoidHom.add_apply] at ha hb ⊢
            rw [ha, hb])
        (by
          refine DirectSum.addHom_ext fun z x => ?_
          change dec (DirectSum.coeAddMonoidHom _ (DirectSum.of _ z x)) = _
          rw [DirectSum.coeAddMonoidHom_of]
          exact hdec z x.1 x.2) }

/-- `B → B₀` is `B₀`-linear. -/
noncomputable def piB :
    letI := (rho 𝒢 Y hI₁ hI₀ hsharp).toRingHom.toAlgebra
    (A ⧸ I₁) →ₐ[A ⧸ I₀] (A ⧸ I₀) :=
  letI := (rho 𝒢 Y hI₁ hI₀ hsharp).toRingHom.toAlgebra
  { (piR 𝒢 Y hI₁ hI₀).toRingHom with
    commutes' := fun r => piR_rho 𝒢 Y hI₁ hI₀ hsharp r }

/-- **Theorem 12.4**, algebra: `A` is `Z`-graded, `Y` sharp, `w : Z → ℕ` is a morphism on the
support of the grading of `B = A / J_Y`, with `w⁻¹(0) = 0`. If `B₀ = A / J_0 → B` is formally smooth
and of finite type, then `P = ker(B → B₀)/ker²` is finite projective and `Sym_{B₀}(P) = B`. -/
theorem printed_graded (w : Z → ℕ)
    (hw : ∀ z, ∀ a ∈ 𝒢 z, Ideal.Quotient.mk I₁ a ≠ 0 → w z = 0 → z = 0)
    (hadd : ∀ u, ∀ a ∈ 𝒢 u, Ideal.Quotient.mk I₁ a ≠ 0 → ∀ v, ∀ b ∈ 𝒢 v,
      Ideal.Quotient.mk I₁ b ≠ 0 → w (u + v) = w u + w v) :
    letI := (rho 𝒢 Y hI₁ hI₀ hsharp).toRingHom.toAlgebra
    ∀ [Algebra.FormallySmooth (A ⧸ I₀) (A ⧸ I₁)] [Algebra.FiniteType (A ⧸ I₀) (A ⧸ I₁)],
    Module.Finite (A ⧸ I₀) (Conormal (piB 𝒢 Y hI₁ hI₀ hsharp)) ∧
      Module.Projective (A ⧸ I₀) (Conormal (piB 𝒢 Y hI₁ hI₀ hsharp)) ∧
      Nonempty (SymmetricAlgebra (A ⧸ I₀) (Conormal (piB 𝒢 Y hI₁ hI₀ hsharp)) ≃ₐ[A ⧸ I₀] (A ⧸ I₁)) := by
  letI := (rho 𝒢 Y hI₁ hI₀ hsharp).toRingHom.toAlgebra
  intro _ _
  letI := gradedB 𝒢 Y hI₁ hI₀ hsharp
  refine printed_ring (𝒜 := gradB 𝒢 Y hI₁ hI₀ hsharp) (w := w) ⟨?_, ?_, ?_, ?_⟩
  · rintro y _ ⟨a, ha, rfl⟩ hb e
    exact hw y a ha hb e
  · rintro u _ ⟨a, ha, rfl⟩ hb v _ ⟨d, hd, rfl⟩ hd'
    exact hadd u a ha hb v d hd hd'
  · rintro y hy _ ⟨a, ha, rfl⟩
    change Ideal.Quotient.mk I₀ a = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, hI₀]
    exact mem_magnetIdeal_of_notMem (fun e => hy e) ha
  · rintro _ ⟨a, ha, rfl⟩
    change rho 𝒢 Y hI₁ hI₀ hsharp (Ideal.Quotient.mk I₀ a) = Ideal.Quotient.mk I₁ a
    rw [rho_mk, pr0_of_mem 𝒢 ha, if_pos rfl]

end

end AlgMag.Sec12Printed
