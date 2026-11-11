/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Extension.Presentation.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.Algebra.MonoidAlgebra.Grading
import AlgMag.Affine.MagnetAlgebra

/-!
# Rings associated to monoids

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026) 126–201, §2.

Ring-level statements only: `R[N]` is `AddMonoidAlgebra R N`, for an arbitrary commutative ring
`R` wherever the paper's `ℤ` or `𝒪_S` allows it. Taking `R = ℤ` recovers `ℤ[N]`, and a statement
over `R` is the case `S = Spec R` of the paper's statement over `S`. Nothing here is proved for
non-affine `S` or for algebraic spaces.

## Main results

* Fact 2.2: `AlgMag.counit_X`, `AlgMag.comul_X`, `AlgMag.antipode_X`.
* Definition 2.3 (i): `AlgMag.baseChangeEquiv`.
* Fact 2.7: `AlgMag.tensorAlgEquiv`.
* Proposition 2.8: `AlgMag.flat_diag`, `AlgMag.flat_comul`.
* Remark 2.9: `AlgMag.isFreeAction_of_group`, `AlgMag.not_isFreeAction_natNeOne`.
* Fact 2.10: `AlgMag.finitePresentation`, `AlgMag.finitePresentation_comul`.
* Fact 2.12: `AlgMag.coact`, `AlgMag.coact_coassoc`, `AlgMag.coact_counit`.
* Facts 2.13, 2.15: `AlgMag.incl_mem_grading`, `AlgMag.faceProj_mem_grading`.
* Proposition 2.16: `AlgMag.isFace_iff`.
* Proposition 2.17, Fact 2.18: `AlgMag.unitsFace`, `AlgMag.faceCond_unitsFace`,
  `AlgMag.unitsFace_le`.
* Proposition 2.19, affine algebra: `AlgMag.gluedMagnet`, `AlgMag.faceCond_gluedMagnet`,
  `AlgMag.existsUnique_glued`.
-/

suppress_compilation

open TensorProduct Coalgebra

namespace AlgMag

section Bialgebra

set_option linter.unusedSectionVars false

variable (R : Type*) [CommRing R] {N L : Type*} [AddCommMonoid N] [AddCommMonoid L]

/-- The monomial `X^n` of `R[N]`. -/
abbrev X (n : N) : AddMonoidAlgebra R N := AddMonoidAlgebra.single n 1

/-- **Fact 2.2.** The augmentation sends `X^n` to `1`. The bialgebra structure itself is Mathlib's
instance on `AddMonoidAlgebra`. -/
theorem counit_X (n : N) : counit (R := R) (X R n) = 1 := by
  simp

/-- **Fact 2.2.** The comultiplication sends `X^n` to `X^n ⊗ X^n`. -/
theorem comul_X (n : N) : comul (R := R) (X R n) = X R n ⊗ₜ[R] X R n := by
  simp

/-- **Fact 2.2.** If `N` is a group, the antipode sends `X^n` to `X^{-n}`. -/
theorem antipode_X {G : Type*} [AddCommGroup G] (n : G) :
    HopfAlgebra.antipode R (X R n) = X R (-n) := by
  simp [AddMonoidAlgebra.antipode_single]

/-- **Definition 2.3 (i).** `R[N] = ℤ[N] ⊗ R`, written with `R` on the left. -/
def baseChangeEquiv : R ⊗[ℤ] AddMonoidAlgebra ℤ N ≃ₐ[R] AddMonoidAlgebra R N :=
  AddMonoidAlgebra.scalarTensorEquiv ℤ R

/-- **Fact 2.7.** `R[N] ⊗_R R[L] = R[N × L]` as `R`-algebras, `X^n ⊗ X^l ↦ X^{(n,l)}`. This is the
identification `𝔸(N × L)_S = 𝔸(N)_S ×_S 𝔸(L)_S` for `S = Spec R`; the case `R = ℤ` is the first
assertion of the Fact. -/
def tensorAlgEquiv :
    AddMonoidAlgebra R N ⊗[R] AddMonoidAlgebra R L ≃ₐ[R] AddMonoidAlgebra R (N × L) :=
  AlgEquiv.ofLinearEquiv (AddMonoidAlgebra.tensorEquiv R)
    (by
      rw [Algebra.TensorProduct.one_def]
      change AddMonoidAlgebra.tensorEquiv R
        (AddMonoidAlgebra.single 0 1 ⊗ₜ AddMonoidAlgebra.single 0 1) = _
      simp [AddMonoidAlgebra.one_def]
      rfl)
    (by
      intro x y
      induction x with
      | zero => simp
      | add a b ha hb => simp only [add_mul, map_add, ha, hb]
      | tmul a b =>
        induction y with
        | zero => simp
        | add c d hc hd => simp only [mul_add, map_add, hc, hd]
        | tmul c d =>
          induction a using AddMonoidAlgebra.induction_linear with
          | zero => simp
          | add a₁ a₂ h₁ h₂ => simp only [add_mul, add_tmul, map_add, h₁, h₂]
          | single n r =>
            induction b using AddMonoidAlgebra.induction_linear with
            | zero => simp
            | add a₁ a₂ h₁ h₂ => simp only [add_mul, tmul_add, map_add, h₁, h₂]
            | single l s =>
              induction c using AddMonoidAlgebra.induction_linear with
              | zero => simp
              | add a₁ a₂ h₁ h₂ => simp only [mul_add, add_tmul, map_add, h₁, h₂]
              | single n' r' =>
                induction d using AddMonoidAlgebra.induction_linear with
                | zero => simp
                | add a₁ a₂ h₁ h₂ => simp only [mul_add, tmul_add, map_add, h₁, h₂]
                | single l' s' =>
                  simp only [Algebra.TensorProduct.tmul_mul_tmul,
                    AddMonoidAlgebra.single_mul_single,
                    AddMonoidAlgebra.tensorEquiv_single_tmul_single, Prod.mk_add_mk]
                  congr 1
                  ring)

@[simp] lemma tensorAlgEquiv_X (n : N) (l : L) :
    tensorAlgEquiv R (X R n ⊗ₜ[R] X R l) = X R (n, l) := by
  simp [tensorAlgEquiv]

end Bialgebra

section Free

variable {P Q : Type*} [AddCommMonoid P] [AddCommMonoid Q]

/-- The action of `P` on `Q` through `θ` is free: `Q` has a subset `S` such that `P × S → Q`,
`(p, s) ↦ θ p + s`, is bijective, i.e. `Q` is a free `P`-set. This is "free" in Proposition 2.8:
a basis in Ogus's *Lectures on Logarithmic Algebraic Geometry*, §1.2, is a map `i : T → Q` with
`P × T → Q` bijective, and such an `i` is injective, so it is the inclusion of a subset. -/
def IsFreeAlong (θ : P →+ Q) : Prop :=
  ∃ S : Set Q, Function.Bijective (fun p : P × S => θ p.1 + (p.2 : Q))

/-- If `P` acts freely on `Q` through `θ`, then `R[θ] : R[P] → R[Q]` is flat; indeed `R[Q]` is a
free `R[P]`-module. This is the step of Proposition 2.8 (i) for which the paper cites Ogus. -/
theorem flat_of_isFreeAlong (R : Type*) [CommRing R] {θ : P →+ Q} (h : IsFreeAlong θ) :
    (AddMonoidAlgebra.mapDomainRingHom R θ).Flat := by
  obtain ⟨S, hS⟩ := h
  let e : P × S ≃ Q := Equiv.ofBijective _ hS
  have he : ∀ (p : P) (s : S), e.symm (θ p + (s : Q)) = (p, s) := fun p s =>
    e.symm_apply_apply (p, s)
  have he' : ∀ q : Q, θ (e.symm q).1 + ((e.symm q).2 : Q) = q := fun q => e.apply_symm_apply q
  let := (AddMonoidAlgebra.mapDomainRingHom R θ).toAlgebra
  have hsmul : ∀ (a : AddMonoidAlgebra R P) (b : AddMonoidAlgebra R Q),
      a • b = AddMonoidAlgebra.mapDomainRingHom R θ a * b := fun a b => rfl
  let F : (S →₀ AddMonoidAlgebra R P) →ₗ[AddMonoidAlgebra R P] AddMonoidAlgebra R Q :=
    Finsupp.linearCombination _ (fun s : S => AddMonoidAlgebra.single (s : Q) (1 : R))
  let g₀ : (Q →₀ R) →+ (S →₀ AddMonoidAlgebra R P) :=
    Finsupp.liftAddHom fun q =>
      (Finsupp.singleAddHom (e.symm q).2).comp
        ((AddMonoidAlgebra.coeffAddEquiv (R := R) (M := P)).symm.toAddMonoidHom.comp
          (Finsupp.singleAddHom (e.symm q).1))
  let g : AddMonoidAlgebra R Q →+ (S →₀ AddMonoidAlgebra R P) :=
    g₀.comp (AddMonoidAlgebra.coeffAddEquiv (R := R) (M := Q)).toAddMonoidHom
  have hg : ∀ (q : Q) (c : R), g (AddMonoidAlgebra.single q c) =
      Finsupp.single (e.symm q).2 (AddMonoidAlgebra.single (e.symm q).1 c) := by
    intro q c
    simp only [g, g₀, AddMonoidHom.comp_apply]
    change Finsupp.liftAddHom _ (Finsupp.single q c) = _
    simp only [Finsupp.liftAddHom_apply_single]
    rfl
  have hF : ∀ (s : S) (p : P) (c : R),
      F (Finsupp.single s (AddMonoidAlgebra.single p c)) =
        AddMonoidAlgebra.single (θ p + (s : Q)) c := by
    intro s p c
    simp [F, Finsupp.linearCombination_single, hsmul, AddMonoidAlgebra.single_mul_single]
  have left : ∀ y, g (F y) = y := by
    intro y
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single s a =>
      induction a using AddMonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [Finsupp.single_add, map_add, ha, hb]
      | single p c => rw [hF, hg, he]
  have right : ∀ x, F (g x) = x := by
    intro x
    induction x using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single q c => rw [hg, hF, he']
  let E := LinearEquiv.ofBijective F
    ⟨Function.LeftInverse.injective left, Function.RightInverse.surjective right⟩
  have : Module.Free (AddMonoidAlgebra R P) (AddMonoidAlgebra R Q) := Module.Free.of_equiv E
  exact Module.Flat.of_free

variable (N : Type*) [AddCommMonoid N]

/-- The diagonal `N → N × N`, giving the action `n · (a, b) = (a + n, b + n)` of Proposition 2.8. -/
def diag : N →+ N × N := (AddMonoidHom.id N).prod (AddMonoidHom.id N)

variable {N}

/-- **Proposition 2.8 (i)**, over any commutative ring. If the diagonal action of `N` on `N × N`
is free, then `R[N] → R[N × N]`, `X^n ↦ X^{(n,n)}`, is flat. The paper also assumes `N`
cancellative; this is not needed once the action is free in the sense of `IsFreeAlong`. -/
theorem flat_diag (R : Type*) [CommRing R] (h : IsFreeAlong (diag N)) :
    (AddMonoidAlgebra.mapDomainRingHom R (diag N)).Flat :=
  flat_of_isFreeAlong R h

/-- The comultiplication is the diagonal map, read through Fact 2.7. -/
lemma comul_eq_diag (R : Type*) [CommRing R] (a : AddMonoidAlgebra R N) :
    tensorAlgEquiv R (Bialgebra.comulAlgHom R (AddMonoidAlgebra R N) a) =
      AddMonoidAlgebra.mapDomainRingHom R (diag N) a := by
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single n c =>
    have hc : (AddMonoidAlgebra.single n c : AddMonoidAlgebra R N) = c • X R n := by
      simp [AddMonoidAlgebra.smul_single]
    have hr : AddMonoidAlgebra.mapDomainRingHom R (diag N) (AddMonoidAlgebra.single n c) =
        AddMonoidAlgebra.single (diag N n) c := AddMonoidAlgebra.mapDomain_single
    rw [hr, hc, map_smul, map_smul]
    simp [diag, AddMonoidAlgebra.smul_single]

/-- **Proposition 2.8 (ii), (iii)**, affine case. The multiplication of `𝔸(N)_{Spec R}` is flat:
its ring map `R[N] → R[N] ⊗_R R[N]`, the comultiplication, is flat. `R = ℤ` is assertion (ii),
and `S = Spec R` is assertion (iii). Non-affine `S` and algebraic spaces (iv) are not treated. -/
theorem flat_comul (R : Type*) [CommRing R] (h : IsFreeAlong (diag N)) :
    (Bialgebra.comulAlgHom R (AddMonoidAlgebra R N)).toRingHom.Flat := by
  have key : (Bialgebra.comulAlgHom R (AddMonoidAlgebra R N)).toRingHom =
      ((tensorAlgEquiv (N := N) (L := N) R).symm.toRingEquiv.toRingHom).comp
        (AddMonoidAlgebra.mapDomainRingHom R (diag N)) := by
    refine RingHom.ext fun a => ?_
    change _ = (tensorAlgEquiv (N := N) (L := N) R).symm _
    rw [← comul_eq_diag, AlgEquiv.symm_apply_apply]
    rfl
  rw [key]
  exact (flat_diag R h).comp (RingHom.Flat.of_bijective (tensorAlgEquiv (N := N) (L := N) R).symm.bijective)

/-- **Remark 2.9**, first assertion: for a commutative group, the diagonal action is free. -/
theorem isFreeAction_of_group (G : Type*) [AddCommGroup G] : IsFreeAlong (diag G) := by
  refine ⟨{x | x.1 = 0}, ?_, ?_⟩
  · rintro ⟨p, ⟨⟨a, b⟩, ha⟩⟩ ⟨p', ⟨⟨a', b'⟩, ha'⟩⟩ h
    simp only [Set.mem_ofPred_eq] at ha ha'
    subst ha ha'
    simp only [diag, AddMonoidHom.prod_apply, AddMonoidHom.id_apply, Prod.mk_add_mk, add_zero,
      Prod.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    simp only [add_right_inj] at h
    subst h
    rfl
  · rintro ⟨a, b⟩
    refine ⟨⟨a, ⟨(0, b - a), rfl⟩⟩, ?_⟩
    simp [diag]

/-- The monoid `ℕ \ {1}` of Remark 2.9. -/
def natNeOne : AddSubmonoid ℕ where
  carrier := {n | n ≠ 1}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    omega

/-- **Remark 2.9**, second assertion: for `N = ℕ \ {1}` the diagonal action is not free.
The witness differs from the printed one: `(4, 5)` does *not* lie in the orbit of `(3, 4)`, as
`1 ∉ N`; the point lying in both orbits used here is `(5, 6) = 3 · (2, 3) = 2 · (3, 4)`. -/
theorem not_isFreeAction_natNeOne : ¬ IsFreeAlong (diag natNeOne) := by
  rintro ⟨S, hinj, hsurj⟩
  -- an element of the form `(a, b)` with no proper decomposition lies in `S`
  have key : ∀ a b (ha : a ≠ 1) (hb : b ≠ 1),
      (∀ p, p ≠ 1 → p ≤ a → p ≤ b → (a - p) ≠ 1 → (b - p) ≠ 1 → p = 0) →
      ((⟨a, ha⟩ : natNeOne), (⟨b, hb⟩ : natNeOne)) ∈ S := by
    intro a b ha hb hmin
    obtain ⟨⟨p, ⟨⟨⟨u, hu⟩, ⟨v, hv⟩⟩, hs⟩⟩, h⟩ := hsurj (⟨a, ha⟩, ⟨b, hb⟩)
    obtain ⟨p, hp⟩ := p
    have h1 : p + u = a := congrArg (fun q : natNeOne × natNeOne => (q.1 : ℕ)) h
    have h2 : p + v = b := congrArg (fun q : natNeOne × natNeOne => (q.2 : ℕ)) h
    have hu' : u ≠ 1 := hu
    have hv' : v ≠ 1 := hv
    have hp0 : p = 0 := hmin p hp (by omega) (by omega) (by omega) (by omega)
    subst hp0
    simp only [zero_add] at h1 h2
    subst h1 h2
    exact hs
  have h23 := key 2 3 (by omega) (by omega) (by
    intro p _ _ _ _ _; omega)
  have h34 := key 3 4 (by omega) (by omega) (by
    intro p _ _ _ _ _; omega)
  have := @hinj
    ((⟨3, by change 3 ≠ 1; omega⟩ : natNeOne), ⟨_, h23⟩)
    ((⟨2, by change 2 ≠ 1; omega⟩ : natNeOne), ⟨_, h34⟩) rfl
  have h32 : (3 : ℕ) = 2 := congrArg (fun q : natNeOne × S => ((q.1 : natNeOne) : ℕ)) this
  omega

end Free

section FinitePresentation

variable (R : Type*) [CommRing R] (N : Type*) [AddCommMonoid N] [AddMonoid.FG N]

/-- **Fact 2.10 (ii), (v)**, affine case. If `N` is finitely generated then `R[N]` is a finitely
presented `R`-algebra; `R = ℤ` is (ii). The proof uses that `ℤ` is noetherian, and so does not
pass through Fact 2.10 (i). -/
theorem finitePresentation : Algebra.FinitePresentation R (AddMonoidAlgebra R N) := by
  have hZ : Algebra.FinitePresentation ℤ (AddMonoidAlgebra ℤ N) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨n, m, ⟨P⟩⟩ := Algebra.Presentation.exists_presentation_fin ℤ (AddMonoidAlgebra ℤ N)
  have : Algebra.FinitePresentation R (R ⊗[ℤ] AddMonoidAlgebra ℤ N) :=
    (P.baseChange R).finitePresentation_of_isFinite
  exact Algebra.FinitePresentation.equiv (baseChangeEquiv R)

/-- **Fact 2.10 (iv), (v)**, affine case. The multiplication of `𝔸(N)_{Spec R}` is of finite
presentation. -/
theorem finitePresentation_comul :
    (Bialgebra.comulAlgHom R (AddMonoidAlgebra R N)).toRingHom.FinitePresentation := by
  have h1 : Algebra.FinitePresentation R (AddMonoidAlgebra R (N × N)) :=
    finitePresentation R (N × N)
  have h2 : Algebra.FinitePresentation R
      (AddMonoidAlgebra R N ⊗[R] AddMonoidAlgebra R N) :=
    Algebra.FinitePresentation.equiv (tensorAlgEquiv R).symm
  refine RingHom.FinitePresentation.of_comp_finiteType (algebraMap R (AddMonoidAlgebra R N))
    ?_ ?_
  · have : (Bialgebra.comulAlgHom R (AddMonoidAlgebra R N)).toRingHom.comp
        (algebraMap R (AddMonoidAlgebra R N)) =
        algebraMap R (AddMonoidAlgebra R N ⊗[R] AddMonoidAlgebra R N) :=
      (Bialgebra.comulAlgHom R (AddMonoidAlgebra R N)).comp_algebraMap
    rw [this, RingHom.finitePresentation_algebraMap]
    exact h2
  · rw [RingHom.finiteType_algebraMap]
    exact inferInstance

end FinitePresentation

section Magnets

variable (R : Type*) [CommRing R] {M : Type*} [AddCommMonoid M]

/-- The inclusion morphism `R[N] → R[N']` of Fact 2.13, for submonoids `N ≤ N'` of `M`. -/
def incl {N N' : AddSubmonoid M} (h : N ≤ N') : AddMonoidAlgebra R N →ₐ[R] AddMonoidAlgebra R N' :=
  AddMonoidAlgebra.mapDomainAlgHom R R (AddSubmonoid.inclusion h)

@[simp] lemma incl_single {N N' : AddSubmonoid M} (h : N ≤ N') (n : N) (c : R) :
    incl R h (AddMonoidAlgebra.single n c) =
      AddMonoidAlgebra.single (AddSubmonoid.inclusion h n) c := by
  simp [incl]

/-- The projection `R[N] → R[F]` of Definition 2.14: `X^n ↦ X^n` if `n ∈ F`, and `X^n ↦ 0`
otherwise. It is `R`-linear, and a priori not multiplicative. -/
def faceProj {F N : AddSubmonoid M} (h : F ≤ N) : AddMonoidAlgebra R N →ₗ[R] AddMonoidAlgebra R F :=
  (AddMonoidAlgebra.coeffLinearEquiv R).symm.toLinearMap ∘ₗ
    Finsupp.lcomapDomain _ (AddSubmonoid.inclusion_injective h) ∘ₗ
    (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

lemma faceProj_coeff {F N : AddSubmonoid M} (h : F ≤ N) (a : AddMonoidAlgebra R N) (f : F) :
    (faceProj R h a).coeff f = a.coeff (AddSubmonoid.inclusion h f) := rfl

variable {R}

lemma faceProj_single_mem {F N : AddSubmonoid M} (h : F ≤ N) (f : F) (c : R) :
    faceProj R h (AddMonoidAlgebra.single (AddSubmonoid.inclusion h f) c) =
      AddMonoidAlgebra.single f c := by
  refine AddMonoidAlgebra.coeff_inj.mp (Finsupp.ext fun g => ?_)
  rw [faceProj_coeff]
  simp only [AddMonoidAlgebra.coeff_single]
  exact Finsupp.single_apply_left (AddSubmonoid.inclusion_injective h) _ _ _

lemma faceProj_single_notMem {F N : AddSubmonoid M} (h : F ≤ N) (n : N) (hn : (n : M) ∉ F) (c : R) :
    faceProj R h (AddMonoidAlgebra.single n c) = 0 := by
  refine AddMonoidAlgebra.coeff_inj.mp (Finsupp.ext fun g => ?_)
  rw [faceProj_coeff]
  simp only [AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero,
    Pi.zero_apply]
  refine Finsupp.single_eq_of_ne ?_
  intro e
  have e' := congrArg Subtype.val e
  first
    | exact hn (e' ▸ g.2)

variable (R)

/-- **Definition 2.14**, over `R`: the projection `R[N] → R[F]` is a morphism of rings. The paper's
definition is the case `R = ℤ`. -/
def IsFaceOver {F N : AddSubmonoid M} (h : F ≤ N) : Prop :=
  faceProj R h 1 = 1 ∧ ∀ a b, faceProj R h (a * b) = faceProj R h a * faceProj R h b

/-- The combinatorial condition of Proposition 2.16. -/
def FaceCond (F N : AddSubmonoid M) : Prop :=
  ∀ x ∈ N, ∀ y ∈ N, x + y ∈ F → x ∈ F ∧ y ∈ F

variable {R}

/-- **Proposition 2.16**, over any nontrivial commutative ring (`R = ℤ` is the printed statement):
`F` is a face of `N` if and only if `x + y ∈ F ⇒ x ∈ F and y ∈ F` for all `x, y ∈ N`. -/
theorem isFace_iff [Nontrivial R] {F N : AddSubmonoid M} (h : F ≤ N) :
    IsFaceOver R h ↔ FaceCond F N := by
  constructor
  · rintro ⟨-, hmul⟩ x hx y hy hxy
    have hsplit := hmul (AddMonoidAlgebra.single ⟨x, hx⟩ 1) (AddMonoidAlgebra.single ⟨y, hy⟩ 1)
    rw [AddMonoidAlgebra.single_mul_single, one_mul] at hsplit
    have hne : faceProj R h (AddMonoidAlgebra.single (⟨x, hx⟩ + ⟨y, hy⟩ : N) (1 : R)) ≠ 0 := by
      have := faceProj_single_mem (R := R) h ⟨x + y, hxy⟩ 1
      have e : AddSubmonoid.inclusion h ⟨x + y, hxy⟩ = (⟨x, hx⟩ + ⟨y, hy⟩ : N) := rfl
      rw [e] at this
      rw [this]
      simp
    constructor
    · by_contra hc
      rw [hsplit, faceProj_single_notMem h ⟨x, hx⟩ hc, zero_mul] at hne
      exact hne rfl
    · by_contra hc
      rw [hsplit, faceProj_single_notMem h ⟨y, hy⟩ hc, mul_zero] at hne
      exact hne rfl
  · intro hc
    refine ⟨?_, fun a b => ?_⟩
    · have := faceProj_single_mem (R := R) h 0 1
      simpa [AddMonoidAlgebra.one_def] using this
    · induction a using AddMonoidAlgebra.induction_linear with
      | zero => simp
      | add a₁ a₂ h₁ h₂ => simp only [add_mul, map_add, h₁, h₂]
      | single x r =>
        induction b using AddMonoidAlgebra.induction_linear with
        | zero => simp
        | add a₁ a₂ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂]
        | single y s =>
          rw [AddMonoidAlgebra.single_mul_single]
          by_cases hx : (x : M) ∈ F
          · by_cases hy : (y : M) ∈ F
            · have e₁ := faceProj_single_mem (R := R) h ⟨x, hx⟩ r
              have e₂ := faceProj_single_mem (R := R) h ⟨y, hy⟩ s
              have e₃ := faceProj_single_mem (R := R) h ⟨x + y, F.add_mem hx hy⟩ (r * s)
              change faceProj R h (AddMonoidAlgebra.single x r) = _ at e₁
              change faceProj R h (AddMonoidAlgebra.single y s) = _ at e₂
              change faceProj R h (AddMonoidAlgebra.single (x + y) (r * s)) = _ at e₃
              rw [e₁, e₂, e₃, AddMonoidAlgebra.single_mul_single]
              rfl
            · rw [faceProj_single_notMem h y hy, mul_zero, faceProj_single_notMem h (x + y)]
              exact fun hxy => hy (hc x x.2 y y.2 hxy).2
          · rw [faceProj_single_notMem h x hx, zero_mul, faceProj_single_notMem h (x + y)]
            exact fun hxy => hx (hc x x.2 y y.2 hxy).1

/-- A face of `N` as a morphism of `R`-algebras `R[N] → R[F]`. -/
def faceProjAlgHom {F N : AddSubmonoid M} (h : F ≤ N) (hc : FaceCond F N) [Nontrivial R] :
    AddMonoidAlgebra R N →ₐ[R] AddMonoidAlgebra R F :=
  AlgHom.ofLinearMap (faceProj R h) ((isFace_iff h).mpr hc).1 ((isFace_iff h).mpr hc).2

variable (R)

/-- **Fact 2.13.** The inclusion `R[N] → R[N']` preserves the `M`-gradings. -/
theorem incl_mem_grading [DecidableEq M] {N N' : AddSubmonoid M} (h : N ≤ N') {m : M}
    {a : AddMonoidAlgebra R N} (ha : a ∈ Magnetism.magnetGrading N R m) :
    incl R h a ∈ Magnetism.magnetGrading N' R m := by
  by_cases hm : m ∈ N
  · obtain ⟨c, rfl⟩ := Magnetism.exists_single_of_mem_magnetGrading hm ha
    rw [incl_single]
    exact Magnetism.single_mem_magnetGrading (AddSubmonoid.inclusion h ⟨m, hm⟩) c
  · rw [Magnetism.magnetGrading_eq_bot hm, Submodule.mem_bot] at ha
    simp [ha]

/-- **Fact 2.15.** The projection `R[N] → R[F]` preserves the `M`-gradings. -/
theorem faceProj_mem_grading [DecidableEq M] {F N : AddSubmonoid M} (h : F ≤ N) {m : M}
    {a : AddMonoidAlgebra R N} (ha : a ∈ Magnetism.magnetGrading N R m) :
    faceProj R h a ∈ Magnetism.magnetGrading F R m := by
  by_cases hm : m ∈ N
  · obtain ⟨c, rfl⟩ := Magnetism.exists_single_of_mem_magnetGrading hm ha
    by_cases hF : m ∈ F
    · have := faceProj_single_mem (R := R) h ⟨m, hF⟩ c
      change faceProj R h (AddMonoidAlgebra.single ⟨m, hm⟩ c) = _ at this
      rw [this]
      exact Magnetism.single_mem_magnetGrading ⟨m, hF⟩ c
    · rw [faceProj_single_notMem h ⟨m, hm⟩ hF]
      exact Submodule.zero_mem _
  · rw [Magnetism.magnetGrading_eq_bot hm, Submodule.mem_bot] at ha
    simp [ha]

/-- **Fact 2.12.** The coaction `R[N] → R[N] ⊗ R[M]`, `X^n ↦ X^n ⊗ X^n`, of the algebraic action
of `𝔸(M)` on `𝔸(N)`. -/
def coact (N : AddSubmonoid M) :
    AddMonoidAlgebra R N →ₐ[R] AddMonoidAlgebra R N ⊗[R] AddMonoidAlgebra R M :=
  (Algebra.TensorProduct.map (AlgHom.id R _)
    (AddMonoidAlgebra.mapDomainAlgHom R R N.subtype)).comp
      (Bialgebra.comulAlgHom R (AddMonoidAlgebra R N))

@[simp] lemma coact_X (N : AddSubmonoid M) (n : N) :
    coact R N (X R n) = X R n ⊗ₜ[R] X R (n : M) := by
  simp [coact]

/-- **Fact 2.12.** The coaction is coassociative: this is `(g h) · x = g · (h · x)`. -/
theorem coact_coassoc (N : AddSubmonoid M) (a : AddMonoidAlgebra R N) :
    TensorProduct.assoc R _ _ _
      (TensorProduct.map (coact R N).toLinearMap LinearMap.id (coact R N a)) =
    TensorProduct.map LinearMap.id (comul (R := R) (A := AddMonoidAlgebra R M)) (coact R N a) := by
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single n c =>
    have hc : (AddMonoidAlgebra.single n c : AddMonoidAlgebra R N) = c • X R n := by
      simp [AddMonoidAlgebra.smul_single]
    rw [hc, map_smul]
    simp only [map_smul, coact_X, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, coact_X,
      TensorProduct.assoc_tmul, LinearMap.id_apply, comul_X]

/-- **Fact 2.12.** The unit of `𝔸(M)` acts trivially. -/
theorem coact_counit (N : AddSubmonoid M) (a : AddMonoidAlgebra R N) :
    TensorProduct.rid R _
      (TensorProduct.map LinearMap.id (counit (R := R) (A := AddMonoidAlgebra R M))
        (coact R N a)) = a := by
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single n c =>
    have hc : (AddMonoidAlgebra.single n c : AddMonoidAlgebra R N) = c • X R n := by
      simp [AddMonoidAlgebra.smul_single]
    rw [hc, map_smul]
    simp only [map_smul, coact_X, TensorProduct.map_tmul, LinearMap.id_apply, counit_X,
      TensorProduct.rid_tmul, one_smul]

/-- **Proposition 2.17.** The submonoid `N^×` of `M` of invertible elements of `N`. -/
def unitsFace (N : AddSubmonoid M) : AddSubmonoid M where
  carrier := {x | x ∈ N ∧ ∃ y ∈ N, x + y = 0}
  zero_mem' := ⟨N.zero_mem, 0, N.zero_mem, add_zero 0⟩
  add_mem' := by
    rintro a b ⟨ha, a', ha', e⟩ ⟨hb, b', hb', e'⟩
    exact ⟨N.add_mem ha hb, a' + b', N.add_mem ha' hb', by
      rw [add_add_add_comm, e, e', add_zero]⟩

lemma unitsFace_le (N : AddSubmonoid M) : unitsFace N ≤ N := fun _ h => h.1

/-- **Proposition 2.17.** `N^×` is a group: inverses of its elements lie in it. -/
theorem unitsFace_isGroup (N : AddSubmonoid M) {x : M} (hx : x ∈ unitsFace N) :
    ∃ y ∈ unitsFace N, x + y = 0 := by
  obtain ⟨hxN, y, hy, e⟩ := hx
  exact ⟨y, ⟨hy, x, hxN, by rw [add_comm, e]⟩, e⟩

/-- **Proposition 2.17.** `N^×` is a face of `N`. -/
theorem faceCond_unitsFace (N : AddSubmonoid M) : FaceCond (unitsFace N) N := by
  rintro x hx y hy ⟨-, z, hz, e⟩
  exact ⟨⟨hx, y + z, N.add_mem hy hz, by rw [← add_assoc, e]⟩,
    ⟨hy, x + z, N.add_mem hx hz, by rw [← add_assoc, add_comm y x, e]⟩⟩

/-- **Proposition 2.17.** `N^×` is the largest subgroup of `N`. -/
theorem le_unitsFace {G N : AddSubmonoid M} (hG : G ≤ N) (hinv : ∀ x ∈ G, ∃ y ∈ G, x + y = 0) :
    G ≤ unitsFace N := fun x hx => by
  obtain ⟨y, hy, e⟩ := hinv x hx
  exact ⟨hG hx, y, hG hy, e⟩

/-- **Fact 2.18.** Every face of `N` contains `N^×`. -/
theorem unitsFace_le_face {F N : AddSubmonoid M} (hc : FaceCond F N) : unitsFace N ≤ F := by
  rintro x ⟨hx, y, hy, e⟩
  exact (hc x hx y hy (e ▸ F.zero_mem)).1

/-- **Proposition 2.19.** The submonoid `N' = L' \ (L \ N)`. -/
def gluedMagnet {N L L' : AddSubmonoid M} (_hNL : N ≤ L) (hc : FaceCond L L') :
    AddSubmonoid M where
  carrier := {x | x ∈ L' ∧ ¬ (x ∈ L ∧ x ∉ N)}
  zero_mem' := ⟨L'.zero_mem, fun h => h.2 N.zero_mem⟩
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨L'.add_mem ha hb, fun h => h.2 ?_⟩
    obtain ⟨h1, h2⟩ := hc a ha b hb h.1
    have hn1 : a ∈ N := by by_contra hn; exact ha' ⟨h1, hn⟩
    have hn2 : b ∈ N := by by_contra hn; exact hb' ⟨h2, hn⟩
    exact N.add_mem hn1 hn2

variable {N L L' : AddSubmonoid M} (hNL : N ≤ L) (hLL' : L ≤ L') (hc : FaceCond L L')

lemma mem_gluedMagnet {x : M} : x ∈ gluedMagnet hNL hc ↔ x ∈ L' ∧ ¬ (x ∈ L ∧ x ∉ N) := Iff.rfl

include hLL' in
lemma le_gluedMagnet : N ≤ gluedMagnet hNL hc := fun _ hx =>
  ⟨hLL' (hNL hx), fun h => h.2 hx⟩

lemma gluedMagnet_le : gluedMagnet hNL hc ≤ L' := fun _ hx => hx.1

/-- **Proposition 2.19.** `N` is a face of `N' = L' \ (L \ N)`. -/
theorem faceCond_gluedMagnet : FaceCond N (gluedMagnet hNL hc) := by
  rintro x ⟨hx, hx'⟩ y ⟨hy, hy'⟩ hxy
  obtain ⟨h1, h2⟩ := hc x hx y hy (hNL hxy)
  exact ⟨by by_contra hn; exact hx' ⟨h1, hn⟩, by by_contra hn; exact hy' ⟨h2, hn⟩⟩

/-- The square of Proposition 2.19 commutes. -/
theorem glued_comm (z : AddMonoidAlgebra R (gluedMagnet hNL hc)) :
    faceProj R hLL' (incl R (gluedMagnet_le hNL hc) z) =
      incl R hNL (faceProj R (le_gluedMagnet hNL hLL' hc) z) := by
  induction z using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single n c =>
    by_cases hn : (n : M) ∈ N
    · have e := faceProj_single_mem (R := R) (le_gluedMagnet hNL hLL' hc) ⟨n, hn⟩ c
      change faceProj R _ (AddMonoidAlgebra.single n c) = _ at e
      have e' := faceProj_single_mem (R := R) hLL' ⟨n, hNL hn⟩ c
      rw [e, incl_single, incl_single]
      exact e'
    · have hnL : (n : M) ∉ L := fun h => n.2.2 ⟨h, hn⟩
      rw [faceProj_single_notMem _ n hn, map_zero, incl_single,
        faceProj_single_notMem hLL' _ hnL]

/-- **Proposition 2.19**, affine algebra. `R[N']` is the fibre product `R[L'] ×_{R[L]} R[N]`:
given `x ∈ R[L']` and `y ∈ R[N]` with the same image in `R[L]`, there is a unique `z ∈ R[N']`
restricting to them. Together with `AlgMag.glued_comm` this is the identity used in the paper's
proof. The push-out assertion in the category of schemes is not formalized here. -/
theorem existsUnique_glued (x : AddMonoidAlgebra R L') (y : AddMonoidAlgebra R N)
    (hxy : faceProj R hLL' x = incl R hNL y) :
    ∃! z : AddMonoidAlgebra R (gluedMagnet hNL hc),
      incl R (gluedMagnet_le hNL hc) z = x ∧
        faceProj R (le_gluedMagnet hNL hLL' hc) z = y := by
  classical
  have hincl_coeff : ∀ {A B : AddSubmonoid M} (h : A ≤ B) (a : AddMonoidAlgebra R A) (f : A),
      (incl R h a).coeff (AddSubmonoid.inclusion h f) = a.coeff f := by
    intro A B h a f
    change (Finsupp.mapDomain _ a.coeff) _ = _
    exact Finsupp.mapDomain_apply (AddSubmonoid.inclusion_injective h) _ _
  have hincl_off : ∀ {A B : AddSubmonoid M} (h : A ≤ B) (a : AddMonoidAlgebra R A) (b : B),
      (b : M) ∉ A → (incl R h a).coeff b = 0 := by
    intro A B h a b hb
    change (Finsupp.mapDomain _ a.coeff) _ = _
    refine Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨f, rfl⟩
    exact hb f.2
  have hle := gluedMagnet_le hNL hc
  have hsupp : ∀ l : L', l ∈ x.coeff.support → (l : M) ∈ gluedMagnet hNL hc := by
    intro l hl
    refine ⟨l.2, fun hbad => ?_⟩
    have h1 := faceProj_coeff R hLL' x ⟨l, hbad.1⟩
    rw [hxy, hincl_off hNL y ⟨l, hbad.1⟩ hbad.2] at h1
    exact Finsupp.mem_support_iff.mp hl h1.symm
  let z : AddMonoidAlgebra R (gluedMagnet hNL hc) :=
    AddMonoidAlgebra.ofCoeff (x.coeff.comapDomain (AddSubmonoid.inclusion hle)
      (AddSubmonoid.inclusion_injective hle).injOn)
  have hz : ∀ f, z.coeff f = x.coeff (AddSubmonoid.inclusion hle f) := fun f => rfl
  have hzx : incl R hle z = x := by
    refine AddMonoidAlgebra.coeff_inj.mp (Finsupp.ext fun l => ?_)
    by_cases hl : (l : M) ∈ gluedMagnet hNL hc
    · have := hincl_coeff hle z ⟨l, hl⟩
      rw [hz] at this
      exact this
    · rw [hincl_off hle z l hl]
      by_contra hne
      exact hl (hsupp l (Finsupp.mem_support_iff.mpr (Ne.symm hne)))
  refine ⟨z, ⟨hzx, ?_⟩, ?_⟩
  · refine AddMonoidAlgebra.coeff_inj.mp (Finsupp.ext fun n => ?_)
    rw [faceProj_coeff, hz]
    have h1 := faceProj_coeff R hLL' x (AddSubmonoid.inclusion hNL n)
    rw [hxy, hincl_coeff] at h1
    exact h1.symm
  · rintro w ⟨hw, -⟩
    have hinj : Function.Injective (incl R hle) := by
      intro a b hab
      refine AddMonoidAlgebra.coeff_inj.mp (Finsupp.ext fun f => ?_)
      rw [← hincl_coeff hle a f, ← hincl_coeff hle b f, hab]
    exact hinj (hw.trans hzx.symm)

end Magnets

end AlgMag
