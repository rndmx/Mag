/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Algebra.Category.CommAlgCat.Basic
import AlgMag.Foundations
import AlgMag.Affine.Naturality

/-!
# Comparison of Definition 3.1 with the graded description, affine case

Let `S = Spec R` and `X = Spec A`, with `A` an `M`-graded `R`-algebra; by Proposition 2.22 the
grading is an action of `𝔸(M)_S` on `X`. We work on the category of affine `S`-schemes, the opposite
of `R`-algebras.

The main result `AlgMag.attractorPtEquiv` identifies the points of the general attractor of
`AlgMag.Foundations` with the graded maps `Hom_R^{M-graded}(A, C[N])` of `Magnetism.Attractor`. This
is the identification used in the proof of Theorem 3.20. Composing with `Magnetism.attractorEquiv`
gives `AlgMag.attractorPtEquivQuotient`: the attractor is represented by `Spec (A / J_N)`.
-/

suppress_compilation

open CategoryTheory Opposite Magnetism

universe u

namespace AlgMag

variable (R : Type u) [CommRing R]

/-- The category of affine schemes over `Spec R`. -/
abbrev Aff := (CommAlgCat.{u} R)ᵒᵖ

/-- The ring of functions on affine schemes over `Spec R`. -/
def affO : (Aff R)ᵒᵖ ⥤ CommRingCat.{u} :=
  unopUnop _ ⋙ forget₂ (CommAlgCat.{u} R) CommRingCat.{u}

variable {R}
variable {M A : Type u} [AddCommMonoid M] [DecidableEq M] [CommRing A] [Algebra R A]

variable (R A) in
/-- The functor of points of `X = Spec A` on affine schemes over `Spec R`. -/
def affX : (Aff R)ᵒᵖ ⥤ Type u where
  obj U := A →ₐ[R] (unop (unop U) : CommAlgCat.{u} R)
  map f := ↾ fun x => f.unop.unop.hom.comp x

variable (𝒜 : M → Submodule R A) [GradedAlgebra 𝒜]

/-- Two algebra maps out of a graded algebra agree if they agree on homogeneous elements. -/
lemma algHom_ext_of_homogeneous {D : Type u} [CommRing D] [Algebra R D] {f g : A →ₐ[R] D}
    (h : ∀ (m : M) (a : A), a ∈ 𝒜 m → f a = g a) : f = g := by
  refine AlgHom.ext fun a => ?_
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous m x => exact h m x x.2
  | add a a' ha ha' => simp only [map_add, ha, ha']

section Smul

variable {D : Type u} [CommRing D] [Algebra R D]

/-- Degree `m` component of `h • f`: multiplication of `f` by `h(m)`. -/
def smulComponent (h : Multiplicative M →* D) (f : A →ₐ[R] D) (m : M) : 𝒜 m →ₗ[R] D where
  toFun a := h (Multiplicative.ofAdd m) * f a
  map_add' a b := by simp [mul_add]
  map_smul' r a := by simp

/-- The action of `h ∈ 𝔸(M)(D)` on `f ∈ X(D)` given by the grading (Proposition 2.22). -/
def gradedSmul (h : Multiplicative M →* D) (f : A →ₐ[R] D) : A →ₐ[R] D :=
  (DirectSum.toAlgebra R (fun m => (𝒜 m : Submodule R A)) (smulComponent 𝒜 h f)
    (by
      change h (Multiplicative.ofAdd 0) * f _ = 1
      simp)
    (by
      intro i j ai aj
      change h (Multiplicative.ofAdd (i + j)) * f _ =
        h (Multiplicative.ofAdd i) * f ai * (h (Multiplicative.ofAdd j) * f aj)
      rw [SetLike.coe_gMul 𝒜 ai aj, ofAdd_add, map_mul, map_mul]
      ring)).comp
    (DirectSum.decomposeAlgEquiv 𝒜).toAlgHom

lemma gradedSmul_apply_of_mem (h : Multiplicative M →* D) (f : A →ₐ[R] D) {m : M} {a : A}
    (ha : a ∈ 𝒜 m) : gradedSmul 𝒜 h f a = h (Multiplicative.ofAdd m) * f a := by
  rw [gradedSmul, AlgHom.comp_apply,
    show (DirectSum.decomposeAlgEquiv 𝒜).toAlgHom a = DirectSum.of (fun i => 𝒜 i) m ⟨a, ha⟩ from
      DirectSum.decompose_of_mem 𝒜 ha]
  simp only [DirectSum.toAlgebra_apply]
  exact DirectSum.toSemiring_of _ _ _ _ _

end Smul

/-- The action of `𝔸(M)` on `Spec A` determined by the grading (Proposition 2.22). -/
def gradedAction : AAction (affO R) M (affX R A) where
  smul {U} h x := gradedSmul (D := (unop (unop U) : CommAlgCat.{u} R)) 𝒜 h x
  one_smul {U} x := by
    let D : CommAlgCat.{u} R := unop (unop U)
    refine algHom_ext_of_homogeneous (D := D) 𝒜 fun m a ha => ?_
    refine (gradedSmul_apply_of_mem (D := D) 𝒜 _ _ ha).trans ?_
    exact one_mul (M := D) _
  mul_smul {U} g h x := by
    let D : CommAlgCat.{u} R := unop (unop U)
    refine algHom_ext_of_homogeneous (D := D) 𝒜 fun m a ha => ?_
    refine (gradedSmul_apply_of_mem (D := D) 𝒜 _ _ ha).trans ?_
    refine Eq.trans ?_ (gradedSmul_apply_of_mem (D := D) 𝒜 _ _ ha).symm
    refine Eq.trans (mul_assoc (G := D) _ _ _) (congrArg _ ?_)
    exact (gradedSmul_apply_of_mem (D := D) 𝒜 _ _ ha).symm
  map_smul {U V} f h x := by
    let D : CommAlgCat.{u} R := unop (unop U)
    let D' : CommAlgCat.{u} R := unop (unop V)
    let φ : D →ₐ[R] D' := f.unop.unop.hom
    refine algHom_ext_of_homogeneous (D := D') 𝒜 fun m a ha => ?_
    refine Eq.trans ?_ (gradedSmul_apply_of_mem (D := D') 𝒜 _ _ ha).symm
    refine Eq.trans (congrArg φ (gradedSmul_apply_of_mem (D := D) 𝒜 _ _ ha)) ?_
    exact map_mul φ _ _

section Comparison

variable (N : AddSubmonoid M) (C : Type u) [CommRing C] [Algebra R C]

variable {N C} in
/-- The evaluation `C[N] → D` of a point `a` of `𝔸(N)` over `t : C → D`. -/
def evalAlg {D : Type u} [CommRing D] [Algebra R D] (t : C →ₐ[R] D)
    (a : Multiplicative N →* D) : AddMonoidAlgebra C N →ₐ[R] D :=
  AddMonoidAlgebra.liftNCAlgHom t a fun _ _ => Commute.all _ _

@[simp] lemma evalAlg_single {D : Type u} [CommRing D] [Algebra R D] (t : C →ₐ[R] D)
    (a : Multiplicative N →* D) (n : N) (c : C) :
    evalAlg t a (AddMonoidAlgebra.single n c) = t c * a (Multiplicative.ofAdd n) := by
  simp [evalAlg, AddMonoidAlgebra.liftNC_single]

/-- The inclusion of constants `C → C[N]`, as a map of `R`-algebras. -/
def constAlg (P : Type u) [AddCommMonoid P] (C : Type u) [CommRing C] [Algebra R C] :
    C →ₐ[R] AddMonoidAlgebra C P :=
  (Algebra.ofId C (AddMonoidAlgebra C P)).restrictScalars R

lemma constAlg_apply (P : Type u) [AddCommMonoid P] (c : C) :
    constAlg (R := R) P C c = AddMonoidAlgebra.single 0 c := rfl

/-- Morphism of affine schemes induced by an algebra map. -/
abbrev affHom {D D' : Type u} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D']
    (f : D →ₐ[R] D') :
    op (CommAlgCat.of R D') ⟶ op (CommAlgCat.of R D) := (CommAlgCat.ofHom f).op

variable {𝒜 N C} in
/-- The universal value `u = φ(X)` of an attractor point, in `C[N]`. -/
def AttractorPt.univ (φ : AttractorPt (gradedAction 𝒜) N (op (CommAlgCat.of R C))) :
    A →ₐ[R] AddMonoidAlgebra C N :=
  φ.app (T' := op (CommAlgCat.of R (AddMonoidAlgebra C N))) (affHom (constAlg N C))
    (AddMonoidAlgebra.of C N)

lemma comp_evalAlg {D D' : Type u} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D']
    (f : D →ₐ[R] D') (t : C →ₐ[R] D) (a : Multiplicative N →* D) :
    f.comp (evalAlg t a) = evalAlg (f.comp t) ((f : D →* D').comp a) := by
  refine AlgHom.ext fun x => ?_
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single n c => simp

lemma evalAlg_univ : evalAlg (constAlg N C) (AddMonoidAlgebra.of C N) = AlgHom.id R _ := by
  refine AlgHom.ext fun x => ?_
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, AlgHom.id_apply]
  | single n c => simp [constAlg_apply, AddMonoidAlgebra.of_apply,
      AddMonoidAlgebra.single_mul_single]

/-- The comultiplication-like map `C[N] → C[N][M]`, `X^n ↦ X^n ⊗ X^n`, used to read off degrees. -/
def diagUnit : Multiplicative N →* AddMonoidAlgebra (AddMonoidAlgebra C N) M where
  toFun n := AddMonoidAlgebra.single ((Multiplicative.toAdd n : N) : M)
    (AddMonoidAlgebra.single (Multiplicative.toAdd n) 1)
  map_one' := by
    simp [AddMonoidAlgebra.one_def]
  map_mul' x y := by
    simp [AddMonoidAlgebra.single_mul_single]

/-- The map `C[N] → C[N][M]`, `X^n ↦ X^n ⊗ X^n`. -/
def diagGrading : AddMonoidAlgebra C N →ₐ[R] AddMonoidAlgebra (AddMonoidAlgebra C N) M :=
  evalAlg ((constAlg M (AddMonoidAlgebra C N)).comp (constAlg N C)) (diagUnit N C)

lemma diag_single (n : N) (c : C) :
    diagGrading (R := R) (M := M) N C (AddMonoidAlgebra.single n c) =
      AddMonoidAlgebra.single (n : M) (AddMonoidAlgebra.single n c) := by
  simp [diagGrading, diagUnit, constAlg_apply, AddMonoidAlgebra.single_mul_single]

lemma coeff_coeff_diag (x : AddMonoidAlgebra C N) (n : N) :
    ((diagGrading (R := R) (M := M) N C x).coeff (n : M)).coeff n = x.coeff n := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hx, hy]
  | single k c =>
      rw [diag_single, AddMonoidAlgebra.coeff_single]
      by_cases h : k = n
      · subst h; simp
      · have h' : (k : M) ≠ n := fun e => h (Subtype.ext e)
        simp [Finsupp.single_eq_of_ne, h, h', Ne.symm h, Ne.symm h',
          AddMonoidAlgebra.coeff_single]

lemma diag_comp_const :
    (diagGrading (R := R) (M := M) N C).comp (constAlg N C) =
      (constAlg M (AddMonoidAlgebra C N)).comp (constAlg N C) := by
  refine AlgHom.ext fun c => ?_
  simp only [AlgHom.comp_apply, constAlg_apply, diag_single]
  rfl

variable {𝒜 N C}

/-- A point of the attractor is graded: this is where equivariance enters. -/
lemma AttractorPt.univ_mem (φ : AttractorPt (gradedAction 𝒜) N (op (CommAlgCat.of R C))) {m : M}
    {a : A} (ha : a ∈ 𝒜 m) : φ.univ a ∈ magnetGrading N C m := by
  let B := AddMonoidAlgebra C N
  let E := AddMonoidAlgebra B M
  let i : B →ₐ[R] E := constAlg M B
  let Δ : B →ₐ[R] E := diagGrading N C
  let X : Multiplicative N →* B := AddMonoidAlgebra.of C N
  let t₀ : op (CommAlgCat.of R B) ⟶ op (CommAlgCat.of R C) := affHom (constAlg N C)
  let t₁ : op (CommAlgCat.of R E) ⟶ op (CommAlgCat.of R C) := affHom (i.comp (constAlg N C))
  have h₁ : φ.app t₁ ((i : B →* E).comp X) = i.comp φ.univ := φ.naturality (affHom i) t₀ X
  have hΔ : affHom Δ ≫ t₀ = t₁ := by
    change (CommAlgCat.ofHom (Δ.comp (constAlg N C))).op = _
    rw [show Δ.comp (constAlg N C) = i.comp (constAlg N C) from diag_comp_const N C]
  have h₂ : φ.app t₁ ((Δ : B →* E).comp X) = Δ.comp φ.univ := by
    have := φ.naturality (affHom Δ) t₀ X
    rw [hΔ] at this
    exact this
  let hu : Multiplicative M →* E := AddMonoidAlgebra.of B M
  have hX : (Δ : B →* E).comp X = (hu.comp (AddMonoidHom.toMultiplicative N.subtype)) *
      (i : B →* E).comp X := by
    refine MonoidHom.ext fun n => ?_
    change Δ (AddMonoidAlgebra.single (Multiplicative.toAdd n) 1) =
      AddMonoidAlgebra.single ((Multiplicative.toAdd n : N) : M) 1 *
        AddMonoidAlgebra.single 0 (AddMonoidAlgebra.single (Multiplicative.toAdd n) 1)
    rw [show Δ (AddMonoidAlgebra.single (Multiplicative.toAdd n) 1) = _ from diag_single N C _ _,
      AddMonoidAlgebra.single_mul_single]
    simp
  have key : Δ.comp φ.univ = gradedSmul 𝒜 hu (i.comp φ.univ) := by
    rw [← h₂, hX, ← h₁]
    exact φ.equivariant t₁ hu _
  have hval : Δ (φ.univ a) = AddMonoidAlgebra.single m (φ.univ a) := by
    have := DFunLike.congr_fun key a
    rw [gradedSmul_apply_of_mem 𝒜 _ _ ha] at this
    refine this.trans ?_
    change AddMonoidAlgebra.single m 1 * AddMonoidAlgebra.single 0 (φ.univ a) = _
    rw [AddMonoidAlgebra.single_mul_single]
    simp
  intro n hn
  by_contra hne
  have hcoeff := coeff_coeff_diag (R := R) (M := M) N C (φ.univ a) n
  change ((Δ (φ.univ a)).coeff (n : M)).coeff n = _ at hcoeff
  have hne' : (n : M) ≠ m := hne
  rw [hval, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne hne'] at hcoeff
  exact (Finsupp.mem_support_iff.mp hn) (by simpa using hcoeff.symm)

/-- Equivariance of evaluation on homogeneous elements. -/
lemma evalAlg_mul_graded {D : Type u} [CommRing D] [Algebra R D] (t : C →ₐ[R] D)
    (h : Multiplicative M →* D) (a : Multiplicative N →* D) (g : Attractor 𝒜 N C) {m : M} {x : A}
    (hx : x ∈ 𝒜 m) :
    evalAlg t (h.comp (AddMonoidHom.toMultiplicative N.subtype) * a) (g x) =
      h (Multiplicative.ofAdd m) * evalAlg t a (g x) := by
  by_cases hm : m ∈ N
  · obtain ⟨c, hc⟩ := exists_single_of_mem_magnetGrading hm (g.map_mem hx)
    rw [hc, evalAlg_single, evalAlg_single]
    change t c * (h (Multiplicative.ofAdd m) * a _) = _
    ring
  · rw [attractor_apply_eq_zero_of_notMem g hm hx]
    simp

variable (𝒜 N C)

/-- A graded map `A → C[N]` defines a point of the attractor, by evaluating `C[N]` at points of
`𝔸(N)`. -/
def attractorPtOfGraded (g : Attractor 𝒜 N C) :
    AttractorPt (gradedAction 𝒜) N (op (CommAlgCat.of R C)) where
  app {T'} t a := (evalAlg (D := (unop T' : CommAlgCat.{u} R)) t.unop.hom a).comp g.toAlgHom
  naturality {T' T''} s t a := by
    exact congrArg (fun f => AlgHom.comp f g.toAlgHom)
      (comp_evalAlg (D := (unop T' : CommAlgCat.{u} R)) (D' := (unop T'' : CommAlgCat.{u} R))
        N C s.unop.hom t.unop.hom a).symm
  equivariant {T'} t h a := by
    refine algHom_ext_of_homogeneous (D := (unop T' : CommAlgCat.{u} R)) 𝒜 fun m x hx => ?_
    refine Eq.trans ?_ (gradedSmul_apply_of_mem (D := (unop T' : CommAlgCat.{u} R)) 𝒜 _ _ hx).symm
    exact evalAlg_mul_graded (D := (unop T' : CommAlgCat.{u} R)) t.unop.hom h a g hx

/-- **Comparison with the graded description.** For `S = Spec R` and `X = Spec A`, the points of the
attractor of Definition 3.1 are the graded maps `A → C[N]`. -/
def attractorPtEquiv :
    AttractorPt (gradedAction 𝒜) N (op (CommAlgCat.of R C)) ≃ Attractor 𝒜 N C where
  toFun φ :=
    { __ := φ.univ
      map_mem' := fun ha => φ.univ_mem ha }
  invFun := attractorPtOfGraded 𝒜 N C
  left_inv φ := by
    refine AttractorPt.ext ?_
    funext T' t a
    let ev : AddMonoidAlgebra C N →ₐ[R] (unop T' : CommAlgCat.{u} R) := evalAlg (D := (unop T' : CommAlgCat.{u} R)) t.unop.hom a
    let s : T' ⟶ op (CommAlgCat.of R (AddMonoidAlgebra C N)) :=
      (CommAlgCat.ofHom ev : CommAlgCat.of R (AddMonoidAlgebra C N) ⟶ CommAlgCat.of R (unop T' : CommAlgCat.{u} R)).op
    have hn := φ.naturality s (affHom (constAlg N C)) (AddMonoidAlgebra.of C N)
    have e₁ : s ≫ affHom (constAlg N C) = t := by
      refine Quiver.Hom.unop_inj (CommAlgCat.hom_ext (AlgHom.ext fun c => ?_))
      change ev (AddMonoidAlgebra.single 0 c) = t.unop.hom c
      rw [show ev (AddMonoidAlgebra.single 0 c) = _ from evalAlg_single (R := R) (D := (unop T' : CommAlgCat.{u} R)) N C t.unop.hom a 0 c]
      simp only [ofAdd_zero]
      exact (congrArg _ (map_one a)).trans (mul_one (M := (unop T' : CommAlgCat.{u} R)) _)
    have e₂ : APt.res (𝒪 := affO R) s.op (AddMonoidAlgebra.of C N) = a := by
      refine MonoidHom.ext fun n => ?_
      change ev (AddMonoidAlgebra.single (Multiplicative.toAdd n) 1) = a n
      rw [show ev (AddMonoidAlgebra.single (Multiplicative.toAdd n) 1) = _ from
        evalAlg_single (R := R) (D := (unop T' : CommAlgCat.{u} R)) N C t.unop.hom a (Multiplicative.toAdd n) 1]
      simp
      rfl
    rw [e₁, e₂] at hn
    exact hn.symm
  right_inv g := by
    refine GradedAlgHom.ext fun a => ?_
    change (evalAlg (constAlg N C) (AddMonoidAlgebra.of C N)) (g a) = g a
    rw [evalAlg_univ]
    rfl

/-- The attractor of Definition 3.1 is represented by `Spec (A / J_N)` (Theorem 3.20, affine
case). -/
def attractorPtEquivQuotient :
    AttractorPt (gradedAction 𝒜) N (op (CommAlgCat.of R C)) ≃
      ((A ⧸ magnetIdeal 𝒜 N) →ₐ[R] C) :=
  (attractorPtEquiv 𝒜 N C).trans (attractorEquiv 𝒜 N C).symm

end Comparison

end AlgMag
