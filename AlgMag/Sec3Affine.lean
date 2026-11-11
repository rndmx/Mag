/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.GroupTheory.QuotientGroup.Defs
import AlgMag.Affine.Naturality

/-!
# Section 3 of *Algebraic Magnetism*: the affine, graded-algebra content

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026), §3, in the case `S = Spec R₀`,
`X = Spec A`, where the action of `𝔸(M)_S` is an `M`-grading `𝒜` of `A` (Proposition 2.22).
Everything rests on `Magnetism.magnetIdeal` (the ideal `J_N`) and `Magnetism.attractorEquiv`
(Theorem 3.20). A closed subscheme of `Spec A` is expressed by a surjection of algebras out of
`A`, and an identification of attractors by a bijection on `C`-points, natural in `C` or
compatible with the underlying point of `X`.

## Main results

* `AlgMag.magnetIdeal_anti`, `AlgMag.magnetQuotMap`, `AlgMag.attractorIncl_attractorEquiv`:
  Corollary 3.22.
* `AlgMag.magnetIdeal_iInf`, `AlgMag.attractorIInfEquiv`: Proposition 3.24.
* `AlgMag.magnetIdeal_map_quotient`, `AlgMag.comap_magnetIdeal_quotient`: Lemma 3.26.
* `AlgMag.IsFaceGr`, `AlgMag.faceProjGr`, `AlgMag.attractorFaceProj`, `AlgMag.faceSection`:
  Fact 3.15, with the face condition of Proposition 2.16.
* `AlgMag.pushGrading`, `AlgMag.magnetIdeal_pushGrading`, `AlgMag.attractorPushEquiv`:
  Proposition 3.31 (i).
* `AlgMag.comap_magnetIdeal_inf`: Proposition 3.32 (i).
* `AlgMag.magnetIdeal_eq_of_forall_eq`: Fact 3.34 (i).
* `AlgMag.IsFixedPoint`, `AlgMag.attractorFixedEquiv`, `AlgMag.magnetIdeal_quotientGrading`:
  Proposition 3.35.
-/

suppress_compilation

set_option linter.unusedSectionVars false

open Magnetism DirectSum

open scoped Classical

namespace AlgMag

variable {M : Type*} [AddCommMonoid M]
variable {R₀ A : Type*} [CommRing R₀] [CommRing A] [Algebra R₀ A]

section Ideals

variable (𝒜 : M → Submodule R₀ A)

/-- **Corollary 3.22**, ideal form: if `N ⊆ L` then `J_L ⊆ J_N`. -/
lemma magnetIdeal_anti {N L : Magnet M} (h : N ≤ L) : magnetIdeal 𝒜 L ≤ magnetIdeal 𝒜 N :=
  Ideal.span_mono <| by
    simp only [Set.iUnion_subset_iff]
    intro m hm a ha
    simp only [Set.mem_iUnion]
    exact ⟨m, fun hN => hm (h hN), ha⟩

/-- Fact 3.6, ideal form: `J_M = 0`. -/
lemma magnetIdeal_top : magnetIdeal 𝒜 (⊤ : Magnet M) = ⊥ := by
  simp [magnetIdeal]

/-- **Proposition 3.24**, ideal form: `J_{⋂ N_i} = ∑ J_{N_i}`. -/
lemma magnetIdeal_iInf {ι : Sort*} (N : ι → Magnet M) :
    magnetIdeal 𝒜 (⨅ i, N i) = ⨆ i, magnetIdeal 𝒜 (N i) := by
  refine le_antisymm ?_ (iSup_le fun i => magnetIdeal_anti 𝒜 (iInf_le N i))
  rw [magnetIdeal, Ideal.span_le]
  simp only [Set.iUnion_subset_iff]
  intro m hm a ha
  simp only [AddSubmonoid.mem_iInf, not_forall] at hm
  obtain ⟨i, hi⟩ := hm
  exact Ideal.mem_iSup_of_mem i (mem_magnetIdeal_of_notMem hi ha)

/-- **Proposition 3.24** for two magnets, ideal form: `J_{N ∩ L} = J_N + J_L`. -/
lemma magnetIdeal_inf (N L : Magnet M) :
    magnetIdeal 𝒜 (N ⊓ L) = magnetIdeal 𝒜 N ⊔ magnetIdeal 𝒜 L := by
  refine le_antisymm ?_ (sup_le (magnetIdeal_anti 𝒜 inf_le_left) (magnetIdeal_anti 𝒜 inf_le_right))
  rw [magnetIdeal, Ideal.span_le]
  simp only [Set.iUnion_subset_iff]
  intro m hm a ha
  by_cases hN : m ∈ N
  · have hL : m ∉ L := fun hL => hm ⟨hN, hL⟩
    exact Ideal.mem_sup_right (mem_magnetIdeal_of_notMem hL ha)
  · exact Ideal.mem_sup_left (mem_magnetIdeal_of_notMem hN ha)

/-- **Fact 3.34 (i)**, ideal form: if all the `J_{N_i}` coincide (`X^{N_i} = X^{N_j}`), then they
equal `J_{⋂ N_i}`. -/
lemma magnetIdeal_eq_of_forall_eq {ι : Sort*} (N : ι → Magnet M)
    (h : ∀ i j, magnetIdeal 𝒜 (N i) = magnetIdeal 𝒜 (N j)) (i : ι) :
    magnetIdeal 𝒜 (N i) = magnetIdeal 𝒜 (⨅ j, N j) := by
  rw [magnetIdeal_iInf]
  exact le_antisymm (le_iSup (fun j => magnetIdeal 𝒜 (N j)) i)
    (iSup_le fun j => (h j i).le)

/-- **Lemma 3.26**, ideal form. Let `I ⊆ A` be an ideal (homogeneous when `Z = Spec (A / I)` is an
equivariant closed subscheme of `Y = Spec A`), and give `A / I` the image grading. Then the ideal
of `A / I` defining `Z^N` is the image of `J_N`. -/
lemma magnetIdeal_map_quotient (I : Ideal A) (N : Magnet M) :
    magnetIdeal (fun m => (𝒜 m).map (Ideal.Quotient.mkₐ R₀ I).toLinearMap) N =
      (magnetIdeal 𝒜 N).map (Ideal.Quotient.mk I) := by
  rw [magnetIdeal, magnetIdeal, Ideal.map_span]
  congr 1
  ext x
  simp only [Set.mem_iUnion, Set.mem_image, SetLike.mem_coe, Submodule.mem_map]
  constructor
  · rintro ⟨m, hm, a, ha, rfl⟩
    exact ⟨a, ⟨m, hm, ha⟩, rfl⟩
  · rintro ⟨a, ⟨m, hm, ha⟩, rfl⟩
    exact ⟨m, hm, a, ha, rfl⟩

/-- **Lemma 3.26**: the ideal of `A` defining `Z^N` is `I + J_N`, i.e. `Z^N = Z ×_Y Y^N`. -/
lemma comap_magnetIdeal_quotient (I : Ideal A) (N : Magnet M) :
    (magnetIdeal (fun m => (𝒜 m).map (Ideal.Quotient.mkₐ R₀ I).toLinearMap) N).comap
      (Ideal.Quotient.mk I) = I ⊔ magnetIdeal 𝒜 N := by
  rw [magnetIdeal_map_quotient, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_comm]

/-- **Proposition 3.32 (i)**, ideal form: `(X^N)^L = X^{N ∩ L}`. The ideal of `A` defining
`(X^N)^L`, computed in `A / J_N` with its image grading, is `J_{N ∩ L}`. -/
lemma comap_magnetIdeal_inf (N L : Magnet M) :
    (magnetIdeal (fun m => (𝒜 m).map (Ideal.Quotient.mkₐ R₀ (magnetIdeal 𝒜 N)).toLinearMap) L).comap
      (Ideal.Quotient.mk (magnetIdeal 𝒜 N)) = magnetIdeal 𝒜 (N ⊓ L) := by
  rw [comap_magnetIdeal_quotient, magnetIdeal_inf]

variable {𝒜} in
/-- A map out of `A` kills `J_N` as soon as it kills the components of degree outside `N`. -/
lemma map_eq_zero_of_mem_magnetIdeal {C : Type*} [CommRing C] [Algebra R₀ C] {N : Magnet M}
    (g : A →ₐ[R₀] C) (hg : ∀ m, m ∉ N → ∀ a ∈ 𝒜 m, g a = 0) {a : A}
    (ha : a ∈ magnetIdeal 𝒜 N) : g a = 0 := by
  have hle : magnetIdeal 𝒜 N ≤ RingHom.ker (g : A →+* C) := by
    rw [magnetIdeal, Ideal.span_le]
    simp only [Set.iUnion_subset_iff]
    intro m hm x hx
    exact hg m hm x hx
  exact hle ha

end Ideals

section Closed

variable (𝒜 : M → Submodule R₀ A)

/-- **Corollary 3.22**: the algebra map `A / J_L → A / J_N` for magnets `N ⊆ L`. It is surjective
(`magnetQuotMap_surjective`): this is the closed immersion `X^N → X^L`. -/
def magnetQuotMap {N L : Magnet M} (h : N ≤ L) :
    (A ⧸ magnetIdeal 𝒜 L) →ₐ[R₀] (A ⧸ magnetIdeal 𝒜 N) :=
  Ideal.Quotient.factorₐ R₀ (magnetIdeal_anti 𝒜 h)

@[simp] lemma magnetQuotMap_mk {N L : Magnet M} (h : N ≤ L) (a : A) :
    magnetQuotMap 𝒜 h (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ a := rfl

/-- **Corollary 3.22**: `A / J_L → A / J_N` is surjective. -/
lemma magnetQuotMap_surjective {N L : Magnet M} (h : N ≤ L) :
    Function.Surjective (magnetQuotMap 𝒜 h) := by
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨Ideal.Quotient.mk _ a, rfl⟩

end Closed

variable [DecidableEq M]
variable {𝒜 : M → Submodule R₀ A} [GradedAlgebra 𝒜]
variable {C : Type*} [CommRing C] [Algebra R₀ C]

section Points

variable (𝒜) in
/-- The point of `X = Spec A` underlying a point of `X^N`: the morphism `X^N → X`
(unit section of `𝔸(N)`), i.e. `A → C[N] → C`. -/
abbrev attractorPoint {N : Magnet M} (f : Attractor 𝒜 N C) : A →ₐ[R₀] C := psiAux f

lemma attractorPoint_attractorEquiv {N : Magnet M} (F : (A ⧸ magnetIdeal 𝒜 N) →ₐ[R₀] C) (a : A) :
    attractorPoint 𝒜 (attractorEquiv 𝒜 N C F) a = F (Ideal.Quotient.mk _ a) := by
  have := congrArg (fun G => G (Ideal.Quotient.mk _ a)) (psi_theta F)
  exact this

variable (𝒜 C) in
/-- Theorem 3.20 in terms of `X`: `X^N(C)` is the set of points of `X(C)` vanishing on `J_N`, the
bijection being `f ↦` its underlying point. In particular `X^N → X` is a monomorphism. -/
def attractorPointsEquiv (N : Magnet M) :
    Attractor 𝒜 N C ≃ {g : A →ₐ[R₀] C // ∀ a ∈ magnetIdeal 𝒜 N, g a = 0} where
  toFun f := ⟨attractorPoint 𝒜 f, fun _ ha => psiAux_eq_zero_of_mem_magnetIdeal f ha⟩
  invFun g := attractorEquiv 𝒜 N C (Ideal.Quotient.liftₐ _ g.1 g.2)
  left_inv f := theta_psi f
  right_inv g := by
    refine Subtype.ext (AlgHom.ext fun a => ?_)
    exact attractorPoint_attractorEquiv (Ideal.Quotient.liftₐ _ g.1 g.2) a

lemma attractorPoint_injective {N : Magnet M} :
    Function.Injective (attractorPoint 𝒜 (N := N) (C := C)) := fun _ _ h =>
  (attractorPointsEquiv 𝒜 C N).injective (Subtype.ext h)

/-- A point of `X` comes from `X^N` iff it kills the components of degree outside `N`. -/
lemma exists_attractorPoint_eq_iff {N : Magnet M} (g : A →ₐ[R₀] C) :
    (∃ f : Attractor 𝒜 N C, attractorPoint 𝒜 f = g) ↔ ∀ m, m ∉ N → ∀ a ∈ 𝒜 m, g a = 0 := by
  constructor
  · rintro ⟨f, rfl⟩ m hm a ha
    exact psiAux_eq_zero_of_mem_magnetIdeal f (mem_magnetIdeal_of_notMem hm ha)
  · intro h
    exact ⟨(attractorPointsEquiv 𝒜 C N).symm ⟨g, fun _ ha => map_eq_zero_of_mem_magnetIdeal g h ha⟩,
      congrArg Subtype.val ((attractorPointsEquiv 𝒜 C N).apply_symm_apply _)⟩

end Points

section Inclusion

variable {N L : Magnet M}

/-- The map `C[N] → C[L]` induced by an inclusion of magnets `N ⊆ L`. -/
def magnetIncl (h : N ≤ L) (C : Type*) [CommRing C] :
    AddMonoidAlgebra C N →ₐ[C] AddMonoidAlgebra C L :=
  AddMonoidAlgebra.lift C (AddMonoidAlgebra C L) N
    { toFun := fun n => AddMonoidAlgebra.single (AddSubmonoid.inclusion h (Multiplicative.toAdd n)) 1
      map_one' := rfl
      map_mul' := fun x y => by
        rw [AddMonoidAlgebra.single_mul_single, mul_one]
        rfl }

@[simp] lemma magnetIncl_single (h : N ≤ L) (n : N) (c : C) :
    magnetIncl h C (AddMonoidAlgebra.single n c) =
      AddMonoidAlgebra.single (AddSubmonoid.inclusion h n) c := by
  simp only [magnetIncl, AddMonoidAlgebra.lift_single]
  change c • (AddMonoidAlgebra.single (AddSubmonoid.inclusion h n) (1 : C)) = _
  rw [AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one]

/-- The morphism of functors `X^N → X^L` for magnets `N ⊆ L` (§3): a point `A → C[N]` is sent to
`A → C[N] → C[L]`. -/
def attractorIncl (h : N ≤ L) (f : Attractor 𝒜 N C) : Attractor 𝒜 L C where
  __ := ((magnetIncl h C).restrictScalars R₀).comp f.toAlgHom
  map_mem' {m a} ha := by
    show magnetIncl h C (f a) ∈ magnetGrading L C m
    by_cases hm : m ∈ N
    · obtain ⟨c, hc⟩ := exists_single_of_mem_magnetGrading hm (f.map_mem ha)
      rw [hc, magnetIncl_single]
      exact single_mem_magnetGrading (AddSubmonoid.inclusion h ⟨m, hm⟩) c
    · rw [attractor_apply_eq_zero_of_notMem f hm ha, map_zero]
      exact zero_mem _

@[simp] lemma attractorIncl_apply (h : N ≤ L) (f : Attractor 𝒜 N C) (a : A) :
    attractorIncl h f a = magnetIncl h C (f a) := rfl

lemma magnetAug_magnetIncl (h : N ≤ L) (x : AddMonoidAlgebra C N) :
    magnetAug L C (magnetIncl h C x) = magnetAug N C x := by
  have : (magnetAug L C).comp (magnetIncl h C) = magnetAug N C := by
    ext n
    simp
  exact congrArg (fun φ => φ x) this

/-- `X^N → X^L` is compatible with the maps to `X`. -/
@[simp] lemma attractorPoint_attractorIncl (h : N ≤ L) (f : Attractor 𝒜 N C) :
    attractorPoint 𝒜 (attractorIncl h f) = attractorPoint 𝒜 f :=
  AlgHom.ext fun a => magnetAug_magnetIncl h (f a)

/-- **Corollary 3.22.** Through the identifications of Theorem 3.20, the morphism `X^N → X^L` is
`Spec` of the surjection `A / J_L → A / J_N`; hence it is a closed immersion. -/
theorem attractorIncl_attractorEquiv (h : N ≤ L) (F : (A ⧸ magnetIdeal 𝒜 N) →ₐ[R₀] C) :
    attractorEquiv 𝒜 L C (F.comp (magnetQuotMap 𝒜 h)) =
      attractorIncl h (attractorEquiv 𝒜 N C F) := by
  apply attractorPoint_injective
  refine AlgHom.ext fun a => ?_
  rw [attractorPoint_attractorEquiv, attractorPoint_attractorIncl, attractorPoint_attractorEquiv]
  rfl

/-- §3: `X^N → X^L` is a monomorphism in the affine case. -/
lemma attractorIncl_injective (h : N ≤ L) :
    Function.Injective (attractorIncl (𝒜 := 𝒜) (C := C) h) := fun f f' e => by
  apply attractorPoint_injective
  rw [← attractorPoint_attractorIncl h f, ← attractorPoint_attractorIncl h f', e]

end Inclusion

section Intersection

variable {ι : Sort*} (N : ι → Magnet M)

/-- **Proposition 3.24**, on points: a `C`-point of `X^{⋂ N_i}` is a `C`-point of `X` which lies
in every `X^{N_i}`. This is the equality `X^{⋂ N_i} = ⋂ X^{N_i}` (intersection, equivalently fibre
product, of the closed subschemes `X^{N_i}` over `X`), for an arbitrary family. -/
def attractorIInfEquiv :
    Attractor 𝒜 (⨅ i, N i) C ≃
      {g : A →ₐ[R₀] C // ∀ i, ∃ f : Attractor 𝒜 (N i) C, attractorPoint 𝒜 f = g} :=
  Equiv.ofBijective
    (fun f => ⟨attractorPoint 𝒜 f, fun i =>
      ⟨attractorIncl (iInf_le N i) f, attractorPoint_attractorIncl _ _⟩⟩)
    ⟨fun _ _ h => attractorPoint_injective (congrArg Subtype.val h), fun g => by
      obtain ⟨f, hf⟩ := (exists_attractorPoint_eq_iff (𝒜 := 𝒜) (N := ⨅ i, N i) g.1).2
        fun m hm a ha => by
          simp only [AddSubmonoid.mem_iInf, not_forall] at hm
          obtain ⟨i, hi⟩ := hm
          exact (exists_attractorPoint_eq_iff g.1).1 (g.2 i) m hi a ha
      exact ⟨f, Subtype.ext hf⟩⟩

end Intersection

section Face

/-- `F` is a face of the magnet `N` (Definition 2.14), in the form of the characterization of
Proposition 2.16: `F ⊆ N` and, for `x, y ∈ N`, `x + y ∈ F ↔ x ∈ F ∧ y ∈ F`. (The implication `←`
holds automatically.) -/
structure IsFaceGr (F N : Magnet M) : Prop where
  le : F ≤ N
  mem_of_add_mem : ∀ {x y : M}, x ∈ N → y ∈ N → x + y ∈ F → x ∈ F ∧ y ∈ F

variable {F N : Magnet M}

/-- The monoid map behind the projection `C[N] → C[F]`. -/
def faceProjGrHom (hF : IsFaceGr F N) (C : Type*) [CommRing C] :
    Multiplicative N →* AddMonoidAlgebra C F where
  toFun n := if h : (Multiplicative.toAdd n : N).1 ∈ F then AddMonoidAlgebra.single ⟨_, h⟩ 1 else 0
  map_one' := by
    have h0 : ((Multiplicative.toAdd (1 : Multiplicative N) : N) : M) ∈ F := F.zero_mem
    simp only [h0, ↓reduceDIte]
    rfl
  map_mul' x y := by
    by_cases hx : (Multiplicative.toAdd x : N).1 ∈ F
    · by_cases hy : (Multiplicative.toAdd y : N).1 ∈ F
      · have hxy : (Multiplicative.toAdd (x * y) : N).1 ∈ F := F.add_mem hx hy
        simp only [hx, hy, hxy, ↓reduceDIte, AddMonoidAlgebra.single_mul_single, mul_one]
        rfl
      · have hxy : (Multiplicative.toAdd (x * y) : N).1 ∉ F := fun h =>
          hy (hF.mem_of_add_mem (Multiplicative.toAdd x).2 (Multiplicative.toAdd y).2 h).2
        simp only [hy, hxy, ↓reduceDIte, mul_zero]
    · have hxy : (Multiplicative.toAdd (x * y) : N).1 ∉ F := fun h =>
        hx (hF.mem_of_add_mem (Multiplicative.toAdd x).2 (Multiplicative.toAdd y).2 h).1
      simp only [hx, hxy, ↓reduceDIte, zero_mul]

/-- **Definition 2.14 / Proposition 2.16**: for a face `F` of `N`, the projection `C[N] → C[F]`,
`X^n ↦ X^n` for `n ∈ F` and `X^n ↦ 0` otherwise, is a morphism of algebras. -/
def faceProjGr (hF : IsFaceGr F N) (C : Type*) [CommRing C] :
    AddMonoidAlgebra C N →ₐ[C] AddMonoidAlgebra C F :=
  AddMonoidAlgebra.lift C (AddMonoidAlgebra C F) N (faceProjGrHom hF C)

lemma faceProjGr_single_of_mem (hF : IsFaceGr F N) (n : N) (h : (n : M) ∈ F) (c : C) :
    faceProjGr hF C (AddMonoidAlgebra.single n c) = AddMonoidAlgebra.single ⟨n, h⟩ c := by
  simp [faceProjGr, faceProjGrHom, AddMonoidAlgebra.lift_single, h, AddMonoidAlgebra.smul_single]

lemma faceProjGr_single_of_notMem (hF : IsFaceGr F N) (n : N) (h : (n : M) ∉ F) (c : C) :
    faceProjGr hF C (AddMonoidAlgebra.single n c) = 0 := by
  simp [faceProjGr, faceProjGrHom, AddMonoidAlgebra.lift_single, h]

/-- **Fact 3.15**: the morphism `p_{N,F} : X^N → X^F` attached to a face `F` of `N`. -/
def attractorFaceProj (hF : IsFaceGr F N) (f : Attractor 𝒜 N C) : Attractor 𝒜 F C where
  __ := ((faceProjGr hF C).restrictScalars R₀).comp f.toAlgHom
  map_mem' {m a} ha := by
    show faceProjGr hF C (f a) ∈ magnetGrading F C m
    by_cases hm : m ∈ N
    · obtain ⟨c, hc⟩ := exists_single_of_mem_magnetGrading hm (f.map_mem ha)
      rw [hc]
      by_cases hmF : m ∈ F
      · rw [faceProjGr_single_of_mem hF ⟨m, hm⟩ hmF]
        exact single_mem_magnetGrading (⟨m, hmF⟩ : F) c
      · rw [faceProjGr_single_of_notMem hF ⟨m, hm⟩ hmF]
        exact zero_mem _
    · rw [attractor_apply_eq_zero_of_notMem f hm ha, map_zero]
      exact zero_mem _

@[simp] lemma attractorFaceProj_apply (hF : IsFaceGr F N) (f : Attractor 𝒜 N C) (a : A) :
    attractorFaceProj hF f a = faceProjGr hF C (f a) := rfl

lemma faceProjGr_magnetIncl (hF : IsFaceGr F N) (x : AddMonoidAlgebra C F) :
    faceProjGr hF C (magnetIncl hF.le C x) = x := by
  have : (faceProjGr hF C).comp (magnetIncl hF.le C) = AlgHom.id C _ := by
    ext n k
    show (faceProjGr hF C (magnetIncl hF.le C (AddMonoidAlgebra.single n 1))).coeff k =
      (AddMonoidAlgebra.single n (1 : C)).coeff k
    rw [magnetIncl_single, faceProjGr_single_of_mem hF _ n.2]
    rfl
  exact congrArg (fun φ => φ x) this

/-- **Fact 3.15**: `p_{N,F} ∘ ι_{F,N} = Id_{X^F}`. -/
theorem attractorFaceProj_attractorIncl (hF : IsFaceGr F N) (f : Attractor 𝒜 F C) :
    attractorFaceProj hF (attractorIncl hF.le f) = f :=
  GradedAlgHom.ext fun a => faceProjGr_magnetIncl hF (f a)

/-- `p_{N,F}` is natural in `C`. -/
lemma attractorFaceProj_map {C' : Type*} [CommRing C'] [Algebra R₀ C'] (hF : IsFaceGr F N)
    (g : C →ₐ[R₀] C') (f : Attractor 𝒜 N C) :
    attractorFaceProj hF (Attractor.map N g f) = Attractor.map F g (attractorFaceProj hF f) := by
  refine GradedAlgHom.ext fun a => ?_
  show faceProjGr hF C' (magnetMap N g (f a)) = magnetMap F g (faceProjGr hF C (f a))
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous m x =>
      by_cases hm : m ∈ N
      · obtain ⟨c, hc⟩ := exists_single_of_mem_magnetGrading hm (f.map_mem x.2)
        rw [hc, magnetMap_single]
        by_cases hmF : m ∈ F
        · rw [faceProjGr_single_of_mem hF ⟨m, hm⟩ hmF, faceProjGr_single_of_mem hF ⟨m, hm⟩ hmF,
            magnetMap_single]
        · rw [faceProjGr_single_of_notMem hF ⟨m, hm⟩ hmF, faceProjGr_single_of_notMem hF ⟨m, hm⟩ hmF,
            map_zero]
      · rw [attractor_apply_eq_zero_of_notMem f hm x.2]
        simp
  | add a a' ha ha' => simp only [map_add] at ha ha' ⊢; rw [ha, ha']

variable (𝒜) in
/-- **Fact 3.15**, on algebras: `p_{N,F}` is `Spec` of this algebra map `A / J_F → A / J_N`. -/
def faceSection (hF : IsFaceGr F N) : (A ⧸ magnetIdeal 𝒜 F) →ₐ[R₀] (A ⧸ magnetIdeal 𝒜 N) :=
  (attractorEquiv 𝒜 F _).symm
    (attractorFaceProj hF (attractorEquiv 𝒜 N _ (AlgHom.id R₀ (A ⧸ magnetIdeal 𝒜 N))))

/-- **Fact 3.15** (affine case): `A / J_N → A / J_F` is split by `faceSection`, which is the
identity `p_{N,F} ∘ ι_{F,N} = Id` on algebras. -/
theorem magnetQuotMap_comp_faceSection (hF : IsFaceGr F N) :
    (magnetQuotMap 𝒜 hF.le).comp (faceSection 𝒜 hF) = AlgHom.id R₀ _ := by
  apply (attractorEquiv 𝒜 F _).injective
  rw [attractorEquiv_naturality, faceSection, Equiv.apply_symm_apply, ← attractorFaceProj_map,
    ← attractorEquiv_naturality, AlgHom.comp_id]
  have := attractorIncl_attractorEquiv (𝒜 := 𝒜) hF.le (AlgHom.id R₀ (A ⧸ magnetIdeal 𝒜 F))
  rw [AlgHom.id_comp] at this
  rw [this, attractorFaceProj_attractorIncl]

end Face

section Push

variable {Z : Type*} [AddCommMonoid Z] [DecidableEq Z]

variable (𝒜) in
/-- The `Z`-grading on `A` induced by `f : M → Z`, `A_z = ⨁_{f m = z} A_m`: the grading of the
action of `𝔸(Z)_S` through `𝔸(Z)_S → 𝔸(M)_S` (Proposition 3.31). -/
def pushGrading (f : M →+ Z) (z : Z) : Submodule R₀ A := ⨆ m : {m // f m = z}, 𝒜 m.1

lemma le_pushGrading (f : M →+ Z) (m : M) : 𝒜 m ≤ pushGrading 𝒜 f (f m) :=
  le_iSup (fun m' : {m' // f m' = f m} => 𝒜 m'.1) ⟨m, rfl⟩

/-- Regrouping the components of `⨁ A_m` along `f`. -/
def pushDecomposeAux (f : M →+ Z) : (⨁ m, 𝒜 m) →+ ⨁ z, pushGrading 𝒜 f z :=
  DirectSum.toAddMonoid fun m =>
    (DirectSum.of (fun z => pushGrading 𝒜 f z) (f m)).comp
      (Submodule.inclusion (le_pushGrading (𝒜 := 𝒜) f m)).toAddMonoidHom

/-- The decomposition map for `pushGrading`. -/
def pushDecompose (f : M →+ Z) : A →+ ⨁ z, pushGrading 𝒜 f z :=
  (pushDecomposeAux f).comp (DirectSum.decomposeAddEquiv 𝒜).toAddMonoidHom

lemma pushDecompose_of_mem (f : M →+ Z) {m : M} {a : A} (ha : a ∈ 𝒜 m) :
    pushDecompose (𝒜 := 𝒜) f a =
      DirectSum.of (fun z => pushGrading 𝒜 f z) (f m) ⟨a, le_pushGrading f m ha⟩ := by
  have : DirectSum.decompose 𝒜 a = DirectSum.of (fun i => 𝒜 i) m ⟨a, ha⟩ :=
    DirectSum.decompose_of_mem 𝒜 ha
  show pushDecomposeAux f (DirectSum.decompose 𝒜 a) = _
  rw [this, pushDecomposeAux, DirectSum.toAddMonoid_of]
  rfl

lemma pushGrading_induction {f : M →+ Z} {z : Z} {motive : A → Prop} {x : A}
    (hx : x ∈ pushGrading 𝒜 f z) (mem : ∀ m, f m = z → ∀ a ∈ 𝒜 m, motive a) (zero : motive 0)
    (add : ∀ a b, motive a → motive b → motive (a + b)) : motive x :=
  Submodule.iSup_induction (fun m : {m // f m = z} => 𝒜 m.1) (motive := motive) hx
    (fun m a ha => mem m.1 m.2 a ha) zero add

instance pushGradedAlgebra (f : M →+ Z) : GradedAlgebra (pushGrading 𝒜 f) where
  one_mem := by
    have := le_pushGrading (𝒜 := 𝒜) f 0 (SetLike.GradedOne.one_mem)
    rwa [map_zero] at this
  mul_mem := by
    intro i j x y hx hy
    refine pushGrading_induction (motive := fun x => x * y ∈ pushGrading 𝒜 f (i + j)) hx
      (fun m hm a ha => ?_) (by simp) (fun a b h h' => by rw [add_mul]; exact add_mem h h')
    refine pushGrading_induction (motive := fun y => a * y ∈ pushGrading 𝒜 f (i + j)) hy
      (fun n hn b hb => ?_) (by simp) (fun c d h h' => by rw [mul_add]; exact add_mem h h')
    have := le_pushGrading (𝒜 := 𝒜) f (m + n) (SetLike.GradedMul.mul_mem ha hb)
    rwa [map_add, hm, hn] at this
  toDecomposition := DirectSum.Decomposition.ofAddHom _ (pushDecompose f)
    (by
      ext a
      show DirectSum.coeAddMonoidHom _ (pushDecompose f a) = a
      induction a using DirectSum.Decomposition.inductionOn 𝒜 with
      | zero => simp
      | @homogeneous m x =>
          rw [pushDecompose_of_mem f x.2, DirectSum.coeAddMonoidHom_of]
      | add a a' ha ha' => rw [map_add, map_add, ha, ha'])
    (by
      refine DirectSum.addHom_ext fun z ⟨x, hx⟩ => ?_
      show pushDecompose f (DirectSum.coeAddMonoidHom _ (DirectSum.of _ z ⟨x, hx⟩)) = _
      rw [DirectSum.coeAddMonoidHom_of]
      have key : ∃ h : x ∈ pushGrading 𝒜 f z, pushDecompose (𝒜 := 𝒜) f x =
          DirectSum.of (fun z => pushGrading 𝒜 f z) z ⟨x, h⟩ := by
        refine pushGrading_induction (motive := fun x => ∃ h : x ∈ pushGrading 𝒜 f z,
          pushDecompose (𝒜 := 𝒜) f x = DirectSum.of (fun z => pushGrading 𝒜 f z) z ⟨x, h⟩) hx
          (fun m hm a ha => ?_) ?_ ?_
        · subst hm
          exact ⟨le_pushGrading f m ha, pushDecompose_of_mem f ha⟩
        · refine ⟨zero_mem _, ?_⟩
          rw [map_zero]
          exact (map_zero (DirectSum.of (fun z => pushGrading 𝒜 f z) z)).symm
        · rintro a b ⟨h1, e1⟩ ⟨h2, e2⟩
          refine ⟨add_mem h1 h2, ?_⟩
          rw [map_add, e1, e2, ← map_add]
          rfl
      obtain ⟨_, e⟩ := key
      exact e)

/-- **Proposition 3.31 (i)**, ideal form. For `f : M → Z`, `Y` a magnet of `Z` and `N = f⁻¹(Y)`,
the ideal defining `X^Y` for the `Z`-grading equals the ideal defining `X^N` for the `M`-grading. -/
theorem magnetIdeal_pushGrading (f : M →+ Z) (Y : Magnet Z) :
    magnetIdeal (pushGrading 𝒜 f) Y = magnetIdeal 𝒜 (Y.comap f) := by
  apply le_antisymm
  · rw [magnetIdeal, Ideal.span_le]
    simp only [Set.iUnion_subset_iff]
    intro z hz x hx
    have hle : pushGrading 𝒜 f z ≤ (magnetIdeal 𝒜 (Y.comap f)).restrictScalars R₀ :=
      iSup_le fun m => magnetIdeal_le_of_notMem (m := m.1) (by
        simpa [AddSubmonoid.mem_comap, m.2] using hz)
    exact hle hx
  · rw [magnetIdeal, Ideal.span_le]
    simp only [Set.iUnion_subset_iff]
    intro m hm x hx
    exact mem_magnetIdeal_of_notMem (m := f m) hm (le_pushGrading f m hx)

/-- **Proposition 3.31 (i)**: the identification `X^{f⁻¹(Y)}_M = X^Y_Z` on points. -/
def attractorPushEquiv (f : M →+ Z) (Y : Magnet Z) :
    Attractor 𝒜 (Y.comap f) C ≃ Attractor (pushGrading 𝒜 f) Y C :=
  (attractorPointsEquiv 𝒜 C (Y.comap f)).trans
    ((Equiv.subtypeEquivRight fun g => by rw [magnetIdeal_pushGrading]).trans
      (attractorPointsEquiv (pushGrading 𝒜 f) C Y).symm)

/-- The identification of Proposition 3.31 (i) is compatible with the maps to `X`. -/
@[simp] lemma attractorPoint_attractorPushEquiv (f : M →+ Z) (Y : Magnet Z)
    (x : Attractor 𝒜 (Y.comap f) C) :
    attractorPoint (pushGrading 𝒜 f) (attractorPushEquiv f Y x) = attractorPoint 𝒜 x :=
  congrArg Subtype.val ((attractorPointsEquiv (pushGrading 𝒜 f) C Y).apply_symm_apply _)

end Push

section Fixed

variable {G : Type*} [AddCommGroup G] [DecidableEq G]
variable {𝒢 : G → Submodule R₀ A} [GradedAlgebra 𝒢] (Z : AddSubgroup G)

variable (𝒢) in
/-- A point `g : A → C` of `X = Spec A` is **fixed by `D(M/Z)`**: the coaction
`A → C[M/Z]`, `a ↦ g a · X^{[m]}` for `a ∈ A_m`, agrees with the trivial one
`a ↦ g a · X^0`. By `IsFixedPoint.character` and `isFixedPoint_of_character` this is the
functor-of-points definition of `X^{D(M/Z)}`. -/
def IsFixedPoint (g : A →ₐ[R₀] C) : Prop :=
  ∀ (m : G), ∀ a ∈ 𝒢 m,
    (AddMonoidAlgebra.single (QuotientAddGroup.mk m : G ⧸ Z) (g a) : AddMonoidAlgebra C (G ⧸ Z)) =
      AddMonoidAlgebra.single 0 (g a)

variable {Z} in
/-- A fixed point is fixed by every point `χ` of `D(M/Z)` with values in any `C`-algebra. -/
lemma IsFixedPoint.character {g : A →ₐ[R₀] C} (hg : IsFixedPoint 𝒢 Z g)
    {C' : Type*} [CommRing C'] [Algebra C C'] (χ : Multiplicative (G ⧸ Z) →* C')
    {m : G} {a : A} (ha : a ∈ 𝒢 m) :
    χ (Multiplicative.ofAdd (QuotientAddGroup.mk m)) * algebraMap C C' (g a) =
      algebraMap C C' (g a) := by
  have := congrArg (AddMonoidAlgebra.lift C C' (G ⧸ Z) χ) (hg m a ha)
  simpa [AddMonoidAlgebra.lift_single, Algebra.smul_def, mul_comm] using this

/-- Conversely, a point fixed by the universal character of `D(M/Z)` is fixed. -/
lemma isFixedPoint_of_character {g : A →ₐ[R₀] C}
    (h : ∀ (m : G), ∀ a ∈ 𝒢 m,
      (AddMonoidAlgebra.single (QuotientAddGroup.mk m : G ⧸ Z) 1 : AddMonoidAlgebra C (G ⧸ Z)) *
          AddMonoidAlgebra.single 0 (g a) = AddMonoidAlgebra.single 0 (g a)) :
    IsFixedPoint 𝒢 Z g := fun m a ha => by
  have := h m a ha
  rwa [AddMonoidAlgebra.single_mul_single, add_zero, one_mul] at this

/-- A point is fixed by `D(M/Z)` iff it kills the components of degree outside `Z`. -/
lemma isFixedPoint_iff (g : A →ₐ[R₀] C) :
    IsFixedPoint 𝒢 Z g ↔ ∀ m, m ∉ Z.toAddSubmonoid → ∀ a ∈ 𝒢 m, g a = 0 := by
  constructor
  · intro h m hm a ha
    have hne : (QuotientAddGroup.mk m : G ⧸ Z) ≠ 0 := fun e =>
      hm ((QuotientAddGroup.eq_zero_iff m).1 e)
    have := congrArg (fun x : AddMonoidAlgebra C (G ⧸ Z) => x.coeff (QuotientAddGroup.mk m))
      (h m a ha)
    simpa [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, hne, Ne.symm hne] using this
  · intro h m a ha
    by_cases hm : m ∈ Z
    · rw [(QuotientAddGroup.eq_zero_iff m).2 hm]
    · rw [h m hm a ha, AddMonoidAlgebra.single_zero, AddMonoidAlgebra.single_zero]

/-- **Proposition 3.35** (affine case; the finite generation of `M` is not needed). For a subgroup
`Z ⊆ M`, the attractor `X^Z` for the `M`-grading is the fixed-point functor `X^{D(M/Z)}`: taking
the underlying point of `X` is a bijection from `X^Z(C)` onto the points fixed by `D(M/Z)`. -/
def attractorFixedEquiv :
    Attractor 𝒢 Z.toAddSubmonoid C ≃ {g : A →ₐ[R₀] C // IsFixedPoint 𝒢 Z g} :=
  (attractorPointsEquiv 𝒢 C Z.toAddSubmonoid).trans <| Equiv.subtypeEquivRight fun g =>
    ⟨fun h => (isFixedPoint_iff Z g).2 fun _ hm _ ha => h _ (mem_magnetIdeal_of_notMem hm ha),
      fun h _ ha => map_eq_zero_of_mem_magnetIdeal g ((isFixedPoint_iff Z g).1 h) ha⟩

@[simp] lemma attractorFixedEquiv_coe (f : Attractor 𝒢 Z.toAddSubmonoid C) :
    (attractorFixedEquiv Z f : A →ₐ[R₀] C) = attractorPoint 𝒢 f := rfl

/-- **Proposition 3.35**, grading statement, with Remark 3.5: for the `M/Z`-grading on `A`
(the action of `D(M/Z)`), the fixed-point ideal `J_{0}` equals `J_Z` for the `M`-grading. -/
theorem magnetIdeal_quotientGrading :
    magnetIdeal (pushGrading 𝒢 (QuotientAddGroup.mk' Z)) (⊥ : Magnet (G ⧸ Z)) =
      magnetIdeal 𝒢 Z.toAddSubmonoid := by
  rw [magnetIdeal_pushGrading]
  congr 1
  ext m
  simp

end Fixed

end AlgMag

