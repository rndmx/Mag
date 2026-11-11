/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Thm153NonFGInv
import AlgMag.Thm153NonFGLemmaD

/-!
# Lemma 1.1 of `notes/thm153-wall.md` (Theorem 15.3, `M^gp` not finitely generated), assembled

`X` an algebraic space locally of finite presentation over `S`, `T` affine, `δ : P → Γ`, `P` countable.
A point `F_α` of `X` over `W_α = A(δ⁻¹ Γ_α)_T` which is `D(Γ)`-invariant after `D(Γ) × W → D(Γ_α) × W_α`
descends, after passing to some finitely generated `Γ_β ⊃ Γ_α`, uniquely to `A(δ_β⁻¹ 0)`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Cardinal

universe u

namespace AlgMag.NonFGL

open AlgMag AlgMag.SD AlgMag.SDTorus AlgMag.NonFGGen AlgMag.NonFGD

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {Γ P : Type u} [AddCommGroup Γ] [AddCommMonoid P] [Countable P] (δ : P →+ Γ)

/-- `δ_β : δ⁻¹ Γ_β → Γ_β`. -/
def δβ (G : FGSub Γ) : Q₁ δ G →+ G.1 where
  toFun p := ⟨δ p, p.2⟩
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

/-- `Γ_β × δ⁻¹ Γ_β → Q₂ Γ_β ⊂ Γ × P`. -/
def eQ (G : FGSub Γ) : G.1 × Q₁ δ G →+ Q₂ δ G where
  toFun q := ⟨((q.1 : Γ), (q.2 : P)), q.1.2, q.2.2⟩
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

/-- The inverse of `eQ`. -/
def eQinv (G : FGSub Γ) : Q₂ δ G →+ G.1 × Q₁ δ G where
  toFun q := (⟨q.1.1, q.2.1⟩, ⟨q.1.2, q.2.2⟩)
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

omit [Countable P] in
lemma eQinv_eQ (G : FGSub Γ) : (eQinv δ G).comp (eQ δ G) = AddMonoidHom.id _ := by
  ext <;> rfl

omit [Countable P] in
lemma actHom_eq (G : FGSub Γ) : actHom δ G = (eQ δ G).comp (actH (δβ δ G)) := by
  ext <;> rfl

omit [Countable P] in
lemma prHom_eq (G : FGSub Γ) : prHom δ G = (eQ δ G).comp (prH (Γ := G.1) (P := Q₁ δ G)) := by
  ext <;> rfl

variable (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  (hP : #P < B.cutoff) (hΓP : #(Γ × P) < B.cutoff)

instance (G : FGSub Γ) : Countable G.1 := by
  have : AddGroup.FG G.1 := (AddGroup.fg_iff_addSubgroup_fg G.1).2 G.2
  have : Module.Finite ℤ G.1 := Module.Finite.iff_addGroup_fg.mpr inferInstance
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' ℤ G.1
  exact hf.countable

instance (G : FGSub Γ) : Countable (Q₂ δ G) :=
  Function.Injective.countable (f := eQinv δ G) fun a b h => by
    have h1 := congrArg (fun q => (q.1 : Γ)) h
    have h2 := congrArg (fun q => (q.2 : P)) h
    exact Subtype.ext (Prod.ext h1 h2)

lemma aMap_eq (G : (FGSub Γ)ᵒᵖ) :
    aMap δ T hP hΓP G = specAlong T (actHom δ G.unop) := site_hom_ext rfl

lemma pMap_eq (G : (FGSub Γ)ᵒᵖ) :
    pMap δ T hP hΓP G = specAlong T (prHom δ G.unop) := site_hom_ext rfl

/-- The universal-point invariance at level `β`, in the product form of `AlgMag.NonFGD`. -/
lemma univ_of_level {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (G : (FGSub Γ)ᵒᵖ)
    (x : X.obj (op ((siteSys (Q₁ δ) (Q₁_mono δ) T hP).obj G)))
    (h : X.map (aMap δ T hP hΓP G).op x = X.map (pMap δ T hP hΓP G).op x) :
    X.map (specAlong T (actH (δβ δ G.unop))).op x =
      X.map (specAlong T (prH (Γ := G.unop.1) (P := Q₁ δ G.unop))).op x := by
  rw [aMap_eq, pMap_eq, actHom_eq, prHom_eq, specAlong_comp, specAlong_comp] at h
  have key : ∀ (W : BigFppfOver B S hS) (k : specObj (G.unop.1 × Q₁ δ G.unop) T ⟶ W)
      (y : X.obj (op W)), X.map k.op y = X.map (specAlong T (eQinv δ G.unop)).op
        (X.map (specAlong T (eQ δ G.unop) ≫ k).op y) := by
    intro W k y
    rw [op_comp, Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp,
      ← specAlong_comp, eQinv_eQ, specAlong_id, op_id, Functor.map_id_apply]
  rw [key _ (specAlong T (actH (δβ δ G.unop))) x, key _ (specAlong T prH) x]
  exact congrArg _ h

/-- **Lemma 1.1** (thm153-wall.md), `P` countable: `F_α ∈ X(W_α)` invariant after
`D(Γ) × W → D(Γ_α) × W_α` gives a finitely generated `Γ_β ⊃ Γ_α` and a unique point of `X` over
`A(δ_β⁻¹ 0)_T` whose pullback to `W_β` is `F_β = F_α ∘ (W_β → W_α)`. -/
theorem lemma11 {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X)) {G : (FGSub Γ)ᵒᵖ}
    (x : X.obj (op ((siteSys (Q₁ δ) (Q₁_mono δ) T hP).obj G)))
    (h : X.map ((siteCone (Q₂ δ) (Q₂_mono δ) T hΓP).π.app G ≫ aMap δ T hP hΓP G).op x =
      X.map ((siteCone (Q₂ δ) (Q₂_mono δ) T hΓP).π.app G ≫ pMap δ T hP hΓP G).op x) :
    ∃ (H : (FGSub Γ)ᵒᵖ) (f : H ⟶ G),
      ∃! x₀ : X.obj (op (specObj (AddSubmonoid.comap (δβ δ H.unop) ⊥) T)),
        X.map (specAlong T (AddSubmonoid.comap (δβ δ H.unop) ⊥).subtype).op x₀ =
          X.map ((siteSys (Q₁ δ) (Q₁_mono δ) T hP).map f).op x := by
  obtain ⟨H, f, hf⟩ := exists_fg_inv δ T hP hΓP hX hfp x h
  refine ⟨H, f, ?_⟩
  have hinv : X.map (aMap δ T hP hΓP H).op (X.map ((siteSys (Q₁ δ) (Q₁_mono δ) T hP).map f).op x) =
      X.map (pMap δ T hP hΓP H).op (X.map ((siteSys (Q₁ δ) (Q₁_mono δ) T hP).map f).op x) := by
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
      ← aMap_nat, ← pMap_nat]
    exact hf
  have : AddGroup.FG H.unop.1 := (AddGroup.fg_iff_addSubgroup_fg H.unop.1).2 H.unop.2
  exact existsUnique_desc_of_univ (δβ δ H.unop) hX _ (univ_of_level δ T hP hΓP H _ hinv)

end AlgMag.NonFGL

#print axioms AlgMag.NonFGL.lemma11
