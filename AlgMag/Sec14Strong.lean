/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec14Final

/-!
# Algebraic Magnetism, §14: strengthened forms

* `AlgMag.indHomCanon`, `AlgMag.indHomCanon_bijective`: **Remark 14.2**, the canonical map
  `Hom(X, Y) → lim_i colim_j Hom(X_i, Y_j)`, characterized by `indHomCanon_eval` and
  `indHomCanon_eq_mk`, and bijective.
* `AlgMag.indHomLim_compat_iff`: the compatibility in `IndHomLim` is the transition map of the
  limit, precomposition with `X_i → X_k`.
* `AlgMag.IndAttractorMapHasPropNat`: the pullback of `X^N → X` in **Proposition 14.4**, with
  bijections natural in the test scheme.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

namespace AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "AFF" => BigAffineFppf B S hS
local notation "incl" => BigAffineFppf.inclusion B S hS
local notation "SITE" => BigFppfOver B S hS

section HomBijection

variable {P Q : ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) → Prop} {X Y : (BigAffineFppf B S hS)ᵒᵖ ⥤ Type u}
  (pX : IndPresentation.{u, v, u} P X) (pY : IndPresentation.{u, v, u} Q Y)

/-- The transition map of `lim_i colim_j Hom(X_i, Y_j)`: precomposition. -/
def IndHomColim.precomp {F F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : F' ⟶ F) :
    IndHomColim pY F → IndHomColim pY F' :=
  Quotient.map' (s₁ := indHomRel pY F) (s₂ := indHomRel pY F') (fun a => ⟨a.1, g ≫ a.2⟩) (by
    rintro a b ⟨k, h, h', e⟩
    refine ⟨k, h, h', ?_⟩
    change (g ≫ a.2) ≫ _ = (g ≫ b.2) ≫ _
    rw [Category.assoc, Category.assoc, e])

variable {pY} in
theorem IndHomColim.eval_precomp {F F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : F' ⟶ F)
    (c : IndHomColim pY F) (A : AFF) (x : F'.obj (op ((incl).obj A))) :
    (IndHomColim.precomp pY g c).eval pY A x = c.eval pY A (g.app _ x) := by
  induction c using Quotient.inductionOn with | _ a => rfl

variable {pX pY} in
/-- The condition defining `IndHomLim` is the equalizer condition of the limit `lim_i`. -/
theorem indHomLim_compat_iff
    (hZ : ∀ j, Presieve.IsSheaf (BigFppfOver.topology B S hS) (pY.obj j))
    (c : ∀ i : pX.I, IndHomColim pY (pX.obj i)) :
    (∀ {i k : pX.I} (h : i ≤ k) (A : AFF) (x : (pX.obj i).obj (op ((incl).obj A))),
      (c k).eval pY A ((pX.tr h).app _ x) = (c i).eval pY A x) ↔
    ∀ {i k : pX.I} (h : i ≤ k), IndHomColim.precomp pY (pX.tr h) (c k) = c i := by
  constructor
  · intro H i k h
    exact IndHomColim.ext_eval hZ fun A x => by rw [IndHomColim.eval_precomp, H h]
  · intro H i k h A x
    rw [← IndHomColim.eval_precomp, H h]

/-- **Remark 14.2**: the canonical map `Hom(X, Y) → lim_i colim_j Hom(X_i, Y_j)`; on `X_i` it is the
class of any factorization of `X_i → X → Y` through a term `Y_j`. -/
noncomputable def indHomCanon
    (hZ : ∀ j, Presieve.IsSheaf (BigFppfOver.topology B S hS) (pY.obj j))
    (hX : ∀ i, IsFinitelyCovered (B := B) (S := S) (hS := hS) (pX.obj i)) (f : X ⟶ Y) :
    IndHomLim pX pY :=
  have hfwd : ∀ i : pX.I, ∃ c : IndHomColim pY (pX.obj i),
      ∀ (A : AFF) (x : (pX.obj i).obj (op ((incl).obj A))), c.eval pY A x = f.app _ (pX.π i A x) := by
    intro i
    obtain ⟨j, ψ, h⟩ := exists_indHom_term pX pY hZ hX f i
    exact ⟨Quotient.mk (indHomRel pY _) ⟨j, ψ⟩, h⟩
  ⟨fun i => (hfwd i).choose, fun {i k} h A x => by
    rw [(hfwd k).choose_spec, (hfwd i).choose_spec, pX.π_tr]⟩

variable {pX pY} in
/-- **Remark 14.2**: the value of the canonical map. -/
theorem indHomCanon_eval
    (hZ : ∀ j, Presieve.IsSheaf (BigFppfOver.topology B S hS) (pY.obj j))
    (hX : ∀ i, IsFinitelyCovered (B := B) (S := S) (hS := hS) (pX.obj i)) (f : X ⟶ Y) (i : pX.I)
    (A : AFF) (x : (pX.obj i).obj (op ((incl).obj A))) :
    ((indHomCanon pX pY hZ hX f).1 i).eval pY A x = f.app _ (pX.π i A x) := by
  have hfwd : ∀ i : pX.I, ∃ c : IndHomColim pY (pX.obj i),
      ∀ (A : AFF) (x : (pX.obj i).obj (op ((incl).obj A))), c.eval pY A x = f.app _ (pX.π i A x) := by
    intro i
    obtain ⟨j, ψ, h⟩ := exists_indHom_term pX pY hZ hX f i
    exact ⟨Quotient.mk (indHomRel pY _) ⟨j, ψ⟩, h⟩
  exact (hfwd i).choose_spec A x

variable {pX pY} in
/-- **Remark 14.2**: the canonical map sends `f` to the class of any factorization of
`X_i → X → Y` through `Y_j`. -/
theorem indHomCanon_eq_mk
    (hZ : ∀ j, Presieve.IsSheaf (BigFppfOver.topology B S hS) (pY.obj j))
    (hX : ∀ i, IsFinitelyCovered (B := B) (S := S) (hS := hS) (pX.obj i)) (f : X ⟶ Y) (i : pX.I)
    (j : pY.I) (ψ : pX.obj i ⟶ pY.obj j)
    (h : ∀ (A : AFF) (x : (pX.obj i).obj (op ((incl).obj A))),
      pY.π j A (ψ.app _ x) = f.app _ (pX.π i A x)) :
    (indHomCanon pX pY hZ hX f).1 i = Quotient.mk (indHomRel pY _) ⟨j, ψ⟩ :=
  IndHomColim.ext_eval hZ fun A x => (indHomCanon_eval hZ hX f i A x).trans (h A x).symm

/-- **Remark 14.2**: the canonical map is bijective. -/
theorem indHomCanon_bijective
    (hZ : ∀ j, Presieve.IsSheaf (BigFppfOver.topology B S hS) (pY.obj j))
    (hX : ∀ i, IsFinitelyCovered (B := B) (S := S) (hS := hS) (pX.obj i)) :
    Function.Bijective (indHomCanon pX pY hZ hX) := by
  constructor
  · intro f g e
    refine indHom_ext pX fun i A x => ?_
    rw [← indHomCanon_eval hZ hX f, ← indHomCanon_eval hZ hX g, e]
  · intro c
    have hnat : ∀ (i : pX.I) {A A' : AFF} (s : A' ⟶ A)
        (x : (pX.obj i).obj (op ((incl).obj A))),
        (c.1 i).eval pY A' ((pX.obj i).map ((incl).map s).op x) =
          Y.map s.op ((c.1 i).eval pY A x) := by
      intro i A A' s x
      generalize c.1 i = d
      induction d using Quotient.inductionOn with | _ a => ?_
      change pY.π a.1 A' _ = Y.map s.op (pY.π a.1 A _)
      rw [← pY.π_map]
      congr 1
      exact hom_naturality_apply a.2 ((incl).map s).op x
    obtain ⟨f, hf⟩ := exists_indHom_of_compatible pX (fun i A x => (c.1 i).eval pY A x)
      (fun i _ _ s x => hnat i s x) (fun h A x => c.2 h A x)
    refine ⟨f, Subtype.ext (funext fun i => IndHomColim.ext_eval hZ fun A x => ?_)⟩
    rw [indHomCanon_eval, hf]

end HomBijection

section Attractor

variable {M : Type u} [AddCommGroup M] [Countable M] {P : ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) → Prop}
variable {X : (BigAffineFppf B S hS)ᵒᵖ ⥤ Type u} {p : IndPresentation.{u, v, u} P X}
variable (a : IndAction M p) (N : AddSubmonoid M)

/-- **Proposition 14.4**: `T ×_X X^N` is represented by a presheaf over `T` with property `Q`, the
bijection on `T'`-points being natural in `T'`, compatibly with the map to `X`. -/
def IndAttractorMapHasPropNat (Q : ∀ {Z T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, (Z ⟶ T') → Prop) :
    Prop :=
  ∀ (T : AFF) (y : X.obj (op T)),
    ∃ (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (q : Z ⟶ yoneda.obj ((incl).obj T)), Q q ∧
      ∃ e : ∀ (T' : AFF) (t : T' ⟶ T), {z : Z.obj (op ((incl).obj T')) // q.app _ z = (incl).map t} ≃
          {ψ : AttractorPt a.toAction N T' // ψ.toPoint = X.map t.op y},
        ∀ {T' T'' : AFF} (s : T'' ⟶ T') (t : T' ⟶ T)
          (z : {z : Z.obj (op ((incl).obj T')) // q.app _ z = (incl).map t})
          (hz : q.app _ (Z.map ((incl).map s).op z.1) = (incl).map (s ≫ t)),
          (e T'' (s ≫ t) ⟨Z.map ((incl).map s).op z.1, hz⟩).1 = (e T' t z).1.baseChange s

/-- `indPt` commutes with base change. -/
theorem indPt_baseChange (i : p.I) {T T' : AFF} (s : T' ⟶ T)
    (φ : AttractorPt (a.act i) N ((incl).obj T)) :
    indPt a N i (φ.baseChange ((incl).map s)) = (indPt a N i φ).baseChange s := by
  ext T'' t b
  change p.π i T'' (φ.app ((incl).map t ≫ (incl).map s) b) = p.π i T'' (φ.app ((incl).map (t ≫ s)) b)
  rw [Functor.map_comp]

/-- `AlgMag.indAttractorFibreEquiv` is natural in the test scheme. -/
theorem indAttractorFibreEquiv_nat {i : p.I} {Zi : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (r : RepresentsAttractor (a.act i) N Zi) (j : Zi ⟶ p.obj i)
    (hj : ∀ (T : SITE) (z : Zi.obj (op T)), j.app (op T) z = (r.equiv T z).toPoint)
    {T : AFF} (x : (p.obj i).obj (op ((incl).obj T))) {T' T'' : AFF} (s : T'' ⟶ T') (t : T' ⟶ T)
    (z : {z : (fibreProduct j (yonedaEquiv.symm x)).obj (op ((incl).obj T')) //
        (fibreSnd j (yonedaEquiv.symm x)).app _ z = (incl).map t})
    (hz : (fibreSnd j (yonedaEquiv.symm x)).app _
      ((fibreProduct j (yonedaEquiv.symm x)).map ((incl).map s).op z.1) = (incl).map (s ≫ t)) :
    (indAttractorFibreEquiv a N r j hj x T'' (s ≫ t)
        ⟨(fibreProduct j (yonedaEquiv.symm x)).map ((incl).map s).op z.1, hz⟩).1 =
      (indAttractorFibreEquiv a N r j hj x T' t z).1.baseChange s := by
  change indPt a N i (r.equiv _ (Zi.map ((incl).map s).op z.1.1.1)) = _
  rw [r.naturality]
  exact indPt_baseChange a N i s _

/-- **Proposition 14.4**, "representable by algebraic spaces", natural form. -/
theorem indAttractorMap_rep_nat {Zi : p.I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (r : ∀ i, RepresentsAttractor (a.act i) N (Zi i)) (j : ∀ i, Zi i ⟶ p.obj i)
    (hj : ∀ i (T : SITE) (z : (Zi i).obj (op T)), (j i).app (op T) z = ((r i).equiv T z).toPoint)
    (hZ : ∀ i, IsAlgebraicSpace B S hS (Zi i)) (hX : ∀ i, IsAlgebraicSpace B S hS (p.obj i)) :
    IndAttractorMapHasPropNat a N (fun {Z' _} _ => IsAlgebraicSpace B S hS Z') := by
  intro T y
  obtain ⟨i, x, rfl⟩ := p.surj T y
  refine ⟨fibreProduct (j i) (yonedaEquiv.symm x), fibreSnd _ _, ?_,
    fun T' t => indAttractorFibreEquiv a N (r i) (j i) (hj i) x T' t,
    fun s t z hz => indAttractorFibreEquiv_nat a N (r i) (j i) (hj i) x s t z hz⟩
  exact isAlgebraicSpace_of_isPullback (hZ i) (isAlgebraicSpace_yoneda B S hS _) (hX i).isSheaf
    (hX i).diagonal_representable (isPullback_fibreProduct _ _)

/-- **Proposition 14.4**, resp. ind-schemes, natural form. -/
theorem indAttractorMap_rep_scheme_nat {Zi : p.I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (r : ∀ i, RepresentsAttractor (a.act i) N (Zi i)) (j : ∀ i, Zi i ⟶ p.obj i)
    (hj : ∀ i (T : SITE) (z : (Zi i).obj (op T)), (j i).app (op T) z = ((r i).equiv T z).toPoint)
    (hZ : ∀ i, ∃ U : BigFppfOver B S hS, Nonempty (Zi i ≅ yoneda.obj U))
    (hX : ∀ i, ∃ U : BigFppfOver B S hS, Nonempty (p.obj i ≅ yoneda.obj U)) :
    IndAttractorMapHasPropNat a N
      (fun {Z' _} _ => ∃ U : BigFppfOver B S hS, Nonempty (Z' ≅ yoneda.obj U)) := by
  intro T y
  obtain ⟨i, x, rfl⟩ := p.surj T y
  exact ⟨fibreProduct (j i) (yonedaEquiv.symm x), fibreSnd _ _,
    representable_fibreProduct (hZ i) ⟨_, ⟨Iso.refl _⟩⟩ (hX i) _ _,
    fun T' t => indAttractorFibreEquiv a N (r i) (j i) (hj i) x T' t,
    fun s t z hz => indAttractorFibreEquiv_nat a N (r i) (j i) (hj i) x s t z hz⟩

/-- **Proposition 14.4**, last assertion, natural form, with a `Z`-FPR atlas on each term, the
hypothesis of Proposition 8.1. It cannot be dropped, see `AlgMag/Sec14Counterexample.lean`. -/
theorem indAttractorMap_isClosedImm_nat [AddGroup.FG M] (Z : AddSubgroup M)
    (hX : ∀ i, IsAlgebraicSpace B S hS (p.obj i)) (hat : ∀ i, ExistsZFPRAtlas (a.act i) Z) :
    IndAttractorMapHasPropNat a Z.toAddSubmonoid (fun f => IsClosedImm f) := by
  intro T y
  obtain ⟨i, x, rfl⟩ := p.surj T y
  obtain ⟨Zi, j, r, -, hc, hj⟩ := prop81FG.{u, u} B S hS M (p.obj i) (hX i) (a.act i) Z (hat i)
  refine ⟨fibreProduct j (yonedaEquiv.symm x), fibreSnd _ _, ?_,
    fun T' t => indAttractorFibreEquiv a Z.toAddSubmonoid r j hj x T' t,
    fun s t z hz => indAttractorFibreEquiv_nat a Z.toAddSubmonoid r j hj x s t z hz⟩
  exact (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
    (isPullback_fibreProduct _ _) hc

end Attractor

end AlgMag

#print axioms AlgMag.indHomLim_compat_iff
#print axioms AlgMag.indHomCanon_eq_mk
#print axioms AlgMag.indHomCanon_bijective
#print axioms AlgMag.indAttractorMap_rep_nat
#print axioms AlgMag.indAttractorMap_rep_scheme_nat
#print axioms AlgMag.indAttractorMap_isClosedImm_nat
