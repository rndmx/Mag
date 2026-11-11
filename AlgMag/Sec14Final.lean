/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec12Final
import AlgMag.Sec8Representability
import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC

/-!
# Algebraic Magnetism, §14: remaining assertions

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026), §14.

* `AlgMag.isFinitelyCovered_of_isQuasiCompactSpace`: the quasi-compactness of Remark 14.2.
* `AlgMag.isIndScheme_fibreProduct`: Remark 14.2 for ind-schemes with quasi-compact terms.
* `AlgMag.indHomEquiv`: Remark 14.2, `Hom(X, Y) = lim_i colim_j Hom(X_i, Y_j)` as a bijection.
* `AlgMag.indAttractorMap_rep`, `AlgMag.indAttractorMap_isClosedImm`: Proposition 14.4, the last two
  assertions.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

namespace AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "AFF" => BigAffineFppf B S hS
local notation "incl" => BigAffineFppf.inclusion B S hS
local notation "SITE" => BigFppfOver B S hS

/-- **Remark 14.2**: a quasi-compact algebraic space is covered by one affine scheme. -/
theorem isFinitelyCovered_of_isQuasiCompactSpace {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hq : Space.IsQuasiCompactSpace B S hS F) :
    IsFinitelyCovered (B := B) (S := S) (hS := hS) F := by
  obtain ⟨U, f, h1, h2, h3⟩ :=
    (Space.isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS F hF).1 hq
  exact isFinitelyCovered_of_atlas (⟨U, h1⟩ : AFF) f h2 (Space.presheaf_etale_of_isEtale B S hS h3)

section Schemes

/-- Fibre products of representable presheaves are representable. -/
theorem representable_fibreProduct {F₁ F₂ F₃ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (h₁ : ∃ U : SITE, Nonempty (F₁ ≅ yoneda.obj U)) (h₂ : ∃ U : SITE, Nonempty (F₂ ≅ yoneda.obj U))
    (h₃ : ∃ U : SITE, Nonempty (F₃ ≅ yoneda.obj U)) (a : F₁ ⟶ F₃) (b : F₂ ⟶ F₃) :
    ∃ U : SITE, Nonempty (fibreProduct a b ≅ yoneda.obj U) := by
  obtain ⟨U₁, ⟨e₁⟩⟩ := h₁
  obtain ⟨U₂, ⟨e₂⟩⟩ := h₂
  obtain ⟨U₃, ⟨e₃⟩⟩ := h₃
  let α : U₁ ⟶ U₃ := yoneda.preimage (e₁.inv ≫ a ≫ e₃.hom)
  let β : U₂ ⟶ U₃ := yoneda.preimage (e₂.inv ≫ b ≫ e₃.hom)
  have hp : IsPullback (yoneda.map (pullback.fst α β)) (yoneda.map (pullback.snd α β))
      (yoneda.map α) (yoneda.map β) := (IsPullback.of_hasPullback α β).map yoneda
  have hp' : IsPullback (yoneda.map (pullback.fst α β) ≫ e₁.inv)
      (yoneda.map (pullback.snd α β) ≫ e₂.inv) a b := by
    refine IsPullback.of_iso hp (Iso.refl _) e₁.symm e₂.symm e₃.symm ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp [α]
    · simp [β]
  exact ⟨pullback α β, ⟨(isPullback_fibreProduct a b).isoIsPullback _ _ hp'⟩⟩

/-- **Remark 14.2**: ind-schemes with quasi-compact terms are closed under fibre products. -/
theorem isIndScheme_fibreProduct {X Y Z : (BigAffineFppf B S hS)ᵒᵖ ⥤ Type u}
    (pX : IndPresentation.{u, v, u}
      (fun F : SITEᵒᵖ ⥤ Type u => ∃ U : SITE, Nonempty (F ≅ yoneda.obj U)) X)
    (pY : IndPresentation.{u, v, u}
      (fun F : SITEᵒᵖ ⥤ Type u => ∃ U : SITE, Nonempty (F ≅ yoneda.obj U)) Y)
    (pZ : IndPresentation.{u, v, u}
      (fun F : SITEᵒᵖ ⥤ Type u => ∃ U : SITE, Nonempty (F ≅ yoneda.obj U)) Z)
    (f : X ⟶ Z) (g : Y ⟶ Z)
    (hX : ∀ i, IsFinitelyCovered (B := B) (S := S) (hS := hS) (pX.obj i))
    (hY : ∀ j, IsFinitelyCovered (B := B) (S := S) (hS := hS) (pY.obj j)) :
    IsIndScheme.{u, v} (fibreProduct f g) :=
  exists_indPresentation_fibreProduct pX pY pZ f g
    (fun k => by
      obtain ⟨U, ⟨e⟩⟩ := pZ.prop k
      exact (isSheaf_iff_isSheaf_of_type _ _).mp
        ((Presheaf.isSheaf_of_iso_iff e).2 (isAlgebraicSpace_yoneda B S hS U).isSheaf)) hX hY
    (fun i j k a b => representable_fibreProduct (pX.prop i) (pY.prop j) (pZ.prop k) a b)

end Schemes

section HomBijection

variable {P Q : ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) → Prop} {X Y : (BigAffineFppf B S hS)ᵒᵖ ⥤ Type u}
  (pX : IndPresentation.{u, v, u} P X) (pY : IndPresentation.{u, v, u} Q Y)

/-- The relation defining `colim_j Hom(F, Y_j)`. -/
def indHomRel (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Setoid (Σ j : pY.I, F ⟶ pY.obj j) where
  r a b := ∃ (k : pY.I) (h : a.1 ≤ k) (h' : b.1 ≤ k), a.2 ≫ pY.tr h = b.2 ≫ pY.tr h'
  iseqv :=
    { refl := fun a => ⟨a.1, le_refl _, le_refl _, rfl⟩
      symm := fun ⟨k, h, h', e⟩ => ⟨k, h', h, e.symm⟩
      trans := by
        rintro a b c ⟨k, h, h', e⟩ ⟨l, g, g', e'⟩
        obtain ⟨m, hk, hl⟩ := exists_ge_ge k l
        refine ⟨m, h.trans hk, g'.trans hl, ?_⟩
        have e₁ : a.2 ≫ pY.tr (h.trans hk) = b.2 ≫ pY.tr (h'.trans hk) := by
          rw [pY.tr_trans h hk, pY.tr_trans h' hk, ← Category.assoc, e, Category.assoc]
        have e₂ : b.2 ≫ pY.tr (g.trans hl) = c.2 ≫ pY.tr (g'.trans hl) := by
          rw [pY.tr_trans g hl, pY.tr_trans g' hl, ← Category.assoc, e', Category.assoc]
        exact e₁.trans e₂ }

/-- `colim_j Hom(F, Y_j)`. -/
def IndHomColim (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Type _ := Quotient (indHomRel pY F)

/-- The value of a class of `colim_j Hom(F, Y_j)` on an affine point of `F`. -/
def IndHomColim.eval {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (c : IndHomColim pY F) (A : AFF)
    (x : F.obj (op ((incl).obj A))) : Y.obj (op A) :=
  Quotient.lift (s := indHomRel pY F) (fun a => pY.π a.1 A (a.2.app _ x)) (by
    rintro a b ⟨k, h, h', e⟩
    change pY.π a.1 A _ = pY.π b.1 A _
    rw [← pY.π_tr h, ← pY.π_tr h']
    exact congrArg (pY.π k A) (hom_app_congr e _ x)) c

variable {pY} in
/-- A class in `colim_j Hom(F, Y_j)` is determined by its values on affine points, for `Y_j` sheaves. -/
theorem IndHomColim.ext_eval (hZ : ∀ j, Presieve.IsSheaf (BigFppfOver.topology B S hS) (pY.obj j))
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {c c' : IndHomColim pY F}
    (h : ∀ (A : AFF) (x : F.obj (op ((incl).obj A))), c.eval pY A x = c'.eval pY A x) : c = c' := by
  induction c using Quotient.inductionOn with | _ a => ?_
  induction c' using Quotient.inductionOn with | _ b => ?_
  obtain ⟨k, h₁, h₂⟩ := exists_ge_ge a.1 b.1
  refine Quotient.sound ⟨k, h₁, h₂, ?_⟩
  ext T x
  refine ind_sep_affine (hZ k) fun A s => ?_
  refine ind_π_injective pY k A ?_
  have e₁ := hom_naturality_apply (a.2 ≫ pY.tr h₁) s.op x
  have e₂ := hom_naturality_apply (b.2 ≫ pY.tr h₂) s.op x
  refine (congrArg _ e₁.symm).trans (Eq.trans ?_ (congrArg _ e₂))
  exact (pY.π_tr h₁ A _).trans ((h A (F.map s.op x)).trans (pY.π_tr h₂ A _).symm)

/-- `lim_i colim_j Hom(X_i, Y_j)`: compatible classes. -/
def IndHomLim : Type _ :=
  { c : ∀ i : pX.I, IndHomColim pY (pX.obj i) //
    ∀ {i k : pX.I} (h : i ≤ k) (A : AFF) (x : (pX.obj i).obj (op ((incl).obj A))),
      (c k).eval pY A ((pX.tr h).app _ x) = (c i).eval pY A x }

/-- **Remark 14.2**, as a bijection: `Hom(X, Y) = lim_i colim_j Hom(X_i, Y_j)`, when the `X_i` are
quasi-compact and the `Y_j` are sheaves. -/
noncomputable def indHomEquiv
    (hZ : ∀ j, Presieve.IsSheaf (BigFppfOver.topology B S hS) (pY.obj j))
    (hX : ∀ i, IsFinitelyCovered (B := B) (S := S) (hS := hS) (pX.obj i)) :
    (X ⟶ Y) ≃ IndHomLim pX pY := by
  have hfwd : ∀ (f : X ⟶ Y) (i : pX.I), ∃ c : IndHomColim pY (pX.obj i),
      ∀ (A : AFF) (x : (pX.obj i).obj (op ((incl).obj A))), c.eval pY A x = f.app _ (pX.π i A x) := by
    intro f i
    obtain ⟨j, ψ, h⟩ := exists_indHom_term pX pY hZ hX f i
    exact ⟨Quotient.mk (indHomRel pY _) ⟨j, ψ⟩, h⟩
  have hnat : ∀ (c : IndHomLim pX pY) (i : pX.I) {A A' : AFF} (s : A' ⟶ A)
      (x : (pX.obj i).obj (op ((incl).obj A))),
      (c.1 i).eval pY A' ((pX.obj i).map ((incl).map s).op x) = Y.map s.op ((c.1 i).eval pY A x) := by
    intro c i A A' s x
    generalize c.1 i = d
    induction d using Quotient.inductionOn with | _ a => ?_
    change pY.π a.1 A' _ = Y.map s.op (pY.π a.1 A _)
    rw [← pY.π_map]
    congr 1
    exact hom_naturality_apply a.2 ((incl).map s).op x
  have hbwd : ∀ c : IndHomLim pX pY, ∃ f : X ⟶ Y, ∀ (i : pX.I) (A : AFF)
      (x : (pX.obj i).obj (op ((incl).obj A))), f.app _ (pX.π i A x) = (c.1 i).eval pY A x :=
    fun c => exists_indHom_of_compatible pX (fun i A x => (c.1 i).eval pY A x)
      (fun i _ _ s x => hnat c i s x) (fun h A x => c.2 h A x)
  refine
    { toFun := fun f => ⟨fun i => (hfwd f i).choose, fun {i k} h A x => ?_⟩
      invFun := fun c => (hbwd c).choose
      left_inv := fun f => ?_
      right_inv := fun c => ?_ }
  · rw [(hfwd f k).choose_spec, (hfwd f i).choose_spec, pX.π_tr]
  · refine indHom_ext pX fun i A x => ?_
    exact ((hbwd _).choose_spec i A x).trans ((hfwd f i).choose_spec A x)
  · refine Subtype.ext (funext fun i => IndHomColim.ext_eval hZ fun A x => ?_)
    rw [(hfwd _ i).choose_spec, (hbwd c).choose_spec]

end HomBijection

section Attractor

variable {M : Type u} [AddCommGroup M] [Countable M] {P : ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) → Prop}
variable {X : (BigAffineFppf B S hS)ᵒᵖ ⥤ Type u} {p : IndPresentation.{u, v, u} P X}
variable (a : IndAction M p) (N : AddSubmonoid M)

/-- **Remark 14.2** for the natural morphism `X^N → X` of **Proposition 14.4**: for every affine
`T → X`, the pullback `T ×_X X^N` is represented by a presheaf over `T` with the property `Q`. The
attractor functor takes values in a larger universe, so it is not an instance of
`AlgMag.IndMapHasProp`. -/
def IndAttractorMapHasProp (Q : ∀ {Z T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, (Z ⟶ T') → Prop) : Prop :=
  ∀ (T : AFF) (y : X.obj (op T)),
    ∃ (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (q : Z ⟶ yoneda.obj ((incl).obj T)), Q q ∧
      ∀ (T' : AFF) (t : T' ⟶ T),
        Nonempty ({z : Z.obj (op ((incl).obj T')) // q.app _ z = (incl).map t} ≃
          {ψ : AttractorPt a.toAction N T' // ψ.toPoint = X.map t.op y})

/-- **Proposition 14.4**, `T ×_X X^N = T ×_{X_i} X_i^N`, as a bijection on `T'`-points. -/
noncomputable def indAttractorFibreEquiv {i : p.I} {Zi : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (r : RepresentsAttractor (a.act i) N Zi) (j : Zi ⟶ p.obj i)
    (hj : ∀ (T : SITE) (z : Zi.obj (op T)), j.app (op T) z = (r.equiv T z).toPoint)
    {T : AFF} (x : (p.obj i).obj (op ((incl).obj T))) (T' : AFF) (t : T' ⟶ T) :
    {z : (fibreProduct j (yonedaEquiv.symm x)).obj (op ((incl).obj T')) //
        (fibreSnd j (yonedaEquiv.symm x)).app _ z = (incl).map t} ≃
      {ψ : AttractorPt a.toAction N T' // ψ.toPoint = X.map t.op (p.π i T x)} := by
  have hx : ∀ z : {z : (fibreProduct j (yonedaEquiv.symm x)).obj (op ((incl).obj T')) //
        (fibreSnd j (yonedaEquiv.symm x)).app _ z = (incl).map t},
      (r.equiv _ z.1.1.1).toPoint = (p.obj i).map ((incl).map t).op x := by
    rintro ⟨⟨⟨v, s⟩, hvs⟩, hs⟩
    obtain rfl : s = (incl).map t := hs
    rw [← hj]
    exact hvs
  refine Equiv.ofBijective
    (fun z => ⟨indPt a N i (r.equiv _ z.1.1.1), ?_⟩) ⟨?_, ?_⟩
  · change p.π i T' (r.equiv _ z.1.1.1).toPoint = _
    rw [hx z]
    exact p.π_map i t x
  · intro z z' e
    have e' : indPt a N i (r.equiv _ z.1.1.1) = indPt a N i (r.equiv _ z'.1.1.1) :=
      congrArg Subtype.val e
    have hu := (existsUnique_indPt_of_toPoint a N i ((p.obj i).map ((incl).map t).op x)
      (indPt a N i (r.equiv _ z.1.1.1)) (by
        change p.π i T' (r.equiv _ z.1.1.1).toPoint = _
        rw [hx z])).unique
      (y₁ := r.equiv _ z.1.1.1) (y₂ := r.equiv _ z'.1.1.1)
      ⟨rfl, hx z⟩ ⟨e'.symm, hx z'⟩
    have hv : z.1.1.1 = z'.1.1.1 := (r.equiv _).injective hu
    exact Subtype.ext (Subtype.ext (Prod.ext hv (z.2.trans z'.2.symm)))
  · rintro ⟨ψ, hψ⟩
    have hb : ψ.toPoint = p.π i T' ((p.obj i).map ((incl).map t).op x) :=
      Eq.trans hψ (p.π_map i t x).symm
    obtain ⟨φ, ⟨h₁, h₂⟩, -⟩ := existsUnique_indPt_of_toPoint a N i _ ψ hb
    refine ⟨⟨⟨((r.equiv _).symm φ, (incl).map t), ?_⟩, rfl⟩, ?_⟩
    · change j.app _ _ = (yonedaEquiv.symm x).app _ _
      rw [hj, Equiv.apply_symm_apply, h₂]
      rfl
    · exact Subtype.ext (by
        change indPt a N i (r.equiv _ ((r.equiv _).symm φ)) = ψ
        rw [Equiv.apply_symm_apply, h₁])

/-- **Proposition 14.4**, "the natural morphism `X^N → X` is representable by algebraic spaces": if
`X_i^N` is represented by an algebraic space `Z_i` over `X_i` for all `i`, the pullback of `X^N → X`
to an affine `T → X` is represented by an algebraic space. -/
theorem indAttractorMap_rep {Zi : p.I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (r : ∀ i, RepresentsAttractor (a.act i) N (Zi i)) (j : ∀ i, Zi i ⟶ p.obj i)
    (hj : ∀ i (T : SITE) (z : (Zi i).obj (op T)), (j i).app (op T) z = ((r i).equiv T z).toPoint)
    (hZ : ∀ i, IsAlgebraicSpace B S hS (Zi i)) (hX : ∀ i, IsAlgebraicSpace B S hS (p.obj i)) :
    IndAttractorMapHasProp a N (fun {Z' _} _ => IsAlgebraicSpace B S hS Z') := by
  intro T y
  obtain ⟨i, x, rfl⟩ := p.surj T y
  refine ⟨fibreProduct (j i) (yonedaEquiv.symm x), fibreSnd _ _, ?_, fun T' t =>
    ⟨indAttractorFibreEquiv a N (r i) (j i) (hj i) x T' t⟩⟩
  exact isAlgebraicSpace_of_isPullback (hZ i) (isAlgebraicSpace_yoneda B S hS _) (hX i).isSheaf
    (hX i).diagonal_representable (isPullback_fibreProduct _ _)

/-- **Proposition 14.4**, resp. ind-schemes: if `X` is an ind-scheme and `X_i^N` is represented by a
scheme `Z_i` over `X_i` for all `i`, the pullback of `X^N → X` to an affine `T → X` is a scheme. -/
theorem indAttractorMap_rep_scheme {Zi : p.I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (r : ∀ i, RepresentsAttractor (a.act i) N (Zi i)) (j : ∀ i, Zi i ⟶ p.obj i)
    (hj : ∀ i (T : SITE) (z : (Zi i).obj (op T)), (j i).app (op T) z = ((r i).equiv T z).toPoint)
    (hZ : ∀ i, ∃ U : BigFppfOver B S hS, Nonempty (Zi i ≅ yoneda.obj U))
    (hX : ∀ i, ∃ U : BigFppfOver B S hS, Nonempty (p.obj i ≅ yoneda.obj U)) :
    IndAttractorMapHasProp a N (fun {Z' _} _ => ∃ U : BigFppfOver B S hS, Nonempty (Z' ≅ yoneda.obj U)) := by
  intro T y
  obtain ⟨i, x, rfl⟩ := p.surj T y
  exact ⟨fibreProduct (j i) (yonedaEquiv.symm x), fibreSnd _ _,
    representable_fibreProduct (hZ i) ⟨_, ⟨Iso.refl _⟩⟩ (hX i) _ _, fun T' t =>
    ⟨indAttractorFibreEquiv a N (r i) (j i) (hj i) x T' t⟩⟩

/-- **Proposition 14.4**, last assertion: if `M` is finitely generated and `N = Z` is a group, the
natural morphism `X^Z → X` is representable by a closed immersion. The `Z`-FPR atlas of each term is
the input of Proposition 8.1 (`AlgMag.prop81FG`). -/
theorem indAttractorMap_isClosedImm [AddGroup.FG M] (Z : AddSubgroup M)
    (hX : ∀ i, IsAlgebraicSpace B S hS (p.obj i)) (hat : ∀ i, ExistsZFPRAtlas (a.act i) Z) :
    IndAttractorMapHasProp a Z.toAddSubmonoid (fun f => IsClosedImm f) := by
  intro T y
  obtain ⟨i, x, rfl⟩ := p.surj T y
  obtain ⟨Zi, j, r, -, hc, hj⟩ := prop81FG.{u, u} B S hS M (p.obj i) (hX i) (a.act i) Z (hat i)
  refine ⟨fibreProduct j (yonedaEquiv.symm x), fibreSnd _ _, ?_, fun T' t =>
    ⟨indAttractorFibreEquiv a Z.toAddSubmonoid r j hj x T' t⟩⟩
  exact (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
    (isPullback_fibreProduct _ _) hc

end Attractor

end AlgMag

#print axioms AlgMag.isFinitelyCovered_of_isQuasiCompactSpace
#print axioms AlgMag.isIndScheme_fibreProduct
#print axioms AlgMag.indHomEquiv
#print axioms AlgMag.indAttractorMap_rep
#print axioms AlgMag.indAttractorMap_rep_scheme
#print axioms AlgMag.indAttractorMap_isClosedImm
