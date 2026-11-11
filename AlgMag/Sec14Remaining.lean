/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec14Ind

/-!
# Algebraic Magnetism, §14: remaining statements

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026), §14.

* `AlgMag.HasIndProp`, `AlgMag.IndMapHasProp`, `AlgMag.exists_indHom_factor`: Remark 14.2 (ind-`P`,
  property of a map, maps from an affine scheme to an ind-space factor through a term).
* `AlgMag.MonoidPresheaf`, `AlgMag.CatAction`, `AlgMag.IndActionG`, `AlgMag.IndActionG.toCatAction`:
  Definition 14.3 for a general monoid (in particular group) functor `G`.
* `AlgMag.isIndScheme_attractor`: Proposition 14.4, the ind-scheme variant.
-/

open CategoryTheory Opposite AlgebraicGeometry

universe u v w

namespace AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "AFF" => BigAffineFppf B S hS
local notation "incl" => BigAffineFppf.inclusion B S hS
local notation "SITE" => BigFppfOver B S hS

/-! ### Remark 14.2 -/

/-- **Remark 14.2.** `X` has ind-`P`: it has a presentation whose terms have the property `P`. -/
def HasIndProp (P : (SITEᵒᵖ ⥤ Type u) → Prop) (X : AFFᵒᵖ ⥤ Type w) : Prop :=
  Nonempty (IndPresentation.{u, v, w} P X)

/-- **Remark 14.2.** A map `f : X → Y` of functors on `(Aff/S)` has the property `Q`: for every
affine `T → Y`, the pullback `T ×_Y X` is represented by a presheaf `Z` over `T` on the site, whose
morphism to `T` has the property `Q`. -/
def IndMapHasProp (Q : ∀ {Z T' : SITEᵒᵖ ⥤ Type u}, (Z ⟶ T') → Prop) {X Y : AFFᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) : Prop :=
  ∀ (T : AFF) (y : Y.obj (op T)),
    ∃ (Z : SITEᵒᵖ ⥤ Type u) (q : Z ⟶ yoneda.obj ((incl).obj T)), Q q ∧
      ∀ (T' : AFF) (t : T' ⟶ T),
        Nonempty ({z : Z.obj (op ((incl).obj T')) // q.app _ z = (incl).map t} ≃
          {x : X.obj (op T') // f.app _ x = Y.map t.op y})

section Hom

variable {P : ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) → Prop} {Y : (BigAffineFppf B S hS)ᵒᵖ ⥤ Type w}
  (p : IndPresentation.{u, v, w} P Y)

/-- **Remark 14.2**, `Hom(T, Y) = colim_j Hom(T, Y_j)` for `T` affine: every map from an affine
scheme factors through a term of the presentation, and two factorizations agree in a later term. -/
theorem exists_indHom_factor (T : AFF) (y : Y.obj (op T)) :
    ∃ (j : p.I) (y' : (p.obj j).obj (op ((incl).obj T))), p.π j T y' = y ∧
      ∀ y'' : (p.obj j).obj (op ((incl).obj T)), p.π j T y'' = y →
        ∃ (k : p.I) (h : j ≤ k), (p.tr h).app _ y'' = (p.tr h).app _ y' := by
  obtain ⟨j, y', hy⟩ := p.surj T y
  exact ⟨j, y', hy, fun y'' h => p.inj j T y'' y' (h.trans hy.symm)⟩

end Hom

/-! ### Definition 14.3 for general `G` -/

/-- A functor of monoids on a category `C` (a monoid or group scheme `G` over `S`, seen as a
functor). -/
structure MonoidPresheaf.{a, b, c} (C : Type a) [Category.{b} C] where
  /-- The underlying functor. -/
  F : Cᵒᵖ ⥤ Type c
  [mon : ∀ U, Monoid (F.obj U)]
  map_one : ∀ {U V : Cᵒᵖ} (f : U ⟶ V), F.map f 1 = 1
  map_mul : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (g h : F.obj U), F.map f (g * h) = F.map f g * F.map f h

attribute [instance] MonoidPresheaf.mon

/-- **Definition 14.3 (i).** A categorical action of `G` on the functor `X`. -/
structure CatAction {C : Type*} [Category C] (G : MonoidPresheaf C) (X : Cᵒᵖ ⥤ Type w) where
  /-- The action on points. -/
  smul : ∀ {U : Cᵒᵖ}, G.F.obj U → X.obj U → X.obj U
  one_smul : ∀ {U : Cᵒᵖ} (x : X.obj U), smul 1 x = x
  mul_smul : ∀ {U : Cᵒᵖ} (g h : G.F.obj U) (x : X.obj U), smul (g * h) x = smul g (smul h x)
  map_smul : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (g : G.F.obj U) (x : X.obj U),
    X.map f (smul g x) = smul (G.F.map f g) (X.map f x)

/-- The restriction of a monoid functor on the site to affine schemes. -/
noncomputable def MonoidPresheaf.toAff (G : MonoidPresheaf.{u + 1, u, u} SITE) : MonoidPresheaf.{u + 1, u, u} AFF where
  F := (incl).op ⋙ G.F
  mon U := G.mon _
  map_one f := G.map_one _
  map_mul f g h := G.map_mul _ g h

section Action

variable {P : ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) → Prop} {X : (BigAffineFppf B S hS)ᵒᵖ ⥤ Type w}
variable (p : IndPresentation.{u, v, w} P X) (G : MonoidPresheaf.{u + 1, u, u} (BigFppfOver B S hS))

/-- **Definition 14.3 (ii).** A collection of actions `G ×_S X_i → X_i` compatible with the
transition maps, for a general `G`. -/
structure IndActionG where
  /-- The actions on the terms. -/
  act : ∀ i, CatAction G (p.obj i)
  tr_smul : ∀ {i j : p.I} (h : i ≤ j) {U : SITEᵒᵖ} (g : G.F.obj U)
    (x : (p.obj i).obj U), (p.tr h).app U ((act i).smul g x) = (act j).smul g ((p.tr h).app U x)

variable {p}
variable {G}

lemma IndActionG.smul_wd (a : IndActionG p G) {T : AFF}
    (g : G.F.obj (op ((incl).obj T))) {i j : p.I} {x : (p.obj i).obj (op ((incl).obj T))}
    {y : (p.obj j).obj (op ((incl).obj T))} (hxy : p.π i T x = p.π j T y) :
    p.π i T ((a.act i).smul g x) = p.π j T ((a.act j).smul g y) := by
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  have h : p.π k T ((p.tr hik).app _ x) = p.π k T ((p.tr hjk).app _ y) := by
    rw [p.π_tr, p.π_tr, hxy]
  obtain ⟨l, hkl, e⟩ := p.inj k T _ _ h
  rw [← p.π_tr (hik.trans hkl), ← p.π_tr (hjk.trans hkl), a.tr_smul, a.tr_smul, p.tr_trans hik hkl,
    p.tr_trans hjk hkl]
  congr 2

/-- **Definition 14.3 (ii).** An ind-action of a general `G` gives birth to a categorical action of
`G` on `X` (Definition 14.3 (i)). -/
noncomputable def IndActionG.toCatAction (a : IndActionG p G) : CatAction G.toAff X where
  smul {U} g x :=
    p.π (p.surj (unop U) x).choose (unop U)
      (((a.act _).smul g (p.surj (unop U) x).choose_spec.choose))
  one_smul {U} x := by
    have h := (p.surj (unop U) x).choose_spec.choose_spec
    exact (congrArg _ ((a.act _).one_smul _)).trans h
  mul_smul {U} g g' x := by
    have h := (p.surj (unop U) x).choose_spec.choose_spec
    set i := (p.surj (unop U) x).choose
    set y := (p.surj (unop U) x).choose_spec.choose
    refine (congrArg _ ((a.act i).mul_smul g g' y)).trans ?_
    refine a.smul_wd g ?_
    exact (p.surj _ _).choose_spec.choose_spec.symm
  map_smul {U V} f g x := by
    have h := (p.surj (unop U) x).choose_spec.choose_spec
    set i := (p.surj (unop U) x).choose
    set y := (p.surj (unop U) x).choose_spec.choose
    have e := p.π_map i f.unop ((a.act i).smul g y)
    refine e.symm.trans ?_
    have e2 := (a.act i).map_smul ((incl).map f.unop).op g y
    refine (congrArg (p.π i (unop V)) e2).trans ?_
    refine a.smul_wd _ ?_
    rw [p.π_map, h]
    exact (p.surj _ _).choose_spec.choose_spec.symm

end Action

/-! ### Proposition 14.4: the ind-scheme variant -/

section Attractor

variable {M : Type u} [AddCommMonoid M] [Countable M] {P : ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) → Prop}
variable {X : (BigAffineFppf B S hS)ᵒᵖ ⥤ Type u} {p : IndPresentation.{u, v, u} P X}
variable (a : IndAction M p) (N : AddSubmonoid M)

/-- **Proposition 14.4**, resp. ind-schemes. If each `X_i^N` is represented by a scheme `Z_i`, the
attractor functor on `(Aff/S)` is the ind-scheme `colim_i Z_i`. -/
theorem isIndScheme_attractor {Z : p.I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (r : ∀ i, RepresentsAttractor (a.act i) N (Z i)) (hZ : ∀ i, ∃ U : BigFppfOver B S hS, Nonempty (Z i ≅ yoneda.obj U)) :
    IsIndScheme.{u, v} (attractor a.toAction N) := by
  refine ⟨{ I := p.I, obj := Z, prop := hZ
            tr := fun h => repAttractorMap ⟨p.tr h, a.tr_smul h⟩ N (r _) (r _)
            tr_refl := fun i => ?_
            tr_trans := fun h₁ h₂ => ?_
            closed := fun h => isClosedImm_indAttractor a N r h
            π := fun i T z => indPt a N i (((r i).equiv _) z)
            π_map := fun i T T' s z => ?_
            π_tr := fun h T z => ?_
            surj := fun T ψ => ?_
            inj := fun i T z z' e => ?_ }⟩
  · ext T z
    change ((r i).equiv (unop T)).symm (((r i).equiv (unop T) z).push ⟨p.tr (le_refl i), _⟩) = z
    refine ((r i).equiv (unop T)).symm_apply_eq.mpr ?_
    refine AttractorPt.ext ?_
    funext T' t b
    change (p.tr (le_refl i)).app _ _ = _
    rw [p.tr_refl]
    rfl
  · rename_i i j k
    ext T z
    change ((r k).equiv (unop T)).symm (((r i).equiv (unop T) z).push ⟨p.tr (h₁.trans h₂), _⟩) =
      ((r k).equiv (unop T)).symm (((r j).equiv (unop T) (((r j).equiv (unop T)).symm
        (((r i).equiv (unop T) z).push ⟨p.tr h₁, _⟩))).push ⟨p.tr h₂, _⟩)
    rw [Equiv.apply_symm_apply]
    congr 1
    refine AttractorPt.ext ?_
    funext T' t b
    change (p.tr (h₁.trans h₂)).app _ _ = (p.tr h₂).app _ ((p.tr h₁).app _ _)
    rw [p.tr_trans h₁ h₂]
    rfl
  · refine AttractorPt.ext ?_
    funext T'' t b
    change p.π i T'' (((r i).equiv _ ((Z i).map ((incl).map s).op z)).app ((incl).map t) b) =
      p.π i T'' (((r i).equiv _ z).app ((incl).map (t ≫ s)) b)
    rw [(r i).naturality]
    rfl
  · rename_i i j
    refine AttractorPt.ext ?_
    funext T'' t b
    change p.π j T'' (((r j).equiv _ (((r j).equiv _).symm (((r i).equiv _ z).push ⟨p.tr h, _⟩))).app
      ((incl).map t) b) = p.π i T'' (((r i).equiv _ z).app ((incl).map t) b)
    rw [Equiv.apply_symm_apply]
    exact p.π_tr h T'' _
  · obtain ⟨j, φ, h⟩ := exists_indPt_eq a N ψ
    exact ⟨j, ((r j).equiv _).symm φ, by
      change indPt a N j (((r j).equiv _) (((r j).equiv _).symm φ)) = ψ
      rw [Equiv.apply_symm_apply, h]⟩
  · obtain ⟨j, hij, e'⟩ := exists_indPt_inj a N i _ _ e
    exact ⟨j, hij, congrArg ((r j).equiv _).symm e'⟩

end Attractor

end AlgMag
