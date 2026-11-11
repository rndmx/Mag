/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.GroupTheory.QuotientGroup.Defs
import AlgMag.Representation
import AlgMag.AlgebraicSpace

/-!
# Fixed-point-reflecting atlases

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026) 126–201, §6, and the statement of
Proposition 8.1.

Let `M` be an abelian group. Every monoid map from `M` to a ring lands in the units, so the points
of `𝔸(M)` are those of `D(M)`, and an `AlgMag.AAction` of a group `M` is an action of `D(M)`. The
inclusion `D(M/Z) ⊆ D(M)` is dual to `M → M/Z`, whence `AlgMag.quotientAction`.

## Main definitions (Definition 6.1)

* `AlgMag.IsEquivariant`, `AlgMag.fixedPoints`, `AlgMag.fixedMap`.
* `AlgMag.IsFPR`, `AlgMag.IsZFPR`, `AlgMag.IsStronglyFPR`: (i), (ii), (iii).
* `AlgMag.IsEquivariantAtlas`, `AlgMag.IsSAffineAtlas`: (iv).
* `AlgMag.IsZFPRAtlas`, `AlgMag.IsStronglyFPRAtlas`: (v), (vi).
* `AlgMag.Prop81Statement`, `AlgMag.Prop81StatementFG`: Proposition 8.1, as statements.

## Main results

* `AlgMag.isFPR_iff`: the pointwise form of fixed-point reflection.
* `AlgMag.IsFPR.of_isPullback`, `AlgMag.IsZFPR.of_isPullback`: the FPR part of Lemma 6.7 (i).
* `AlgMag.hasFiniteAffineDecomposition_iff`: Remark 6.2.
* `AlgMag.AttractorPt.toPoint_mem_fixedPoints`: `X^Z → X` lands in `X^{D(M/Z)}`, one half of
  the identification of Proposition 3.35.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe w u v

namespace AlgMag

section General

variable {C : Type*} [Category.{v} C] {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}}
variable {M P : Type*} [AddCommMonoid M] [AddCommMonoid P]
variable {F : Cᵒᵖ ⥤ Type u}

/-- The action of `𝔸(P)` induced along the morphism `𝔸(P) → 𝔸(M)` dual to `φ : M → P`. -/
def AAction.comap (φ : M →+ P) (act : AAction 𝒪 M F) : AAction 𝒪 P F where
  smul h x := act.smul (h.comp (AddMonoidHom.toMultiplicative φ)) x
  one_smul x := by
    rw [MonoidHom.one_comp, act.one_smul]
  mul_smul g h x := by
    rw [MonoidHom.mul_comp, act.mul_smul]
  map_smul f h x := act.map_smul f _ x

/-- **Definition 6.1**, preamble: `f` is equivariant. -/
def IsEquivariant {U X : Cᵒᵖ ⥤ Type u} (actU : AAction 𝒪 M U) (actX : AAction 𝒪 M X)
    (f : U ⟶ X) : Prop :=
  ∀ {T : Cᵒᵖ} (h : APt 𝒪 M T) (x : U.obj T), f.app T (actU.smul h x) = actX.smul h (f.app T x)

lemma IsEquivariant.comap {U X : Cᵒᵖ ⥤ Type u} {actU : AAction 𝒪 M U} {actX : AAction 𝒪 M X}
    {f : U ⟶ X} (hf : IsEquivariant actU actX f) (φ : M →+ P) :
    IsEquivariant (actU.comap φ) (actX.comap φ) f :=
  fun _ x => hf _ x

/-- The fixed-point functor `X^{D(M)}`: the points `x ∈ X(T)` such that `h • x|_{T'} = x|_{T'}` for
every `T' → T` and every `h ∈ D(M)(T')`. -/
def fixedPoints (act : AAction 𝒪 M F) : Subfunctor F where
  obj T := {x | ∀ {T' : Cᵒᵖ} (s : T ⟶ T') (h : APt 𝒪 M T'),
    act.smul h (F.map s x) = F.map s x}
  map {T T'} i x hx {T''} s h := by
    have := hx (i ≫ s) h
    rwa [Functor.map_comp_apply] at this

/-- The morphism `U^{D(M)} → X^{D(M)}` induced by an equivariant morphism. -/
def fixedMap {U X : Cᵒᵖ ⥤ Type u} {actU : AAction 𝒪 M U} {actX : AAction 𝒪 M X} {f : U ⟶ X}
    (hf : IsEquivariant actU actX f) :
    (fixedPoints actU).toFunctor ⟶ (fixedPoints actX).toFunctor where
  app T := ↾ fun x => ⟨f.app T x.1, fun {T'} s h => by
    rw [← NatTrans.naturality_apply, ← hf]
    exact congrArg (f.app T') (x.2 s h)⟩
  naturality T T' s := by
    ext x
    refine Subtype.ext ?_
    change f.app T' (U.map s x.1) = X.map s (f.app T x.1)
    exact NatTrans.naturality_apply f s x.1

/-- **Definition 6.1 (i).** `f` is fixed-point reflecting: the canonical morphism
`U^{D(M)} → U ×_X X^{D(M)}` is an isomorphism, that is, the square with sides `U^{D(M)} → X^{D(M)}`,
`U^{D(M)} → U`, `X^{D(M)} → X`, `U → X` is cartesian. -/
def IsFPR {U X : Cᵒᵖ ⥤ Type u} {actU : AAction 𝒪 M U} {actX : AAction 𝒪 M X} {f : U ⟶ X}
    (hf : IsEquivariant actU actX f) : Prop :=
  IsPullback (fixedMap hf) (fixedPoints actU).ι (fixedPoints actX).ι f

/-- Pointwise form of **Definition 6.1 (i)**: `f` is FPR iff a point of `U` whose image in `X` is
fixed is itself fixed. -/
theorem isFPR_iff {U X : Cᵒᵖ ⥤ Type u} {actU : AAction 𝒪 M U} {actX : AAction 𝒪 M X} {f : U ⟶ X}
    (hf : IsEquivariant actU actX f) :
    IsFPR hf ↔ ∀ (T : Cᵒᵖ) (x : U.obj T),
      f.app T x ∈ (fixedPoints actX).obj T → x ∈ (fixedPoints actU).obj T := by
  constructor
  · intro H T x hx
    obtain ⟨y, -, hy⟩ := Types.exists_of_isPullback (H.app T)
      (⟨f.app T x, hx⟩ : (fixedPoints actX).toFunctor.obj T) x rfl
    have hy' : y.1 = x := hy
    intro T' s h
    rw [← hy']
    exact y.2 s h
  · intro H
    refine IsPullback.of_forall_isPullback_app fun T => ?_
    refine (Types.isPullback_iff _ _ _ _).mpr ⟨?_, ?_, ?_⟩
    · ext x
      rfl
    · rintro x y ⟨-, h⟩
      exact Subtype.ext h
    · intro x₂ x₃ e
      have e' : x₂.1 = f.app T x₃ := e
      have hx₃ : x₃ ∈ (fixedPoints actU).obj T := H T x₃ (e' ▸ x₂.2)
      exact ⟨⟨x₃, hx₃⟩, Subtype.ext e'.symm, rfl⟩

/-- A composite of FPR morphisms is FPR (immediate; not stated in the paper). -/
theorem IsFPR.comp {U V X : Cᵒᵖ ⥤ Type u} {actU : AAction 𝒪 M U} {actV : AAction 𝒪 M V}
    {actX : AAction 𝒪 M X} {f : U ⟶ V} {g : V ⟶ X} {hf : IsEquivariant actU actV f}
    {hg : IsEquivariant actV actX g} (Hf : IsFPR hf) (Hg : IsFPR hg)
    (hfg : IsEquivariant actU actX (f ≫ g)) : IsFPR hfg :=
  (isFPR_iff hfg).mpr fun T x hx =>
    (isFPR_iff hf).mp Hf T x ((isFPR_iff hg).mp Hg T (f.app T x) hx)

/-- The FPR part of **Lemma 6.7 (i)**: the base change `U ×_X X' → X'` of an FPR morphism along
an equivariant morphism `X' → X` is FPR. Here `W` is any pullback, with an action for which both
projections are equivariant. No affineness of `X' → X` is needed for this part; the atlas part of
Lemma 6.7 is not treated here. -/
theorem IsFPR.of_isPullback {W U X' X : Cᵒᵖ ⥤ Type u} {actW : AAction 𝒪 M W}
    {actU : AAction 𝒪 M U} {actX' : AAction 𝒪 M X'} {actX : AAction 𝒪 M X}
    {a : W ⟶ U} {b : W ⟶ X'} {f : U ⟶ X} {g : X' ⟶ X}
    (hpb : IsPullback a b f g) (ha : IsEquivariant actW actU a) (hb : IsEquivariant actW actX' b)
    {hf : IsEquivariant actU actX f} (hg : IsEquivariant actX' actX g) (Hf : IsFPR hf) :
    IsFPR hb := by
  refine (isFPR_iff hb).mpr fun T y hy => ?_
  have hw : f.app T (a.app T y) = g.app T (b.app T y) :=
    ConcreteCategory.congr_hom (NatTrans.congr_app hpb.w T) y
  have hfix : a.app T y ∈ (fixedPoints actU).obj T := by
    refine (isFPR_iff hf).mp Hf T _ ?_
    rw [hw]
    exact ((fixedMap hg).app T ⟨_, hy⟩).2
  intro T' s h
  refine Types.ext_of_isPullback (hpb.app T') ?_ ?_
  · rw [ha, NatTrans.naturality_apply]
    exact hfix s h
  · rw [hb, NatTrans.naturality_apply]
    exact hy s h

end General

section Group

variable {C : Type*} [Category.{v} C] {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}}
variable {M : Type*} [AddCommGroup M] {F : Cᵒᵖ ⥤ Type u}

/-- The action of `D(M/Z)` induced by an action of `D(M)`, through `D(M/Z) ⊆ D(M)`. -/
abbrev quotientAction (act : AAction 𝒪 M F) (Z : AddSubgroup M) : AAction 𝒪 (M ⧸ Z) F :=
  act.comap (QuotientAddGroup.mk' Z)

/-- **Definition 6.1 (ii).** `f` is `Z`-FPR: it is FPR for the induced action of `D(M/Z)`. -/
def IsZFPR {U X : Cᵒᵖ ⥤ Type u} {actU : AAction 𝒪 M U} {actX : AAction 𝒪 M X} {f : U ⟶ X}
    (hf : IsEquivariant actU actX f) (Z : AddSubgroup M) : Prop :=
  IsFPR (hf.comap (QuotientAddGroup.mk' Z))

/-- **Definition 6.1 (iii).** `f` is strongly-FPR: it is `Z`-FPR for all subgroups `Z ⊆ M`. -/
def IsStronglyFPR {U X : Cᵒᵖ ⥤ Type u} {actU : AAction 𝒪 M U} {actX : AAction 𝒪 M X} {f : U ⟶ X}
    (hf : IsEquivariant actU actX f) : Prop :=
  ∀ Z : AddSubgroup M, IsZFPR hf Z

/-- The FPR part of **Lemma 6.7 (i)**, for `Z`-FPR morphisms. -/
theorem IsZFPR.of_isPullback {W U X' X : Cᵒᵖ ⥤ Type u} {actW : AAction 𝒪 M W}
    {actU : AAction 𝒪 M U} {actX' : AAction 𝒪 M X'} {actX : AAction 𝒪 M X}
    {a : W ⟶ U} {b : W ⟶ X'} {f : U ⟶ X} {g : X' ⟶ X}
    (hpb : IsPullback a b f g) (ha : IsEquivariant actW actU a) (hb : IsEquivariant actW actX' b)
    {hf : IsEquivariant actU actX f} (hg : IsEquivariant actX' actX g) {Z : AddSubgroup M}
    (Hf : IsZFPR hf Z) : IsZFPR hb Z :=
  IsFPR.of_isPullback (hf := hf.comap _) hpb (ha.comap _) (hb.comap _) (hg.comap _) Hf

/-- One half of the identification of **Proposition 3.35**: the morphism `X^Z → X` lands in the
fixed points of `D(M/Z)`. This half needs no finiteness of `M`. -/
theorem AttractorPt.toPoint_mem_fixedPoints {act : AAction 𝒪 M F} {Z : AddSubgroup M} {T : C}
    (φ : AttractorPt act Z.toAddSubmonoid T) :
    φ.toPoint ∈ (fixedPoints (quotientAction act Z)).obj (op T) := by
  intro T' s h
  have hnat := φ.naturality s.unop (𝟙 T) 1
  have hone : APt.res (𝒪 := 𝒪) (P := Z.toAddSubmonoid) s.unop.op 1 = 1 := by
    ext p; simp
  rw [Category.comp_id, hone] at hnat
  have heq := φ.equivariant s.unop
    (h.comp (AddMonoidHom.toMultiplicative (QuotientAddGroup.mk' Z))) 1
  have htriv : APt.toMagnet Z.toAddSubmonoid
      (h.comp (AddMonoidHom.toMultiplicative (QuotientAddGroup.mk' Z))) * 1 = 1 := by
    refine MonoidHom.ext fun n => ?_
    have hn : QuotientAddGroup.mk' Z ((Multiplicative.toAdd n : Z.toAddSubmonoid) : M) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).mpr (Multiplicative.toAdd n).2
    have e : AddMonoidHom.toMultiplicative (QuotientAddGroup.mk' Z)
        (Multiplicative.ofAdd ((Multiplicative.toAdd n : Z.toAddSubmonoid) : M)) = 1 :=
      congrArg Multiplicative.ofAdd hn
    have : h (AddMonoidHom.toMultiplicative (QuotientAddGroup.mk' Z)
        (Multiplicative.ofAdd ((Multiplicative.toAdd n : Z.toAddSubmonoid) : M))) = 1 := by
      rw [e, map_one]
    rw [MonoidHom.mul_apply, MonoidHom.one_apply, mul_one]
    exact this
  rw [htriv] at heq
  have hs : F.map s (AttractorPt.toPoint φ) = φ.app s.unop 1 := hnat.symm
  rw [hs]
  exact heq.symm

end Group

section Site

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {M : Type w} [AddCommGroup M]

/-- The structure morphism to `S` of an object of the big fppf site of `S`. -/
abbrev structMap (U : BigFppfOver B S hS) : (BigFppfOver.toScheme B S hS).obj U ⟶ S := U.hom.hom

/-- An open `V` of the `S`-scheme `U` is stable under the action: a point of `U` factoring through
`V` still does so after acting by any point of `D(M)`. -/
def IsStableOpen {U : BigFppfOver B S hS} (actU : AAction (fppfO B S hS) M (yoneda.obj U))
    (V : ((BigFppfOver.toScheme B S hS).obj U).Opens) : Prop :=
  ∀ {T : BigFppfOver B S hS} (t : T ⟶ U) (h : APt (fppfO B S hS) M (op T)),
    Set.range ((BigFppfOver.toScheme B S hS).map t) ⊆ V →
    Set.range ((BigFppfOver.toScheme B S hS).map
      (actU.smul h t : T ⟶ U)) ⊆ V

/-- `U` is the disjoint union, indexed by `A`, of `D(M)_S`-stable `S`-affine schemes
(Definition 6.1 (iv)); the pieces are given as a partition of `U` into open subschemes. -/
structure IsAffineDecomposition {U : BigFppfOver B S hS}
    (actU : AAction (fppfO B S hS) M (yoneda.obj U)) {A : Type u}
    (V : A → ((BigFppfOver.toScheme B S hS).obj U).Opens) : Prop where
  disjoint : Pairwise (Function.onFun Disjoint V)
  iSup_eq_top : iSup V = ⊤
  stable : ∀ a, IsStableOpen actU (V a)
  isAffineHom : ∀ a, IsAffineHom ((V a).ι ≫ structMap U)

/-- `U` has an affine decomposition, with arbitrary index set. -/
def HasAffineDecomposition {U : BigFppfOver B S hS}
    (actU : AAction (fppfO B S hS) M (yoneda.obj U)) : Prop :=
  ∃ (A : Type u) (V : A → ((BigFppfOver.toScheme B S hS).obj U).Opens),
    IsAffineDecomposition actU V

/-- `U` has an affine decomposition with finite index set. -/
def HasFiniteAffineDecomposition {U : BigFppfOver B S hS}
    (actU : AAction (fppfO B S hS) M (yoneda.obj U)) : Prop :=
  ∃ (A : Type u) (_ : Finite A) (V : A → ((BigFppfOver.toScheme B S hS).obj U).Opens),
    IsAffineDecomposition actU V

/-- **Remark 6.2.** A finite disjoint union of `S`-affine schemes is `S`-affine, so `U` has a finite
decomposition iff `U` is `S`-affine, and then the decomposition may be taken to be a singleton
(the proof uses `A = PUnit`, `V = ⊤`). -/
theorem hasFiniteAffineDecomposition_iff {U : BigFppfOver B S hS}
    (actU : AAction (fppfO B S hS) M (yoneda.obj U)) :
    HasFiniteAffineDecomposition actU ↔ IsAffineHom (structMap U) := by
  constructor
  · rintro ⟨A, _, V, hV⟩
    refine ⟨fun W hW => ?_⟩
    have haff : ∀ a, IsAffineOpen (structMap U ⁻¹ᵁ W ⊓ V a) := by
      intro a
      have := hV.isAffineHom a
      have h1 : IsAffineOpen (((V a).ι ≫ structMap U) ⁻¹ᵁ W) :=
        IsAffineHom.isAffine_preimage _ hW
      have h2 := h1.image_of_isOpenImmersion (V a).ι
      have e : (V a).ι ''ᵁ (((V a).ι ≫ structMap U) ⁻¹ᵁ W) = structMap U ⁻¹ᵁ W ⊓ V a := by
        rw [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
          Scheme.Opens.opensRange_ι, inf_comm]
      rwa [e] at h2
    have hd : Pairwise (Function.onFun Disjoint fun a => structMap U ⁻¹ᵁ W ⊓ V a) :=
      fun a b hab => (hV.disjoint hab).mono inf_le_right inf_le_right
    have := IsAffineOpen.iSup_of_disjoint haff hd
    rwa [← inf_iSup_eq, hV.iSup_eq_top, inf_top_eq] at this
  · intro h
    refine ⟨PUnit, inferInstance, fun _ => ⊤, ⟨?_, ?_, ?_, ?_⟩⟩
    · intro a b hab
      exact absurd (Subsingleton.elim a b) hab
    · exact iSup_const
    · intro a T t g _ x hx
      trivial
    · intro a
      have : IsIso (⊤ : ((BigFppfOver.toScheme B S hS).obj U).Opens).ι :=
        isIso_of_isOpenImmersion_of_opensRange_eq_top _ (Scheme.Opens.opensRange_ι _)
      infer_instance

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Definition 6.1 (iv).** `f : U → X` is an equivariant atlas: it is equivariant, étale and
surjective, and `U` is a disjoint union of `D(M)_S`-stable `S`-affine schemes. Étale and surjective
are tested after every representable base change, as in `AlgebraicGeometry.IsAlgebraicSpace`. -/
structure IsEquivariantAtlas {U : BigFppfOver B S hS} (actU : AAction (fppfO B S hS) M (yoneda.obj U))
    (actX : AAction (fppfO B S hS) M X) (f : yoneda.obj U ⟶ X) : Prop where
  equivariant : IsEquivariant actU actX f
  surjective : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f
  etale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f
  decomposition : HasAffineDecomposition actU

/-- **Definition 6.1 (iv).** The equivariant atlas is `S`-affine: the index set may be chosen
finite. By `AlgMag.hasFiniteAffineDecomposition_iff` this means that `U` is an `S`-affine scheme
(Remark 6.2). -/
def IsSAffineAtlas {U : BigFppfOver B S hS} (actU : AAction (fppfO B S hS) M (yoneda.obj U))
    (actX : AAction (fppfO B S hS) M X) (f : yoneda.obj U ⟶ X) : Prop :=
  IsEquivariantAtlas actU actX f ∧ HasFiniteAffineDecomposition actU

/-- **Definition 6.1 (v).** `f` is a `Z`-FPR atlas. -/
structure IsZFPRAtlas {U : BigFppfOver B S hS} (actU : AAction (fppfO B S hS) M (yoneda.obj U))
    (actX : AAction (fppfO B S hS) M X) (f : yoneda.obj U ⟶ X) (Z : AddSubgroup M) : Prop where
  atlas : IsEquivariantAtlas actU actX f
  isZFPR : IsZFPR atlas.equivariant Z

/-- **Definition 6.1 (vi).** `f` is a strongly-FPR atlas. -/
structure IsStronglyFPRAtlas {U : BigFppfOver B S hS}
    (actU : AAction (fppfO B S hS) M (yoneda.obj U))
    (actX : AAction (fppfO B S hS) M X) (f : yoneda.obj U ⟶ X) : Prop where
  atlas : IsEquivariantAtlas actU actX f
  isStronglyFPR : IsStronglyFPR atlas.equivariant

/-- A strongly-FPR atlas is a `Z`-FPR atlas for all `Z`. -/
lemma IsStronglyFPRAtlas.isZFPRAtlas {U : BigFppfOver B S hS}
    {actU : AAction (fppfO B S hS) M (yoneda.obj U)} {actX : AAction (fppfO B S hS) M X}
    {f : yoneda.obj U ⟶ X} (h : IsStronglyFPRAtlas actU actX f) (Z : AddSubgroup M) :
    IsZFPRAtlas actU actX f Z :=
  ⟨h.atlas, h.isStronglyFPR Z⟩

/-- There exists a `Z`-FPR atlas for `X` under the action of `D(M)_S`. -/
def ExistsZFPRAtlas (actX : AAction (fppfO B S hS) M X) (Z : AddSubgroup M) : Prop :=
  ∃ (U : BigFppfOver B S hS) (actU : AAction (fppfO B S hS) M (yoneda.obj U))
    (f : yoneda.obj U ⟶ X), IsZFPRAtlas actU actX f Z

/-- The conclusion of **Proposition 8.1**: the attractor `X^Z` is represented by a presheaf `Y`
which is an algebraic space, whose inclusion into `X`, the morphism `X^Z → X` of §3, is a closed
immersion (tested after every representable base change). -/
def AttractorIsClosedSubspace (actX : AAction (fppfO B S hS) M X) (Z : AddSubgroup M) : Prop :=
  ∃ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (i : Y ⟶ X)
    (r : RepresentsAttractor actX Z.toAddSubmonoid Y),
    IsAlgebraicSpace B S hS Y ∧
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) i ∧
    ∀ (T : BigFppfOver B S hS) (y : Y.obj (op T)), i.app (op T) y = (r.equiv T y).toPoint

end Site

/-- **Proposition 8.1**, for an arbitrary abelian group `M`. If `X` has a `Z`-FPR atlas under
`D(M)_S`, then `X^Z` is representable by a closed subspace of `X`.

The hypothesis that `D(M)_T` is an object of the site for every `T`, is not in the paper, whose
category of schemes has no size cutoff. Here attractor points are tested only on objects of the
site, and for `M` too large relative to the cutoff of `B` this test sees too little. -/
def Prop81Statement : Prop :=
  ∀ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (M : Type w) [AddCommGroup M]
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS X)
    (actX : AAction (fppfO B S hS) M X) (Z : AddSubgroup M)
    (_ : ∀ T : BigFppfOver B S hS,
      Nonempty (UniversalPoint (fppfO B S hS) (⊤ : AddSubmonoid M) T)),
    ExistsZFPRAtlas actX Z → AttractorIsClosedSubspace actX Z

/-- **Proposition 8.1** for `M` finitely generated, the case covered by Proposition 3.35 as printed;
no size hypothesis is imposed, since `D(M)_T` is then finitely presented over `T` and should
belong to the site (this is not proved here). -/
def Prop81StatementFG : Prop :=
  ∀ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (M : Type w) [AddCommGroup M]
    [AddGroup.FG M]
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS X)
    (actX : AAction (fppfO B S hS) M X) (Z : AddSubgroup M),
    ExistsZFPRAtlas actX Z → AttractorIsClosedSubspace actX Z

end AlgMag

#print axioms AlgMag.isFPR_iff
#print axioms AlgMag.IsZFPR.of_isPullback
#print axioms AlgMag.hasFiniteAffineDecomposition_iff
#print axioms AlgMag.AttractorPt.toPoint_mem_fixedPoints
#print axioms AlgMag.Prop81Statement
#print axioms AlgMag.Prop81StatementFG
