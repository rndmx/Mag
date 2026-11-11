/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec13General
import StacksFrontier.AlgebraicGeometry.Spaces.EquivalenceRelations
import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
import StacksFrontier.AlgebraicGeometry.Spaces.AtlasMorphismDescent
import StacksFrontier.AlgebraicGeometry.Size.Cutoff
import StacksFrontier.AlgebraicGeometry.Spaces.QuotientAlgebraic
import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafAlgebraic
import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEffectiveDescent
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleDescent
import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
import StacksFrontier.AlgebraicGeometry.Spaces.Category
import AlgMag.AlgebraicSpace
import AlgMag.Representation
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Dilatations of algebraic spaces and Proposition 13.1 over spaces

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026) 126-201, §13, on the big fppf site
`BigFppfOver B S hS`. The scheme version is `AlgMag.Sec13General`.

## Main definitions

* `AlgMag.DilSp.Reg`, `AlgMag.DilSp.SpReg`: `S'`-regular objects and sheaves (via atlases).
* `AlgMag.DilSp.IsSpDil`: `Bl_Y^D X`, by its universal property among `S'`-regular objects.

## Main results

* `AlgMag.DilSp.exists_spDilatation`: existence of `Bl_Y^D X` as an algebraic space, affine over
  `X`: the quotient of the dilatation of an atlas, affine by étale descent
  (`isEffectiveDescentAlongSurjectiveEtale_isAffineHom`).
* `AlgMag.DilSp.IsSpDil.exists_iso`: uniqueness.
* `AlgMag.DilSp.blAction`, `AlgMag.DilSp.smB_map`: `𝔸(M)_S` acts on `Bl_Y^D X`, equivariantly.
* `AlgMag.DilSp.attractor_isSpDil`, `AlgMag.DilSp.prop13_1_spaces`: **Proposition 13.1**.
-/

universe u

section PartA

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry


namespace AlgMag.DilSp

open Dil

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc pullback.lift_snd_assoc

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc pullback.lift_snd_assoc

variable {S : Scheme.{u}} {I : S.IdealSheafData}

/-- The groupoid `R ⇉ U` of an étale chart, in the only form needed here. -/
structure ChartRel (I : S.IdealSheafData) {U R Y : Over S} (j : Y ⟶ U) (s t : R ⟶ U) : Prop where
  mono : ∀ ⦃T : Over S⦄ (r r' : T ⟶ R), r ≫ s = r' ≫ s → r ≫ t = r' ≫ t → r = r'
  refl : ∀ ⦃T : Over S⦄ (x : T ⟶ U), ∃ r : T ⟶ R, r ≫ s = x ∧ r ≫ t = x
  symm : ∀ ⦃T : Over S⦄ (r : T ⟶ R), ∃ r' : T ⟶ R, r' ≫ s = r ≫ t ∧ r' ≫ t = r ≫ s
  trans : ∀ ⦃T : Over S⦄ (r r' : T ⟶ R), r ≫ t = r' ≫ s →
    ∃ r'' : T ⟶ R, r'' ≫ s = r ≫ s ∧ r'' ≫ t = r' ≫ t
  factors : ∀ ⦃T : Over S⦄ (r : T ⟶ R), Factors I j (r ≫ s) → Factors I j (r ≫ t)

variable {U R Y B : Over S} {j : Y ⟶ U} {s t : R ⟶ U} {b : B ⟶ U}

/-- `R' = B ×_{U,s} R`, the pull-back of the dilatation along `s`. -/
noncomputable abbrev Rp (b : B ⟶ U) (s : R ⟶ U) : Over S := pullback b s

lemma flat_left_of_isPullback {P A C D : Over S} {f : P ⟶ A} {g : P ⟶ C} {h : A ⟶ D} {k : C ⟶ D}
    (sq : IsPullback f g h k) [Flat k.left] : Flat f.left := by
  have sq' : IsPullback f.left g.left h.left k.left := sq.map (Over.forget S)
  exact MorphismProperty.of_isPullback (P := @Flat) sq'.flip inferInstance

section

variable (hR : ChartRel I j s t) (hD : IsDilatation I j b) [Flat s.left]

include hR hD in
lemma exists_tr : ∃ l : Rp b s ⟶ B, l ≫ b = pullback.snd b s ≫ t := by
  have : Flat (pullback.fst b s).left :=
    flat_left_of_isPullback (IsPullback.of_hasPullback b s)
  refine hD.exists_lift (hD.reg.of_flat (pullback.fst b s)) _ (fun _ _ => trivial) ?_
  refine hR.factors _ ?_
  rw [← pullback.condition]
  exact hD.factors.comp j _

/-- The second leg `R' ⟶ B`. -/
noncomputable def tr : Rp b s ⟶ B := (exists_tr hR hD).choose

@[reassoc]
lemma tr_map : tr hR hD ≫ b = pullback.snd b s ≫ t := (exists_tr hR hD).choose_spec

include hD in
lemma rp_regular : IsRegular I (Rp b s) := by
  have : Flat (pullback.fst b s).left :=
    flat_left_of_isPullback (IsPullback.of_hasPullback b s)
  exact hD.reg.of_flat (pullback.fst b s)

/-- Transport of a lift along an arrow of the groupoid. -/
noncomputable def φ {T : Over S} (x : T ⟶ B) (r : T ⟶ R) (h : x ≫ b = r ≫ s) : T ⟶ B :=
  pullback.lift x r h ≫ tr hR hD

@[reassoc]
lemma φ_map {T : Over S} (x : T ⟶ B) (r : T ⟶ R) (h : x ≫ b = r ≫ s) :
    φ hR hD x r h ≫ b = r ≫ t := by
  simp [φ, tr_map]

lemma comp_φ {T T' : Over S} (v : T' ⟶ T) (x : T ⟶ B) (r : T ⟶ R) (h : x ≫ b = r ≫ s) :
    v ≫ φ hR hD x r h = φ hR hD (v ≫ x) (v ≫ r) (by simp [h]) := by
  rw [φ, φ, ← Category.assoc]
  congr 1
  apply pullback.hom_ext <;> simp

lemma φ_refl {T : Over S} (x : T ⟶ B) (r : T ⟶ R) (h : x ≫ b = r ≫ s) (h' : r ≫ t = r ≫ s) :
    φ hR hD x r h = x := by
  obtain ⟨δ, h1, h2⟩ := hR.refl b
  have hr : r = x ≫ δ := hR.mono _ _ (by simp [h1, h]) (by simp [h2, h', h])
  subst hr
  have key : φ hR hD (𝟙 B) δ (by simp [h1]) = 𝟙 B := hD.uniq hD.reg _ _ (by
    rw [φ_map, h2, Category.id_comp])
  have := comp_φ hR hD x (𝟙 B) δ (by simp [h1])
  rw [key] at this
  simpa using this.symm

lemma φ_trans {T : Over S} (x : T ⟶ B) (r r' r'' : T ⟶ R) (h : x ≫ b = r ≫ s)
    (h' : r ≫ t = r' ≫ s) (h'' : r'' ≫ s = r ≫ s) (h3 : r'' ≫ t = r' ≫ t) :
    φ hR hD (φ hR hD x r h) r' (by rw [φ_map, h']) =
      φ hR hD x r'' (by rw [h'', h]) := by
  -- the universal case, on the regular object `R' ×_{U} R`
  let q : Rp b s ⟶ U := pullback.snd b s ≫ t
  let W : Over S := pullback q s
  have : Flat (pullback.fst q s).left := flat_left_of_isPullback (IsPullback.of_hasPullback q s)
  have hW : IsRegular I W := (rp_regular (s := s) hD).of_flat (pullback.fst q s)
  let w₁ : W ⟶ R := pullback.fst q s ≫ pullback.snd b s
  let w₂ : W ⟶ R := pullback.snd q s
  have hw : w₁ ≫ t = w₂ ≫ s := by simpa [q, w₁, w₂] using (pullback.condition (f := q) (g := s))
  obtain ⟨w₃, e1, e2⟩ := hR.trans w₁ w₂ hw
  let x₀ : W ⟶ B := pullback.fst q s ≫ pullback.fst b s
  have hx₀ : x₀ ≫ b = w₁ ≫ s := by simp [x₀, w₁, pullback.condition]
  have key : φ hR hD (φ hR hD x₀ w₁ hx₀) w₂ (by rw [φ_map, hw]) =
      φ hR hD x₀ w₃ (by rw [e1, hx₀]) := hD.uniq hW _ _ (by rw [φ_map, φ_map, e2])
  let v : T ⟶ W := pullback.lift (pullback.lift x r h) r' (by simp [q, h'])
  have hv₀ : v ≫ x₀ = x := by simp [v, x₀]
  have hv₁ : v ≫ w₁ = r := by simp [v, w₁]
  have hv₂ : v ≫ w₂ = r' := by simp [v, w₂]
  have hv₃ : v ≫ w₃ = r'' := hR.mono _ _ (by rw [Category.assoc, e1, ← Category.assoc, hv₁, h''])
    (by rw [Category.assoc, e2, ← Category.assoc, hv₂, h3])
  have e := congrArg (v ≫ ·) key
  simp only [comp_φ] at e
  simp only [hv₀, hv₁, hv₂, hv₃] at e
  exact e

/-- `R' ⟶ B × B`. -/
noncomputable def relJ : Stacks.Groupoids.PreRelation (Rp b s) B :=
  prod.lift (pullback.fst b s) (tr hR hD)

@[simp] lemma relJ_target : (relJ hR hD).target = pullback.fst b s := by simp [relJ]
@[simp] lemma relJ_source : (relJ hR hD).source = tr hR hD := by simp [relJ]

instance relJ_mono : Mono (relJ hR hD) := by
  refine ⟨fun {T} f g e => ?_⟩
  have e1 : f ≫ pullback.fst b s = g ≫ pullback.fst b s := by
    simpa [relJ] using congrArg (· ≫ prod.fst) e
  have e2 : f ≫ tr hR hD = g ≫ tr hR hD := by
    simpa [relJ] using congrArg (· ≫ prod.snd) e
  apply pullback.hom_ext e1
  apply hR.mono
  · rw [Category.assoc, Category.assoc, ← pullback.condition, ← Category.assoc, e1, Category.assoc]
  · have := congrArg (· ≫ b) e2
    simpa [tr_map] using this

/-- The relation is: `y` is the transport of `x`. -/
lemma rel_iff {T : Over S} (x y : T ⟶ B) : (relJ hR hD).Rel x y ↔
    ∃ (r : T ⟶ R) (h : x ≫ b = r ≫ s), φ hR hD x r h = y := by
  constructor
  · rintro ⟨r, hx, hy⟩
    rw [relJ_target] at hx
    rw [relJ_source] at hy
    have hc : x ≫ b = (r ≫ pullback.snd b s) ≫ s := by
      rw [← hx, Category.assoc, Category.assoc, pullback.condition]
    refine ⟨r ≫ pullback.snd b s, hc, ?_⟩
    rw [← hy, φ]
    congr 1
    apply pullback.hom_ext <;> simp [hx]
  · rintro ⟨r, h, rfl⟩
    exact ⟨pullback.lift x r h, by simp, by simp [φ]⟩

lemma relJ_equiv : Stacks.Groupoids.IsPreEquivalenceRelation (relJ hR hD) := fun T => by
  refine ⟨fun x => ?_, fun {x y} h => ?_, fun {x y z} h h' => ?_⟩
  · obtain ⟨r, h1, h2⟩ := hR.refl (x ≫ b)
    exact (rel_iff hR hD x x).2 ⟨r, h1.symm, φ_refl hR hD x r _ (h2.trans h1.symm)⟩
  · obtain ⟨r, hh, rfl⟩ := (rel_iff hR hD x y).1 h
    obtain ⟨r', h1, h2⟩ := hR.symm r
    refine (rel_iff hR hD _ _).2 ⟨r', by rw [φ_map, h1], ?_⟩
    obtain ⟨r'', h3, h4⟩ := hR.refl (x ≫ b)
    rw [φ_trans hR hD x r r' r'' hh h1.symm (by rw [h3, hh]) (by rw [h4, h2, hh]),
      φ_refl hR hD x r'' _ (by rw [h3, h4])]
  · obtain ⟨r, hh, rfl⟩ := (rel_iff hR hD _ _).1 h
    obtain ⟨r', h1, rfl⟩ := (rel_iff hR hD _ _).1 h'
    have h2 : r ≫ t = r' ≫ s := by rw [← h1, φ_map]
    obtain ⟨r'', e1, e2⟩ := hR.trans r r' h2
    refine (rel_iff hR hD _ _).2 ⟨r'', by rw [e1, hh], ?_⟩
    exact (φ_trans hR hD x r r' r'' hh h2 e1 e2).symm

/-- Related points of `B` over the same point of `U` agree. -/
lemma eq_of_rel_of_map_eq {T : Over S} (x y : T ⟶ B) (h : (relJ hR hD).Rel x y)
    (e : x ≫ b = y ≫ b) : x = y := by
  obtain ⟨r, hh, rfl⟩ := (rel_iff hR hD _ _).1 h
  rw [φ_map] at e
  exact (φ_refl hR hD x r hh (e.symm.trans hh)).symm

end

end AlgMag.DilSp

end PartA

section PartB

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry


namespace AlgMag.DilSp

open Dil

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "C" => BigFppfOver B S hS
local notation "SCH" => BigFppfOver.toScheme B S hS
local notation "J" => BigFppfOver.topology B S hS

/-- A map out of `yoneda.obj A` into a sheaf, invariant on points, descends along a locally
surjective map. -/
lemma exists_desc_of_locSurj {P G : Cᵒᵖ ⥤ Type u} (hG : Presheaf.IsSheaf J G) {A : C}
    (a : yoneda.obj A ⟶ P) (hloc : Presheaf.IsLocallySurjective J a) (k : yoneda.obj A ⟶ G)
    (hinv : ∀ (W : C) (w₁ w₂ : W ⟶ A), a.app (op W) w₁ = a.app (op W) w₂ →
      k.app (op W) w₁ = k.app (op W) w₂) :
    ∃ g : P ⟶ G, a ≫ g = k := by
  have hG' := (isSheaf_iff_isSheaf_of_type _ _).1 hG
  have hak : ∀ {W W' : C} (v : W' ⟶ W) (w : W ⟶ A), G.map v.op (k.app (op W) w) =
      k.app (op W') (v ≫ w) := fun v w => (NatTrans.naturality_apply k v.op w).symm
  have haa : ∀ {W W' : C} (v : W' ⟶ W) (w : W ⟶ A), P.map v.op (a.app (op W) w) =
      a.app (op W') (v ≫ w) := fun v w => (NatTrans.naturality_apply a v.op w).symm
  have key : ∀ (T : C) (ξ : P.obj (op T)), ∃ γ : G.obj (op T), (∀ (W : C) (v : W ⟶ T) (w : W ⟶ A),
      a.app (op W) w = P.map v.op ξ → G.map v.op γ = k.app (op W) w) ∧
      ∀ γ' : G.obj (op T), (∀ (W : C) (v : W ⟶ T) (w : W ⟶ A),
        a.app (op W) w = P.map v.op ξ → G.map v.op γ' = k.app (op W) w) → γ' = γ := by
    intro T ξ
    have hmem := Presheaf.imageSieve_mem J a ξ
    have hex : ∀ {W : C} (v : W ⟶ T), Presheaf.imageSieve a ξ v →
        ∃ w : W ⟶ A, a.app (op W) w = P.map v.op ξ := fun v hv => hv
    let fam : Presieve.FamilyOfElements G (Presheaf.imageSieve a ξ).arrows :=
      fun W v hv => k.app (op W) (hex v hv).choose
    have hcomp : fam.Compatible := by
      intro W₁ W₂ Z g₁ g₂ f₁ f₂ h₁ h₂ e
      change G.map g₁.op (k.app _ _) = G.map g₂.op (k.app _ _)
      rw [hak, hak]
      apply hinv
      rw [← haa, ← haa, (hex f₁ h₁).choose_spec, (hex f₂ h₂).choose_spec,
        ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, e]
    have hS' := hG' _ hmem
    refine ⟨hS'.amalgamate fam hcomp, ?_, ?_⟩
    · intro W v w hw
      have hv : Presheaf.imageSieve a ξ v := ⟨w, hw⟩
      rw [hS'.valid_glue hcomp v hv]
      apply hinv
      rw [(hex v hv).choose_spec, hw]
    · intro γ' hγ'
      refine hS'.isSeparatedFor.ext fun W v hv => ?_
      rw [hS'.valid_glue hcomp v hv]
      exact hγ' W v _ (hex v hv).choose_spec
  choose γ hγ hγu using key
  refine ⟨{ app := fun T => ↾ fun ξ => γ T.unop ξ, naturality := ?_ }, ?_⟩
  · intro T T' f
    ext ξ
    change γ T'.unop (P.map f ξ) = G.map f (γ T.unop ξ)
    symm
    refine hγu _ _ _ fun W v w hw => ?_
    have := hγ T.unop ξ W (v ≫ f.unop) w (by
      rw [hw, op_comp, Functor.map_comp_apply]; rfl)
    rw [op_comp, Functor.map_comp_apply] at this
    exact this
  · ext T w
    obtain ⟨T⟩ := T
    change γ T (a.app _ w) = k.app _ w
    have := hγ T (a.app _ w) T (𝟙 T) w (by simp)
    simpa using this

variable (I : S.IdealSheafData)

/-- The functor from the site to `S`-schemes. -/
noncomputable abbrev toO : C ⥤ Over S := Over.post B.inclusion

/-- `T` is `S'`-regular. -/
def Reg (T : C) : Prop := IsRegular I (toO.obj T)

/-- `T` lies over `S'`. -/
def Lies (T : C) : Prop := LiesOver I (toO.obj T)

section

/-- `x ∈ X(T)` restricted to `S'` factors through `Y`. -/
def SpFac (I : S.IdealSheafData) {X Y : Cᵒᵖ ⥤ Type u} (j : Y ⟶ X) {T : C} (x : X.obj (op T)) : Prop :=
  ∀ ⦃Z : C⦄ (s : Z ⟶ T), Lies I Z → ∃ y : Y.obj (op Z), j.app (op Z) y = X.map s.op x

/-- `F` is `S'`-regular: it has a surjective étale atlas by an `S'`-regular scheme. -/
def SpReg (F : Cᵒᵖ ⥤ Type u) : Prop :=
  ∃ (U : C) (a : yoneda.obj U ⟶ F), Reg I U ∧
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) SCH)) a ∧
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) SCH)) a

/-- `b : F ⟶ X` is the dilatation `Bl_Y^D X` of the sheaf `X`, by its universal property among
`S'`-regular objects. -/
structure IsSpDil {X Y F : Cᵒᵖ ⥤ Type u} (j : Y ⟶ X) (b : F ⟶ X) : Prop where
  sheaf : Presheaf.IsSheaf J F
  reg : SpReg I F
  factors : ∀ ⦃T : C⦄ (ξ : F.obj (op T)), SpFac I j (b.app (op T) ξ)
  exists_lift : ∀ ⦃T : Cᵒᵖ ⥤ Type u⦄, SpReg I T → ∀ x : T ⟶ X,
    (∀ ⦃W : C⦄ (τ : T.obj (op W)), SpFac I j (x.app (op W) τ)) → ∃ f : T ⟶ F, f ≫ b = x
  uniq : ∀ ⦃T : Cᵒᵖ ⥤ Type u⦄, SpReg I T → ∀ f g : T ⟶ F, f ≫ b = g ≫ b → f = g

variable {I}

/-- Two dilatations are canonically isomorphic. -/
theorem IsSpDil.exists_iso {X Y F F' : Cᵒᵖ ⥤ Type u} {j : Y ⟶ X} {b : F ⟶ X} {b' : F' ⟶ X}
    (h : IsSpDil I j b) (h' : IsSpDil I j b') : ∃ e : F ≅ F', e.hom ≫ b' = b := by
  obtain ⟨f, hf⟩ := h'.exists_lift h.reg b h.factors
  obtain ⟨g, hg⟩ := h.exists_lift h'.reg b' h'.factors
  refine ⟨⟨f, g, h.uniq h.reg _ _ ?_, h'.uniq h'.reg _ _ ?_⟩, hf⟩
  · simp [hf, hg]
  · simp [hf, hg]

end

end AlgMag.DilSp

end PartB

section PartC

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry


namespace AlgMag.DilSp

open Dil

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc pullback.lift_snd_assoc

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "C" => BigFppfOver B S hS
local notation "SCH" => BigFppfOver.toScheme B S hS
local notation "J" => BigFppfOver.topology B S hS

lemma contains_of_isPullback {P A D E : Over S} {f : P ⟶ A} {g : P ⟶ E} {h : A ⟶ D} {k : E ⟶ D}
    (sq : IsPullback f g h k) (hA : B.Contains A.left) (hE : B.Contains E.left) :
    B.Contains P.left := by
  have sq' : IsPullback f.left g.left h.left k.left := sq.map (Over.forget S)
  exact Scheme.size_lt_of_isOpenImmersion sq'.isoPullback.hom
    (Scheme.size_pullback_lt _ _ hA hE)

/-- An `S`-scheme of the right size, as an object of the site. -/
noncomputable def ofO (E : Over S) (h : B.Contains E.left) : C :=
  siteObject B S hS h E.hom

@[simp] lemma toO_ofO (E : Over S) (h : B.Contains E.left) :
    (toO (B := B) (hS := hS)).obj (ofO E h) = E := rfl

instance : (toO (B := B) (S := S) (hS := hS)).Full := inferInstanceAs (Over.post B.inclusion).Full
instance : (toO (B := B) (S := S) (hS := hS)).Faithful := inferInstanceAs (Over.post B.inclusion).Faithful

/-- A morphism `E ⟶ T` in `Over S` as a morphism of the site. -/
noncomputable def preO {E : Over S} (hE : B.Contains E.left) {A : C} (f : E ⟶ (toO (B := B) (hS := hS)).obj A) :
    (ofO E hE : C) ⟶ A :=
  (toO (B := B) (hS := hS)).preimage (X := ofO E hE) f

lemma map_preO {E : Over S} (hE : B.Contains E.left) {A : C} (f : E ⟶ (toO (B := B) (hS := hS)).obj A) :
    (toO (B := B) (hS := hS)).map (preO hE f) = f :=
  (toO (B := B) (hS := hS)).map_preimage (X := ofO E hE) f

lemma c_comp {X : Cᵒᵖ ⥤ Type u} {U W W' : C} (c : yoneda.obj U ⟶ X) (v : W' ⟶ W) (w : W ⟶ U) :
    c.app (op W') (v ≫ w) = X.map v.op (c.app (op W) w) :=
  NatTrans.naturality_apply c v.op w

lemma y_comp_eq {X : Cᵒᵖ ⥤ Type u} {U W : C} (c : yoneda.obj U ⟶ X) {w₁ w₂ : W ⟶ U}
    (h : c.app (op W) w₁ = c.app (op W) w₂) : yoneda.map w₁ ≫ c = yoneda.map w₂ ≫ c := by
  ext ⟨Z⟩ v
  change c.app (op Z) (v ≫ w₁) = c.app (op Z) (v ≫ w₂)
  rw [c_comp, c_comp, h]

lemma app_eq_of_y {X : Cᵒᵖ ⥤ Type u} {U W : C} (c : yoneda.obj U ⟶ X) {w₁ w₂ : W ⟶ U}
    (h : yoneda.map w₁ ≫ c = yoneda.map w₂ ≫ c) : c.app (op W) w₁ = c.app (op W) w₂ := by
  have := congrArg (fun q => q.app (op W) (𝟙 W)) h
  simpa using this

section Kernel

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {j : Y ⟶ X} {U R Yu : BigFppfOver B S hS} {c : yoneda.obj U ⟶ X} {s t : R ⟶ U}
  {jU : Yu ⟶ U} {yu : yoneda.obj Yu ⟶ Y}

lemma ker_exists (pb : IsPullback (yoneda.map s) (yoneda.map t) c c) {W : C} {w₁ w₂ : W ⟶ U}
    (h : c.app (op W) w₁ = c.app (op W) w₂) : ∃ r : W ⟶ R, r ≫ s = w₁ ∧ r ≫ t = w₂ := by
  let l := pb.lift (yoneda.map w₁) (yoneda.map w₂) (y_comp_eq c h)
  refine ⟨yoneda.preimage l, yoneda.map_injective ?_, yoneda.map_injective ?_⟩
  · simp [l]
  · simp [l]

lemma ker_uniq (pb : IsPullback (yoneda.map s) (yoneda.map t) c c) {W : C} {r r' : W ⟶ R}
    (h₁ : r ≫ s = r' ≫ s) (h₂ : r ≫ t = r' ≫ t) : r = r' := by
  apply yoneda.map_injective
  apply pb.hom_ext
  · simp only [← yoneda.map_comp, h₁]
  · simp only [← yoneda.map_comp, h₂]

lemma ker_c (pb : IsPullback (yoneda.map s) (yoneda.map t) c c) {W : C} (r : W ⟶ R) :
    c.app (op W) (r ≫ s) = c.app (op W) (r ≫ t) := by
  apply app_eq_of_y
  simp only [yoneda.map_comp, Category.assoc, pb.w]

lemma chartRel (I : S.IdealSheafData)
    (pb : IsPullback (yoneda.map s) (yoneda.map t) c c)
    (pbY : IsPullback yu (yoneda.map jU) j c) :
    ChartRel I (toO.map jU) (toO.map s) (toO.map t) := by
  have hU : B.Contains ((toO (B := B) (hS := hS)).obj U).left := U.left.2
  have hR : B.Contains ((toO (B := B) (hS := hS)).obj R).left := R.left.2
  have hY : B.Contains ((toO (B := B) (hS := hS)).obj Yu).left := Yu.left.2
  let F := toO (B := B) (hS := hS)
  let So : F.obj R ⟶ F.obj U := F.map s
  let To : F.obj R ⟶ F.obj U := F.map t
  let jo : F.obj Yu ⟶ F.obj U := F.map jU
  change ChartRel I jo So To
  have hst : ∀ {E : Over S} (hE : B.Contains E.left) {A A' : C} (f f' : E ⟶ F.obj A) (g : A ⟶ A'),
      f ≫ F.map g = f' ≫ F.map g → preO hE f ≫ g = preO hE f' ≫ g := by
    intro E hE A A' f f' g e
    apply F.map_injective
    rw [Functor.map_comp, Functor.map_comp, map_preO, map_preO]
    exact e
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro T r r' h₁ h₂
    let P : Over S := pullback So So
    have hP : B.Contains P.left := contains_of_isPullback (IsPullback.of_hasPullback So So) hR hR
    let π₁ : P ⟶ F.obj R := pullback.fst So So
    let π₂ : P ⟶ F.obj R := pullback.snd So So
    let d : F.obj U ⟶ F.obj U ⨯ F.obj U := prod.lift (𝟙 _) (𝟙 _)
    let m : P ⟶ F.obj U ⨯ F.obj U := prod.lift (π₁ ≫ To) (π₂ ≫ To)
    let E : Over S := pullback m d
    have hE : B.Contains E.left := contains_of_isPullback (IsPullback.of_hasPullback m d) hP hU
    have hmd : pullback.fst m d ≫ π₁ ≫ To = pullback.fst m d ≫ π₂ ≫ To := by
      have := pullback.condition (f := m) (g := d)
      have a := congrArg (· ≫ prod.fst) this
      have b := congrArg (· ≫ prod.snd) this
      simp only [m, d, Category.assoc, prod.lift_fst, prod.lift_snd, Category.comp_id] at a b
      rw [a, b]
    have hms : pullback.fst m d ≫ π₁ ≫ So = pullback.fst m d ≫ π₂ ≫ So :=
      congrArg (pullback.fst m d ≫ ·) (pullback.condition (f := So) (g := So))
    have hee := ker_uniq pb
      (hst hE (pullback.fst m d ≫ π₁) (pullback.fst m d ≫ π₂) s (by simpa only [Category.assoc] using hms))
      (hst hE (pullback.fst m d ≫ π₁) (pullback.fst m d ≫ π₂) t (by simpa only [Category.assoc] using hmd))
    have hee' : pullback.fst m d ≫ π₁ = pullback.fst m d ≫ π₂ := by
      have := congrArg F.map hee
      rwa [map_preO, map_preO] at this
    let v : T ⟶ E := pullback.lift (pullback.lift r r' h₁) (r ≫ To) (by
      apply Limits.prod.hom_ext
      · simp only [m, d, π₁, Category.assoc, prod.lift_fst, Category.comp_id, pullback.lift_fst_assoc]
      · simp only [m, d, π₂, Category.assoc, prod.lift_snd, Category.comp_id, pullback.lift_snd_assoc]
        exact h₂.symm)
    have := congrArg (v ≫ ·) hee'
    simpa only [v, π₁, π₂, pullback.lift_fst_assoc, pullback.lift_fst, pullback.lift_snd] using this
  · intro T x
    obtain ⟨δ, h1, h2⟩ := ker_exists pb (W := U) (w₁ := 𝟙 U) (w₂ := 𝟙 U) rfl
    refine ⟨x ≫ F.map δ, ?_, ?_⟩
    · rw [Category.assoc]; change x ≫ F.map δ ≫ F.map s = x
      rw [← Functor.map_comp, h1, CategoryTheory.Functor.map_id, Category.comp_id]
    · rw [Category.assoc]; change x ≫ F.map δ ≫ F.map t = x
      rw [← Functor.map_comp, h2, CategoryTheory.Functor.map_id, Category.comp_id]
  · intro T r
    obtain ⟨σ, h1, h2⟩ := ker_exists pb (ker_c pb (𝟙 R)).symm
    refine ⟨r ≫ F.map σ, ?_, ?_⟩
    · rw [Category.assoc]; change r ≫ F.map σ ≫ F.map s = r ≫ F.map t
      rw [← Functor.map_comp, h1, Category.id_comp]
    · rw [Category.assoc]; change r ≫ F.map σ ≫ F.map t = r ≫ F.map s
      rw [← Functor.map_comp, h2, Category.id_comp]
  · intro T r r' h
    let P : Over S := pullback To So
    have hP : B.Contains P.left := contains_of_isPullback (IsPullback.of_hasPullback To So) hR hR
    let ps : C := ofO P hP
    let p₁ : ps ⟶ R := F.preimage (pullback.fst To So)
    let p₂ : ps ⟶ R := F.preimage (pullback.snd To So)
    have hp₁ : F.map p₁ = pullback.fst To So := Functor.map_preimage _ _
    have hp₂ : F.map p₂ = pullback.snd To So := Functor.map_preimage _ _
    have hw : p₁ ≫ t = p₂ ≫ s := F.map_injective (by
      rw [Functor.map_comp, Functor.map_comp, hp₁, hp₂]; exact pullback.condition)
    have hc : c.app (op ps) (p₁ ≫ s) = c.app (op ps) (p₂ ≫ t) := by
      rw [ker_c pb p₁, hw, ker_c pb p₂]
    obtain ⟨τ, h1, h2⟩ := ker_exists pb hc
    let l : T ⟶ P := pullback.lift r r' h
    let τ' : P ⟶ F.obj R := F.map τ
    have a1 : τ' ≫ So = pullback.fst To So ≫ So := by
      have := congrArg F.map h1
      rwa [Functor.map_comp, Functor.map_comp, hp₁] at this
    have a2 : τ' ≫ To = pullback.snd To So ≫ To := by
      have := congrArg F.map h2
      rwa [Functor.map_comp, Functor.map_comp, hp₂] at this
    refine ⟨l ≫ τ', ?_, ?_⟩
    · rw [Category.assoc, a1, pullback.lift_fst_assoc]
    · rw [Category.assoc, a2, pullback.lift_snd_assoc]
  · intro T r hf Z s' hZ
    obtain ⟨y, hy⟩ := hf s' hZ
    let Q : Over S := pullback jo So
    have hQ : B.Contains Q.left := contains_of_isPullback (IsPullback.of_hasPullback jo So) hY hR
    let qs : C := ofO Q hQ
    let q₁ : qs ⟶ Yu := F.preimage (pullback.fst jo So)
    let q₂ : qs ⟶ R := F.preimage (pullback.snd jo So)
    have hq₁ : F.map q₁ = pullback.fst jo So := Functor.map_preimage _ _
    have hq₂ : F.map q₂ = pullback.snd jo So := Functor.map_preimage _ _
    have hw : q₁ ≫ jU = q₂ ≫ s := F.map_injective (by
      rw [Functor.map_comp, Functor.map_comp, hq₁, hq₂]; exact pullback.condition)
    have hc : (yoneda.map q₁ ≫ yu) ≫ j = yoneda.map (q₂ ≫ t) ≫ c := by
      rw [Category.assoc, pbY.w, ← Category.assoc, ← yoneda.map_comp, hw]
      exact y_comp_eq c (ker_c pb q₂)
    let z := pbY.lift (yoneda.map q₁ ≫ yu) (yoneda.map (q₂ ≫ t)) hc
    let z' : qs ⟶ Yu := yoneda.preimage z
    have hz : z' ≫ jU = q₂ ≫ t := yoneda.map_injective (by
      rw [yoneda.map_comp, yoneda.map_preimage]; exact pbY.lift_snd _ _ hc)
    let v : Z ⟶ Q := pullback.lift y (s' ≫ r) (by rw [hy, Category.assoc])
    let z'' : Q ⟶ F.obj Yu := F.map z'
    have a : z'' ≫ jo = pullback.snd jo So ≫ To := by
      have := congrArg F.map hz
      rwa [Functor.map_comp, Functor.map_comp, hq₂] at this
    refine ⟨v ≫ z'', ?_⟩
    rw [Category.assoc, a, pullback.lift_snd_assoc, Category.assoc]

end Kernel

end AlgMag.DilSp

end PartC

section PartD

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Cardinal


namespace AlgMag.DilSp

open Dil

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "C" => BigFppfOver B S hS
local notation "SCH" => BigFppfOver.toScheme B S hS
local notation "J" => BigFppfOver.topology B S hS

/-- The dilatation of an object of the site is an object of the site. -/
lemma contains_blOver {I : S.IdealSheafData} {U Yo : Over S} (hU : B.Contains U.left) (j : Yo ⟶ U)
    [IsClosedImmersion j.left] (hYI : LiesOver I Yo) (hP : LocPrincipal I) :
    B.Contains (blOver j hYI hP).left := by
  classical
  by_cases hne : Nonempty (goodCover U hP).I₀
  · refine B.contains_of_openCover_of_size_le (μ := U.left.size) hU ?_
      (fun i => (blι j hYI hP i).left) ?_ ?_
    · exact (Cardinal.mk_subtype_le _).trans U.left.mk_affineOpens_le_size
    · intro y
      obtain ⟨V, hV, hx, -⟩ := good_basis U hP (O := ⊤) (x := (blMap j hYI hP).left y) trivial
      obtain ⟨z, hz⟩ := mem_range_of_mem j hYI hP (i := ⟨V, hV⟩) hx
      exact ⟨⟨V, hV⟩, z, hz⟩
    · intro i
      change (Spec (CommRingCat.of (chartC j _ _))).size ≤ _
      rw [Scheme.size_Spec]
      refine max_le U.left.aleph0_le_size ?_
      refine (Cardinal.mk_subtype_le _).trans ?_
      refine (Localization.cardinalMk_le _).trans ?_
      exact U.left.mk_sections_le_size i.1
  · have hemp : IsEmpty (blOver j hYI hP).left := by
      refine ⟨fun y => hne ?_⟩
      obtain ⟨V, hV, -, -⟩ := good_basis U hP (O := ⊤) (x := (blMap j hYI hP).left y) trivial
      exact ⟨⟨V, hV⟩⟩
    exact Scheme.size_lt_of_isOpenImmersion (blMap j hYI hP).left hU

lemma contains_restr {T : Scheme.{u}} (p : T ⟶ S) (I : S.IdealSheafData) (h : B.Contains T) :
    B.Contains (pullback p I.subschemeι) := by
  have hcf : IsClosedImmersion (pullback.fst p I.subschemeι) := inferInstance
  exact Scheme.size_lt_of_isClosedImmersion (pullback.fst p I.subschemeι) h

set_option maxHeartbeats 1000000 in
theorem exists_presentation (I : S.IdealSheafData) (hP : LocPrincipal I)
    {X Y : Cᵒᵖ ⥤ Type u} (j : Y ⟶ X)
    (hj : (MorphismProperty.inverseImage (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) SCH).presheaf j)
    (hYI : ∀ (Z : C) (_ : Y.obj (op Z)), Lies I Z)
    {U : C} (c : yoneda.obj U ⟶ X)
    (he : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) SCH).presheaf c) :
    ∃ (U' : C) (bU : U' ⟶ U) (F : Cᵒᵖ ⥤ Type u) (a : yoneda.obj U' ⟶ F),
      Presheaf.IsSheaf J F ∧ Presheaf.IsLocallySurjective J a ∧ IsAffineHom ((SCH).map bU) ∧
      (∀ ⦃W : C⦄ (x y : W ⟶ U'), a.app (op W) x = a.app (op W) y →
        c.app (op W) (x ≫ bU) = c.app (op W) (y ≫ bU)) ∧
      (∀ ⦃W : C⦄ (x y : W ⟶ U'), a.app (op W) x = a.app (op W) y → x ≫ bU = y ≫ bU → x = y) ∧
      (∀ ⦃W : C⦄ (x : W ⟶ U') (w : W ⟶ U), c.app (op W) w = c.app (op W) (x ≫ bU) →
        ∃ y : W ⟶ U', y ≫ bU = w ∧ a.app (op W) y = a.app (op W) x) ∧
      Reg I U' ∧
      (∀ ⦃W : C⦄ (l : W ⟶ U'), SpFac I j (c.app (op W) (l ≫ bU))) ∧
      (∀ ⦃W : C⦄, Reg I W → ∀ w : W ⟶ U, SpFac I j (c.app (op W) w) → ∃ l : W ⟶ U', l ≫ bU = w) ∧
      (∀ ⦃W : C⦄, Reg I W → ∀ l l' : W ⟶ U', l ≫ bU = l' ≫ bU → l = l') := by
  obtain ⟨R, s, t, pb⟩ := Space.exists_kernelPair_of_etale_atlas B S hS c he
  let Yu : C := hj.rep.pullback c
  let jU : Yu ⟶ U := hj.rep.snd c
  let yu : yoneda.obj Yu ⟶ Y := hj.rep.fst c
  have pbY : IsPullback yu (yoneda.map jU) j c := hj.rep.isPullback c
  let G := toO (B := B) (hS := hS)
  let jo : G.obj Yu ⟶ G.obj U := G.map jU
  have hcl : IsClosedImmersion jo.left := hj.2 c yu jU pbY
  have hlies : LiesOver I (G.obj Yu) := hYI Yu (yonedaEquiv yu)
  have hR : ChartRel I jo (G.map s) (G.map t) := chartRel I pb pbY
  have hsE : Etale ((SCH).map s) := he.2 c (yoneda.map t) s pb.flip
  have hsF : Flat (G.map s).left := (Etale.iff_flat_and_formallyUnramified.1 hsE).1
  obtain ⟨B0, b0, hD, haff⟩ := exists_dilatation jo hlies hP
  have hc : B.Contains B0.left := by
    have hbl : IsDilatation I jo (blMap jo hlies hP) := ⟨bl_regular jo hlies hP, fun _ _ => trivial,
      bl_factors jo hlies hP, fun T hT x _ hx => bl_exists_lift jo hlies hP hT x hx,
      fun T hT f g e => bl_uniq jo hlies hP hT f g e⟩
    obtain ⟨e, -⟩ := IsDilOn.exists_iso hD hbl
    have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
    have hUc : B.Contains (G.obj U).left := U.left.2
    have h1 : B.Contains (blOver jo hlies hP).left := contains_blOver hUc jo hlies hP
    exact Scheme.size_lt_of_isOpenImmersion e.hom.left h1
  let U' : C := ofO B0 hc
  let bU : U' ⟶ U := preO hc b0
  have hbU : G.map bU = b0 := map_preO hc b0
  have hmapb : ∀ {W : C} (x : W ⟶ U'), G.map (x ≫ bU) = G.map x ≫ b0 := fun x => by
    rw [Functor.map_comp, hbU]
  haveI : HasSheafify J (Type u) := BigFppfOver.hasSheafify_type B S hS
  let j' : Stacks.Groupoids.PreRelation (Rp b0 (G.map s)) (G.obj U') := relJ hR hD
  have hj'm : Mono j' := relJ_mono hR hD
  have hEq : ∀ {W : C} (x y : W ⟶ U'),
      (Stacks.Groupoids.quotientChart J G U' j').app (op W) x =
        (Stacks.Groupoids.quotientChart J G U' j').app (op W) y ↔ j'.Rel (G.map x) (G.map y) :=
    fun x y => Stacks.Groupoids.quotientChart_app_eq_iff_rel J G U' j' (relJ_equiv hR hD)
      (Stacks.Groupoids.isSheaf_points B S hS _) (Stacks.Groupoids.isSheaf_points B S hS _) x y
  refine ⟨U', bU, (Stacks.Groupoids.quotientSheaf J G j').obj,
    Stacks.Groupoids.quotientChart J G U' j', (Stacks.Groupoids.quotientSheaf J G j').property,
    Stacks.Groupoids.isLocallySurjective_quotientChart J G U' j', ?_, ?_, ?_, ?_, hD.reg, ?_, ?_, ?_⟩
  · have : (SCH).map bU = (G.map bU).left := rfl
    rw [this, hbU]; exact haff
  · intro W x y h
    obtain ⟨r, hh, e⟩ := (rel_iff hR hD _ _).1 ((hEq x y).1 h)
    let r' : W ⟶ R := G.preimage r
    have hr' : G.map r' = r := G.map_preimage r
    have e1 : x ≫ bU = r' ≫ s := G.map_injective ((hmapb x).trans (hh.trans (by rw [Functor.map_comp, hr'])))
    have e2 : y ≫ bU = r' ≫ t := G.map_injective ((hmapb y).trans (by
      refine (congrArg (· ≫ b0) e).symm.trans ((φ_map hR hD _ r hh).trans ?_)
      rw [Functor.map_comp, hr']))
    rw [e1, e2, ker_c pb]
  · intro W x y h e
    apply G.map_injective
    exact eq_of_rel_of_map_eq hR hD _ _ ((hEq x y).1 h)
      ((hmapb x).symm.trans ((congrArg G.map e).trans (hmapb y)))
  · intro W x w hw
    obtain ⟨r, h1, h2⟩ := ker_exists pb hw.symm
    have hh : G.map x ≫ b0 = G.map r ≫ G.map s := 
      (hmapb x).symm.trans (by rw [← Functor.map_comp, h1])
    let y : W ⟶ U' := G.preimage (X := W) (Y := U') (φ hR hD (G.map x) (G.map r) hh)
    have hy : G.map y = φ hR hD (G.map x) (G.map r) hh := G.map_preimage _
    refine ⟨y, G.map_injective ?_, ((hEq x y).2 ((rel_iff hR hD _ _).2 ⟨G.map r, hh, hy.symm⟩)).symm⟩
    refine (hmapb y).trans ((congrArg (· ≫ b0) hy).trans ((φ_map hR hD _ _ hh).trans ?_))
    rw [← Functor.map_comp, h2]
  · intro W l Z s' hZ
    obtain ⟨y, hy⟩ := hD.factors (G.map (s' ≫ l)) hZ
    let z : Z ⟶ Yu := G.preimage y
    have hz : G.map z = y := G.map_preimage y
    have e : z ≫ jU = s' ≫ l ≫ bU := G.map_injective (by
      rw [Functor.map_comp, hz, hy]
      refine Eq.trans ?_ (congrArg G.map (Category.assoc s' l bU))
      exact (hmapb (s' ≫ l)).symm)
    refine ⟨yu.app (op Z) z, ?_⟩
    have hw := congrArg (fun q => q.app (op Z) z) pbY.w
    refine hw.trans ?_
    change c.app (op Z) (z ≫ jU) = _
    rw [e, c_comp]
  · intro W hW w hf
    have hfac : Factors I jo (G.map w) := by
      rw [factors_iff_pullback]
      have hZs : B.Contains (restr I (G.obj W)).left := contains_restr _ I W.left.2
      let s' : (ofO _ hZs : C) ⟶ W := preO hZs (restrι I (G.obj W))
      obtain ⟨y, hy⟩ := hf s' (liesOver_restr (G.obj W))
      have hcomm : (yonedaEquiv.symm y) ≫ j = yoneda.map (s' ≫ w) ≫ c := by
        apply yonedaEquiv.injective
        rw [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, hy, ← c_comp]
        exact congrArg _ (Category.id_comp _).symm
      let z' := pbY.lift _ _ hcomm
      let z : (ofO _ hZs : C) ⟶ Yu := yoneda.preimage z'
      have hz : z ≫ jU = s' ≫ w := yoneda.map_injective (by
        rw [yoneda.map_comp, yoneda.map_preimage]; exact pbY.lift_snd _ _ hcomm)
      refine ⟨G.map z, ?_⟩
      have := congrArg G.map hz
      rw [Functor.map_comp, Functor.map_comp, map_preO] at this
      exact this
    obtain ⟨l₀, hl₀⟩ := hD.exists_lift hW (G.map w) (fun _ _ => trivial) hfac
    let l : W ⟶ U' := G.preimage (X := W) (Y := U') l₀
    have hl : G.map l = l₀ := G.map_preimage (X := W) (Y := U') l₀
    exact ⟨l, G.map_injective ((hmapb l).trans ((congrArg (· ≫ b0) hl).trans hl₀))⟩
  · intro W hW l l' e
    apply G.map_injective
    refine hD.uniq hW _ _ ?_
    exact (hmapb l).symm.trans ((congrArg G.map e).trans (hmapb l'))

end AlgMag.DilSp

end PartD

section PartE

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry


namespace AlgMag.DilSp

open Dil

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "C" => BigFppfOver B S hS
local notation "SCH" => BigFppfOver.toScheme B S hS
local notation "J" => BigFppfOver.topology B S hS

/-- Two sections of a sheaf agreeing on a locally surjective cover agree: a locally surjective
map can be cancelled on the left in maps to a sheaf. -/
lemma hom_ext_of_locSurj {P G Q : Cᵒᵖ ⥤ Type u} (hG : Presheaf.IsSheaf J G) (a : Q ⟶ P)
    (hloc : Presheaf.IsLocallySurjective J a) (g₁ g₂ : P ⟶ G) (h : a ≫ g₁ = a ≫ g₂) : g₁ = g₂ := by
  have hG' := (isSheaf_iff_isSheaf_of_type _ _).1 hG
  ext ⟨T⟩ ξ
  refine (hG' _ (Presheaf.imageSieve_mem J a ξ)).isSeparatedFor.ext fun W v hv => ?_
  obtain ⟨w, hw⟩ := hv
  have e := congrArg (fun q => q.app (op W) w) h
  change g₁.app _ (a.app _ w) = g₂.app _ (a.app _ w) at e
  rw [hw, NatTrans.naturality_apply g₁, NatTrans.naturality_apply g₂] at e
  exact e

/-- A point of `X` lifting locally along an injective map from a sheaf lifts. -/
lemma lift_of_local_mono {X Y : Cᵒᵖ ⥤ Type u} (hY : Presheaf.IsSheaf J Y) (hX : Presheaf.IsSheaf J X)
    (j : Y ⟶ X) [Mono j] {T : C} (x : X.obj (op T)) (R : Sieve T) (hR : R ∈ J T)
    (h : ∀ ⦃W : C⦄ (v : W ⟶ T), R v → ∃ y : Y.obj (op W), j.app _ y = X.map v.op x) :
    ∃ y : Y.obj (op T), j.app _ y = x := by
  have hY' := (isSheaf_iff_isSheaf_of_type _ _).1 hY
  have hX' := (isSheaf_iff_isSheaf_of_type _ _).1 hX
  have inj : ∀ U : Cᵒᵖ, Function.Injective (j.app U) := fun U =>
    (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 inferInstance U)
  let fam : Presieve.FamilyOfElements Y R.arrows := fun W v hv => (h v hv).choose
  have hcomp : fam.Compatible := by
    intro W₁ W₂ Z g₁ g₂ f₁ f₂ h₁ h₂ e
    apply inj
    rw [NatTrans.naturality_apply j, NatTrans.naturality_apply j]
    change X.map g₁.op (j.app _ (h f₁ h₁).choose) = X.map g₂.op (j.app _ (h f₂ h₂).choose)
    rw [(h f₁ h₁).choose_spec, (h f₂ h₂).choose_spec, ← Functor.map_comp_apply,
      ← Functor.map_comp_apply, ← op_comp, ← op_comp, e]
  refine ⟨(hY' _ hR).amalgamate fam hcomp, (hX' _ hR).isSeparatedFor.ext fun W v hv => ?_⟩
  rw [← NatTrans.naturality_apply j, (hY' _ hR).valid_glue hcomp v hv]
  exact (h v hv).choose_spec

lemma app_eq_of_y' {X : Cᵒᵖ ⥤ Type u} {U W P : C} {c : yoneda.obj U ⟶ X} {α : P ⟶ U} {q : P ⟶ W}
    {g : yoneda.obj W ⟶ X} (w : yoneda.map α ≫ c = yoneda.map q ≫ g) :
    c.app (op P) α = X.map q.op (g.app (op W) (𝟙 W)) := by
  have := congrArg (fun r => r.app (op P) (𝟙 P)) w
  change c.app (op P) (𝟙 P ≫ α) = g.app (op P) (𝟙 P ≫ q) at this
  rw [Category.id_comp, Category.id_comp] at this
  rw [this, ← c_comp, Category.comp_id]

/-- A regular cover of a regular `W` trivializing a point of `X`. -/
lemma exists_cover (I : S.IdealSheafData) {X : Cᵒᵖ ⥤ Type u} {U : C} (c : yoneda.obj U ⟶ X)
    (hs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u}) SCH).presheaf c)
    (he : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) SCH).presheaf c)
    {W : C} (hW : Reg I W) (x₀ : X.obj (op W)) :
    ∃ (P : C) (q : P ⟶ W) (α : P ⟶ U), Reg I P ∧ c.app (op P) α = X.map q.op x₀ ∧
      Presheaf.IsLocallySurjective J (yoneda.map q) ∧
      ∀ ⦃Z : C⦄ (z₁ z₂ : Z ⟶ P), z₁ ≫ q = z₂ ≫ q → ∃ (K : C) (k₁ k₂ : K ⟶ P) (v : Z ⟶ K),
        Reg I K ∧ k₁ ≫ q = k₂ ≫ q ∧ v ≫ k₁ = z₁ ∧ v ≫ k₂ = z₂ := by
  let g : yoneda.obj W ⟶ X := yonedaEquiv.symm x₀
  let hrep := he.rep
  let P : C := hrep.pullback g
  let q : P ⟶ W := hrep.snd g
  let α : P ⟶ U := yoneda.preimage (hrep.fst g)
  have hpb : IsPullback (yoneda.map α) (yoneda.map q) c g := by
    have := hrep.isPullback g
    simpa only [α, yoneda.map_preimage] using this
  have hqS : Surjective ((SCH).map q) := hs.2 g (yoneda.map α) q hpb
  have hqE : Etale ((SCH).map q) := he.2 g (yoneda.map α) q hpb
  let G := toO (B := B) (hS := hS)
  have hqF : Flat (G.map q).left := (Etale.iff_flat_and_formallyUnramified.1 hqE).1
  have hS' : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u}) SCH).presheaf (yoneda.map q) :=
    Space.presheaf_yoneda_map_of_inverseImage B S hS inferInstance q hqS
  have hE' : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) SCH).presheaf (yoneda.map q) :=
    Space.presheaf_yoneda_map_of_inverseImage B S hS inferInstance q hqE
  have hPr : Reg I P := IsRegular.of_flat hW (G.map q)
  refine ⟨P, q, α, hPr, ?_, isLocallySurjective_of_surjective_etale B S hS _ hS' hE', ?_⟩
  · have e := app_eq_of_y' hpb.w
    have e2 : g.app (op W) (𝟙 W) = x₀ := yonedaEquiv.apply_symm_apply x₀
    rwa [e2] at e
  · intro Z z₁ z₂ e
    have hPc : B.Contains (G.obj P).left := P.left.2
    let Go := G.map q
    let K₀ : Over S := pullback Go Go
    have hK : B.Contains K₀.left := contains_of_isPullback (IsPullback.of_hasPullback Go Go) hPc hPc
    let k₁ : (ofO K₀ hK : C) ⟶ P := preO hK (pullback.fst Go Go)
    let k₂ : (ofO K₀ hK : C) ⟶ P := preO hK (pullback.snd Go Go)
    have m₁ : G.map k₁ = pullback.fst Go Go := map_preO hK _
    have m₂ : G.map k₂ = pullback.snd Go Go := map_preO hK _
    have hfl : Flat (pullback.fst Go Go).left :=
      flat_left_of_isPullback (IsPullback.of_hasPullback Go Go)
    have hKr : Reg I (ofO K₀ hK : C) := @IsRegular.of_flat S I _ _ hPr (pullback.fst Go Go) hfl
    let v₀ : G.obj Z ⟶ K₀ := pullback.lift (G.map z₁) (G.map z₂) (by
      change G.map z₁ ≫ G.map q = G.map z₂ ≫ G.map q
      rw [← Functor.map_comp, ← Functor.map_comp, e])
    let v : Z ⟶ (ofO K₀ hK : C) := G.preimage (X := Z) (Y := ofO K₀ hK) v₀
    have mv : G.map v = v₀ := G.map_preimage (X := Z) (Y := ofO K₀ hK) v₀
    refine ⟨_, k₁, k₂, v, hKr, G.map_injective ?_, G.map_injective ?_, G.map_injective ?_⟩
    · rw [Functor.map_comp, Functor.map_comp, m₁, m₂]; exact pullback.condition
    · rw [Functor.map_comp, m₁, mv]; exact pullback.lift_fst _ _ _
    · rw [Functor.map_comp, m₂, mv]; exact pullback.lift_snd _ _ _

/-- The universal property among regular sheaves follows from the one on regular objects of the
site. -/
theorem isSpDil_of_site {I : S.IdealSheafData} {X Y F : Cᵒᵖ ⥤ Type u} {j : Y ⟶ X} {b : F ⟶ X}
    (hF : Presheaf.IsSheaf J F) (hX : Presheaf.IsSheaf J X) (hreg : SpReg I F)
    (hfac : ∀ ⦃T : C⦄ (ξ : F.obj (op T)), SpFac I j (b.app (op T) ξ))
    (LIFT : ∀ ⦃W : C⦄, Reg I W → ∀ x₀ : X.obj (op W), SpFac I j x₀ →
      ∃ ξ : F.obj (op W), b.app _ ξ = x₀)
    (UNIQ : ∀ ⦃W : C⦄, Reg I W → ∀ ξ₁ ξ₂ : F.obj (op W), b.app _ ξ₁ = b.app _ ξ₂ → ξ₁ = ξ₂) :
    IsSpDil I j b := by
  refine ⟨hF, hreg, hfac, ?_, ?_⟩
  · intro T ⟨A, aT, hAr, hAs, hAe⟩ x hx
    have hAloc := isLocallySurjective_of_surjective_etale B S hS aT hAs hAe
    obtain ⟨ξ, hξ⟩ := LIFT hAr (x.app _ (aT.app _ (𝟙 A))) (hx _)
    obtain ⟨Rk, s, t, pb⟩ := Space.exists_kernelPair_of_etale_atlas B S hS aT hAe
    have hsE : Etale ((SCH).map s) := hAe.2 aT (yoneda.map t) s pb.flip
    have hsF : Flat ((toO (B := B) (hS := hS)).map s).left :=
      (Etale.iff_flat_and_formallyUnramified.1 hsE).1
    have hRk : Reg I Rk := IsRegular.of_flat hAr ((toO (B := B) (hS := hS)).map s)
    have hel : ∀ {W : C} (w : W ⟶ A), aT.app (op W) w = T.map w.op (aT.app _ (𝟙 A)) := fun {W} w => by
      rw [← c_comp, Category.comp_id]
    have hval : ∀ {W : C} (w : W ⟶ A), b.app _ (F.map w.op ξ) = x.app _ (aT.app (op W) w) := fun {W} w => by
      rw [NatTrans.naturality_apply b, hξ, ← NatTrans.naturality_apply x, ← hel]
    obtain ⟨g, hg⟩ := exists_desc_of_locSurj hF aT hAloc (yonedaEquiv.symm ξ) (fun W w₁ w₂ e => by
      obtain ⟨r, rfl, rfl⟩ := ker_exists pb e
      have : F.map s.op ξ = F.map t.op ξ := UNIQ hRk _ _ (by
        rw [hval, hval]
        exact congrArg _ (app_eq_of_y aT (by simpa using pb.w)))
      have h1 : ∀ w : W ⟶ A, (yonedaEquiv.symm ξ).app (op W) w = F.map w.op ξ := fun w => rfl
      rw [h1, h1, op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, this])
    refine ⟨g, hom_ext_of_locSurj hX aT hAloc _ _ ?_⟩
    ext ⟨W⟩ w
    change b.app _ ((aT ≫ g).app _ w) = x.app _ (aT.app _ w)
    rw [hg, ← hval]
    rfl
  · intro T ⟨A, aT, hAr, hAs, hAe⟩ f g e
    have hAloc := isLocallySurjective_of_surjective_etale B S hS aT hAs hAe
    refine hom_ext_of_locSurj hF aT hAloc _ _ ?_
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_comp]
    refine UNIQ hAr _ _ ?_
    exact congrArg (fun q => q.app (op A) (yonedaEquiv aT)) e


/-- **Existence of the dilatation of an algebraic space** (Mayeux, *Algebraic Magnetism*, §13):
`S'` closed locally principal in `S`, `X` an algebraic space over `S`, `Y` a closed subspace of `X`
lying over `S'`. There is an algebraic space `Bl_Y^D X` and an affine morphism `Bl_Y^D X ⟶ X`, the
dilatation. It is obtained from the dilatation of an étale atlas by étale descent of an affine
morphism. -/
theorem exists_spDilatation (I : S.IdealSheafData) (hP : LocPrincipal I)
    {X Y : Cᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X) (hYs : Presheaf.IsSheaf J Y) (j : Y ⟶ X)
    (hj : (MorphismProperty.inverseImage (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) SCH).presheaf j)
    (hYI : ∀ (Z : C) (_ : Y.obj (op Z)), Lies I Z) :
    ∃ (F : Cᵒᵖ ⥤ Type u) (b : F ⟶ X), IsAlgebraicSpace B S hS F ∧
      (MorphismProperty.inverseImage (@IsAffineHom.{u} : MorphismProperty Scheme.{u}) SCH).presheaf b ∧
      IsSpDil I j b := by
  obtain ⟨U, c, hs, he⟩ := hX.exists_atlas
  obtain ⟨U', bU, F, a, hF, hloc, haff, hA, hBB, hCC, hreg, hfac, hlift, huniq⟩ :=
    exists_presentation I hP j hj hYI c he
  have hUs : Presheaf.IsSheaf J (yoneda.obj U') := (isAlgebraicSpace_yoneda B S hS U').isSheaf
  have hUs' := (isSheaf_iff_isSheaf_of_type _ _).1 hUs
  have hF' := (isSheaf_iff_isSheaf_of_type _ _).1 hF
  have haa : ∀ {W W' : C} (v : W' ⟶ W) (l : W ⟶ U'), a.app (op W') (v ≫ l) = F.map v.op (a.app (op W) l) :=
    fun v l => c_comp a v l
  obtain ⟨b, hb⟩ := exists_desc_of_locSurj hX.isSheaf a hloc (yoneda.map bU ≫ c)
    (fun W x y h => hA x y h)
  have hab : ∀ {W : C} (l : W ⟶ U'), b.app (op W) (a.app (op W) l) = c.app (op W) (l ≫ bU) :=
    fun {W} l => congrArg (fun q => q.app (op W) l) hb
  -- the fibre product of `b` with the atlas is the dilatation of the atlas
  have L2 : ∀ {T : C} (ξ : F.obj (op T)) (w : T ⟶ U), c.app (op T) w = b.app (op T) ξ →
      ∃ l : T ⟶ U', l ≫ bU = w ∧ a.app (op T) l = ξ := by
    intro T ξ w h
    have hmem := Presheaf.imageSieve_mem J a ξ
    have hex : ∀ {W : C} (v : W ⟶ T), Presheaf.imageSieve a ξ v →
        ∃ l : W ⟶ U', l ≫ bU = v ≫ w ∧ a.app (op W) l = F.map v.op ξ := by
      intro W v hv
      obtain ⟨l₀, hl₀⟩ := hv
      have : c.app (op W) (v ≫ w) = c.app (op W) (l₀ ≫ bU) := by
        rw [c_comp, h, ← hab, hl₀, NatTrans.naturality_apply b]
      obtain ⟨y, h1, h2⟩ := hCC l₀ (v ≫ w) this
      exact ⟨y, h1, h2.trans hl₀⟩
    let fam : Presieve.FamilyOfElements (yoneda.obj U') (Presheaf.imageSieve a ξ).arrows :=
      fun W v hv => (hex v hv).choose
    have hcomp : fam.Compatible := by
      intro W₁ W₂ Z g₁ g₂ f₁ f₂ h₁ h₂ e
      change g₁ ≫ (hex f₁ h₁).choose = g₂ ≫ (hex f₂ h₂).choose
      apply hBB
      · rw [haa, haa, (hex f₁ h₁).choose_spec.2, (hex f₂ h₂).choose_spec.2,
          ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, e]
      · rw [Category.assoc, Category.assoc, (hex f₁ h₁).choose_spec.1, (hex f₂ h₂).choose_spec.1,
          ← Category.assoc, ← Category.assoc, e]
    let l : T ⟶ U' := (hUs' _ hmem).amalgamate fam hcomp
    have hl : ∀ {W : C} (v : W ⟶ T) (hv : Presheaf.imageSieve a ξ v), v ≫ l = (hex v hv).choose :=
      fun v hv => (hUs' _ hmem).valid_glue hcomp v hv
    have hUs2 := (isSheaf_iff_isSheaf_of_type _ _).1 (isAlgebraicSpace_yoneda B S hS U).isSheaf
    refine ⟨l, ?_, ?_⟩
    · refine (hUs2 _ hmem).isSeparatedFor.ext fun W v hv => ?_
      change v ≫ l ≫ bU = v ≫ w
      rw [← Category.assoc, hl v hv]
      exact (hex v hv).choose_spec.1
    · refine (hF' _ hmem).isSeparatedFor.ext fun W v hv => ?_
      rw [← haa, hl v hv]
      exact (hex v hv).choose_spec.2
  have pb2 : IsPullback (yoneda.map bU) a c b := by
    refine IsPullback.of_forall_isPullback_app fun T => ?_
    obtain ⟨T⟩ := T
    rw [Types.isPullback_iff]
    refine ⟨?_, ?_, ?_⟩
    · ext l; exact (hab l).symm
    · rintro x y ⟨h1, h2⟩
      exact hBB x y h2 h1
    · intro w ξ h
      exact L2 ξ w h
  have hsa : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u}) SCH).presheaf a := by
    have := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u}) SCH)
    exact MorphismProperty.of_isPullback pb2 hs
  have hea : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) SCH).presheaf a := by
    have := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) SCH)
    exact MorphismProperty.of_isPullback pb2 he
  -- affineness, by étale descent
  have hV : (MorphismProperty.inverseImage (@IsAffineHom.{u} : MorphismProperty Scheme.{u}) SCH).presheaf
      (pullback.snd b c) := by
    have hpn := Space.presheaf_yoneda_map_of_inverseImage B S hS
      (P := @IsAffineHom.{u}) inferInstance bU haff
    have hRI : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@IsAffineHom.{u} : MorphismProperty Scheme.{u}) SCH)).RespectsIso :=
      (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) _).respectsIso
    let e := pb2.flip.isoPullback
    have hfinal : pullback.snd b c = e.inv ≫ yoneda.map bU := by
      rw [Iso.eq_inv_comp]; exact pb2.flip.isoPullback_hom_snd
    rw [hfinal]
    exact MorphismProperty.RespectsIso.precomp _ e.inv _ hpn
  have hRIa : MorphismProperty.RespectsIso (@IsAffineHom.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  obtain ⟨hFalg, hbaff⟩ := Space.isAlgebraicSpace_and_presheaf_of_surjectiveEtaleChart_of_descent
    (Space.isEffectiveDescentAlongSurjectiveEtale_isAffineHom B S hS) hF hX hs he hV
  -- the universal property on regular objects of the site
  have UNIQ : ∀ ⦃W : C⦄, Reg I W → ∀ ξ₁ ξ₂ : F.obj (op W), b.app _ ξ₁ = b.app _ ξ₂ → ξ₁ = ξ₂ := by
    intro W hW ξ₁ ξ₂ e
    obtain ⟨P, q, α, hPr, hα, hqloc, -⟩ := exists_cover I c hs he hW (b.app _ ξ₁)
    have e₁ : c.app (op P) α = b.app _ (F.map q.op ξ₁) := by
      rw [hα, NatTrans.naturality_apply b]
    have e₂ : c.app (op P) α = b.app _ (F.map q.op ξ₂) := by
      rw [hα, e, NatTrans.naturality_apply b]
    obtain ⟨l₁, h1, h1'⟩ := L2 _ α e₁
    obtain ⟨l₂, h2, h2'⟩ := L2 _ α e₂
    have hl := huniq hPr l₁ l₂ (h1.trans h2.symm)
    have hq : F.map q.op ξ₁ = F.map q.op ξ₂ := by rw [← h1', ← h2', hl]
    have := hom_ext_of_locSurj hF (yoneda.map q) hqloc (yonedaEquiv.symm ξ₁) (yonedaEquiv.symm ξ₂) (by
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, yonedaEquiv_comp]
      simpa [yonedaEquiv] using hq)
    exact yonedaEquiv.symm.injective this
  have LIFT : ∀ ⦃W : C⦄, Reg I W → ∀ x₀ : X.obj (op W), SpFac I j x₀ →
      ∃ ξ : F.obj (op W), b.app _ ξ = x₀ := by
    intro W hW x₀ hx
    obtain ⟨P, q, α, hPr, hα, hqloc, hker⟩ := exists_cover I c hs he hW x₀
    have hxa : SpFac I j (c.app (op P) α) := by
      intro Z s' hZ
      obtain ⟨y, hy⟩ := hx (s' ≫ q) hZ
      refine ⟨y, hy.trans ?_⟩
      rw [hα, ← Functor.map_comp_apply, op_comp]
    obtain ⟨l, hl⟩ := hlift hPr α hxa
    obtain ⟨g, hg⟩ := exists_desc_of_locSurj hF (yoneda.map q) hqloc (yoneda.map l ≫ a)
      (fun Z z₁ z₂ e => by
        have e' : z₁ ≫ q = z₂ ≫ q := e
        change a.app (op Z) (z₁ ≫ l) = a.app (op Z) (z₂ ≫ l)
        obtain ⟨K, k₁, k₂, v, hK, hkq, rfl, rfl⟩ := hker z₁ z₂ e'
        have hcc : c.app (op K) (k₂ ≫ α) = c.app (op K) ((k₁ ≫ l) ≫ bU) := by
          rw [Category.assoc, hl, c_comp, c_comp, hα, ← Functor.map_comp_apply,
            ← Functor.map_comp_apply, ← op_comp, ← op_comp, hkq]
        obtain ⟨y, h1, h2⟩ := hCC (k₁ ≫ l) (k₂ ≫ α) hcc
        have hy : y = k₂ ≫ l := huniq hK _ _ (by rw [h1, Category.assoc, hl])
        rw [Category.assoc, Category.assoc, haa v, haa v]
        rw [hy] at h2
        rw [h2])
    refine ⟨yonedaEquiv g, ?_⟩
    have := hom_ext_of_locSurj hX.isSheaf (yoneda.map q) hqloc (g ≫ b) (yonedaEquiv.symm x₀) (by
      rw [← Category.assoc, hg, Category.assoc, hb, ← Category.assoc, ← yoneda.map_comp, hl]
      ext ⟨Z⟩ v
      change c.app _ (v ≫ α) = X.map (v ≫ q).op x₀
      rw [c_comp, hα, op_comp, Functor.map_comp_apply])
    have e2 := congrArg yonedaEquiv this
    rw [Equiv.apply_symm_apply, yonedaEquiv_comp] at e2
    exact e2
  haveI hjm : Mono j := Functor.relativelyRepresentable.mono_of_mono_snd hj.rep fun _ g => by
    have hcl : IsClosedImmersion ((SCH).map (hj.rep.snd g)) :=
      hj.2 g (hj.rep.fst g) (hj.rep.snd g) (hj.rep.isPullback g)
    exact (SCH).mono_of_mono_map inferInstance
  refine ⟨F, b, hFalg, hbaff, isSpDil_of_site hF hX.isSheaf ⟨U', a, hreg, hsa, hea⟩ ?_ LIFT UNIQ⟩
  · intro T ξ Z s' hZ
    let ξ' := F.map s'.op ξ
    have e0 : X.map s'.op (b.app _ ξ) = b.app _ ξ' := (NatTrans.naturality_apply b s'.op ξ).symm
    rw [e0]
    refine lift_of_local_mono hYs hX.isSheaf j _ _ (Presheaf.imageSieve_mem J a ξ') ?_
    rintro W v ⟨l, hl⟩
    have hLW : Lies I W := LiesOver.of_hom hZ (toO.map v)
    obtain ⟨y, hy⟩ := hfac l (𝟙 W) hLW
    refine ⟨y, hy.trans ?_⟩
    rw [op_id, CategoryTheory.Functor.map_id_apply, ← hab, hl, NatTrans.naturality_apply b]

end AlgMag.DilSp

end PartE

section PartG

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry


namespace AlgMag.DilSp

open Dil GB

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "C" => BigFppfOver B S hS
local notation "SCH" => BigFppfOver.toScheme B S hS
local notation "J" => BigFppfOver.topology B S hS
local notation "OO" => fppfO B S hS

lemma spReg_yoneda {I : S.IdealSheafData} {W : C} (hW : Reg I W) : SpReg I (yoneda.obj W) := by
  refine ⟨W, 𝟙 _, hW, ?_, ?_⟩
  · have := Space.presheaf_yoneda_map_of_inverseImage B S hS (P := @Surjective.{u}) inferInstance (𝟙 W)
      (by rw [CategoryTheory.Functor.map_id]; infer_instance)
    simpa using this
  · have := Space.presheaf_yoneda_map_of_inverseImage B S hS (P := @Etale.{u}) inferInstance (𝟙 W)
      (by rw [CategoryTheory.Functor.map_id]; infer_instance)
    simpa using this

lemma IsSpDil.uniq_pt {I : S.IdealSheafData} {X Y F : Cᵒᵖ ⥤ Type u} {j : Y ⟶ X} {b : F ⟶ X}
    (h : IsSpDil I j b) {W : C} (hW : Reg I W) (ξ₁ ξ₂ : F.obj (op W))
    (e : b.app _ ξ₁ = b.app _ ξ₂) : ξ₁ = ξ₂ := by
  have := h.uniq (spReg_yoneda hW) (yonedaEquiv.symm ξ₁) (yonedaEquiv.symm ξ₂) (by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact e)
  exact yonedaEquiv.symm.injective this

lemma SpFac.map {I : S.IdealSheafData} {X Y : Cᵒᵖ ⥤ Type u} {j : Y ⟶ X} {W : C}
    {x : X.obj (op W)} (hx : SpFac I j x) {W' : C} (v : W' ⟶ W) :
    SpFac I j (X.map v.op x) := by
  intro Z s hZ
  obtain ⟨y, hy⟩ := hx (s ≫ v) hZ
  refine ⟨y, hy.trans ?_⟩
  rw [op_comp, Functor.map_comp_apply]

lemma IsSpDil.lift_pt {I : S.IdealSheafData} {X Y F : Cᵒᵖ ⥤ Type u} {j : Y ⟶ X} {b : F ⟶ X}
    (h : IsSpDil I j b) {W : C} (hW : Reg I W) (x₀ : X.obj (op W))
    (hx : SpFac I j x₀) : ∃ ξ : F.obj (op W), b.app _ ξ = x₀ := by
  obtain ⟨f, hf⟩ := h.exists_lift (spReg_yoneda hW) (yonedaEquiv.symm x₀) (fun V τ => hx.map τ)
  refine ⟨yonedaEquiv f, ?_⟩
  have := congrArg yonedaEquiv hf
  rwa [yonedaEquiv_comp, Equiv.apply_symm_apply] at this

section Univ

variable {M : Type u} [AddCommMonoid M]

/-- `𝔸(N)_T` as an object of the big fppf site. -/
noncomputable def up (N : AddSubmonoid M) (hN : B.Contains (AZ N)) (T : BigFppfOver B S hS) :
    UniversalPoint (fppfO B S hS) N T :=
  let G := toO (B := B) (hS := hS)
  let U0 := GB.universalPoint N (G.obj T)
  have hP : B.Contains U0.P.left := Scheme.size_pullback_lt _ _ T.left.2 hN
  { P := ofO U0.P hP
    π := preO hP U0.π
    u := U0.u
    lift := fun {T'} t a => G.preimage (X := T') (Y := ofO U0.P hP) (U0.lift (G.map t) a)
    lift_π := fun {T'} t a => G.map_injective (by
      rw [Functor.map_comp, map_preO]
      refine (congrArg (· ≫ U0.π) (G.map_preimage (X := T') (Y := ofO U0.P hP) (U0.lift (G.map t) a))).trans ?_
      exact U0.lift_π _ _)
    res_lift := fun {T'} t a => by
      have e := G.map_preimage (X := T') (Y := ofO U0.P hP) (U0.lift (G.map t) a)
      have h := U0.res_lift (G.map t) a
      rw [← e] at h
      exact h
    uniq := fun {T'} t a s h1 h2 => G.map_injective (by
      refine Eq.trans ?_ (G.map_preimage (X := T') (Y := ofO U0.P hP) (U0.lift (G.map t) a)).symm
      refine U0.uniq (G.map t) a (G.map s) ?_ h2
      have := congrArg G.map h1
      rwa [Functor.map_comp, map_preO] at this) }

lemma up_reg {I : S.IdealSheafData} (N : AddSubmonoid M) (hN : B.Contains (AZ N))
    {T : BigFppfOver B S hS} (hT : Reg I T) : Reg I (up N hN T).P :=
  IsRegular.univPt hT N

/-- `𝔸(M) × F`. -/
noncomputable def APr (M : Type u) [AddCommMonoid M] (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type u where
  obj U := APt (fppfO B S hS) M U × F.obj U
  map f := ↾ fun p => (APt.res f p.1, F.map f p.2)
  map_id U := by
    refine ConcreteCategory.hom_ext _ _ fun p => ?_
    change (APt.res (𝟙 U) p.1, F.map (𝟙 U) p.2) = p
    rw [APt.res_id, CategoryTheory.Functor.map_id_apply]
  map_comp f g := by
    refine ConcreteCategory.hom_ext _ _ fun p => ?_
    change (APt.res (f ≫ g) p.1, F.map (f ≫ g) p.2) = (APt.res g (APt.res f p.1), F.map g (F.map f p.2))
    rw [APt.res_comp, Functor.map_comp_apply]

/-- The projection `𝔸(M) × F ⟶ F`. -/
noncomputable def APr.π (M : Type u) [AddCommMonoid M] (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    APr M F ⟶ F where
  app U := ↾ fun p => p.2
  naturality _ _ _ := rfl

/-- The universal point of `𝔸(M)` on `𝔸(M)_T`. -/
noncomputable def gMs (hM : B.Contains (AZ (⊤ : AddSubmonoid M))) (T : BigFppfOver B S hS) :
    APt (fppfO B S hS) M (op (up ⊤ hM T).P) :=
  ((up ⊤ hM T).u).comp
    (AddMonoidHom.toMultiplicative (AddSubmonoid.topEquiv (M := M)).symm.toAddMonoidHom)

/-- The classifying map of a point of `𝔸(M)`. -/
noncomputable def liftMs (hM : B.Contains (AZ (⊤ : AddSubmonoid M))) {T T' : BigFppfOver B S hS}
    (t : T' ⟶ T) (h : APt (fppfO B S hS) M (op T')) : T' ⟶ (up ⊤ hM T).P :=
  (up ⊤ hM T).lift t (APt.toMagnet ⊤ h)

lemma liftMs_π (hM : B.Contains (AZ (⊤ : AddSubmonoid M))) {T T' : BigFppfOver B S hS}
    (t : T' ⟶ T) (h : APt (fppfO B S hS) M (op T')) : liftMs hM t h ≫ (up ⊤ hM T).π = t :=
  UniversalPoint.lift_π _ _ _

lemma res_liftMs (hM : B.Contains (AZ (⊤ : AddSubmonoid M))) {T T' : BigFppfOver B S hS}
    (t : T' ⟶ T) (h : APt (fppfO B S hS) M (op T')) :
    APt.res (liftMs hM t h).op (gMs hM T) = h := by
  have := (up ⊤ hM T).res_lift t (APt.toMagnet ⊤ h)
  ext p
  exact congrArg (fun q => q (Multiplicative.ofAdd (⟨Multiplicative.toAdd p, trivial⟩ :
    (⊤ : AddSubmonoid M)))) this

lemma liftMs_uniq (hM : B.Contains (AZ (⊤ : AddSubmonoid M))) {T T' : BigFppfOver B S hS}
    (s s' : T' ⟶ (up ⊤ hM T).P) (h1 : s ≫ (up ⊤ hM T).π = s' ≫ (up ⊤ hM T).π)
    (h2 : APt.res s.op (gMs hM T) = APt.res s'.op (gMs hM T)) : s = s' := by
  have key : ∀ r : T' ⟶ (up ⊤ hM T).P, r = (up ⊤ hM T).lift (r ≫ (up ⊤ hM T).π)
      (APt.toMagnet ⊤ (APt.res r.op (gMs hM T))) := fun r =>
    (up ⊤ hM T).uniq _ _ r rfl (by
      ext p
      obtain ⟨p, hp⟩ := p
      rfl)
  rw [key s, key s', h1, h2]

/-- `𝔸(M) × F` has the regular atlas `𝔸(M)_U`. -/
lemma SpReg.apr {I : S.IdealSheafData} (hM : B.Contains (AZ (⊤ : AddSubmonoid M)))
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : SpReg I F) : SpReg I (APr M F) := by
  obtain ⟨A, a, hA, hs, he⟩ := hF
  let P := (up ⊤ hM A).P
  let a' : yoneda.obj P ⟶ APr M F :=
    { app := fun U => ↾ fun x => (APt.res x.op (gMs hM A), a.app U (x ≫ (up ⊤ hM A).π))
      naturality := fun U V f => by
        refine ConcreteCategory.hom_ext _ _ fun (x : unop U ⟶ P) => ?_
        change (APt.res (f.unop ≫ x).op (gMs hM A), a.app V ((f.unop ≫ x) ≫ (up ⊤ hM A).π)) =
          (APt.res f (APt.res x.op (gMs hM A)), F.map f (a.app U (x ≫ (up ⊤ hM A).π)))
        rw [Category.assoc]
        exact Prod.ext (APt.res_comp x.op f _) (c_comp a f.unop (x ≫ (up ⊤ hM A).π)) }
  have pb : IsPullback (yoneda.map (up ⊤ hM A).π) a' a (APr.π M F) := by
    refine IsPullback.of_forall_isPullback_app fun T => ?_
    obtain ⟨T⟩ := T
    rw [Types.isPullback_iff]
    refine ⟨rfl, ?_, ?_⟩
    · rintro x y ⟨h1, h2⟩
      exact liftMs_uniq hM x y h1 (congrArg Prod.fst h2)
    · rintro l ⟨h, ξ⟩ e
      refine ⟨liftMs hM l h, liftMs_π hM l h, Prod.ext (res_liftMs hM l h) ?_⟩
      change a.app _ (liftMs hM l h ≫ _) = ξ
      rw [liftMs_π]
      exact e
  refine ⟨P, a', up_reg ⊤ hM hA, ?_, ?_⟩
  · have := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u}) SCH)
    exact MorphismProperty.of_isPullback pb hs
  · have := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) SCH)
    exact MorphismProperty.of_isPullback pb he

end Univ

section Action

variable {M : Type u} [AddCommMonoid M] {I : S.IdealSheafData}
  {X Y F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {j : Y ⟶ X} {b : F ⟶ X}
  {act : AAction (fppfO B S hS) M X} {actY : AAction (fppfO B S hS) M Y}

/-- `Y` is stable under the action. -/
def SpStable (j : Y ⟶ X) (act : AAction (fppfO B S hS) M X) (actY : AAction (fppfO B S hS) M Y) : Prop :=
  ∀ ⦃U : (BigFppfOver B S hS)ᵒᵖ⦄ (h : APt (fppfO B S hS) M U) (y : Y.obj U),
    act.smul h (j.app U y) = j.app U (actY.smul h y)

variable (hs : SpStable j act actY) (hD : IsSpDil I j b)
  (hM : B.Contains (AZ (⊤ : AddSubmonoid M)))

/-- The action on points of `X` of the dilatation. -/
noncomputable def actMap (b : F ⟶ X) (act : AAction (fppfO B S hS) M X) : APr M F ⟶ X where
  app U := ↾ fun p => act.smul p.1 (b.app U p.2)
  naturality U V f := by
    ext p
    change act.smul (APt.res f p.1) (b.app V (F.map f p.2)) = X.map f (act.smul p.1 (b.app U p.2))
    rw [act.map_smul, NatTrans.naturality_apply b]

include hs hD hM in
lemma exists_aUniv : ∃ a : APr M F ⟶ F, a ≫ b = actMap b act := by
  refine hD.exists_lift (SpReg.apr hM hD.reg) _ ?_
  rintro W ⟨h, ξ⟩ Z s hZ
  obtain ⟨y, hy⟩ := hD.factors ξ s hZ
  refine ⟨actY.smul (APt.res s.op h) y, ?_⟩
  rw [← hs, hy]
  exact (act.map_smul s.op h (b.app _ ξ)).symm

/-- The action morphism `𝔸(M) × Bl ⟶ Bl`, from the universal property. -/
noncomputable def aUniv : APr M F ⟶ F := (exists_aUniv hs hD hM).choose

/-- The value of the action on `Bl_Y^D X`. -/
noncomputable def smB {U : (BigFppfOver B S hS)ᵒᵖ} (h : APt (fppfO B S hS) M U) (ξ : F.obj U) : F.obj U :=
  (aUniv hs hD hM).app U (h, ξ)

/-- The dilatation map is equivariant (Proposition 13.1). -/
lemma smB_map {U : (BigFppfOver B S hS)ᵒᵖ} (h : APt (fppfO B S hS) M U) (ξ : F.obj U) :
    b.app U (smB hs hD hM h ξ) = act.smul h (b.app U ξ) :=
  congrArg (fun q => q.app U (h, ξ)) (exists_aUniv hs hD hM).choose_spec

lemma smB_nat {U V : (BigFppfOver B S hS)ᵒᵖ} (f : U ⟶ V) (h : APt (fppfO B S hS) M U) (ξ : F.obj U) :
    smB hs hD hM (APt.res f h) (F.map f ξ) = F.map f (smB hs hD hM h ξ) :=
  NatTrans.naturality_apply (aUniv hs hD hM) f (⟨h, ξ⟩ : (APr M F).obj U)

/-- **Proposition 13.1, first assertion**: `𝔸(M)_S` acts on `Bl_Y^D X` for an algebraic space `X`.
`b` is equivariant (`smB_map`). -/
noncomputable def blAction : AAction (fppfO B S hS) M F where
  smul h ξ := smB hs hD hM h ξ
  one_smul {U} ξ := by
    let f₁ : F ⟶ F :=
      { app := fun U => ↾ fun ξ => smB hs hD hM 1 ξ
        naturality := fun U V f => by
          ext ξ
          change smB hs hD hM 1 (F.map f ξ) = F.map f (smB hs hD hM 1 ξ)
          rw [← smB_nat]
          congr 1
          ext; simp }
    have : f₁ = 𝟙 F := hD.uniq hD.reg _ _ (by
      ext V ξ
      refine (smB_map hs hD hM 1 ξ).trans ?_
      exact act.one_smul _)
    exact congrArg (fun q => q.app U ξ) this
  mul_smul {U} g h ξ := by
    let T := APr M (APr M F)
    let f₁ : T ⟶ F :=
      { app := fun V => ↾ fun p => smB hs hD hM (p.1 * p.2.1) p.2.2
        naturality := fun V W f => by
          ext ⟨p, q, ξ⟩
          change smB hs hD hM (APt.res f p * APt.res f q) (F.map f ξ) = F.map f (smB hs hD hM (p * q) ξ)
          rw [← smB_nat, APt.res_mul] }
    let f₂ : T ⟶ F :=
      { app := fun V => ↾ fun p => smB hs hD hM p.1 (smB hs hD hM p.2.1 p.2.2)
        naturality := fun V W f => by
          ext ⟨p, q, ξ⟩
          change smB hs hD hM (APt.res f p) (smB hs hD hM (APt.res f q) (F.map f ξ)) =
            F.map f (smB hs hD hM p (smB hs hD hM q ξ))
          rw [← smB_nat, smB_nat] }
    have : f₁ = f₂ := hD.uniq (SpReg.apr hM (SpReg.apr hM hD.reg)) _ _ (by
      ext V ⟨p, q, ξ⟩
      change b.app V (smB hs hD hM (p * q) ξ) = b.app V (smB hs hD hM p (smB hs hD hM q ξ))
      rw [smB_map, smB_map, smB_map, act.mul_smul])
    exact congrArg (fun q => q.app U (g, h, ξ)) this
  map_smul {U V} f h ξ := (smB_nat hs hD hM f h ξ).symm

end Action

end AlgMag.DilSp

end PartG

section PartH

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry


namespace AlgMag.DilSp

open Dil GB

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "C" => BigFppfOver B S hS
local notation "SCH" => BigFppfOver.toScheme B S hS
local notation "J" => BigFppfOver.topology B S hS

section Descent

lemma injective_stalkMap_of_flat {X X₁ : Scheme.{u}} (f : X₁ ⟶ X) [Flat f] (x : X₁) :
    Function.Injective (f.stalkMap x).hom := by
  let φ : X.presheaf.stalk (f x) →+* X₁.presheaf.stalk x := (f.stalkMap x).hom
  algebraize [φ]
  have hfl : Module.Flat (X.presheaf.stalk (f x)) (X₁.presheaf.stalk x) := Flat.stalkMap f x
  have hloc : IsLocalHom (algebraMap (X.presheaf.stalk (f x)) (X₁.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have : Module.FaithfullyFlat (X.presheaf.stalk (f x)) (X₁.presheaf.stalk x) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact FaithfulSMul.algebraMap_injective _ _

lemma reg_descent_aux {I : S.IdealSheafData} {X X₁ : Scheme.{u}} (p : X ⟶ S) (f : X₁ ⟶ X) [Flat f]
    [Surjective f]
    (h : ∀ (t : X₁) (U : S.affineOpens) (r : Γ(S, U.1)) (_ : I.ideal U = Ideal.span {r})
      (ht : (f ≫ p) t ∈ U.1) (g : X₁.presheaf.stalk t),
      (f ≫ p).stalkMap t (S.presheaf.germ U.1 ((f ≫ p) t) ht r) * g = 0 → g = 0)
    (t : X) (U : S.affineOpens) (r : Γ(S, U.1)) (hr : I.ideal U = Ideal.span {r})
    (ht : p t ∈ U.1) (g : X.presheaf.stalk t)
    (hg : p.stalkMap t (S.presheaf.germ U.1 (p t) ht r) * g = 0) : g = 0 := by
  obtain ⟨x, rfl⟩ := f.surjective t
  apply injective_stalkMap_of_flat f x
  rw [map_zero]
  refine h x U r hr ht _ ?_
  rw [Scheme.Hom.stalkMap_comp]
  change (f.stalkMap x).hom _ * _ = 0
  rw [← map_mul]
  exact (congrArg (f.stalkMap x).hom hg).trans (map_zero _)

/-- Regularity descends along flat surjective morphisms. -/
lemma isRegular_descent {I : S.IdealSheafData} {T T₁ : Over S} (f : T₁ ⟶ T) [Flat f.left]
    [Surjective f.left] (h : IsRegular I T₁) : IsRegular I T := by
  have key : ∀ (p₁ : T₁.left ⟶ S) (_ : f.left ≫ T.hom = p₁), (∀ (t : T₁.left) (U : S.affineOpens)
      (r : Γ(S, U.1)) (_ : I.ideal U = Ideal.span {r}) (ht : p₁ t ∈ U.1)
      (g : T₁.left.presheaf.stalk t), p₁.stalkMap t (S.presheaf.germ U.1 (p₁ t) ht r) * g = 0 →
      g = 0) → IsRegular I T := by
    rintro _ rfl hh
    exact reg_descent_aux T.hom f.left hh
  exact key _ (Over.w f) h

end Descent

section Attractor

variable {M : Type u} [AddCommMonoid M] {I : S.IdealSheafData}
  {X Y F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {j : Y ⟶ X} {b : F ⟶ X}
  {act : AAction (fppfO B S hS) M X} {actY : AAction (fppfO B S hS) M Y}
  {N : AddSubmonoid M}

/-- The map `f^N` on points. -/
def pushPt {A A' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {ac : AAction (fppfO B S hS) M A}
    {ac' : AAction (fppfO B S hS) M A'} (f : A ⟶ A')
    (hf : ∀ ⦃U : (BigFppfOver B S hS)ᵒᵖ⦄ (h : APt (fppfO B S hS) M U) (x : A.obj U),
      f.app U (ac.smul h x) = ac'.smul h (f.app U x))
    {T : BigFppfOver B S hS} (φ : AttractorPt ac N T) : AttractorPt ac' N T where
  app t a := f.app _ (φ.app t a)
  naturality s t a := by
    rw [φ.naturality, NatTrans.naturality_apply f]
  equivariant t h a := by
    rw [φ.equivariant, hf]

/-- The attractor map `f^N`. -/
def repMap {A A' Z Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {ac : AAction (fppfO B S hS) M A}
    {ac' : AAction (fppfO B S hS) M A'} (f : A ⟶ A')
    (hf : ∀ ⦃U : (BigFppfOver B S hS)ᵒᵖ⦄ (h : APt (fppfO B S hS) M U) (x : A.obj U),
      f.app U (ac.smul h x) = ac'.smul h (f.app U x))
    (r : RepresentsAttractor ac N Z) (r' : RepresentsAttractor ac' N Z') : Z ⟶ Z' where
  app U := ↾ fun z => (r'.equiv U.unop).symm (pushPt f hf (r.equiv U.unop z))
  naturality U V s := by
    refine ConcreteCategory.hom_ext _ _ fun z => ?_
    obtain ⟨U⟩ := U
    obtain ⟨V⟩ := V
    obtain ⟨s, rfl⟩ : ∃ s' : V ⟶ U, s = s'.op := ⟨s.unop, rfl⟩
    apply (r'.equiv V).injective
    change r'.equiv V ((r'.equiv V).symm (pushPt f hf (r.equiv V (Z.map s.op z)))) =
      r'.equiv V (Z'.map s.op ((r'.equiv U).symm (pushPt f hf (r.equiv U z))))
    rw [r'.naturality, Equiv.apply_symm_apply, Equiv.apply_symm_apply, r.naturality]
    rfl

lemma equiv_repMap {A A' Z Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {ac : AAction (fppfO B S hS) M A}
    {ac' : AAction (fppfO B S hS) M A'} (f : A ⟶ A')
    (hf : ∀ ⦃U : (BigFppfOver B S hS)ᵒᵖ⦄ (h : APt (fppfO B S hS) M U) (x : A.obj U),
      f.app U (ac.smul h x) = ac'.smul h (f.app U x))
    (r : RepresentsAttractor ac N Z) (r' : RepresentsAttractor ac' N Z') {W : BigFppfOver B S hS}
    (z : Z.obj (op W)) :
    r'.equiv W ((repMap f hf r r').app (op W) z) = pushPt f hf (r.equiv W z) :=
  Equiv.apply_symm_apply _ _

variable (hs : SpStable j act actY) (hD : IsSpDil I j b)
  (hM : B.Contains (AZ (⊤ : AddSubmonoid M))) (hN : B.Contains (AZ N))
  {ZX ZY ZB : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (rX : RepresentsAttractor act N ZX) (rY : RepresentsAttractor actY N ZY)
  (rB : RepresentsAttractor (blAction hs hD hM) N ZB)

/-- `j^N : Y^N ⟶ X^N`. -/
def jN : ZY ⟶ ZX := repMap j (fun _ h y => (hs h y).symm) rY rX

/-- `b^N : (Bl_Y^D X)^N ⟶ X^N`. -/
noncomputable def bN : ZB ⟶ ZX := repMap b (fun _ h ξ => smB_map hs hD hM h ξ) rB rX

set_option maxHeartbeats 2000000 in
include hN in
/-- **Proposition 13.1** for algebraic spaces, in universal form: if `(Bl_Y^D X)^N` is `S'`-regular
then `b^N` is the dilatation of `X^N` with center `Y^N`. -/
theorem attractor_isSpDil [Mono j] (hZB : Presheaf.IsSheaf J ZB) (hZX : Presheaf.IsSheaf J ZX)
    (hreg : SpReg I ZB) : IsSpDil I (jN hs rX rY) (bN hs hD hM rX rB) := by
  have inj : ∀ U, Function.Injective (j.app U) := fun U =>
    (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 inferInstance U)
  refine isSpDil_of_site hZB hZX hreg ?_ ?_ ?_
  · intro T z Z s hZ
    let ψ := rB.equiv Z (ZB.map s.op z)
    have hval : ∀ (T' : C) (t : T' ⟶ Z) (a : APt (fppfO B S hS) N (op T')),
        ∃ y : Y.obj (op T'), j.app _ y = b.app _ (ψ.app t a) := by
      intro T' t a
      have hL : Lies I T' := LiesOver.of_hom hZ (toO.map t)
      obtain ⟨y, hy⟩ := hD.factors (ψ.app t a) (𝟙 T') hL
      refine ⟨y, hy.trans ?_⟩
      rw [op_id, CategoryTheory.Functor.map_id_apply]
    choose y hy using hval
    let γ : AttractorPt actY N Z :=
      { app := fun {T'} t a => y T' t a
        naturality := fun {T' T''} v t a => by
          apply inj
          rw [hy, NatTrans.naturality_apply j, hy, ψ.naturality, NatTrans.naturality_apply b]
        equivariant := fun {T'} t h a => by
          apply inj
          rw [hy, ← hs, hy, ψ.equivariant]
          exact smB_map hs hD hM h _ }
    refine ⟨(rY.equiv Z).symm γ, (rX.equiv Z).injective ?_⟩
    have h1 := equiv_repMap j (fun _ h y => (hs h y).symm) rY rX ((rY.equiv Z).symm γ)
    refine h1.trans ?_
    rw [Equiv.apply_symm_apply, rX.naturality]
    have h2 := equiv_repMap b (fun _ h ξ => smB_map hs hD hM h ξ) rB rX z
    change _ = ((rX.equiv T) ((bN hs hD hM rX rB).app (op T) z)).baseChange s
    rw [show (rX.equiv T) ((bN hs hD hM rX rB).app (op T) z) = _ from h2]
    refine AttractorPt.ext ?_
    funext T' t a
    refine (hy T' t a).trans ?_
    change b.app _ ((rB.equiv Z (ZB.map s.op z)).app t a) = b.app _ ((rB.equiv T z).app (t ≫ s) a)
    rw [rB.naturality]
    rfl
  · intro W hW z hz
    let φ := rX.equiv W z
    let U := up N hN W
    have hP : Reg I U.P := up_reg N hN hW
    have hfac : SpFac I j (φ.app U.π U.u) := by
      intro Z s hZ
      obtain ⟨y, hy⟩ := hz (s ≫ U.π) hZ
      let γ := rY.equiv Z y
      have h1 : pushPt j (fun _ h y => (hs h y).symm) γ = φ.baseChange (s ≫ U.π) := by
        have := equiv_repMap j (fun _ h y => (hs h y).symm) rY rX y
        refine this.symm.trans ?_
        rw [show (repMap j (fun _ h y => (hs h y).symm) rY rX).app (op Z) y = _ from hy, rX.naturality]
      let u' := APt.res s.op U.u
      refine ⟨γ.app (𝟙 Z) u', ?_⟩
      have h2 := congrArg (fun p : AttractorPt act N Z => p.app (𝟙 Z) u') h1
      refine h2.trans ?_
      change φ.app (𝟙 Z ≫ s ≫ U.π) u' = _
      rw [Category.id_comp]
      exact φ.naturality s U.π U.u
    obtain ⟨v, hv⟩ := hD.lift_pt hP _ hfac
    have hval : ∀ {T' : C} (t : T' ⟶ W) (a : APt (fppfO B S hS) N (op T')),
        b.app _ (F.map (U.lift t a).op v) = φ.app t a := by
      intro T' t a
      rw [NatTrans.naturality_apply b, hv]
      exact (φ.app_eq_of_universal U t a).symm
    have hequiv : ∀ {T' : C} (t : T' ⟶ W) (h : APt (fppfO B S hS) M (op T'))
        (a : APt (fppfO B S hS) N (op T')),
        F.map (U.lift t (APt.toMagnet N h * a)).op v =
          smB hs hD hM h (F.map (U.lift t a).op v) := by
      intro T' t h a
      let Q := up ⊤ hM U.P
      let p2 : Q.P ⟶ U.P := Q.π
      let tt : Q.P ⟶ W := p2 ≫ U.π
      let hh := gMs hM U.P
      let aa : APt (fppfO B S hS) N (op Q.P) := APt.res p2.op U.u
      have hQ : Reg I Q.P := up_reg ⊤ hM hP
      have key : F.map (U.lift tt (APt.toMagnet N hh * aa)).op v =
          smB hs hD hM hh (F.map (U.lift tt aa).op v) := hD.uniq_pt hQ _ _ (by
        rw [hval, smB_map, hval]
        exact φ.equivariant tt hh aa)
      let s' : T' ⟶ Q.P := liftMs hM (U.lift t a) h
      have hst : s' ≫ tt = t := by
        have : s' ≫ p2 = U.lift t a := liftMs_π hM _ _
        change s' ≫ p2 ≫ U.π = t
        rw [← Category.assoc, this, U.lift_π]
      have e1 : APt.res s'.op hh = h := res_liftMs hM _ _
      have e2 : APt.res s'.op aa = a := by
        change APt.res s'.op (APt.res p2.op U.u) = a
        rw [← APt.res_comp]
        have h2 : p2.op ≫ s'.op = (s' ≫ p2).op := rfl
        have h3 : s' ≫ p2 = U.lift t a := liftMs_π hM _ _
        rw [h2, h3]
        exact U.res_lift t a
      have e3 : ∀ c : APt (fppfO B S hS) N (op Q.P),
          F.map s'.op (F.map (U.lift tt c).op v) = F.map (U.lift t (APt.res s'.op c)).op v := by
        intro c
        rw [← Functor.map_comp_apply, ← op_comp, ← U.lift_comp, hst]
      have e := congrArg (F.map s'.op) key
      rw [e3, ← smB_nat, e3, APt.res_mul, ← APt.toMagnet_res, e1, e2] at e
      exact e
    let ψ : AttractorPt (blAction hs hD hM) N W :=
      (attractorPtEquivOfUniversal U).symm ⟨v, fun t h a => hequiv t h a⟩
    refine ⟨(rB.equiv W).symm ψ, (rX.equiv W).injective ?_⟩
    refine (equiv_repMap b (fun _ h ξ => smB_map hs hD hM h ξ) rB rX _).trans ?_
    rw [Equiv.apply_symm_apply]
    refine AttractorPt.ext ?_
    funext T' t a
    exact hval t a
  · intro W hW z₁ z₂ e
    let U := up N hN W
    apply (rB.equiv W).injective
    have h1 := equiv_repMap b (fun _ h ξ => smB_map hs hD hM h ξ) rB rX z₁
    have h2 := equiv_repMap b (fun _ h ξ => smB_map hs hD hM h ξ) rB rX z₂
    have h3 : pushPt b (fun _ h ξ => smB_map hs hD hM h ξ) (rB.equiv W z₁) =
        pushPt b (fun _ h ξ => smB_map hs hD hM h ξ) (rB.equiv W z₂) :=
      h1.symm.trans ((congrArg _ e).trans h2)
    have hu : (rB.equiv W z₁).app U.π U.u = (rB.equiv W z₂).app U.π U.u :=
      hD.uniq_pt (up_reg N hN hW) _ _
        (congrArg (fun p : AttractorPt act N W => p.app U.π U.u) h3)
    refine AttractorPt.ext ?_
    funext T' t a
    rw [(rB.equiv W z₁).app_eq_of_universal U t a, (rB.equiv W z₂).app_eq_of_universal U t a, hu]

include hs hD hM rB in
/-- `(Bl_Y^D X)^N` is `S'`-regular when it has a surjective étale atlas which is flat over `S`:
it maps to `Bl_Y^D X`. -/
lemma spReg_attractor {U₀ : BigFppfOver B S hS} (c₀ : yoneda.obj U₀ ⟶ ZB)
    (hs₀ : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u}) SCH).presheaf c₀)
    (he₀ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) SCH).presheaf c₀)
    (hfl : Flat ((toO (B := B) (hS := hS)).obj U₀).hom) : SpReg I ZB := by
  refine ⟨U₀, c₀, ?_, hs₀, he₀⟩
  obtain ⟨A, a, hA, hsa, hea⟩ := hD.reg
  let ξ₀ : F.obj (op U₀) := (rB.equiv U₀ (yonedaEquiv c₀)).toPoint
  let g : yoneda.obj U₀ ⟶ F := yonedaEquiv.symm ξ₀
  let hrep := hea.rep
  let P : BigFppfOver B S hS := hrep.pullback g
  let q : P ⟶ U₀ := hrep.snd g
  let α : P ⟶ A := yoneda.preimage (hrep.fst g)
  have hpb : IsPullback (yoneda.map α) (yoneda.map q) a g := by
    have := hrep.isPullback g
    simpa only [α, yoneda.map_preimage] using this
  have hqS : Surjective ((SCH).map q) := hsa.2 g (yoneda.map α) q hpb
  have hqE : Etale ((SCH).map q) := hea.2 g (yoneda.map α) q hpb
  let G := toO (B := B) (hS := hS)
  have hqF : Flat (G.map q).left := (Etale.iff_flat_and_formallyUnramified.1 hqE).1
  have hqS' : Surjective (G.map q).left := hqS
  have hPfl : Flat (G.obj P).hom := by
    rw [← Over.w (G.map q)]
    exact MorphismProperty.comp_mem @Flat _ _ hqF hfl
  have hPr : Reg I P := isRegular_of_flat_of_hom (G.map α) hA
  exact isRegular_descent (G.map q) hPr

include hN in
/-- **Proposition 13.1** (Mayeux, *Algebraic Magnetism*), `S` a scheme, `X` an algebraic space,
`Y` a closed subspace lying over a closed locally principal `S'`, stable under `𝔸(M)_S`, `N` a
magnet, and `X^N`, `Y^N`, `(Bl_Y^D X)^N` represented by sheaves. If `(Bl_Y^D X)^N` has a surjective
étale atlas flat over `S`, then `b^N` is the dilatation of `X^N` with center `Y^N`; so
`(Bl_Y^D X)^N = Bl_{Y^N}^{D^N} X^N` canonically over `X^N` for any model `B'` of the latter. -/
theorem prop13_1_spaces [Mono j] (hZB : Presheaf.IsSheaf J ZB) (hZX : Presheaf.IsSheaf J ZX)
    {U₀ : BigFppfOver B S hS} (c₀ : yoneda.obj U₀ ⟶ ZB)
    (hs₀ : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u}) SCH).presheaf c₀)
    (he₀ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) SCH).presheaf c₀)
    (hfl : Flat ((toO (B := B) (hS := hS)).obj U₀).hom)
    {B' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {b' : B' ⟶ ZX} (hB' : IsSpDil I (jN hs rX rY) b') :
    IsSpDil I (jN hs rX rY) (bN hs hD hM rX rB) ∧
      ∃ e : ZB ≅ B', e.hom ≫ b' = bN hs hD hM rX rB := by
  have h := attractor_isSpDil hs hD hM hN rX rY rB hZB hZX
    (spReg_attractor hs hD hM rB c₀ hs₀ he₀ hfl)
  exact ⟨h, h.exists_iso hB'⟩

end Attractor

end AlgMag.DilSp

end PartH

#print axioms AlgMag.DilSp.exists_spDilatation
#print axioms AlgMag.DilSp.IsSpDil.exists_iso
#print axioms AlgMag.DilSp.blAction
#print axioms AlgMag.DilSp.attractor_isSpDil
#print axioms AlgMag.DilSp.prop13_1_spaces
