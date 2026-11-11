/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Scheme input for the counterexample to the last assertion of Proposition 14.4

* `AlgMag.Sec14Counter.twist`: the action on `X` of `μ₂` through an involution `σ`, when `2` is
  invertible: a section `ε` with `ε² = 1` splits the source into `ε = 1` and `ε = -1`, and `twist`
  is the identity on the first part and `σ` on the second.
* `AlgMag.Sec14Counter.doubled`: `A` with the complement of an open `D` doubled, and its swap.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgMag.Sec14Counter

section Twist

variable {X U : Scheme.{u}}

/-- A point lies in the open where `a` or the open where `b` is invertible, if `a + b` is a unit. -/
theorem basicOpen_sup_of_isUnit_add (a b : Γ(U, ⊤)) (h : IsUnit (a + b)) (x : U) :
    x ∈ U.basicOpen a ∨ x ∈ U.basicOpen b := by
  have hx := h.map (U.presheaf.germ ⊤ x trivial).hom
  rw [map_add] at hx
  obtain h' | h' := IsLocalRing.isUnit_or_isUnit_of_isUnit_add hx
  · exact Or.inl ((Scheme.mem_basicOpen_top _ _ _).2 h')
  · exact Or.inr ((Scheme.mem_basicOpen_top _ _ _).2 h')

/-- A global section invertible at every point is a unit. -/
theorem isUnit_of_basicOpen_eq_top (a : Γ(U, ⊤)) (h : U.basicOpen a = ⊤) : IsUnit a := by
  refine RingedSpace.isUnit_of_isUnit_germ U.toSheafedSpace ⊤ a fun x hx => ?_
  have : x ∈ U.basicOpen a := by rw [h]; trivial
  exact (Scheme.mem_basicOpen_top _ _ _).1 this

variable (ε : Γ(U, ⊤))

/-- The locus `ε = 1`. -/
noncomputable abbrev Vp : U.Opens := U.basicOpen (1 + ε)
/-- The locus `ε = -1`. -/
noncomputable abbrev Vm : U.Opens := U.basicOpen (1 - ε)
/-- Both loci. -/
noncomputable def Vb : Bool → U.Opens
  | true => Vp ε
  | false => Vm ε

variable {ε}

theorem isOpenCover_V (h2 : IsUnit (2 : Γ(U, ⊤))) : TopologicalSpace.IsOpenCover (Vb ε) := by
  rw [TopologicalSpace.IsOpenCover, eq_top_iff]
  intro x _
  have : (1 + ε) + (1 - ε) = 2 := by ring
  obtain h | h := basicOpen_sup_of_isUnit_add (1 + ε) (1 - ε) (this ▸ h2) x
  · exact TopologicalSpace.Opens.mem_iSup.2 ⟨true, h⟩
  · exact TopologicalSpace.Opens.mem_iSup.2 ⟨false, h⟩

theorem Vp_inf_Vm (hε : ε * ε = 1) : Vp ε ⊓ Vm ε = ⊥ := by
  rw [Vp, Vm, ← Scheme.basicOpen_mul]
  have : (1 + ε) * (1 - ε) = 0 := by linear_combination -hε
  rw [this, Scheme.basicOpen_zero]

theorem isUnit_two_map {W : Scheme.{u}} (g : W ⟶ U) (h2 : IsUnit (2 : Γ(U, ⊤))) :
    IsUnit (2 : Γ(W, ⊤)) := by
  have h2' := h2.map g.appTop.hom
  rwa [map_ofNat] at h2'

theorem appTop_mul' {W : Scheme.{u}} (g : W ⟶ U) (a b : Γ(U, ⊤)) :
    g.appTop (a * b) = g.appTop a * g.appTop b := map_mul g.appTop.hom a b

theorem appTop_one' {W : Scheme.{u}} (g : W ⟶ U) : g.appTop (1 : Γ(U, ⊤)) = 1 :=
  map_one g.appTop.hom

theorem appTop_comp' {W W' : Scheme.{u}} (h : W' ⟶ W) (g : W ⟶ U) (a : Γ(U, ⊤)) :
    (h ≫ g).appTop a = h.appTop (g.appTop a) := by
  rw [Scheme.Hom.comp_appTop]; rfl

theorem appTop_neg_one' {W : Scheme.{u}} (g : W ⟶ U) : g.appTop (-1 : Γ(U, ⊤)) = -1 := by
  have : g.appTop.hom (-1 : Γ(U, ⊤)) = -1 := by rw [map_neg, map_one]
  exact this

theorem factor_Vp {W : Scheme.{u}} (g : W ⟶ U) (h2 : IsUnit (2 : Γ(U, ⊤)))
    (h : g.appTop ε = 1) : g ⁻¹ᵁ (Vp ε) = ⊤ := by
  rw [Vp, Scheme.preimage_basicOpen_top]
  apply Scheme.basicOpen_of_isUnit
  have e : g.appTop.hom (1 + ε) = 2 := by
    rw [map_add, map_one]
    change 1 + g.appTop ε = 2
    rw [h]; norm_num
  change IsUnit (g.appTop.hom (1 + ε))
  rw [e]
  exact isUnit_two_map g h2

theorem factor_Vm {W : Scheme.{u}} (g : W ⟶ U) (h2 : IsUnit (2 : Γ(U, ⊤)))
    (h : g.appTop ε = -1) : g ⁻¹ᵁ (Vm ε) = ⊤ := by
  rw [Vm, Scheme.preimage_basicOpen_top]
  apply Scheme.basicOpen_of_isUnit
  have e : g.appTop.hom (1 - ε) = 2 := by
    rw [map_sub, map_one]
    change 1 - g.appTop ε = 2
    rw [h]; norm_num
  change IsUnit (g.appTop.hom (1 - ε))
  rw [e]
  exact isUnit_two_map g h2

/-- `g` factors through an open containing its image. -/
theorem exists_factor {W : Scheme.{u}} (g : W ⟶ U) (V : U.Opens) (h : g ⁻¹ᵁ V = ⊤) :
    ∃ l : W ⟶ (V : Scheme.{u}), l ≫ V.ι = g := by
  have hr : Set.range g ⊆ Set.range V.ι := by
    rintro _ ⟨w, rfl⟩
    have : w ∈ g ⁻¹ᵁ V := by rw [h]; trivial
    simpa using this
  exact ⟨IsOpenImmersion.lift V.ι g hr, IsOpenImmersion.lift_fac _ _ _⟩

theorem unit_on_V (V : U.Opens) (a : Γ(U, ⊤)) (h : V = U.basicOpen a) :
    IsUnit (V.ι.appTop.hom a) := by
  apply isUnit_of_basicOpen_eq_top
  change (V : Scheme.{u}).basicOpen (V.ι.appTop a) = ⊤
  rw [← Scheme.preimage_basicOpen_top, ← h, Scheme.Opens.ι_preimage_self]

theorem appTop_ι_Vp (hε : ε * ε = 1) : (Vp ε).ι.appTop ε = 1 := by
  have hu := unit_on_V (Vp ε) (1 + ε) rfl
  have h0 : (Vp ε).ι.appTop.hom (1 + ε) * (Vp ε).ι.appTop.hom (1 - ε) = 0 := by
    rw [← map_mul]
    have : (1 + ε) * (1 - ε) = 0 := by linear_combination -hε
    rw [this, map_zero]
  have := (hu.mul_right_eq_zero).1 h0
  rw [map_sub, map_one] at this
  exact (sub_eq_zero.1 this).symm

theorem appTop_ι_Vm (hε : ε * ε = 1) : (Vm ε).ι.appTop ε = -1 := by
  have hu := unit_on_V (Vm ε) (1 - ε) rfl
  have h0 : (Vm ε).ι.appTop.hom (1 - ε) * (Vm ε).ι.appTop.hom (1 + ε) = 0 := by
    rw [← map_mul]
    have : (1 - ε) * (1 + ε) = 0 := by linear_combination -hε
    rw [this, map_zero]
  have := (hu.mul_right_eq_zero).1 h0
  rw [map_add, map_one] at this
  exact eq_neg_of_add_eq_zero_right this

/-- Morphisms out of `U` are compared on the loci `ε = 1` and `ε = -1`. -/
theorem hom_ext_sign (hε : ε * ε = 1) (h2 : IsUnit (2 : Γ(U, ⊤))) {a b : U ⟶ X}
    (H : ∀ {W : Scheme.{u}} (g : W ⟶ U), (g.appTop ε = 1 ∨ g.appTop ε = -1) → g ≫ a = g ≫ b) :
    a = b := by
  refine (U.openCoverOfIsOpenCover _ (isOpenCover_V (ε := ε) h2)).hom_ext _ _ fun c => ?_
  cases c
  · exact H _ (Or.inr (appTop_ι_Vm hε))
  · exact H _ (Or.inl (appTop_ι_Vp hε))

variable (σ : X ⟶ X)

/-- `y` is the twist of `x` by `ε` through `σ`: `x` on `ε = 1`, and `σ ∘ x` on `ε = -1`. -/
structure IsTwist (ε : Γ(U, ⊤)) (x y : U ⟶ X) : Prop where
  plus : ∀ {W : Scheme.{u}} (g : W ⟶ U), g.appTop ε = 1 → g ≫ y = g ≫ x
  minus : ∀ {W : Scheme.{u}} (g : W ⟶ U), g.appTop ε = -1 → g ≫ y = g ≫ x ≫ σ

theorem exists_isTwist (hε : ε * ε = 1) (h2 : IsUnit (2 : Γ(U, ⊤))) (x : U ⟶ X) :
    ∃ y, IsTwist σ ε x y := by
  let C := U.openCoverOfIsOpenCover _ (isOpenCover_V (ε := ε) h2)
  let f : ∀ c : Bool, C.X c ⟶ X := fun c =>
    match c with
    | true => (Vp ε).ι ≫ x
    | false => (Vm ε).ι ≫ x ≫ σ
  have hf : ∀ c d : Bool, pullback.fst (C.f c) (C.f d) ≫ f c = pullback.snd (C.f c) (C.f d) ≫ f d := by
    have hempty : ∀ c d : Bool, c ≠ d → IsEmpty (↑(pullback (C.f c) (C.f d) : Scheme.{u})) := by
      intro c d hcd
      refine ⟨fun z => ?_⟩
      have h1 : (C.f c) (pullback.fst (C.f c) (C.f d) z) ∈ Vb ε c :=
        (pullback.fst (C.f c) (C.f d) z).2
      have e : (C.f c) (pullback.fst (C.f c) (C.f d) z) = (C.f d) (pullback.snd (C.f c) (C.f d) z) := by
        simp only [← Scheme.Hom.comp_apply, pullback.condition]
      have h3 : (C.f d) (pullback.snd (C.f c) (C.f d) z) ∈ Vb ε d :=
        (pullback.snd (C.f c) (C.f d) z).2
      rw [← e] at h3
      have hb := Vp_inf_Vm hε
      have hmem : (C.f c) (pullback.fst (C.f c) (C.f d) z) ∈ Vp ε ⊓ Vm ε := by
        cases c <;> cases d <;> first | exact absurd rfl hcd | exact ⟨h3, h1⟩ | exact ⟨h1, h3⟩
      rw [hb] at hmem
      exact hmem
    intro c d
    by_cases hcd : c = d
    · subst hcd
      haveI : Mono (C.f c) := inferInstanceAs (Mono (Vb ε c).ι)
      have : pullback.fst (C.f c) (C.f c) = pullback.snd (C.f c) (C.f c) :=
        (cancel_mono (C.f c)).1 pullback.condition
      rw [this]
    · have := hempty c d hcd
      exact (isInitialOfIsEmpty).hom_ext _ _
  refine ⟨C.glueMorphisms f hf, ?_, ?_⟩
  · intro W g hg
    obtain ⟨l, rfl⟩ := exists_factor g (Vp ε) (factor_Vp g h2 hg)
    have := C.ι_glueMorphisms f hf true
    rw [Category.assoc, Category.assoc]
    exact congrArg (l ≫ ·) this
  · intro W g hg
    obtain ⟨l, rfl⟩ := exists_factor g (Vm ε) (factor_Vm g h2 hg)
    have := C.ι_glueMorphisms f hf false
    rw [Category.assoc, Category.assoc]
    exact congrArg (l ≫ ·) this

theorem IsTwist.unique (hε : ε * ε = 1) (h2 : IsUnit (2 : Γ(U, ⊤))) {x y y' : U ⟶ X}
    (h : IsTwist σ ε x y) (h' : IsTwist σ ε x y') : y = y' :=
  hom_ext_sign hε h2 fun g hg => by
    obtain hg | hg := hg
    · rw [h.plus g hg, h'.plus g hg]
    · rw [h.minus g hg, h'.minus g hg]

/-- The action of the point `ε` of `μ₂` on `x`, through `σ`. -/
noncomputable def twist (hε : ε * ε = 1) (h2 : IsUnit (2 : Γ(U, ⊤))) (x : U ⟶ X) : U ⟶ X :=
  (exists_isTwist σ hε h2 x).choose

theorem isTwist_twist (hε : ε * ε = 1) (h2 : IsUnit (2 : Γ(U, ⊤))) (x : U ⟶ X) :
    IsTwist σ ε x (twist σ hε h2 x) :=
  (exists_isTwist σ hε h2 x).choose_spec

theorem twist_of_eq_one (hε : ε * ε = 1) (h2 : IsUnit (2 : Γ(U, ⊤))) (x : U ⟶ X) (h : ε = 1) :
    twist σ hε h2 x = x := by
  simpa using (isTwist_twist σ hε h2 x).plus (𝟙 U) (by simpa using h)

theorem twist_of_eq_neg_one (hε : ε * ε = 1) (h2 : IsUnit (2 : Γ(U, ⊤))) (x : U ⟶ X) (h : ε = -1) :
    twist σ hε h2 x = x ≫ σ := by
  simpa using (isTwist_twist σ hε h2 x).minus (𝟙 U) (by simpa using h)

theorem comp_twist {W : Scheme.{u}} (k : W ⟶ U) (hε : ε * ε = 1) (h2 : IsUnit (2 : Γ(U, ⊤)))
    (x : U ⟶ X) (hε' : k.appTop ε * k.appTop ε = 1) (h2' : IsUnit (2 : Γ(W, ⊤))) :
    k ≫ twist σ hε h2 x = twist σ hε' h2' (k ≫ x) := by
  refine hom_ext_sign hε' h2' fun g hg => ?_
  have ht := isTwist_twist σ hε h2 x
  have ht' := isTwist_twist σ hε' h2' (k ≫ x)
  obtain hg | hg := hg
  · rw [ht'.plus g hg, ← Category.assoc, ht.plus (g ≫ k) (by rw [appTop_comp']; exact hg),
      Category.assoc]
  · rw [ht'.minus g hg, ← Category.assoc, ht.minus (g ≫ k) (by rw [appTop_comp']; exact hg)]
    simp

theorem twist_mul {δ : Γ(U, ⊤)} (hσ : σ ≫ σ = 𝟙 X) (hε : ε * ε = 1) (hδ : δ * δ = 1)
    (hm : (ε * δ) * (ε * δ) = 1) (h2 : IsUnit (2 : Γ(U, ⊤))) (x : U ⟶ X) :
    twist σ hm h2 x = twist σ hε h2 (twist σ hδ h2 x) := by
  refine hom_ext_sign hε h2 fun {W} g hg => ?_
  have h2W := isUnit_two_map g h2
  have hδ' : g.appTop δ * g.appTop δ = 1 := by rw [← appTop_mul', hδ, appTop_one']
  refine hom_ext_sign hδ' h2W fun {W'} g' hg' => ?_
  rw [← Category.assoc, ← Category.assoc]
  have hgε : (g' ≫ g).appTop ε = 1 ∨ (g' ≫ g).appTop ε = -1 := by
    obtain h | h := hg
    · exact Or.inl (by rw [appTop_comp', h, appTop_one'])
    · exact Or.inr (by rw [appTop_comp', h, appTop_neg_one'])
  have hgδ : (g' ≫ g).appTop δ = 1 ∨ (g' ≫ g).appTop δ = -1 := by
    rw [appTop_comp']; exact hg'
  set G := g' ≫ g
  have tm := isTwist_twist σ hm h2 x
  have t1 := isTwist_twist σ hε h2 (twist σ hδ h2 x)
  have t2 := isTwist_twist σ hδ h2 x
  obtain h1 | h1 := hgε <;> obtain h3 | h3 := hgδ
  · rw [tm.plus G (by rw [appTop_mul', h1, h3]; simp), t1.plus G h1, t2.plus G h3]
  · rw [tm.minus G (by rw [appTop_mul', h1, h3]; simp), t1.plus G h1, t2.minus G h3]
  · rw [tm.minus G (by rw [appTop_mul', h1, h3]; simp), t1.minus G h1]
    simp only [← Category.assoc, t2.plus G h3]
  · rw [tm.plus G (by rw [appTop_mul', h1, h3]; simp), t1.minus G h1]
    simp only [← Category.assoc, t2.minus G h3]
    simp [hσ]

theorem twist_comp {S : Scheme.{u}} (p : X ⟶ S) (hp : σ ≫ p = p) (hε : ε * ε = 1)
    (h2 : IsUnit (2 : Γ(U, ⊤))) (x : U ⟶ X) : twist σ hε h2 x ≫ p = x ≫ p := by
  refine hom_ext_sign hε h2 fun g hg => ?_
  have t := isTwist_twist σ hε h2 x
  obtain hg | hg := hg
  · rw [← Category.assoc, t.plus g hg, Category.assoc]
  · rw [← Category.assoc, t.minus g hg]; simp [hp]

/-- If `σ ∘ x = x` every twist of `x` is `x`. -/
theorem twist_of_fixed (hε : ε * ε = 1) (h2 : IsUnit (2 : Γ(U, ⊤))) (x : U ⟶ X)
    (hx : x ≫ σ = x) : twist σ hε h2 x = x :=
  IsTwist.unique σ hε h2 (isTwist_twist σ hε h2 x)
    ⟨fun _ _ => rfl, fun g _ => by rw [hx]⟩

end Twist

section Doubled

variable {D A : Scheme.{u}} (i : D ⟶ A) [IsOpenImmersion i]

/-- The span `A ← D → A`. -/
noncomputable abbrev spanF : WidePushoutShape Bool ⥤ Scheme.{u} :=
  WidePushoutShape.wideSpan D (fun _ => A) (fun _ => i)

instance : ∀ {a b : WidePushoutShape Bool} (f : a ⟶ b), IsOpenImmersion ((spanF i).map f) := by
  rintro _ _ (_ | b)
  · simp only [WidePushoutShape.hom_id, Functor.map_id]; infer_instance
  · simpa using (inferInstance : IsOpenImmersion i)

/-- `A` with the complement of `D` doubled: two copies of `A` glued along `D`. -/
noncomputable abbrev doubled : Scheme.{u} := colimit (spanF i)

/-- The two charts. -/
noncomputable abbrev chart (b : Bool) : A ⟶ doubled i := colimit.ι (spanF i) (some b)

theorem i_comp_chart (b c : Bool) : i ≫ chart i b = i ≫ chart i c := by
  have h : ∀ b : Bool, i ≫ chart i b = colimit.ι (spanF i) none := fun b =>
    colimit.w (spanF i) (WidePushoutShape.Hom.init b)
  rw [h, h]

/-- A cocone on the span, from two maps agreeing on `D`. -/
noncomputable def spanCocone {Y : Scheme.{u}} (f : Bool → (A ⟶ Y)) (hf : i ≫ f true = i ≫ f false) :
    Cocone (spanF i) where
  pt := Y
  ι :=
    { app := fun j => match j with
        | none => i ≫ f true
        | some b => f b
      naturality := by
        rintro a _ (_ | b)
        · have e : (spanF i).map (WidePushoutShape.Hom.id a) = 𝟙 _ := (spanF i).map_id a
          erw [e]; simp
        · cases b
          · simpa using hf.symm
          · simp }

/-- A map out of the doubled scheme. -/
noncomputable def doubledDesc {Y : Scheme.{u}} (f : Bool → (A ⟶ Y))
    (hf : i ≫ f true = i ≫ f false) : doubled i ⟶ Y :=
  colimit.desc (spanF i) (spanCocone i f hf)

@[reassoc]
theorem chart_desc {Y : Scheme.{u}} (f : Bool → (A ⟶ Y)) (hf : i ≫ f true = i ≫ f false) (b : Bool) :
    chart i b ≫ doubledDesc i f hf = f b :=
  colimit.ι_desc (spanCocone i f hf) (some b)

theorem doubled_hom_ext {Y : Scheme.{u}} {a b : doubled i ⟶ Y}
    (h : ∀ c, chart i c ≫ a = chart i c ≫ b) : a = b := by
  refine colimit.hom_ext fun j => ?_
  rcases j with _ | c
  · have e : colimit.ι (spanF i) none = i ≫ chart i true :=
      (colimit.w (spanF i) (WidePushoutShape.Hom.init true)).symm
    rw [e, Category.assoc, Category.assoc, h]
  · exact h c

/-- The swap of the two charts. -/
noncomputable def swap : doubled i ⟶ doubled i :=
  doubledDesc i (fun b => chart i (!b)) (i_comp_chart i _ _)

@[reassoc (attr := simp)]
theorem chart_swap (b : Bool) : chart i b ≫ swap i = chart i (!b) :=
  chart_desc i _ _ b

theorem swap_swap : swap i ≫ swap i = 𝟙 _ :=
  doubled_hom_ext i fun c => by simp

/-- The structure morphism to `A`, the identity on both charts. -/
noncomputable def doubledToBase : doubled i ⟶ A :=
  doubledDesc i (fun _ => 𝟙 A) rfl

@[reassoc (attr := simp)]
theorem chart_toBase (b : Bool) : chart i b ≫ doubledToBase i = 𝟙 A :=
  chart_desc i _ _ b

theorem swap_toBase : swap i ≫ doubledToBase i = doubledToBase i :=
  doubled_hom_ext i fun c => by simp

/-- If the two charts agree, `D → A` is surjective. -/
theorem surjective_of_chart_eq (h : chart i true = chart i false) : Function.Surjective i := by
  intro a
  have e : colimit.ι (spanF i) (some true) a = colimit.ι (spanF i) (some false) a := by
    change chart i true a = chart i false a
    rw [h]
  obtain ⟨k, fi, fj, z, h1, h2⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff (spanF i)).1 e
  rcases k with _ | c
  · refine ⟨z, ?_⟩
    rcases fi with _ | _
    simpa using h1
  · rcases fi with _ | _
    rcases fj with _ | _

theorem charts_cover (x : doubled i) : ∃ b, x ∈ Set.range (chart i b) := by
  obtain ⟨j, y, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (spanF i) x
  rcases j with _ | c
  · refine ⟨true, i y, ?_⟩
    rw [← Scheme.Hom.comp_apply]
    exact congrArg (fun f => f y) (colimit.w (spanF i) (WidePushoutShape.Hom.init true))
  · exact ⟨c, y, rfl⟩

/-- The doubled scheme is locally of finite presentation over `A`. -/
theorem locallyOfFinitePresentation_toBase :
    LocallyOfFinitePresentation (doubledToBase i) := by
  haveI : IsZariskiLocalAtSource @LocallyOfFinitePresentation :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FinitePresentation)
  refine (IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFinitePresentation)
    (Scheme.IsLocallyDirected.openCover (spanF i))).2 fun j => ?_
  rcases j with _ | c
  · have e : (Scheme.IsLocallyDirected.openCover (spanF i)).f none ≫ doubledToBase i = i := by
      change colimit.ι (spanF i) none ≫ _ = _
      rw [← colimit.w (spanF i) (WidePushoutShape.Hom.init true), Category.assoc]
      simp
    rw [e]; exact locallyOfFinitePresentation_of_isOpenImmersion i
  · have e : (Scheme.IsLocallyDirected.openCover (spanF i)).f (some c) ≫ doubledToBase i = 𝟙 A :=
      chart_toBase i c
    rw [e]; exact locallyOfFinitePresentation_of_isOpenImmersion (𝟙 A)

end Doubled

end AlgMag.Sec14Counter
