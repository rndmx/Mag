/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.RelativeGluing
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.RingTheory.Flat.EquationalCriterion
import AlgMag.Sec13Dilatations
import AlgMag.GeneralBase
import AlgMag.GeneralBaseThm320
import AlgMag.Representation

/-!
# Attractors and dilatations over a general base

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026) 126-201, §13, for an arbitrary base scheme
`S`, schemes `X`, `Y`, and a closed locally principal subscheme `S' = V(I)` of `S`.

## Main definitions

* `AlgMag.Dil.LocPrincipal`, `AlgMag.Dil.IsRegular`: `S'` locally principal; `S'`-regular objects.
* `AlgMag.Dil.IsDilatation`: `Bl_Y^D X`, by its universal property among `S'`-regular objects.
* `AlgMag.Dil.Stable`: stability of `Y` under the action.

## Main results

* `AlgMag.Dil.exists_dilatation`: existence of `Bl_Y^D X` (glued from `AlgMag.dilatation`), and
  `Bl_Y^D X → X` is affine. `AlgMag.Dil.IsDilOn.exists_iso`: uniqueness.
* `AlgMag.Dil.blAction`, `AlgMag.Dil.smB_map`: `𝔸(M)_S` acts on `Bl_Y^D X`, equivariantly over `X`.
* `AlgMag.Dil.attractor_isDilatation`: `b^N` is the dilatation of `X^N` if `(Bl_Y^D X)^N` is regular.
* `AlgMag.Dil.prop13_1`, `AlgMag.Dil.prop13_1_of_isAffineHom`: **Proposition 13.1**.
-/

suppress_compilation

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

universe u

namespace AlgMag.Dil

section


variable {S : Scheme.{u}}

/-- `S' = V(I)` is a closed *locally principal* subscheme of `S` (§13). -/
def LocPrincipal (I : S.IdealSheafData) : Prop :=
  ∀ s : S, ∃ U : S.affineOpens, s ∈ U.1 ∧ ∃ r : Γ(S, U.1), I.ideal U = Ideal.span {r}

/-- `T ∈ Sch_S^{S'-reg}`: every local generator of the ideal of `S'` pulls back to a nonzerodivisor
on `T`, i.e. `T ×_S S' → T` is an effective Cartier divisor. -/
def IsRegular (I : S.IdealSheafData) (T : Over S) : Prop :=
  ∀ (t : T.left) (U : S.affineOpens) (r : Γ(S, U.1)) (_ : I.ideal U = Ideal.span {r})
    (ht : T.hom t ∈ U.1) (g : T.left.presheaf.stalk t),
    T.hom.stalkMap t (S.presheaf.germ U.1 (T.hom t) ht r) * g = 0 → g = 0

/-- A flat ring map preserves nonzerodivisors. -/
lemma regular_of_flat {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (hφ : φ.Flat) (c : A)
    (hc : ∀ g : A, c * g = 0 → g = 0) (g : B) (h : φ c * g = 0) : g = 0 := by
  algebraize [φ]
  have hflat : Module.Flat A B := hφ
  have reg : IsSMulRegular A c := fun a b e => by
    have : c * (a - b) = 0 := by
      simp only [smul_eq_mul] at e; rw [mul_sub, e, sub_self]
    exact sub_eq_zero.1 (hc _ this)
  refine reg.of_flat (S := B) (a₁ := g) (a₂ := 0) ?_
  simp only [smul_eq_mul, mul_zero]
  exact h

/-- A nonzerodivisor on an affine open stays one in its stalks. -/
lemma germ_regular {X : Scheme.{u}} {W : X.Opens} (hW : IsAffineOpen W) (t : X) (ht : t ∈ W)
    (c : Γ(X, W)) (hc : ∀ g : Γ(X, W), c * g = 0 → g = 0) (g : X.presheaf.stalk t)
    (h : X.presheaf.germ W t ht c * g = 0) : g = 0 := by
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨t, ht⟩ : W)
  have := hW.isLocalization_stalk ⟨t, ht⟩
  have hfl : Module.Flat Γ(X, W) (X.presheaf.stalk t) :=
    IsLocalization.flat _ (hW.primeIdealOf ⟨t, ht⟩).asIdeal.primeCompl
  exact regular_of_flat (algebraMap Γ(X, W) (X.presheaf.stalk t)) (RingHom.flat_algebraMap_iff.2 hfl)
    c hc g h

/-- Sections are detected by stalks: a stalkwise nonzerodivisor is a nonzerodivisor. -/
lemma section_regular {X : Scheme.{u}} {W : X.Opens} (c : Γ(X, W))
    (hc : ∀ (t : X) (ht : t ∈ W) (g : X.presheaf.stalk t), X.presheaf.germ W t ht c * g = 0 → g = 0)
    (g : Γ(X, W)) (h : c * g = 0) : g = 0 := by
  refine TopCat.Presheaf.section_ext X.sheaf W g 0 fun t ht => ?_
  rw [map_zero]
  refine hc t ht _ ?_
  have := congrArg (X.presheaf.germ W t ht) h
  rwa [map_mul, map_zero] at this

variable {I : S.IdealSheafData}

/-- Two generators of `I` are locally multiples of each other. -/
lemma germ_dvd {U U' : S.affineOpens} {r : Γ(S, U.1)} {r' : Γ(S, U'.1)}
    (hr : I.ideal U = Ideal.span {r}) (hr' : I.ideal U' = Ideal.span {r'}) (s : S)
    (hs : s ∈ U.1) (hs' : s ∈ U'.1) :
    ∃ v : S.presheaf.stalk s, S.presheaf.germ U.1 s hs r = v * S.presheaf.germ U'.1 s hs' r' := by
  obtain ⟨f, g, e, hf⟩ := exists_basicOpen_le_affine_inter U.2 U'.2 s ⟨hs, hs'⟩
  let D : S.affineOpens := ⟨S.basicOpen g, U'.2.basicOpen g⟩
  have hDU : D ≤ U := by
    change S.basicOpen g ≤ U.1; rw [← e]; exact S.basicOpen_le f
  have hDU' : D ≤ U' := S.basicOpen_le g
  have h1 := I.map_ideal hDU
  have h2 := I.map_ideal hDU'
  have hmem : (S.presheaf.map (homOfLE hDU).op r) ∈ (I.ideal D) := by
    rw [← h1]; exact Ideal.mem_map_of_mem _ (by rw [hr]; exact Ideal.mem_span_singleton_self r)
  rw [← h2, hr', Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hmem
  obtain ⟨v, hv⟩ := hmem
  have hsD : s ∈ D.1 := by change s ∈ S.basicOpen g; rw [← e]; exact hf
  refine ⟨S.presheaf.germ D.1 s hsD v, ?_⟩
  have a1 := TopCat.Presheaf.germ_res_apply S.presheaf (homOfLE hDU) s hsD r
  have a2 := TopCat.Presheaf.germ_res_apply S.presheaf (homOfLE hDU') s hsD r'
  rw [← a1, ← a2, ← map_mul]
  exact congrArg _ hv.symm

/-- Regularity can be tested with one generator at each point. -/
lemma isRegular_of_exists {T : Over S}
    (h : ∀ t : T.left, ∃ (U : S.affineOpens) (r : Γ(S, U.1)) (_ : I.ideal U = Ideal.span {r})
      (ht : T.hom t ∈ U.1), ∀ g : T.left.presheaf.stalk t,
      T.hom.stalkMap t (S.presheaf.germ U.1 (T.hom t) ht r) * g = 0 → g = 0) : IsRegular I T := by
  intro t U r hr ht g hg
  obtain ⟨U', r', hr', ht', H⟩ := h t
  obtain ⟨v, hv⟩ := germ_dvd hr' hr (T.hom t) ht' ht
  refine H g ?_
  rw [hv, map_mul, mul_assoc, hg, mul_zero]

lemma regular_comp_flat {X X₁ : Scheme.{u}} (p : X ⟶ S) (f : X₁ ⟶ X) [Flat f]
    (hT : ∀ (t : X) (U : S.affineOpens) (r : Γ(S, U.1)) (_ : I.ideal U = Ideal.span {r})
      (ht : p t ∈ U.1) (g : X.presheaf.stalk t),
      p.stalkMap t (S.presheaf.germ U.1 (p t) ht r) * g = 0 → g = 0)
    (t : X₁) (U : S.affineOpens) (r : Γ(S, U.1)) (hr : I.ideal U = Ideal.span {r})
    (ht : (f ≫ p) t ∈ U.1) (g : X₁.presheaf.stalk t)
    (hg : (f ≫ p).stalkMap t (S.presheaf.germ U.1 ((f ≫ p) t) ht r) * g = 0) : g = 0 := by
  rw [Scheme.Hom.stalkMap_comp] at hg
  exact regular_of_flat (f.stalkMap t).hom (Flat.stalkMap f t) _
    (fun g' h' => hT (f t) U r hr ht g' h') g hg

/-- Regularity pulls back along flat morphisms (`T₁ → T` over `S`). -/
lemma IsRegular.of_flat {T T₁ : Over S} (hT : IsRegular I T) (f : T₁ ⟶ T) [Flat f.left] :
    IsRegular I T₁ := by
  have key : ∀ (p₁ : T₁.left ⟶ S) (_ : f.left ≫ T.hom = p₁) (t : T₁.left) (U : S.affineOpens)
      (r : Γ(S, U.1)) (_ : I.ideal U = Ideal.span {r}) (ht : p₁ t ∈ U.1)
      (g : T₁.left.presheaf.stalk t), p₁.stalkMap t (S.presheaf.germ U.1 (p₁ t) ht r) * g = 0 →
      g = 0 := by
    rintro _ rfl
    exact regular_comp_flat T.hom f.left hT
  exact key _ (Over.w f)

/-- `Z` lies over `S' = V(I)`: the structure morphism factors through `S'`. -/
def LiesOver (I : S.IdealSheafData) (Z : Over S) : Prop :=
  ∃ l : Z.left ⟶ I.subscheme, l ≫ I.subschemeι = Z.hom

lemma LiesOver.of_hom {Z Z' : Over S} (h : LiesOver I Z) (s : Z' ⟶ Z) : LiesOver I Z' := by
  obtain ⟨l, hl⟩ := h
  exact ⟨s.left ≫ l, by rw [Category.assoc, hl]; exact Over.w s⟩

lemma appLE_comp_ι_eq_zero {Z : Scheme.{u}} (l : Z ⟶ I.subscheme) (U : S.affineOpens)
    {r : Γ(S, U.1)} (hr : r ∈ I.ideal U) (W : Z.Opens) (e : W ≤ (l ≫ I.subschemeι) ⁻¹ᵁ U.1) :
    (l ≫ I.subschemeι).appLE U.1 W e r = 0 := by
  have hker : r ∈ RingHom.ker (I.subschemeι.app U.1).hom := by
    rw [I.ker_subschemeι_app U]; exact hr
  have h0 : (I.subschemeι.app U.1).hom r = 0 := hker
  have : (l ≫ I.subschemeι).appLE U.1 W e =
      I.subschemeι.app U.1 ≫ l.appLE (I.subschemeι ⁻¹ᵁ U.1) W (show W ≤ l ⁻¹ᵁ _ from e) := by
    simp [Scheme.Hom.appLE]
  rw [this]
  change (l.appLE _ W _).hom ((I.subschemeι.app U.1).hom r) = 0
  rw [h0, map_zero]

/-- A generator of `I` restricts to zero on anything lying over `S'`. -/
lemma LiesOver.appLE_eq_zero {Z : Over S} (h : LiesOver I Z) (U : S.affineOpens) {r : Γ(S, U.1)}
    (hr : r ∈ I.ideal U) (W : Z.left.Opens) (e : W ≤ Z.hom ⁻¹ᵁ U.1) : Z.hom.appLE U.1 W e r = 0 := by
  obtain ⟨l, hl⟩ := h
  have key : ∀ (p : Z.left ⟶ S) (_ : l ≫ I.subschemeι = p) (e : W ≤ p ⁻¹ᵁ U.1),
      p.appLE U.1 W e r = 0 := by
    rintro _ rfl e
    exact appLE_comp_ι_eq_zero l U hr W e
  exact key _ hl e

/-- A morphism `p : Z ⟶ X` landing in the affine open `V` is the composite of the morphism
`Z ⟶ Spec Γ(X, V)` attached to `p^#` and `Spec Γ(X, V) ⟶ X`. -/
lemma toSpecΓ_appLE_fromSpec {X Z : Scheme.{u}} (p : Z ⟶ X) {V : X.Opens} (hV : IsAffineOpen V)
    (hZ : ⊤ ≤ p ⁻¹ᵁ V) :
    Z.toSpecΓ ≫ Spec.map (p.appLE V ⊤ hZ) ≫ hV.fromSpec = p := by
  have h := Scheme.Opens.toSpecΓ_SpecMap_appLE p V ⊤ hZ
  have h2 := congrArg (· ≫ hV.fromSpec) h
  simp only [Category.assoc, hV.toSpecΓ_fromSpec, Scheme.Hom.resLE_comp_ι] at h2
  rw [Scheme.Opens.toSpecΓ_top] at h2
  refine Scheme.hom_ext_of_forall _ _ fun x => ⟨⊤, trivial, ?_⟩
  simpa only [Category.assoc] using h2

/-- Conversely, over an open where `I` is generated by `r`, vanishing of `r` means lying over `S'`. -/
lemma liesOver_of_appLE_eq_zero {Z : Over S} (U : S.affineOpens) {r : Γ(S, U.1)}
    (hr : I.ideal U = Ideal.span {r}) (hZ : ⊤ ≤ Z.hom ⁻¹ᵁ U.1)
    (h0 : Z.hom.appLE U.1 ⊤ hZ r = 0) : LiesOver I Z := by
  let φ : Γ(S, U.1) ⟶ Γ(Z.left, ⊤) := Z.hom.appLE U.1 ⊤ hZ
  have hφ : ∀ a ∈ I.ideal U, φ.hom a = 0 := by
    intro a ha
    rw [hr, Ideal.mem_span_singleton'] at ha
    obtain ⟨v, rfl⟩ := ha
    rw [map_mul]
    have : φ.hom r = 0 := h0
    rw [this, mul_zero]
  let ψ : CommRingCat.of (Γ(S, U.1) ⧸ I.ideal U) ⟶ Γ(Z.left, ⊤) :=
    CommRingCat.ofHom (Ideal.Quotient.lift _ φ.hom hφ)
  obtain ⟨c, h2⟩ : ∃ c : Spec (CommRingCat.of (Γ(S, U.1) ⧸ I.ideal U)) ⟶ I.subscheme,
      c ≫ I.subschemeι = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))) ≫
        U.2.fromSpec :=
    ⟨I.subschemeCover.f U, (I.subschemeCover_map_subschemeι U).trans (I.glueDataObjι_ι U)⟩
  refine ⟨Z.left.toSpecΓ ≫ Spec.map ψ ≫ c, ?_⟩
  have hc : CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U)) ≫ ψ = φ := by
    ext x; rfl
  have h3 := toSpecΓ_appLE_fromSpec Z.hom U.2 hZ
  calc _ = Z.left.toSpecΓ ≫ Spec.map ψ ≫ c ≫ I.subschemeι := by
        simp only [Category.assoc]
    _ = Z.left.toSpecΓ ≫ Spec.map ψ ≫
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))) ≫ U.2.fromSpec := by rw [h2]
    _ = Z.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U)) ≫ ψ) ≫
          U.2.fromSpec := by rw [Spec.map_comp, Category.assoc]
    _ = Z.hom := by rw [hc]; exact h3


end

section


variable {S : Scheme.{u}} {I : S.IdealSheafData} {X Y : Over S} (j : Y ⟶ X)

variable (I) in
/-- `x : T ⟶ X` satisfies: the restriction `T|_{S'} ⟶ X` factors through `Y`. It is stated on all
`Z ⟶ T` with `Z` over `S'`, which is the same (`factors_iff_pullback`). -/
def Factors {T : Over S} (x : T ⟶ X) : Prop :=
  ∀ ⦃Z : Over S⦄ (s : Z ⟶ T), LiesOver I Z → ∃ y : Z ⟶ Y, y ≫ j = s ≫ x

/-- `T|_{S'}` as an object over `S`. -/
def restr (I : S.IdealSheafData) (T : Over S) : Over S :=
  Over.mk (pullback.fst T.hom I.subschemeι ≫ T.hom)

/-- `T|_{S'} ⟶ T`. -/
def restrι (I : S.IdealSheafData) (T : Over S) : restr I T ⟶ T :=
  Over.homMk (pullback.fst T.hom I.subschemeι) rfl

lemma liesOver_restr (T : Over S) : LiesOver I (restr I T) :=
  ⟨pullback.snd _ _, (pullback.condition).symm⟩

/-- `Factors` is literally: `T|_{S'} ⟶ X` factors through `Y`. -/
lemma factors_iff_pullback {T : Over S} (x : T ⟶ X) :
    Factors I j x ↔ ∃ y : restr I T ⟶ Y, y ≫ j = restrι I T ≫ x := by
  refine ⟨fun h => h _ (liesOver_restr T), ?_⟩
  rintro ⟨y, hy⟩ Z s ⟨l, hl⟩
  let m : Z ⟶ restr I T := Over.homMk (pullback.lift s.left l ((Over.w s).trans hl.symm)) (by
    change pullback.lift _ _ _ ≫ pullback.fst _ _ ≫ T.hom = Z.hom
    rw [pullback.lift_fst_assoc]; exact Over.w s)
  have hm : m ≫ restrι I T = s := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
  exact ⟨m ≫ y, by rw [Category.assoc, hy, ← Category.assoc, hm]⟩

lemma Factors.comp {T T' : Over S} {x : T ⟶ X} (h : Factors I j x) (s : T' ⟶ T) :
    Factors I j (s ≫ x) := fun Z r hZ => by
  obtain ⟨y, hy⟩ := h (r ≫ s) hZ
  exact ⟨y, by rw [hy, Category.assoc]⟩

variable (I) in
/-- `b : B ⟶ X` is the **dilatation** `Bl_Y^D X` over the open `V` of `X` (`D = X|_{S'}`), by its
universal property in `Sch_X^{D-reg}`: `B` is `S'`-regular, `B|_{S'} ⟶ X` factors through `Y`, and `b`
is terminal among `S'`-regular `T ⟶ X` landing in `V` with this factorization. -/
structure IsDilOn (V : X.left.Opens) {B : Over S} (b : B ⟶ X) : Prop where
  reg : IsRegular I B
  land : ⊤ ≤ b.left ⁻¹ᵁ V
  factors : Factors I j b
  exists_lift : ∀ ⦃T : Over S⦄, IsRegular I T → ∀ x : T ⟶ X, ⊤ ≤ x.left ⁻¹ᵁ V → Factors I j x →
    ∃ f : T ⟶ B, f ≫ b = x
  uniq : ∀ ⦃T : Over S⦄, IsRegular I T → ∀ f g : T ⟶ B, f ≫ b = g ≫ b → f = g

variable (I) in
/-- `b : B ⟶ X` is the dilatation `Bl_Y^D X` of `X` with center `Y` along `S'`. -/
abbrev IsDilatation {B : Over S} (b : B ⟶ X) : Prop := IsDilOn I j ⊤ b

/-- Gluing morphisms over an open cover of `T` lifting `x` through `b`. -/
lemma exists_lift_of_cover {B T : Over S} (b : B ⟶ X) (x : T ⟶ X) (𝒰 : T.left.OpenCover)
    (huniq : ∀ {P : Over S} (p : P ⟶ T) [IsOpenImmersion p.left] (f g : P ⟶ B),
      f ≫ b = g ≫ b → f = g)
    (hlift : ∀ i, ∃ f : Over.mk (𝒰.f i ≫ T.hom) ⟶ B, f ≫ b =
      (Over.homMk (𝒰.f i) rfl : Over.mk (𝒰.f i ≫ T.hom) ⟶ T) ≫ x) :
    ∃ f : T ⟶ B, f ≫ b = x := by
  choose l hl using hlift
  have compat : ∀ i k, pullback.fst (𝒰.f i) (𝒰.f k) ≫ (l i).left =
      pullback.snd (𝒰.f i) (𝒰.f k) ≫ (l k).left := by
    intro i k
    let P : Over S := Over.mk (pullback.fst (𝒰.f i) (𝒰.f k) ≫ 𝒰.f i ≫ T.hom)
    let pi : P ⟶ Over.mk (𝒰.f i ≫ T.hom) := Over.homMk (pullback.fst _ _) rfl
    let pk : P ⟶ Over.mk (𝒰.f k ≫ T.hom) := Over.homMk (pullback.snd _ _) (by
      change pullback.snd _ _ ≫ 𝒰.f k ≫ T.hom = pullback.fst _ _ ≫ 𝒰.f i ≫ T.hom
      rw [← pullback.condition_assoc])
    let p : P ⟶ T := Over.homMk (pullback.fst _ _ ≫ 𝒰.f i) (by simp [P])
    have : IsOpenImmersion p.left := by
      change IsOpenImmersion (pullback.fst _ _ ≫ 𝒰.f i); infer_instance
    have e := huniq p (pi ≫ l i) (pk ≫ l k) (by
      rw [Category.assoc, Category.assoc, hl, hl]
      refine Over.OverMorphism.ext ?_
      simp [pi, pk, pullback.condition_assoc])
    exact congrArg (fun q => q.left) e
  refine ⟨Over.homMk (𝒰.glueMorphisms (fun i => (l i).left) compat) ?_, ?_⟩
  · refine 𝒰.hom_ext _ _ fun i => ?_
    rw [Scheme.Cover.ι_glueMorphisms_assoc]
    exact Over.w (l i)
  · refine Over.OverMorphism.ext (𝒰.hom_ext _ _ fun i => ?_)
    have := congrArg (fun q => q.left) (hl i)
    simp only [Over.comp_left, Over.homMk_left] at this ⊢
    rw [Scheme.Cover.ι_glueMorphisms_assoc]
    exact this

/-- A generator is a global nonzerodivisor on a regular `T` landing over its open. -/
lemma IsRegular.section {T : Over S} (hT : IsRegular I T) {U : S.affineOpens} {r : Γ(S, U.1)}
    (hr : I.ideal U = Ideal.span {r}) (hZ : ⊤ ≤ T.hom ⁻¹ᵁ U.1) (g : Γ(T.left, ⊤))
    (h : T.hom.appLE U.1 ⊤ hZ r * g = 0) : g = 0 := by
  refine section_regular _ (fun t ht g' hg' => hT t U r hr (hZ ht) g' ?_) g h
  rw [← hg']
  congr 1
  exact (Scheme.Hom.germ_stalkMap_apply ..).trans (by simp [Scheme.Hom.appLE]) 


end

section


variable {S : Scheme.{u}} {I : S.IdealSheafData} {X Y : Over S} (j : Y ⟶ X)

section Chart

variable {V : X.left.Opens} (hV : IsAffineOpen V) {U : S.affineOpens} (hVU : V ≤ X.hom ⁻¹ᵁ U.1)
  (r : Γ(S, U.1))

/-- The local equation `a` of `D = X|_{S'}` on `V`. -/
def chartA : Γ(X.left, V) := X.hom.appLE U.1 V hVU r

/-- The ideal of `Y` in `Γ(X, V)`. -/
def chartJ : Ideal Γ(X.left, V) := RingHom.ker (j.left.app V).hom

/-- The coordinate ring `Γ(X, V)[J/a]` of the dilatation on `V` (`AlgMag.dilatation`). -/
abbrev chartC : Subalgebra Γ(X.left, V) (Localization.Away (chartA hVU r)) :=
  dilatation (chartJ j) (chartA hVU r)

/-- `Spec Γ(X, V)[J/a] ⟶ X`. -/
def chartB : Spec (CommRingCat.of (chartC j hVU r)) ⟶ X.left :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(X.left, V) (chartC j hVU r))) ≫ hV.fromSpec

/-- The dilatation on `V`, over `S`. -/
def chartOver : Over S := Over.mk (chartB j hV hVU r ≫ X.hom)

/-- The dilatation on `V`, over `X`. -/
def chartMap : chartOver j hV hVU r ⟶ X := Over.homMk (chartB j hV hVU r) rfl

variable {T : Over S} (x : T ⟶ X) (hT : ⊤ ≤ x.left ⁻¹ᵁ V)

/-- The pull-back `Γ(X, V) ⟶ Γ(T, ⊤)`. -/
def rho : Γ(X.left, V) ⟶ Γ(T.left, ⊤) := x.left.appLE V ⊤ hT

include hVU in
lemma le_T (x : T ⟶ X) (hT : ⊤ ≤ x.left ⁻¹ᵁ V) : ⊤ ≤ T.hom ⁻¹ᵁ U.1 := by
  rw [← Over.w x]
  exact fun t ht => hVU (hT ht)

lemma rho_chartA : (rho x hT).hom (chartA hVU r) = T.hom.appLE U.1 ⊤ (le_T hVU x hT) r := by
  have key : ∀ (p : T.left ⟶ S) (hp : x.left ≫ X.hom = p) (e : ⊤ ≤ p ⁻¹ᵁ U.1),
      x.left.appLE V ⊤ hT (X.hom.appLE U.1 V hVU r) = p.appLE U.1 ⊤ e r := by
    rintro _ rfl e
    rw [← Scheme.Hom.appLE_comp_appLE x.left X.hom U.1 V ⊤ hVU hT]
    rfl
  exact key _ (Over.w x) _

include hV in
/-- If `x^#` kills the ideal of `Y`, then `x` factors through `Y`. -/
lemma exists_factor_of_kills [IsClosedImmersion j.left] (h : ∀ g ∈ chartJ j, (rho x hT).hom g = 0) :
    ∃ y : T ⟶ Y, y ≫ j = x := by
  have hY : IsAffineOpen (j.left ⁻¹ᵁ V) := hV.preimage j.left
  have hsurj : Function.Surjective (j.left.app V).hom := j.left.app_surjective V hV
  let ψ : Γ(Y.left, j.left ⁻¹ᵁ V) →+* Γ(T.left, ⊤) :=
    RingHom.liftOfSurjective (j.left.app V).hom hsurj ⟨(rho x hT).hom, fun g hg => h g hg⟩
  have hψ : j.left.app V ≫ CommRingCat.ofHom ψ = rho x hT := by
    ext g
    change ψ ((j.left.app V).hom g) = _
    exact RingHom.liftOfRightInverse_comp_apply _ _ _ _ g
  let y : T.left ⟶ Y.left := T.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ) ≫ hY.fromSpec
  have hy : y ≫ j.left = x.left := by
    have h1 := IsAffineOpen.SpecMap_appLE_fromSpec j.left hV hY le_rfl
    rw [Scheme.Hom.appLE_eq_app] at h1
    calc y ≫ j.left = T.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ) ≫ hY.fromSpec ≫ j.left := by
          simp [y]
      _ = T.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (j.left.app V) ≫
            hV.fromSpec := by rw [h1]
      _ = T.left.toSpecΓ ≫ Spec.map (rho x hT) ≫ hV.fromSpec := by
          rw [← hψ, Spec.map_comp, Category.assoc]
      _ = x.left := toSpecΓ_appLE_fromSpec x.left hV hT
  refine ⟨Over.homMk y ?_, Over.OverMorphism.ext hy⟩
  have := congrArg (· ≫ X.hom) hy
  simp only [Category.assoc, Over.w j, Over.w x] at this
  exact this

/-- If `x` factors through `Y`, then `x^#` kills the ideal of `Y`. -/
lemma kills_of_factor {y : T ⟶ Y} (hy : y ≫ j = x) (g : Γ(X.left, V)) (hg : g ∈ chartJ j) :
    (rho x hT).hom g = 0 := by
  have key : ∀ (p : T.left ⟶ X.left) (_ : y.left ≫ j.left = p) (e : ⊤ ≤ p ⁻¹ᵁ V),
      p.appLE V ⊤ e g = 0 := by
    rintro _ rfl e
    have h0 : (j.left.app V).hom g = 0 := hg
    have : (y.left ≫ j.left).appLE V ⊤ e = j.left.app V ≫ y.left.appLE (j.left ⁻¹ᵁ V) ⊤ e := by
      simp [Scheme.Hom.appLE]
    rw [this]
    change (y.left.appLE _ ⊤ _).hom ((j.left.app V).hom g) = 0
    rw [h0, map_zero]
  exact key _ (congrArg (fun q => q.left) hy) hT

variable {r} (hr : I.ideal U = Ideal.span {r})

include hV hr in
/-- If `J` maps into `a Γ(T)`, then `T|_{S'} ⟶ X` factors through `Y`. -/
lemma factors_of_div [IsClosedImmersion j.left]
    (h : ∀ g ∈ chartJ j, ∃ w, (rho x hT).hom g = (rho x hT).hom (chartA hVU r) * w) :
    Factors I j x := by
  intro Z s hZ
  have hT' : ⊤ ≤ (s ≫ x).left ⁻¹ᵁ V := fun z _ => hT (Set.mem_univ (s.left z))
  have hres : ∀ g, (rho (s ≫ x) hT').hom g =
      (s.left.appLE ⊤ ⊤ (fun _ _ => trivial)).hom ((rho x hT).hom g) := by
    intro g
    have := Scheme.Hom.appLE_comp_appLE s.left x.left V ⊤ ⊤ hT (fun _ _ => trivial)
    exact (congrArg (fun q => q.hom g) this).symm
  refine exists_factor_of_kills j hV (s ≫ x) hT' fun g hg => ?_
  obtain ⟨w, hw⟩ := h g hg
  rw [hres, hw, map_mul, ← hres, rho_chartA hVU r (s ≫ x) hT']
  rw [hZ.appLE_eq_zero U (by rw [hr]; exact Ideal.mem_span_singleton_self r) ⊤ _, zero_mul]

omit X Y in
lemma germ_appLE {T : Scheme.{u}} (p : T ⟶ S) {U : S.Opens} (hZ : ⊤ ≤ p ⁻¹ᵁ U) (t : T) (ht : p t ∈ U)
    (r : Γ(S, U)) : p.stalkMap t (S.presheaf.germ U (p t) ht r) =
      T.presheaf.germ ⊤ t trivial (p.appLE U ⊤ hZ r) :=
  (Scheme.Hom.germ_stalkMap_apply ..).trans
    (TopCat.Presheaf.germ_res_apply T.presheaf (homOfLE hZ) t trivial _).symm

omit X Y in
lemma spec_section_regular {R : CommRingCat.{u}} (a : R) (ha : ∀ b : R, a * b = 0 → b = 0)
    (g : Γ(Spec R, ⊤)) (h : (Scheme.ΓSpecIso R).inv.hom a * g = 0) : g = 0 := by
  let e := (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
  obtain ⟨b, rfl⟩ := e.symm.surjective g
  have h0 : e.symm (a * b) = 0 := by rw [map_mul]; exact h
  rw [ha b (e.symm.injective (by rw [h0, map_zero])), map_zero]

omit X Y in
lemma appLE_fromSpec {X : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V) {R : CommRingCat.{u}}
    (φ : Γ(X, V) ⟶ R) (e : ⊤ ≤ (Spec.map φ ≫ hV.fromSpec) ⁻¹ᵁ V) :
    (Spec.map φ ≫ hV.fromSpec).appLE V ⊤ e = φ ≫ (Scheme.ΓSpecIso R).inv := by
  rw [Scheme.Hom.comp_appLE, hV.fromSpec_app_self, Category.assoc]
  have h1 : (Spec Γ(X, V)).presheaf.map (eqToHom hV.fromSpec_preimage_self).op ≫
      Scheme.Hom.appLE (Spec.map φ) (hV.fromSpec ⁻¹ᵁ V) ⊤ (show ⊤ ≤ Spec.map φ ⁻¹ᵁ _ from e) =
      (Spec.map φ).appTop := Scheme.Hom.map_appLE _ _ _
  refine (congrArg ((Scheme.ΓSpecIso Γ(X, V)).inv ≫ ·) h1).trans ?_
  exact (Scheme.ΓSpecIso_inv_naturality φ).symm

lemma rho_chartMap (e : ⊤ ≤ (chartMap j hV hVU r).left ⁻¹ᵁ V) :
    rho (chartMap j hV hVU r) e = CommRingCat.ofHom (algebraMap Γ(X.left, V) (chartC j hVU r)) ≫
      (Scheme.ΓSpecIso _).inv :=
  appLE_fromSpec hV _ e

lemma chart_land : ⊤ ≤ (chartMap j hV hVU r).left ⁻¹ᵁ V := by
  intro t _
  change hV.fromSpec _ ∈ V
  rw [← SetLike.mem_coe, ← hV.range_fromSpec]
  exact ⟨_, rfl⟩

include hr in
/-- `a` is regular on `Spec Γ(X, V)[J/a]`: the chart is `S'`-regular. -/
lemma chart_regular : IsRegular I (chartOver j hV hVU r) := by
  refine isRegular_of_exists fun t => ?_
  have hb := chart_land j hV hVU (r := r)
  have hU : (chartOver j hV hVU r).hom t ∈ U.1 := hVU (hb (Set.mem_univ t))
  refine ⟨U, r, hr, hU, fun g hg => ?_⟩
  have hle : ⊤ ≤ (chartOver j hV hVU r).hom ⁻¹ᵁ U.1 := le_T hVU (chartMap j hV hVU r) hb
  have : IsAffine (chartOver j hV hVU r).left := inferInstanceAs (IsAffine (Spec _))
  refine germ_regular (isAffineOpen_top _) t trivial
    ((chartOver j hV hVU r).hom.appLE U.1 ⊤ hle r) ?_ g ?_
  · intro g' hg'
    rw [← rho_chartA hVU r (chartMap j hV hVU r) hb, rho_chartMap j hV hVU hb] at hg'
    exact spec_section_regular _ (fun b hb' => dilatation_regular b hb') g' hg'
  · rw [← hg]
    congr 1
    exact (germ_appLE _ hle t hU r).symm

include hr in
lemma chartA_mem (hYI : LiesOver I Y) : chartA hVU r ∈ chartJ j := by
  have hmem : r ∈ I.ideal U := by rw [hr]; exact Ideal.mem_span_singleton_self r
  have key : ∀ (p : Y.left ⟶ S) (_ : j.left ≫ X.hom = p) (e : j.left ⁻¹ᵁ V ≤ p ⁻¹ᵁ U.1),
      (j.left.app V).hom (X.hom.appLE U.1 V hVU r) = p.appLE U.1 (j.left ⁻¹ᵁ V) e r := by
    rintro _ rfl e
    rw [Scheme.Hom.app_eq_appLE, ← Scheme.Hom.appLE_comp_appLE j.left X.hom U.1 V _ hVU le_rfl]
    rfl
  have hle : j.left ⁻¹ᵁ V ≤ Y.hom ⁻¹ᵁ U.1 := by
    rw [← Over.w j]; exact fun t ht => hVU ht
  change (j.left.app V).hom (X.hom.appLE U.1 V hVU r) = 0
  rw [key _ (Over.w j) hle]
  exact hYI.appLE_eq_zero U hmem _ hle

include hV hr in
lemma chart_factors [IsClosedImmersion j.left] :
    Factors I j (chartMap j hV hVU r) := by
  have hb := chart_land j hV hVU (r := r)
  refine factors_of_div j hV hVU _ hb hr fun g hg => ?_
  let R := CommRingCat.of (chartC j hVU r)
  let q : R := dilOverA (I := chartJ j) (a := chartA hVU r) hg
  have e : (algebraMap Γ(X.left, V) (chartC j hVU r) (chartA hVU r) : R) * q =
      algebraMap Γ(X.left, V) (chartC j hVU r) g := algebraMap_mul_dilOverA hg
  refine ⟨(Scheme.ΓSpecIso R).inv.hom q, ?_⟩
  rw [rho_chartMap j hV hVU hb]
  exact (congrArg (Scheme.ΓSpecIso R).inv.hom e.symm).trans (map_mul _ _ _)

lemma rho_comp {T T' : Over S} (s : T' ⟶ T) (x : T ⟶ X) (hT : ⊤ ≤ x.left ⁻¹ᵁ V)
    (hT' : ⊤ ≤ (s ≫ x).left ⁻¹ᵁ V) :
    rho (s ≫ x) hT' = rho x hT ≫ s.left.appLE ⊤ ⊤ (fun _ _ => trivial) :=
  (Scheme.Hom.appLE_comp_appLE s.left x.left V ⊤ ⊤ hT (fun _ _ => trivial)).symm

include hr in
lemma chart_uniq (hYI : LiesOver I Y) {T : Over S} (hT : IsRegular I T)
    (f g : T ⟶ chartOver j hV hVU r)
    (h : f ≫ chartMap j hV hVU r = g ≫ chartMap j hV hVU r) : f = g := by
  have hb := chart_land j hV hVU (r := r)
  have ha := chartA_mem j hVU hr hYI
  have hx : ⊤ ≤ (f ≫ chartMap j hV hVU r).left ⁻¹ᵁ V := fun t _ => hb (Set.mem_univ (f.left t))
  let ρ := (rho (f ≫ chartMap j hV hVU r) hx).hom
  have hreg : ∀ b, ρ (chartA hVU r) * b = 0 → b = 0 := fun b hb' => by
    rw [show ρ _ = _ from rho_chartA hVU r _ hx] at hb'
    exact hT.section hr _ b hb'
  let φ : ∀ f' : T ⟶ chartOver j hV hVU r, (chartC j hVU r) →+* Γ(T.left, ⊤) := fun f' =>
    (GB.homSpecEquiv T.left (CommRingCat.of (chartC j hVU r)) f'.left).hom
  have hφ : ∀ (f' : T ⟶ chartOver j hV hVU r) (_ : f' ≫ chartMap j hV hVU r = f ≫ chartMap j hV hVU r)
      (c : Γ(X.left, V)), φ f' (algebraMap _ _ c) = ρ c := by
    intro f' e c
    have hx' : ⊤ ≤ (f' ≫ chartMap j hV hVU r).left ⁻¹ᵁ V := by rw [e]; exact hx
    have e1 : rho (f ≫ chartMap j hV hVU r) hx = rho (f' ≫ chartMap j hV hVU r) hx' := by
      simp only [e]
    have e2 := rho_comp f' (chartMap j hV hVU r) hb hx'
    rw [rho_chartMap j hV hVU hb] at e2
    change _ = (rho (f ≫ chartMap j hV hVU r) hx).hom c
    rw [e1, e2]
    have hap : f'.left.appLE ⊤ ⊤ (fun _ _ => trivial) = f'.left.appTop :=
      (Scheme.Hom.app_eq_appLE _).symm
    rw [hap]
    rfl
  have := dilatation_ringHom_ext (I := chartJ j) (a := chartA hVU r) ρ ha hreg
    (f := φ f) (g := φ g) (hφ f rfl) (hφ g h.symm)
  refine Over.OverMorphism.ext ((GB.homSpecEquiv T.left _).injective ?_)
  exact CommRingCat.hom_ext this

include hr in
/-- On affine `T`, the factorization through `Y` means that `J` maps into `a Γ(T)`. -/
lemma div_of_factors {T : Over S} (x : T ⟶ X) (hT : ⊤ ≤ x.left ⁻¹ᵁ V) [IsAffine T.left]
    (hx : Factors I j x) (g : Γ(X.left, V)) (hg : g ∈ chartJ j) :
    ∃ w, (rho x hT).hom g = (rho x hT).hom (chartA hVU r) * w := by
  let c := (rho x hT).hom (chartA hVU r)
  let Q := CommRingCat.of (Γ(T.left, ⊤) ⧸ Ideal.span {c})
  let π : Γ(T.left, ⊤) ⟶ Q := CommRingCat.ofHom (Ideal.Quotient.mk _)
  let s₀ : Spec Q ⟶ T.left := Spec.map π ≫ (isAffineOpen_top T.left).fromSpec
  let Z : Over S := Over.mk (s₀ ≫ T.hom)
  let s : Z ⟶ T := Over.homMk s₀ rfl
  have hs : s.left.appLE ⊤ ⊤ (fun _ _ => trivial) = π ≫ (Scheme.ΓSpecIso Q).inv :=
    appLE_fromSpec (isAffineOpen_top T.left) π _
  have hle := le_T hVU (s ≫ x) (fun z _ => hT (Set.mem_univ (s.left z)))
  have hsx : ⊤ ≤ (s ≫ x).left ⁻¹ᵁ V := fun z _ => hT (Set.mem_univ (s.left z))
  have hres := rho_comp s x hT hsx
  have hZ : LiesOver I Z := by
    refine liesOver_of_appLE_eq_zero U hr hle ?_
    rw [← rho_chartA hVU r (s ≫ x) hsx, hres, hs]
    change (Scheme.ΓSpecIso Q).inv.hom (Ideal.Quotient.mk _ c) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self c), map_zero]
  obtain ⟨y, hy⟩ := hx s hZ
  have h0 := kills_of_factor j (s ≫ x) hsx hy g hg
  rw [hres, hs] at h0
  have h1 : (Scheme.ΓSpecIso Q).inv.hom (Ideal.Quotient.mk _ ((rho x hT).hom g)) = 0 := h0
  have h2 : Ideal.Quotient.mk (Ideal.span {c}) ((rho x hT).hom g) = 0 :=
    (Scheme.ΓSpecIso Q).commRingCatIsoToRingEquiv.symm.injective (by rw [map_zero]; exact h1)
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 h2)
  exact ⟨w, by rw [← hw, mul_comm]⟩

include hr in
/-- The universal property on affine `T`. -/
lemma chart_exists_lift {T : Over S} [IsAffine T.left]
    (hreg : IsRegular I T) (x : T ⟶ X) (hT : ⊤ ≤ x.left ⁻¹ᵁ V) (hx : Factors I j x) :
    ∃ f : T ⟶ chartOver j hV hVU r, f ≫ chartMap j hV hVU r = x := by
  have h1 : ∀ b, (rho x hT).hom (chartA hVU r) * b = 0 → b = 0 := fun b hb' => by
    rw [rho_chartA hVU r x hT] at hb'
    exact hreg.section hr _ b hb'
  let L : chartC j hVU r →+* Γ(T.left, ⊤) :=
    dilatationLift (rho x hT).hom h1 (div_of_factors j hVU hr x hT hx)
  have hL : CommRingCat.ofHom (algebraMap Γ(X.left, V) (chartC j hVU r)) ≫ CommRingCat.ofHom L =
      rho x hT := by
    ext c
    exact dilatationLift_algebraMap _ h1 (div_of_factors j hVU hr x hT hx) c
  let f₀ : T.left ⟶ Spec (CommRingCat.of (chartC j hVU r)) :=
    T.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom L)
  have hf : f₀ ≫ chartB j hV hVU r = x.left := by
    calc f₀ ≫ chartB j hV hVU r = T.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom L) ≫
          Spec.map (CommRingCat.ofHom (algebraMap _ _)) ≫ hV.fromSpec := by
          simp [f₀, chartB]
      _ = T.left.toSpecΓ ≫ Spec.map (rho x hT) ≫ hV.fromSpec := by
          rw [← hL, Spec.map_comp, Category.assoc]
      _ = x.left := toSpecΓ_appLE_fromSpec x.left hV hT
  refine ⟨Over.homMk f₀ ?_, Over.OverMorphism.ext hf⟩
  change f₀ ≫ chartB j hV hVU r ≫ X.hom = T.hom
  rw [← Category.assoc, hf]
  exact Over.w x

end Chart


end

section


variable {S : Scheme.{u}} {I : S.IdealSheafData} {X Y : Over S} {j : Y ⟶ X}

/-- Two dilatations over the same open are canonically isomorphic. -/
theorem IsDilOn.exists_iso {V : X.left.Opens} {B B' : Over S} {b : B ⟶ X} {b' : B' ⟶ X}
    (h : IsDilOn I j V b) (h' : IsDilOn I j V b') : ∃ e : B ≅ B', e.hom ≫ b' = b := by
  obtain ⟨f, hf⟩ := h'.exists_lift h.reg b h.land h.factors
  obtain ⟨g, hg⟩ := h.exists_lift h'.reg b' h'.land h'.factors
  refine ⟨⟨f, g, h.uniq h.reg _ _ ?_, h'.uniq h'.reg _ _ ?_⟩, hf⟩
  · simp [hf, hg]
  · simp [hf, hg]

/-- The dilatation is local: it is built on affine opens where `S'` is principal. -/
theorem chart_isDilOn [IsClosedImmersion j.left] (hYI : LiesOver I Y) {V : X.left.Opens}
    (hV : IsAffineOpen V) {U : S.affineOpens} (hVU : V ≤ X.hom ⁻¹ᵁ U.1) {r : Γ(S, U.1)}
    (hr : I.ideal U = Ideal.span {r}) : IsDilOn I j V (chartMap j hV hVU r) where
  reg := chart_regular j hV hVU hr
  land := chart_land j hV hVU
  factors := chart_factors j hV hVU hr
  uniq _ hT f g h := chart_uniq j hV hVU hr hYI hT f g h
  exists_lift T hT x hx hf := by
    refine exists_lift_of_cover _ x T.left.affineCover ?_ fun i => ?_
    · intro P p _ f' g' e
      have : Flat p.left := inferInstance
      exact chart_uniq j hV hVU hr hYI (hT.of_flat p) f' g' e
    · let Ti : Over S := Over.mk (T.left.affineCover.f i ≫ T.hom)
      let m : Ti ⟶ T := Over.homMk (T.left.affineCover.f i) rfl
      have : IsAffine Ti.left := inferInstanceAs (IsAffine (Spec _))
      have : Flat m.left := inferInstanceAs (Flat (T.left.affineCover.f i))
      exact chart_exists_lift j hV hVU hr (hT.of_flat m) (m ≫ x)
        (fun z _ => hx (Set.mem_univ (m.left z))) (hf.comp j m)

/-- Compatibility of the dilatations over `V ≤ V'`: the square is cartesian. -/
theorem isPullback_of_isDilOn {V V' : X.left.Opens} (hle : V ≤ V') {B B' : Over S} {b : B ⟶ X}
    {b' : B' ⟶ X} (h : IsDilOn I j V b) (h' : IsDilOn I j V' b') (tr : B ⟶ B') (htr : tr ≫ b' = b)
    (tv : B.left ⟶ V) (tv' : B'.left ⟶ V') (htv : tv ≫ V.ι = b.left) (htv' : tv' ≫ V'.ι = b'.left) :
    IsPullback tr.left tv tv' (X.left.homOfLE hle) := by
  let P := pullback tv' (X.left.homOfLE hle)
  let Q : Over S := Over.mk (pullback.fst tv' (X.left.homOfLE hle) ≫ B'.hom)
  let m : Q ⟶ B' := Over.homMk (pullback.fst _ _) rfl
  have hmX : (m ≫ b').left = pullback.snd tv' (X.left.homOfLE hle) ≫ V.ι := by
    change pullback.fst _ _ ≫ b'.left = _
    rw [← htv', pullback.condition_assoc, Scheme.homOfLE_ι]
  have hflat : Flat m.left := inferInstanceAs (Flat (pullback.fst tv' (X.left.homOfLE hle)))
  have hmono : Mono m := by
    refine ⟨fun f g e => Over.OverMorphism.ext ?_⟩
    have : IsOpenImmersion m.left := inferInstanceAs (IsOpenImmersion (pullback.fst _ _))
    exact (cancel_mono m.left).1 (congrArg (fun q => q.left) e)
  have hQ : IsDilOn I j V (m ≫ b') := by
    refine ⟨h'.reg.of_flat m, ?_, h'.factors.comp j m, ?_, ?_⟩
    · intro z _
      have : (m ≫ b').left z = V.ι (pullback.snd tv' (X.left.homOfLE hle) z) := by
        rw [hmX]; rfl
      change (m ≫ b').left z ∈ V
      rw [this]
      exact (pullback.snd tv' (X.left.homOfLE hle) z).2
    · intro T hT x hx hf
      obtain ⟨f, hf'⟩ := h'.exists_lift hT x (fun z _ => hle (hx (Set.mem_univ z))) hf
      let xv : T.left ⟶ V := IsOpenImmersion.lift V.ι x.left (by
        rintro _ ⟨z, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact hx (Set.mem_univ z))
      have hxv : xv ≫ V.ι = x.left := IsOpenImmersion.lift_fac _ _ _
      have hw : f.left ≫ tv' = xv ≫ X.left.homOfLE hle := by
        rw [← cancel_mono V'.ι]
        simp only [Category.assoc, htv', Scheme.homOfLE_ι, hxv]
        exact congrArg (fun q => q.left) hf'
      refine ⟨Over.homMk (pullback.lift f.left xv hw) ?_, ?_⟩
      · change pullback.lift _ _ _ ≫ pullback.fst _ _ ≫ B'.hom = T.hom
        rw [pullback.lift_fst_assoc]
        exact Over.w f
      · rw [← hf', ← Category.assoc]
        congr 1
        exact Over.OverMorphism.ext (pullback.lift_fst _ _ _)
    · intro T hT f g e
      exact (cancel_mono m).1 (h'.uniq hT _ _ (by simpa only [Category.assoc] using e))
  obtain ⟨e, he⟩ := h.exists_iso hQ
  have h1 : tr.left = e.hom.left ≫ pullback.fst tv' (X.left.homOfLE hle) := by
    have : tr = e.hom ≫ m := h'.uniq h.reg _ _ (by
      rw [htr, Category.assoc, he])
    exact congrArg (fun q => q.left) this
  have h2 : tv = e.hom.left ≫ pullback.snd tv' (X.left.homOfLE hle) := by
    rw [← cancel_mono V.ι, htv, Category.assoc, ← hmX]
    exact (congrArg (fun q => q.left) he).symm
  let e' := (Over.forget S).mapIso e
  have he' : e'.hom = e.hom.left := rfl
  refine (IsPullback.of_hasPullback tv' (X.left.homOfLE hle)).of_iso
    e'.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [h1, ← he']; simp
  · rw [h2, ← he']; simp
  · simp
  · simp


end

section


variable {S : Scheme.{u}} {I : S.IdealSheafData} {X Y : Over S} (j : Y ⟶ X)

/-- Regularity is local on the source. -/
lemma isRegular_of_openCover {T : Over S} (𝒰 : T.left.OpenCover)
    (h : ∀ i, IsRegular I (Over.mk (𝒰.f i ≫ T.hom))) : IsRegular I T := by
  intro t U r hr ht g hg
  obtain ⟨i, s, rfl⟩ : ∃ i s, 𝒰.f i s = t := ⟨_, 𝒰.covers t⟩
  have hi := h i s U r hr ht
  have inj : Function.Injective ((𝒰.f i).stalkMap s) := (ConcreteCategory.bijective_of_isIso _).1
  apply inj
  rw [map_zero]
  apply hi
  have hc : ((𝒰.f i) ≫ T.hom).stalkMap s (S.presheaf.germ U.1 _ ht r) =
      (𝒰.f i).stalkMap s (T.hom.stalkMap (𝒰.f i s) (S.presheaf.germ U.1 _ ht r)) := by
    rw [Scheme.Hom.stalkMap_comp]; rfl
  refine (congrArg (· * _) hc).trans ?_
  refine (map_mul _ _ _).symm.trans ?_
  rw [hg, map_zero]

section Glue

variable (X) (I) in
/-- The affine opens of `X` lying over an affine open of `S` on which `S'` is principal. -/
def Good (V : X.left.affineOpens) : Prop :=
  ∃ (U : S.affineOpens) (r : Γ(S, U.1)), V.1 ≤ X.hom ⁻¹ᵁ U.1 ∧ I.ideal U = Ideal.span {r}

variable (X) in
lemma good_basis (hP : LocPrincipal I) {x : X.left} {O : X.left.Opens} (hx : x ∈ O) :
    ∃ V : X.left.affineOpens, Good I X V ∧ x ∈ V.1 ∧ V.1 ≤ O := by
  obtain ⟨U, hU, r, hr⟩ := hP (X.hom x)
  obtain ⟨W, hW, hxV, hle⟩ := Opens.isBasis_iff_nbhd.mp X.left.isBasis_affineOpens
    (show x ∈ O ⊓ X.hom ⁻¹ᵁ U.1 from ⟨hx, hU⟩)
  exact ⟨⟨W, hW⟩, ⟨U, r, hle.trans inf_le_right, hr⟩, hxV, hle.trans inf_le_left⟩

variable (X) in
/-- The open cover of `X` by the good affine opens. -/
def goodCover (hP : LocPrincipal I) : X.left.OpenCover where
  I₀ := { V : X.left.affineOpens // Good I X V }
  X V := V.1.1
  f V := V.1.1.ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, inferInstance⟩
    obtain ⟨V, hV, hx, -⟩ := good_basis X hP (O := ⊤) (x := x) trivial
    exact ⟨⟨V, hV⟩, by simpa using hx⟩

instance (hP : LocPrincipal I) : Preorder (goodCover X hP).I₀ :=
  inferInstanceAs (Preorder { V : X.left.affineOpens // Good I X V })

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
instance (hP : LocPrincipal I) : Scheme.Cover.LocallyDirected (goodCover X hP) :=
  .ofIsBasisOpensRange (by intros; simp [goodCover]; rfl) <| by
    refine Opens.isBasis_iff_nbhd.mpr fun {O x} hx => ?_
    obtain ⟨V, hV, hxV, hle⟩ := good_basis X hP hx
    exact ⟨_, ⟨⟨V, hV⟩, rfl⟩, by simpa [goodCover] using hxV, by simpa [goodCover] using hle⟩

variable [IsClosedImmersion j.left] (hYI : LiesOver I Y) (hP : LocPrincipal I)

/-- The chart of the dilatation over a good affine open. -/
abbrev gOver (i : (goodCover X hP).I₀) : Over S :=
  chartOver j i.1.2 i.2.choose_spec.choose_spec.1 i.2.choose_spec.choose

/-- Its map to `X`. -/
abbrev gMap (i : (goodCover X hP).I₀) : gOver j hP i ⟶ X :=
  chartMap j i.1.2 i.2.choose_spec.choose_spec.1 i.2.choose_spec.choose

include hYI in
lemma g_isDilOn (i : (goodCover X hP).I₀) : IsDilOn I j i.1.1 (gMap j hP i) :=
  chart_isDilOn hYI i.1.2 _ i.2.choose_spec.choose_spec.2

include hYI in
lemma g_tr_exists {i k : (goodCover X hP).I₀} (h : i ≤ k) :
    ∃ f : gOver j hP i ⟶ gOver j hP k, f ≫ gMap j hP k = gMap j hP i :=
  (g_isDilOn j hYI hP k).exists_lift (g_isDilOn j hYI hP i).reg _
    (fun z hz => h ((g_isDilOn j hYI hP i).land hz)) (g_isDilOn j hYI hP i).factors

/-- The transition map. -/
def gTr {i k : (goodCover X hP).I₀} (h : i ≤ k) : gOver j hP i ⟶ gOver j hP k :=
  (g_tr_exists j hYI hP h).choose

lemma gTr_map {i k : (goodCover X hP).I₀} (h : i ≤ k) :
    gTr j hYI hP h ≫ gMap j hP k = gMap j hP i := (g_tr_exists j hYI hP h).choose_spec

/-- The map from a chart to its open. -/
def gTo (i : (goodCover X hP).I₀) : (gOver j hP i).left ⟶ i.1.1 :=
  IsOpenImmersion.lift i.1.1.ι (gMap j hP i).left (by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact chart_land j i.1.2 _ (Set.mem_univ z))

lemma gTo_ι (i : (goodCover X hP).I₀) : gTo j hP i ≫ i.1.1.ι = (gMap j hP i).left :=
  IsOpenImmersion.lift_fac _ _ _

/-- The functor `V ↦ Bl` on good opens. -/
def gFunctor : (goodCover X hP).I₀ ⥤ Scheme.{u} where
  obj i := (gOver j hP i).left
  map f := (gTr j hYI hP (leOfHom f)).left
  map_id i := by
    have : gTr j hYI hP (le_refl i) = 𝟙 _ := (g_isDilOn j hYI hP i).uniq (g_isDilOn j hYI hP i).reg _ _ (by
      rw [gTr_map, Category.id_comp])
    exact congrArg (fun q => q.left) this
  map_comp {i k l} f g := by
    have : gTr j hYI hP (leOfHom (f ≫ g)) = gTr j hYI hP (leOfHom f) ≫ gTr j hYI hP (leOfHom g) :=
      (g_isDilOn j hYI hP l).uniq (g_isDilOn j hYI hP i).reg _ _ (by
        rw [gTr_map, Category.assoc, gTr_map, gTr_map])
    exact congrArg (fun q => q.left) this

/-- The natural transformation to the cover. -/
def gNat : gFunctor j hYI hP ⟶ (goodCover X hP).functorOfLocallyDirected where
  app i := gTo j hP i
  naturality {i k} f := by
    apply (cancel_mono ((goodCover X hP).f k)).1
    have h1 := (goodCover X hP).trans_map f
    have h2 : gTo j hP k ≫ (goodCover X hP).f k = (gMap j hP k).left := gTo_ι j hP k
    have h3 : gTo j hP i ≫ (goodCover X hP).f i = (gMap j hP i).left := gTo_ι j hP i
    have h4 := congrArg (fun q => q.left) (gTr_map j hYI hP (leOfHom f))
    change (gTr j hYI hP (leOfHom f)).left ≫ gTo j hP k ≫ (goodCover X hP).f k =
      gTo j hP i ≫ (goodCover X hP).trans f ≫ (goodCover X hP).f k
    refine ((congrArg (_ ≫ ·) h2).trans h4).trans ?_
    exact ((congrArg (gTo j hP i ≫ ·) h1).trans h3).symm

/-- **Gluing datum for the dilatation.** -/
def gData : (goodCover X hP).RelativeGluingData where
  functor := gFunctor j hYI hP
  natTrans := gNat j hYI hP
  equifibered {i k} f := by
    have hle : i.1.1 ≤ k.1.1 := leOfHom f
    have h := isPullback_of_isDilOn hle (g_isDilOn j hYI hP i) (g_isDilOn j hYI hP k)
      (gTr j hYI hP (leOfHom f)) (gTr_map j hYI hP _) (gTo j hP i) (gTo j hP k) (gTo_ι j hP i) (gTo_ι j hP k)
    have htr : (goodCover X hP).trans f = X.left.homOfLE hle := by
      apply (cancel_mono ((goodCover X hP).f k)).1
      exact ((goodCover X hP).trans_map f).trans (Scheme.homOfLE_ι _ hle).symm
    change IsPullback _ _ _ ((goodCover X hP).trans f)
    rw [htr]
    exact h

/-- `Bl_Y^D X` as a scheme over `S`: the glued charts. -/
def blOver : Over S := Over.mk ((gData j hYI hP).toBase ≫ X.hom)

/-- `Bl_Y^D X ⟶ X`. -/
def blMap : blOver j hYI hP ⟶ X := Over.homMk (gData j hYI hP).toBase rfl

/-- The open immersion of a chart in the dilatation. -/
def blι (i : (goodCover X hP).I₀) : gOver j hP i ⟶ blOver j hYI hP :=
  Over.homMk (colimit.ι (gData j hYI hP).functor i) (by
    have h := (gData j hYI hP).ι_toBase_assoc i X.hom
    refine h.trans ?_
    have h3 : gTo j hP i ≫ i.1.1.ι = (gMap j hP i).left := gTo_ι j hP i
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ X.hom) h3).trans rfl))

lemma blι_map (i : (goodCover X hP).I₀) : blι j hYI hP i ≫ blMap j hYI hP = gMap j hP i := by
  refine Over.OverMorphism.ext ?_
  exact ((gData j hYI hP).ι_toBase i).trans (gTo_ι j hP i)

instance (i : (goodCover X hP).I₀) : IsOpenImmersion (blι j hYI hP i).left :=
  (gData j hYI hP).cover.map_prop i

lemma bl_regular : IsRegular I (blOver j hYI hP) := by
  refine isRegular_of_openCover (gData j hYI hP).cover fun i => ?_
  have hi : IsRegular I (gOver j hP i) := (g_isDilOn j hYI hP i).reg
  let m : Over.mk ((gData j hYI hP).cover.f i ≫ (blOver j hYI hP).hom) ⟶ gOver j hP i :=
    Over.homMk (𝟙 ((gData j hYI hP).cover.X i))
      ((Category.id_comp _).trans (Over.w (blι j hYI hP i)).symm)
  have : Flat m.left := inferInstanceAs (Flat (𝟙 ((gData j hYI hP).cover.X i)))
  exact hi.of_flat m

/-- The range of chart `i` is the preimage of `V_i`. -/
lemma mem_range_of_mem {i : (goodCover X hP).I₀} {t : (blOver j hYI hP).left}
    (ht : (blMap j hYI hP).left t ∈ i.1.1) : ∃ s, (blι j hYI hP i).left s = t := by
  have := (gData j hYI hP).preimage_toBase_eq_range_ι i
  have h2 : t ∈ (gData j hYI hP).toBase ⁻¹' Set.range ((goodCover X hP).f i) := by
    refine ⟨⟨_, ht⟩, rfl⟩
  rw [this] at h2
  exact h2

include hYI in
lemma bl_uniq {T : Over S} (hT : IsRegular I T) (f g : T ⟶ blOver j hYI hP)
    (h : f ≫ blMap j hYI hP = g ≫ blMap j hYI hP) : f = g := by
  refine Over.OverMorphism.ext (Scheme.hom_ext_of_forall _ _ fun t => ?_)
  obtain ⟨i, hti⟩ : ∃ i : (goodCover X hP).I₀, (f ≫ blMap j hYI hP).left t ∈ i.1.1 := by
    obtain ⟨V, hV, hx, -⟩ := good_basis X hP (O := ⊤) (x := (f ≫ blMap j hYI hP).left t) trivial
    exact ⟨⟨V, hV⟩, hx⟩
  let W : T.left.Opens := (f ≫ blMap j hYI hP).left ⁻¹ᵁ i.1.1
  refine ⟨W, hti, ?_⟩
  let To : Over S := Over.mk (W.ι ≫ T.hom)
  let n : To ⟶ T := Over.homMk W.ι rfl
  have : Flat n.left := inferInstanceAs (Flat W.ι)
  have hTo := hT.of_flat n
  have hlift : ∀ (q : T ⟶ blOver j hYI hP), q ≫ blMap j hYI hP = f ≫ blMap j hYI hP →
      ∃ q' : To ⟶ gOver j hP i, q' ≫ blι j hYI hP i = n ≫ q := by
    intro q hq
    have hr : Set.range (W.ι ≫ q.left) ⊆ Set.range (blι j hYI hP i).left := by
      rintro _ ⟨z, rfl⟩
      refine mem_range_of_mem j hYI hP ?_
      have e : (blMap j hYI hP).left ((W.ι ≫ q.left) z) = (q ≫ blMap j hYI hP).left (W.ι z) := rfl
      rw [e, hq]
      exact z.2
    refine ⟨Over.homMk (IsOpenImmersion.lift (blι j hYI hP i).left (W.ι ≫ q.left) hr) ?_, ?_⟩
    · rw [← Over.w (blι j hYI hP i), ← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc,
        Over.w q]
      rfl
    · exact Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)
  obtain ⟨f', hf'⟩ := hlift f rfl
  obtain ⟨g', hg'⟩ := hlift g h.symm
  have e : f' = g' := (g_isDilOn j hYI hP i).uniq hTo _ _ (by
    rw [← blι_map j hYI hP i, ← Category.assoc, ← Category.assoc, hf', hg', Category.assoc,
      Category.assoc, h])
  have e2 := hf'.symm.trans ((congrArg (· ≫ blι j hYI hP i) e).trans hg')
  exact congrArg (fun q => q.left) e2

lemma bl_factors : Factors I j (blMap j hYI hP) := by
  intro Z s hZ
  let 𝒰 : Z.left.OpenCover := (gData j hYI hP).cover.pullback₁ s.left
  refine exists_lift_of_cover j (s ≫ blMap j hYI hP) 𝒰 ?_ fun i => ?_
  · intro P p _ f g e
    have : Mono j.left := inferInstance
    exact Over.OverMorphism.ext ((cancel_mono j.left).1 (congrArg (fun q => q.left) e))
  · let i' : (goodCover X hP).I₀ := i
    let Zi : Over S := Over.mk (𝒰.f i ≫ Z.hom)
    let m : Zi ⟶ Z := Over.homMk (𝒰.f i) rfl
    let ι' := (blι j hYI hP i').left
    have hc : pullback.snd s.left ι' ≫ ι' = pullback.fst s.left ι' ≫ s.left :=
      pullback.condition.symm
    let c : Zi ⟶ gOver j hP i' := Over.homMk (pullback.snd s.left ι') (by
      have h2 := Over.w (blι j hYI hP i')
      have h3 := Over.w s
      change pullback.snd s.left ι' ≫ (gOver j hP i').hom = pullback.fst s.left ι' ≫ Z.hom
      rw [← h2, ← h3, ← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ (blOver j hYI hP).hom) hc)
    obtain ⟨y, hy⟩ := (g_isDilOn j hYI hP i').factors c (hZ.of_hom m)
    refine ⟨y, hy.trans ?_⟩
    have hcm : c ≫ blι j hYI hP i' = m ≫ s := Over.OverMorphism.ext hc
    rw [← blι_map j hYI hP i', ← Category.assoc, hcm, Category.assoc]

include hYI in
lemma bl_exists_lift {T : Over S} (hT : IsRegular I T) (x : T ⟶ X) (hx : Factors I j x) :
    ∃ f : T ⟶ blOver j hYI hP, f ≫ blMap j hYI hP = x := by
  let 𝒰 : T.left.OpenCover := (goodCover X hP).pullback₁ x.left
  refine exists_lift_of_cover _ x 𝒰 ?_ fun i => ?_
  · intro P p _ f g e
    have : Flat p.left := inferInstance
    exact bl_uniq j hYI hP (hT.of_flat p) f g e
  · let i' : (goodCover X hP).I₀ := i
    let Ti : Over S := Over.mk (𝒰.f i ≫ T.hom)
    let m : Ti ⟶ T := Over.homMk (𝒰.f i) rfl
    have : Flat m.left := inferInstanceAs (Flat (𝒰.f i))
    have hland : ⊤ ≤ (m ≫ x).left ⁻¹ᵁ i'.1.1 := by
      intro z _
      have e : (m ≫ x).left = pullback.snd x.left i'.1.1.ι ≫ i'.1.1.ι :=
        (pullback.condition (f := x.left) (g := i'.1.1.ι))
      change (m ≫ x).left z ∈ i'.1.1
      rw [e]
      exact (pullback.snd x.left i'.1.1.ι z).2
    obtain ⟨f, hf⟩ := (g_isDilOn j hYI hP i').exists_lift (hT.of_flat m) (m ≫ x) hland (hx.comp j m)
    exact ⟨f ≫ blι j hYI hP i', by rw [Category.assoc, blι_map, hf]⟩

/-- **Existence of the dilatation** `Bl_Y^D X` of a scheme `X` over `S`, with center a closed
subscheme `Y` of `D = X|_{S'}` along a closed locally principal `S'` of `S`; the morphism
`Bl_Y^D X ⟶ X` is affine. -/
theorem exists_dilatation (j : Y ⟶ X) [IsClosedImmersion j.left] (hYI : LiesOver I Y)
    (hP : LocPrincipal I) :
    ∃ (B : Over S) (b : B ⟶ X), IsDilatation I j b ∧ IsAffineHom b.left := by
  refine ⟨blOver j hYI hP, blMap j hYI hP, ⟨bl_regular j hYI hP, fun _ _ => trivial,
    bl_factors j hYI hP, fun T hT x _ hx => bl_exists_lift j hYI hP hT x hx,
    fun T hT f g e => bl_uniq j hYI hP hT f g e⟩, ?_⟩
  refine isAffineHom_of_forall_exists_isAffineOpen _ fun x => ?_
  obtain ⟨V, hV, hx, -⟩ := good_basis X hP (O := ⊤) (x := x) trivial
  let i : (goodCover X hP).I₀ := ⟨V, hV⟩
  refine ⟨i.1.1, hx, i.1.2, ?_⟩
  have h := (gData j hYI hP).toBase_preimage_eq_opensRange_ι i
  have h2 : ((goodCover X hP).f i).opensRange = i.1.1 := Scheme.Opens.opensRange_ι _
  have e : (blMap j hYI hP).left ⁻¹ᵁ i.1.1 = (blι j hYI hP i).left.opensRange := by
    rw [← h2]; exact h
  rw [e]
  have : IsAffine (gOver j hP i).left := inferInstanceAs (IsAffine (Spec _))
  exact isAffineOpen_opensRange _

end Glue


end

section


open GB

variable {S : Scheme.{u}} {I : S.IdealSheafData}

/-- `ℤ[N]` is flat over `ℤ`: the structure morphism `𝔸(N) ⟶ Spec ℤ` is flat. -/
instance flat_terminal_AZ (N : Type u) [AddCommMonoid N] : Flat (terminal.from (AZ N)) := by
  let e := terminalIsoIsTerminal specULiftZIsTerminal
  let φ : CommRingCat.of (ULift.{u} ℤ) ⟶ zRing N := CommRingCat.ofHom
    ((algebraMap ℤ (AddMonoidAlgebra ℤ N)).comp (ULift.ringEquiv.{0, u} (R := ℤ)).toRingHom)
  have h : terminal.from (AZ N) = Spec.map φ ≫ e.inv := terminal.hom_ext _ _
  rw [h]
  have : Flat (Spec.map φ) := by
    rw [Flat.SpecMap_iff]
    refine RingHom.Flat.comp ?_ ?_
    · exact RingHom.Flat.of_bijective (ULift.ringEquiv.{0, u} (R := ℤ)).bijective
    · rw [RingHom.flat_algebraMap_iff]; infer_instance
  infer_instance

variable {M : Type u} [AddCommMonoid M]

instance flat_universalPoint (N : AddSubmonoid M) (T : Over S) :
    Flat (universalPoint N T).π.left :=
  inferInstanceAs (Flat (pullback.fst (terminal.from T.left) (terminal.from (AZ N))))

/-- `𝔸(N)_T` is `S'`-regular if `T` is (flatness of `ℤ[N]`). -/
lemma IsRegular.univPt {T : Over S} (hT : IsRegular I T) (N : AddSubmonoid M) :
    IsRegular I (universalPoint N T).P := hT.of_flat (universalPoint N T).π

/-- The universal `T`-point of `𝔸(M)`: `𝔸(M)_T` with its point in `M`. -/
abbrev PM (M : Type u) [AddCommMonoid M] (T : Over S) : Over S :=
  (universalPoint (⊤ : AddSubmonoid M) T).P

/-- The projection `𝔸(M)_T ⟶ T`. -/
abbrev piM (M : Type u) [AddCommMonoid M] (T : Over S) : PM M T ⟶ T :=
  (universalPoint (⊤ : AddSubmonoid M) T).π

/-- The universal point of `𝔸(M)` over `𝔸(M)_T`. -/
def gM (M : Type u) [AddCommMonoid M] (T : Over S) : APt (overO S) M (op (PM M T)) :=
  ((universalPoint (⊤ : AddSubmonoid M) T).u).comp
    (AddMonoidHom.toMultiplicative (AddSubmonoid.topEquiv (M := M)).symm.toAddMonoidHom)

/-- The classifying morphism of a point of `𝔸(M)`. -/
def liftM {T T' : Over S} (t : T' ⟶ T) (h : APt (overO S) M (op T')) : T' ⟶ PM M T :=
  (universalPoint (⊤ : AddSubmonoid M) T).lift t (APt.toMagnet ⊤ h)

@[reassoc (attr := simp)]
lemma liftM_π {T T' : Over S} (t : T' ⟶ T) (h : APt (overO S) M (op T')) :
    liftM t h ≫ piM M T = t := UniversalPoint.lift_π _ _ _

lemma res_liftM {T T' : Over S} (t : T' ⟶ T) (h : APt (overO S) M (op T')) :
    APt.res (liftM t h).op (gM M T) = h := by
  have := (universalPoint (⊤ : AddSubmonoid M) T).res_lift t (APt.toMagnet ⊤ h)
  ext p
  have h2 := congrArg (fun q => q (Multiplicative.ofAdd (⟨Multiplicative.toAdd p, trivial⟩ :
    (⊤ : AddSubmonoid M)))) this
  exact h2

lemma comp_liftM {T T' T'' : Over S} (s : T'' ⟶ T') (t : T' ⟶ T) (h : APt (overO S) M (op T')) :
    s ≫ liftM t h = liftM (s ≫ t) (APt.res s.op h) :=
  ((universalPoint (⊤ : AddSubmonoid M) T).lift_comp s t (APt.toMagnet ⊤ h)).symm

section Action

variable {X Y : Over S} (j : Y ⟶ X) (act : AAction (overO S) M (yoneda.obj X))
  (actY : AAction (overO S) M (yoneda.obj Y))

/-- `act` written on morphisms. -/
abbrev sm {X : Over S} (act : AAction (overO S) M (yoneda.obj X)) {T : Over S}
    (h : APt (overO S) M (op T)) (x : T ⟶ X) : T ⟶ X := act.smul (U := op T) h x

lemma comp_sm {X : Over S} (act : AAction (overO S) M (yoneda.obj X)) {T T' : Over S} (s : T' ⟶ T)
    (h : APt (overO S) M (op T)) (x : T ⟶ X) :
    s ≫ sm act h x = sm act (APt.res s.op h) (s ≫ x) :=
  act.map_smul (U := op T) (V := op T') s.op h x

/-- `Y` is stable under the action: `j` is equivariant. -/
def Stable : Prop := ∀ ⦃T : Over S⦄ (h : APt (overO S) M (op T)) (y : T ⟶ Y),
  sm act h (y ≫ j) = sm actY h y ≫ j

variable {j act actY} (hs : Stable j act actY)

include hs in
/-- The action preserves the condition defining the dilatation. -/
lemma Factors.sm {T : Over S} {x : T ⟶ X} (hx : Factors I j x) (h : APt (overO S) M (op T)) :
    Factors I j (Dil.sm act h x) := by
  intro Z s hZ
  obtain ⟨y, hy⟩ := hx s hZ
  refine ⟨Dil.sm actY (APt.res s.op h) y, ?_⟩
  rw [← hs, hy, comp_sm]

variable {B : Over S} {b : B ⟶ X} (hD : IsDilatation I j b)

include hs hD in
lemma exists_aUniv : ∃ a : PM M B ⟶ B,
    a ≫ b = Dil.sm act (gM M B) (piM M B ≫ b) :=
  hD.exists_lift (hD.reg.univPt _) _ (fun _ _ => trivial) ((hD.factors.comp j _).sm hs _)

/-- The action morphism `𝔸(M)_B ⟶ B`, from the universal property. -/
def aUniv : PM M B ⟶ B := (exists_aUniv hs hD).choose

lemma aUniv_spec : aUniv hs hD ≫ b = Dil.sm act (gM M B) (piM M B ≫ b) :=
  (exists_aUniv hs hD).choose_spec

/-- The value of the action on `Bl_Y^D X`. -/
def smB {T : Over S} (h : APt (overO S) M (op T)) (x : T ⟶ B) : T ⟶ B :=
  liftM x h ≫ aUniv hs hD

/-- The dilatation map is equivariant. -/
lemma smB_map {T : Over S} (h : APt (overO S) M (op T)) (x : T ⟶ B) :
    smB hs hD h x ≫ b = Dil.sm act h (x ≫ b) := by
  rw [smB, Category.assoc, aUniv_spec, comp_sm, res_liftM, liftM_π_assoc]

lemma comp_smB {T T' : Over S} (s : T' ⟶ T) (h : APt (overO S) M (op T)) (x : T ⟶ B) :
    s ≫ smB hs hD h x = smB hs hD (APt.res s.op h) (s ≫ x) := by
  simp only [smB, ← Category.assoc, comp_liftM]

/-- **Proposition 13.1, first assertion**: `𝔸(M)_S` acts on `Bl_Y^D X`, for a closed locally
principal `S'`, `Y` stable; no flatness is needed. `b` is equivariant (`smB_map`). -/
def blAction : AAction (overO S) M (yoneda.obj B) where
  smul {U} h x := smB hs hD (T := unop U) h x
  one_smul {U} x := by
    change smB hs hD 1 x = x
    have h1 : smB hs hD 1 (𝟙 B) = 𝟙 B := hD.uniq hD.reg _ _ (by
      rw [smB_map, Category.id_comp]
      exact act.one_smul (U := op B) b)
    have := comp_smB hs hD x (1 : APt (overO S) M (op B)) (𝟙 B)
    rw [h1, Category.comp_id] at this
    rw [show APt.res x.op (1 : APt (overO S) M (op B)) = 1 from by ext; simp] at this
    exact this.symm
  mul_smul {U} g h x := by
    let T1 := PM M (PM M B)
    let p : T1 ⟶ PM M B := piM M _
    let g2 := gM M (PM M B)
    let h1 : APt (overO S) M (op T1) := APt.res p.op (gM M B)
    let x1 : T1 ⟶ B := p ≫ piM M B
    have hreg : IsRegular I T1 := (hD.reg.univPt _).univPt _
    have key : smB hs hD (g2 * h1) x1 = smB hs hD g2 (smB hs hD h1 x1) := hD.uniq hreg _ _ (by
      rw [smB_map, smB_map, smB_map]
      exact act.mul_smul (U := op T1) g2 h1 (x1 ≫ b))
    let s : (unop U) ⟶ T1 := liftM (liftM x h) g
    have e := congrArg (s ≫ ·) key
    simp only [comp_smB] at e
    have e1 : APt.res s.op g2 = g := res_liftM _ _
    have e2 : APt.res s.op h1 = h := by
      change APt.res s.op (APt.res p.op (gM M B)) = h
      rw [← APt.res_comp]
      have : p.op ≫ s.op = (s ≫ p).op := rfl
      rw [this, liftM_π]
      exact res_liftM _ _
    have e3 : s ≫ x1 = x := by simp [s, x1, p]
    rw [APt.res_mul, e1, e2, e3] at e
    exact e
  map_smul {U V} f h x := comp_smB hs hD f.unop h x

end Action


end

section


open GB

variable {S : Scheme.{u}} {I : S.IdealSheafData} {M : Type u} [AddCommMonoid M]

section Maps

variable {A A' : Over S} {act : AAction (overO S) M (yoneda.obj A)}
  {act' : AAction (overO S) M (yoneda.obj A')} {f : A ⟶ A'}

/-- Equivariance of `f`. -/
def Equivar (f : A ⟶ A') (act : AAction (overO S) M (yoneda.obj A))
    (act' : AAction (overO S) M (yoneda.obj A')) : Prop :=
  ∀ ⦃T : Over S⦄ (h : APt (overO S) M (op T)) (x : T ⟶ A), sm act h x ≫ f = sm act' h (x ≫ f)

variable {N : AddSubmonoid M}

/-- The map `f^N` on points. -/
def pushPt (hf : Equivar f act act') {T : Over S} (φ : AttractorPt act N T) :
    AttractorPt act' N T where
  app t a := (show _ ⟶ A from φ.app t a) ≫ f
  naturality s t a := by
    have := φ.naturality s t a
    change (show _ ⟶ A from φ.app (s ≫ t) _) ≫ f = s.op.unop ≫ (show _ ⟶ A from φ.app t a) ≫ f
    rw [← Category.assoc]
    exact congrArg (· ≫ f) this
  equivariant t h a := by
    have := φ.equivariant t h a
    change (show _ ⟶ A from φ.app t _) ≫ f = sm act' h ((show _ ⟶ A from φ.app t a) ≫ f)
    rw [← hf]
    exact congrArg (· ≫ f) this

lemma pushPt_baseChange (hf : Equivar f act act') {T T' : Over S} (s : T' ⟶ T)
    (φ : AttractorPt act N T) : pushPt hf (φ.baseChange s) = (pushPt hf φ).baseChange s := rfl

variable {Z Z' : Over S} (rA : RepresentsAttractor act N (yoneda.obj Z))
  (rA' : RepresentsAttractor act' N (yoneda.obj Z'))

/-- `RepresentsAttractor` on morphisms. -/
abbrev rp {T : Over S} {Z : Over S} {A : Over S} {act : AAction (overO S) M (yoneda.obj A)}
    (r : RepresentsAttractor act N (yoneda.obj Z)) (z : T ⟶ Z) : AttractorPt act N T := r.equiv T z

lemma rp_comp {T T' : Over S} (s : T' ⟶ T) (z : T ⟶ Z) :
    rp rA (s ≫ z) = (rp rA z).baseChange s := rA.naturality s z

/-- The attractor map `f^N : Z ⟶ Z'`. -/
def repMap (hf : Equivar f act act') : Z ⟶ Z' := (rA'.equiv Z).symm (pushPt hf (rp rA (𝟙 Z)))

lemma rp_comp_repMap (hf : Equivar f act act') {T : Over S} (z : T ⟶ Z) :
    rp rA' (z ≫ repMap rA rA' hf) = pushPt hf (rp rA z) := by
  rw [rp_comp, repMap]
  change ((rA'.equiv Z) ((rA'.equiv Z).symm _)).baseChange z = _
  rw [Equiv.apply_symm_apply, ← pushPt_baseChange, ← rp_comp, Category.comp_id]

end Maps

section Main

variable {X Y B ZX ZY ZB : Over S} {j : Y ⟶ X} {b : B ⟶ X}
  {act : AAction (overO S) M (yoneda.obj X)} {actY : AAction (overO S) M (yoneda.obj Y)}
  (hs : Stable j act actY) (hD : IsDilatation I j b) {N : AddSubmonoid M}
  (rX : RepresentsAttractor act N (yoneda.obj ZX))
  (rY : RepresentsAttractor actY N (yoneda.obj ZY))
  (rB : RepresentsAttractor (blAction hs hD) N (yoneda.obj ZB))

include hs in
lemma equivar_j : Equivar j actY act := fun _ h y => (hs h y).symm

lemma equivar_b : Equivar b (blAction hs hD) act := fun _ h x => smB_map hs hD h x

/-- `j^N : Y^N ⟶ X^N`. -/
def jN : ZY ⟶ ZX := repMap rY rX (equivar_j hs)

/-- `b^N : (Bl_Y^D X)^N ⟶ X^N`. -/
def bN : ZB ⟶ ZX := repMap rB rX (equivar_b hs hD)

/-- A point of `X^N` over `T` with `T` lying over `S'` all of whose values are in `Y` comes from
`Y^N`. -/
lemma exists_Y_pt {T : Over S} (φ : AttractorPt act N T) [Mono j]
    (h : ∀ ⦃T' : Over S⦄ (t : T' ⟶ T) (a : APt (overO S) N (op T')),
      ∃ y : T' ⟶ Y, y ≫ j = (show T' ⟶ X from φ.app t a)) :
    ∃ γ : AttractorPt actY N T, pushPt (equivar_j hs) γ = φ := by
  choose y hy using h
  refine ⟨{ app := fun {T'} t a => y t a, naturality := ?_, equivariant := ?_ }, ?_⟩
  · intro T' T'' s t a
    apply (cancel_mono j).1
    have := φ.naturality s t a
    refine (hy _ _).trans (this.trans ?_)
    change s ≫ (show T' ⟶ X from φ.app t a) = (s ≫ y t a) ≫ j
    rw [Category.assoc, hy]
  · intro T' t k a
    apply (cancel_mono j).1
    refine (hy _ _).trans ((φ.equivariant t k a).trans ?_)
    change sm act k (show T' ⟶ X from φ.app t a) = sm actY k (y t a) ≫ j
    rw [← hs, hy]
  · refine AttractorPt.ext ?_
    funext T' t a
    exact hy t a

variable [Mono j]

/-- Points of `X^N` over a `T` with `z|_{S'}` in `Y^N` have universal value in `Y` on `𝔸(N)_T`. -/
lemma factors_univ {T : Over S} (z : T ⟶ ZX) (hz : Factors I (jN hs rX rY) z) :
    Factors I j (show (universalPoint N T).P ⟶ X from
      (rp rX z).app (universalPoint N T).π (universalPoint N T).u) := by
  intro W s hW
  obtain ⟨y, hy⟩ := hz (s ≫ (universalPoint N T).π) hW
  have h1 : pushPt (equivar_j hs) (rp rY y) = (rp rX z).baseChange (s ≫ (universalPoint N T).π) := by
    rw [← rp_comp, ← hy]
    exact (rp_comp_repMap rY rX (equivar_j hs) y).symm
  let u' := APt.res s.op (universalPoint N T).u
  refine ⟨(show W ⟶ Y from (rp rY y).app (𝟙 W) u'), ?_⟩
  have h2 := congrArg (fun p : AttractorPt act N W => p.app (𝟙 W) u') h1
  refine h2.trans ?_
  change (show W ⟶ X from (rp rX z).app (𝟙 W ≫ s ≫ (universalPoint N T).π) u') = s ≫ _
  rw [Category.id_comp]
  exact (rp rX z).naturality s (universalPoint N T).π (universalPoint N T).u

include hD in
/-- **Key step of Proposition 13.1**: on an `S'`-regular `T`, a point of `X^N` whose universal value
factors through `Y` over `S'` lifts to `(Bl_Y^D X)^N`. -/
lemma exists_lift_pt {T : Over S} (hT : IsRegular I T) (φ : AttractorPt act N T)
    (hφ : Factors I j (show (universalPoint N T).P ⟶ X from
      φ.app (universalPoint N T).π (universalPoint N T).u)) :
    ∃ ψ : AttractorPt (blAction hs hD) N T, pushPt (equivar_b hs hD) ψ = φ := by
  let U := universalPoint N T
  have hP : IsRegular I U.P := hT.univPt N
  obtain ⟨v, hv⟩ := hD.exists_lift hP _ (fun _ _ => trivial) hφ
  have hval : ∀ {T' : Over S} (t : T' ⟶ T) (a : APt (overO S) N (op T')),
      (U.lift t a ≫ v) ≫ b = (show T' ⟶ X from φ.app t a) := by
    intro T' t a
    rw [Category.assoc, hv]
    exact (φ.app_eq_of_universal U t a).symm
  have hequiv : ∀ {T' : Over S} (t : T' ⟶ T) (h : APt (overO S) M (op T'))
      (a : APt (overO S) N (op T')),
      U.lift t (APt.toMagnet N h * a) ≫ v = smB hs hD h (U.lift t a ≫ v) := by
    intro T' t h a
    let T2 := PM M U.P
    let p2 : T2 ⟶ U.P := piM M U.P
    let tt : T2 ⟶ T := p2 ≫ U.π
    let hh := gM M U.P
    let aa : APt (overO S) N (op T2) := APt.res p2.op U.u
    have hreg : IsRegular I T2 := hP.univPt _
    have key : U.lift tt (APt.toMagnet N hh * aa) ≫ v = smB hs hD hh (U.lift tt aa ≫ v) :=
      hD.uniq hreg _ _ (by
        rw [hval, smB_map, hval]
        exact φ.equivariant tt hh aa)
    let s : T' ⟶ T2 := liftM (U.lift t a) h
    have e := congrArg (s ≫ ·) key
    simp only [← Category.assoc, comp_smB] at e
    simp only [Category.assoc] at e
    have hst : s ≫ tt = t := by simp [s, tt, p2, U.lift_π]
    have e1 : APt.res s.op hh = h := res_liftM _ _
    have e2 : APt.res s.op aa = a := by
      change APt.res s.op (APt.res p2.op U.u) = a
      rw [← APt.res_comp]
      have : p2.op ≫ s.op = (s ≫ p2).op := rfl
      rw [this, liftM_π]
      exact U.res_lift t a
    have e3 : ∀ c : APt (overO S) N (op T2),
        s ≫ U.lift tt c = U.lift t (APt.res s.op c) := fun c => by
      rw [← U.lift_comp, hst]
    simp only [← Category.assoc, e3] at e
    rw [APt.res_mul, ← APt.toMagnet_res, e1, e2] at e
    simpa only [Category.assoc] using e
  refine ⟨(attractorPtEquivOfUniversal U).symm ⟨v, ?_⟩, ?_⟩
  · intro T' t h a
    exact hequiv t h a
  · refine AttractorPt.ext ?_
    funext T' t a
    exact hval t a

include hD in
/-- Injectivity of `(Bl_Y^D X)^N(T) → X^N(T)` on regular `T`. -/
lemma pt_uniq {T : Over S} (hT : IsRegular I T) (ψ ψ' : AttractorPt (blAction hs hD) N T)
    (h : pushPt (equivar_b hs hD) ψ = pushPt (equivar_b hs hD) ψ') : ψ = ψ' := by
  let U := universalPoint N T
  have hu : (show U.P ⟶ B from ψ.app U.π U.u) = ψ'.app U.π U.u :=
    hD.uniq (hT.univPt N) _ _ (congrArg (fun p : AttractorPt act N T => p.app U.π U.u) h)
  refine AttractorPt.ext ?_
  funext T' t a
  rw [ψ.app_eq_of_universal U t a, ψ'.app_eq_of_universal U t a]
  exact congrArg _ hu

/-- **Proposition 13.1** for schemes over an arbitrary `S`, in universal form. If
`(Bl_Y^D X)^N` is `S'`-regular, then `b^N : (Bl_Y^D X)^N ⟶ X^N` is the dilatation of `X^N` with
center `Y^N` along `S'`. -/
theorem attractor_isDilatation (hZB : IsRegular I ZB) :
    IsDilatation I (jN hs rX rY) (bN hs hD rX rB) where
  reg := hZB
  land := fun _ _ => trivial
  factors := by
    intro W s hW
    obtain ⟨γ, hγ⟩ := exists_Y_pt hs (pushPt (equivar_b hs hD) (rp rB s)) (fun T' t a => by
      obtain ⟨y, hy⟩ := hD.factors (show T' ⟶ B from (rp rB s).app t a) (hW.of_hom t)
      exact ⟨y, hy⟩)
    refine ⟨(rY.equiv W).symm γ, (rX.equiv W).injective ?_⟩
    have h1 := rp_comp_repMap rY rX (equivar_j hs) ((rY.equiv W).symm γ)
    have h2 := rp_comp_repMap rB rX (equivar_b hs hD) s
    refine h1.trans (Eq.trans ?_ h2.symm)
    change pushPt _ ((rY.equiv W) ((rY.equiv W).symm γ)) = _
    rw [Equiv.apply_symm_apply, hγ]
  exists_lift := by
    intro T hT z _ hz
    obtain ⟨ψ, hψ⟩ := exists_lift_pt hs hD hT (rp rX z) (factors_univ hs rX rY z hz)
    refine ⟨(rB.equiv T).symm ψ, (rX.equiv T).injective ?_⟩
    have h2 := rp_comp_repMap rB rX (equivar_b hs hD) ((rB.equiv T).symm ψ)
    refine h2.trans ?_
    change pushPt _ ((rB.equiv T) ((rB.equiv T).symm ψ)) = _
    rw [Equiv.apply_symm_apply, hψ]
  uniq := by
    intro T hT f g e
    apply (rB.equiv T).injective
    refine pt_uniq hs hD hT _ _ ?_
    have h1 := rp_comp_repMap rB rX (equivar_b hs hD) f
    have h2 := rp_comp_repMap rB rX (equivar_b hs hD) g
    refine h1.symm.trans (Eq.trans ?_ h2)
    exact congrArg _ e

end Main


end

section


open GB

variable {S : Scheme.{u}} {I : S.IdealSheafData} {M : Type u} [AddCommMonoid M]

/-- Stalkwise form of the flatness argument of Proposition 13.1. -/
lemma regular_of_flat_of_map_aux {Z B : Scheme.{u}} (p : Z ⟶ B) (q : B ⟶ S) [Flat (p ≫ q)]
    (hB : ∀ (t : B) (U : S.affineOpens) (r : Γ(S, U.1)) (_ : I.ideal U = Ideal.span {r})
      (ht : q t ∈ U.1) (g : B.presheaf.stalk t),
      q.stalkMap t (S.presheaf.germ U.1 (q t) ht r) * g = 0 → g = 0)
    (t : Z) (U : S.affineOpens) (r : Γ(S, U.1)) (hr : I.ideal U = Ideal.span {r})
    (ht : (p ≫ q) t ∈ U.1) (g : Z.presheaf.stalk t)
    (hg : (p ≫ q).stalkMap t (S.presheaf.germ U.1 ((p ≫ q) t) ht r) * g = 0) : g = 0 := by
  let A := S.presheaf.stalk ((p ≫ q) t)
  let C := Z.presheaf.stalk t
  let φ : A →+* C := ((p ≫ q).stalkMap t).hom
  let r' : A := S.presheaf.germ U.1 _ ht r
  algebraize [φ]
  have hfl : Module.Flat A C := Flat.stalkMap (p ≫ q) t
  have h0 : ∑ _i : Unit, (fun _ : Unit => r') () • (fun _ : Unit => g) () = 0 := by
    simp only [Finset.univ_unique, Finset.sum_singleton, Algebra.smul_def]
    exact hg
  obtain ⟨k, c, y, hxy, hrel⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero
    (f := fun _ : Unit => r') (x := fun _ : Unit => g) h0
  have hc0 : ∀ k', φ (c () k') = 0 := by
    intro k'
    have hrc : r' * c () k' = 0 := by simpa using hrel k'
    have hstalk : (p ≫ q).stalkMap t = q.stalkMap (p t) ≫ p.stalkMap t := Scheme.Hom.stalkMap_comp _ _ _
    have h1 : q.stalkMap (p t) (c () k') = 0 := by
      refine hB (p t) U r hr ht _ ?_
      have := congrArg (q.stalkMap (p t)).hom hrc
      exact (map_mul (q.stalkMap (p t)).hom _ _).symm.trans (this.trans (map_zero _))
    change ((p ≫ q).stalkMap t).hom (c () k') = 0
    rw [hstalk]
    change (p.stalkMap t).hom ((q.stalkMap (p t)).hom (c () k')) = 0
    erw [h1]
    exact map_zero _
  have hg' : g = ∑ k', c () k' • y k' := hxy ()
  rw [hg']
  refine Finset.sum_eq_zero fun k' _ => ?_
  rw [Algebra.smul_def]
  change φ (c () k') * _ = 0
  rw [hc0, zero_mul]

/-- The repaired flatness step: an object that is flat over `S` **and** maps to an `S'`-regular
object is `S'`-regular. Flatness over `S` alone does not suffice when `S'` is not Cartier in `S`. -/
lemma isRegular_of_flat_of_hom {Z B : Over S} (p : Z ⟶ B) (hB : IsRegular I B) [hf : Flat Z.hom] :
    IsRegular I Z := by
  have key : ∀ (q₁ : Z.left ⟶ S) (_ : p.left ≫ B.hom = q₁) (_ : Flat q₁) (t : Z.left)
      (U : S.affineOpens) (r : Γ(S, U.1)) (_ : I.ideal U = Ideal.span {r}) (ht : q₁ t ∈ U.1)
      (g : Z.left.presheaf.stalk t), q₁.stalkMap t (S.presheaf.germ U.1 (q₁ t) ht r) * g = 0 →
      g = 0 := by
    rintro _ rfl hfl
    exact regular_of_flat_of_map_aux p.left B.hom hB
  exact key _ (Over.w p) hf

section Main

variable {X Y B ZX ZY ZB : Over S} {j : Y ⟶ X} {b : B ⟶ X}
  {act : AAction (overO S) M (yoneda.obj X)} {actY : AAction (overO S) M (yoneda.obj Y)}
  (hs : Stable j act actY) (hD : IsDilatation I j b) {N : AddSubmonoid M}
  (rX : RepresentsAttractor act N (yoneda.obj ZX))
  (rY : RepresentsAttractor actY N (yoneda.obj ZY))
  (rB : RepresentsAttractor (blAction hs hD) N (yoneda.obj ZB))

include hs hD rB in
/-- `(Bl_Y^D X)^N` is `S'`-regular when flat over `S`: it maps to `Bl_Y^D X`. -/
lemma isRegular_attractor [Flat ZB.hom] : IsRegular I ZB :=
  isRegular_of_flat_of_hom (show ZB ⟶ B from (rp rB (𝟙 ZB)).toPoint) hD.reg

/-- **Proposition 13.1** (Mayeux, *Algebraic Magnetism*), `S` an arbitrary scheme, `X`, `Y` schemes.
`S'` is closed locally principal in `S`, `X` has an action of `𝔸(M)_S`, `Y` is a closed subscheme of
`X|_{S'}` stable under the action, `N` a magnet, and `X^N`, `Y^N`, `(Bl_Y^D X)^N` are represented by
schemes. If `(Bl_Y^D X)^N → S` is flat then the canonical `b^N` is the dilatation of `X^N` with
center `Y^N`; so `(Bl_Y^D X)^N = Bl_{Y^N}^{D^N} X^N` canonically over `X^N` for any model `B'` of the
latter. Flatness of `X` and of `Bl_{Y^N}^{D^N} X^N` is not needed. -/
theorem prop13_1 [Mono j] [Flat ZB.hom] {B' : Over S} {b' : B' ⟶ ZX}
    (hB' : IsDilatation I (jN hs rX rY) b') :
    IsDilatation I (jN hs rX rY) (bN hs hD rX rB) ∧
      ∃ e : ZB ≅ B', e.hom ≫ b' = bN hs hD rX rB := by
  have h := attractor_isDilatation hs hD rX rY rB (isRegular_attractor hs hD rB)
  exact ⟨h, h.exists_iso hB'⟩

/-- **Proposition 13.1, as printed**: with `X → S`, `(Bl_Y^D X)^N → S` and
`Bl_{Y^N}^{D^N} X^N → S` flat. The proof uses only the flatness of `(Bl_Y^D X)^N`, see `prop13_1`. -/
theorem prop13_1_printed [Mono j] [Flat X.hom] [Flat ZB.hom] {B' : Over S} [Flat B'.hom]
    {b' : B' ⟶ ZX} (hB' : IsDilatation I (jN hs rX rY) b') :
    ∃ e : ZB ≅ B', e.hom ≫ b' = bN hs hD rX rB :=
  (prop13_1 hs hD rX rY rB hB').2

end Main

section Affine

variable {X Y B : Over S} {j : Y ⟶ X} {b : B ⟶ X}
  {act : AAction (overO S) M (yoneda.obj X)} {actY : AAction (overO S) M (yoneda.obj Y)}
  (hs : Stable j act actY) (hD : IsDilatation I j b) (N : AddSubmonoid M)

/-- **Proposition 13.1** with representability discharged: `X → S` affine, `S` arbitrary. Then
`X^N`, `Y^N`, `(Bl_Y^D X)^N` exist by Theorem 3.20. -/
theorem prop13_1_of_isAffineHom [IsAffineHom X.hom] [IsAffineHom Y.hom] [IsAffineHom B.hom] [Mono j]
    [Flat (Zatt (blAction hs hD) N).hom] :
    IsDilatation I (jN hs (representsAttractor act N) (representsAttractor actY N))
      (bN hs hD (representsAttractor act N) (representsAttractor (blAction hs hD) N)) :=
  attractor_isDilatation hs hD _ _ _ (isRegular_attractor hs hD (representsAttractor (blAction hs hD) N))

end Affine


end

end AlgMag.Dil

#print axioms AlgMag.Dil.exists_dilatation
#print axioms AlgMag.Dil.blAction
#print axioms AlgMag.Dil.smB_map
#print axioms AlgMag.Dil.attractor_isDilatation
#print axioms AlgMag.Dil.prop13_1
#print axioms AlgMag.Dil.prop13_1_printed
#print axioms AlgMag.Dil.prop13_1_of_isAffineHom
