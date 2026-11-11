/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec9OverBBridge3Fam

/-!
# Compatible families over an object mapping to a chart

If `τ : T ⟶ V₀` with `T` affine, evaluating at `(𝟙 T, τ)` identifies `Fam 𝓜 T` with
`Γ(T) ⊗_{Γ(V₀)} 𝓜(V₀)` (`eval_bijective`). The proof compares two charts over an affine by
refinement (`test_indep`).
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits

noncomputable section

namespace AlgMag.B3

open AlgMag.S9B AlgMag.S9 AlgebraicGeometry.Space

variable {Bs : BigFppfSite.{u}} {S : Scheme.{u}} {hS : Bs.Contains S}
  {Bsp : (BigFppfOver Bs S hS)ᵒᵖ ⥤ Type u} {hB : IsAlgebraicSpace Bs S hS Bsp}
  (𝓜 : Space.Modules.{u, u} Bs S hS Bsp hB)

lemma cBm_id (V : AffineEtale Bs S hS Bsp) : cBm (𝟙 V) = 𝟙 (cB V) :=
  SB.Hom.ext ((AffineEtale.toOver Bs S hS Bsp).map_id V)

lemma Mres_comp {V'' V' V : AffineEtale Bs S hS Bsp} (φ₂ : V'' ⟶ V') (φ : V' ⟶ V) (m : Mv 𝓜 V) :
    Mres 𝓜 (φ₂ ≫ φ) m = Mres 𝓜 φ₂ (Mres 𝓜 φ m) := by
  change (Pm 𝓜).map ((AffineEtale.inclusion Bs S hS Bsp).map (φ₂ ≫ φ)).op m = _
  rw [Functor.map_comp, op_comp, PresheafOfModules.map_comp]
  rfl

lemma comp_sq {A'' A' A : SB Bsp} {V'' V' V : AffineEtale Bs S hS Bsp} {v : A ⟶ cB V}
    {v' : A' ⟶ cB V'} {v'' : A'' ⟶ cB V''} {s : A' ⟶ A} {φ : V' ⟶ V} (hc : v' ≫ cBm φ = s ≫ v)
    {s₂ : A'' ⟶ A'} {φ₂ : V'' ⟶ V'} (hc₂ : v'' ≫ cBm φ₂ = s₂ ≫ v') :
    v'' ≫ cBm (φ₂ ≫ φ) = (s₂ ≫ s) ≫ v := by
  rw [cBm_comp, ← Category.assoc, hc₂, Category.assoc, hc, Category.assoc]

lemma ρ_comp {A'' A' A : SB Bsp} {V'' V' V : AffineEtale Bs S hS Bsp} {v : A ⟶ cB V}
    {v' : A' ⟶ cB V'} {v'' : A'' ⟶ cB V''} (s : A' ⟶ A) (φ : V' ⟶ V) (hc : v' ≫ cBm φ = s ≫ v)
    (s₂ : A'' ⟶ A') (φ₂ : V'' ⟶ V') (hc₂ : v'' ≫ cBm φ₂ = s₂ ≫ v') (z : Dv 𝓜 v) :
    ρ 𝓜 s₂ φ₂ hc₂ (ρ 𝓜 s φ hc z) = ρ 𝓜 (s₂ ≫ s) (φ₂ ≫ φ) (comp_sq hc hc₂) z := by
  refine BCv.induction _ (P := fun z => ρ 𝓜 s₂ φ₂ hc₂ (ρ 𝓜 s φ hc z) =
    ρ 𝓜 (s₂ ≫ s) (φ₂ ≫ φ) (comp_sq hc hc₂) z) ?_ (fun a m => ?_) (fun x y hx hy => ?_) z
  · simp
  · simp only [ρ, bcMap_tm]
    rw [Mres_comp, op_comp, (OB Bsp).map_comp]
    rfl
  · rw [map_add, map_add, map_add, hx, hy]

lemma ρ_congr {A' A : SB Bsp} {V' V : AffineEtale Bs S hS Bsp} {v : A ⟶ cB V} {v' : A' ⟶ cB V'}
    {s s₂ : A' ⟶ A} {φ φ₂ : V' ⟶ V} (hs : s = s₂) (hφ : φ = φ₂) (hc : v' ≫ cBm φ = s ≫ v)
    (hc₂ : v' ≫ cBm φ₂ = s₂ ≫ v) (z : Dv 𝓜 v) : ρ 𝓜 s φ hc z = ρ 𝓜 s₂ φ₂ hc₂ z := by
  subst hs hφ; rfl

/-- `𝓜` is cartesian on charts: Stacks `QuasicoherentCartesianOnAffineCharts`. -/
def Cartesian : Prop :=
  ∀ {V' V : AffineEtale Bs S hS Bsp} (φ : V' ⟶ V),
    IsBC ((OB Bsp).map (cBm φ).op).hom (Mres 𝓜 φ) (Mres_smul 𝓜 φ)

/-- Over a fixed affine, changing the chart along `φ` is bijective. -/
theorem ρ_bij (hC : Cartesian 𝓜) {A : SB Bsp} {V' V : AffineEtale Bs S hS Bsp} {v : A ⟶ cB V}
    {v' : A ⟶ cB V'} (φ : V' ⟶ V) (hc : v' ≫ cBm φ = 𝟙 A ≫ v) :
    Function.Bijective (ρ 𝓜 (𝟙 A) φ hc) := by
  have hg : ((OB Bsp).map (𝟙 A).op).hom = RingHom.id _ := by rw [op_id, (OB Bsp).map_id]; rfl
  unfold ρ
  have key : ∀ (g : (OB Bsp).obj (op A) →+* (OB Bsp).obj (op A)) (hg : g = RingHom.id _)
      (c : g.comp ((OB Bsp).map v.op).hom =
        ((OB Bsp).map v'.op).hom.comp ((OB Bsp).map (cBm φ).op).hom),
      Function.Bijective (bcMap ((OB Bsp).map (cBm φ).op).hom g c (Mres 𝓜 φ) (Mres_smul 𝓜 φ)) := by
    rintro g rfl c
    exact bcMap_bijective _ _ c _ _ (hC φ)
  exact key _ hg _

lemma sq1 {A' A : SB Bsp} {V : AffineEtale Bs S hS Bsp} (t : A' ⟶ A) (v : A ⟶ cB V) :
    (t ≫ v) ≫ cBm (𝟙 V) = t ≫ v := by rw [cBm_id, Category.comp_id]

lemma sq1' {A : SB Bsp} {V : AffineEtale Bs S hS Bsp} (v : A ⟶ cB V) :
    v ≫ cBm (𝟙 V) = 𝟙 A ≫ v := by rw [cBm_id, Category.comp_id, Category.id_comp]

/-- Zariski descent of the values on affines. -/
def ZDesc : Prop :=
  ∀ {A : SB Bsp} (_ : IsAffine A.left) {V : AffineEtale Bs S hS Bsp} (v : A ⟶ cB V) {ι : Type u}
    (Ai : ι → SB Bsp) (s : ∀ i, Ai i ⟶ A) (_ : ∀ i, IsAffine (Ai i).left)
    (_ : ∀ i, IsOpenImmersion (SB.Hom.left (s i)))
    (_ : ∀ x : A.left, ∃ i, x ∈ Set.range (SB.Hom.left (s i)))
    (y : ∀ i, Dv 𝓜 (s i ≫ v))
    (_ : ∀ (i j : ι) {A'' : SB Bsp} (_ : IsAffine A''.left) (p : A'' ⟶ Ai i) (q : A'' ⟶ Ai j)
      (e : p ≫ s i = q ≫ s j) (v'' : A'' ⟶ cB V) (h1 : v'' ≫ cBm (𝟙 V) = p ≫ s i ≫ v)
      (h2 : v'' ≫ cBm (𝟙 V) = q ≫ s j ≫ v),
      ρ 𝓜 p (𝟙 V) h1 (y i) = ρ 𝓜 q (𝟙 V) h2 (y j)),
    ∃! z : Dv 𝓜 v, ∀ i, ρ 𝓜 (s i) (𝟙 V) (sq1 (s i) v) z = y i

/-- A chart `W` with maps to `V`, `V₀`, and `A ⟶ W` over them. -/
structure Test {A : SB Bsp} {V V₀ : AffineEtale Bs S hS Bsp} (v : A ⟶ cB V) (v₀ : A ⟶ cB V₀) where
  /-- the chart -/
  W : AffineEtale Bs S hS Bsp
  f : W ⟶ V
  f₀ : W ⟶ V₀
  w : A ⟶ cB W
  h : w ≫ cBm f = v
  h₀ : w ≫ cBm f₀ = v₀

/-- The geometric input. -/
structure Geo (Bsp : (BigFppfOver Bs S hS)ᵒᵖ ⥤ Type u) : Prop where
  /-- an affine open neighbourhood with a lift through an open -/
  opn : ∀ {A' A Ai : SB Bsp} (s : A' ⟶ A) (si : Ai ⟶ A) (_ : IsOpenImmersion (SB.Hom.left si))
    (x : A'.left) (_ : SB.Hom.left s x ∈ Set.range (SB.Hom.left si)),
    ∃ (A'' : SB Bsp) (t : A'' ⟶ A') (l : A'' ⟶ Ai), IsAffine A''.left ∧
      IsOpenImmersion (SB.Hom.left t) ∧ x ∈ Set.range (SB.Hom.left t) ∧ l ≫ si = t ≫ s
  /-- a local chart over two given ones -/
  tst : ∀ {A : SB Bsp} {V V₀ : AffineEtale Bs S hS Bsp} (v : A ⟶ cB V) (v₀ : A ⟶ cB V₀)
    (x : A.left), ∃ (A' : SB Bsp) (t : A' ⟶ A), IsAffine A'.left ∧
      IsOpenImmersion (SB.Hom.left t) ∧ x ∈ Set.range (SB.Hom.left t) ∧
        Nonempty (Test (t ≫ v) (t ≫ v₀))
  /-- two tests have a common local refinement -/
  ref : ∀ {A : SB Bsp} {V V₀ : AffineEtale Bs S hS Bsp} {v : A ⟶ cB V} {v₀ : A ⟶ cB V₀}
    (τ τ' : Test v v₀) (x : A.left), ∃ (A' : SB Bsp) (t : A' ⟶ A) (W : AffineEtale Bs S hS Bsp)
      (g : W ⟶ τ.W) (g' : W ⟶ τ'.W) (w : A' ⟶ cB W), IsAffine A'.left ∧
      IsOpenImmersion (SB.Hom.left t) ∧ x ∈ Set.range (SB.Hom.left t) ∧
      g ≫ τ.f = g' ≫ τ'.f ∧ g ≫ τ.f₀ = g' ≫ τ'.f₀ ∧ w ≫ cBm g = t ≫ τ.w ∧ w ≫ cBm g' = t ≫ τ'.w

variable {𝓜}

/-- Separation of values for affine open coverings. -/
theorem sep (hZ : ZDesc 𝓜) {A : SB Bsp} (hA : IsAffine A.left) {V : AffineEtale Bs S hS Bsp}
    {v : A ⟶ cB V} (z z' : Dv 𝓜 v)
    (H : ∀ x : A.left, ∃ (A' : SB Bsp) (t : A' ⟶ A), IsAffine A'.left ∧
      IsOpenImmersion (SB.Hom.left t) ∧ x ∈ Set.range (SB.Hom.left t) ∧
      ρ 𝓜 t (𝟙 V) (sq1 t v) z = ρ 𝓜 t (𝟙 V) (sq1 t v) z') :
    z = z' := by
  choose Ai t hAi hop hx he using H
  obtain ⟨y, -, huniq⟩ := hZ hA v Ai t hAi hop (fun x => ⟨x, hx x⟩)
    (fun i => ρ 𝓜 (t i) (𝟙 V) (sq1 _ v) z)
    (fun i j A'' hA'' p q e v'' h1 h2 => by
      rw [ρ_comp, ρ_comp]
      exact ρ_congr 𝓜 e rfl _ _ z)
  rw [huniq z (fun _ => rfl), huniq z' (fun i => (he i).symm)]

/-- **Two charts over an affine, by refinement.** An equality of values read in one chart `W` over
`V, V₀` holds in every other. -/
theorem test_indep (hC : Cartesian 𝓜) (hZ : ZDesc 𝓜) (hG : Geo Bsp) {A : SB Bsp}
    (hA : IsAffine A.left) {V V₀ : AffineEtale Bs S hS Bsp} {v : A ⟶ cB V} {v₀ : A ⟶ cB V₀}
    (z : Dv 𝓜 v) (z₀ : Dv 𝓜 v₀) (τ τ' : Test v v₀)
    (H : ρ 𝓜 (𝟙 A) τ.f (by rw [τ.h, Category.id_comp]) z =
      ρ 𝓜 (𝟙 A) τ.f₀ (by rw [τ.h₀, Category.id_comp]) z₀) :
    ρ 𝓜 (𝟙 A) τ'.f (by rw [τ'.h, Category.id_comp]) z =
      ρ 𝓜 (𝟙 A) τ'.f₀ (by rw [τ'.h₀, Category.id_comp]) z₀ := by
  refine sep hZ hA _ _ fun x => ?_
  obtain ⟨A', t, W, g, g', w, hA', hop, hx, e, e₀, hw, hw'⟩ := hG.ref τ τ' x
  refine ⟨A', t, hA', hop, hx, ?_⟩
  have hb := (ρ_bij 𝓜 hC (A := A') (v := t ≫ τ'.w) (v' := w) g'
    (by rw [hw', Category.id_comp])).1
  have hc1 : (t ≫ τ'.w) ≫ cBm (𝟙 τ'.W) = t ≫ τ'.w := sq1 t τ'.w
  refine ?_
  have hH := congrArg (ρ 𝓜 t g (by rw [hw])) H
  rw [ρ_comp, ρ_comp] at hH
  -- transport both sides along the common refinement
  have key : ∀ (a b : Dv 𝓜 (t ≫ τ'.w)),
      ρ 𝓜 (𝟙 A') g' (by rw [hw', Category.id_comp]) a =
        ρ 𝓜 (𝟙 A') g' (by rw [hw', Category.id_comp]) b → a = b := fun a b h => hb h
  have e1 : (𝟙 A' ≫ t) = t := Category.id_comp t
  have L : ρ 𝓜 t τ'.f (by rw [Category.assoc, τ'.h]) z =
      ρ 𝓜 t τ'.f₀ (by rw [Category.assoc, τ'.h₀]) z₀ := by
    apply key
    rw [ρ_comp, ρ_comp]
    refine Eq.trans ?_ (Eq.trans hH ?_)
    · exact ρ_congr 𝓜 (by simp) (by rw [← e]) _ _ z
    · exact ρ_congr 𝓜 (by simp) (by simp [e₀]) _ _ z₀
  rw [ρ_comp, ρ_comp]
  exact (ρ_congr 𝓜 (by simp) (by simp) _ _ z).trans
    (L.trans (ρ_congr 𝓜 (by simp) (by simp) _ _ z₀))

/-- `y` and `y₀` have the same reading in every chart over `V`, `V₀`, above every affine. -/
def Match {A : SB Bsp} {V V₀ : AffineEtale Bs S hS Bsp} {v : A ⟶ cB V} {v₀ : A ⟶ cB V₀}
    (y : Dv 𝓜 v) (y₀ : Dv 𝓜 v₀) : Prop :=
  ∀ (A' : SB Bsp) (_ : IsAffine A'.left) (s : A' ⟶ A) {W : AffineEtale Bs S hS Bsp} (f : W ⟶ V)
    (f₀ : W ⟶ V₀) (w : A' ⟶ cB W) (h : w ≫ cBm f = s ≫ v) (h₀ : w ≫ cBm f₀ = s ≫ v₀),
    ρ 𝓜 s f h y = ρ 𝓜 s f₀ h₀ y₀

/-- Agreement in a test over a neighbourhood of each point gives `Match`. -/
theorem match_of_local (hC : Cartesian 𝓜) (hZ : ZDesc 𝓜) (hG : Geo Bsp) {A : SB Bsp}
    {V V₀ : AffineEtale Bs S hS Bsp} {v : A ⟶ cB V} {v₀ : A ⟶ cB V₀} (y : Dv 𝓜 v) (y₀ : Dv 𝓜 v₀)
    (H : ∀ x : A.left, ∃ (A' : SB Bsp) (t : A' ⟶ A) (τ : Test (t ≫ v) (t ≫ v₀)),
      IsOpenImmersion (SB.Hom.left t) ∧ x ∈ Set.range (SB.Hom.left t) ∧
      ρ 𝓜 t τ.f (by rw [τ.h]) y = ρ 𝓜 t τ.f₀ (by rw [τ.h₀]) y₀) : Match y y₀ := by
  intro A' hA' s W f f₀ w h h₀
  refine sep hZ hA' _ _ fun x => ?_
  obtain ⟨Ai, ti, τ, hop, ⟨z, hz⟩, he⟩ := H (SB.Hom.left s x)
  obtain ⟨A'', t, l, hA'', hop', hx', hl⟩ := hG.opn s ti hop x ⟨z, hz⟩
  refine ⟨A'', t, hA'', hop', hx', ?_⟩
  rw [ρ_comp, ρ_comp]
  have hv : ∀ (u : Ai ⟶ cB V), u = ti ≫ v → l ≫ u = t ≫ s ≫ v := by
    rintro u rfl; rw [← Category.assoc, hl, Category.assoc]
  have hv₀ : ∀ (u : Ai ⟶ cB V₀), u = ti ≫ v₀ → l ≫ u = t ≫ s ≫ v₀ := by
    rintro u rfl; rw [← Category.assoc, hl, Category.assoc]
  -- the two tests over `A''`
  let σ : Test (t ≫ s ≫ v) (t ≫ s ≫ v₀) :=
    ⟨τ.W, τ.f, τ.f₀, l ≫ τ.w, by rw [Category.assoc, τ.h]; exact hv _ rfl,
      by rw [Category.assoc, τ.h₀]; exact hv₀ _ rfl⟩
  let σ' : Test (t ≫ s ≫ v) (t ≫ s ≫ v₀) :=
    ⟨W, f, f₀, t ≫ w, by rw [Category.assoc, h], by rw [Category.assoc, h₀]⟩
  have hs : (l ≫ ti) = t ≫ s := hl
  let z₁ : Dv 𝓜 (t ≫ s ≫ v) := ρ 𝓜 (t ≫ s) (𝟙 V) (by rw [cBm_id, Category.comp_id, Category.assoc]) y
  let z₂ : Dv 𝓜 (t ≫ s ≫ v₀) := ρ 𝓜 (t ≫ s) (𝟙 V₀) (by rw [cBm_id, Category.comp_id, Category.assoc]) y₀
  have hσ := test_indep hC hZ hG hA'' z₁ z₂ σ σ' (by
    have := congrArg (ρ 𝓜 l (𝟙 τ.W) (by rw [cBm_id, Category.comp_id])) he
    rw [ρ_comp, ρ_comp] at this
    simp only [z₁, z₂, ρ_comp]
    exact (ρ_congr 𝓜 (by simp [hl]) (by simp only [Category.id_comp]; rfl) _ _ y).trans
      (this.trans (ρ_congr 𝓜 (by simp [hl]) (by simp only [Category.id_comp]; rfl) _ _ y₀)))
  simp only [z₁, z₂, ρ_comp] at hσ
  exact (ρ_congr 𝓜 (by simp) (by simp [σ']) _ _ y).trans
    (hσ.trans (ρ_congr 𝓜 (by simp) (by simp [σ']) _ _ y₀))

/-- Uniqueness in `Match`. -/
theorem match_unique (hC : Cartesian 𝓜) (hZ : ZDesc 𝓜) (hG : Geo Bsp) {A : SB Bsp}
    (hA : IsAffine A.left) {V V₀ : AffineEtale Bs S hS Bsp} {v : A ⟶ cB V} {v₀ : A ⟶ cB V₀}
    {y y' : Dv 𝓜 v} {y₀ : Dv 𝓜 v₀} (h : Match y y₀) (h' : Match y' y₀) : y = y' := by
  refine sep hZ hA _ _ fun x => ?_
  obtain ⟨A', t, hA', hop, hx, ⟨τ⟩⟩ := hG.tst v v₀ x
  refine ⟨A', t, hA', hop, hx, ?_⟩
  refine (ρ_bij 𝓜 hC (v := t ≫ v) (v' := τ.w) τ.f (by rw [τ.h, Category.id_comp])).1 ?_
  rw [ρ_comp, ρ_comp]
  have e := h A' hA' t τ.f τ.f₀ τ.w τ.h τ.h₀
  have e' := h' A' hA' t τ.f τ.f₀ τ.w τ.h τ.h₀
  exact (ρ_congr 𝓜 (by simp) (by simp) _ _ y).trans
    (e.trans (e'.symm.trans (ρ_congr 𝓜 (by simp) (by simp) _ _ y')))

/-- Existence in `Match`: gluing the readings through local charts. -/
theorem match_exists (hC : Cartesian 𝓜) (hZ : ZDesc 𝓜) (hG : Geo Bsp) {A : SB Bsp}
    (hA : IsAffine A.left) {V V₀ : AffineEtale Bs S hS Bsp} (v : A ⟶ cB V) {v₀ : A ⟶ cB V₀}
    (y₀ : Dv 𝓜 v₀) : ∃ y : Dv 𝓜 v, Match y y₀ := by
  choose Ai t hAi hop hx hτ using fun x : A.left => hG.tst v v₀ x
  let τ := fun x => (hτ x).some
  have hid : ∀ x, (τ x).w ≫ cBm (τ x).f = 𝟙 (Ai x) ≫ t x ≫ v := fun x => by
    rw [(τ x).h, Category.id_comp]
  have hb := fun x => ρ_bij 𝓜 hC (τ x).f (hid x)
  have hr : ∀ x, ∃ a : Dv 𝓜 (t x ≫ v), ρ 𝓜 (𝟙 _) (τ x).f (hid x) a =
      ρ 𝓜 (t x) (τ x).f₀ (τ x).h₀ y₀ := fun x => (hb x).2 _
  choose a ha using hr
  obtain ⟨y, hy, -⟩ := hZ hA v Ai t hAi hop (fun x => ⟨x, hx x⟩) a
    (fun i j A'' hA'' p q e v'' h1 h2 => by
      have hv : p ≫ t i ≫ v = v'' := by rw [← h1, cBm_id, Category.comp_id]
      have hv' : q ≫ t j ≫ v = v'' := by rw [← h2, cBm_id, Category.comp_id]
      have e₀ : q ≫ t j ≫ v₀ = p ≫ t i ≫ v₀ := by
        rw [← Category.assoc, ← Category.assoc, e]
      let σ : Test v'' (p ≫ t i ≫ v₀) :=
        ⟨(τ i).W, (τ i).f, (τ i).f₀, p ≫ (τ i).w, by rw [Category.assoc, (τ i).h, hv],
          by rw [Category.assoc, (τ i).h₀]⟩
      let σ' : Test v'' (p ≫ t i ≫ v₀) :=
        ⟨(τ j).W, (τ j).f, (τ j).f₀, q ≫ (τ j).w, by rw [Category.assoc, (τ j).h, hv'],
          by rw [Category.assoc, (τ j).h₀, e₀]⟩
      let y₀' : Dv 𝓜 (p ≫ t i ≫ v₀) := ρ 𝓜 (p ≫ t i) (𝟙 V₀)
        (by rw [cBm_id, Category.comp_id, Category.assoc]) y₀
      have c1 : ρ 𝓜 (𝟙 A'') σ.f (by rw [σ.h, Category.id_comp]) (ρ 𝓜 p (𝟙 V) h1 (a i)) =
          ρ 𝓜 (𝟙 A'') σ.f₀ (by rw [σ.h₀, Category.id_comp]) y₀' := by
        have := congrArg (ρ 𝓜 p (𝟙 (τ i).W) (by rw [cBm_id, Category.comp_id])) (ha i)
        rw [ρ_comp, ρ_comp] at this
        simp only [y₀', ρ_comp]
        exact (ρ_congr 𝓜 (by simp) (by simp only [Category.id_comp, Category.comp_id]; rfl) _ _ _).trans
          (this.trans (ρ_congr 𝓜 (by simp) (by simp only [Category.id_comp, Category.comp_id]; rfl) _ _ _))
      have c2 : ρ 𝓜 (𝟙 A'') σ'.f (by rw [σ'.h, Category.id_comp]) (ρ 𝓜 q (𝟙 V) h2 (a j)) =
          ρ 𝓜 (𝟙 A'') σ'.f₀ (by rw [σ'.h₀, Category.id_comp]) y₀' := by
        have := congrArg (ρ 𝓜 q (𝟙 (τ j).W) (by rw [cBm_id, Category.comp_id])) (ha j)
        rw [ρ_comp, ρ_comp] at this
        simp only [y₀', ρ_comp]
        exact (ρ_congr 𝓜 (by simp) (by simp only [Category.id_comp, Category.comp_id]; rfl) _ _ _).trans
          (this.trans (ρ_congr 𝓜 (by simp [e]) (by simp only [Category.id_comp, Category.comp_id]; rfl) _ _ _))
      have c3 := test_indep hC hZ hG hA'' _ _ σ σ' c1
      exact (ρ_bij 𝓜 hC σ'.f (by rw [σ'.h, Category.id_comp])).1 (c3.trans c2.symm))
  refine ⟨y, match_of_local hC hZ hG y y₀ fun x => ⟨Ai x, t x, τ x, hop x, hx x, ?_⟩⟩
  have := ha x
  rw [← hy x, ρ_comp] at this
  exact (ρ_congr 𝓜 (by simp) (by simp) _ _ y).trans this

/-- **Over an affine `T` mapping to a chart, a compatible family is its value at that chart.** -/
theorem eval_bijective (hC : Cartesian 𝓜) (hZ : ZDesc 𝓜) (hG : Geo Bsp) {T : SB Bsp}
    (hT : IsAffine T.left) {V₀ : AffineEtale Bs S hS Bsp} (τ : T ⟶ cB V₀) :
    Function.Bijective (fun x : Fam 𝓜 T => x.val hT (𝟙 T) τ) := by
  have hm : ∀ (x : Fam 𝓜 T) {A : SB Bsp} (hA : IsAffine A.left) (a : A ⟶ T)
      {V : AffineEtale Bs S hS Bsp} (v : A ⟶ cB V),
      Match (x.val hA a v) (ρ 𝓜 a (𝟙 V₀) (sq1 a τ) (x.val hT (𝟙 T) τ)) := by
    intro x A hA a V v A' hA' s W f f₀ w h h₀
    rw [ρ_comp, x.compat hA' hA a v w s f h, x.compat hA' hT (𝟙 T) τ w (s ≫ a) (f₀ ≫ 𝟙 V₀) _,
      Category.comp_id]
  constructor
  · intro x x' he
    refine Fam.ext fun {A} hA a {V} v => ?_
    have h1 : Match _ _ := hm x hA a v
    have h2 : Match _ _ := hm x' hA a v
    have he' : x.val hT (𝟙 T) τ = x'.val hT (𝟙 T) τ := he
    rw [he'] at h1
    exact match_unique hC hZ hG hA h1 h2
  · intro y₀
    let y : ∀ {A : SB Bsp} (hA : IsAffine A.left) (a : A ⟶ T) {V : AffineEtale Bs S hS Bsp}
        (v : A ⟶ cB V), Dv 𝓜 v := fun hA a _ v =>
      (match_exists hC hZ hG hA v (ρ 𝓜 a (𝟙 V₀) (sq1 a τ) y₀)).choose
    have hy : ∀ {A : SB Bsp} (hA : IsAffine A.left) (a : A ⟶ T) {V : AffineEtale Bs S hS Bsp}
        (v : A ⟶ cB V), Match (y hA a v) (ρ 𝓜 a (𝟙 V₀) (sq1 a τ) y₀) := fun hA a _ v =>
      (match_exists hC hZ hG hA v (ρ 𝓜 a (𝟙 V₀) (sq1 a τ) y₀)).choose_spec
    refine ⟨⟨y, fun {A' A} hA' hA a {V' V} v v' s φ hc => ?_⟩, ?_⟩
    · refine match_unique hC hZ hG hA' ?_ (hy hA' (s ≫ a) v')
      intro A'' hA'' s' W f f₀ w h h₀
      rw [ρ_comp, ρ_comp]
      have := hy hA a v A'' hA'' (s' ≫ s) (f ≫ φ) (f₀ ≫ 𝟙 V₀) w (comp_sq hc h) (by
        rw [cBm_comp, ← Category.assoc, h₀]; simp [cBm_id])
      rw [ρ_comp] at this
      exact this.trans (ρ_congr 𝓜 (by simp) (by simp) _ _ y₀)
    · -- the value at `τ` itself
      have h1 : Match _ _ := hy hT (𝟙 T) τ
      have hself : Match y₀ (ρ 𝓜 (𝟙 T) (𝟙 V₀) (sq1 _ τ) y₀) := by
        refine match_of_local hC hZ hG _ _ fun x => ⟨T, 𝟙 T,
          ⟨V₀, 𝟙 V₀, 𝟙 V₀, τ, sq1' τ, by rw [cBm_id, Category.comp_id, Category.id_comp, Category.id_comp]⟩, ?_, ⟨x, ?_⟩, ?_⟩
        · rw [SB.id_left]; infer_instance
        · rw [SB.id_left]; rfl
        · rw [ρ_comp]
          exact ρ_congr 𝓜 (by simp) (by simp) _ _ y₀
      exact match_unique hC hZ hG hT h1 hself

end AlgMag.B3
