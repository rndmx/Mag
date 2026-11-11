/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.XProductsAction
import AlgMag.Sec8Representability
import AlgMag.Sec5Etale
import AlgMag.GeneralBaseThm320

/-!
# Differences from the published text of the X-products paper (Semigroup Forum, doi 10.1007/s00233-026-10695-7)

The printed versions are in `AlgMag.XProductsPrinted` (Theorem 4.1, Proposition 4.3 (2), Proposition 4.5),
`AlgMag.XProductsF1Base` (Proposition 3.2) and `AlgMag.XProductsExampleFunctor` (Example 4.4). This file keeps
the stronger forms, as remarks: `thm41`, `prop45` need neither condition 1, 2 nor finiteness of `A`. Differences:

1. Base. §4 works over `S = Spec ℤ`. `thm41PrintedZ` (`AlgMag.XProductsPrintedLfp`, outside the default target)
   is that case with the literal hypotheses; `thm41Printed` replaces "quasi-separated, locally of finite
   presentation" by "`S` locally noetherian, charts of finite type", which that case implies.
2. Functor of points. `Hom_{D(M)_T}(𝔸(𝒩)_T, X_T)` is `XNPt`: values on `T'`-points over `T' → T`, natural and
   equivariant. No scheme `𝔸(𝒩)_T` or morphism of spaces out of it is formed.
3. Proposition 3.3 applied to `𝔸(𝒩)_T` and an algebraic space `X_T`. `prop33` is for schemes over `ℤ`, so
   this step is not an instance of it. What is needed is `prop33T`: `X` a sheaf, `𝔸(𝒩)_T` covered by the
   `𝔸(N_α)_T` with intersections `D(Z)_T`, equivariance checked on the cover (header of `XProductsPrinted`).
4. "`X^Z → X` is a monomorphism", condition 1. Proposition 3.35 and Theorem A.1 are applied as printed
   (`toPoint_injective_cond1`), but `X^{D(M/Z)}` is a subfunctor of `X` by definition here, so the injectivity
   does not use the closed immersion given by Theorem A.1. Quasi-separatedness is unused: `S = Spec ℤ` is
   Theorem A.1 (i). "Connected fibres" is `AppR.ConnectedFibres`, over fields mapping to `S`.
5. Proposition 4.5. Tags 042P, 042O are applied on points, not quoted.
6. Example 4.4 is on the category of all schemes, not on a big fppf site; `{0}`, `{∞}` are `⊤_ Scheme`.

# X-products of attractors: Theorem 4.1, Definition 4.2, Proposition 4.5

Mayeux, *Algebraic magnetism: X-products of attractors via F₁-geometry*, §4.

The results hold on any category `C` of schemes (a functor `τ : C ⥤ Scheme`) with a topology for which
`𝔸(𝒩)` is locally covered by the `𝔸(N_α)`. This is specialized to the big fppf site (for algebraic
spaces) and to `Over S` (for the affine case of Proposition 4.3).

## Main results

* `AlgMag.XP.XNPt`, `AlgMag.XP.XN`: **Definition 4.2**, the attractor `X^𝒩 = Hom_{D(M)}(𝔸(𝒩), X)`.
* `AlgMag.XP.XProdPt`: the fibre product `∏_X X^{N_α}`, on points.
* `AlgMag.XP.thm41Equiv`: **Theorem 4.1**, in general.
* `AlgMag.XP.toPoint_injective_gp`: `X^Z → X` is a monomorphism for a subgroup `Z`, for any fppf sheaf.
* `AlgMag.XP.thm41`: **Theorem 4.1** on the big fppf site. The conditions 1 and 2 of the printed statement
  are not needed: by Proposition 3.35 the attractor `X^Z` is the fixed point functor, a subfunctor of `X`.
* `AlgMag.XP.prop45`: **Proposition 4.5**.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

set_option linter.unusedSectionVars false

namespace AlgMag.XP

open GB

variable {M : Type u} [AddCommGroup M] {A : Type u} (𝓝 : MagnetFamily M A)
variable {C : Type*} [Category.{v} C] (τ : C ⥤ Scheme.{u})

/-- The presheaf of rings `T ↦ Γ(τ T, ⊤)`. -/
abbrev τO : Cᵒᵖ ⥤ CommRingCat.{u} := τ.op ⋙ Scheme.Γ

/-- `T'`-points of `𝔸(P)` on `C`. -/
noncomputable def ptsT (P : AddSubmonoid M) (T' : C) :
    (τ.obj T' ⟶ AZ P) ≃ APt (τO τ) P (op T') :=
  pts P (τ.obj T')

variable {τ}

lemma ptsT_comp {P : AddSubmonoid M} {T' T'' : C} (s : T'' ⟶ T') (a : τ.obj T' ⟶ AZ P) :
    ptsT τ P T'' (τ.map s ≫ a) = APt.res s.op (ptsT τ P T' a) :=
  pts_comp (τ.map s) a

lemma ptsT_map {P Q : AddSubmonoid M} (h : P ≤ Q) {T' : C} (a : τ.obj T' ⟶ AZ Q) :
    ptsT τ P T' (a ≫ AZmap (AddSubmonoid.inclusion h)) = APt.restrict h (ptsT τ Q T' a) :=
  pts_map h a

lemma ptsT_smulA {P : AddSubmonoid M} {T' : C} (k : APt (τO τ) M (op T')) (a : τ.obj T' ⟶ AZ P) :
    ptsT τ P T' (smulA (V := τ.obj T') k a) = APt.toMagnet P k * ptsT τ P T' a :=
  pts_smulA k a

variable (τ)
variable {X : Cᵒᵖ ⥤ Type u} (act : AAction (τO τ) M X)

section Defs

variable [Nonempty A]

/-- **Definition 4.2**, on points: a `T`-point of `X^𝒩 = Hom_{D(M)}(𝔸(𝒩), X)` is a `D(M)_T`-equivariant
`T`-morphism `𝔸(𝒩)_T → X_T`, given by its values on points over every `T' → T`. -/
@[ext]
structure XNPt (T : C) where
  /-- The value at a point of `𝔸(𝒩)` over `t : T' ⟶ T`. -/
  app : ∀ {T' : C} (_ : T' ⟶ T), (τ.obj T' ⟶ 𝓝.AN) → X.obj (op T')
  naturality : ∀ {T' T'' : C} (s : T'' ⟶ T') (t : T' ⟶ T) (y : τ.obj T' ⟶ 𝓝.AN),
    app (s ≫ t) (τ.map s ≫ y) = X.map s.op (app t y)
  equivariant : ∀ {T' : C} (t : T' ⟶ T) (k : APt (τO τ) M (op T')) (y : τ.obj T' ⟶ 𝓝.AN),
    app t (𝓝.smulN (W := τ.obj T') k y) = act.smul k (app t y)

variable {τ act 𝓝}

/-- Base change of points of `X^𝒩`. -/
def XNPt.baseChange {T T'' : C} (s : T'' ⟶ T) (ψ : XNPt 𝓝 τ act T) : XNPt 𝓝 τ act T'' where
  app t y := ψ.app (t ≫ s) y
  naturality r t y := by
    rw [Category.assoc]; exact ψ.naturality r (t ≫ s) y
  equivariant t k y := ψ.equivariant (t ≫ s) k y

variable (τ act 𝓝) in
/-- **Definition 4.2**: the attractor `X^𝒩` associated to `𝒩`, as a functor. -/
def XN : Cᵒᵖ ⥤ Type _ where
  obj T := XNPt 𝓝 τ act (unop T)
  map f := ↾ XNPt.baseChange f.unop
  map_id T := by
    ext ψ T' t y
    change ψ.app (t ≫ 𝟙 _) y = ψ.app t y
    simp
  map_comp f g := by
    ext ψ T' t y
    change ψ.app (t ≫ g.unop ≫ f.unop) y = ψ.app ((t ≫ g.unop) ≫ f.unop) y
    simp

variable (τ 𝓝) in
/-- The unit point of `𝔸(𝒩)`, the image of `1 ∈ D(Z)`. -/
noncomputable def unitPt (T' : C) : τ.obj T' ⟶ 𝓝.AN :=
  (ptsT τ 𝓝.Z.toAddSubmonoid T').symm 1 ≫ 𝓝.ιD

lemma comp_unitPt {T' T'' : C} (s : T'' ⟶ T') : τ.map s ≫ unitPt 𝓝 τ T' = unitPt 𝓝 τ T'' := by
  rw [unitPt, unitPt, ← Category.assoc]
  congr 1
  apply (ptsT τ _ T'').injective
  rw [ptsT_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact MonoidHom.ext fun p => by
    rw [APt.res_apply, MonoidHom.one_apply, MonoidHom.one_apply, map_one]

/-- The morphism `X^𝒩 → X`: the value at the unit point. -/
noncomputable def XNPt.toPoint {T : C} (ψ : XNPt 𝓝 τ act T) : X.obj (op T) :=
  ψ.app (𝟙 T) (unitPt 𝓝 τ T)

lemma XNPt.toPoint_baseChange {T T'' : C} (s : T'' ⟶ T) (ψ : XNPt 𝓝 τ act T) :
    (ψ.baseChange s).toPoint = X.map s.op ψ.toPoint := by
  change ψ.app (𝟙 T'' ≫ s) (unitPt 𝓝 τ T'') = X.map s.op (ψ.app (𝟙 T) (unitPt 𝓝 τ T))
  rw [← ψ.naturality, comp_unitPt, Category.id_comp, Category.comp_id]

end Defs

/-- The `X`-fibre product `… ×_X X^{N_α} ×_X X^{N_β} ×_X …` of Theorem 4.1, on points. -/
def XProdPt (T : C) : Type _ :=
  { Φ : ∀ α, AttractorPt act (𝓝.N α) T // ∀ α β, (Φ α).toPoint = (Φ β).toPoint }

variable {τ act 𝓝}

/-- Base change of points of the fibre product. -/
def XProdPt.baseChange {T T'' : C} (s : T'' ⟶ T) (Φ : XProdPt 𝓝 τ act T) : XProdPt 𝓝 τ act T'' :=
  ⟨fun α => AttractorPt.baseChange s (Φ.1 α), fun α β => by
    rw [AttractorPt.toPoint_baseChange, AttractorPt.toPoint_baseChange, Φ.2 α β]⟩

section Main

variable [Nonempty A] {J : GrothendieckTopology C}

/-- The step `X^Z → X` of the printed proof of **Theorem 4.1** gives the equality of the values on
overlaps. -/
lemma XProdPt.app_eq {T : C} (hZ : Function.Injective
      (AttractorPt.toPoint : AttractorPt act 𝓝.Z.toAddSubmonoid T → X.obj (op T)))
    (Φ : XProdPt 𝓝 τ act T) {V : C} (s : V ⟶ T) {α β : A}
    (a : τ.obj V ⟶ AZ (𝓝.N α)) (b : τ.obj V ⟶ AZ (𝓝.N β)) (e : a ≫ 𝓝.ι α = b ≫ 𝓝.ι β) :
    (Φ.1 α).app s (ptsT τ _ V a) = (Φ.1 β).app s (ptsT τ _ V b) := by
  by_cases hne : α = β
  · subst hne
    rw [(cancel_mono (𝓝.ι α)).mp e]
  obtain ⟨u, rfl, rfl⟩ := 𝓝.exists_factor_of_overlap hne a b e
  have hE : AttractorPt.ofLE (𝓝.le α) (Φ.1 α) = AttractorPt.ofLE (𝓝.le β) (Φ.1 β) :=
    hZ (by rw [AttractorPt.toPoint_ofLE, AttractorPt.toPoint_ofLE]; exact Φ.2 α β)
  have := congrArg (fun φ => AttractorPt.app φ s (ptsT τ _ V u)) hE
  have h₁ : ptsT τ _ V (u ≫ 𝓝.gpMap α) = APt.restrict (𝓝.le α) (ptsT τ _ V u) := ptsT_map _ u
  have h₂ : ptsT τ _ V (u ≫ 𝓝.gpMap β) = APt.restrict (𝓝.le β) (ptsT τ _ V u) := ptsT_map _ u
  rw [h₁, h₂]
  exact this

variable (hF : Presieve.IsSheaf J X) (hcov : ∀ {T : C} (y : τ.obj T ⟶ 𝓝.AN), 𝓝.coverSieve τ y ∈ J T)
  (hZ : ∀ T : C, Function.Injective
    (AttractorPt.toPoint : AttractorPt act 𝓝.Z.toAddSubmonoid T → X.obj (op T)))

include hF hcov hZ

/-- The gluing of **Proposition 3.3** applied to a compatible family, on the point `y` of `𝔸(𝒩)`. -/
theorem existsUnique_fam {T : C} (Φ : XProdPt 𝓝 τ act T) {T' : C} (t : T' ⟶ T)
    (y : τ.obj T' ⟶ 𝓝.AN) :
    ∃! z : X.obj (op T'), ∀ (α : A) {V : C} (g : V ⟶ T') (a : τ.obj V ⟶ AZ (𝓝.N α)),
      τ.map g ≫ y = a ≫ 𝓝.ι α → X.map g.op z = (Φ.1 α).app (g ≫ t) (ptsT τ _ V a) := by
  obtain ⟨z, hz, huniq⟩ := MagnetFamily.existsUnique_glue (𝓝 := 𝓝) (τ := τ) (F := X) hF y (hcov y)
    (fun α V g a _ => (Φ.1 α).app (g ≫ t) (ptsT τ _ V a))
    (fun α V V' s g a e e' => by
      rw [ptsT_comp, Category.assoc]
      exact (Φ.1 α).naturality s (g ≫ t) _)
    (fun α β V g a b e e' => XProdPt.app_eq (hZ T) Φ _ a b (e.symm.trans e'))
  exact ⟨z, fun α V g a e => hz α g a e, fun z' hz' => huniq z' fun α V g a e => hz' α g a e⟩

/-- The value at `y` of the morphism glued from a compatible family. -/
noncomputable def glueVal {T : C} (Φ : XProdPt 𝓝 τ act T) {T' : C} (t : T' ⟶ T)
    (y : τ.obj T' ⟶ 𝓝.AN) : X.obj (op T') :=
  (existsUnique_fam hF hcov hZ Φ t y).choose

lemma glueVal_spec {T : C} (Φ : XProdPt 𝓝 τ act T) {T' : C} (t : T' ⟶ T)
    (y : τ.obj T' ⟶ 𝓝.AN) (α : A) {V : C} (g : V ⟶ T') (a : τ.obj V ⟶ AZ (𝓝.N α))
    (e : τ.map g ≫ y = a ≫ 𝓝.ι α) :
    X.map g.op (glueVal hF hcov hZ Φ t y) = (Φ.1 α).app (g ≫ t) (ptsT τ _ V a) :=
  (existsUnique_fam hF hcov hZ Φ t y).choose_spec.1 α g a e

lemma glueVal_unique {T : C} (Φ : XProdPt 𝓝 τ act T) {T' : C} (t : T' ⟶ T)
    (y : τ.obj T' ⟶ 𝓝.AN) (z : X.obj (op T'))
    (hz : ∀ (α : A) {V : C} (g : V ⟶ T') (a : τ.obj V ⟶ AZ (𝓝.N α)),
      τ.map g ≫ y = a ≫ 𝓝.ι α → X.map g.op z = (Φ.1 α).app (g ≫ t) (ptsT τ _ V a)) :
    z = glueVal hF hcov hZ Φ t y :=
  (existsUnique_fam hF hcov hZ Φ t y).choose_spec.2 z hz

omit hF hcov hZ in
lemma smulN_specT {T' V : C} (k : APt (τO τ) M (op T')) (y : τ.obj T' ⟶ 𝓝.AN) (g : V ⟶ T') {α : A}
    (a : τ.obj V ⟶ AZ (𝓝.N α)) (e : τ.map g ≫ y = a ≫ 𝓝.ι α) :
    τ.map g ≫ 𝓝.smulN (W := τ.obj T') k y =
      smulA (V := τ.obj V) (APt.res (𝒪 := τO τ) g.op k) a ≫ 𝓝.ι α :=
  𝓝.smulN_spec (W := τ.obj T') k y (τ.map g) a e

lemma glueVal_naturality {T : C} (Φ : XProdPt 𝓝 τ act T) {T' T'' : C} (s : T'' ⟶ T') (t : T' ⟶ T)
    (y : τ.obj T' ⟶ 𝓝.AN) :
    glueVal hF hcov hZ Φ (s ≫ t) (τ.map s ≫ y) = X.map s.op (glueVal hF hcov hZ Φ t y) := by
  refine (glueVal_unique hF hcov hZ Φ _ _ _ ?_).symm
  intro α V g a e
  rw [← Functor.map_comp_apply, ← op_comp,
    glueVal_spec hF hcov hZ Φ t y α (g ≫ s) a (by rw [τ.map_comp, Category.assoc, e]),
    Category.assoc]

lemma glueVal_equivariant {T : C} (Φ : XProdPt 𝓝 τ act T) {T' : C} (t : T' ⟶ T)
    (k : APt (τO τ) M (op T')) (y : τ.obj T' ⟶ 𝓝.AN) :
    glueVal hF hcov hZ Φ t (𝓝.smulN (W := τ.obj T') k y) =
      act.smul k (glueVal hF hcov hZ Φ t y) := by
  refine (hF _ (hcov y)).isSeparatedFor.ext fun V g hg => ?_
  obtain ⟨α, a, e⟩ := hg
  have h1 := smulN_specT (𝓝 := 𝓝) k y g a e
  have e1 := glueVal_spec hF hcov hZ Φ t (𝓝.smulN (W := τ.obj T') k y) α g _ h1
  have e2 := glueVal_spec hF hcov hZ Φ t y α g a e
  have e3 := ptsT_smulA (τ := τ) (P := 𝓝.N α) (APt.res (𝒪 := τO τ) g.op k) a
  rw [act.map_smul]
  refine e1.trans ?_
  rw [e3, (Φ.1 α).equivariant, ← e2]

/-- From a compatible family to a point of `X^𝒩`, by **Proposition 3.3**. -/
noncomputable def XProdPt.toXN {T : C} (Φ : XProdPt 𝓝 τ act T) : XNPt 𝓝 τ act T where
  app t y := glueVal hF hcov hZ Φ t y
  naturality s t y := glueVal_naturality hF hcov hZ Φ s t y
  equivariant t k y := glueVal_equivariant hF hcov hZ Φ t k y

lemma XProdPt.toXN_app_ι {T : C} (Φ : XProdPt 𝓝 τ act T) {T' : C} (t : T' ⟶ T) {α : A}
    (a : τ.obj T' ⟶ AZ (𝓝.N α)) :
    (Φ.toXN hF hcov hZ).app t (a ≫ 𝓝.ι α) = (Φ.1 α).app t (ptsT τ _ T' a) := by
  have := glueVal_spec hF hcov hZ Φ t (a ≫ 𝓝.ι α) α (𝟙 T') a (by simp)
  rw [op_id, Functor.map_id_apply, ] at this
  rw [Category.id_comp] at this
  exact this

omit hF hcov hZ in
/-- From a point of `X^𝒩` to a compatible family: restriction along the `𝔸(N_α) → 𝔸(𝒩)`. -/
noncomputable def XNPt.toProd {T : C} (ψ : XNPt 𝓝 τ act T) : XProdPt 𝓝 τ act T :=
  ⟨fun α =>
    { app := fun {T'} t a => ψ.app t ((ptsT τ _ T').symm a ≫ 𝓝.ι α)
      naturality := fun {T' T''} s t a => by
        rw [← ψ.naturality, ← Category.assoc]
        congr 2
        apply (ptsT τ _ T'').injective
        rw [ptsT_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      equivariant := fun {T'} t k a => by
        rw [← ψ.equivariant, 𝓝.smulN_comp_ι]
        congr 2
        apply (ptsT τ _ T').injective
        rw [ptsT_smulA, Equiv.apply_symm_apply, Equiv.apply_symm_apply] },
    fun α β => by
      have key : ∀ α : A, (ptsT τ (𝓝.N α) T).symm 1 ≫ 𝓝.ι α = unitPt 𝓝 τ T := by
        intro α
        have e : (ptsT τ (𝓝.N α) T).symm 1 =
            (ptsT τ 𝓝.Z.toAddSubmonoid T).symm 1 ≫ 𝓝.gpMap α := by
          apply (ptsT τ _ T).injective
          have h₁ : ptsT τ _ T ((ptsT τ 𝓝.Z.toAddSubmonoid T).symm 1 ≫ 𝓝.gpMap α) =
              APt.restrict (𝓝.le α) (ptsT τ _ T ((ptsT τ 𝓝.Z.toAddSubmonoid T).symm 1)) :=
            ptsT_map _ _
          rw [h₁, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
          rfl
        rw [e, Category.assoc, 𝓝.gpMap_ι, unitPt]
      change ψ.app (𝟙 T) _ = ψ.app (𝟙 T) _
      rw [key α, key β]⟩

omit hF hcov hZ in
lemma XNPt.toPoint_toProd {T : C} (ψ : XNPt 𝓝 τ act T) (α : A) :
    (ψ.toProd.1 α).toPoint = ψ.toPoint := by
  change ψ.app (𝟙 T) _ = ψ.app (𝟙 T) _
  congr 1
  have e : (ptsT τ (𝓝.N α) T).symm 1 =
      (ptsT τ 𝓝.Z.toAddSubmonoid T).symm 1 ≫ 𝓝.gpMap α := by
    apply (ptsT τ _ T).injective
    have h₁ : ptsT τ _ T ((ptsT τ 𝓝.Z.toAddSubmonoid T).symm 1 ≫ 𝓝.gpMap α) =
        APt.restrict (𝓝.le α) (ptsT τ _ T ((ptsT τ 𝓝.Z.toAddSubmonoid T).symm 1)) :=
      ptsT_map _ _
    rw [h₁, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rfl
  rw [e, Category.assoc, 𝓝.gpMap_ι, unitPt]

/-- **Theorem 4.1**, general form: `∏_X X^{N_α} = Hom_{D(M)}(𝔸(𝒩), X)`, for a sheaf `X` on `C` such that
`X^Z → X` is a monomorphism and `𝔸(𝒩)` is locally covered by the `𝔸(N_α)`. -/
noncomputable def thm41Equiv (T : C) : XNPt 𝓝 τ act T ≃ XProdPt 𝓝 τ act T where
  toFun := XNPt.toProd
  invFun Φ := Φ.toXN hF hcov hZ
  left_inv ψ := by
    refine XNPt.ext ?_
    funext T' t y
    refine (glueVal_unique hF hcov hZ ψ.toProd t y _ ?_).symm
    intro α V g a e
    rw [← ψ.naturality, e]
    change _ = ψ.app (g ≫ t) ((ptsT τ _ V).symm (ptsT τ _ V a) ≫ 𝓝.ι α)
    rw [Equiv.symm_apply_apply]
  right_inv Φ := by
    refine Subtype.ext ?_
    funext α
    refine AttractorPt.ext ?_
    funext T' t a
    change (Φ.toXN hF hcov hZ).app t ((ptsT τ _ T').symm a ≫ 𝓝.ι α) = _
    rw [XProdPt.toXN_app_ι, Equiv.apply_symm_apply]

omit hF hcov hZ in
/-- **Theorem 4.1** is natural in `T`. -/
lemma toProd_baseChange {T T'' : C} (s : T'' ⟶ T) (ψ : XNPt 𝓝 τ act T) :
    (ψ.baseChange s).toProd = ψ.toProd.baseChange s := rfl

omit hF hcov hZ in
/-- **Proposition 4.5**, in general: if each `X^{N_α} → X` is a monomorphism, then so is `X^𝒩 → X`,
given the equality of **Theorem 4.1**. -/
lemma toPoint_injective_of_equiv {T : C} (hE : Function.Injective
      (XNPt.toProd : XNPt 𝓝 τ act T → XProdPt 𝓝 τ act T))
    (hN : ∀ α, Function.Injective
      (AttractorPt.toPoint : AttractorPt act (𝓝.N α) T → X.obj (op T))) :
    Function.Injective (XNPt.toPoint : XNPt 𝓝 τ act T → X.obj (op T)) := by
  intro ψ ψ' h
  apply hE
  refine Subtype.ext ?_
  funext α
  apply hN α
  rw [XNPt.toPoint_toProd, XNPt.toPoint_toProd, h]

end Main

end AlgMag.XP

namespace AlgMag.XP

open GB

section Site

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "Sch" => BigFppfOver.toScheme B S hS

variable {M : Type u} [AddCommGroup M] {A : Type u} (𝓝 : MagnetFamily M A) [Nonempty A]

/-- A point of `𝔸(𝒩)` lands Zariski-locally in the `𝔸(N_α)`, on the big fppf site. -/
theorem coverSieve_mem_site {T : BigFppfOver B S hS} (y : (Sch).obj T ⟶ 𝓝.AN) :
    𝓝.coverSieve (Sch) y ∈ BigFppfOver.topology B S hS T := by
  let U : A → ((Sch).obj T).Opens := fun α => y ⁻¹ᵁ (𝓝.ι α).opensRange
  have hC : ∀ α, B.Contains ((U α : ((Sch).obj T).Opens) : Scheme.{u}) := fun α =>
    Scheme.size_lt_of_isOpenImmersion (U α).ι T.left.property
  let V : A → BigFppfOver B S hS := fun α => siteObject B S hS (hC α) ((U α).ι ≫ T.hom.hom)
  let π : ∀ α, V α ⟶ T := fun α => siteHom (U α).ι rfl
  have hmem : Sieve.ofArrows V π ∈ BigFppfOver.topology B S hS T := by
    refine BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS π
      (fun α => inferInstanceAs (IsOpenImmersion (U α).ι)) fun x => ?_
    obtain ⟨α, hα⟩ := 𝓝.exists_mem_range (y x)
    exact ⟨α, ⟨⟨x, hα⟩, rfl⟩⟩
  refine (BigFppfOver.topology B S hS).superset_covering ?_ hmem
  rintro W g ⟨W', a, b, ⟨α⟩, rfl⟩
  obtain ⟨c, hc⟩ := 𝓝.exists_lift_preimage y α
  refine ⟨α, (Sch).map a ≫ c, ?_⟩
  rw [Functor.map_comp, Category.assoc, Category.assoc, ← hc]
  rfl

end Site

end AlgMag.XP

namespace AlgMag.XP

open GB

section SiteMain

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "Sch" => BigFppfOver.toScheme B S hS

variable {M : Type u} [AddCommGroup M] {A : Type u} (𝓝 : MagnetFamily M A)
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (act : AAction (fppfO B S hS) M X)

/-- The step of the printed proof of **Theorem 4.1**: `X^Z → X` is a monomorphism, for a subgroup `Z`.
The printed proof says `X^Z = X^{D(M/Z)}` by [Algebraic Magnetism, Proposition 3.35]; this already
gives the claim for any fppf sheaf `X`, the fixed point functor being a subfunctor of `X`. The further
appeal to [Algebraic Magnetism, Theorem A.1] and the conditions of Theorem 4.1 are not needed. -/
theorem toPoint_injective_gp [AddGroup.FG M] (hF : Presieve.IsSheaf (BigFppfOver.topology B S hS) X)
    (Z : AddSubgroup M) (T : BigFppfOver B S hS) :
    Function.Injective (AttractorPt.toPoint : AttractorPt act Z.toAddSubmonoid T → X.obj (op T)) := by
  intro φ ψ h
  let e := attractorFixedEquivOfCover (act := act) (Z := Z) hF
    (fun {T} a => extSieve_mem (B := B) (S := S) (hS := hS) Z (T := T) a) T
  apply e.symm.injective
  exact Subtype.ext h

variable [AddGroup.FG M] [Nonempty A]

/-- **Theorem 4.1**, for an fppf sheaf `X`: `∏_X X^{N_α} = Hom_{D(M)}(𝔸(𝒩), X)`. -/
noncomputable def thm41OfSheaf (hF : Presieve.IsSheaf (BigFppfOver.topology B S hS) X)
    (T : BigFppfOver B S hS) : XNPt 𝓝 (Sch) act T ≃ XProdPt 𝓝 (Sch) act T :=
  thm41Equiv (τ := Sch) (𝓝 := 𝓝) (act := act) hF (fun y => coverSieve_mem_site 𝓝 y)
    (toPoint_injective_gp act hF 𝓝.Z) T

/-- **Theorem 4.1.** Let `X` be an algebraic space with an action of `D(M)`. Then
`… ×_X X^{N_α} ×_X X^{N_β} ×_X … = Hom_{D(M)}(𝔸(𝒩), X)`, naturally in `T` (`toProd_baseChange`). The map
is restriction along the `𝔸(N_α) → 𝔸(𝒩)`, and it commutes with the maps to `X` (`XNPt.toPoint_toProd`).
The conditions 1 and 2 of the printed statement are not needed; see `toPoint_injective_gp`. -/
noncomputable def thm41 (hX : IsAlgebraicSpace B S hS X) (T : BigFppfOver B S hS) :
    XNPt 𝓝 (Sch) act T ≃ XProdPt 𝓝 (Sch) act T :=
  thm41OfSheaf 𝓝 act ((isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf) T

@[simp] lemma thm41_apply (hX : IsAlgebraicSpace B S hS X) {T : BigFppfOver B S hS}
    (ψ : XNPt 𝓝 (Sch) act T) : thm41 𝓝 act hX T ψ = ψ.toProd := rfl

/-- **Proposition 4.5**: if `X/S` is separated, `X^𝒩 → X` is a monomorphism. The printed induction on
`#A` uses Theorem 4.1 and Corollary 3.30 at each step; finiteness of `A` is not needed when they are
combined at once. -/
theorem prop45 (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    (T : BigFppfOver B S hS) :
    Function.Injective (XNPt.toPoint : XNPt 𝓝 (Sch) act T → X.obj (op T)) := by
  have : AddMonoid.FG M := AddGroup.fg_iff_addMonoid_fg.mp inferInstance
  exact toPoint_injective_of_equiv (thm41 𝓝 act hX T).injective
    fun α => attractor_toPoint_injective_sep hX hsep (𝓝.N α) T

end SiteMain

section OverMain

variable {S : Scheme.{u}} {M : Type u} [AddCommGroup M] {A : Type u} (𝓝 : MagnetFamily M A)

/-- A point of `𝔸(𝒩)` lands Zariski-locally in the `𝔸(N_α)`, on schemes over `S`. -/
theorem coverSieve_mem_over [Nonempty A] {T : Over S} (y : (Over.forget S).obj T ⟶ 𝓝.AN) :
    𝓝.coverSieve (Over.forget S) y ∈ Scheme.zariskiTopology.over S T := by
  change Sieve.overEquiv T _ ∈ Scheme.zariskiTopology T.left
  refine Scheme.zariskiTopology.superset_covering ?_ (𝓝.coverSieve_mem_zariski (W := T.left) y)
  rintro V g ⟨α, a, e⟩
  rw [Sieve.overEquiv_iff]
  exact ⟨α, a, e⟩

variable {X : Over S} [IsAffineHom X.hom] (act : AAction (overO S) M (yoneda.obj X))

/-- **Theorem 4.1**, for `X` affine over `S`, on all schemes over `S`. -/
noncomputable def thm41Over [Nonempty A] (T : Over S) :
    XNPt 𝓝 (Over.forget S) act T ≃ XProdPt 𝓝 (Over.forget S) act T :=
  thm41Equiv (τ := Over.forget S) (𝓝 := 𝓝) (act := act) (isSheaf_yoneda_over X)
    (fun y => coverSieve_mem_over 𝓝 y) (fun _ => toPoint_injective_global) T

end OverMain

end AlgMag.XP

#print axioms AlgMag.XP.MagnetFamily.prop31
#print axioms AlgMag.XP.MagnetFamily.prop33
#print axioms AlgMag.XP.thm41
#print axioms AlgMag.XP.thm41Over
#print axioms AlgMag.XP.prop45
