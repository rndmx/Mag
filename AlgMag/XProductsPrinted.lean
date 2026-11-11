/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.XProductsRep
import AlgMag.AppendixA3

/-!
# X-products of attractors: the printed versions of Theorem 4.1, Proposition 4.3 (2), Proposition 4.5

Mayeux, *Algebraic magnetism: X-products of attractors via F₁-geometry*, Semigroup Forum,
doi 10.1007/s00233-026-10695-7, §4. The stronger statements of `AlgMag.XProductsThm` and
`AlgMag.XProductsRep` stay as remarks; here the printed hypotheses and the printed proofs.

## The printed proof of Theorem 4.1, step by step

* `XProdPt`, the fibre product over `X`, and `prodCond_g_iff`: "`X^M = X`", the condition `f_α g_α = f_β g_β`.
* `prodCond_hk_iff`: `f_α g_α = f_α h_α k`.
* `toPoint_injective_cond1`, `toPoint_injective_cond2`: "`X^Z → X` is a monomorphism", in the two cases: by
  Proposition 3.35 and Theorem A.1, and by Corollary 3.30.
* `prodEquivZ`: removing `k`.
* `prop33T`: "Proposition 3.3 implies": compatible families on the `𝔸(N_α)_T` glue.
* `thm41Printed`: **Theorem 4.1**.

## What the step "Proposition 3.3 implies" needs

`prop33` is a statement about schemes with a `D(M)`-action over `ℤ`, whereas the proof applies it to `𝔸(𝒩)_T`
and to the algebraic space `X_T`, over `T`. The statement used is `prop33T`, whose hypotheses are:

1. `X` is a sheaf (`hF`): morphisms to `X_T` glue. A scheme target is not needed, and the universal property
   of the colimit in schemes is not what is used.
2. `𝔸(𝒩)_T` is covered by the `𝔸(N_α)_T` (`hcov`): this is base change of the open immersions of Proposition
   3.1. It is `coverSieve_mem_site`.
3. The intersections in `𝔸(𝒩)_T` of the `𝔸(N_α)_T` are `D(Z)_T`: this is `exists_factor_of_overlap`, valid
   after base change since it is stated for all test schemes.
4. A `D(M)_T`-equivariant `T`-morphism `𝔸(𝒩)_T → X_T` is given by its values on `T'`-points for `T' → T`
   (`XNPt`); equivariance is checked on the cover.

## Main results

* `AlgMag.XP.Thm41Cond`, `AlgMag.XP.thm41Printed`: **Theorem 4.1**; the literal hypotheses over `S = Spec ℤ`
  are in `AlgMag.XProductsPrintedLfp`.
* `AlgMag.XP.prop43_ii_printed`: **Proposition 4.3 (2)**.
* `AlgMag.XP.prop45Printed`: **Proposition 4.5**, by induction on `#A`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

set_option linter.unusedSectionVars false

namespace AlgMag.XP

open GB

section Generic

variable {M : Type u} [AddCommGroup M] {A : Type u} {𝓝 : MagnetFamily M A}
variable {C : Type*} [Category.{v} C] {τ : C ⥤ Scheme.{u}}
variable {X : Cᵒᵖ ⥤ Type u} {act : AAction (τO τ) M X}

/-- "`X^M = X`" in the printed proof of **Theorem 4.1**: the fibre product over `X` is the fibre product
over `X^M`, whose condition is `f_α ∘ g_α = f_β ∘ g_β`. -/
theorem prodCond_g_iff {T : C} {α β : A} (φ : AttractorPt act (𝓝.N α) T)
    (χ : AttractorPt act (𝓝.N β) T) :
    φ.toPoint = χ.toPoint ↔
      AttractorPt.ofLE (le_top : 𝓝.N α ≤ ⊤) φ = AttractorPt.ofLE (le_top : 𝓝.N β ≤ ⊤) χ := by
  constructor
  · intro h
    apply (attractorTopEquiv act T).injective
    exact h
  · intro h
    exact congrArg AttractorPt.toPoint h

/-- `g_α = h_α ∘ k` in the printed proof of **Theorem 4.1**. -/
theorem prodCond_hk_iff {T : C} {α : A} (φ : AttractorPt act (𝓝.N α) T) :
    AttractorPt.ofLE (le_top : 𝓝.N α ≤ ⊤) φ =
      AttractorPt.ofLE (le_top : 𝓝.Z.toAddSubmonoid ≤ ⊤) (AttractorPt.ofLE (𝓝.le α) φ) :=
  rfl

variable (𝓝 τ act) in
/-- The set `{{f_α} | f_α ∘ h_α = f_β ∘ h_β}` of the printed proof of **Theorem 4.1**. -/
def XProdZPt (T : C) : Type _ :=
  { Φ : ∀ α, AttractorPt act (𝓝.N α) T //
    ∀ α β, AttractorPt.ofLE (𝓝.le α) (Φ α) = AttractorPt.ofLE (𝓝.le β) (Φ β) }

/-- The step of the printed proof of **Theorem 4.1** removing `k`: it is enough that `X^Z → X` is a
monomorphism. -/
def prodEquivZ {T : C} (hZ : Function.Injective
      (AttractorPt.toPoint : AttractorPt act 𝓝.Z.toAddSubmonoid T → X.obj (op T))) :
    XProdZPt 𝓝 τ act T ≃ XProdPt 𝓝 τ act T where
  toFun Φ := ⟨Φ.1, fun α β => congrArg AttractorPt.toPoint (Φ.2 α β)⟩
  invFun Φ := ⟨Φ.1, fun α β => hZ (by
    rw [AttractorPt.toPoint_ofLE, AttractorPt.toPoint_ofLE]; exact Φ.2 α β)⟩
  left_inv _ := rfl
  right_inv _ := rfl

section Glue

variable [Nonempty A] {J : GrothendieckTopology C}

lemma XProdZPt.app_eq {T : C} (Φ : XProdZPt 𝓝 τ act T) {V : C} (s : V ⟶ T) {α β : A}
    (a : τ.obj V ⟶ AZ (𝓝.N α)) (b : τ.obj V ⟶ AZ (𝓝.N β)) (e : a ≫ 𝓝.ι α = b ≫ 𝓝.ι β) :
    (Φ.1 α).app s (ptsT τ _ V a) = (Φ.1 β).app s (ptsT τ _ V b) := by
  by_cases hne : α = β
  · subst hne
    rw [(cancel_mono (𝓝.ι α)).mp e]
  obtain ⟨u, rfl, rfl⟩ := 𝓝.exists_factor_of_overlap hne a b e
  have := congrArg (fun φ => AttractorPt.app φ s (ptsT τ _ V u)) (Φ.2 α β)
  have h₁ : ptsT τ _ V (u ≫ 𝓝.gpMap α) = APt.restrict (𝓝.le α) (ptsT τ _ V u) := ptsT_map _ u
  have h₂ : ptsT τ _ V (u ≫ 𝓝.gpMap β) = APt.restrict (𝓝.le β) (ptsT τ _ V u) := ptsT_map _ u
  rw [h₁, h₂]
  exact this

variable (hF : Presieve.IsSheaf J X) (hcov : ∀ {T : C} (y : τ.obj T ⟶ 𝓝.AN), 𝓝.coverSieve τ y ∈ J T)

include hF hcov

theorem existsUnique_famZ {T : C} (Φ : XProdZPt 𝓝 τ act T) {T' : C} (t : T' ⟶ T)
    (y : τ.obj T' ⟶ 𝓝.AN) :
    ∃! z : X.obj (op T'), ∀ (α : A) {V : C} (g : V ⟶ T') (a : τ.obj V ⟶ AZ (𝓝.N α)),
      τ.map g ≫ y = a ≫ 𝓝.ι α → X.map g.op z = (Φ.1 α).app (g ≫ t) (ptsT τ _ V a) := by
  obtain ⟨z, hz, huniq⟩ := MagnetFamily.existsUnique_glue (𝓝 := 𝓝) (τ := τ) (F := X) hF y (hcov y)
    (fun α V g a _ => (Φ.1 α).app (g ≫ t) (ptsT τ _ V a))
    (fun α V V' s g a e e' => by
      rw [ptsT_comp, Category.assoc]
      exact (Φ.1 α).naturality s (g ≫ t) _)
    (fun α β V g a b e e' => Φ.app_eq _ a b (e.symm.trans e'))
  exact ⟨z, fun α V g a e => hz α g a e, fun z' hz' => huniq z' fun α V g a e => hz' α g a e⟩

/-- The value at `y` of the morphism glued from a family compatible on `D(Z)`. -/
noncomputable def glueValZ {T : C} (Φ : XProdZPt 𝓝 τ act T) {T' : C} (t : T' ⟶ T)
    (y : τ.obj T' ⟶ 𝓝.AN) : X.obj (op T') :=
  (existsUnique_famZ hF hcov Φ t y).choose

lemma glueValZ_spec {T : C} (Φ : XProdZPt 𝓝 τ act T) {T' : C} (t : T' ⟶ T)
    (y : τ.obj T' ⟶ 𝓝.AN) (α : A) {V : C} (g : V ⟶ T') (a : τ.obj V ⟶ AZ (𝓝.N α))
    (e : τ.map g ≫ y = a ≫ 𝓝.ι α) :
    X.map g.op (glueValZ hF hcov Φ t y) = (Φ.1 α).app (g ≫ t) (ptsT τ _ V a) :=
  (existsUnique_famZ hF hcov Φ t y).choose_spec.1 α g a e

lemma glueValZ_unique {T : C} (Φ : XProdZPt 𝓝 τ act T) {T' : C} (t : T' ⟶ T)
    (y : τ.obj T' ⟶ 𝓝.AN) (z : X.obj (op T'))
    (hz : ∀ (α : A) {V : C} (g : V ⟶ T') (a : τ.obj V ⟶ AZ (𝓝.N α)),
      τ.map g ≫ y = a ≫ 𝓝.ι α → X.map g.op z = (Φ.1 α).app (g ≫ t) (ptsT τ _ V a)) :
    z = glueValZ hF hcov Φ t y :=
  (existsUnique_famZ hF hcov Φ t y).choose_spec.2 z hz

/-- From a family compatible on `D(Z)` to a point of `X^𝒩`: the gluing and the equivariance of the proof of
**Proposition 3.3**, over `T`, for a sheaf `X`. -/
noncomputable def XProdZPt.toXN {T : C} (Φ : XProdZPt 𝓝 τ act T) : XNPt 𝓝 τ act T where
  app t y := glueValZ hF hcov Φ t y
  naturality s t y := by
    refine (glueValZ_unique hF hcov Φ _ _ _ ?_).symm
    intro α V g a e
    rw [← Functor.map_comp_apply, ← op_comp,
      glueValZ_spec hF hcov Φ t y α (g ≫ s) a (by rw [τ.map_comp, Category.assoc, e]),
      Category.assoc]
  equivariant {T'} t k y := by
    refine (hF _ (hcov y)).isSeparatedFor.ext fun V g hg => ?_
    obtain ⟨α, a, e⟩ := hg
    have h1 := smulN_specT (𝓝 := 𝓝) k y g a e
    have e1 := glueValZ_spec hF hcov Φ t (𝓝.smulN (W := τ.obj T') k y) α g _ h1
    have e2 := glueValZ_spec hF hcov Φ t y α g a e
    have e3 := ptsT_smulA (τ := τ) (P := 𝓝.N α) (APt.res (𝒪 := τO τ) g.op k) a
    rw [act.map_smul]
    refine e1.trans ?_
    rw [e3, (Φ.1 α).equivariant, ← e2]

/-- **Proposition 3.3**, in the form used by the printed proof of **Theorem 4.1**, applied to `𝔸(𝒩)_T` and the
space `X_T`: `{{f_α} | f_α ∘ h_α = f_β ∘ h_β} = Hom_{D(M)_T}(𝔸(𝒩)_T, X_T)`, for `X` a sheaf for a topology for
which `𝔸(𝒩)` is locally covered by the `𝔸(N_α)`. See the header of this file. -/
noncomputable def prop33T (T : C) : XNPt 𝓝 τ act T ≃ XProdZPt 𝓝 τ act T where
  toFun ψ := ⟨ψ.toProd.1, fun α β => by
    refine AttractorPt.ext ?_
    funext T' t a
    let u := (ptsT τ 𝓝.Z.toAddSubmonoid T').symm a
    have hu : ∀ γ, APt.restrict (𝓝.le γ) a = ptsT τ _ T' (u ≫ 𝓝.gpMap γ) := fun γ => by
      have h := ptsT_map (τ := τ) (𝓝.le γ) u
      rw [Equiv.apply_symm_apply] at h
      exact h.symm
    change (ψ.toProd.1 α).app t (APt.restrict (𝓝.le α) a) =
      (ψ.toProd.1 β).app t (APt.restrict (𝓝.le β) a)
    rw [hu α, hu β]
    change ψ.app t ((ptsT τ _ T').symm (ptsT τ _ T' (u ≫ 𝓝.gpMap α)) ≫ 𝓝.ι α) =
      ψ.app t ((ptsT τ _ T').symm (ptsT τ _ T' (u ≫ 𝓝.gpMap β)) ≫ 𝓝.ι β)
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, Category.assoc, Category.assoc,
      𝓝.gpMap_ι, 𝓝.gpMap_ι]⟩
  invFun Φ := Φ.toXN hF hcov
  left_inv ψ := by
    refine XNPt.ext ?_
    funext T' t y
    refine (glueValZ_unique hF hcov _ t y _ ?_).symm
    intro α V g a e
    rw [← ψ.naturality, e]
    change _ = ψ.app (g ≫ t) ((ptsT τ _ V).symm (ptsT τ _ V a) ≫ 𝓝.ι α)
    rw [Equiv.symm_apply_apply]
  right_inv Φ := by
    refine Subtype.ext ?_
    funext α
    refine AttractorPt.ext ?_
    funext T' t a
    change (Φ.toXN hF hcov).app t ((ptsT τ _ T').symm a ≫ 𝓝.ι α) = _
    have h := glueValZ_spec hF hcov Φ t ((ptsT τ _ T').symm a ≫ 𝓝.ι α) α (𝟙 T') ((ptsT τ _ T').symm a)
      (by simp)
    rw [op_id, Functor.map_id_apply, Category.id_comp, Equiv.apply_symm_apply] at h
    exact h

end Glue

end Generic

section Site

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "Sch" => BigFppfOver.toScheme B S hS

variable {M : Type u} [AddCommGroup M] [AddGroup.FG M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (act : AAction (fppfO B S hS) M X)

variable (X) in
/-- The conditions of **Theorem 4.1**, for the subgroup `Z`:
1. `S` is locally noetherian, the charts of `X` are of finite type over `S` and `D(M/Z)` has connected fibres, or
2. `X` is separated.
Condition 1 is what the case (i) of [Algebraic Magnetism, Theorem A.1] uses. The printed condition, over
`S = Spec ℤ`, `X` quasi-separated and locally of finite presentation, implies it: `thm41PrintedZ` in
`AlgMag.XProductsPrintedLfp`. -/
def Thm41Cond (Z : AddSubgroup M) : Prop :=
  (IsLocallyNoetherian S ∧ ChartsOfFiniteType X ∧ AppR.ConnectedFibres (M ⧸ Z) S) ∨ IsSeparatedOver X

/-- The first case of the step of the printed proof of **Theorem 4.1**: `X^Z = X^{D(M/Z)}` by [Algebraic
Magnetism, Proposition 3.35], and `X^{D(M/Z)} → X` is a closed immersion by [Algebraic Magnetism, Theorem
A.1]. So `X^Z → X` is a monomorphism. -/
theorem toPoint_injective_cond1 (hX : IsAlgebraicSpace B S hS X) [IsLocallyNoetherian S]
    (hC : ChartsOfFiniteType X) (Z : AddSubgroup M)
    (hc : AppR.ConnectedFibres (M ⧸ Z) S) (T : BigFppfOver B S hS) :
    Space.IsClosedImmersion B S hS (fixedPoints (quotientAction act Z)).ι ∧
      Function.Injective (AttractorPt.toPoint : AttractorPt act Z.toAddSubmonoid T → X.obj (op T)) := by
  refine ⟨AppA3.thmA1_closed hX hC _
    (AppR.torsionResidue_of_connected _ _ hc), ?_⟩
  intro φ ψ h
  let e := attractorFixedEquivOfCover (act := act) (Z := Z)
    ((isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf)
    (fun {T} a => extSieve_mem (B := B) (S := S) (hS := hS) Z (T := T) a) T
  apply e.symm.injective
  exact Subtype.ext h

/-- The second case of the step of the printed proof of **Theorem 4.1**: [Algebraic Magnetism, Corollary
3.30]. -/
theorem toPoint_injective_cond2 (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    (Z : AddSubgroup M) (T : BigFppfOver B S hS) :
    Function.Injective (AttractorPt.toPoint : AttractorPt act Z.toAddSubmonoid T → X.obj (op T)) :=
  have : AddMonoid.FG M := AddGroup.fg_iff_addMonoid_fg.mp inferInstance
  attractor_toPoint_injective_sep hX hsep _ T

/-- The step of the printed proof of **Theorem 4.1**: `X^Z → X` is a monomorphism. -/
theorem toPoint_injective_of_cond (hX : IsAlgebraicSpace B S hS X) {Z : AddSubgroup M}
    (h : Thm41Cond (hS := hS) X Z) (T : BigFppfOver B S hS) :
    Function.Injective (AttractorPt.toPoint : AttractorPt act Z.toAddSubmonoid T → X.obj (op T)) := by
  rcases h with ⟨hN, hC, hc⟩ | hsep
  · exact (toPoint_injective_cond1 act hX hC Z hc T).2
  · exact toPoint_injective_cond2 act hX hsep Z T

lemma Thm41Cond.of_sep {Z : AddSubgroup M} (h : IsSeparatedOver X) :
    Thm41Cond (hS := hS) X Z :=
  Or.inr h

variable {A : Type u} (𝓝 : MagnetFamily M A) [Nonempty A]

/-- **Theorem 4.1**, as printed: `X` an algebraic space with an action of `D(M)` satisfying condition 1 or 2.
Then `… ×_X X^{N_α} ×_X X^{N_β} ×_X … = Hom_{D(M)}(𝔸(𝒩), X)`; the proof is the printed chain. -/
noncomputable def thm41Printed (hX : IsAlgebraicSpace B S hS X) (h : Thm41Cond (hS := hS) X 𝓝.Z)
    (T : BigFppfOver B S hS) : XNPt 𝓝 (Sch) act T ≃ XProdPt 𝓝 (Sch) act T :=
  (prop33T (τ := Sch) (𝓝 := 𝓝) (act := act) ((isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf)
    (fun y => coverSieve_mem_site 𝓝 y) T).trans (prodEquivZ (toPoint_injective_of_cond act hX h T))

/-- The bijection of **Theorem 4.1** is restriction along the `𝔸(N_α) → 𝔸(𝒩)`. -/
@[simp] lemma thm41Printed_apply (hX : IsAlgebraicSpace B S hS X) (h : Thm41Cond (hS := hS) X 𝓝.Z)
    {T : BigFppfOver B S hS} (ψ : XNPt 𝓝 (Sch) act T) :
    thm41Printed act 𝓝 hX h T ψ = ψ.toProd := rfl

/-- **Proposition 4.3 (2)**, as printed: if `A` is finite, each `X^{N_α}` is representable, and one of the
conditions (a), (b) holds, then `X^𝒩` is representable by an algebraic space. The proof: `A` is finite, and
Theorem 4.1. -/
theorem prop43_ii_printed [Finite A] (Z : A → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (r : ∀ α, RepresentsAttractor act (𝓝.N α) (Z α)) (hX : IsAlgebraicSpace B S hS X)
    (hZ : ∀ α, IsAlgebraicSpace B S hS (Z α)) (h : Thm41Cond (hS := hS) X 𝓝.Z) :
    ∃ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS Y ∧
      Nonempty (RepresentsXN 𝓝 (Sch) act Y) := by
  classical
  have := Fintype.ofFinite A
  obtain ⟨Y, hY, ρ, e, hnat, hρ⟩ := exists_rep_finset 𝓝 act Z r hX hZ Finset.univ
  obtain ⟨α₀⟩ := ‹Nonempty A›
  let f : ∀ T, FP 𝓝 act Finset.univ T ≃ XProdPt 𝓝 (Sch) act T := fun T =>
    { toFun := fun p => ⟨fun α => p.1.2 α (Finset.mem_univ α), fun α β => (p.2 α _).trans (p.2 β _).symm⟩
      invFun := fun Φ => ⟨((Φ.1 α₀).toPoint, fun α _ => Φ.1 α), fun α _ => Φ.2 α _⟩
      left_inv := fun p => FP.ext' (p.2 _ _) fun α h => rfl
      right_inv := fun Φ => rfl }
  let E := thm41Printed act 𝓝 hX h
  refine ⟨Y, hY, ⟨⟨fun T => (e T).trans ((f T).trans (E T).symm), ?_⟩⟩⟩
  intro T T' s y
  apply (E T').injective
  change (E T') ((E T').symm (f T' (e T' (Y.map s.op y)))) =
    (XNPt.baseChange s ((E T).symm (f T (e T y)))).toProd
  rw [Equiv.apply_symm_apply]
  refine Eq.trans ?_ (toProd_baseChange (act := act) s _).symm
  change _ = XProdPt.baseChange s ((E T) ((E T).symm (f T (e T y))))
  rw [Equiv.apply_symm_apply, hnat]
  rfl

end Site

section Sub

variable {M : Type u} [AddCommGroup M]

/-- The subfamily `𝒩' = {N_α}_{α ∈ A'}`, used in the induction of Proposition 4.5. -/
def MagnetFamily.sub {A : Type u} (𝓝 : MagnetFamily M A) (p : A → Prop) :
    MagnetFamily M {a // p a} where
  N a := 𝓝.N a.1
  Z := 𝓝.Z
  fg a := 𝓝.fg a.1
  gp a := 𝓝.gp a.1

/-- The projection of the fibre product over `A` to the fibre product over a subset. -/
def XProdPt.sub {A : Type u} {𝓝 : MagnetFamily M A} {C : Type*} [Category.{v} C] {τ : C ⥤ Scheme.{u}}
    {X : Cᵒᵖ ⥤ Type u} {act : AAction (τO τ) M X} {T : C} (Φ : XProdPt 𝓝 τ act T) (p : A → Prop) :
    XProdPt (𝓝.sub p) τ act T :=
  ⟨fun a => Φ.1 a.1, fun a a' => Φ.2 a.1 a'.1⟩

end Sub

section Prop45

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "Sch" => BigFppfOver.toScheme B S hS

variable {M : Type u} [AddCommGroup M] [AddGroup.FG M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (act : AAction (fppfO B S hS) M X)

theorem prop45_aux (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X) (n : ℕ) :
    ∀ (A : Type u) [Fintype A] [Nonempty A] (𝓝 : MagnetFamily M A), Fintype.card A = n + 1 →
      ∀ T : BigFppfOver B S hS,
        Function.Injective (XNPt.toPoint : XNPt 𝓝 (Sch) act T → X.obj (op T)) := by
  classical
  have : AddMonoid.FG M := AddGroup.fg_iff_addMonoid_fg.mp inferInstance
  have hN : ∀ (N : AddSubmonoid M) (T : BigFppfOver B S hS), Function.Injective
      (AttractorPt.toPoint : AttractorPt act N T → X.obj (op T)) := fun N T =>
    attractor_toPoint_injective_sep hX hsep N T
  induction n with
  | zero =>
    -- `#A = 1`: [Algebraic Magnetism, Corollary 3.30]
    intro A _ _ 𝓝 hc T ψ ψ' h
    apply (thm41Printed act 𝓝 hX (Thm41Cond.of_sep hsep) T).injective
    refine Subtype.ext (funext fun α => hN _ T ?_)
    exact (XNPt.toPoint_toProd ψ α).trans (h.trans (XNPt.toPoint_toProd ψ' α).symm)
  | succ n ih =>
    intro A _ _ 𝓝 hc T ψ ψ' h
    obtain ⟨β⟩ := ‹Nonempty A›
    -- `A = A' ⊔ {β}`
    let p : A → Prop := fun a => a ≠ β
    have hcard : Fintype.card {a // p a} = n + 1 := by
      rw [Fintype.card_subtype_compl, hc]
      simp
    have hne : Nonempty {a // p a} := Fintype.card_pos_iff.mp (by omega)
    -- the projection `X^𝒩 = X^{𝒩'} ×_X X^{N_β} → X^{𝒩'}`
    let E' := thm41Printed act (𝓝.sub p) hX (Thm41Cond.of_sep hsep) T
    let res : XNPt 𝓝 (Sch) act T → XNPt (𝓝.sub p) (Sch) act T := fun χ => E'.symm (χ.toProd.sub p)
    have hres : ∀ χ, (res χ).toProd = χ.toProd.sub p := fun χ => E'.apply_symm_apply _
    have htp : ∀ χ, (res χ).toPoint = χ.toPoint := fun χ => by
      let a := hne.some
      refine (XNPt.toPoint_toProd (res χ) a).symm.trans ?_
      rw [hres]
      exact XNPt.toPoint_toProd χ a.1
    -- by induction `X^{𝒩'} → X` is a monomorphism; [Stacks, Tag 042P] and [Stacks, Tag 042O], on points
    have hr : res ψ = res ψ' := ih {a // p a} (𝓝.sub p) hcard T ((htp ψ).trans (h.trans (htp ψ').symm))
    apply (thm41Printed act 𝓝 hX (Thm41Cond.of_sep hsep) T).injective
    refine Subtype.ext (funext fun α => ?_)
    by_cases hα : α = β
    · subst hα
      apply hN
      exact (XNPt.toPoint_toProd ψ α).trans (h.trans (XNPt.toPoint_toProd ψ' α).symm)
    · have e := (hres ψ).symm.trans ((congrArg XNPt.toProd hr).trans (hres ψ'))
      exact congrFun (congrArg Subtype.val e) ⟨α, hα⟩

/-- **Proposition 4.5**, as printed: if `A` is finite and `X/S` is separated, `X^𝒩 → X` is a monomorphism. The
proof is the printed induction on `#A`. -/
theorem prop45Printed {A : Type u} [Finite A] [Nonempty A] (𝓝 : MagnetFamily M A)
    (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X) (T : BigFppfOver B S hS) :
    Function.Injective (XNPt.toPoint : XNPt 𝓝 (Sch) act T → X.obj (op T)) := by
  have := Fintype.ofFinite A
  have hpos : 0 < Fintype.card A := Fintype.card_pos
  exact prop45_aux act hX hsep (Fintype.card A - 1) A 𝓝 (by omega) T

end Prop45

end AlgMag.XP

#print axioms AlgMag.XP.prodCond_g_iff
#print axioms AlgMag.XP.prop33T
#print axioms AlgMag.XP.toPoint_injective_cond1
#print axioms AlgMag.XP.thm41Printed
#print axioms AlgMag.XP.prop43_ii_printed
#print axioms AlgMag.XP.prop45Printed
