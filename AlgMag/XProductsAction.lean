/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.XProductsGlue
import AlgMag.Sec6FPR
import AlgMag.Sec3Functorial

/-!
# X-products of attractors: the action of `D(M)` on `𝔸(𝒩)` (Proposition 3.3)

Mayeux, *Algebraic magnetism: X-products of attractors via F₁-geometry*, §3.

An action of `D(M)` on a scheme is written as an action on its functor of points, an
`AAction Scheme.Γ M (yoneda.obj X)`; by Yoneda this is a morphism `D(M) × X → X`.

## Main results

* `AlgMag.XP.MagnetFamily.existsUnique_glue`: Zariski gluing of a morphism out of `𝔸(𝒩)`, on points.
* `AlgMag.XP.MagnetFamily.actAN`: the action of `D(M)` on `𝔸(𝒩)` of the proof of Proposition 3.3.
* `AlgMag.XP.DScheme`: the category of schemes with a `D(M)`-action.
* `AlgMag.XP.MagnetFamily.prop33`: **Proposition 3.3**.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v w

set_option linter.unusedSectionVars false

namespace AlgMag.XP

open GB

variable {M : Type u} [AddCommGroup M] {A : Type u} (𝓝 : MagnetFamily M A)

namespace MagnetFamily

section Glue

variable {C : Type*} [Category.{v} C] (τ : C ⥤ Scheme.{u})

/-- The sieve on `T` of the morphisms along which a point `y` of `𝔸(𝒩)` lands in some `𝔸(N_α)`. -/
def coverSieve {T : C} (y : τ.obj T ⟶ 𝓝.AN) : Sieve T where
  arrows V g := ∃ α, ∃ a : τ.obj V ⟶ AZ (𝓝.N α), τ.map g ≫ y = a ≫ 𝓝.ι α
  downward_closed := by
    rintro V W g ⟨α, a, e⟩ s
    exact ⟨α, τ.map s ≫ a, by simp [e]⟩

variable {𝓝 τ} {J : GrothendieckTopology C} {F : Cᵒᵖ ⥤ Type w}

/-- The gluing behind the proofs of **Proposition 3.3** and **Theorem 4.1**: a point `y` of `𝔸(𝒩)` over
`T` is covered by points of the `𝔸(N_α)`, and values on these which are natural and agree on overlaps
glue to a unique value at `y`, for a sheaf `F`. -/
theorem existsUnique_glue (hF : Presieve.IsSheaf J F) {T : C} (y : τ.obj T ⟶ 𝓝.AN)
    (hy : 𝓝.coverSieve τ y ∈ J T)
    (v : ∀ (α : A) {V : C} (g : V ⟶ T) (a : τ.obj V ⟶ AZ (𝓝.N α)),
      τ.map g ≫ y = a ≫ 𝓝.ι α → F.obj (op V))
    (hnat : ∀ (α : A) {V V' : C} (s : V' ⟶ V) (g : V ⟶ T) (a : τ.obj V ⟶ AZ (𝓝.N α)) (e)
      (e' : τ.map (s ≫ g) ≫ y = (τ.map s ≫ a) ≫ 𝓝.ι α),
      v α (s ≫ g) (τ.map s ≫ a) e' = F.map s.op (v α g a e))
    (hwell : ∀ (α β : A) {V : C} (g : V ⟶ T) (a : τ.obj V ⟶ AZ (𝓝.N α))
      (b : τ.obj V ⟶ AZ (𝓝.N β)) (e) (e'), v α g a e = v β g b e') :
    ∃! z : F.obj (op T), ∀ (α : A) {V : C} (g : V ⟶ T) (a : τ.obj V ⟶ AZ (𝓝.N α)) (e),
      F.map g.op z = v α g a e := by
  have sh := hF _ hy
  let x : Presieve.FamilyOfElements F (𝓝.coverSieve τ y).arrows := fun V g hg =>
    v hg.choose g hg.choose_spec.choose hg.choose_spec.choose_spec
  have hcongr : ∀ (α : A) {V : C} {g g' : V ⟶ T} (_ : g = g') (a : τ.obj V ⟶ AZ (𝓝.N α)) (e) (e'),
      v α g a e = v α g' a e' := by
    intro α V g g' h a e e'
    subst h
    rfl
  have hc : x.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ comm
    have e₁ := h₁.choose_spec.choose_spec
    have e₂ := h₂.choose_spec.choose_spec
    change F.map g₁.op (v _ f₁ _ e₁) = F.map g₂.op (v _ f₂ _ e₂)
    have k₁ : τ.map (g₁ ≫ f₁) ≫ y = (τ.map g₁ ≫ h₁.choose_spec.choose) ≫ 𝓝.ι _ := by
      rw [Category.assoc, ← e₁, τ.map_comp, Category.assoc]
    have k₂ : τ.map (g₂ ≫ f₂) ≫ y = (τ.map g₂ ≫ h₂.choose_spec.choose) ≫ 𝓝.ι _ := by
      rw [Category.assoc, ← e₂, τ.map_comp, Category.assoc]
    rw [← hnat _ g₁ f₁ _ e₁ k₁, ← hnat _ g₂ f₂ _ e₂ k₂]
    have k₂' : τ.map (g₁ ≫ f₁) ≫ y = (τ.map g₂ ≫ h₂.choose_spec.choose) ≫ 𝓝.ι _ := by
      rw [comm]; exact k₂
    exact (hwell _ _ _ _ _ k₁ k₂').trans (hcongr _ comm _ _ _)
  refine ⟨sh.amalgamate x hc, ?_, ?_⟩
  · intro α V g a e
    have hg : (𝓝.coverSieve τ y).arrows g := ⟨α, a, e⟩
    exact (sh.valid_glue hc g hg).trans (hwell _ _ _ _ _ _ _)
  · intro z hz
    refine sh.isSeparatedFor.ext fun V g hg => ?_
    rw [show F.map g.op (sh.amalgamate x hc) = x g hg from sh.valid_glue hc g hg]
    exact hz _ g _ hg.choose_spec.choose_spec

end Glue

section Zariski

variable [Nonempty A]

/-- Over the opens `y⁻¹(𝔸(N_α))`, a point `y` of `𝔸(𝒩)` lands in `𝔸(N_α)`. -/
lemma exists_lift_preimage {W : Scheme.{u}} (y : W ⟶ 𝓝.AN) (α : A) :
    ∃ a : (y ⁻¹ᵁ (𝓝.ι α).opensRange).toScheme ⟶ AZ (𝓝.N α),
      (y ⁻¹ᵁ (𝓝.ι α).opensRange).ι ≫ y = a ≫ 𝓝.ι α := by
  have hr : Set.range ((y ⁻¹ᵁ (𝓝.ι α).opensRange).ι ≫ y) ⊆ Set.range (𝓝.ι α) := by
    rintro _ ⟨w, rfl⟩
    exact w.2
  exact ⟨IsOpenImmersion.lift (𝓝.ι α) _ hr, (IsOpenImmersion.lift_fac _ _ _).symm⟩

/-- A point of `𝔸(𝒩)` lands Zariski-locally in the `𝔸(N_α)`. -/
theorem coverSieve_mem_zariski {W : Scheme.{u}} (y : (𝟭 Scheme.{u}).obj W ⟶ 𝓝.AN) :
    𝓝.coverSieve (𝟭 Scheme.{u}) y ∈ Scheme.zariskiTopology W := by
  let U : A → W.Opens := fun α => y ⁻¹ᵁ (𝓝.ι α).opensRange
  have hU : ⨆ α, U α = ⊤ := by
    refine top_le_iff.mp fun x _ => ?_
    obtain ⟨α, hα⟩ := 𝓝.exists_mem_range (y x)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨α, hα⟩
  let 𝒰 : W.OpenCover := W.openCoverOfIsOpenCover U hU
  refine Scheme.zariskiTopology.superset_covering ?_ (𝒰.mem_grothendieckTopology)
  rw [Sieve.generate_le_iff]
  rintro _ _ ⟨α⟩
  obtain ⟨a, ha⟩ := 𝓝.exists_lift_preimage y α
  exact ⟨α, a, ha⟩

end Zariski

end MagnetFamily

section ActionA

variable {P Q : AddSubmonoid M} {V V' : Scheme.{u}}

/-- `T`-points of `𝔸(P)`, in the form of the repository: `Hom(T, Spec ℤ[P]) = Hom(P, Γ(T))`. -/
noncomputable def pts (P : AddSubmonoid M) (V : Scheme.{u}) : (V ⟶ AZ P) ≃ APt Scheme.Γ P (op V) :=
  ptsZ V

lemma pts_comp (g : V' ⟶ V) (f : V ⟶ AZ P) : pts P V' (g ≫ f) = APt.res g.op (pts P V f) :=
  ptsZ_comp g f

lemma pts_map (h : P ≤ Q) (f : V ⟶ AZ Q) :
    pts P V (f ≫ AZmap (AddSubmonoid.inclusion h)) = APt.restrict h (pts Q V f) :=
  ptsZ_AZmap _ f

/-- The action `k • a` of `D(M)` on `𝔸(P)`: `(k • a)(p) = k(p) a(p)` (Fact 2.12). -/
noncomputable def smulA (k : APt Scheme.Γ M (op V)) (a : V ⟶ AZ P) : V ⟶ AZ P :=
  (pts P V).symm (APt.toMagnet P k * pts P V a)

lemma pts_smulA (k : APt Scheme.Γ M (op V)) (a : V ⟶ AZ P) :
    pts P V (smulA k a) = APt.toMagnet P k * pts P V a :=
  Equiv.apply_symm_apply _ _

lemma comp_smulA (g : V' ⟶ V) (k : APt Scheme.Γ M (op V)) (a : V ⟶ AZ P) :
    g ≫ smulA k a = smulA (APt.res g.op k) (g ≫ a) := by
  apply (pts P V').injective
  rw [pts_comp, pts_smulA, pts_smulA, pts_comp, APt.res_mul, APt.toMagnet_res]

lemma smulA_one (a : V ⟶ AZ P) : smulA (1 : APt Scheme.Γ M (op V)) a = a := by
  apply (pts P V).injective
  rw [pts_smulA]
  have : APt.toMagnet P (1 : APt Scheme.Γ M (op V)) = 1 := rfl
  rw [this, one_mul]

lemma smulA_mul (k k' : APt Scheme.Γ M (op V)) (a : V ⟶ AZ P) :
    smulA (k * k') a = smulA k (smulA k' a) := by
  apply (pts P V).injective
  rw [pts_smulA, pts_smulA, pts_smulA]
  have : APt.toMagnet P (k * k') = APt.toMagnet P k * APt.toMagnet P k' := rfl
  rw [this, mul_assoc]

lemma smulA_incl (h : P ≤ Q) (k : APt Scheme.Γ M (op V)) (a : V ⟶ AZ Q) :
    smulA k (a ≫ AZmap (AddSubmonoid.inclusion h)) = smulA k a ≫ AZmap (AddSubmonoid.inclusion h) := by
  apply (pts P V).injective
  rw [pts_smulA, pts_map, pts_map, pts_smulA]
  rfl

variable (P) in
/-- The action of `D(M)` on `𝔸(P)`, for a submonoid `P ⊆ M`. -/
noncomputable def actA : AAction Scheme.Γ M (yoneda.obj (AZ P)) where
  smul {U} k a := smulA (V := unop U) k a
  one_smul x := smulA_one x
  mul_smul g h x := smulA_mul g h x
  map_smul f h x := comp_smulA f.unop h x

lemma isEquivariant_incl (h : P ≤ Q) :
    IsEquivariant (actA Q) (actA P) (yoneda.map (AZmap (AddSubmonoid.inclusion h))) :=
  fun k a => (smulA_incl h k a).symm

end ActionA

namespace MagnetFamily

section Action

variable [Nonempty A] {W : Scheme.{u}}

/-- Compatibility of the action on the `𝔸(N_α)` over overlaps. -/
lemma smulA_ι_congr {V : Scheme.{u}} (k : APt Scheme.Γ M (op V)) {α β : A} (a : V ⟶ AZ (𝓝.N α))
    (b : V ⟶ AZ (𝓝.N β)) (e : a ≫ 𝓝.ι α = b ≫ 𝓝.ι β) :
    smulA k a ≫ 𝓝.ι α = smulA k b ≫ 𝓝.ι β := by
  by_cases hne : α = β
  · subst hne
    rw [(cancel_mono (𝓝.ι α)).mp e]
  obtain ⟨u, rfl, rfl⟩ := 𝓝.exists_factor_of_overlap hne a b e
  have hα : smulA k (u ≫ 𝓝.gpMap α) = smulA k u ≫ 𝓝.gpMap α := smulA_incl (𝓝.le α) k u
  have hβ : smulA k (u ≫ 𝓝.gpMap β) = smulA k u ≫ 𝓝.gpMap β := smulA_incl (𝓝.le β) k u
  rw [hα, hβ, Category.assoc, Category.assoc, gpMap_ι, gpMap_ι]

/-- The proof of **Proposition 3.3**: the action of `D(M)` on the `𝔸(N_α)` glues to `𝔸(𝒩)`. -/
theorem existsUnique_smul (k : APt Scheme.Γ M (op W)) (y : W ⟶ 𝓝.AN) :
    ∃! z : W ⟶ 𝓝.AN, ∀ (α : A) {V : Scheme.{u}} (g : V ⟶ W) (a : V ⟶ AZ (𝓝.N α)),
      g ≫ y = a ≫ 𝓝.ι α → g ≫ z = smulA (APt.res g.op k) a ≫ 𝓝.ι α := by
  have hF : Presieve.IsSheaf Scheme.zariskiTopology (yoneda.obj 𝓝.AN) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (yoneda.obj 𝓝.AN)
  obtain ⟨z, hz, huniq⟩ := existsUnique_glue (𝓝 := 𝓝) (τ := 𝟭 Scheme.{u}) (F := yoneda.obj 𝓝.AN) hF y
    (𝓝.coverSieve_mem_zariski y)
    (fun α V g a _ => smulA (APt.res g.op k) a ≫ 𝓝.ι α)
    (fun α V V' s g a e e' => by
      change smulA (APt.res (s ≫ g).op k) (s ≫ a) ≫ 𝓝.ι α = s ≫ smulA (APt.res g.op k) a ≫ 𝓝.ι α
      rw [← Category.assoc, comp_smulA, op_comp, APt.res_comp])
    (fun α β V g a b e e' => 𝓝.smulA_ι_congr _ a b (e.symm.trans e'))
  exact ⟨z, fun α V g a e => hz α g a e, fun z' hz' => huniq z' fun α V g a e => hz' α g a e⟩

/-- The action of `k ∈ D(M)(W)` on a point `y ∈ 𝔸(𝒩)(W)`. -/
noncomputable def smulN (k : APt Scheme.Γ M (op W)) (y : W ⟶ 𝓝.AN) : W ⟶ 𝓝.AN :=
  (𝓝.existsUnique_smul k y).choose

lemma smulN_spec (k : APt Scheme.Γ M (op W)) (y : W ⟶ 𝓝.AN) {α : A} {V : Scheme.{u}} (g : V ⟶ W)
    (a : V ⟶ AZ (𝓝.N α)) (e : g ≫ y = a ≫ 𝓝.ι α) :
    g ≫ 𝓝.smulN k y = smulA (APt.res g.op k) a ≫ 𝓝.ι α :=
  (𝓝.existsUnique_smul k y).choose_spec.1 α g a e

lemma smulN_unique (k : APt Scheme.Γ M (op W)) (y z : W ⟶ 𝓝.AN)
    (hz : ∀ (α : A) {V : Scheme.{u}} (g : V ⟶ W) (a : V ⟶ AZ (𝓝.N α)),
      g ≫ y = a ≫ 𝓝.ι α → g ≫ z = smulA (APt.res g.op k) a ≫ 𝓝.ι α) :
    z = 𝓝.smulN k y :=
  (𝓝.existsUnique_smul k y).choose_spec.2 z hz

/-- `𝔸(N_α) → 𝔸(𝒩)` is equivariant, on points. -/
lemma smulN_comp_ι (k : APt Scheme.Γ M (op W)) {α : A} (a : W ⟶ AZ (𝓝.N α)) :
    𝓝.smulN k (a ≫ 𝓝.ι α) = smulA k a ≫ 𝓝.ι α := by
  have := 𝓝.smulN_spec k (a ≫ 𝓝.ι α) (𝟙 W) a (by simp)
  rw [Category.id_comp] at this
  have e : APt.res (𝟙 W).op k = k := APt.res_id k
  rw [this, e]

lemma smulN_comp_ιD (k : APt Scheme.Γ M (op W)) (a : W ⟶ 𝓝.D) :
    𝓝.smulN k (a ≫ 𝓝.ιD) = smulA k a ≫ 𝓝.ιD := by
  obtain ⟨α⟩ := ‹Nonempty A›
  have e : a ≫ 𝓝.ιD = (a ≫ 𝓝.gpMap α) ≫ 𝓝.ι α := by rw [Category.assoc, gpMap_ι]
  have hα : smulA k (a ≫ 𝓝.gpMap α) = smulA k a ≫ 𝓝.gpMap α := smulA_incl (𝓝.le α) k a
  rw [e, 𝓝.smulN_comp_ι, hα, Category.assoc, gpMap_ι]

lemma comp_smulN {V : Scheme.{u}} (f : V ⟶ W) (k : APt Scheme.Γ M (op W)) (y : W ⟶ 𝓝.AN) :
    f ≫ 𝓝.smulN k y = 𝓝.smulN (APt.res f.op k) (f ≫ y) := by
  refine 𝓝.smulN_unique _ _ _ fun α V' g a e => ?_
  rw [← Category.assoc, 𝓝.smulN_spec k y (g ≫ f) a (by rw [Category.assoc, e]), op_comp,
    APt.res_comp]

/-- The action of `D(M)` on `𝔸(𝒩)` of **Proposition 3.3**, "defined by gluing". -/
noncomputable def actAN : AAction Scheme.Γ M (yoneda.obj 𝓝.AN) where
  smul {U} k y := 𝓝.smulN (W := unop U) k y
  one_smul {U} x := by
    refine (𝓝.smulN_unique (W := unop U) 1 x x fun α V g a e => ?_).symm
    rw [e]
    congr 1
    have : APt.res g.op (1 : APt Scheme.Γ M (op (unop U))) = 1 :=
      MonoidHom.ext fun p => by
        rw [APt.res_apply, MonoidHom.one_apply, MonoidHom.one_apply, map_one]
    rw [this, smulA_one]
  mul_smul {U} k k' x := by
    refine (𝓝.smulN_unique (W := unop U) (k * k') x _ fun α V g a e => ?_).symm
    rw [𝓝.smulN_spec k (𝓝.smulN k' x) g (smulA (APt.res g.op k') a) (𝓝.smulN_spec k' x g a e),
      APt.res_mul, smulA_mul]
  map_smul {U U'} f k x := 𝓝.comp_smulN f.unop k x

/-- `𝔸(N_α) → 𝔸(𝒩)` is `D(M)`-equivariant (**Proposition 3.3**). -/
theorem isEquivariant_ι (α : A) : IsEquivariant (actA (𝓝.N α)) 𝓝.actAN (yoneda.map (𝓝.ι α)) :=
  fun {T} k a => (𝓝.smulN_comp_ι (W := unop T) k a).symm

end Action

end MagnetFamily

variable (M) in
/-- A scheme with an action of `D(M)`. -/
structure DScheme where
  /-- The scheme. -/
  X : Scheme.{u}
  /-- The action, on points. -/
  act : AAction Scheme.Γ M (yoneda.obj X)

namespace DScheme

/-- A `D(M)`-equivariant morphism of schemes. -/
@[ext]
structure Hom (X Y : DScheme M) where
  /-- The morphism of schemes. -/
  hom : X.X ⟶ Y.X
  eqv : IsEquivariant X.act Y.act (yoneda.map hom)

instance : Category (DScheme M) where
  Hom := Hom
  id X := ⟨𝟙 _, fun {T} h x => by
    change X.act.smul h x ≫ 𝟙 _ = X.act.smul h (x ≫ 𝟙 _)
    rw [Category.comp_id, Category.comp_id]⟩
  comp {X Y Z} f g := ⟨f.hom ≫ g.hom, fun {T} h x => by
    have h1 := f.eqv h x
    have h2 := g.eqv h (x ≫ f.hom)
    change X.act.smul h x ≫ f.hom ≫ g.hom = Z.act.smul h (x ≫ f.hom ≫ g.hom)
    rw [← Category.assoc, ← Category.assoc]
    exact (congrArg (· ≫ g.hom) h1).trans h2⟩

@[simp] lemma comp_hom {X Y Z : DScheme M} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Hom.hom (f ≫ g) = Hom.hom f ≫ Hom.hom g := rfl

@[simp] lemma id_hom (X : DScheme M) : Hom.hom (𝟙 X) = 𝟙 X.X := rfl

@[ext] lemma hom_ext {X Y : DScheme M} {f g : X ⟶ Y} (h : Hom.hom f = Hom.hom g) : f = g :=
  Hom.ext h

end DScheme

namespace MagnetFamily

/-- `𝔸(P)` with its `D(M)`-action. -/
noncomputable def dA (P : AddSubmonoid M) : DScheme M := ⟨AZ P, actA P⟩

/-- `D(Z) → 𝔸(N_α)` as a morphism of `D(M)`-schemes. -/
noncomputable def dGp (α : A) : dA 𝓝.Z.toAddSubmonoid ⟶ dA (𝓝.N α) :=
  ⟨𝓝.gpMap α, isEquivariant_incl (𝓝.le α)⟩

/-- The diagram of **Proposition 3.3**, in the category of schemes with a `D(M)`-action. -/
noncomputable def dDiag : WidePushoutShape A ⥤ DScheme M :=
  WidePushoutShape.wideSpan (dA 𝓝.Z.toAddSubmonoid) (fun α => dA (𝓝.N α)) 𝓝.dGp

variable [Nonempty A]

/-- `𝔸(𝒩)` with the action of **Proposition 3.3**. -/
noncomputable def dAN : DScheme M := ⟨𝓝.AN, 𝓝.actAN⟩

/-- The cocone of the `D(M)`-equivariant morphisms `𝔸(N_α) → 𝔸(𝒩)`. -/
noncomputable def dCocone : Cocone 𝓝.dDiag :=
  WidePushoutShape.mkCocone (F := 𝓝.dDiag) (X := 𝓝.dAN)
    ⟨𝓝.ιD, fun {T} k a => (𝓝.smulN_comp_ιD (W := unop T) k a).symm⟩
    (fun α => ⟨𝓝.ι α, 𝓝.isEquivariant_ι α⟩)
    (fun α => DScheme.hom_ext (𝓝.gpMap_ι α))

/-- A scheme morphism out of `𝔸(𝒩)` whose restrictions to the `𝔸(N_α)` are equivariant is equivariant:
the last step of the proof of **Proposition 3.3**. -/
theorem isEquivariant_of_ι {Y : DScheme M} (f : 𝓝.AN ⟶ Y.X)
    (hf : ∀ α, IsEquivariant (actA (𝓝.N α)) Y.act (yoneda.map (𝓝.ι α ≫ f))) :
    IsEquivariant 𝓝.actAN Y.act (yoneda.map f) := by
  intro T k y
  have hF : Presieve.IsSheaf Scheme.zariskiTopology (yoneda.obj Y.X) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (yoneda.obj Y.X)
  refine (hF _ (𝓝.coverSieve_mem_zariski (W := unop T) y)).isSeparatedFor.ext fun V g hg => ?_
  obtain ⟨α, a, e⟩ := hg
  have e' : g ≫ y = a ≫ 𝓝.ι α := e
  have h1 : g ≫ 𝓝.smulN (W := unop T) k y = smulA (APt.res g.op k) a ≫ 𝓝.ι α := 𝓝.smulN_spec k y g a e'
  have h2 := hf α (T := op V) (APt.res g.op k) a
  have h3 := Y.act.map_smul g.op k (y ≫ f)
  change g ≫ 𝓝.smulN (W := unop T) k y ≫ f = g ≫ Y.act.smul k (y ≫ f)
  have h3' : g ≫ Y.act.smul k (y ≫ f) = Y.act.smul (APt.res g.op k) (g ≫ y ≫ f) := h3
  rw [h3', ← Category.assoc, h1, ← Category.assoc g y f, e', Category.assoc, Category.assoc]
  exact h2

/-- Morphisms out of `𝔸(𝒩)` agreeing on all `𝔸(N_α)` are equal. -/
lemma AN_hom_ext {Y : Scheme.{u}} {f g : 𝓝.AN ⟶ Y} (h : ∀ α, 𝓝.ι α ≫ f = 𝓝.ι α ≫ g) : f = g := by
  refine colimit.hom_ext fun j => ?_
  cases j with
  | none =>
    obtain ⟨α⟩ := ‹Nonempty A›
    have e := 𝓝.gpMap_ι α
    change 𝓝.ιD ≫ f = 𝓝.ιD ≫ g
    rw [← e, Category.assoc, Category.assoc, h α]
  | some α => exact h α

section Desc

variable (s : Cocone 𝓝.dDiag)

/-- The legs of a cocone, as morphisms of schemes. -/
noncomputable def sLeg (α : A) : AZ (𝓝.N α) ⟶ s.pt.X := DScheme.Hom.hom (s.ι.app (some α))

/-- The leg at `D(Z)`. -/
noncomputable def sLeg₀ : 𝓝.D ⟶ s.pt.X := DScheme.Hom.hom (s.ι.app none)

lemma sLeg_w (α : A) : 𝓝.gpMap α ≫ 𝓝.sLeg s α = 𝓝.sLeg₀ s :=
  congrArg DScheme.Hom.hom (s.w (WidePushoutShape.Hom.init α))

/-- The morphism of schemes out of `𝔸(𝒩)` given by the universal property in schemes. -/
noncomputable def sDesc : 𝓝.AN ⟶ s.pt.X := 𝓝.desc (𝓝.sLeg s) (𝓝.sLeg₀ s) (𝓝.sLeg_w s)

lemma ι_sDesc (α : A) : 𝓝.ι α ≫ 𝓝.sDesc s = 𝓝.sLeg s α := 𝓝.ι_desc _ _ _ α

end Desc

/-- **Proposition 3.3**: the diagram `D(N^gp) → 𝔸(N_α)` admits a colimit in the category of schemes with
a `D(M)`-action, namely `𝔸(𝒩)` as a scheme (`dCocone` has point `dAN`, whose scheme is `AN`). -/
noncomputable def prop33 : IsColimit 𝓝.dCocone where
  desc s := ⟨𝓝.sDesc s, 𝓝.isEquivariant_of_ι _ fun α => by
    rw [ι_sDesc]
    exact (s.ι.app (some α)).eqv⟩
  fac s j := by
    apply DScheme.hom_ext
    cases j with
    | none =>
      obtain ⟨α⟩ := ‹Nonempty A›
      change 𝓝.ιD ≫ 𝓝.sDesc s = 𝓝.sLeg₀ s
      rw [← 𝓝.gpMap_ι α, Category.assoc, ι_sDesc, sLeg_w]
    | some α => exact 𝓝.ι_sDesc s α
  uniq s m hm := by
    apply DScheme.hom_ext
    refine 𝓝.AN_hom_ext fun α => ?_
    refine (congrArg DScheme.Hom.hom (hm (some α))).trans ?_
    exact (𝓝.ι_sDesc s α).symm

/-- **Proposition 3.3**: the colimit is `𝔸(𝒩)` as a scheme. -/
theorem prop33_scheme : (𝓝.dCocone.pt).X = 𝓝.AN := rfl

end MagnetFamily

end AlgMag.XP
