/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import StacksFrontier.AlgebraicGeometry.Spaces.Basic
import StacksFrontier.AlgebraicGeometry.Size.FlatSurjective
import AlgMag.Sec9General

/-!
# Hochschild cohomology of `𝔸(M)` over an algebraic space

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026) 126–201, §9.3: Propositions 9.11, 9.12,
9.13 and Remark 9.14 over a base `B` which is an algebraic space. `AlgMag.Sec9General` treats a
scheme base.

The site `B_spaces,fppf` is modelled by `SB Bsp`, the category of schemes `T` of the big fppf site of
`S` with a point of `Bsp`; an object over `B` which is an algebraic space is a presheaf on `SB Bsp`,
and its sections are the natural maps (see `CochainV`). `Bsp` is any presheaf: the algebraic
space axioms are not used. `M` is countable, which is implied by the assumption of §9.3 that `M` is
finitely generated: this makes `Spec Γ(W)[Mⁿ]` an object of the size-cut site.
-/

universe v u

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.checkUnivs false
set_option linter.deprecated false

open CategoryTheory Opposite AlgebraicGeometry

open scoped Classical

noncomputable section

variable {Bs : BigFppfSite.{u}} {S : Scheme.{u}} {hS : Bs.Contains S}

namespace AlgMag.S9B

open AlgMag.S9

/-- A scheme `T` of the site with a morphism to the base `Bsp`. -/
structure SB (Bsp : (BigFppfOver Bs S hS)ᵒᵖ ⥤ Type u) where
  /-- the scheme -/
  obj : BigFppfOver Bs S hS
  /-- the morphism to the base -/
  pt : Bsp.obj (op obj)

end AlgMag.S9B

open AlgMag.S9B

variable {Bsp : (BigFppfOver Bs S hS)ᵒᵖ ⥤ Type u}

namespace AlgMag.S9B

open AlgMag.S9

/-- The underlying scheme. -/
abbrev SB.left (T : SB Bsp) : Scheme.{u} := (BigFppfOver.toScheme Bs S hS).obj T.obj

/-- Morphisms over the base. -/
@[ext]
structure SB.Hom (T T' : SB Bsp) where
  /-- the morphism of schemes over `S` -/
  hom : T.obj ⟶ T'.obj
  w : Bsp.map hom.op T'.pt = T.pt

/-- The underlying morphism of schemes. -/
abbrev SB.Hom.left {T T' : SB Bsp} (f : SB.Hom T T') : T.left ⟶ T'.left :=
  (BigFppfOver.toScheme Bs S hS).map f.hom

instance : Category (SB Bsp) where
  Hom := SB.Hom
  id T := ⟨𝟙 _, by simp⟩
  comp {X Y Z} f g := ⟨f.hom ≫ g.hom, by
    rw [op_comp, Bsp.map_comp]
    simp only [types_comp_apply, g.w, f.w]⟩

@[simp] lemma SB.id_left (T : SB Bsp) : SB.Hom.left (𝟙 T) = 𝟙 T.left :=
  (BigFppfOver.toScheme Bs S hS).map_id _

@[simp] lemma SB.comp_left {T T' T'' : SB Bsp} (f : T ⟶ T') (g : T' ⟶ T'') :
    SB.Hom.left (f ≫ g) = SB.Hom.left f ≫ SB.Hom.left g :=
  (BigFppfOver.toScheme Bs S hS).map_comp _ _

/-- Morphisms over the base are determined by their underlying morphism of schemes. -/
lemma SB.hom_ext {T T' : SB Bsp} {f g : T ⟶ T'} (h : SB.Hom.left f = SB.Hom.left g) : f = g := by
  have : f.hom = g.hom := by
    apply Over.OverMorphism.ext
    exact (Bs.inclusion).map_injective h
  exact SB.Hom.ext this

/-- The structure morphism to `S`, in `Sch_κ`. -/
abbrev SB.str (T : SB Bsp) : Bs.obj T.obj.left.property ⟶ Bs.obj hS := T.obj.hom

/-- `X ⟶ T.left`, as a morphism of `Sch_κ`. -/
abbrev SB.kmap {X Y : Scheme.{u}} (hX : Bs.Contains X) (hY : Bs.Contains Y) (f : X ⟶ Y) :
    Bs.obj hX ⟶ Bs.obj hY := ObjectProperty.homMk f

/-- A scheme of the site over `T`, as an object over the base. -/
def SB.ofMap (T : SB Bsp) {X : Scheme.{u}} (hX : Bs.Contains X) (f : X ⟶ T.left) : SB Bsp where
  obj := Over.mk (SB.kmap hX T.obj.left.property f ≫ T.obj.hom)
  pt := Bsp.map (Over.homMk (SB.kmap hX T.obj.left.property f)).op T.pt

/-- The morphism `X ⟶ T`. -/
def SB.ofMapι (T : SB Bsp) {X : Scheme.{u}} (hX : Bs.Contains X) (f : X ⟶ T.left) :
    T.ofMap hX f ⟶ T :=
  ⟨Over.homMk (SB.kmap hX T.obj.left.property f), rfl⟩

/-- The morphism `W ⟶ X`, in the slice. -/
def SB.liftAux {T W : SB Bsp} {X : Scheme.{u}} (hX : Bs.Contains X) {f : X ⟶ T.left} (t : W ⟶ T)
    (u : W.left ⟶ X) (hu : u ≫ f = SB.Hom.left t) : W.obj ⟶ (T.ofMap hX f).obj :=
  Over.homMk (SB.kmap W.obj.left.property hX u) (by
    have e : SB.kmap W.obj.left.property hX u ≫ SB.kmap hX T.obj.left.property f = t.hom.left :=
      (Bs.inclusion).map_injective hu
    change _ ≫ SB.kmap hX T.obj.left.property f ≫ T.obj.hom = W.obj.hom
    rw [← Category.assoc, e]
    exact Over.w t.hom)

/-- Lifting a morphism `W ⟶ T` through `X ⟶ T`. -/
def SB.ofMapLift {T W : SB Bsp} {X : Scheme.{u}} (hX : Bs.Contains X) {f : X ⟶ T.left} (t : W ⟶ T)
    (u : W.left ⟶ X) (hu : u ≫ f = SB.Hom.left t) : W ⟶ T.ofMap hX f :=
  ⟨SB.liftAux hX t u hu, by
    have e : SB.liftAux hX t u hu ≫ (T.ofMapι hX f).hom = t.hom := by
      apply Over.OverMorphism.ext
      exact (Bs.inclusion).map_injective hu
    change Bsp.map _ (Bsp.map (T.ofMapι hX f).hom.op T.pt) = W.pt
    rw [← types_comp_apply (Bsp.map _) (Bsp.map _), ← Bsp.map_comp, ← op_comp, e]
    exact t.w⟩

lemma SB.ofMapLift_ι {T W : SB Bsp} {X : Scheme.{u}} (hX : Bs.Contains X) {f : X ⟶ T.left}
    (t : W ⟶ T) (u : W.left ⟶ X) (hu : u ≫ f = SB.Hom.left t) :
    SB.ofMapLift hX t u hu ≫ T.ofMapι hX f = t :=
  SB.hom_ext (by rw [SB.comp_left]; exact hu)

variable (Bsp) in
/-- The structure presheaf `𝒪_B` on the site. -/
def OB : (SB Bsp)ᵒᵖ ⥤ CommRingCat.{u} where
  obj T := Γ((unop T).left, ⊤)
  map f := (SB.Hom.left f.unop).appTop
  map_id T := by
    change (SB.Hom.left (𝟙 (unop T))).appTop = _
    rw [SB.id_left]
    simp
  map_comp f g := by
    change (SB.Hom.left (g.unop ≫ f.unop)).appTop = _
    rw [SB.comp_left]
    simp

/-- The sieve generated by an open cover of `T`. -/
def coverSieve (T : SB Bsp) (𝒰 : Scheme.OpenCover.{u} T.left) : Sieve T where
  arrows W f := ∃ (i : 𝒰.I₀) (u : W.left ⟶ 𝒰.X i), SB.Hom.left f = u ≫ 𝒰.f i
  downward_closed := by
    rintro W W' f ⟨i, u, hu⟩ g
    exact ⟨i, SB.Hom.left g ≫ u, by rw [SB.comp_left, hu, Category.assoc]⟩

lemma coverContains (T : SB Bsp) (𝒰 : Scheme.OpenCover.{u} T.left) (i : 𝒰.I₀) :
    Bs.Contains (𝒰.X i) :=
  (Scheme.size_le_of_isOpenImmersion (𝒰.f i)).trans_lt T.obj.left.property

/-- The piece of `T` given by `𝒰.X i`. -/
abbrev coverPiece (T : SB Bsp) (𝒰 : Scheme.OpenCover.{u} T.left) (i : 𝒰.I₀) : SB Bsp :=
  T.ofMap (coverContains T 𝒰 i) (𝒰.f i)

/-- The inclusion of a piece. -/
abbrev coverHom (T : SB Bsp) (𝒰 : Scheme.OpenCover.{u} T.left) (i : 𝒰.I₀) : coverPiece T 𝒰 i ⟶ T :=
  T.ofMapι (coverContains T 𝒰 i) (𝒰.f i)

/-- **Quasi-coherent** `𝒪_B`-modules: Zariski sheaves on every object, whose restriction along a
morphism of affine schemes `T' → T` is the base change `F(T') = F(T) ⊗_{Γ(T)} Γ(T')`. As in
`AlgMag.S9.IsQCoh`, fppf descent holds automatically for these and is not used. -/
structure IsQCoh (F : PMod (OB Bsp)) : Prop where
  sheaf : ∀ (T : SB Bsp) (𝒰 : Scheme.OpenCover.{u} T.left) (R : Sieve T),
    coverSieve T 𝒰 ≤ R → Presieve.IsSheafFor F.toPresheaf R.arrows
  base_change : ∀ {T T' : SB Bsp} (s : T' ⟶ T) [IsAffine T.left] [IsAffine T'.left],
    IsBC ((OB Bsp).map s.op).hom (F.map s.op) (F.map_smul s.op)

/-- The monoid functor `𝔸(M)_B`. -/
def Hm (M : Type u) [AddCommMonoid M] (Bsp : (BigFppfOver Bs S hS)ᵒᵖ ⥤ Type u) :
    (SB Bsp)ᵒᵖ ⥤ MonCat.{u} where
  obj T := MonCat.of (APt (OB Bsp) M T)
  map f := MonCat.ofHom
    { toFun := APt.res f
      map_one' := by ext p; simp
      map_mul' := APt.res_mul f }
  map_id T := MonCat.hom_ext (MonoidHom.ext fun a => APt.res_id a)
  map_comp f g := MonCat.hom_ext (MonoidHom.ext fun a => APt.res_comp f g a)

variable {F : PMod (OB Bsp)}

/-- `#(N →₀ R) ≤ max ℵ₀ #R` for `N` countable. -/
lemma mk_finsupp_le_of_countable (N R : Type u) [Countable N] [AddCommMonoid R] :
    Cardinal.mk (N →₀ R) ≤ max Cardinal.aleph0 (Cardinal.mk R) := by
  have hs : Function.Surjective
      (fun l : List (N × R) => (l.map fun p => Finsupp.single p.1 p.2).sum) := by
    intro x
    induction x using Finsupp.induction_linear with
    | zero => exact ⟨[], rfl⟩
    | add p q hp hq =>
      obtain ⟨l, rfl⟩ := hp
      obtain ⟨l', rfl⟩ := hq
      exact ⟨l ++ l', by simp⟩
    | single m f => exact ⟨[(m, f)], by simp⟩
  refine (Cardinal.mk_le_of_surjective hs).trans ?_
  refine (Cardinal.mk_list_le_max _).trans (max_le (le_max_left _ _) ?_)
  rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
  refine (Cardinal.mul_le_max _ _).trans (max_le (max_le ?_ (le_max_right _ _)) (le_max_left _ _))
  exact (Cardinal.mk_le_aleph0 (α := N)).trans (le_max_left _ _)

lemma sep_cover (hF : IsQCoh F) (T : SB Bsp) (𝒰 : Scheme.OpenCover.{u} T.left) {y y' : F.obj (op T)}
    (h : ∀ i, F.map (coverHom T 𝒰 i).op y = F.map (coverHom T 𝒰 i).op y') : y = y' := by
  refine (hF.sheaf T 𝒰 _ le_rfl).isSeparatedFor.ext fun W f hf => ?_
  obtain ⟨i, u, hu⟩ := hf
  have e : f = SB.ofMapLift (coverContains T 𝒰 i) f u hu.symm ≫ coverHom T 𝒰 i :=
    (SB.ofMapLift_ι _ _ _ _).symm
  change F.map f.op y = F.map f.op y'
  rw [e, op_comp, F.map_comp, F.map_comp, h]

/-- Two sections agreeing on all affine schemes over `T` are equal. -/
lemma sep_affine (hF : IsQCoh F) (T : SB Bsp) {y y' : F.obj (op T)}
    (h : ∀ (A : SB Bsp) (a : A ⟶ T) [IsAffine A.left], F.map a.op y = F.map a.op y') : y = y' := by
  refine sep_cover hF T T.left.affineCover fun i => ?_
  haveI : IsAffine (coverPiece T T.left.affineCover i).left := by
    change IsAffine (T.left.affineCover.X i)
    infer_instance
  exact h _ _

/-- **Gluing over affines**: a compatible family of sections over all affine schemes over `T` comes
from a unique section over `T`. -/
theorem affine_glue (hF : IsQCoh F) (T : SB Bsp)
    (val : ∀ (A : SB Bsp) (a : A ⟶ T) [IsAffine A.left], F.obj (op A))
    (compat : ∀ (A A' : SB Bsp) (s : A' ⟶ A) (a : A ⟶ T) [IsAffine A.left] [IsAffine A'.left],
      val A' (s ≫ a) = F.map s.op (val A a)) :
    ∃! v : F.obj (op T), ∀ (A : SB Bsp) (a : A ⟶ T) [IsAffine A.left], F.map a.op v = val A a := by
  let 𝒰 := T.left.affineCover
  have hA : ∀ i, IsAffine (coverPiece T 𝒰 i).left := fun i => by
    change IsAffine (𝒰.X i)
    infer_instance
  let aff : Sieve T :=
    { arrows := fun W f => ∃ (A : SB Bsp) (_ : IsAffine A.left) (u : W ⟶ A) (a : A ⟶ T), u ≫ a = f
      downward_closed := by
        rintro W W' f ⟨A, hA, u, a, rfl⟩ g
        exact ⟨A, hA, g ≫ u, a, Category.assoc _ _ _⟩ }
  have hle : coverSieve T 𝒰 ≤ aff := by
    rintro W f ⟨i, u, hu⟩
    exact ⟨coverPiece T 𝒰 i, hA i, SB.ofMapLift (coverContains T 𝒰 i) f u hu.symm, coverHom T 𝒰 i,
      SB.ofMapLift_ι _ _ _ _⟩
  have sh := hF.sheaf T 𝒰 aff hle
  let x : Presieve.FamilyOfElements F.toPresheaf aff.arrows := fun W f hf =>
    haveI := hf.choose_spec.choose
    F.map hf.choose_spec.choose_spec.choose.op
      (val hf.choose hf.choose_spec.choose_spec.choose_spec.choose)
  have hx : ∀ {W} (f : W ⟶ T) (hf : aff.arrows f) (A : SB Bsp) [IsAffine A.left] (u : W ⟶ A)
      (a : A ⟶ T), u ≫ a = f → x f hf = F.map u.op (val A a) := by
    intro W f hf A _ u a hua
    obtain ⟨A₀, hA₀, u₀, a₀, h₀⟩ := id hf
    have key : ∀ (A' : SB Bsp) [IsAffine A'.left] (u' : W ⟶ A') (a' : A' ⟶ T), u' ≫ a' = f →
        ∀ (A'' : SB Bsp) [IsAffine A''.left] (u'' : W ⟶ A'') (a'' : A'' ⟶ T), u'' ≫ a'' = f →
        F.map u'.op (val A' a') = F.map u''.op (val A'' a'') := by
      intro A' _ u' a' h' A'' _ u'' a'' h''
      refine sep_affine hF W fun E e _ => ?_
      change F.map e.op (F.map u'.op _) = F.map e.op (F.map u''.op _)
      rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp, ← compat, ← compat]
      congr 1
      rw [Category.assoc, Category.assoc, h', h'']
    haveI := hf.choose_spec.choose
    exact key _ _ _ hf.choose_spec.choose_spec.choose_spec.choose_spec _ u a hua
  have hc : x.Compatible := by
    intro W₁ W₂ Z g₁ g₂ f₁ f₂ h₁ h₂ comm
    obtain ⟨A₁, hA₁, u₁, a₁, e₁⟩ := id h₁
    obtain ⟨A₂, hA₂, u₂, a₂, e₂⟩ := id h₂
    change F.map g₁.op (x f₁ h₁) = F.map g₂.op (x f₂ h₂)
    rw [hx f₁ h₁ A₁ u₁ a₁ e₁, hx f₂ h₂ A₂ u₂ a₂ e₂]
    refine sep_affine hF Z fun E e _ => ?_
    simp only [← F.map_comp, ← op_comp]
    rw [← compat, ← compat]
    congr 1
    subst e₁ e₂
    simp only [Category.assoc] at comm ⊢
    rw [comm]
  refine ⟨sh.amalgamate x hc, fun A a _ => ?_, fun v hv => ?_⟩
  · have ha : aff.arrows a := ⟨A, inferInstance, 𝟙 A, a, Category.id_comp a⟩
    have := sh.valid_glue hc a ha
    refine Eq.trans this ?_
    rw [hx a ha A (𝟙 A) a (Category.id_comp a), op_id, F.map_id]
  · refine sep_affine hF T fun A a _ => ?_
    rw [hv]
    have ha : aff.arrows a := ⟨A, inferInstance, 𝟙 A, a, Category.id_comp a⟩
    have := sh.valid_glue hc a ha
    refine Eq.symm (Eq.trans this ?_)
    rw [hx a ha A (𝟙 A) a (Category.id_comp a), op_id, F.map_id]

/-! ### The universal point: cochains over an affine scheme -/

section Eval

variable {N : Type u} [AddCommMonoid N] [Countable N]

/-- `x = ∑ f_m X^m ↦ ∑ a(m) • f_m|_T`, for `x ∈ ⨁_{m ∈ N} F(V)`, `t : T ⟶ V`, `a ∈ 𝔸(N)(T)`. -/
def evalE {V T : SB Bsp} (t : T ⟶ V) (a : APt (OB Bsp) N (op T)) :
    (N →₀ F.obj (op V)) →+ F.obj (op T) :=
  Finsupp.liftAddHom fun m =>
    { toFun := fun f => a (Multiplicative.ofAdd m) • F.map t.op f
      map_zero' := by simp
      map_add' := fun f f' => by simp [smul_add] }

@[simp] lemma evalE_single {V T : SB Bsp} (t : T ⟶ V) (a : APt (OB Bsp) N (op T)) (m : N)
    (f : F.obj (op V)) :
    evalE t a (Finsupp.single m f) = a (Multiplicative.ofAdd m) • F.map t.op f := by
  simp [evalE]

lemma evalE_res {V T T' : SB Bsp} (s : T' ⟶ T) (t : T ⟶ V) (a : APt (OB Bsp) N (op T))
    (x : N →₀ F.obj (op V)) :
    evalE (s ≫ t) (APt.res s.op a) x = F.map s.op (evalE t a x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single m f =>
    rw [evalE_single, evalE_single, F.map_smul, op_comp, F.map_comp]
    rfl

variable (F N) in
/-- The natural maps `𝔸(N) → F` over `V`. -/
@[ext]
structure NC (V : SB Bsp) where
  /-- the values -/
  app : ∀ {T : SB Bsp} (_ : T ⟶ V), APt (OB Bsp) N (op T) → F.obj (op T)
  naturality : ∀ {T T' : SB Bsp} (s : T' ⟶ T) (t : T ⟶ V) (a : APt (OB Bsp) N (op T)),
    app (s ≫ t) (APt.res s.op a) = F.map s.op (app t a)

/-- Restriction of natural maps. -/
def NC.res {V V' : SB Bsp} (s : V' ⟶ V) (c : NC F N V) : NC F N V' where
  app t a := c.app (t ≫ s) a
  naturality r t a := by rw [Category.assoc]; exact c.naturality r (t ≫ s) a

/-- `x ↦ (a ↦ ∑ a(m) • f_m)`. -/
def phiN {V : SB Bsp} (x : N →₀ F.obj (op V)) : NC F N V where
  app t a := evalE t a x
  naturality s t a := evalE_res s t a x

variable (N) in
/-- The Hopf algebra `Γ(V)[N]`. -/
abbrev Dring (V : SB Bsp) : CommRingCat.{u} :=
  CommRingCat.of (AddMonoidAlgebra Γ(V.left, ⊤) N)

/-- `Γ(V) → Γ(V)[N]`. -/
def Dalg (V : SB Bsp) : Γ(V.left, ⊤) ⟶ Dring N V :=
  CommRingCat.ofHom (algebraMap Γ(V.left, ⊤) (AddMonoidAlgebra Γ(V.left, ⊤) N))

variable (W : SB Bsp) [IsAffine W.left]

/-- `Spec Γ(W)[N] → W`, for `W` affine. -/
def pr0 : Spec (Dring N W) ⟶ W.left :=
  Spec.map (Dalg W) ≫ W.left.isoSpec.inv

variable (N) in
/-- Size: `Spec Γ(W)[N]` lies in the site, for `N` countable. -/
lemma contains_Dring : Bs.Contains (Spec (Dring N W)) := by
  have hW : Bs.Contains (Spec (.of Γ(W.left, ⊤))) :=
    (Scheme.size_congr W.left.isoSpec).symm.trans_lt W.obj.left.property
  refine Scheme.size_Spec_lt_of_mk_le_max Bs.aleph0_lt_cutoff Bs.cutoff_isStrongPrelimit hW ?_
  refine (Cardinal.mk_le_of_injective (AddMonoidAlgebra.coeff_injective
    (R := Γ(W.left, ⊤)) (M := N))).trans ?_
  exact mk_finsupp_le_of_countable N Γ(W.left, ⊤)

variable (N) in
/-- `𝔸(N)_W`, for `W` affine: `Spec Γ(W)[N]`, an object of the site since `N` is countable. -/
def Yobj : SB Bsp := SB.ofMap W (contains_Dring N W) (pr0 (N := N) W)

instance : IsAffine (Yobj N W).left := by
  change IsAffine (Spec (Dring N W))
  infer_instance

variable (N) in
/-- `𝔸(N)_W → W`. -/
def Ypr : Yobj N W ⟶ W := SB.ofMapι W (contains_Dring N W) (pr0 W)

/-- The identification `Γ(W)[N] → Γ(𝔸(N)_W)`. -/
def Yiota : Dring N W ⟶ Γ((Yobj N W).left, ⊤) :=
  (Scheme.ΓSpecIso (Dring N W)).inv

lemma Yiota_bijective : Function.Bijective (Yiota (N := N) W) := by
  have : IsIso (Scheme.ΓSpecIso (Dring N W)).inv := inferInstance
  exact (ConcreteCategory.isIso_iff_bijective _).mp this

/-- The ring map `Γ(W) → Γ(𝔸(N)_W)` of `Ypr` is the inclusion of constants. -/
lemma Ypr_map : (Ypr N W).left.appTop = Dalg W ≫ Yiota W := by
  have h1 : pr0 (N := N) W ≫ W.left.toSpecΓ = Spec.map (Dalg W) := by
    have e : W.left.toSpecΓ = W.left.isoSpec.hom := rfl
    rw [e, pr0, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have h2 := GB.homSpecEquiv_comp (pr0 (N := N) W) W.left.toSpecΓ
  have h3 := GB.homSpecEquiv_map (T := Spec (Dring N W)) (Dalg (N := N) W) (𝟙 _)
  rw [Category.id_comp, ← h1, h2] at h3
  have h4 : GB.homSpecEquiv W.left _ W.left.toSpecΓ = 𝟙 _ := by
    simp [GB.homSpecEquiv, Scheme.toSpecΓ_appTop]
  rw [h4, Category.id_comp] at h3
  refine h3.trans ?_
  congr 1

variable {W}

/-- The ring map `Γ(W)[N] → Γ(T)` of a point `a` of `𝔸(N)` over `t : T ⟶ W`. -/
def rhoOf {T : SB Bsp} (t : T ⟶ W) (a : APt (OB Bsp) N (op T)) :
    Dring N W ⟶ Γ(T.left, ⊤) :=
  CommRingCat.ofHom (AddMonoidAlgebra.liftNCRingHom t.left.appTop.hom a
    (fun _ _ => Commute.all _ _))

lemma rhoOf_single {T : SB Bsp} (t : T ⟶ W) (a : APt (OB Bsp) N (op T)) (m : N)
    (r : Γ(W.left, ⊤)) :
    (rhoOf t a).hom (AddMonoidAlgebra.single m r) =
      t.left.appTop.hom r * (show Γ(T.left, ⊤) from a (Multiplicative.ofAdd m)) :=
  AddMonoidAlgebra.liftNC_single _ _ m r

lemma Dalg_rhoOf {T : SB Bsp} (t : T ⟶ W) (a : APt (OB Bsp) N (op T)) :
    Dalg W ≫ rhoOf t a = t.left.appTop := by
  refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
  change (rhoOf t a).hom (AddMonoidAlgebra.single 0 r) = _
  rw [rhoOf_single]
  have : (show Γ(T.left, ⊤) from a (Multiplicative.ofAdd (0 : N))) = 1 := a.map_one
  rw [this]
  exact mul_one _

lemma k_pr0 {T : SB Bsp} (t : T ⟶ W) (a : APt (OB Bsp) N (op T)) :
    (T.left.toSpecΓ ≫ Spec.map (rhoOf t a)) ≫ pr0 W = t.left := by
  rw [pr0, Category.assoc, ← Category.assoc (Spec.map _), ← Spec.map_comp, Dalg_rhoOf,
    ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc]
  have e : W.left.toSpecΓ = W.left.isoSpec.hom := rfl
  rw [e, Iso.hom_inv_id, Category.comp_id]

/-- The classifying morphism of a point `a` of `𝔸(N)` over `t : T ⟶ W`. -/
def classify {T : SB Bsp} (t : T ⟶ W) (a : APt (OB Bsp) N (op T)) : T ⟶ Yobj N W :=
  SB.ofMapLift (contains_Dring N W) t (T.left.toSpecΓ ≫ Spec.map (rhoOf t a)) (k_pr0 t a)

lemma classify_pr {T : SB Bsp} (t : T ⟶ W) (a : APt (OB Bsp) N (op T)) :
    classify t a ≫ Ypr N W = t :=
  SB.ofMapLift_ι _ _ _ _

lemma classify_map {T : SB Bsp} (t : T ⟶ W) (a : APt (OB Bsp) N (op T)) :
    Yiota W ≫ (classify t a).left.appTop = rhoOf t a :=
  (GB.homSpecEquiv T.left _).right_inv (rhoOf t a)

variable (N W) in
/-- The character `χ^m ∈ Γ(𝔸(N)_W)`. -/
def uch (m : N) : Γ((Yobj N W).left, ⊤) := (Yiota W).hom (AddMonoidAlgebra.single m 1)

variable (N W) in
/-- The universal point of `𝔸(N)` over `𝔸(N)_W`. -/
def univ : APt (OB Bsp) N (op (Yobj N W)) :=
  (show Multiplicative N →* Γ((Yobj N W).left, ⊤) from
    { toFun := fun m => uch N W (Multiplicative.toAdd m)
      map_one' := map_one (Yiota (N := N) W).hom
      map_mul' := fun m m' => by
        simp only [uch]
        rw [← map_mul, AddMonoidAlgebra.single_mul_single, mul_one]
        rfl })

lemma res_classify_univ {T : SB Bsp} (t : T ⟶ W) (a : APt (OB Bsp) N (op T)) :
    APt.res (classify t a).op (univ N W) = a := by
  refine MonoidHom.ext fun m => ?_
  have h := congrArg (fun k => k.hom (AddMonoidAlgebra.single (Multiplicative.toAdd m) 1))
    (classify_map t a)
  refine h.trans ?_
  rw [rhoOf_single, map_one, one_mul]
  rfl

lemma theta_basis :
    Function.Bijective (fun y : N →₀ Γ(W.left, ⊤) => y.sum fun m r =>
      ((Ypr N W).left.appTop.hom r) * uch N W m) := by
  let B := AddMonoidAlgebra.basis N Γ(W.left, ⊤)
  have e : (fun y : N →₀ Γ(W.left, ⊤) => y.sum fun m r =>
      ((Ypr N W).left.appTop.hom r) * uch N W m) =
      (Yiota (N := N) W) ∘ B.repr.symm := by
    funext y
    simp only [Function.comp, Module.Basis.repr_symm_apply, Finsupp.linearCombination_apply]
    rw [Finsupp.sum, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Ypr_map, Algebra.smul_def, map_mul]
    have hB : B m = AddMonoidAlgebra.single m 1 := by simp [B]
    rw [hB]
    rfl
  rw [e]
  exact (Yiota_bijective W).comp B.repr.symm.bijective

/-- `θ`: `⨁_{m ∈ N} F(W) → F(𝔸(N)_W)`, `f X^m ↦ χ^m f|`, is bijective: this is quasi-coherence, since
`Γ(𝔸(N)_W)` is free over `Γ(W)` on the characters. -/
theorem theta_bijective (hF : IsQCoh F) :
    Function.Bijective (fun x : N →₀ F.obj (op W) => evalE (Ypr N W) (univ N W) x) := by
  have h := IsBC.bijective (hF.base_change (Ypr N W)) (uch N W) (theta_basis (N := N))
  exact h

/-- A natural map `𝔸(N) → F` over `W` is determined by its value at the universal point. -/
lemma NC.eq_of_univ {c c' : NC F N W} (h : c.app (Ypr N W) (univ N W) = c'.app (Ypr N W) (univ N W)) :
    c = c' := by
  ext T t a
  have e : ∀ c : NC F N W, c.app t a = F.map (classify t a).op (c.app (Ypr N W) (univ N W)) := by
    intro c
    rw [← c.naturality, res_classify_univ, classify_pr]
  rw [e c, e c', h]

/-- **Proposition 9.12** over an affine scheme: natural maps `𝔸(N) → F` are `⨁_{m ∈ N} F(W)`. -/
theorem phiN_bijective (hF : IsQCoh F) : Function.Bijective (phiN (F := F) (N := N) (V := W)) := by
  constructor
  · intro x y h
    apply (theta_bijective (N := N) hF).1
    exact congrArg (fun c : NC F N W => c.app (Ypr N W) (univ N W)) h
  · intro c
    obtain ⟨x, hx⟩ := (theta_bijective (N := N) hF).2 (c.app (Ypr N W) (univ N W))
    exact ⟨x, NC.eq_of_univ hx⟩

end Eval

end AlgMag.S9B

/-! ### Proposition 9.12: sections of the sheaf `⨁ F_m` -/

namespace AlgMag.S9B

open CategoryTheory Opposite AlgebraicGeometry

open AlgMag.S9

open scoped Classical

section Sections

variable {F : PMod (OB Bsp)} {N : Type u} [AddCommMonoid N] [Countable N]

/-- Restriction of a family of coefficients. -/
def resF {V V' : SB Bsp} (s : V' ⟶ V) (x : N →₀ F.obj (op V)) : N →₀ F.obj (op V') :=
  x.mapRange (F.map s.op) (map_zero _)

@[simp] lemma resF_apply {V V' : SB Bsp} (s : V' ⟶ V) (x : N →₀ F.obj (op V)) (m : N) :
    resF s x m = F.map s.op (x m) := rfl

lemma evalE_resF {V V' T : SB Bsp} (s : V' ⟶ V) (t : T ⟶ V') (a : APt (OB Bsp) N (op T))
    (x : N →₀ F.obj (op V)) : evalE t a (resF s x) = evalE (t ≫ s) a x := by
  induction x using Finsupp.induction_linear with
  | zero => simp [resF]
  | add p q hp hq =>
    have : resF s (p + q) = resF s p + resF s q := by
      ext m; simp
    rw [this, map_add, map_add, hp, hq]
  | single m f =>
    have : resF s (Finsupp.single m f) = Finsupp.single m (F.map s.op f) := by
      simp [resF]
    rw [this, evalE_single, evalE_single, op_comp, F.map_comp]

lemma phiN_res {V V' : SB Bsp} (s : V' ⟶ V) (x : N →₀ F.obj (op V)) :
    (phiN x).res s = phiN (F := F) (resF s x) := by
  ext T t a
  exact (evalE_resF s t a x).symm

lemma NC.res_comp {V V' V'' : SB Bsp} (s : V' ⟶ V) (s' : V'' ⟶ V') (c : NC F N V) :
    c.res (s' ≫ s) = (c.res s).res s' := by
  ext T t a
  change c.app (t ≫ s' ≫ s) a = c.app ((t ≫ s') ≫ s) a
  rw [Category.assoc]

/-- A value at the identity of an arrow to `V`. -/
lemma NC.app_eq_res_id {V A : SB Bsp} (c : NC F N V) (a : A ⟶ V) (b : APt (OB Bsp) N (op A)) :
    c.app a b = (c.res a).app (𝟙 A) b := by
  change _ = c.app (𝟙 A ≫ a) b
  rw [Category.id_comp]

/-- `F` separated: natural maps agreeing over all affine schemes are equal. -/
lemma NC.ext_affine (hF : IsQCoh F) {V : SB Bsp} {c c' : NC F N V}
    (h : ∀ (A : SB Bsp) (a : A ⟶ V) [IsAffine A.left], c.res a = c'.res a) : c = c' := by
  ext T t a
  refine sep_affine hF T fun A e _ => ?_
  rw [← c.naturality, ← c'.naturality, NC.app_eq_res_id c, NC.app_eq_res_id c', h]

/-- **Proposition 9.12, first assertion**: a section over `V` of the sheaf `⨁_{m ∈ N} F_m`. Its
value on a quasi-compact scheme is the literal direct sum, so that a section is a compatible family
of finitely supported families over the affine schemes `A → V`. -/
@[ext]
structure Sec (F : PMod (OB Bsp)) (N : Type u) [AddCommMonoid N] (V : SB Bsp) where
  /-- the value on `a : A ⟶ V` -/
  val : ∀ (A : SB Bsp) (a : A ⟶ V) [IsAffine A.left], N →₀ F.obj (op A)
  compat : ∀ (A A' : SB Bsp) (s : A' ⟶ A) (a : A ⟶ V) [IsAffine A.left] [IsAffine A'.left],
    val A' (s ≫ a) = resF s (val A a)

variable (hF : IsQCoh F)

include hF

/-- The inverse of `phiN`, over an affine scheme. -/
def phiInv {W : SB Bsp} [IsAffine W.left] (c : NC F N W) : N →₀ F.obj (op W) :=
  (phiN_bijective hF).2 c |>.choose

lemma phiN_phiInv {W : SB Bsp} [IsAffine W.left] (c : NC F N W) : phiN (phiInv hF c) = c :=
  ((phiN_bijective hF).2 c).choose_spec

lemma phiInv_phiN {W : SB Bsp} [IsAffine W.left] (x : N →₀ F.obj (op W)) :
    phiInv hF (phiN x) = x :=
  (phiN_bijective hF).1 (phiN_phiInv hF _)

/-- A natural map gives a section of `⨁ F_m`. -/
def secOf {V : SB Bsp} (c : NC F N V) : Sec F N V where
  val A a _ := phiInv hF (c.res a)
  compat A A' s a _ _ := by
    refine (phiN_bijective hF).1 ?_
    rw [phiN_phiInv, ← phiN_res, phiN_phiInv, NC.res_comp]

/-- The section glued from a compatible family. -/
def glueV (T : SB Bsp) (val : ∀ (A : SB Bsp) (a : A ⟶ T) [IsAffine A.left], F.obj (op A))
    (compat : ∀ (A A' : SB Bsp) (s : A' ⟶ A) (a : A ⟶ T) [IsAffine A.left] [IsAffine A'.left],
      val A' (s ≫ a) = F.map s.op (val A a)) : F.obj (op T) :=
  (affine_glue hF T val compat).choose

lemma glueV_spec (T : SB Bsp) (val : ∀ (A : SB Bsp) (a : A ⟶ T) [IsAffine A.left], F.obj (op A))
    (compat : ∀ (A A' : SB Bsp) (s : A' ⟶ A) (a : A ⟶ T) [IsAffine A.left] [IsAffine A'.left],
      val A' (s ≫ a) = F.map s.op (val A a)) (A : SB Bsp) (a : A ⟶ T) [IsAffine A.left] :
    F.map a.op (glueV hF T val compat) = val A a :=
  (affine_glue hF T val compat).choose_spec.1 A a

omit hF in
lemma ofSec_compat {V : SB Bsp} (σ : Sec F N V) {T : SB Bsp} (t : T ⟶ V)
    (a : APt (OB Bsp) N (op T)) (A A' : SB Bsp) (s : A' ⟶ A) (e : A ⟶ T) [IsAffine A.left]
    [IsAffine A'.left] :
    evalE (𝟙 A') (APt.res (s ≫ e).op a) (σ.val A' ((s ≫ e) ≫ t)) =
      F.map s.op (evalE (𝟙 A) (APt.res e.op a) (σ.val A (e ≫ t))) := by
  rw [Category.assoc, σ.compat, evalE_resF, op_comp, APt.res_comp, ← evalE_res]
  simp

/-- A section of `⨁ F_m` gives a natural map. -/
def ofSec {V : SB Bsp} (σ : Sec F N V) : NC F N V where
  app {T} t a := glueV hF T (fun A e _ => evalE (𝟙 A) (APt.res e.op a) (σ.val A (e ≫ t)))
    (fun A A' s e _ _ => ofSec_compat σ t a A A' s e)
  naturality {T T'} s t a := by
    refine sep_affine hF T' fun A e _ => ?_
    rw [glueV_spec, ← F.map_comp, ← op_comp, glueV_spec, op_comp, APt.res_comp]
    simp only [Category.assoc]

lemma ofSec_app_spec {V : SB Bsp} (σ : Sec F N V) {T : SB Bsp} (t : T ⟶ V)
    (b : APt (OB Bsp) N (op T)) {E : SB Bsp} (e : E ⟶ T) [IsAffine E.left] :
    F.map e.op ((ofSec hF σ).app t b) = evalE (𝟙 E) (APt.res e.op b) (σ.val E (e ≫ t)) :=
  glueV_spec hF T _ (fun A A' s e _ _ => ofSec_compat σ t b A A' s e) E e

lemma ofSec_res {V : SB Bsp} (σ : Sec F N V) {A : SB Bsp} (a : A ⟶ V) [IsAffine A.left] :
    (ofSec hF σ).res a = phiN (σ.val A a) := by
  ext T t b
  refine sep_affine hF T fun E e _ => ?_
  change F.map e.op ((ofSec hF σ).app (t ≫ a) b) = F.map e.op (evalE t b (σ.val A a))
  rw [ofSec_app_spec, ← evalE_res, ← Category.assoc, σ.compat A E (e ≫ t) a, evalE_resF]
  simp

/-- **Proposition 9.12, first assertion**, for `𝔸(N)`: natural maps `𝔸(N)|_V → F|_V` are the sections
over `V` of `⨁_{m ∈ N} F_m`, for any `V`. -/
def ncEquivSec (V : SB Bsp) : NC F N V ≃ Sec F N V where
  toFun := secOf hF
  invFun := ofSec hF
  left_inv c := by
    refine NC.ext_affine hF fun A a _ => ?_
    rw [ofSec_res]
    exact phiN_phiInv hF _
  right_inv σ := by
    refine Sec.ext ?_
    funext A a inst
    change phiInv hF ((ofSec hF σ).res a) = _
    rw [ofSec_res, phiInv_phiN]

lemma secOf_val_phiN_res {V : SB Bsp} (c : NC F N V) {A : SB Bsp} (a : A ⟶ V) [IsAffine A.left] :
    phiN ((secOf hF c).val A a) = c.res a :=
  phiN_phiInv hF _

/-- The coefficient at `m` of a section of `⨁ F_m`. -/
def coef {V : SB Bsp} (σ : Sec F N V) (m : N) : F.obj (op V) :=
  glueV hF V (fun A a _ => σ.val A a m) (fun A A' s a _ _ => by rw [σ.compat, resF_apply])

lemma coef_spec {V : SB Bsp} (σ : Sec F N V) (m : N) {A : SB Bsp} (a : A ⟶ V) [IsAffine A.left] :
    F.map a.op (coef hF σ m) = σ.val A a m :=
  glueV_spec hF V _ _ A a

lemma coef_finite {V : SB Bsp} [CompactSpace V.left] (σ : Sec F N V) :
    (Function.support (coef hF σ)).Finite := by
  let 𝒰 : Scheme.OpenCover.{u} V.left := V.left.affineCover.finiteSubcover
  have hA : ∀ i, IsAffine (coverPiece V 𝒰 i).left := fun i => by
    change IsAffine (V.left.affineCover.X _)
    infer_instance
  have hfin : (⋃ i : 𝒰.I₀, ((σ.val _ (coverHom V 𝒰 i)).support : Set N)).Finite :=
    Set.finite_iUnion fun i => Finset.finite_toSet _
  refine hfin.subset fun m hm => ?_
  by_contra hc
  apply hm
  refine sep_cover hF V 𝒰 fun i => ?_
  rw [coef_spec, map_zero]
  by_contra hne
  exact hc (Set.mem_iUnion.mpr ⟨i, by simpa using hne⟩)

/-- **Proposition 9.12**, quasi-compact case: a section of `⨁ F_m` over `V` quasi-compact is an
element of the literal direct sum. -/
def xOf {V : SB Bsp} [CompactSpace V.left] (σ : Sec F N V) : N →₀ F.obj (op V) :=
  Finsupp.ofSupportFinite (coef hF σ) (coef_finite hF σ)

lemma resF_xOf {V : SB Bsp} [CompactSpace V.left] (σ : Sec F N V) {A : SB Bsp} (a : A ⟶ V)
    [IsAffine A.left] : resF a (xOf hF σ) = σ.val A a := by
  ext m
  exact coef_spec hF σ m a

/-- **Proposition 9.12**, quasi-compact case: `phiN` is a bijection from `⨁_{m ∈ N} F(V)` to the
natural maps `𝔸(N)|_V → F|_V`. Only the quasi-compactness of `V` is used. -/
theorem phiN_bijective_compact {V : SB Bsp} [CompactSpace V.left] :
    Function.Bijective (phiN (F := F) (N := N) (V := V)) := by
  constructor
  · intro x y h
    ext m
    refine sep_affine hF V fun A a _ => ?_
    have h1 : resF a x = resF a y := by
      refine (phiN_bijective hF).1 ?_
      rw [← phiN_res, ← phiN_res, h]
    exact congrArg (fun z => z m) h1
  · intro c
    refine ⟨xOf hF (secOf hF c), NC.ext_affine hF fun A a _ => ?_⟩
    rw [phiN_res, resF_xOf, secOf_val_phiN_res]

end Sections

end AlgMag.S9B

/-! ### Cochains of `𝔸(M)`, comodules, and the differential -/

namespace AlgMag.S9B

open CategoryTheory Opposite AlgebraicGeometry

open AlgMag.S9

open scoped Classical

section AM

variable {F : PMod (OB Bsp)} {M : Type u} [AddCommMonoid M] [Countable M]

lemma evalE_smul {N : Type u} [AddCommMonoid N] [Countable N] {V T : SB Bsp} (t : T ⟶ V)
    (a : APt (OB Bsp) N (op T)) (r : (OB Bsp).obj (op V)) (x : N →₀ F.obj (op V)) :
    evalE t a (r • x) = ((OB Bsp).map t.op).hom r • evalE t a x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [smul_add, map_add, hp, hq]
  | single m f =>
    rw [Finsupp.smul_single, evalE_single, evalE_single, F.map_smul, smul_comm]

/-- `(g₁,…,gₙ) ↦ (m ↦ ∏ gᵢ(mᵢ))`: `𝔸(M)ⁿ = 𝔸(Mⁿ)`. -/
def toPt {T : SB Bsp} {n : ℕ} (g : Fin n → APt (OB Bsp) M (op T)) :
    APt (OB Bsp) (Fin n → M) (op T) where
  toFun m := ∏ i, g i (Multiplicative.ofAdd (Multiplicative.toAdd m i))
  map_one' := by simp
  map_mul' a b := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← map_mul]
    rfl

@[simp] lemma toPt_ofAdd {T : SB Bsp} {n : ℕ} (g : Fin n → APt (OB Bsp) M (op T))
    (m : Fin n → M) :
    toPt g (Multiplicative.ofAdd m) = ∏ i, g i (Multiplicative.ofAdd (m i)) := rfl

/-- The components of a point of `𝔸(Mⁿ)`. -/
def ofPt {T : SB Bsp} {n : ℕ} (a : APt (OB Bsp) (Fin n → M) (op T)) :
    Fin n → APt (OB Bsp) M (op T) := fun i =>
  a.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.single (fun _ => M) i))

lemma toPt_ofPt {T : SB Bsp} {n : ℕ} (a : APt (OB Bsp) (Fin n → M) (op T)) :
    toPt (ofPt a) = a := by
  refine MonoidHom.ext fun m => ?_
  change ∏ i, a (Multiplicative.ofAdd (Pi.single i (Multiplicative.toAdd m i))) = a m
  rw [← map_prod, ← ofAdd_sum, Finset.univ_sum_single]
  rfl

lemma ofPt_toPt {T : SB Bsp} {n : ℕ} (g : Fin n → APt (OB Bsp) M (op T)) :
    ofPt (toPt g) = g := by
  funext i
  refine MonoidHom.ext fun m => ?_
  change ∏ j, g j (Multiplicative.ofAdd ((Pi.single i (Multiplicative.toAdd m) : Fin n → M) j)) = _
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

lemma toPt_res {T T' : SB Bsp} (s : T' ⟶ T) {n : ℕ} (g : Fin n → APt (OB Bsp) M (op T)) :
    toPt (fun i => APt.res s.op (g i)) = APt.res s.op (toPt g) := by
  refine MonoidHom.ext fun m => ?_
  simp [toPt]

/-- `Cⁿ(𝔸(M), F)` is the set of natural maps `𝔸(Mⁿ) → F`. -/
def cochainEquivNC (V : SB Bsp) (n : ℕ) : Cochain (Hm M Bsp) F V n ≃ NC F (Fin n → M) V where
  toFun c :=
    { app := fun t a => c.app t (ofPt a)
      naturality := fun s t a => c.naturality s t (ofPt a) }
  invFun c :=
    { app := fun t g => c.app t (toPt g)
      naturality := fun s t g =>
        (congrArg (c.app (s ≫ t)) (toPt_res s g)).trans (c.naturality s t (toPt g)) }
  left_inv c := by
    ext T t g
    exact congrArg (c.app t) (ofPt_toPt g)
  right_inv c := by
    ext T t a
    exact congrArg (c.app t) (toPt_ofPt a)

/-- The map `⨁_{m ∈ Mⁿ} F(V) → Cⁿ(𝔸(M)_V, F)`: `f X^{m₁}⋯X^{mₙ}` is the cochain
`(g₁,…,gₙ) ↦ g₁(m₁)⋯gₙ(mₙ) f`. -/
def phiC (V : SB Bsp) (n : ℕ) :
    ((Fin n → M) →₀ F.obj (op V)) →ₗ[(OB Bsp).obj (op V)] Cochain (Hm M Bsp) F V n where
  toFun x := (cochainEquivNC V n).symm (phiN x)
  map_add' x y := by
    ext T t g
    exact map_add (evalE t (toPt g)) x y
  map_smul' r x := by
    ext T t g
    exact evalE_smul t (toPt g) r x

lemma phiC_app (V : SB Bsp) (n : ℕ) (x : (Fin n → M) →₀ F.obj (op V)) {T : SB Bsp} (t : T ⟶ V)
    (g : Fin n → APt (OB Bsp) M (op T)) :
    (phiC V n x).app t g = evalE t (toPt g) x := rfl

lemma phiC_res {V V' : SB Bsp} (s : V' ⟶ V) (n : ℕ) (x : (Fin n → M) →₀ F.obj (op V)) :
    (phiC V n x).res s = phiC V' n (resF s x) := by
  ext T t g
  exact (evalE_resF s t _ x).symm

variable (hF : IsQCoh F)

include hF

/-- **Proposition 9.12, first assertion**: for any `V`,
`Cⁿ(𝔸(M)_B, F)(V) = (⨁_{(m₁,…,mₙ)} F X^{m₁}⋯X^{mₙ})(V)`. -/
def cochainEquivSec (V : SB Bsp) (n : ℕ) : Cochain (Hm M Bsp) F V n ≃ Sec F (Fin n → M) V :=
  (cochainEquivNC V n).trans (ncEquivSec hF V)

/-- **Proposition 9.12**, quasi-compact case: `Cⁿ(𝔸(M)_B, F)(V) = ⨁_{m ∈ Mⁿ} F_m(V)` as
`𝒪(V)`-modules. -/
theorem phiC_bijective (V : SB Bsp) [CompactSpace V.left] (n : ℕ) :
    Function.Bijective (phiC (F := F) (M := M) V n) :=
  (cochainEquivNC V n).symm.bijective.comp (phiN_bijective_compact hF)

/-- **Proposition 9.12**, quasi-compact case, as an isomorphism. -/
def cochainLinearEquiv (V : SB Bsp) [CompactSpace V.left] (n : ℕ) :
    ((Fin n → M) →₀ F.obj (op V)) ≃ₗ[(OB Bsp).obj (op V)] Cochain (Hm M Bsp) F V n :=
  LinearEquiv.ofBijective (phiC V n) (phiC_bijective hF V n)

omit hF

lemma cochain_ext_affine (hF : IsQCoh F) {V : SB Bsp} {n : ℕ} {c c' : Cochain (Hm M Bsp) F V n}
    (h : ∀ (A : SB Bsp) (a : A ⟶ V) [IsAffine A.left], c.res a = c'.res a) : c = c' := by
  apply (cochainEquivNC V n).injective
  refine NC.ext_affine hF fun A a _ => ?_
  ext T t b
  exact congrArg (fun k : Cochain (Hm M Bsp) F A n => k.app t (ofPt b)) (h A a)

/-! ### Comodule structure on sections (Proposition 9.10 for `𝔸(M)`) -/

variable (A : HModule (Hm M Bsp) F)

/-- The action of a point of `𝔸(M)`. -/
def asmul {T : SB Bsp} (a : APt (OB Bsp) M (op T)) (x : F.obj (op T)) : F.obj (op T) :=
  A.smul (U := op T) a x

lemma asmul_add {T : SB Bsp} (a : APt (OB Bsp) M (op T)) (x y : F.obj (op T)) :
    asmul A a (x + y) = asmul A a x + asmul A a y := A.smul_add _ _ _

lemma asmul_zero {T : SB Bsp} (a : APt (OB Bsp) M (op T)) :
    asmul A a (0 : F.obj (op T)) = 0 := A.smul_zero _

lemma asmul_smul {T : SB Bsp} (a : APt (OB Bsp) M (op T)) (r : (OB Bsp).obj (op T))
    (x : F.obj (op T)) : asmul A a (r • x) = r • asmul A a x := A.smul_smul _ _ _

lemma asmul_one {T : SB Bsp} (x : F.obj (op T)) :
    asmul A (1 : APt (OB Bsp) M (op T)) x = x := A.one_smul x

lemma asmul_mul {T : SB Bsp} (g h : APt (OB Bsp) M (op T)) (x : F.obj (op T)) :
    asmul A (g * h) x = asmul A g (asmul A h x) := A.mul_smul _ _ _

lemma asmul_map {T T' : SB Bsp} (s : T' ⟶ T) (a : APt (OB Bsp) M (op T)) (x : F.obj (op T)) :
    F.map s.op (asmul A a x) = asmul A (APt.res s.op a) (F.map s.op x) := A.map_smul _ _ _

lemma asmul_sum {ι : Type*} {T : SB Bsp} (g : APt (OB Bsp) M (op T)) (s : Finset ι)
    (f : ι → F.obj (op T)) : asmul A g (∑ i ∈ s, f i) = ∑ i ∈ s, asmul A g (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using asmul_zero A g
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, asmul_add, ih]

/-- The orbit map `g ↦ g • v|_T`. -/
def orbit {V : SB Bsp} (v : F.obj (op V)) : NC F M V where
  app t a := asmul A a (F.map t.op v)
  naturality s t a := by
    rw [asmul_map, ← F.map_comp, ← op_comp]

/-- `ρ`, on the sections over `V` quasi-compact (Proposition 9.10): `ρ(v) = ∑ ρ_m(v) X^m` is the
unique element such that `g • v = ∑ g(m) ρ_m(v)`. -/
def rhoV (hF : IsQCoh F) {V : SB Bsp} [CompactSpace V.left] (v : F.obj (op V)) : M →₀ F.obj (op V) :=
  ((phiN_bijective_compact hF (N := M) (V := V)).2 (orbit A v)).choose

variable {A}

lemma smul_eq_evalE (hF : IsQCoh F) {V : SB Bsp} [CompactSpace V.left] (v : F.obj (op V))
    {T : SB Bsp} (t : T ⟶ V) (a : APt (OB Bsp) M (op T)) :
    asmul A a (F.map t.op v) = evalE t a (rhoV A hF v) :=
  (congrArg (fun c : NC F M V => c.app t a)
    ((phiN_bijective_compact hF (N := M) (V := V)).2 (orbit A v)).choose_spec).symm

lemma rhoV_eq (hF : IsQCoh F) {V : SB Bsp} [CompactSpace V.left] (v : F.obj (op V))
    (x : M →₀ F.obj (op V))
    (h : ∀ {T : SB Bsp} (t : T ⟶ V) (a : APt (OB Bsp) M (op T)),
      evalE t a x = asmul A a (F.map t.op v)) : rhoV A hF v = x := by
  refine (phiN_bijective_compact hF (N := M) (V := V)).1 ?_
  ext T t a
  change evalE t a (rhoV A hF v) = evalE t a x
  rw [h, smul_eq_evalE hF]

lemma evalE_sum {N : Type u} [AddCommMonoid N] [Countable N] {V T : SB Bsp} (t : T ⟶ V)
    (a : APt (OB Bsp) N (op T)) (x : N →₀ F.obj (op V)) :
    evalE t a x = x.sum fun m f => a (Multiplicative.ofAdd m) • F.map t.op f := by
  rfl

/-- The left component `g` of a point of `𝔸(M × M)`. -/
def ptL {T : SB Bsp} (a : APt (OB Bsp) (M × M) (op T)) : APt (OB Bsp) M (op T) :=
  a.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inl M M))

/-- The right component `h` of a point of `𝔸(M × M)`. -/
def ptR {T : SB Bsp} (a : APt (OB Bsp) (M × M) (op T)) : APt (OB Bsp) M (op T) :=
  a.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inr M M))

lemma pt_pair {T : SB Bsp} (a : APt (OB Bsp) (M × M) (op T)) (m k : M) :
    a (Multiplicative.ofAdd (m, k)) =
      ptL a (Multiplicative.ofAdd m) * ptR a (Multiplicative.ofAdd k) := by
  rw [ptL, ptR, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_mul]
  congr 1
  change Multiplicative.ofAdd (m, k) = Multiplicative.ofAdd ((m, 0) + (0, k))
  simp

/-- **Proposition 9.10** for `𝔸(M)`, on sections over `V` quasi-compact: an action gives an
`𝒪(V)[M]`-comodule structure on `F(V)`, the two formulas being `g • v = ∑ g(m) ρ_m(v)`. -/
def coactionOf (hF : IsQCoh F) (A : HModule (Hm M Bsp) F) (V : SB Bsp) [CompactSpace V.left] :
    Hochschild.Coaction ((OB Bsp).obj (op V)) M (F.obj (op V)) where
  ρ :=
    { toFun := rhoV A hF
      map_add' := fun v w => by
        refine rhoV_eq hF _ _ fun t a => ?_
        rw [map_add, map_add, ← smul_eq_evalE, ← smul_eq_evalE, asmul_add]
      map_smul' := fun r v => by
        refine rhoV_eq hF _ _ fun t a => ?_
        rw [RingHom.id_apply, evalE_smul, ← smul_eq_evalE, F.map_smul, asmul_smul] }
  coassoc := fun v => by
    refine (phiN_bijective_compact hF (N := M × M) (V := V)).1 ?_
    ext T t a
    change evalE t a _ = evalE t a _
    set x := rhoV A hF v with hx
    have key1 : ∀ (k : M) (z : M →₀ F.obj (op V)),
        evalE t a (z.mapDomain fun m => (m, k)) =
          ptR a (Multiplicative.ofAdd k) • evalE t (ptL a) z := by
      intro k z
      induction z using Finsupp.induction_linear with
      | zero => simp
      | add p q hp hq => simp only [Finsupp.mapDomain_add, map_add, smul_add, hp, hq]
      | single m f =>
        rw [Finsupp.mapDomain_single, evalE_single, evalE_single, pt_pair, mul_comm, mul_smul]
    have key2 : ∀ z : M →₀ F.obj (op V),
        evalE t a (z.mapDomain fun m => (m, m)) = evalE t (ptL a * ptR a) z := by
      intro z
      induction z using Finsupp.induction_linear with
      | zero => simp
      | add p q hp hq => simp only [Finsupp.mapDomain_add, map_add, hp, hq]
      | single m f =>
        rw [Finsupp.mapDomain_single, evalE_single, evalE_single, pt_pair]
        rfl
    change evalE t a (x.sum fun k y => (rhoV A hF y).mapDomain fun m => (m, k)) =
      evalE t a (x.mapDomain fun m => (m, m))
    rw [key2, ← smul_eq_evalE hF v, Finsupp.sum, map_sum]
    simp only [key1, ← smul_eq_evalE hF]
    have hmul := asmul_mul A (ptL a) (ptR a) (F.map t.op v)
    refine Eq.trans ?_ hmul.symm
    rw [smul_eq_evalE hF v t (ptR a), evalE_sum, Finsupp.sum, asmul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact (asmul_smul A (ptL a) _ _).symm
  counit := fun v => by
    have h := smul_eq_evalE (A := A) hF v (𝟙 V) 1
    have h1 : asmul A (1 : APt (OB Bsp) M (op V)) (F.map (𝟙 V).op v) = v := by
      rw [op_id, F.map_id, asmul_one]
    rw [h1, evalE_sum] at h
    refine Eq.trans ?_ h.symm
    refine Finsupp.sum_congr fun m _ => ?_
    rw [op_id, F.map_id]
    change _ = (1 : (OB Bsp).obj (op V)) • _
    rw [one_smul]

end AM

end AlgMag.S9B

/-! ### Proposition 9.12, the differential; Proposition 9.13, Remark 9.14 -/

namespace AlgMag.S9B

open CategoryTheory Opposite AlgebraicGeometry

open AlgMag.S9

open scoped Classical

section Diff

variable {F : PMod (OB Bsp)} {M : Type u} [AddCommMonoid M] [Countable M]

open Hochschild in
private lemma toPt_cons {T : SB Bsp} {n : ℕ} (g : Fin (n + 1) → APt (OB Bsp) M (op T)) (k : M)
    (m : Fin n → M) :
    toPt g (Multiplicative.ofAdd (consW k m)) =
      g 0 (Multiplicative.ofAdd k) * toPt (fun i => g i.succ) (Multiplicative.ofAdd m) := by
  simp only [toPt_ofAdd]
  rw [Fin.prod_univ_succ]
  simp [consW]

open Hochschild in
private lemma toPt_snoc {T : SB Bsp} {n : ℕ} (g : Fin (n + 1) → APt (OB Bsp) M (op T))
    (m : Fin n → M) :
    toPt g (Multiplicative.ofAdd (snoc0 m)) =
      toPt (fun i => g i.castSucc) (Multiplicative.ofAdd m) := by
  simp only [toPt_ofAdd]
  rw [Fin.prod_univ_castSucc]
  simp only [snoc0, Fin.snoc_last, Fin.snoc_castSucc, ofAdd_zero, map_one, mul_one]

private lemma val_predAbove' {n : ℕ} (p : Fin n) (i : Fin (n + 1)) :
    (Fin.predAbove p i : ℕ) = if (p : ℕ) < i then (i : ℕ) - 1 else i := by
  unfold Fin.predAbove
  by_cases h : p.castSucc < i
  · have h' : (p : ℕ) < i := by simpa [Fin.lt_def] using h
    simp [h, h']
  · have h' : ¬ (p : ℕ) < i := by simpa [Fin.lt_def] using h
    simp [h, h']

private lemma val_succAbove' {n : ℕ} (i l : Fin n) :
    (i.castSucc.succAbove l : ℕ) = if (l : ℕ) < i then (l : ℕ) else l + 1 := by
  unfold Fin.succAbove
  by_cases h : (l : ℕ) < i
  · have h' : l.castSucc < i.castSucc := h
    rw [if_pos h', if_pos h]
    rfl
  · have h' : ¬ l.castSucc < i.castSucc := h
    rw [if_neg h', if_neg h]
    rfl

open Hochschild in
private lemma toPt_dup {T : SB Bsp} {n : ℕ} (i : Fin n)
    (g : Fin (n + 1) → APt (OB Bsp) M (op T)) (m : Fin n → M) :
    toPt g (Multiplicative.ofAdd (dupWord i m)) =
      toPt (merge i g) (Multiplicative.ofAdd m) := by
  simp only [toPt_ofAdd, dupWord, Function.comp]
  rw [Fin.prod_univ_succAbove _ i.castSucc]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun l => merge i g l _) (Finset.mem_univ i)]
  have hp : ∀ l : Fin n, Fin.predAbove i (i.castSucc.succAbove l) = l := by
    intro l
    ext
    rw [val_predAbove', val_succAbove']
    split_ifs <;> omega
  simp only [hp]
  have hpi : Fin.predAbove i i.castSucc = i := by
    ext
    rw [val_predAbove']
    simp
  rw [hpi, ← mul_assoc]
  congr 1
  · have : i.castSucc.succAbove i = i.succ := by
      ext
      rw [val_succAbove']
      simp
    rw [this]
    simp only [merge, lt_irrefl, if_false, if_true]
    rfl
  · refine Finset.prod_congr rfl fun l hl => ?_
    have hne : (l : ℕ) ≠ i := fun h => (Finset.ne_of_mem_erase hl) (Fin.ext h)
    have e : merge i g l = g (i.castSucc.succAbove l) := by
      simp only [merge]
      by_cases h : (l : ℕ) < i
      · rw [if_pos h]
        congr 1
        ext
        rw [val_succAbove', if_pos h]
        rfl
      · rw [if_neg h, if_neg hne]
        congr 1
        ext
        rw [val_succAbove', if_neg h]
        rfl
    rw [e]

variable (hF : IsQCoh F) (A : HModule (Hm M Bsp) F)

private lemma delta_phiC_single (V : SB Bsp) [CompactSpace V.left] (n : ℕ) (m : Fin n → M)
    (f : F.obj (op V)) {T : SB Bsp} (t : T ⟶ V) (g : Fin (n + 1) → APt (OB Bsp) M (op T)) :
    deltaFun A (phiC V n (Finsupp.single m f)) t g =
      evalE t (toPt g) ((coactionOf hF A V).delta n (Finsupp.single m f)) := by
  rw [Hochschild.Coaction.delta_single, map_add, map_add, map_sum, map_zsmul]
  have hmap : ∀ (z : M →₀ F.obj (op V)),
      evalE t (toPt g) (z.mapDomain fun k => Hochschild.consW k m) =
        toPt (fun i => g i.succ) (Multiplicative.ofAdd m) • evalE t (g 0) z := by
    intro z
    induction z using Finsupp.induction_linear with
    | zero => simp
    | add p q hp hq => simp only [Finsupp.mapDomain_add, map_add, smul_add, hp, hq]
    | single k y =>
      rw [Finsupp.mapDomain_single, evalE_single, evalE_single, toPt_cons, mul_comm, mul_smul]
  have h1 := smul_eq_evalE (A := A) hF f t (g 0)
  have h2 : A.smul (U := op T) (g 0) (toPt (fun i => g i.succ) (Multiplicative.ofAdd m) • F.map t.op f) =
      toPt (fun i => g i.succ) (Multiplicative.ofAdd m) • evalE t (g 0) (rhoV A hF f) := by
    rw [← h1]
    exact asmul_smul A (g 0) _ _
  simp only [deltaFun, phiC_app, evalE_single, map_zsmul, toPt_snoc, toPt_dup]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (h2.trans (hmap _).symm)
    (Finset.sum_congr rfl fun i _ => congrArg (fun y => ((-1 : ℤ) ^ ((i : ℕ) + 1)) • y)
      ((phiC_app V n _ t (merge i g)).trans (evalE_single t _ m f)))) rfl

/-- **Proposition 9.12, second assertion**: on quasi-compact objects, the differential of
Definition 9.4 is given by the formula
`f X^{m₁}⋯X^{mₙ} ↦ ρ(f) X^{m₁}⋯X^{mₙ} + ∑ (-1)^i f X^{m₁}⋯Δ(X^{mᵢ})⋯X^{mₙ} + (-1)^{n+1} f X^{m₁}⋯X^{mₙ} X^0`,
that is `AlgMag.Hochschild.Coaction.delta`. -/
theorem delta_phiC (V : SB Bsp) [CompactSpace V.left] (n : ℕ) (x : (Fin n → M) →₀ F.obj (op V)) :
    delta A (phiC V n x) = phiC V (n + 1) ((coactionOf hF A V).delta n x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single m f =>
    ext T t g
    exact delta_phiC_single hF A V n m f t g

lemma phiC_eq (B : SB Bsp) (n : ℕ) (y : (Fin n → M) →₀ F.obj (op B)) :
    phiC B n y = (cochainEquivNC B n).symm (phiN y) := rfl

lemma equivNC_res_symm {V B : SB Bsp} {n : ℕ} (c' : NC F (Fin n → M) V) (a : B ⟶ V) :
    cochainEquivNC B n (((cochainEquivNC V n).symm c').res a) = c'.res a := by
  ext T t b
  exact congrArg (c'.app (t ≫ a)) (toPt_ofPt b)

/-- A cochain over an affine scheme is its section. -/
lemma phiC_sec {V : SB Bsp} {n : ℕ} (c : Cochain (Hm M Bsp) F V n) {B : SB Bsp} (a : B ⟶ V)
    [IsAffine B.left] : phiC B n ((cochainEquivSec hF V n c).val B a) = c.res a := by
  rw [phiC_eq, Equiv.symm_apply_eq]
  exact secOf_val_phiN_res hF (cochainEquivNC V n c) a

lemma res_symm_sec {V : SB Bsp} {n : ℕ} (τ : Sec F (Fin n → M) V) {B : SB Bsp} (a : B ⟶ V)
    [IsAffine B.left] : ((cochainEquivSec hF V n).symm τ).res a = phiC B n (τ.val B a) := by
  rw [phiC_eq, Equiv.eq_symm_apply]
  exact (equivNC_res_symm _ a).trans (ofSec_res hF τ a)

include hF

/-- **Proposition 9.13 and Remark 9.14**: over any `V`, with no assumption on `V`, every cocycle in
degree `n + 1` is a coboundary. -/
theorem exists_delta_eq (V : SB Bsp) (n : ℕ) (c : Cochain (Hm M Bsp) F V (n + 1))
    (hc : delta A c = 0) : ∃ e, delta A e = c := by
  let σ := cochainEquivSec hF V (n + 1) c
  have hx : ∀ (B : SB Bsp) (a : B ⟶ V) [IsAffine B.left],
      (coactionOf hF A B).delta (n + 1) (σ.val B a) = 0 := by
    intro B a _
    refine (phiC_bijective hF B (n + 2)).1 ?_
    rw [← delta_phiC, phiC_sec, map_zero, delta_res, hc]
    rfl
  let τ : Sec F (Fin n → M) V :=
    { val := fun B a _ =>
        ((-1 : ℤ) ^ (n + 1)) • Hochschild.lastCoeff M (F.obj (op B)) ((OB Bsp).obj (op B)) n
          (σ.val B a)
      compat := fun B B' s a _ _ => by
        rw [σ.compat]
        ext u
        change ((-1 : ℤ) ^ (n + 1)) • F.map s.op _ = F.map s.op (((-1 : ℤ) ^ (n + 1)) • _)
        rw [map_zsmul]
        rfl }
  refine ⟨(cochainEquivSec hF V n).symm τ, cochain_ext_affine hF fun B a _ => ?_⟩
  rw [← delta_res, res_symm_sec, delta_phiC hF A, ← phiC_sec hF c a]
  congr 1
  exact ((coactionOf hF A B).eq_delta_of_cocycle n _ (hx B a)).symm

/-- **Proposition 9.13**: `H¹_monoid(𝔸(M)_B, F) = 0`, for any base and any object `V`. -/
theorem H1_subsingleton (V : SB Bsp) : Subsingleton (Hn A V 1) :=
  Hn_subsingleton_of A V 0 (exists_delta_eq hF A V 0)

/-- **Remark 9.14** (the paper's conjecture, proved): `Hⁿ_monoid(𝔸(M)_B, F) = 0` for all `n ≥ 1`, for
any base and any object `V`. -/
theorem Hn_subsingleton (V : SB Bsp) (n : ℕ) : Subsingleton (Hn A V (n + 1)) :=
  Hn_subsingleton_of A V n (exists_delta_eq hF A V n)

end Diff

end AlgMag.S9B

/-! ### Proposition 9.11 -/

namespace AlgMag.S9B

open CategoryTheory Opposite AlgebraicGeometry

open AlgMag.S9

open scoped Classical

section P911

variable {F : PMod (OB Bsp)} {M : Type u} [AddCommMonoid M] [Countable M]

variable (F M) in
/-- **Proposition 9.11**, corrected wording: a family `(ρ_m)_{m ∈ M}` in `Hom_𝒪(F, F)` of orthogonal
idempotents, such that `∑ ρ_m = Id` and, **at each section** over an affine scheme, only finitely
many of the `ρ_m` are nonzero. The printed "only finitely many of the `(ρ_m)` are nonzero locally" is
false: see `AlgMag.Hochschild.regular_comp_ne_zero`. -/
structure Decomp where
  /-- `ρ_m`, on `T` -/
  comp : M → ∀ T : SB Bsp, F.obj (op T) →ₗ[(OB Bsp).obj (op T)] F.obj (op T)
  natural : ∀ (m : M) {T T' : SB Bsp} (s : T' ⟶ T) (v : F.obj (op T)),
    comp m T' (F.map s.op v) = F.map s.op (comp m T v)
  finite : ∀ (T : SB Bsp) [IsAffine T.left] (v : F.obj (op T)),
    (Function.support fun m => comp m T v).Finite
  same : ∀ (m : M) (T : SB Bsp) (v : F.obj (op T)), comp m T (comp m T v) = comp m T v
  ne : ∀ (m k : M) (T : SB Bsp) (v : F.obj (op T)), k ≠ m → comp m T (comp k T v) = 0
  sum : ∀ (T : SB Bsp) [IsAffine T.left] (v : F.obj (op T)), ∑ᶠ m, comp m T v = v

variable (hF : IsQCoh F) (A : HModule (Hm M Bsp) F)

lemma orbit_res {V V' : SB Bsp} (s : V' ⟶ V) (v : F.obj (op V)) :
    (orbit A v).res s = orbit A (F.map s.op v) := by
  ext T t a
  change asmul A a (F.map (t ≫ s).op v) = asmul A a (F.map t.op (F.map s.op v))
  rw [op_comp, F.map_comp]

/-- The component `ρ_m(v)` of `v ∈ F(T)`, for any `T`: glued from the affine schemes over `T`. -/
def compOf (m : M) {T : SB Bsp} (v : F.obj (op T)) : F.obj (op T) :=
  coef hF (secOf hF (orbit A v)) m

lemma map_compOf (m : M) {T E : SB Bsp} (e : E ⟶ T) [IsAffine E.left] (v : F.obj (op T)) :
    F.map e.op (compOf hF A m v) = rhoV A hF (F.map e.op v) m := by
  rw [compOf, coef_spec]
  have : (secOf hF (orbit A v)).val E e = rhoV A hF (F.map e.op v) := by
    refine (phiN_bijective hF).1 ?_
    rw [secOf_val_phiN_res, orbit_res]
    exact ((phiN_bijective_compact hF (N := M) (V := E)).2 (orbit A _)).choose_spec.symm
  rw [this]

lemma compOf_affine (m : M) {T : SB Bsp} [IsAffine T.left] (v : F.obj (op T)) :
    compOf hF A m v = rhoV A hF v m := by
  have := map_compOf hF A m (𝟙 T) v
  rw [op_id, F.map_id, F.map_id] at this
  exact this

lemma rhoV_comp (m k : M) {E : SB Bsp} [IsAffine E.left] (w : F.obj (op E)) :
    rhoV A hF (rhoV A hF w k) m = open Classical in if m = k then rhoV A hF w k else 0 :=
  (coactionOf hF A E).comp_comp m k w

/-- **Proposition 9.11**, from the action to the family. -/
def decompOf : Decomp F M where
  comp m T :=
    { toFun := compOf hF A m
      map_add' := fun v w => by
        refine sep_affine hF T fun E e _ => ?_
        rw [map_compOf, map_add, map_add, map_compOf, map_compOf]
        exact congrArg (fun z : M →₀ F.obj (op E) => z m)
          ((coactionOf hF A E).ρ.map_add _ _)
      map_smul' := fun r v => by
        refine sep_affine hF T fun E e _ => ?_
        rw [RingHom.id_apply, map_compOf, F.map_smul, F.map_smul, map_compOf]
        exact congrArg (fun z : M →₀ F.obj (op E) => z m)
          ((coactionOf hF A E).ρ.map_smul _ _) }
  natural m {T T'} s v := by
    change compOf hF A m _ = F.map s.op (compOf hF A m v)
    refine sep_affine hF T' fun E e _ => ?_
    have h := map_compOf hF A m (e ≫ s) v
    rw [op_comp, F.map_comp, F.map_comp] at h
    rw [map_compOf hF A m e]
    exact h.symm
  finite T _ v := by
    have hs : (Function.support fun m => compOf hF A m v) ⊆ (rhoV A hF v).support := by
      intro m hm
      have : compOf hF A m v ≠ 0 := hm
      rw [compOf_affine] at this
      simpa using this
    exact (Finset.finite_toSet _).subset hs
  same m T v := by
    change compOf hF A m (compOf hF A m v) = compOf hF A m v
    refine sep_affine hF T fun E e _ => ?_
    rw [map_compOf, map_compOf, rhoV_comp]
    simp
  ne m k T v h := by
    change compOf hF A m (compOf hF A k v) = 0
    refine sep_affine hF T fun E e _ => ?_
    rw [map_compOf, map_compOf, rhoV_comp, map_zero, if_neg (Ne.symm h)]
  sum T _ v := by
    change ∑ᶠ m, compOf hF A m v = v
    simp only [compOf_affine]
    have hs : (Function.support fun m => rhoV A hF v m) ⊆ (rhoV A hF v).support := by
      intro m hm
      simpa using hm
    rw [finsum_eq_sum_of_support_subset _ hs]
    exact (coactionOf hF A T).counit v

/-- The family `ρ_m` at quasi-compact objects is also finite at each section. -/
theorem decompOf_finite_of_compact {T : SB Bsp} [CompactSpace T.left] (v : F.obj (op T)) :
    (Function.support fun m => compOf hF A m v).Finite :=
  coef_finite hF _

variable (D : Decomp F M)

/-- The element `∑ ρ_m(w) X^m`, for `w` a section over an affine scheme. -/
def tval {E : SB Bsp} [IsAffine E.left] (w : F.obj (op E)) : M →₀ F.obj (op E) :=
  Finsupp.ofSupportFinite (fun m => D.comp m E w) (D.finite E w)

@[simp] lemma tval_apply {E : SB Bsp} [IsAffine E.left] (w : F.obj (op E)) (m : M) :
    tval D w m = D.comp m E w := rfl

lemma tval_res {E E' : SB Bsp} [IsAffine E.left] [IsAffine E'.left] (s : E' ⟶ E)
    (w : F.obj (op E)) : tval D (F.map s.op w) = resF s (tval D w) := by
  ext m
  exact D.natural m s w

/-- The section of `⨁ F_m` of `v ∈ F(T)`. -/
def tsec {T : SB Bsp} (v : F.obj (op T)) : Sec F M T where
  val E e _ := tval D (F.map e.op v)
  compat E E' s e _ _ := by
    rw [op_comp, F.map_comp, tval_res]

include hF in
/-- **Proposition 9.11**, from the family to the action. -/
def dsmul {T : SB Bsp} (g : APt (OB Bsp) M (op T)) (v : F.obj (op T)) : F.obj (op T) :=
  (ofSec hF (tsec D v)).app (𝟙 T) g

lemma map_dsmul {T E : SB Bsp} (e : E ⟶ T) [IsAffine E.left] (g : APt (OB Bsp) M (op T))
    (v : F.obj (op T)) :
    F.map e.op (dsmul hF D g v) = evalE (𝟙 E) (APt.res e.op g) (tval D (F.map e.op v)) := by
  rw [dsmul, ofSec_app_spec]
  change evalE _ _ (tval D (F.map (e ≫ 𝟙 T).op v)) = _
  rw [Category.comp_id]

/-- `evalE` at the identity. -/
lemma evalE_id {E : SB Bsp} (a : APt (OB Bsp) M (op E)) (x : M →₀ F.obj (op E)) :
    evalE (𝟙 E) a x = x.sum fun m f => a (Multiplicative.ofAdd m) • f := by
  rw [evalE_sum]
  refine Finsupp.sum_congr fun m _ => ?_
  rw [op_id, F.map_id]

lemma comp_evalE_tval (m : M) {E : SB Bsp} [IsAffine E.left] (a : APt (OB Bsp) M (op E))
    (w : F.obj (op E)) :
    D.comp m E (evalE (𝟙 E) a (tval D w)) = a (Multiplicative.ofAdd m) • D.comp m E w := by
  rw [evalE_id, Finsupp.sum, map_sum]
  simp only [map_smul]
  rw [Finset.sum_eq_single m]
  · simp only [tval_apply, D.same]
  · intro k _ hk
    simp only [tval_apply, D.ne m k E w hk, smul_zero]
  · intro hm
    have : D.comp m E w = 0 := by simpa using hm
    simp [this]

lemma evalE_tval_mul {E : SB Bsp} [IsAffine E.left] (g h : APt (OB Bsp) M (op E))
    (w : F.obj (op E)) :
    evalE (𝟙 E) (g * h) (tval D w) = evalE (𝟙 E) g (tval D (evalE (𝟙 E) h (tval D w))) := by
  have hs : (tval D (evalE (𝟙 E) h (tval D w))).support ⊆ (tval D w).support := by
    intro m hm
    rw [Finsupp.mem_support_iff] at hm ⊢
    intro h0
    apply hm
    change D.comp m E _ = 0
    rw [comp_evalE_tval]
    have : D.comp m E w = 0 := h0
    rw [this, smul_zero]
  rw [evalE_id, evalE_id, Finsupp.sum, Finsupp.sum, Finset.sum_subset hs]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [tval_apply D (evalE _ _ _), comp_evalE_tval, smul_smul]
    rfl
  · intro m _ hm
    rw [Finsupp.notMem_support_iff.mp hm, smul_zero]

lemma dsmul_one {T : SB Bsp} (v : F.obj (op T)) :
    dsmul hF D (1 : APt (OB Bsp) M (op T)) v = v := by
  refine sep_affine hF T fun E e _ => ?_
  rw [map_dsmul, evalE_id]
  have h1 : APt.res e.op (1 : APt (OB Bsp) M (op T)) = 1 := by
    refine MonoidHom.ext fun p => ?_
    simp
  rw [h1]
  have hs : (Function.support fun m => D.comp m E (F.map e.op v)) ⊆
      (tval D (F.map e.op v)).support := by
    intro m hm
    simpa using hm
  conv_rhs => rw [← D.sum E (F.map e.op v), finsum_eq_sum_of_support_subset _ hs]
  refine Finset.sum_congr rfl fun m _ => ?_
  change (1 : (OB Bsp).obj (op E)) • _ = _
  rw [one_smul]
  rfl

lemma dsmul_mul {T : SB Bsp} (g h : APt (OB Bsp) M (op T)) (v : F.obj (op T)) :
    dsmul hF D (g * h) v = dsmul hF D g (dsmul hF D h v) := by
  refine sep_affine hF T fun E e _ => ?_
  rw [map_dsmul, map_dsmul, map_dsmul, APt.res_mul, evalE_tval_mul]

lemma dsmul_add {T : SB Bsp} (g : APt (OB Bsp) M (op T)) (v w : F.obj (op T)) :
    dsmul hF D g (v + w) = dsmul hF D g v + dsmul hF D g w := by
  refine sep_affine hF T fun E e _ => ?_
  have h : tval D (F.map e.op (v + w)) = tval D (F.map e.op v) + tval D (F.map e.op w) := by
    ext m
    rw [map_add]
    exact (D.comp m E).map_add _ _
  rw [map_add (F.map e.op) (dsmul hF D g v), map_dsmul, map_dsmul, map_dsmul, h, map_add]

lemma dsmul_smul {T : SB Bsp} (g : APt (OB Bsp) M (op T)) (a : (OB Bsp).obj (op T))
    (v : F.obj (op T)) : dsmul hF D g (a • v) = a • dsmul hF D g v := by
  refine sep_affine hF T fun E e _ => ?_
  rw [F.map_smul, map_dsmul, map_dsmul, F.map_smul]
  have : tval D (((OB Bsp).map e.op).hom a • F.map e.op v) =
      ((OB Bsp).map e.op).hom a • tval D (F.map e.op v) := by
    ext m
    exact (D.comp m E).map_smul _ _
  rw [this, evalE_smul]
  have e1 : ((OB Bsp).map (𝟙 E).op).hom (((OB Bsp).map e.op).hom a) =
      ((OB Bsp).map e.op).hom a := by
    rw [op_id, (OB Bsp).map_id]
    rfl
  rw [e1]

lemma dsmul_map {T T' : SB Bsp} (s : T' ⟶ T) (g : APt (OB Bsp) M (op T)) (v : F.obj (op T)) :
    F.map s.op (dsmul hF D g v) = dsmul hF D (APt.res s.op g) (F.map s.op v) := by
  refine sep_affine hF T' fun E e _ => ?_
  rw [← F.map_comp, ← op_comp, map_dsmul, map_dsmul, op_comp, F.map_comp, APt.res_comp]

/-- **Proposition 9.11**, the action of the family. -/
def actionOf : HModule (Hm M Bsp) F where
  smul {U} g v := dsmul hF D (T := unop U) g v
  one_smul {U} v := dsmul_one hF D (T := unop U) v
  mul_smul {U} g h v := dsmul_mul hF D (T := unop U) g h v
  smul_add {U} g v w := dsmul_add hF D (T := unop U) g v w
  smul_smul {U} g a v := dsmul_smul hF D (T := unop U) g a v
  map_smul {U V} f g v := dsmul_map hF D f.unop (T := unop U) g v

lemma actionOf_smul {T : SB Bsp} (g : APt (OB Bsp) M (op T)) (v : F.obj (op T)) :
    asmul (actionOf hF D) g v = dsmul hF D g v := rfl

lemma evalE_tval_eq {E T : SB Bsp} [IsAffine E.left] (t : T ⟶ E) (a : APt (OB Bsp) M (op T))
    (w : F.obj (op E)) : evalE t a (tval D w) = dsmul hF D a (F.map t.op w) := by
  refine sep_affine hF T fun E' e _ => ?_
  rw [← evalE_res, map_dsmul, ← F.map_comp, ← op_comp, tval_res, evalE_resF, Category.id_comp]

lemma rhoV_actionOf {E : SB Bsp} [IsAffine E.left] (w : F.obj (op E)) :
    rhoV (actionOf hF D) hF w = tval D w :=
  rhoV_eq hF w _ fun t a => evalE_tval_eq hF D t a w

lemma dsmul_decompOf {T : SB Bsp} (g : APt (OB Bsp) M (op T)) (x : F.obj (op T)) :
    dsmul hF (decompOf hF A) g x = asmul A g x := by
  refine sep_affine hF T fun E e _ => ?_
  have : tval (decompOf hF A) (F.map e.op x) = rhoV A hF (F.map e.op x) := by
    ext m
    exact compOf_affine hF A m _
  rw [map_dsmul, this, asmul_map, ← smul_eq_evalE, op_id, F.map_id]

lemma hModule_ext {A B : HModule (Hm M Bsp) F}
    (h : ∀ (U : (SB Bsp)ᵒᵖ) (g : (Hm M Bsp).obj U) (x : F.obj U), A.smul g x = B.smul g x) :
    A = B := by
  cases A with
  | mk a _ _ _ _ _ =>
    cases B with
    | mk b _ _ _ _ _ =>
      have : @a = @b := by
        funext U g x
        exact h U g x
      subst this
      rfl

/-- **Proposition 9.11** (corrected wording): `𝔸(M)_B`-`𝒪_B`-module structures on a quasi-coherent
`F` correspond to families `(ρ_m)` of orthogonal idempotents of sum the identity, finitely many
nonzero at each section. `M` is any commutative monoid and `B` any scheme. -/
def hModuleEquivDecomp : HModule (Hm M Bsp) F ≃ Decomp F M where
  toFun := decompOf hF
  invFun := actionOf hF
  left_inv A := by
    exact hModule_ext fun U g x => dsmul_decompOf hF A (T := unop U) g x
  right_inv D := by
    cases D with
    | mk comp natural finite same ne sum =>
      have : (fun (m : M) (T : SB Bsp) => (decompOf hF (actionOf hF
          ⟨comp, natural, finite, same, ne, sum⟩)).comp m T) = comp := by
        funext m T
        refine LinearMap.ext fun v => ?_
        refine sep_affine hF T fun E e _ => ?_
        change F.map e.op (compOf hF _ m v) = _
        rw [map_compOf, rhoV_actionOf]
        exact natural m e v
      simp only [decompOf] at this ⊢
      congr

end P911


/-! ### Objects `V` which are not schemes, notably the base `B`: Propositions 9.12, 9.13, Remark 9.14 -/

section SpacesV

variable {F : PMod (OB Bsp)} {M : Type u} [AddCommMonoid M] [Countable M]

lemma res_res {V V' V'' : SB Bsp} (s : V' ⟶ V) (s' : V'' ⟶ V') {n : ℕ}
    (c : Cochain (Hm M Bsp) F V n) : (c.res s).res s' = c.res (s' ≫ s) := by
  ext T t g
  change c.app ((t ≫ s') ≫ s) g = c.app (t ≫ s' ≫ s) g
  rw [Category.assoc]

lemma sec_res (hF : IsQCoh F) {V V' B : SB Bsp} (s : V' ⟶ V) {n : ℕ}
    (c : Cochain (Hm M Bsp) F V n) (a : B ⟶ V') [IsAffine B.left] :
    (cochainEquivSec hF V' n (c.res s)).val B a = (cochainEquivSec hF V n c).val B (a ≫ s) := by
  refine (phiC_bijective hF B n).1 ?_
  rw [phiC_sec, phiC_sec, res_res]

/-- The explicit primitive of the proof of **Proposition 9.13**: up to sign, the coefficient at the
last letter `X^0`, "given by explicit compatible formula". -/
def primOf (hF : IsQCoh F) {V : SB Bsp} {n : ℕ} (c : Cochain (Hm M Bsp) F V (n + 1)) :
    Cochain (Hm M Bsp) F V n :=
  (cochainEquivSec hF V n).symm
    { val := fun B a _ =>
        ((-1 : ℤ) ^ (n + 1)) • Hochschild.lastCoeff M (F.obj (op B)) ((OB Bsp).obj (op B)) n
          ((cochainEquivSec hF V (n + 1) c).val B a)
      compat := fun B B' s a _ _ => by
        rw [(cochainEquivSec hF V (n + 1) c).compat]
        ext u
        change ((-1 : ℤ) ^ (n + 1)) • F.map s.op _ = F.map s.op (((-1 : ℤ) ^ (n + 1)) • _)
        rw [map_zsmul]
        rfl }

theorem delta_primOf (hF : IsQCoh F) (A : HModule (Hm M Bsp) F) {V : SB Bsp} {n : ℕ}
    (c : Cochain (Hm M Bsp) F V (n + 1)) (hc : delta A c = 0) : delta A (primOf hF c) = c := by
  have hx : ∀ (B : SB Bsp) (a : B ⟶ V) [IsAffine B.left],
      (coactionOf hF A B).delta (n + 1) ((cochainEquivSec hF V (n + 1) c).val B a) = 0 := by
    intro B a _
    refine (phiC_bijective hF B (n + 2)).1 ?_
    rw [← delta_phiC, phiC_sec, map_zero, delta_res, hc]
    rfl
  refine cochain_ext_affine hF fun B a _ => ?_
  rw [← delta_res, primOf, res_symm_sec, delta_phiC hF A, ← phiC_sec hF c a]
  congr 1
  exact ((coactionOf hF A B).eq_delta_of_cocycle n _ (hx B a)).symm

lemma primOf_res (hF : IsQCoh F) {V V' : SB Bsp} (s : V' ⟶ V) {n : ℕ}
    (c : Cochain (Hm M Bsp) F V (n + 1)) : (primOf hF c).res s = primOf hF (c.res s) := by
  refine cochain_ext_affine hF fun B a _ => ?_
  rw [res_res, primOf, primOf, res_symm_sec, res_symm_sec]
  congr 1

variable (F M) in
/-- **Definition 9.4** over an object `V` of `B_spaces,fppf`, given by the presheaf of its points on
the schemes over `B`: `Cⁿ(𝔸(M)_V, F_V)`. `V` = the terminal presheaf is the base `B`. -/
@[ext]
structure CochainV (V : (SB Bsp)ᵒᵖ ⥤ Type u) (n : ℕ) where
  /-- the value at a point of `𝔸(M)ⁿ` over `t ∈ V(T)` -/
  app : ∀ {T : SB Bsp} (_ : V.obj (op T)), (Fin n → (Hm M Bsp).obj (op T)) → F.obj (op T)
  naturality : ∀ {T T' : SB Bsp} (s : T' ⟶ T) (t : V.obj (op T)) (g : Fin n → (Hm M Bsp).obj (op T)),
    app (V.map s.op t) (fun i => ((Hm M Bsp).map s.op).hom (g i)) = F.map s.op (app t g)

variable {V : (SB Bsp)ᵒᵖ ⥤ Type u} {n : ℕ}

/-- The restriction of a cochain along the point `t ∈ V(T)`. -/
def CochainV.at (c : CochainV F M V n) {T : SB Bsp} (t : V.obj (op T)) :
    Cochain (Hm M Bsp) F T n where
  app {T'} s g := c.app (V.map s.op t) g
  naturality {T' T''} r s g := by
    have e : V.map (r ≫ s).op t = V.map r.op (V.map s.op t) := by
      rw [op_comp, V.map_comp]; rfl
    rw [e]
    exact c.naturality r _ g

lemma CochainV.at_res (c : CochainV F M V n) {T T' : SB Bsp} (t : V.obj (op T)) (s : T' ⟶ T) :
    (c.at t).res s = c.at (V.map s.op t) := by
  ext R r g
  change c.app (V.map (r ≫ s).op t) g = c.app (V.map r.op (V.map s.op t)) g
  rw [op_comp, V.map_comp]
  rfl

lemma res_app_id {T T' : SB Bsp} {k : ℕ} (d : Cochain (Hm M Bsp) F T k) (s : T' ⟶ T)
    (g : Fin k → (Hm M Bsp).obj (op T')) : (d.res s).app (𝟙 T') g = d.app s g := by
  change d.app (𝟙 T' ≫ s) g = _
  rw [Category.id_comp]

/-- **Definition 9.5** over `V`. -/
def deltaV (A : HModule (Hm M Bsp) F) (c : CochainV F M V n) : CochainV F M V (n + 1) where
  app {T} t g := (delta A (c.at t)).app (𝟙 T) g
  naturality {T T'} s t g := by
    rw [← c.at_res, delta_res, res_app_id]
    have h := (delta A (c.at t)).naturality s (𝟙 T) g
    rw [Category.comp_id] at h
    exact h

lemma delta_at_app (A : HModule (Hm M Bsp) F) (c : CochainV F M V n) {T T' : SB Bsp}
    (t : V.obj (op T)) (s : T' ⟶ T) (g : Fin (n + 1) → (Hm M Bsp).obj (op T')) :
    (delta A (c.at t)).app s g = (deltaV A c).app (V.map s.op t) g := by
  change _ = (delta A (c.at (V.map s.op t))).app (𝟙 T') g
  rw [← c.at_res, delta_res, res_app_id]

/-- **Proposition 9.13 and Remark 9.14** over any object `V` of `B_spaces,fppf`, in particular over
`B`: every cocycle of degree `n + 1` is a coboundary. The local primitives are glued as in the printed
proof, "since they are given by explicit compatible formula". -/
theorem exists_deltaV_eq (hF : IsQCoh F) (A : HModule (Hm M Bsp) F)
    (c : CochainV F M V (n + 1))
    (hc : ∀ {T : SB Bsp} (t : V.obj (op T)) g, (deltaV A c).app t g = 0) :
    ∃ e : CochainV F M V n, deltaV A e = c := by
  have hz : ∀ {T : SB Bsp} (t : V.obj (op T)), delta A (c.at t) = 0 := by
    intro T t
    ext R r g
    rw [delta_at_app, hc]
    rfl
  let e : CochainV F M V n :=
    { app := fun {T} t g => (primOf hF (c.at t)).app (𝟙 T) g
      naturality := fun {T T'} s t g => by
        rw [← c.at_res, ← primOf_res, res_app_id]
        have h := (primOf hF (c.at t)).naturality s (𝟙 T) g
        rw [Category.comp_id] at h
        exact h }
  have he : ∀ {T : SB Bsp} (t : V.obj (op T)), e.at t = primOf hF (c.at t) := by
    intro T t
    ext R r g
    change (primOf hF (c.at (V.map r.op t))).app (𝟙 R) g = _
    rw [← c.at_res, ← primOf_res, res_app_id]
  refine ⟨e, ?_⟩
  ext T t g
  change (delta A (e.at t)).app (𝟙 T) g = _
  rw [he, delta_primOf hF A _ (hz t)]
  change c.app (V.map (𝟙 T).op t) g = _
  rw [op_id, V.map_id]
  rfl

variable (Bsp) in
/-- The base `B`, as a presheaf on its site: the terminal presheaf. -/
def baseV : (SB Bsp)ᵒᵖ ⥤ Type u := (Functor.const _).obj PUnit

/-- **Proposition 9.13** over the base: `H¹_monoid(𝔸(M)_B, F) = 0`, i.e. `Z¹ ⊆ B¹`, for `B` an
algebraic space. -/
theorem H1_base (hF : IsQCoh F) (A : HModule (Hm M Bsp) F) (c : CochainV F M (baseV Bsp) 1)
    (hc : ∀ {T : SB Bsp} (t : (baseV Bsp).obj (op T)) g, (deltaV A c).app t g = 0) :
    ∃ e : CochainV F M (baseV Bsp) 0, deltaV A e = c :=
  exists_deltaV_eq hF A c hc

/-- **Remark 9.14** over the base: `Hⁿ_monoid(𝔸(M)_B, F) = 0` for `n ≥ 1`. -/
theorem Hn_base (hF : IsQCoh F) (A : HModule (Hm M Bsp) F) (c : CochainV F M (baseV Bsp) (n + 1))
    (hc : ∀ {T : SB Bsp} (t : (baseV Bsp).obj (op T)) g, (deltaV A c).app t g = 0) :
    ∃ e : CochainV F M (baseV Bsp) n, deltaV A e = c :=
  exists_deltaV_eq hF A c hc

variable (F M V n) in
/-- **Proposition 9.12, first assertion** over `V`: a section over `V` of the sheaf `⨁ F_m`, i.e. a
compatible family of finitely supported families over the affine points of `V`. -/
@[ext]
structure SecV where
  /-- the value at an affine point of `V` -/
  val : ∀ (E : SB Bsp) [IsAffine E.left] (_ : V.obj (op E)), (Fin n → M) →₀ F.obj (op E)
  compat : ∀ (E E' : SB Bsp) [IsAffine E.left] [IsAffine E'.left] (s : E' ⟶ E) (t : V.obj (op E)),
    val E' (V.map s.op t) = resF s (val E t)

/-- The section of `⨁ F_m` over a scheme point `t` of `V`. -/
def SecV.at (σ : SecV F M V n) {T : SB Bsp} (t : V.obj (op T)) : Sec F (Fin n → M) T where
  val E e _ := σ.val E (V.map e.op t)
  compat E E' s e _ _ := by
    rw [← σ.compat, op_comp, V.map_comp]
    rfl

lemma symm_at_res (hF : IsQCoh F) (σ : SecV F M V n) {T R : SB Bsp} (t : V.obj (op T)) (r : R ⟶ T) :
    (cochainEquivSec hF R n).symm (σ.at (V.map r.op t)) =
      ((cochainEquivSec hF T n).symm (σ.at t)).res r := by
  refine cochain_ext_affine hF fun B a _ => ?_
  rw [res_res, res_symm_sec, res_symm_sec]
  congr 1
  change σ.val B (V.map a.op (V.map r.op t)) = σ.val B (V.map (a ≫ r).op t)
  rw [op_comp, V.map_comp]
  rfl

/-- The cochain of a section over `V`. -/
def ofSecV (hF : IsQCoh F) (σ : SecV F M V n) : CochainV F M V n where
  app {T} t g := ((cochainEquivSec hF T n).symm (σ.at t)).app (𝟙 T) g
  naturality {T T'} s t g := by
    rw [symm_at_res, res_app_id]
    have h := ((cochainEquivSec hF T n).symm (σ.at t)).naturality s (𝟙 T) g
    rw [Category.comp_id] at h
    exact h

/-- The section over `V` of a cochain. -/
def toSecV (hF : IsQCoh F) (c : CochainV F M V n) : SecV F M V n where
  val E _ t := (cochainEquivSec hF E n (c.at t)).val E (𝟙 E)
  compat E E' _ _ s t := by
    rw [← c.at_res, sec_res, Category.id_comp, ← (cochainEquivSec hF E n (c.at t)).compat,
      Category.comp_id]

lemma ofSecV_at (hF : IsQCoh F) (σ : SecV F M V n) {T : SB Bsp} (t : V.obj (op T)) :
    (ofSecV hF σ).at t = (cochainEquivSec hF T n).symm (σ.at t) := by
  ext R r g
  change ((cochainEquivSec hF R n).symm (σ.at (V.map r.op t))).app (𝟙 R) g = _
  rw [symm_at_res, res_app_id]

/-- **Proposition 9.12, first assertion** over any object `V` of `B_spaces,fppf`, `B` included. -/
def cochainVEquivSec (hF : IsQCoh F) : CochainV F M V n ≃ SecV F M V n where
  toFun := toSecV hF
  invFun := ofSecV hF
  left_inv c := by
    have e : ∀ {T : SB Bsp} (t : V.obj (op T)),
        (cochainEquivSec hF T n).symm ((toSecV hF c).at t) = c.at t := by
      intro T t
      rw [Equiv.symm_apply_eq]
      refine Sec.ext ?_
      funext E a inst
      change (cochainEquivSec hF E n (c.at (V.map a.op t))).val E (𝟙 E) = _
      rw [← c.at_res, sec_res, Category.id_comp]
    ext T t g
    change ((cochainEquivSec hF T n).symm _).app (𝟙 T) g = _
    rw [e]
    change c.app (V.map (𝟙 T).op t) g = _
    rw [op_id, V.map_id]
    rfl
  right_inv σ := by
    refine SecV.ext ?_
    funext E inst t
    change (cochainEquivSec hF E n ((ofSecV hF σ).at t)).val E (𝟙 E) = _
    rw [ofSecV_at, Equiv.apply_symm_apply]
    change σ.val E (V.map (𝟙 E).op t) = _
    rw [op_id, V.map_id]
    rfl

end SpacesV

end AlgMag.S9B

end
