/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec16Scheme
import AlgMag.AppendixA
import AlgMag.Sec16Gm
import AlgMag.Sec4Limits
import AlgMag.Sec8Representability
import AlgMag.GeneralBaseThm320
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# What remains of §16 (Algebraic Magnetism)

* `dualFppf`, `dualPointFppf`: `I_S` as an object of the big fppf site, so that §§16.1, 16.2 and
  Proposition 16.15 (iii) apply to algebraic spaces.
* `prop1615_i`: **Proposition 16.15 (i)**.
* §16.4 on any site, in particular `BigFppfOver`: there the attractor `X^N` lands in a bigger
  universe than `X`, so one cannot literally iterate `attractor` (`AlgMag.stagesIso` needs a small
  site, which `BigFppfOver` is not). A stage is a presheaf in the right universe representing `X^N`.
  It exists as soon as `𝔸(N)_T` is in the site (`exists_rep`), e.g. for `N` countable.

* §16.7: `Mono.ToricMono` (toric monoschemes presented by their affine opens), `Mono.toricScheme`,
  `Mono.chartι`, `Mono.chart_surjective`.

The stage lemmas of `AlgMag.Sec16Gm` are restated here because that file requires `C : Type u`, which
`BigFppfOver` does not satisfy.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v w

set_option linter.unusedSectionVars false

namespace AlgMag

/-! ### `I_S` in the fppf site (§16.1, §16.2) -/

section Fppf

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

local notation "SCH" => BigFppfOver.toScheme B S hS

include hS in
theorem contains_dual : B.Contains
    (pullback (specULiftZIsTerminal.from S) (Spec.map dualUnit.{u})) := by
  have h : B.Contains (Spec dualRing.{u}) := by
    refine Scheme.size_Spec_lt_of_mk_le B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit _ hS ?_
    have hc : Countable (DualNumber (ULift.{u} ℤ)) :=
      inferInstanceAs (Countable (ULift.{u} ℤ × ULift.{u} ℤ))
    refine (Cardinal.mk_le_aleph0 (α := DualNumber (ULift.{u} ℤ))).trans ?_
    exact (Scheme.aleph0_le_size S).trans (Cardinal.self_le_power _ Cardinal.one_le_aleph0)
  exact lt_of_le_of_lt (Scheme.size_pullback_le _ _) (max_lt hS h)

/-- **§16.1.** `I_S = Spec(ℤ[ε]) ×_ℤ S` as an object of the big fppf site over `S`. -/
noncomputable def dualFppf : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS (contains_dual B S hS) (pullback.fst _ _)

/-- The zero section of `I_S`, in the site. -/
noncomputable def dualPointFppf : DualPoint (dualFppf B S hS) where
  o T := BigFppfOver.homMk B S hS (contains_dual B S hS) (pullback.fst _ _)
    (pullback.lift (B.inclusion.map T.hom)
      (B.inclusion.map T.hom ≫ specULiftZIsTerminal.from S ≫ Spec.map dualZero.{u})
      (specULiftZIsTerminal.hom_ext _ _)) (pullback.lift_fst _ _ _)
  comp_o {T T'} s := by
    apply (SCH).map_injective
    refine pullback.hom_ext ?_ ?_
    · have hw : (SCH).map s ≫ B.inclusion.map T.hom = B.inclusion.map T'.hom :=
        congrArg (B.inclusion.map) (Over.w s)
      change (SCH).map s ≫ pullback.lift _ _ _ ≫ pullback.fst _ _ = pullback.lift _ _ _ ≫ pullback.fst _ _
      rw [pullback.lift_fst, pullback.lift_fst]
      exact hw
    · have hw : (SCH).map s ≫ B.inclusion.map T.hom = B.inclusion.map T'.hom :=
        congrArg (B.inclusion.map) (Over.w s)
      change (SCH).map s ≫ pullback.lift _ _ _ ≫ pullback.snd _ _ = pullback.lift _ _ _ ≫ pullback.snd _ _
      rw [pullback.lift_snd, pullback.lift_snd, ← Category.assoc, hw]

instance : HasBinaryProducts (BigFppfOver B S hS) := hasBinaryProducts_fppf B S hS

variable {B S hS} {M : Type*} [AddCommMonoid M]

/-- **Proposition 16.2** on the big fppf site: for an algebraic space (indeed any presheaf) `X` over
`S` with an action of `𝔸(M)_S`, `(TX)^N = T(X^N)`. -/
noncomputable def tangentAttractorIsoFppf {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (act : AAction (fppfO B S hS) M X) (N : AddSubmonoid M) :
    attractor (tangentAction (dualFppf B S hS) act) N ≅ tangent (dualFppf B S hS) (attractor act N) :=
  tangentAttractorIso _ act N

/-- **Proposition 16.4** on the big fppf site: `Lie(G)^N = Lie(G^N)`. -/
noncomputable def lieAttractorIsoFppf {G : GrpFunctor.{u} (BigFppfOver B S hS)}
    (act : AAction (fppfO B S hS) M G.F) (ha : ActsByMonoidEnd act) (N : AddSubmonoid M) :
    GrpIso (attrGrp (Lie (dualPointFppf B S hS) G) (lieAction (dualPointFppf B S hS) act ha)
        (actsByMonoidEnd_lie (dualPointFppf B S hS) act ha) N)
      (Lie (dualPointFppf B S hS) (attrGrp G act ha N)) :=
  lieAttractorIso _ act ha N

/-- **Proposition 16.15 (iii)** on the big fppf site, for `G^{[α⟩}`. -/
noncomputable def lieRootAttrIsoFppf {G : GrpFunctor.{u} (BigFppfOver B S hS)}
    (act : AAction (fppfO B S hS) M G.F) (ha : ActsByMonoidEnd act) (α : M) :=
  lieRootAttrIso (dualPointFppf B S hS) act ha α

/-- **Proposition 16.15 (iii)** on the big fppf site, for `G^{[α⟩}_{e_S}`. -/
noncomputable def lieRootKernelIsoFppf {G : GrpFunctor.{u} (BigFppfOver B S hS)}
    (act : AAction (fppfO B S hS) M G.F) (ha : ActsByMonoidEnd act) (α : M) :=
  lieRootKernelIso (dualPointFppf B S hS) act ha α

end Fppf

/-! ### Proposition 16.15 (i) -/

section Prop1615

variable {S : Scheme.{u}} {M : Type u} [AddCommMonoid M]

/-- A group scheme over `S`, as a group functor on `Sch/S`. -/
def schemeGrp (X : Over S) (grp : ∀ U : (Over S)ᵒᵖ, Group ((yoneda.obj X).obj U))
    (map_mul : ∀ {U V : (Over S)ᵒᵖ} (s : U ⟶ V) (x y : (yoneda.obj X).obj U),
      (yoneda.obj X).map s (x * y) = (yoneda.obj X).map s x * (yoneda.obj X).map s y) :
    GrpFunctor.{u} (Over S) where
  F := yoneda.obj X
  grp := grp
  map_mul := map_mul

/-- **Proposition 16.15 (i).** Let `G` be a group scheme affine over `S`, with `𝔸(M)_S` acting by
group endomorphisms (`D(M)_S` by automorphisms if `M` is a group), and `α ∈ M`. Then
`G^{[α⟩}_{e_S} → G^{[α⟩} → G` are closed immersions: `G^{[α⟩}` is represented by a closed subscheme
`Y` of `G`, and `G^{[α⟩}_{e_S}` by a closed subscheme `K` of `Y`. The maps are the canonical ones:
`Y → G` is the point of `X^N → X`, and `K → Y` the first projection of the fibre product defining
`G^{[α⟩}_{e_S}`. -/
theorem prop1615_i {X : Over S} [IsAffineHom X.hom]
    {grp : ∀ U : (Over S)ᵒᵖ, Group ((yoneda.obj X).obj U)}
    {map_mul : ∀ {U V : (Over S)ᵒᵖ} (s : U ⟶ V) (x y : (yoneda.obj X).obj U),
      (yoneda.obj X).map s (x * y) = (yoneda.obj X).map s x * (yoneda.obj X).map s y}
    (act : AAction (overO S) M (schemeGrp X grp map_mul).F)
    (ha : ActsByMonoidEnd act) (α : M) :
    ∃ (Y K : Over S) (i : Y ⟶ X) (j : K ⟶ Y)
      (eY : ∀ T : Over S, (T ⟶ Y) ≃ AttractorPt act (AddSubmonoid.closure {α}) T)
      (eK : ∀ T : Over S, (T ⟶ K) ≃ (rootKernel act ha α).F.obj (op T)),
      IsClosedImmersion i.left ∧ IsClosedImmersion j.left ∧
      (∀ {T : Over S} (z : T ⟶ Y), (eY T z).toPoint = z ≫ i) ∧
      (∀ {T : Over S} (z : T ⟶ K), (eK T z).1.1 = eY T (z ≫ j)) := by
  let act' : AAction (overO S) M (yoneda.obj X) := act
  let N := AddSubmonoid.closure {α}
  let Q := unitsFace N
  have hQ : IsFace Q N := unitsIsFace N
  let Y := GB.Zatt act' N
  let Y0 := GB.Zatt act' Q
  let i0 := GB.iAtt act' Q
  have hi0 : IsClosedImmersion i0.left := GB.instClosedIAtt act' Q
  let e1 : ∀ T, (T ⟶ Y) ≃ AttractorPt act' N T := fun T => GB.attEquiv act' N T
  let e0 : ∀ T, (T ⟶ Y0) ≃ AttractorPt act' Q T := fun T => GB.attEquiv act' Q T
  have n0 : ∀ {T T' : Over S} (s : T' ⟶ T) (z : T ⟶ Y0), e0 T' (s ≫ z) = (e0 T z).baseChange s :=
    fun s z => GB.attEquiv_comp act' Q s z
  have n1 : ∀ {T T' : Over S} (s : T' ⟶ T) (z : T ⟶ Y), e1 T' (s ≫ z) = (e1 T z).baseChange s :=
    fun s z => GB.attEquiv_comp act' N s z
  let p : Y ⟶ Y0 := (e0 Y).symm (AttractorPt.ofFace hQ (e1 Y (𝟙 Y)))
  have hp : ∀ {T : Over S} (z : T ⟶ Y), e0 T (z ≫ p) = AttractorPt.ofFace hQ (e1 T z) := by
    intro T z
    rw [n0, Equiv.apply_symm_apply]
    have : e1 T z = (e1 Y (𝟙 Y)).baseChange z := by
      rw [← n1, Category.comp_id]
    rw [this]
    rfl
  let G' := attrGrp (schemeGrp X grp map_mul) act ha Q
  let Sobj : Over S := Over.mk (𝟙 S)
  let oneQ : ∀ T : Over S, AttractorPt act' Q T := fun T => (1 : G'.F.obj (op T))
  have hone : ∀ {T T' : Over S} (s : T' ⟶ T), (oneQ T).baseChange s = oneQ T' := fun {T T'} s =>
    GrpFunctor.map_one G' s.op
  let u : Sobj ⟶ Y0 := (e0 Sobj).symm (oneQ Sobj)
  have hu : ∀ {T : Over S} (τ : T ⟶ Sobj), e0 T (τ ≫ u) = oneQ T := by
    intro T τ
    rw [n0, Equiv.apply_symm_apply, hone]
  have huc : IsClosedImmersion u.left := by
    have hsec : u.left ≫ Y0.hom = 𝟙 S := Over.w u
    have hsep : IsSeparated Y0.hom := by
      have hw : Y0.hom = i0.left ≫ X.hom := (Over.w i0).symm
      rw [hw]
      have : IsSeparated X.hom := IsSeparated.of_isAffineHom X.hom
      infer_instance
    have : IsClosedImmersion (u.left ≫ Y0.hom) := by
      have h0 : IsClosedImmersion (𝟙 S : S ⟶ S) := inferInstance
      rw [hsec]
      exact h0
    exact IsClosedImmersion.of_comp u.left Y0.hom
  let K : Over S := Over.mk (pullback.fst p.left u.left ≫ Y.hom)
  let j : K ⟶ Y := Over.homMk (pullback.fst p.left u.left) rfl
  let v : K ⟶ Sobj := Over.homMk (pullback.snd p.left u.left) (by
    have h1 := pullback.condition (f := p.left) (g := u.left)
    have h2 : p.left ≫ Y0.hom = Y.hom := Over.w p
    have h3 : u.left ≫ Y0.hom = 𝟙 S := Over.w u
    change pullback.snd p.left u.left ≫ 𝟙 S = pullback.fst p.left u.left ≫ Y.hom
    rw [← h3, ← Category.assoc, ← h1, Category.assoc, h2])
  have hjv : j ≫ p = v ≫ u := Over.OverMorphism.ext (pullback.condition (f := p.left) (g := u.left))
  have hτ' : ∀ {T : Over S} (a b : T ⟶ Sobj), a = b := by
    intro T a b
    refine Over.OverMorphism.ext ?_
    have ha' := Over.w a
    have hb' := Over.w b
    simp only [Sobj, Over.mk_hom] at ha' hb'
    exact ha'.trans hb'.symm
  let eK : ∀ T : Over S, (T ⟶ K) ≃ (rootKernel act ha α).F.obj (op T) := fun T =>
    { toFun := fun z => ⟨(e1 T (z ≫ j), PUnit.unit), by
        change AttractorPt.ofFace hQ (e1 T (z ≫ j)) = oneQ T
        rw [← hp, Category.assoc, hjv, ← Category.assoc, hu]⟩
      invFun := fun x =>
        let z0 : T ⟶ Y := (e1 T).symm x.1.1
        let τ : T ⟶ Sobj := Over.homMk T.hom (by simp [Sobj])
        have hz : z0 ≫ p = τ ≫ u := by
          apply (e0 T).injective
          rw [hp, hu]
          have e : e1 T z0 = x.1.1 := Equiv.apply_symm_apply _ _
          rw [e]
          exact x.2
        Over.homMk (pullback.lift z0.left τ.left (congrArg (fun k => k.left) hz)) (by
          simp only [K, Over.mk_hom]
          rw [pullback.lift_fst_assoc]
          exact Over.w z0)
      left_inv := fun z => by
        refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
        · simp only [Over.homMk_left, pullback.lift_fst, Equiv.symm_apply_apply]
          rfl
        · simp only [Over.homMk_left, pullback.lift_snd]
          have := Over.w (z ≫ v)
          simpa [Sobj, v] using this.symm
      right_inv := fun x => by
        refine Subtype.ext (Prod.ext ?_ rfl)
        have h : ∀ w : T ⟶ K, w.left ≫ pullback.fst p.left u.left = ((e1 T).symm x.1.1).left →
            w ≫ j = (e1 T).symm x.1.1 := fun w hw => Over.OverMorphism.ext hw
        exact (congrArg (e1 T) (h _ (pullback.lift_fst _ _ _))).trans (Equiv.apply_symm_apply _ _) }
  have hjc : IsClosedImmersion j.left := by
    change IsClosedImmersion (pullback.fst p.left u.left)
    infer_instance
  exact ⟨Y, K, GB.iAtt act' N, j, e1, eK, GB.instClosedIAtt act' N, hjc,
    fun z => GB.toPoint_attEquiv act' N z, fun z => rfl⟩

end Prop1615

/-! ### §16.4 on a general site -/

namespace S16R

variable {C : Type*} [Category.{v} C] {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}}

section Big

variable {P : Type*} [AddCommMonoid P] {W : Cᵒᵖ ⥤ Type w} (a : AAction 𝒪 P W) (N : AddSubmonoid P)

/-- The points of the attractor of a functor in an arbitrary universe, with the same definition as
`AlgMag.AttractorPt`, which requires the universe of `𝒪`. -/
@[ext]
structure BigPt (T : C) where
  /-- The value at a point of `𝔸(N)` over `t`. -/
  app : ∀ {T' : C} (_ : T' ⟶ T), APt 𝒪 N (op T') → W.obj (op T')
  naturality : ∀ {T' T'' : C} (s : T'' ⟶ T') (t : T' ⟶ T) (b : APt 𝒪 N (op T')),
    app (s ≫ t) (APt.res s.op b) = W.map s.op (app t b)
  equivariant : ∀ {T' : C} (t : T' ⟶ T) (h : APt 𝒪 P (op T')) (b : APt 𝒪 N (op T')),
    app t (APt.toMagnet N h * b) = a.smul h (app t b)

variable {a N} in
/-- Base change of `BigPt`. -/
def BigPt.baseChange {T T'' : C} (s : T'' ⟶ T) (φ : BigPt a N T) : BigPt a N T'' where
  app t b := φ.app (t ≫ s) b
  naturality r t b := by
    rw [Category.assoc]; exact φ.naturality r (t ≫ s) b
  equivariant t h b := φ.equivariant (t ≫ s) h b

/-- A presheaf in the universe of `𝒪` with the same points as `W`. -/
structure SmallModel (W : Cᵒᵖ ⥤ Type w) (Y : Cᵒᵖ ⥤ Type u) where
  /-- The bijection on points. -/
  equiv : ∀ T : C, Y.obj (op T) ≃ W.obj (op T)
  naturality : ∀ {T T' : C} (s : T' ⟶ T) (y : Y.obj (op T)),
    equiv T' (Y.map s.op y) = W.map s.op (equiv T y)

variable {Y : Cᵒᵖ ⥤ Type u}

lemma SmallModel.map_symm (r : SmallModel W Y) {T T' : C} (s : T' ⟶ T) (x : W.obj (op T)) :
    Y.map s.op ((r.equiv T).symm x) = (r.equiv T').symm (W.map s.op x) := by
  apply (r.equiv T').injective
  rw [r.naturality, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The action transported to the small model. -/
def SmallModel.transport (r : SmallModel W Y) (a : AAction 𝒪 P W) : AAction 𝒪 P Y where
  smul {U} h y := (r.equiv (unop U)).symm (a.smul h (r.equiv (unop U) y))
  one_smul {U} y := by rw [a.one_smul, Equiv.symm_apply_apply]
  mul_smul {U} g h y := by rw [a.mul_smul, Equiv.apply_symm_apply]
  map_smul {U V} s h y := by
    have := r.map_symm s.unop (a.smul h (r.equiv (unop U) y))
    refine this.trans ?_
    congr 1
    refine (a.map_smul s h _).trans ?_
    congr 1
    exact (r.naturality s.unop y).symm

lemma SmallModel.equiv_transport (r : SmallModel W Y) {U : Cᵒᵖ} (h : APt 𝒪 P U) (y : Y.obj U) :
    r.equiv (unop U) ((r.transport a).smul h y) = a.smul h (r.equiv (unop U) y) :=
  Equiv.apply_symm_apply _ _

/-- The points of the attractor of the small model are those of the big attractor. -/
def SmallModel.ptEquiv (r : SmallModel W Y) (T : C) :
    AttractorPt (r.transport a) N T ≃ BigPt a N T where
  toFun φ :=
    { app := fun t b => r.equiv _ (φ.app t b)
      naturality := fun s t b => by
        rw [φ.naturality]; exact r.naturality s _
      equivariant := fun t h b => by
        rw [φ.equivariant]; exact r.equiv_transport a h _ }
  invFun ψ :=
    { app := fun t b => (r.equiv _).symm (ψ.app t b)
      naturality := fun s t b => by
        rw [ψ.naturality]; exact (r.map_symm s _).symm
      equivariant := fun {T'} t h b => by
        rw [ψ.equivariant]
        change _ = (r.equiv T').symm (a.smul h (r.equiv T' ((r.equiv T').symm _)))
        rw [Equiv.apply_symm_apply] }
  left_inv φ := by
    refine AttractorPt.ext ?_
    funext T' t b
    exact Equiv.symm_apply_apply _ _
  right_inv ψ := by
    refine BigPt.ext ?_
    funext T' t b
    exact Equiv.apply_symm_apply _ _

lemma SmallModel.ptEquiv_baseChange (r : SmallModel W Y) {T T' : C} (s : T' ⟶ T)
    (φ : AttractorPt (r.transport a) N T) :
    r.ptEquiv a N T' (φ.baseChange s) = (r.ptEquiv a N T φ).baseChange s := rfl

end Big

section Rep

variable {M : Type*} [AddCommMonoid M] {F : Cᵒᵖ ⥤ Type u} {act : AAction 𝒪 M F} {N : AddSubmonoid M}
  {Y : Cᵒᵖ ⥤ Type u}

/-- A representation of `X^N` is a small model of the functor `X^N`. -/
def smallModelOfRep (r : RepresentsAttractor act N Y) : SmallModel (attractor act N) Y where
  equiv := r.equiv
  naturality s y := r.naturality s y

variable (act N) in
/-- **The size fix.** If `𝔸(N)_T` is in the site for all `T`, then the attractor `X^N` is represented
by a presheaf in the universe of `𝒪`. -/
theorem exists_rep (hU : ∀ T : C, Nonempty (UniversalPoint 𝒪 N T)) :
    ∃ Y : Cᵒᵖ ⥤ Type u, Nonempty (RepresentsAttractor act N Y) := by
  classical
  let U : ∀ T : C, UniversalPoint 𝒪 N T := fun T => (hU T).some
  let Z : C → Type u := fun T => { x : F.obj (op (U T).P) // ∀ {T' : C} (t : T' ⟶ T) (h : APt 𝒪 M (op T'))
      (a : APt 𝒪 N (op T')), F.map ((U T).lift t (APt.toMagnet N h * a)).op x =
        act.smul h (F.map ((U T).lift t a).op x) }
  let e : ∀ T, Z T ≃ AttractorPt act N T := fun T => (attractorPtEquivOfUniversal (U T)).symm
  let Yf : Cᵒᵖ ⥤ Type u :=
    { obj := fun T => Z (unop T)
      map := fun {T T'} s => ↾ fun z => (e (unop T')).symm ((e (unop T) z).baseChange s.unop)
      map_id := fun T => by
        refine ConcreteCategory.hom_ext _ _ fun z => ?_
        change (e _).symm ((e _ z).baseChange (𝟙 _)) = z
        have : (e (unop T) z).baseChange (𝟙 _) = e (unop T) z := by
          refine AttractorPt.ext ?_
          funext T' t a
          exact congrArg (fun k => AttractorPt.app (e (unop T) z) k a) (Category.comp_id t)
        rw [this, Equiv.symm_apply_apply]
      map_comp := fun {T T' T''} f g => by
        refine ConcreteCategory.hom_ext _ _ fun z => ?_
        change (e _).symm ((e _ z).baseChange (f ≫ g).unop) =
          (e _).symm ((e _ ((e _).symm ((e _ z).baseChange f.unop))).baseChange g.unop)
        rw [Equiv.apply_symm_apply]
        congr 1
        refine AttractorPt.ext ?_
        funext W t a
        exact congrArg (fun k => AttractorPt.app (e (unop T) z) k a) (Category.assoc _ _ _).symm }
  refine ⟨Yf, ⟨{ equiv := e, naturality := fun {T T'} s z => ?_ }⟩⟩
  exact Equiv.apply_symm_apply _ _

end Rep

/-! #### Example (ii): products -/

section Prod

variable {M₁ M₂ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂] {F : Cᵒᵖ ⥤ Type u}
  (act : AAction 𝒪 (M₁ × M₂) F) (N₁ : AddSubmonoid M₁) (N₂ : AddSubmonoid M₂)

/-- `𝔸(M₁) → 𝔸(M₁ × M₂)`, `a ↦ a ⊠ 1`, or the action of `M₁`: the action of the factor `D(M₁)`. -/
def inlPt {U : Cᵒᵖ} (a : APt 𝒪 M₁ U) : APt 𝒪 (M₁ × M₂) U :=
  a.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst M₁ M₂))

/-- The second factor. -/
def inrPt {U : Cᵒᵖ} (a : APt 𝒪 M₂ U) : APt 𝒪 (M₁ × M₂) U :=
  a.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.snd M₁ M₂))

/-- `𝔸(M₁)` acting through the first factor (paper: `Z × 0`). -/
def actFst : AAction 𝒪 M₁ F where
  smul h x := act.smul (inlPt h) x
  one_smul x := act.one_smul x
  mul_smul g h x := act.mul_smul (inlPt g) (inlPt h) x
  map_smul f h x := act.map_smul f _ x

/-- `𝔸(M₂)` acting on the first stage `X^{N₁}_{M₁}` through the second factor (Remark 3.11). -/
def actSnd : AAction 𝒪 M₂ (attractor (actFst act) N₁) where
  smul {U} h φ :=
    { app := fun {T'} t a => act.smul (inrPt (APt.res t.op h)) (AttractorPt.app φ t a)
      naturality := fun {T' T''} s t a => by
        rw [AttractorPt.naturality φ s t a, act.map_smul]
        congr 1
        rw [op_comp, APt.res_comp]
        rfl
      equivariant := fun {T'} t k a => by
        rw [AttractorPt.equivariant φ t k a]
        change act.smul _ (act.smul _ _) = act.smul _ (act.smul _ _)
        rw [← act.mul_smul, ← act.mul_smul, mul_comm] }
  one_smul {U} φ := by
    refine AttractorPt.ext ?_
    funext T' t a
    have h1 : inrPt (M₁ := M₁) (APt.res t.op (1 : APt 𝒪 M₂ U)) = 1 := by ext p; simp [inrPt]
    change act.smul (inrPt (APt.res t.op 1)) _ = _
    rw [h1, act.one_smul]
  mul_smul {U} g h φ := by
    refine AttractorPt.ext ?_
    funext T' t a
    change act.smul (inrPt (APt.res t.op (g * h))) _ = act.smul _ (act.smul _ _)
    rw [← act.mul_smul]
    congr 1
    rw [APt.res_mul]
    rfl
  map_smul {U V} s h φ := by
    refine AttractorPt.ext ?_
    funext T' t a
    change act.smul (inrPt (APt.res (t ≫ s.unop).op h)) _ = act.smul (inrPt (APt.res t.op (APt.res s h))) _
    rw [← APt.res_comp]
    rfl

/-- The inclusion `N₁ → N₁ × N₂`. -/
def inMagnet₁ : N₁ →+ (N₁.prod N₂) :=
  { toFun := fun n => ⟨(n, 0), n.2, N₂.zero_mem⟩, map_zero' := rfl
    map_add' := fun a b => Subtype.ext (Prod.ext rfl (add_zero 0).symm) }

/-- The inclusion `N₂ → N₁ × N₂`. -/
def inMagnet₂ : N₂ →+ (N₁.prod N₂) :=
  { toFun := fun n => ⟨(0, n), N₁.zero_mem, n.2⟩, map_zero' := rfl
    map_add' := fun a b => Subtype.ext (Prod.ext (add_zero 0).symm rfl) }

/-- The first restriction `𝔸(N₁ × N₂) → 𝔸(N₁)`. -/
def cut₁ {U : Cᵒᵖ} (c : APt 𝒪 (N₁.prod N₂) U) : APt 𝒪 N₁ U :=
  c.comp (AddMonoidHom.toMultiplicative (inMagnet₁ N₁ N₂))

/-- The second restriction `𝔸(N₁ × N₂) → 𝔸(N₂)`. -/
def cut₂ {U : Cᵒᵖ} (c : APt 𝒪 (N₁.prod N₂) U) : APt 𝒪 N₂ U :=
  c.comp (AddMonoidHom.toMultiplicative (inMagnet₂ N₁ N₂))

/-- `𝔸(N₁) × 𝔸(N₂) → 𝔸(N₁ × N₂)`. -/
def glue {U : Cᵒᵖ} (a : APt 𝒪 N₁ U) (b : APt 𝒪 N₂ U) : APt 𝒪 (N₁.prod N₂) U where
  toFun n := a (Multiplicative.ofAdd ⟨(Multiplicative.toAdd n : N₁.prod N₂).1.1,
      (Multiplicative.toAdd n : N₁.prod N₂).2.1⟩) *
    b (Multiplicative.ofAdd ⟨(Multiplicative.toAdd n : N₁.prod N₂).1.2,
      (Multiplicative.toAdd n : N₁.prod N₂).2.2⟩)
  map_one' := by
    have ha := a.map_one
    have hb := b.map_one
    exact (congrArg₂ (· * ·) ha hb).trans (mul_one 1)
  map_mul' x y := by
    have ha := a.map_mul
      (Multiplicative.ofAdd ⟨(Multiplicative.toAdd x : N₁.prod N₂).1.1,
        (Multiplicative.toAdd x : N₁.prod N₂).2.1⟩)
      (Multiplicative.ofAdd ⟨(Multiplicative.toAdd y : N₁.prod N₂).1.1,
        (Multiplicative.toAdd y : N₁.prod N₂).2.1⟩)
    have hb := b.map_mul
      (Multiplicative.ofAdd ⟨(Multiplicative.toAdd x : N₁.prod N₂).1.2,
        (Multiplicative.toAdd x : N₁.prod N₂).2.2⟩)
      (Multiplicative.ofAdd ⟨(Multiplicative.toAdd y : N₁.prod N₂).1.2,
        (Multiplicative.toAdd y : N₁.prod N₂).2.2⟩)
    refine (congrArg₂ (· * ·) ha hb).trans ?_
    exact mul_mul_mul_comm _ _ _ _

lemma glue_res {U V : Cᵒᵖ} (f : U ⟶ V) (a : APt 𝒪 N₁ U) (b : APt 𝒪 N₂ U) :
    glue N₁ N₂ (APt.res f a) (APt.res f b) = APt.res f (glue N₁ N₂ a b) := by
  refine MonoidHom.ext fun n => ?_
  exact (map_mul (𝒪.map f).hom _ _).symm

lemma glue_cut {U : Cᵒᵖ} (c : APt 𝒪 (N₁.prod N₂) U) :
    glue N₁ N₂ (cut₁ N₁ N₂ c) (cut₂ N₁ N₂ c) = c := by
  refine MonoidHom.ext fun n => ?_
  refine (c.map_mul _ _).symm.trans (congrArg c ?_)
  refine Multiplicative.toAdd.injective (Subtype.ext (Prod.ext ?_ ?_))
  · exact add_zero _
  · exact zero_add _

lemma cut₁_glue {U : Cᵒᵖ} (a : APt 𝒪 N₁ U) (b : APt 𝒪 N₂ U) :
    cut₁ N₁ N₂ (glue N₁ N₂ a b) = a := by
  refine MonoidHom.ext fun n => ?_
  have h1 : b (Multiplicative.ofAdd (⟨0, N₂.zero_mem⟩ : N₂)) = 1 := b.map_one
  exact (congrArg (_ * ·) h1).trans (mul_one _)

lemma cut₂_glue {U : Cᵒᵖ} (a : APt 𝒪 N₁ U) (b : APt 𝒪 N₂ U) :
    cut₂ N₁ N₂ (glue N₁ N₂ a b) = b := by
  refine MonoidHom.ext fun n => ?_
  have h1 : a (Multiplicative.ofAdd (⟨0, N₁.zero_mem⟩ : N₁)) = 1 := a.map_one
  exact (congrArg (· * _) h1).trans (one_mul _)

lemma glue_mul {U : Cᵒᵖ} (h : APt 𝒪 M₁ U) (a : APt 𝒪 N₁ U) (b : APt 𝒪 N₂ U) :
    glue N₁ N₂ (APt.toMagnet N₁ h * a) b =
      APt.toMagnet (N₁.prod N₂) (inlPt h) * glue N₁ N₂ a b := by
  refine MonoidHom.ext fun n => ?_
  exact mul_assoc _ _ _

lemma glue_mul' {U : Cᵒᵖ} (h : APt 𝒪 M₂ U) (a : APt 𝒪 N₁ U) (b : APt 𝒪 N₂ U) :
    glue N₁ N₂ a (APt.toMagnet N₂ h * b) =
      APt.toMagnet (N₁.prod N₂) (inrPt h) * glue N₁ N₂ a b := by
  refine MonoidHom.ext fun n => ?_
  exact mul_left_comm _ _ _

lemma split_pt {U : Cᵒᵖ} (h : APt 𝒪 (M₁ × M₂) U) :
    inlPt (h.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inl M₁ M₂))) *
      inrPt (h.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inr M₁ M₂))) = h := by
  refine MonoidHom.ext fun n => ?_
  refine (h.map_mul _ _).symm.trans (congrArg h ?_)
  exact Multiplicative.toAdd.injective (Prod.ext (add_zero _) (zero_add _))

lemma app_congr' {M : Type*} [AddCommMonoid M] {F : Cᵒᵖ ⥤ Type u}
    {act : AAction 𝒪 M F} {N : AddSubmonoid M} {T T' : C}
    (φ : AttractorPt act N T) {t t' : T' ⟶ T} (h : t = t') {a : APt 𝒪 N (op T')} :
    φ.app t a = φ.app t' a := by
  subst h; rfl

/-- The bijection of §16.4 (ii) on points. -/
def stagesEquiv (T : C) :
    AttractorPt act (N₁.prod N₂) T ≃ BigPt (actSnd act N₁) N₂ T where
  toFun φ :=
    { app := fun {T'} t b =>
        { app := fun {T''} t' a => φ.app (t' ≫ t) (glue N₁ N₂ a (APt.res t'.op b))
          naturality := fun {T₂ T₃} s t' a => by
            rw [Category.assoc, ← φ.naturality s (t' ≫ t), ← glue_res, ← APt.res_comp]
            rfl
          equivariant := fun {T''} t' k a => by
            rw [glue_mul]
            exact φ.equivariant _ _ _ }
      naturality := fun {T' T''} s t b => by
        refine AttractorPt.ext ?_
        funext T₂ t' a
        change φ.app (t' ≫ s ≫ t) (glue N₁ N₂ a (APt.res t'.op (APt.res s.op b))) =
          φ.app ((t' ≫ s) ≫ t) (glue N₁ N₂ a (APt.res (t' ≫ s).op b))
        rw [Category.assoc, op_comp, APt.res_comp]
      equivariant := fun {T'} t k b => by
        refine AttractorPt.ext ?_
        funext T₂ t' a
        change φ.app (t' ≫ t) (glue N₁ N₂ a (APt.res t'.op (APt.toMagnet N₂ k * b))) =
          act.smul (inrPt (APt.res t'.op k)) (φ.app (t' ≫ t) (glue N₁ N₂ a (APt.res t'.op b)))
        rw [APt.res_mul, ← φ.equivariant, ← glue_mul']
        rfl }
  invFun ψ :=
    { app := fun {T'} t c => AttractorPt.app (ψ.app t (cut₂ N₁ N₂ c)) (𝟙 T') (cut₁ N₁ N₂ c)
      naturality := fun {T' T''} s t c => by
        have e := ψ.naturality s t (cut₂ N₁ N₂ c)
        have e' := congrArg (fun χ : AttractorPt (actFst act) N₁ T'' =>
          χ.app (𝟙 T'') (cut₁ N₁ N₂ (APt.res s.op c))) e
        refine e'.trans ?_
        have n := AttractorPt.naturality (ψ.app t (cut₂ N₁ N₂ c)) s (𝟙 T') (cut₁ N₁ N₂ c)
        refine Eq.trans ?_ n
        change AttractorPt.app (ψ.app t (cut₂ N₁ N₂ c)) (𝟙 T'' ≫ s) (cut₁ N₁ N₂ (APt.res s.op c)) = _
        rw [Category.id_comp, Category.comp_id]
        rfl
      equivariant := fun {T'} t k c => by
        have hc₂ : cut₂ N₁ N₂ (APt.toMagnet (N₁.prod N₂) k * c) =
            APt.toMagnet N₂ (k.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inr M₁ M₂))) *
              cut₂ N₁ N₂ c := rfl
        have hc₁ : cut₁ N₁ N₂ (APt.toMagnet (N₁.prod N₂) k * c) =
            APt.toMagnet N₁ (k.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inl M₁ M₂))) *
              cut₁ N₁ N₂ c := rfl
        rw [hc₂, hc₁]
        set k₁ := k.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inl M₁ M₂))
        set k₂ := k.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inr M₁ M₂))
        have e₂ := congrArg (fun χ : AttractorPt (actFst act) N₁ T' =>
          χ.app (𝟙 T') (APt.toMagnet N₁ k₁ * cut₁ N₁ N₂ c)) (ψ.equivariant t k₂ (cut₂ N₁ N₂ c))
        refine e₂.trans ?_
        change act.smul (inrPt (APt.res (𝟙 T').op k₂)) (AttractorPt.app (ψ.app t (cut₂ N₁ N₂ c)) (𝟙 T')
          (APt.toMagnet N₁ k₁ * cut₁ N₁ N₂ c)) = _
        rw [AttractorPt.equivariant (ψ.app t (cut₂ N₁ N₂ c)) (𝟙 T') k₁ (cut₁ N₁ N₂ c)]
        change act.smul _ (act.smul (inlPt k₁) _) = _
        rw [← act.mul_smul]
        congr 1
        have hk₂ : APt.res (𝟙 T').op k₂ = k₂ := by simp
        rw [hk₂, mul_comm]
        exact split_pt k }
  left_inv φ := by
    refine AttractorPt.ext ?_
    funext T' t c
    change φ.app (𝟙 T' ≫ t) (glue N₁ N₂ (cut₁ N₁ N₂ c) (APt.res (𝟙 T').op (cut₂ N₁ N₂ c))) = _
    rw [Category.id_comp]
    simp only [op_id, APt.res_id, glue_cut]
  right_inv ψ := by
    refine BigPt.ext ?_
    funext T' t b
    refine AttractorPt.ext ?_
    funext T₂ t' a
    change AttractorPt.app (ψ.app (t' ≫ t) (cut₂ N₁ N₂ (glue N₁ N₂ a (APt.res t'.op b)))) (𝟙 T₂)
      (cut₁ N₁ N₂ (glue N₁ N₂ a (APt.res t'.op b))) = _
    rw [cut₁_glue, cut₂_glue]
    have e := congrArg (fun χ : AttractorPt (actFst act) N₁ T₂ => χ.app (𝟙 T₂) a) (ψ.naturality t' t b)
    refine e.trans ?_
    change AttractorPt.app (ψ.app t b) (𝟙 T₂ ≫ t') a = _
    rw [Category.id_comp]


lemma stagesEquiv_baseChange {T T' : C} (s : T' ⟶ T) (φ : AttractorPt act (N₁.prod N₂) T) :
    stagesEquiv act N₁ N₂ T' (φ.baseChange s) = (stagesEquiv act N₁ N₂ T φ).baseChange s := by
  refine BigPt.ext ?_
  funext T₁ t b
  refine AttractorPt.ext ?_
  funext T₂ t' a
  exact app_congr' (act := act) (N := N₁.prod N₂) (T := T) φ (by simp)

variable {act N₁ N₂}

/-- **§16.4 (ii).** `X^{N₁ × N₂} = (X^{N₁})^{N₂}` for `D(M₁ × M₂)` acting on a presheaf `X` on any
site, e.g. an algebraic space on `BigFppfOver`: if `Y₁` represents the first stage (attractor for the
factor `M₁`) and `Y₂` the second stage (attractor for `M₂` on `Y₁`), then `Y₂` represents
`X^{N₁×N₂}`. -/
def stagesRep {Y₁ Y₂ : Cᵒᵖ ⥤ Type u} (r₁ : RepresentsAttractor (S16R.actFst act) N₁ Y₁)
    (r₂ : RepresentsAttractor ((smallModelOfRep r₁).transport (S16R.actSnd act N₁)) N₂ Y₂) :
    RepresentsAttractor act (N₁.prod N₂) Y₂ where
  equiv T := (r₂.equiv T).trans (((smallModelOfRep r₁).ptEquiv (S16R.actSnd act N₁) N₂ T).trans
    (stagesEquiv act N₁ N₂ T).symm)
  naturality {T T'} s z := by
    apply (stagesEquiv act N₁ N₂ T').injective
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
    rw [stagesEquiv_baseChange, Equiv.apply_symm_apply, r₂.naturality]
    rfl

end Prod

/-! #### Example (iii): towers -/

section Tower

/-- A succession of `r` attractors under `G_m` from `X` to `Y`, each represented in the universe of
`𝒪`: `G_m = D(ℤ)` acts on the stage `X`, and the next stage represents `X^ℕ`. -/
inductive GmTowerR : (Cᵒᵖ ⥤ Type u) → (Cᵒᵖ ⥤ Type u) → ℕ → Prop
  | nil (X) : GmTowerR X X 0
  | step {X X' Y r} (a : AAction 𝒪 (ULift.{u} ℤ) X)
      (h : Nonempty (RepresentsAttractor a natMagnet X')) :
      GmTowerR X' Y r → GmTowerR X Y (r + 1)

/-- `X^⊤ = X`, as a representation (Fact 3.6). -/
def repTop {M : Type*} [AddCommMonoid M] {F : Cᵒᵖ ⥤ Type u} (act : AAction 𝒪 M F) :
    RepresentsAttractor act ⊤ F where
  equiv T := (attractorTopEquiv act T).symm
  naturality {T T'} s z := by
    apply (attractorTopEquiv act T').injective
    rw [Equiv.apply_symm_apply]
    have h := AttractorPt.toPoint_baseChange (act := act) (N := ⊤) s ((attractorTopEquiv act T).symm z)
    refine Eq.trans ?_ h.symm
    congr 1
    exact ((attractorTopEquiv act T).apply_symm_apply z).symm

/-- **§16.4 (iii).** If `M = ℤ^r`, `N = ℕ^r` and `𝔸(ℕ)_T` is in the site for all `T` (always the case
on `BigFppfOver`, see `exists_gmTower_fppf`), then `X ↦ X^N` is `r` stages of `G_m`-attractors. -/
theorem exists_gmTowerR (hU : ∀ T : C, Nonempty (UniversalPoint 𝒪 natMagnet.{u} T)) :
    ∀ (r : ℕ) (X : Cᵒᵖ ⥤ Type u) (act : AAction 𝒪 (ZP.{u} r) X),
      ∃ Y, GmTowerR (𝒪 := 𝒪) X Y r ∧ Nonempty (RepresentsAttractor act (NP r) Y)
  | 0, X, act => ⟨X, .nil X, ⟨repTop act⟩⟩
  | r + 1, X, act => by
    obtain ⟨Y₁, ⟨r₁⟩⟩ := exists_rep (S16R.actFst act) natMagnet hU
    obtain ⟨Y, hY, ⟨i⟩⟩ := exists_gmTowerR hU r Y₁
      ((smallModelOfRep r₁).transport (S16R.actSnd act natMagnet))
    exact ⟨Y, .step (S16R.actFst act) ⟨r₁⟩ hY, ⟨stagesRep r₁ i⟩⟩

end Tower

/-! #### Example (i) -/

section Inner

variable {M : Type*} [AddCommMonoid M] {F : Cᵒᵖ ⥤ Type u} (act : AAction 𝒪 M F)
  {N L : AddSubmonoid M} (hNL : N ≤ L)

/-- `N` seen as a magnet of `L`. -/
abbrev innerMagnet (N L : AddSubmonoid M) : AddSubmonoid L := N.comap L.subtype

/-- `𝔸(N') → 𝔸(N)` where `N' = N` is seen in `L`. -/
def upPt (hNL : N ≤ L) {U : Cᵒᵖ} (b : APt 𝒪 (innerMagnet N L) U) : APt 𝒪 N U :=
  b.comp (AddMonoidHom.toMultiplicative
    { toFun := fun n => ⟨⟨n.1, hNL n.2⟩, n.2⟩, map_zero' := rfl, map_add' := fun _ _ => rfl })

/-- `𝔸(N) → 𝔸(N')`. -/
def downPt {U : Cᵒᵖ} (c : APt 𝒪 N U) : APt 𝒪 (innerMagnet N L) U :=
  c.comp (AddMonoidHom.toMultiplicative
    { toFun := fun n => ⟨n.1.1, n.2⟩, map_zero' := rfl, map_add' := fun _ _ => rfl })

/-- The bijection of §16.4 (i) on points. -/
def innerEquiv (T : C) :
    AttractorPt act N T ≃ BigPt (magnetAction act L) (innerMagnet N L) T where
  toFun φ :=
    { app := fun {T'} t b =>
        { app := fun {T''} t' a =>
            φ.app (t' ≫ t) (APt.restrict hNL a * upPt hNL (APt.res t'.op b))
          naturality := fun {T₂ T₃} s t' a => by
            rw [← φ.naturality s (t' ≫ t), Category.assoc, APt.res_mul, op_comp, APt.res_comp]
            rfl
          equivariant := fun {T''} t' k a => by
            rw [← φ.equivariant]
            congr 1
            refine MonoidHom.ext fun n => ?_
            exact mul_assoc _ _ _ }
      naturality := fun {T' T''} s t b => by
        refine AttractorPt.ext ?_
        funext T₂ t' a
        change φ.app (t' ≫ s ≫ t) (_ * upPt hNL (APt.res t'.op (APt.res s.op b))) =
          φ.app ((t' ≫ s) ≫ t) (_ * upPt hNL (APt.res (t' ≫ s).op b))
        rw [Category.assoc, op_comp, APt.res_comp]
      equivariant := fun {T'} t k b => by
        refine AttractorPt.ext ?_
        funext T₂ t' a
        change φ.app (t' ≫ t) (APt.restrict hNL a *
            upPt hNL (APt.res t'.op (APt.toMagnet (innerMagnet N L) k * b))) =
          φ.app (t' ≫ t) (APt.restrict hNL (APt.res t'.op k * a) * upPt hNL (APt.res t'.op b))
        congr 1
        refine MonoidHom.ext fun n => ?_
        have key : ∀ (x : 𝒪.obj (op T₂)) (y w : 𝒪.obj (op T')), x * (𝒪.map t'.op).hom (y * w) =
            ((𝒪.map t'.op).hom y * x) * (𝒪.map t'.op).hom w := by
          intro x y w
          rw [map_mul]
          ring
        exact key _ _ _ }
  invFun ψ :=
    { app := fun {T'} t c => AttractorPt.app (ψ.app t (downPt c)) (𝟙 T') 1
      naturality := fun {T' T''} s t c => by
        have e := congrArg (fun χ : AttractorPt act L T'' => χ.app (𝟙 T'') 1)
          (ψ.naturality s t (downPt c))
        refine e.trans ?_
        have n := AttractorPt.naturality (ψ.app t (downPt c)) s (𝟙 T') 1
        have h1 : APt.res (𝒪 := 𝒪) (P := L) s.op 1 = 1 := by ext p; simp
        rw [h1, Category.comp_id] at n
        refine Eq.trans ?_ n
        change AttractorPt.app (ψ.app t (downPt c)) (𝟙 T'' ≫ s) 1 = _
        rw [Category.id_comp]
      equivariant := fun {T'} t k c => by
        have hc : downPt (APt.toMagnet N k * c) =
            APt.toMagnet (innerMagnet N L) (APt.toMagnet L k) * downPt c := rfl
        rw [hc]
        have e := congrArg (fun χ : AttractorPt act L T' => χ.app (𝟙 T') 1)
          (ψ.equivariant t (APt.toMagnet L k) (downPt c))
        refine e.trans ?_
        change AttractorPt.app (ψ.app t (downPt c)) (𝟙 T') (APt.res (𝟙 T').op (APt.toMagnet L k) * 1) = _
        have h1 : APt.res (𝟙 T').op (APt.toMagnet L k) * 1 = APt.toMagnet L k * 1 := by simp
        rw [h1]
        exact AttractorPt.equivariant (ψ.app t (downPt c)) (𝟙 T') k 1 }
  left_inv φ := by
    refine AttractorPt.ext ?_
    funext T' t c
    change φ.app (𝟙 T' ≫ t) (APt.restrict hNL 1 * upPt hNL (APt.res (𝟙 T').op (downPt c))) = _
    have e : APt.restrict hNL (1 : APt 𝒪 L (op T')) * upPt hNL (APt.res (𝟙 T').op (downPt c)) = c := by
      rw [APt.restrict_one, one_mul]
      simp only [op_id, APt.res_id]
      rfl
    rw [e, Category.id_comp]
  right_inv ψ := by
    refine BigPt.ext ?_
    funext T' t b
    refine AttractorPt.ext ?_
    funext T₂ t' a
    change AttractorPt.app (ψ.app (t' ≫ t)
      (downPt (APt.restrict hNL a * upPt hNL (APt.res t'.op b)))) (𝟙 T₂) 1 = _
    have hd : downPt (APt.restrict hNL a * upPt hNL (APt.res t'.op b)) =
        APt.toMagnet (innerMagnet N L) a * APt.res t'.op b := rfl
    rw [hd]
    have e := congrArg (fun χ : AttractorPt act L T₂ => χ.app (𝟙 T₂) 1)
      (ψ.equivariant (t' ≫ t) a (APt.res t'.op b))
    refine e.trans ?_
    change AttractorPt.app (ψ.app (t' ≫ t) (APt.res t'.op b)) (𝟙 T₂) (APt.res (𝟙 T₂).op a * 1) = _
    have e' := congrArg (fun χ : AttractorPt act L T₂ => χ.app (𝟙 T₂) (APt.res (𝟙 T₂).op a * 1))
      (ψ.naturality t' t b)
    refine e'.trans ?_
    change AttractorPt.app (ψ.app t b) (𝟙 T₂ ≫ t') (APt.res (𝟙 T₂).op a * 1) = _
    have h1 : APt.res (𝟙 T₂).op a * 1 = a := by simp
    rw [h1, Category.id_comp]

lemma innerEquiv_baseChange {T T' : C} (s : T' ⟶ T) (φ : AttractorPt act N T) :
    innerEquiv act hNL T' (φ.baseChange s) = (innerEquiv act hNL T φ).baseChange s := by
  refine BigPt.ext ?_
  funext T₁ t b
  refine AttractorPt.ext ?_
  funext T₂ t' a
  exact app_congr' (act := act) (N := N) (T := T) φ (by simp)

variable {act hNL}

/-- **§16.4 (i)**, second step: for magnets `N ⊆ L`, if `Y₁` represents `X^L` and `Y₂` the attractor
of `Y₁` under `𝔸(L)` (Remark 3.12) for `N` seen in `L`, then `Y₂` represents `X^N`. -/
def innerRep (hNL : N ≤ L) {Y₁ Y₂ : Cᵒᵖ ⥤ Type u} (r₁ : RepresentsAttractor act L Y₁)
    (r₂ : RepresentsAttractor ((smallModelOfRep r₁).transport (magnetAction act L))
      (innerMagnet N L) Y₂) :
    RepresentsAttractor act N Y₂ where
  equiv T := (r₂.equiv T).trans (((smallModelOfRep r₁).ptEquiv (magnetAction act L) _ T).trans
    (innerEquiv act hNL T).symm)
  naturality {T T'} s z := by
    apply (innerEquiv act hNL T').injective
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
    rw [innerEquiv_baseChange, Equiv.apply_symm_apply, r₂.naturality]
    rfl

end Inner

end S16R

/-! ### §16.4 instantiated on `BigFppfOver` -/

section FppfGm

open S16R

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- `𝔸(N)_T` is an object of the site if `N` is countable. -/
theorem nonempty_universalPoint {M : Type u} [AddCommMonoid M] (N : AddSubmonoid M) [Countable N]
    (T : BigFppfOver B S hS) : Nonempty (UniversalPoint (fppfO B S hS) N T) :=
  ⟨monAffUniversal N (contains_zmon_of_countable hS N) T⟩

instance : Countable natMagnet.{u} :=
  inferInstance

/-- **§16.4 (ii)** on the big fppf site: `X` an algebraic space (or presheaf) with an action of
`D(M₁ × M₂)`, with `N₁, N₂` countable. There are a first stage `Y₁`, the attractor for `M₁`, with an
action of `M₂`, and a second stage `Y₂`, its attractor for `N₂`, which represents `X^{N₁×N₂}`.
For `M₁ = M₂ = ℤ`, `N₁ = N₂ = ℕ`, this is two stages of `G_m`-attractors. -/
theorem stages_fppf {M₁ M₂ : Type u} [AddCommMonoid M₁] [AddCommMonoid M₂]
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (act : AAction (fppfO B S hS) (M₁ × M₂) X)
    (N₁ : AddSubmonoid M₁) (N₂ : AddSubmonoid M₂) [Countable N₁] [Countable N₂] :
    ∃ (Y₁ Y₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (r₁ : RepresentsAttractor (S16R.actFst act) N₁ Y₁),
      Nonempty (RepresentsAttractor ((smallModelOfRep r₁).transport (S16R.actSnd act N₁)) N₂ Y₂) ∧
      Nonempty (RepresentsAttractor act (N₁.prod N₂) Y₂) := by
  obtain ⟨Y₁, ⟨r₁⟩⟩ := exists_rep (S16R.actFst act) N₁ (nonempty_universalPoint N₁)
  obtain ⟨Y₂, ⟨r₂⟩⟩ := exists_rep ((smallModelOfRep r₁).transport (S16R.actSnd act N₁)) N₂
    (nonempty_universalPoint N₂)
  exact ⟨Y₁, Y₂, r₁, ⟨r₂⟩, ⟨stagesRep r₁ r₂⟩⟩

/-- **§16.4 (iii)** on the big fppf site: if `M = ℤ^r`, `N = ℕ^r`, then for any algebraic space (or
presheaf) `X` with an action of `D(ℤ^r)`, `X ↦ X^N` is `r` stages of `G_m`-attractors. -/
theorem exists_gmTower_fppf (r : ℕ) {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (act : AAction (fppfO B S hS) (ZP.{u} r) X) :
    ∃ Y, GmTowerR (𝒪 := fppfO B S hS) X Y r ∧ Nonempty (RepresentsAttractor act (NP r) Y) :=
  exists_gmTowerR (fun T => nonempty_universalPoint natMagnet T) r X act

/-- **§16.4 (i)**, first step, without any retraction `M → ℤα`: for `M` a finitely generated abelian
group, `α ∈ M`, and `X` an fppf sheaf (an algebraic space) with an action of `D(M)_S`, the attractor
`X^{ℤα}` is the fixed-point functor `X^{D(M/ℤα)}` (Proposition 3.35). -/
noncomputable def fixedStep_fppf {M : Type u} [AddCommGroup M] [AddGroup.FG M]
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (act : AAction (fppfO B S hS) M X) (α : M) (T : BigFppfOver B S hS) :
    (fixedPoints (quotientAction act (AddSubgroup.zmultiples α))).obj (op T) ≃
      AttractorPt act (AddSubgroup.zmultiples α).toAddSubmonoid T :=
  attractorFixedEquivOfCover ((isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf)
    (fun a => extSieve_mem _ a) T

/-- **§16.4 (i)** on the big fppf site: `M` a finitely generated abelian group, `α ∈ M`, `L = ℤα`,
`N = [α⟩`. The first stage `Y₁` is the fixed-point functor of `D(M/L)` and has an action of `𝔸(L)`;
the second stage `Y₂` is the attractor of `Y₁` for `𝔸(L)`, `N` seen in `L`, and represents `X^{[α⟩}`.
That second stage is an attractor under `𝔸(ℤα)`, which is `G_m` when `α` is not torsion. -/
theorem stage_i_fppf {M : Type u} [AddCommGroup M] [AddGroup.FG M]
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (act : AAction (fppfO B S hS) M X) (α : M) :
    let L := (AddSubgroup.zmultiples α).toAddSubmonoid
    let N := AddSubmonoid.closure {α}
    ∃ (Y₁ Y₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (r₁ : RepresentsAttractor act L Y₁),
      Nonempty (∀ T, Y₁.obj (op T) ≃
        (fixedPoints (quotientAction act (AddSubgroup.zmultiples α))).obj (op T)) ∧
      Nonempty (RepresentsAttractor ((smallModelOfRep r₁).transport (magnetAction act L))
        (innerMagnet N L) Y₂) ∧
      Nonempty (RepresentsAttractor act N Y₂) := by
  intro L N
  have : Countable M := countable_of_fg M
  have hNL : N ≤ L := by
    refine (AddSubmonoid.closure_le).2 ?_
    rintro _ rfl
    exact AddSubgroup.mem_zmultiples _
  obtain ⟨Y₁, ⟨r₁⟩⟩ := exists_rep act L (nonempty_universalPoint L)
  obtain ⟨Y₂, ⟨r₂⟩⟩ := exists_rep ((smallModelOfRep r₁).transport (magnetAction act L))
    (innerMagnet N L) (nonempty_universalPoint _)
  exact ⟨Y₁, Y₂, r₁, ⟨fun T => (r₁.equiv T).trans (fixedStep_fppf hX act α T).symm⟩, ⟨r₂⟩,
    ⟨innerRep hNL r₁ r₂⟩⟩

end FppfGm

end AlgMag

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AddMonoidAlgebra


namespace AlgMag.Mono

noncomputable section

variable {M : Type u} [AddCommGroup M]

/-- The localization `N[-f] ⊆ M`, the monoid of the open `D(f)` of `spec N`. -/
def locAt (N : AddSubmonoid M) (f : M) : AddSubmonoid M where
  carrier := {x | ∃ k : ℕ, x + k • f ∈ N}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨k, hk⟩ ⟨l, hl⟩
    refine ⟨k + l, ?_⟩
    have := N.add_mem hk hl
    rwa [add_add_add_comm, ← add_nsmul] at this

lemma le_locAt (N : AddSubmonoid M) (f : M) : N ≤ locAt N f := fun x hx => ⟨0, by simpa using hx⟩

/-- The points of `spec N`: prime ideals of `N`, given by their complements, the faces of `N`. -/
def SpecPt (N : AddSubmonoid M) : Type u := {F : AddSubmonoid M // F ≤ N ∧ FaceCond F N}

/-- The open `D(f)` of `spec N`: the faces containing `f`. -/
def basicD (N : AddSubmonoid M) (f : M) : Set (SpecPt N) := {F | f ∈ F.1}

/-- **Minimal monoscheme theory: toric monoschemes.** A toric monoscheme with group `M` (Ogus II
§1.9, connected) presented by its affine opens: the poset `J` of the affine opens `spec(N i)`,
`N i ⊆ M`; each is a principal open of the larger ones, the intersection of two affine opens in a
third one is the affine open of `N i + N j`, and all contain the generic open `spec M`. -/
structure ToricMono (M : Type u) [AddCommGroup M] where
  /-- The affine opens. -/
  J : Type u
  [ord : PartialOrder J]
  /-- `Γ(spec(N i), 𝓜)`. -/
  N : J → AddSubmonoid M
  fg : ∀ i, (N i).FG
  anti : ∀ {i j}, i ≤ j → N j ≤ N i
  loc : ∀ {i j}, i ≤ j → ∃ f ∈ N j, N i = locAt (N j) f
  inter : ∀ {i j k}, i ≤ k → j ≤ k → ∃ l, l ≤ i ∧ l ≤ j ∧ N l = N i ⊔ N j
  generic : J
  generic_le : ∀ i, generic ≤ i
  N_generic : N generic = ⊤

attribute [instance] ToricMono.ord

/-- `ℤ[N] → ℤ[N']` for `N ≤ N'`. -/
def trans {N N' : AddSubmonoid M} (h : N ≤ N') : ZMon N ⟶ ZMon N' :=
  CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom _ (AddSubmonoid.inclusion h))

lemma trans_single {N N' : AddSubmonoid M} (h : N ≤ N') (n : N) (r : ULift.{u} ℤ) :
    (trans h).hom (single n r) = single (AddSubmonoid.inclusion h n) r := by
  simp [trans]

/-- `ℤ[N[-f]]` is the localization of `ℤ[N]` at `X^f`. -/
theorem isLocalization_away {N N' : AddSubmonoid M} (h : N ≤ N') {f : M} (hf : f ∈ N)
    (hN : N' = locAt N f) :
    letI := (trans h).hom.toAlgebra
    IsLocalization.Away (single (⟨f, hf⟩ : N) (1 : ULift.{u} ℤ) : AddMonoidAlgebra (ULift.{u} ℤ) N)
      (AddMonoidAlgebra (ULift.{u} ℤ) N') := by
  subst hN
  letI := (trans h).hom.toAlgebra
  have hmap : ∀ x, algebraMap (AddMonoidAlgebra (ULift.{u} ℤ) N)
      (AddMonoidAlgebra (ULift.{u} ℤ) (locAt N f)) x = (trans h).hom x := fun _ => rfl
  have hfm : -f ∈ locAt N f := ⟨1, by simpa using N.zero_mem⟩
  have hfn : f ∈ locAt N f := h hf
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, k, rfl⟩
    rw [map_pow, hmap, trans_single]
    refine IsUnit.pow k (IsUnit.of_mul_eq_one (single (⟨-f, hfm⟩ : locAt N f) 1) ?_)
    rw [AddMonoidAlgebra.single_mul_single, one_mul]
    have : (AddSubmonoid.inclusion h ⟨f, hf⟩ + ⟨-f, hfm⟩ : locAt N f) = 0 :=
      Subtype.ext (add_neg_cancel f)
    rw [this]
    rfl
  · intro z
    have key : ∃ k : ℕ, ∃ x : AddMonoidAlgebra (ULift.{u} ℤ) N,
        z * (single (⟨f, hfn⟩ : locAt N f) 1) ^ k = (trans h).hom x := by
      induction z using AddMonoidAlgebra.induction_linear with
      | zero => exact ⟨0, 0, by simp⟩
      | add a b ha hb =>
        obtain ⟨k, x, hx⟩ := ha
        obtain ⟨l, y, hy⟩ := hb
        let g : AddMonoidAlgebra (ULift.{u} ℤ) N := single ⟨f, hf⟩ 1
        have hg : (trans h).hom g = single (⟨f, hfn⟩ : locAt N f) 1 := trans_single h _ _
        refine ⟨k + l, x * g ^ l + y * g ^ k, ?_⟩
        rw [map_add, map_mul, map_mul, map_pow, map_pow, hg, ← hx, ← hy, pow_add]
        ring
      | single n r =>
        obtain ⟨k, hk⟩ := n.2
        refine ⟨k, single ⟨n + k • f, hk⟩ r, ?_⟩
        rw [trans_single, AddMonoidAlgebra.single_pow, AddMonoidAlgebra.single_mul_single,
          one_pow, mul_one]
        congr 1
    obtain ⟨k, x, hx⟩ := key
    refine ⟨⟨x, ⟨single (⟨f, hf⟩ : N) 1 ^ k, k, rfl⟩⟩, ?_⟩
    change z * algebraMap _ _ (single (⟨f, hf⟩ : N) 1 ^ k) = algebraMap _ _ x
    rw [hmap, hmap, hx.symm, map_pow, trans_single]
    rfl
  · intro x y hxy
    refine ⟨1, ?_⟩
    have hinj : Function.Injective (trans h).hom := by
      intro a b hab
      apply AddMonoidAlgebra.coeff_injective
      exact Finsupp.mapDomain_injective (AddSubmonoid.inclusion_injective h)
        (congrArg AddMonoidAlgebra.coeff hab)
    rw [hinj hxy]

variable (X : ToricMono M)

/-- The diagram of the affine opens `Spec ℤ[N i]`. -/
def chartF : X.J ⥤ Scheme.{u} where
  obj i := Spec (ZMon (X.N i))
  map {i j} g := Spec.map (trans (X.anti (leOfHom g)))
  map_id i := by
    rw [← Spec.map_id]
    congr 1
    refine MonAff.zmon_ext fun p => ?_
    rw [trans_single]
    rfl
  map_comp {i j k} a b := by
    rw [← Spec.map_comp]
    congr 1
    refine MonAff.zmon_ext fun p => ?_
    change _ = (trans _).hom ((trans _).hom _)
    rw [trans_single, trans_single, trans_single]
    rfl

instance {i j : X.J} (g : i ⟶ j) : IsOpenImmersion ((chartF X).map g) := by
  obtain ⟨f, hf, hN⟩ := X.loc (leOfHom g)
  letI := (trans (X.anti (leOfHom g))).hom.toAlgebra
  have := isLocalization_away (X.anti (leOfHom g)) hf hN
  exact IsOpenImmersion.of_isLocalization (single (⟨f, hf⟩ : X.N j) (1 : ULift.{u} ℤ))

end

end AlgMag.Mono

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AddMonoidAlgebra


namespace AlgMag.Mono

noncomputable section

variable {M : Type u} [AddCommGroup M] (X : ToricMono M)

lemma locAt_add {N : AddSubmonoid M} {f g : M} (hf : f ∈ N) (hg : g ∈ N) :
    locAt N f ⊔ locAt N g = locAt N (f + g) := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · rintro x ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have := N.add_mem hk (N.nsmul_mem hg k)
      rwa [add_assoc, ← nsmul_add] at this
    · rintro x ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have := N.add_mem hk (N.nsmul_mem hf k)
      rwa [add_assoc, ← nsmul_add, add_comm g f] at this
  · rintro x ⟨k, hk⟩
    have h1 : x + k • g ∈ locAt N f := ⟨k, by rwa [add_assoc, ← nsmul_add, add_comm g f]⟩
    have h2 : -(k • g) ∈ locAt N g := ⟨k, by simp [N.zero_mem]⟩
    have := AddSubmonoid.add_mem_sup h1 h2
    simpa using this

lemma range_chart {i k : X.J} (a : i ⟶ k) {f : M} (hf : f ∈ X.N k) (hN : X.N i = locAt (X.N k) f)
    (p : (chartF X).obj k) :
    p ∈ Set.range ((chartF X).map a) ↔
      (single (⟨f, hf⟩ : X.N k) (1 : ULift.{u} ℤ) : AddMonoidAlgebra (ULift.{u} ℤ) (X.N k)) ∉
        (show PrimeSpectrum (AddMonoidAlgebra (ULift.{u} ℤ) (X.N k)) from p).asIdeal := by
  letI := (trans (X.anti (leOfHom a))).hom.toAlgebra
  have := isLocalization_away (X.anti (leOfHom a)) hf hN
  have h := PrimeSpectrum.localization_away_comap_range (AddMonoidAlgebra (ULift.{u} ℤ) (X.N i))
    (single (⟨f, hf⟩ : X.N k) (1 : ULift.{u} ℤ) : AddMonoidAlgebra (ULift.{u} ℤ) (X.N k))
  exact Set.ext_iff.1 h p

/-- The diagram of charts is locally directed. -/
instance : ((chartF X) ⋙ Scheme.forget).IsLocallyDirected := by
  constructor
  intro i j k fi fj xi xj hxy
  obtain ⟨f, hf, hNi⟩ := X.loc (leOfHom fi)
  obtain ⟨g, hg, hNj⟩ := X.loc (leOfHom fj)
  obtain ⟨l, hli, hlj, hNl⟩ := X.inter (leOfHom fi) (leOfHom fj)
  have hxy' : (chartF X).map fi xi = (chartF X).map fj xj := hxy
  let p := (chartF X).map fi xi
  have h1 := (range_chart X fi hf hNi p).1 ⟨xi, rfl⟩
  have h2 := (range_chart X fj hg hNj p).1 ⟨xj, hxy'.symm⟩
  have hNl' : X.N l = locAt (X.N k) (f + g) := by rw [hNl, hNi, hNj, locAt_add hf hg]
  let lk : l ⟶ k := homOfLE (hli.trans (leOfHom fi))
  have h3 : p ∈ Set.range ((chartF X).map lk) := by
    refine (range_chart X lk ((X.N k).add_mem hf hg) hNl' p).2 ?_
    have e : (single (⟨f + g, (X.N k).add_mem hf hg⟩ : X.N k) (1 : ULift.{u} ℤ) :
        AddMonoidAlgebra (ULift.{u} ℤ) (X.N k)) = single ⟨f, hf⟩ 1 * single ⟨g, hg⟩ 1 := by
      rw [AddMonoidAlgebra.single_mul_single, mul_one]
      rfl
    rw [e]
    intro hm
    rcases (show PrimeSpectrum _ from p).isPrime.mem_or_mem hm with h | h
    · exact h1 h
    · exact h2 h
  obtain ⟨z, hz⟩ := h3
  let li : l ⟶ i := homOfLE hli
  let lj : l ⟶ j := homOfLE hlj
  refine ⟨l, li, lj, z, ?_, ?_⟩
  · apply ((chartF X).map fi).isOpenEmbedding.injective
    change (chartF X).map fi ((chartF X).map li z) = _
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp]
    exact hz
  · apply ((chartF X).map fj).isOpenEmbedding.injective
    change (chartF X).map fj ((chartF X).map lj z) = (chartF X).map fj xj
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, ← hxy']
    exact hz

/-- **§16.7, Ogus II Prop. 1.9.1.** The toric scheme `A(N)` of the toric monoscheme. -/
def toricScheme : Scheme.{u} := colimit (chartF X)

/-- **§16.7.** The chart `A(N_α) → A(N)`. -/
def chartι (i : X.J) : Spec (ZMon (X.N i)) ⟶ toricScheme X := colimit.ι (chartF X) i

/-- **§16.7.** `{A(N_α)}` is an open affine covering of `A(N)`: open immersions, -/
instance (i : X.J) : IsOpenImmersion (chartι X i) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (chartF X) i))

/-- **§16.7.** `{A(N_α)}` is an open affine covering of `A(N)`: jointly surjective. -/
theorem chart_surjective (x : toricScheme X) : ∃ (i : X.J) (y : Spec (ZMon (X.N i))), chartι X i y = x :=
  Scheme.IsLocallyDirected.ι_jointly_surjective (chartF X) x

/-- Two chart points with the same image in `A(N)` come from a smaller chart. -/
theorem chart_eq_iff {i j : X.J} (x : Spec (ZMon (X.N i))) (y : Spec (ZMon (X.N j))) :
    chartι X i x = chartι X j y ↔ ∃ (k : X.J) (a : k ⟶ i) (b : k ⟶ j) (z : (chartF X).obj k),
      (chartF X).map a z = x ∧ (chartF X).map b z = y :=
  Scheme.IsLocallyDirected.ι_eq_ι_iff (chartF X)

/-- The generic chart `Spec ℤ[M]` (the torus) is contained in every chart: `A(N)` is a toric scheme,
the map to `A(N)` from `D(M)` being an open immersion. -/
theorem torus_open : IsOpenImmersion (chartι X X.generic) := inferInstance

end

end AlgMag.Mono

#print axioms AlgMag.dualPointFppf
#print axioms AlgMag.tangentAttractorIsoFppf
#print axioms AlgMag.lieAttractorIsoFppf
#print axioms AlgMag.prop1615_i
#print axioms AlgMag.stages_fppf
#print axioms AlgMag.exists_gmTower_fppf
#print axioms AlgMag.stage_i_fppf
#print axioms AlgMag.Mono.chart_surjective
#print axioms AlgMag.Mono.chart_eq_iff
