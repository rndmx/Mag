/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec10LiftsCor
import StacksFrontier.AlgebraicGeometry.Limits.SurjectiveFinitePresentationCriterion

/-!
# Attractors and limits: Fact 3.19 for schemes

Mayeux, *Algebraic Magnetism*, Fact 3.19, schemes only: if `g : X → Y` is locally of finite
presentation and `X^N`, `Y^N` are representable by schemes, then `g^N` is locally of finite
presentation. The printed proof is "follows from the definitions and Tag 04AK"; here the argument
is that `Spec R_i[N]` is a limit, which gives `g^N` the limit lifting criterion.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.SmoothSchemes

open AlgMag.GB AlgMag.Lifts

/-- The functor `R ↦ R[P]`. -/
noncomputable def monFun (P : Type u) [AddCommMonoid P] : CommRingCat.{u} ⥤ CommRingCat.{u} where
  obj R := CommRingCat.of (AddMonoidAlgebra R P)
  map f := CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom P f.hom)
  map_id R := by
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    ext m
    simp [AddMonoidAlgebra.coeff_mapRingHom]
  map_comp f g := by
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    ext m
    simp [AddMonoidAlgebra.coeff_mapRingHom]

section Lim

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {P : Type u} [AddCommMonoid P]

lemma hse_comp' {W : Scheme.{u}} {E F : CommRingCat.{u}} (t : W ⟶ Spec E) (r : F ⟶ E) :
    homSpecEquiv W F (t ≫ Spec.map r) = r ≫ homSpecEquiv W E t := by
  change (Scheme.ΓSpecIso _).inv ≫ (t ≫ Spec.map r).appTop = r ≫ (Scheme.ΓSpecIso _).inv ≫ t.appTop
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality]

/-- The cone `Spec A` over `Spec R_i`. -/
noncomputable def specCone (G : I ⥤ CommRingCat.{u}ᵒᵖ) (A : CommRingCat.{u})
    (q : ∀ i, (G.obj i).unop ⟶ A) (hq : ∀ {i j : I} (f : i ⟶ j), (G.map f).unop ≫ q i = q j) :
    Cone (G ⋙ Scheme.Spec) where
  pt := Spec A
  π :=
    { app := fun i => Spec.map (q i)
      naturality := fun {i j} f => by
        change 𝟙 _ ≫ Spec.map (q j) = Spec.map (q i) ≫ Spec.map (G.map f).unop
        rw [Category.id_comp, ← Spec.map_comp, hq] }

lemma monFun_q (G : I ⥤ CommRingCat.{u}ᵒᵖ) (A : CommRingCat.{u})
    (q : ∀ i, (G.obj i).unop ⟶ A) (hq : ∀ {i j : I} (f : i ⟶ j), (G.map f).unop ≫ q i = q j)
    {i j : I} (f : i ⟶ j) :
    ((G ⋙ (monFun P).op).map f).unop ≫ (monFun P).map (q i) = (monFun P).map (q j) := by
  change (monFun P).map (G.map f).unop ≫ (monFun P).map (q i) = _
  rw [← Functor.map_comp, hq]

/-- If `Spec A` is the limit of `Spec R_i`, then `Spec A[P]` is the limit of `Spec R_i[P]`. -/
noncomputable def isLimitMon (G : I ⥤ CommRingCat.{u}ᵒᵖ) (A : CommRingCat.{u})
    (q : ∀ i, (G.obj i).unop ⟶ A) (hq : ∀ {i j : I} (f : i ⟶ j), (G.map f).unop ≫ q i = q j)
    (hl : IsLimit (specCone G A q hq)) :
    IsLimit (specCone (G ⋙ (monFun P).op) ((monFun P).obj A) (fun i => (monFun P).map (q i))
      (monFun_q G A q hq)) := by
  have hex : ∀ s : Cone ((G ⋙ (monFun P).op) ⋙ Scheme.Spec), ∃! l : s.pt ⟶ Spec ((monFun P).obj A),
      ∀ i, l ≫ Spec.map ((monFun P).map (q i)) = s.π.app i := by
    intro s
    let U := s.pt
    let cR : ∀ R : CommRingCat.{u}, R ⟶ (monFun P).obj R := fun R =>
      CommRingCat.ofHom AddMonoidAlgebra.singleZeroRingHom
    have hcR : ∀ {R R₁ : CommRingCat.{u}} (f : R ⟶ R₁), f ≫ cR R₁ = cR R ≫ (monFun P).map f := by
      intro R R₁ f
      ext x
      exact (AddMonoidAlgebra.mapRingHom_single _ _ _).symm
    let hv : ∀ i, ((monFun P).obj (G.obj i).unop) ⟶ Γ(U, ⊤) := fun i =>
      homSpecEquiv U _ (s.π.app i)
    have hw : ∀ {i j : I} (f : i ⟶ j), s.π.app i ≫ Spec.map ((monFun P).map (G.map f).unop) = s.π.app j := by
      intro i j f
      exact s.w f
    have hvw : ∀ {i j : I} (f : i ⟶ j), (monFun P).map (G.map f).unop ≫ hv i = hv j := by
      intro i j f
      change _ ≫ homSpecEquiv U _ _ = homSpecEquiv U _ _
      rw [← hse_comp', hw]
    let s₀ : Cone (G ⋙ Scheme.Spec) :=
      { pt := U
        π :=
          { app := fun i => s.π.app i ≫ Spec.map (cR _)
            naturality := fun {i j} f => by
              change 𝟙 _ ≫ s.π.app j ≫ Spec.map (cR _) =
                (s.π.app i ≫ Spec.map (cR _)) ≫ Spec.map (G.map f).unop
              rw [Category.id_comp, Category.assoc, ← Spec.map_comp, hcR, Spec.map_comp, ← hw f,
                Category.assoc] } }
    let u₀ : U ⟶ Spec A := hl.lift s₀
    have hu₀ : ∀ i, u₀ ≫ Spec.map (q i) = s.π.app i ≫ Spec.map (cR _) := fun i => hl.fac s₀ i
    let i₀ : I := Classical.choice IsCofiltered.nonempty
    let e₀ : ∀ i, (m : P) → Γ(U, ⊤) := fun i m => (hv i).hom (AddMonoidAlgebra.single m 1)
    have hesame : ∀ {i j : I} (f : i ⟶ j) (m : P), e₀ i m = e₀ j m := by
      intro i j f m
      have := congrArg (fun k => k.hom (AddMonoidAlgebra.single m 1)) (hvw f)
      change (hv i).hom (AddMonoidAlgebra.mapRingHom P _ (AddMonoidAlgebra.single m 1)) = _ at this
      rw [AddMonoidAlgebra.mapRingHom_single, map_one] at this
      exact this
    have he : ∀ i m, e₀ i m = e₀ i₀ m := fun i m =>
      (hesame (IsCofiltered.minToLeft i i₀) m).symm.trans (hesame (IsCofiltered.minToRight i i₀) m)
    let a : Multiplicative P →* Γ(U, ⊤) :=
      { toFun := fun m => e₀ i₀ (Multiplicative.toAdd m)
        map_one' := by
          change (hv i₀).hom (AddMonoidAlgebra.single 0 1) = 1
          exact map_one (hv i₀).hom
        map_mul' := fun x y => by
          change (hv i₀).hom (AddMonoidAlgebra.single (_ + _) 1) = _
          refine Eq.trans (congrArg (hv i₀).hom (show (AddMonoidAlgebra.single (Multiplicative.toAdd x +
              Multiplicative.toAdd y) (1 : (G.obj i₀).unop) : AddMonoidAlgebra _ P) =
              AddMonoidAlgebra.single (Multiplicative.toAdd x) 1 *
                AddMonoidAlgebra.single (Multiplicative.toAdd y) 1 from by
              rw [AddMonoidAlgebra.single_mul_single, one_mul]))
            (map_mul (hv i₀).hom (AddMonoidAlgebra.single (Multiplicative.toAdd x) 1)
              (AddMonoidAlgebra.single (Multiplicative.toAdd y) 1)) }
    let ψ : A →+* Γ(U, ⊤) := (homSpecEquiv U A u₀).hom
    let Ψ : AddMonoidAlgebra A P →+* Γ(U, ⊤) :=
      AddMonoidAlgebra.liftNCRingHom ψ a (fun _ _ => Commute.all _ _)
    have hΨ₀ : ∀ r, Ψ (AddMonoidAlgebra.single 0 r) = ψ r := fun r => by
      have e := AddMonoidAlgebra.liftNC_single (ψ : A →+ Γ(U, ⊤)) a (0 : P) r
      refine e.trans ?_
      refine (congrArg (fun z => ψ r * z) (map_one a)).trans (mul_one _)
    have hΨ₁ : ∀ m, Ψ (AddMonoidAlgebra.single m 1) = e₀ i₀ m := fun m => by
      have e := AddMonoidAlgebra.liftNC_single (ψ : A →+ Γ(U, ⊤)) a m 1
      refine e.trans ?_
      change ψ 1 * e₀ i₀ m = _
      rw [map_one, one_mul]
    have hhse : ∀ {R : CommRingCat.{u}} {x y : U ⟶ Spec R},
        homSpecEquiv U R x = homSpecEquiv U R y → x = y := fun h => (homSpecEquiv U _).injective h
    let l : U ⟶ Spec ((monFun P).obj A) := (homSpecEquiv U _).symm (CommRingCat.ofHom Ψ)
    have hl₀ : homSpecEquiv U _ l = CommRingCat.ofHom Ψ := Equiv.apply_symm_apply _ _
    have hu₁ : ∀ i (r : (G.obj i).unop), ψ ((q i).hom r) = (hv i).hom (AddMonoidAlgebra.single 0 r) := by
      intro i r
      have := congrArg (fun k => homSpecEquiv U _ k) (hu₀ i)
      simp only [hse_comp'] at this
      exact congrArg (fun k => k.hom r) this
    refine ⟨l, fun i => hhse ?_, fun m hm => hhse ?_⟩
    · rw [hse_comp', hl₀]
      refine CommRingCat.hom_ext (AddMonoidAlgebra.ringHom_ext (fun r => ?_) (fun m => ?_))
      · change Ψ (AddMonoidAlgebra.mapRingHom P (q i).hom (AddMonoidAlgebra.single 0 r)) = (hv i).hom _
        rw [AddMonoidAlgebra.mapRingHom_single, hΨ₀, hu₁]
      · change Ψ (AddMonoidAlgebra.mapRingHom P (q i).hom (AddMonoidAlgebra.single m 1)) = (hv i).hom _
        rw [AddMonoidAlgebra.mapRingHom_single, map_one, hΨ₁]
        exact (he i m).symm
    · rw [hl₀]
      have hmu : m ≫ Spec.map (cR A) = u₀ := by
        refine hl.uniq s₀ _ fun i => ?_
        change _ ≫ Spec.map (q i) = s.π.app i ≫ Spec.map (cR _)
        rw [← hm i, Category.assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp, hcR]
      refine CommRingCat.hom_ext (AddMonoidAlgebra.ringHom_ext (fun r => ?_) (fun n => ?_))
      · have := congrArg (fun k => (homSpecEquiv U A k).hom r) hmu
        simp only [hse_comp'] at this
        exact this.trans (hΨ₀ r).symm
      · have e₁ := congrArg (fun k => (homSpecEquiv U _ k).hom (AddMonoidAlgebra.single n 1)) (hm i₀)
        simp only [hse_comp'] at e₁
        change (homSpecEquiv U _ m).hom (AddMonoidAlgebra.mapRingHom P (q i₀).hom (AddMonoidAlgebra.single n 1)) =
          e₀ i₀ n at e₁
        rw [AddMonoidAlgebra.mapRingHom_single, map_one] at e₁
        exact e₁.trans (hΨ₁ n).symm
  exact IsLimit.ofExistsUnique fun s => (hex s).imp fun l hl => ⟨hl.1, fun m hm => hl.2 m hm⟩

omit [IsCofiltered I] in
lemma nat₁ {U A B : Scheme.{u}} [IsAffine A] [IsAffine B] (a : U ⟶ Spec Γ(A, ⊤)) (b : U ⟶ Spec Γ(B, ⊤))
    (f : A ⟶ B) (h : a ≫ Spec.map f.appTop = b) :
    b ≫ B.isoSpec.inv = (a ≫ A.isoSpec.inv) ≫ f := by
  subst h
  rw [Category.assoc, Category.assoc, Scheme.isoSpec_inv_naturality]

lemma fac₁ {U A B : Scheme.{u}} [IsAffine A] [IsAffine B] (l : U ⟶ A) (f : A ⟶ B)
    (b : U ⟶ Spec Γ(B, ⊤)) (h : l ≫ f = b ≫ B.isoSpec.inv) :
    (l ≫ A.isoSpec.hom) ≫ Spec.map f.appTop = b := by
  rw [Category.assoc, Scheme.isoSpec_hom_naturality, ← Category.assoc, h, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- `Spec` of an affine cofiltered limit, as the limit of `Spec Γ`. -/
noncomputable def isLimitBase (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)] (c : Cone D) (hc : IsLimit c)
    [IsAffine c.pt] :
    IsLimit (specCone (D ⋙ Scheme.Γ.rightOp) Γ(c.pt, ⊤) (fun i => (c.π.app i).appTop)
      (fun {i j} f => by
        change (D.map f).appTop ≫ (c.π.app i).appTop = (c.π.app j).appTop
        rw [← Scheme.Hom.comp_appTop, c.w])) := by
  refine IsLimit.ofExistsUnique fun s => ?_
  let s₀ : Cone D :=
    { pt := s.pt
      π :=
        { app := fun i => s.π.app i ≫ (D.obj i).isoSpec.inv
          naturality := fun {i j} f => by
            change 𝟙 _ ≫ s.π.app j ≫ _ = (s.π.app i ≫ _) ≫ D.map f
            rw [Category.id_comp]
            exact nat₁ _ _ _ (s.w f) } }
  refine ⟨hc.lift s₀ ≫ c.pt.isoSpec.hom, fun i => ?_, fun m hm => ?_⟩
  · exact fac₁ (hc.lift s₀) (c.π.app i) (s.π.app i) (hc.fac s₀ i)
  · have : m ≫ c.pt.isoSpec.inv = hc.lift s₀ :=
      hc.uniq s₀ _ fun i => (nat₁ m (s.π.app i) (c.π.app i) (hm i)).symm
    exact (Iso.comp_inv_eq _).1 this

end Lim

variable {S : Scheme.{u}} {M : Type u} [AddCommGroup M] (N : AddSubmonoid M)

/-- The value of an attractor point at the universal point. -/
noncomputable def vv {X : Over S} {aX : AAction (overO S) M (yoneda.obj X)} {T : Over S}
    [IsAffine T.left] (y : AttractorPt aX N T) : Ov (magnetπ N T.left ≫ T.hom) ⟶ X :=
  y.app (specUP N T _ rfl).π (specUP N T _ rfl).u

/-- The morphism `𝔸(N)_{T₀} → 𝔸(N)_T`. -/
noncomputable def muM {T₀ T : Over S} [IsAffine T₀.left] [IsAffine T.left] (j : T₀ ⟶ T) :
    Ov (magnetπ N T₀.left ≫ T₀.hom) ⟶ Ov (magnetπ N T.left ≫ T.hom) :=
  ovHom (AddMonoidAlgebra.mapRingHom N j.left.appTop.hom) (π_thick N j).symm

lemma val_base {X : Over S} {aX : AAction (overO S) M (yoneda.obj X)} {T₀ T : Over S}
    [IsAffine T₀.left] [IsAffine T.left] (j : T₀ ⟶ T) (y : AttractorPt aX N T) :
    muM N j ≫ vv N y = vv N (y.baseChange j) := by
  let U := specUP N T _ rfl
  let U₀ := specUP N T₀ _ rfl
  have hj : U.lift (U₀.π ≫ j) U₀.u = muM N j := by
    symm
    refine U.uniq _ _ _ (Over.OverMorphism.ext (π_sq N j).symm) (MonoidHom.ext fun n => ?_)
    refine (sp_inv _ _).trans (congrArg _ ?_)
    refine (AddMonoidAlgebra.mapRingHom_single _ _ _).trans ?_
    rw [map_one]
  have := y.app_eq_of_universal U (U₀.π ≫ j) U₀.u
  exact (congrArg (fun z : _ ⟶ U.P => z ≫ y.app U.π U.u) hj).symm.trans this.symm

lemma sp_map_comp {P : Type u} [AddCommMonoid P] {R₁ R₂ R₃ : Type u} [CommRing R₁] [CommRing R₂]
    [CommRing R₃] (g₁ : R₂ →+* R₃) (g₂ : R₁ →+* R₂) (g₃ : R₁ →+* R₃) (h : ∀ r, g₁ (g₂ r) = g₃ r) :
    sp (AddMonoidAlgebra.mapRingHom P g₁) ≫ sp (AddMonoidAlgebra.mapRingHom P g₂) =
      sp (AddMonoidAlgebra.mapRingHom P g₃) := by
  have e : (AddMonoidAlgebra.mapRingHom P g₁).comp (AddMonoidAlgebra.mapRingHom P g₂) =
      AddMonoidAlgebra.mapRingHom P g₃ := by
    refine RingHom.ext fun w => ?_
    ext m
    simp [AddMonoidAlgebra.coeff_mapRingHom, h]
  rw [← sp_comp, e]

lemma muM_comp {T₀ T₁ T : Over S} [IsAffine T₀.left] [IsAffine T₁.left] [IsAffine T.left]
    (j₀ : T₀ ⟶ T₁) (j₁ : T₁ ⟶ T) (j₂ : T₀ ⟶ T) (h : j₀ ≫ j₁ = j₂) :
    muM N j₀ ≫ muM N j₁ = muM N j₂ := by
  have hl : j₂.left = j₀.left ≫ j₁.left := (congrArg (fun k => k.left) h).symm
  have hr : ∀ r, j₀.left.appTop.hom (j₁.left.appTop.hom r) = j₂.left.appTop.hom r := fun r => by
    rw [hl, Scheme.Hom.comp_appTop]
    rfl
  exact Over.OverMorphism.ext (sp_map_comp _ _ _ hr)

section Coact

variable (T : Over S) [IsAffine T.left]

/-- The structure of `𝔸(N)_T × D(M)` over `S`. -/
noncomputable abbrev s₂T : Spec (CommRingCat.of (AddMonoidAlgebra (RR N T) M)) ⟶ S :=
  sp (cst (RR N T) M) ≫ magnetπ N T.left ≫ T.hom

/-- The action morphism. -/
noncomputable def rrT : Ov (s₂T (M := M) N T) ⟶ Ov (magnetπ N T.left ≫ T.hom) :=
  ovHom (coactN (M := M) N Γ(T.left, ⊤)) (hρs N T _ rfl)

/-- The projection. -/
noncomputable def ccT : Ov (s₂T (M := M) N T) ⟶ Ov (magnetπ N T.left ≫ T.hom) :=
  ovHom (cst (RR N T) M) rfl

/-- The universal point of `D(M)`. -/
noncomputable def eT : APt (overO S) M (op (Ov (s₂T (M := M) N T))) := eOf _ (eU (RR N T) M)

variable {T}
variable {T₀ : Over S} [IsAffine T₀.left] (j : T₀ ⟶ T)

/-- Base change of `𝔸(N)_T × D(M)`. -/
noncomputable def piM : Ov (s₂T (M := M) N T₀) ⟶ Ov (s₂T (M := M) N T) :=
  ovHom (AddMonoidAlgebra.mapRingHom M (AddMonoidAlgebra.mapRingHom N j.left.appTop.hom)) 
    ((tri (sp_sq (g₃ := AddMonoidAlgebra.mapRingHom N j.left.appTop.hom) (g₄ := cst (RR N T₀) M)
      (RingHom.ext fun w => map_cst _ w)) _).trans
        (congrArg (fun z => sp (cst (RR N T₀) M) ≫ z) (π_thick N j).symm))

lemma piM_rr : piM (M := M) N j ≫ rrT N T = rrT N T₀ ≫ muM N j :=
  Over.OverMorphism.ext (sp_sq (RingHom.ext fun w => coactN_map N _ w))

lemma piM_cc : piM (M := M) N j ≫ ccT N T = ccT N T₀ ≫ muM N j :=
  Over.OverMorphism.ext (sp_sq (RingHom.ext fun w => map_cst _ w))

lemma res_piM : APt.res (piM (M := M) N j).op (eT N T) = eT N T₀ :=
  (res_eOf _ _ _).trans (eOf_congr _ (hof _))

variable {X : Over S} {aX : AAction (overO S) M (yoneda.obj X)}

lemma vv_equiv (y : AttractorPt aX N T) : rrT N T ≫ vv N y = sm aX (eT N T) (ccT N T ≫ vv N y) :=
  equiv_of_attPt N _ rfl y _ rfl (hρs N T _ rfl)

/-- The two sides of equivariance pull back. -/
lemma equiv_pull (x : Ov (magnetπ N T.left ≫ T.hom) ⟶ X) :
    piM (M := M) N j ≫ rrT N T ≫ x = rrT N T₀ ≫ muM N j ≫ x ∧
      piM (M := M) N j ≫ sm aX (eT N T) (ccT N T ≫ x) = sm aX (eT N T₀) (ccT N T₀ ≫ muM N j ≫ x) := by
  refine ⟨tri (piM_rr N j) x, ?_⟩
  refine (comp_sm aX _ _ _).trans ?_
  rw [res_piM]
  exact congrArg _ (tri (piM_cc N j) x)

end Coact

set_option maxHeartbeats 3000000 in
/-- **Fact 3.19**, schemes only: if `g : X → Y` is equivariant and locally of finite presentation
and `X^N`, `Y^N` are representable by the schemes `Zx`, `Zy`, then `Zx → Zy` is locally of finite
presentation. `M` is any commutative group and `N` any magnet. -/
theorem locallyOfFinitePresentation_repMap {X Y Zx Zy : Over S}
    {aX : AAction (overO S) M (yoneda.obj X)} {aY : AAction (overO S) M (yoneda.obj Y)}
    (g : X ⟶ Y) (hg : ∀ {T : Over S} (h : APt (overO S) M (op T)) (x : T ⟶ X),
      sm aX h x ≫ g = sm aY h (x ≫ g)) [LocallyOfFinitePresentation g.left]
    (rx : RepresentsAttractor aX N (yoneda.obj Zx)) (ry : RepresentsAttractor aY N (yoneda.obj Zy))
    (z : Zx ⟶ Zy) (hz : ∀ (T : Over S) (w : T ⟶ Zx),
      ry.equiv T (w ≫ z) = AttractorPt.push (eqHom g hg) (rx.equiv T w)) :
    LocallyOfFinitePresentation z.left := by
  refine locallyOfFinitePresentation_of_affineLimit_surjective z.left ?_
  intro I _ _ D c hc hD g₀
  classical
  let D₁ : I ⥤ Scheme.{u} := D ⋙ Over.forget _
  have hc₁ : IsLimit ((Over.forget _).mapCone c) := isLimitOfPreserves _ hc
  have hDa : ∀ i, IsAffine (D₁.obj i) := hD
  have hinf : IsAffine c.pt.left := Scheme.isAffine_of_isLimit _ hc₁
  have hinf₁ : IsAffine ((Over.forget _).mapCone c).pt := hinf
  let Tm : Over Zy.left ⥤ Over S := Over.map Zy.hom
  let Ti : I → Over S := fun i => Tm.obj (D.obj i)
  let Tinf : Over S := Tm.obj c.pt
  have hTa : ∀ i, IsAffine (Ti i).left := hD
  have hTinf : IsAffine Tinf.left := hinf
  let pr : ∀ i, Tinf ⟶ Ti i := fun i => Tm.map (c.π.app i)
  let tr : ∀ {i j : I}, (i ⟶ j) → (Ti i ⟶ Ti j) := fun f => Tm.map (D.map f)
  let ψ : ∀ i, AttractorPt aY N (Ti i) := fun i => ry.equiv (Ti i) (Over.homMk (D.obj i).hom rfl)
  have hψ : ∀ {i j : I} (f : i ⟶ j), (ψ j).baseChange (tr f) = ψ i := by
    intro i j f
    refine (ry.naturality (tr f) _).symm.trans (congrArg _ ?_)
    exact Over.OverMorphism.ext (Over.w (D.map f))
  let val : ∀ i, Ov (magnetπ N (Ti i).left ≫ (Ti i).hom) ⟶ Y := fun i => vv N (ψ i)
  have hval : ∀ {i j : I} (f : i ⟶ j), muM N (tr f) ≫ val j = val i := fun {i j} f =>
    (val_base N (tr f) (ψ j)).trans (congrArg (vv N) (hψ f))
  let g₀' : Tinf ⟶ Zx := Over.homMk g₀.left (by
    change g₀.left ≫ Zx.hom = c.pt.hom ≫ Zy.hom
    rw [← Over.w z, ← Category.assoc]
    exact congrArg (· ≫ Zy.hom) (Over.w g₀))
  let φinf : AttractorPt aX N Tinf := rx.equiv Tinf g₀'
  let vX := vv N φinf
  have hprV : ∀ i, muM N (pr i) ≫ val i = vX ≫ g := by
    intro i
    refine (val_base N (pr i) (ψ i)).trans ?_
    have e₁ : (ψ i).baseChange (pr i) = ry.equiv Tinf (g₀' ≫ z) := by
      refine (ry.naturality (pr i) _).symm.trans (congrArg _ ?_)
      refine Over.OverMorphism.ext ?_
      exact (Over.w (c.π.app i)).trans (Over.w g₀).symm
    rw [e₁, hz]
    rfl
  let G₀ : I ⥤ CommRingCat.{u}ᵒᵖ := D₁ ⋙ Scheme.Γ.rightOp
  have l₀ := isLimitBase D₁ _ hc₁
  have lN := isLimitMon (P := N) _ _ _ _ l₀
  have lM := isLimitMon (P := M) _ _ _ _ lN
  let tN : (G₀ ⋙ (monFun N).op) ⋙ Scheme.Spec ⟶ (Functor.const I).obj Y.left :=
    { app := fun i => (val i).left
      naturality := fun {i j} f => by
        refine Eq.trans (congrArg (fun k => k.left) (hval f)) (Category.comp_id _).symm }
  have hsN : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (((G₀ ⋙ (monFun N).op) ⋙ Scheme.Spec).map f) := fun f => by
    change IsAffineHom (Spec.map _)
    infer_instance
  have hcN : ∀ i, CompactSpace (((G₀ ⋙ (monFun N).op) ⋙ Scheme.Spec).obj i) := fun i => by
    change CompactSpace (Spec _)
    infer_instance
  have hqN : ∀ i, QuasiSeparatedSpace (((G₀ ⋙ (monFun N).op) ⋙ Scheme.Spec).obj i) := fun i => by
    change QuasiSeparatedSpace (Spec _)
    infer_instance
  obtain ⟨i, x, hx₁, hx₂⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    ((G₀ ⋙ (monFun N).op) ⋙ Scheme.Spec) tN g.left _ lN vX.left (by
      ext i
      exact (congrArg (fun k => k.left) (hprV i)).trans (Category.id_comp _).symm)
  let xO : Ov (magnetπ N (Ti i).left ≫ (Ti i).hom) ⟶ X := Over.homMk x (by
    exact (congrArg (x ≫ ·) (Over.w g).symm).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ Y.hom) hx₂).trans (Over.w (val i)))))
  have hxg : xO ≫ g = val i := Over.OverMorphism.ext hx₂
  have hxV : muM N (pr i) ≫ xO = vX := Over.OverMorphism.ext hx₁
  -- equivariance descends
  let tM : ((G₀ ⋙ (monFun N).op) ⋙ (monFun M).op) ⋙ Scheme.Spec ⟶ (Functor.const I).obj Y.left :=
    { app := fun j => (rrT (M := M) N (Ti j) ≫ val j).left
      naturality := fun {j l} f => by
        refine Eq.trans ?_ (Category.comp_id _).symm
        have e₁ := (equiv_pull (M := M) (aX := aY) N (tr f) (val l)).1
        exact congrArg (fun k => k.left) (e₁.trans (congrArg (fun z => rrT N (Ti j) ≫ z) (hval f))) }
  have hLg : (rrT (M := M) N (Ti i) ≫ xO) ≫ g = rrT N (Ti i) ≫ val i :=
    (Category.assoc _ _ _).trans (congrArg (fun z => rrT N (Ti i) ≫ z) hxg)
  have hRg : sm aX (eT N (Ti i)) (ccT (M := M) N (Ti i) ≫ xO) ≫ g = rrT N (Ti i) ≫ val i := by
    refine (hg _ _).trans ?_
    refine (congrArg (sm aY (eT N (Ti i))) ((Category.assoc _ _ _).trans
      (congrArg (fun z => ccT N (Ti i) ≫ z) hxg))).trans (vv_equiv N (ψ i)).symm
  have habO : piM (M := M) N (pr i) ≫ rrT N (Ti i) ≫ xO =
      piM (M := M) N (pr i) ≫ sm aX (eT N (Ti i)) (ccT N (Ti i) ≫ xO) := by
    obtain ⟨a₁, a₂⟩ := equiv_pull (M := M) (aX := aX) N (pr i) xO
    rw [a₁, a₂, hxV]
    exact vv_equiv N φinf
  have hsM : ∀ {i j : I} (f : i ⟶ j), IsAffineHom ((((G₀ ⋙ (monFun N).op) ⋙ (monFun M).op) ⋙ Scheme.Spec).map f) := fun f => by
    change IsAffineHom (Spec.map _)
    infer_instance
  have hcM : ∀ i, CompactSpace (((((G₀ ⋙ (monFun N).op) ⋙ (monFun M).op) ⋙ Scheme.Spec)).obj i) := fun i => by
    change CompactSpace (Spec _)
    infer_instance
  obtain ⟨k, hik, hk⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    (((G₀ ⋙ (monFun N).op) ⋙ (monFun M).op) ⋙ Scheme.Spec) tM g.left _ lM (i := i)
    (rrT (M := M) N (Ti i) ≫ xO).left (sm aX (eT N (Ti i)) (ccT N (Ti i) ≫ xO)).left
    (congrArg (fun k => k.left) hLg).symm (congrArg (fun k => k.left) hRg).symm
    (congrArg (fun k => k.left) habO)
  have hkO : piM (M := M) N (tr hik) ≫ rrT N (Ti i) ≫ xO =
      piM (M := M) N (tr hik) ≫ sm aX (eT N (Ti i)) (ccT N (Ti i) ≫ xO) := Over.OverMorphism.ext hk
  let xk := muM N (tr hik) ≫ xO
  have heq : rrT (M := M) N (Ti k) ≫ xk = sm aX (eT N (Ti k)) (ccT N (Ti k) ≫ xk) := by
    obtain ⟨a₁, a₂⟩ := equiv_pull (M := M) (aX := aX) N (tr hik) xO
    exact a₁.symm.trans (hkO.trans a₂)
  let φk : AttractorPt aX N (Ti k) := attPtOf N _ rfl xk (hρs N (Ti k) _ rfl) heq
  have a1 : vv N φk = xk := attPtOf_app N _ rfl xk (hρs N (Ti k) _ rfl) heq
  have hxkg : xk ≫ g = val k :=
    (Category.assoc _ _ _).trans ((congrArg (fun z => muM N (tr hik) ≫ z) hxg).trans (hval hik))
  let w : Ti k ⟶ Zx := (rx.equiv (Ti k)).symm φk
  have hwe : rx.equiv (Ti k) w = φk := Equiv.apply_symm_apply _ _
  have hzk : w ≫ z = Over.homMk (D.obj k).hom rfl := by
    refine (ry.equiv (Ti k)).injective ?_
    rw [hz, hwe]
    refine (attractorPtEquivOfUniversal (act := aY) (specUP N (Ti k) _ rfl)).injective (Subtype.ext ?_)
    exact (congrArg (· ≫ g) a1).trans hxkg
  refine ⟨k, Over.homMk w.left (congrArg (fun z => z.left) hzk), Over.OverMorphism.ext ?_⟩
  have hfin : pr k ≫ w = g₀' := by
    refine (rx.equiv Tinf).injective ?_
    refine (rx.naturality (pr k) w).trans ?_
    rw [hwe]
    refine (attractorPtEquivOfUniversal (act := aX) (specUP N Tinf _ rfl)).injective (Subtype.ext ?_)
    refine (val_base N (pr k) φk).symm.trans ?_
    refine (congrArg (fun z => muM N (pr k) ≫ z) a1).trans ?_
    refine Eq.trans ?_ hxV
    have sq : muM N (pr k) ≫ muM N (tr hik) = muM N (pr i) :=
      muM_comp N (pr k) (tr hik) (pr i) ((Tm.map_comp _ _).symm.trans (congrArg Tm.map (c.w hik)))
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ xO) sq)
  exact congrArg (fun z => z.left) hfin

end AlgMag.SmoothSchemes
