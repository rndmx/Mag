/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec11SpacesLimit

/-!
# Fact 3.19 for algebraic spaces

Mayeux, *Algebraic Magnetism*, Fact 3.19: if `f : X → Y` is equivariant and locally of finite
presentation, and `X^N`, `Y^N` are representable by algebraic spaces, then `f^N` is locally of finite
presentation. This uses Stacks 049J for `f` on `𝔸(N)_T` and on `𝔸(N)_T × D(M)`, and Stacks 0CM6
for `f^N`. `#M` is below the cutoff of the site.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.SpacesLift

open AlgMag.GB AlgMag.Lifts AlgMag.SmoothSchemes

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommMonoid M] [SM B M] (N : AddSubmonoid M)

instance srSec (T : BigFppfOver B S hS) [IsAffine (τS T)] : SR B Γ(τS T, ⊤) := sr_sections T

/-- The structure morphism of `𝔸(N)_T`. -/
noncomputable abbrev tN (T : BigFppfOver B S hS) [IsAffine (τS T)] :
    Spec (CommRingCat.of (RS N (τS T))) ⟶ S := magnetπ N (τS T) ≫ T.hom.hom

/-- `𝔸(N)_T` in the site. -/
noncomputable abbrev PO (T : BigFppfOver B S hS) [IsAffine (τS T)] : BigFppfOver B S hS :=
  Sv B hS (tN N T)

/-- The structure morphism of `𝔸(N)_T × D(M)`. -/
noncomputable abbrev t2 (T : BigFppfOver B S hS) [IsAffine (τS T)] :
    Spec (CommRingCat.of (AddMonoidAlgebra (RS N (τS T)) M)) ⟶ S := sp (cst (RS N (τS T)) M) ≫ tN N T

/-- `𝔸(N)_T × D(M)` in the site. -/
noncomputable abbrev PO2 (T : BigFppfOver B S hS) [IsAffine (τS T)] : BigFppfOver B S hS :=
  Sv B hS (t2 (M := M) N T)

/-- The value of an attractor point at the universal point. -/
noncomputable def vvS {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {aX : AAction (fppfO B S hS) M X}
    {T : BigFppfOver B S hS} [IsAffine (τS T)] (y : AttractorPt aX N T) : X.obj (op (PO N T)) :=
  y.app (specU N T _ rfl).π (specU N T _ rfl).u

section Mu

variable {T₀ T T₁ : BigFppfOver B S hS} [IsAffine (τS T₀)] [IsAffine (τS T)] [IsAffine (τS T₁)]

lemma tN_thick (j : T₀ ⟶ T) : sp (AddMonoidAlgebra.mapRingHom N
    ((BigFppfOver.toScheme B S hS).map j).appTop.hom) ≫ tN N T = tN N T₀ := by
  have hw : (BigFppfOver.toScheme B S hS).map j ≫ T.hom.hom = T₀.hom.hom :=
    congrArg (fun k => k.hom) (Over.w j)
  change _ ≫ magnetπ N (τS T) ≫ T.hom.hom = magnetπ N (τS T₀) ≫ T₀.hom.hom
  rw [← hw, ← Category.assoc, ← Category.assoc, piSq N ((BigFppfOver.toScheme B S hS).map j)]

/-- The morphism `𝔸(N)_{T₀} → 𝔸(N)_T`. -/
noncomputable def muS (j : T₀ ⟶ T) : PO N T₀ ⟶ PO N T :=
  svHom B hS (AddMonoidAlgebra.mapRingHom N ((BigFppfOver.toScheme B S hS).map j).appTop.hom)
    (tN_thick N j)

lemma muS_comp (j₀ : T₁ ⟶ T₀) (j₁ : T₀ ⟶ T) (j₂ : T₁ ⟶ T) (h : j₀ ≫ j₁ = j₂) :
    muS N j₀ ≫ muS N j₁ = muS N j₂ := by
  subst h
  refine site_ext (sp_map_comp _ _ _ fun r => ?_)
  rw [Functor.map_comp, Scheme.Hom.comp_appTop]
  rfl

lemma muS_id : muS N (𝟙 T) = 𝟙 _ := by
  refine site_ext ?_
  change sp _ = 𝟙 _
  have e : AddMonoidAlgebra.mapRingHom N ((BigFppfOver.toScheme B S hS).map (𝟙 T)).appTop.hom =
      RingHom.id _ := by
    refine RingHom.ext fun w => ?_
    ext m
    simp [AddMonoidAlgebra.coeff_mapRingHom]
  rw [e, sp_id']

lemma vvS_base {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {aX : AAction (fppfO B S hS) M X}
    (j : T₀ ⟶ T) (y : AttractorPt aX N T) : pb X (muS N j) (vvS N y) = vvS N (y.baseChange j) := by
  let U := specU N T _ rfl
  let U₀ := specU N T₀ _ rfl
  have hj : U.lift (U₀.π ≫ j) U₀.u = muS N j := by
    symm
    refine U.uniq _ _ _ (site_ext (piSq N ((BigFppfOver.toScheme B S hS).map j)).symm)
      (MonoidHom.ext fun n => ?_)
    refine (sp_inv _ _).trans (congrArg _ ?_)
    refine (AddMonoidAlgebra.mapRingHom_single _ _ _).trans ?_
    rw [map_one]
  have := y.app_eq_of_universal U (U₀.π ≫ j) U₀.u
  exact (congrArg (fun z : _ ⟶ U.P => pb X z (y.app U.π U.u)) hj).symm.trans this.symm

lemma t2_thick (j : T₀ ⟶ T) : sp (AddMonoidAlgebra.mapRingHom M (AddMonoidAlgebra.mapRingHom N
    ((BigFppfOver.toScheme B S hS).map j).appTop.hom)) ≫ t2 (M := M) N T = t2 (M := M) N T₀ :=
  (tri (sp_sq (g₃ := AddMonoidAlgebra.mapRingHom N ((BigFppfOver.toScheme B S hS).map j).appTop.hom)
    (g₄ := cst (RS N (τS T₀)) M) (RingHom.ext fun w => map_cst _ w)) _).trans
      (congrArg (fun z => sp (cst (RS N (τS T₀)) M) ≫ z) (tN_thick N j))

/-- The morphism `𝔸(N)_{T₀} × D(M) → 𝔸(N)_T × D(M)`. -/
noncomputable def piS (j : T₀ ⟶ T) : PO2 (M := M) N T₀ ⟶ PO2 (M := M) N T :=
  svHom B hS _ (t2_thick N j)

lemma piS_comp (j₀ : T₁ ⟶ T₀) (j₁ : T₀ ⟶ T) (j₂ : T₁ ⟶ T) (h : j₀ ≫ j₁ = j₂) :
    piS (M := M) N j₀ ≫ piS (M := M) N j₁ = piS N j₂ := by
  subst h
  refine site_ext (sp_map_comp _ _ _ fun w => ?_)
  rw [Functor.map_comp, Scheme.Hom.comp_appTop]
  ext m
  simp [AddMonoidAlgebra.coeff_mapRingHom]

lemma piS_id : piS (M := M) N (𝟙 T) = 𝟙 _ := by
  refine site_ext ?_
  change sp _ = 𝟙 _
  have e : AddMonoidAlgebra.mapRingHom M (AddMonoidAlgebra.mapRingHom N
      ((BigFppfOver.toScheme B S hS).map (𝟙 T)).appTop.hom) = RingHom.id _ := by
    refine RingHom.ext fun w => ?_
    ext m n
    simp [AddMonoidAlgebra.coeff_mapRingHom]
  rw [e, sp_id']

variable (T) in
/-- The action morphism. -/
noncomputable def rrS : PO2 (M := M) N T ⟶ PO N T :=
  svHom B hS (coactN (M := M) N Γ(τS T, ⊤)) (rhoS N _ rfl)

variable (T) in
/-- The projection. -/
noncomputable def ccS : PO2 (M := M) N T ⟶ PO N T := svHom B hS (cst (RS N (τS T)) M) rfl

variable (T) in
/-- The universal point of `D(M)`. -/
noncomputable def eTS : APt (fppfO B S hS) M (op (PO2 (M := M) N T)) :=
  eS B hS _ (eU (RS N (τS T)) M)

lemma piS_rr (j : T₀ ⟶ T) : piS (M := M) N j ≫ rrS N T = rrS N T₀ ≫ muS N j :=
  site_ext (sp_sq (RingHom.ext fun w => coactN_map N _ w))

lemma piS_cc (j : T₀ ⟶ T) : piS (M := M) N j ≫ ccS N T = ccS N T₀ ≫ muS N j :=
  site_ext (sp_sq (RingHom.ext fun w => map_cst _ w))

lemma res_piS (j : T₀ ⟶ T) : APt.res (piS (M := M) N j).op (eTS N T) = eTS N T₀ :=
  (res_eS _ _ _).trans (eS_congr _ (hof _))

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {aX : AAction (fppfO B S hS) M X}

lemma vvS_equiv (y : AttractorPt aX N T) :
    pb X (rrS N T) (vvS N y) = ss aX (eTS N T) (pb X (ccS N T) (vvS N y)) :=
  equiv_of_attPtS N _ rfl y _ rfl (rhoS N _ rfl)

lemma equiv_pullS (j : T₀ ⟶ T) (x : X.obj (op (PO N T))) :
    pb X (piS (M := M) N j) (pb X (rrS N T) x) = pb X (rrS N T₀) (pb X (muS N j) x) ∧
      pb X (piS (M := M) N j) (ss aX (eTS N T) (pb X (ccS N T) x)) =
        ss aX (eTS N T₀) (pb X (ccS N T₀) (pb X (muS N j) x)) := by
  refine ⟨pb_sq X (piS_rr N j) x, ?_⟩
  rw [pb_ss, res_piS, pb_sq X (piS_cc N j) x]

end Mu

section Lim

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ BigFppfOver B S hS) (c : Cone D)
  [∀ i, IsAffine (τS (D.obj i))] [IsAffine (τS c.pt)]

/-- The projection `𝔸(N)_{c} → 𝔸(N)_{D i}`. -/
noncomputable abbrev muC (i : I) : PO N c.pt ⟶ PO N (D.obj i) :=
  muS (T₀ := c.pt) (T := D.obj i) N (c.π.app i)

/-- The projection `𝔸(N)_{c} × D(M) → 𝔸(N)_{D i} × D(M)`. -/
noncomputable abbrev piC (i : I) : PO2 (M := M) N c.pt ⟶ PO2 (M := M) N (D.obj i) :=
  piS (T₀ := c.pt) (T := D.obj i) N (c.π.app i)

/-- The system `𝔸(N)_{D i}`. -/
noncomputable def DN : I ⥤ BigFppfOver B S hS where
  obj i := PO N (D.obj i)
  map u := muS N (D.map u)
  map_id i := by rw [D.map_id]; exact muS_id N
  map_comp u v := (muS_comp N (D.map u) (D.map v) _ (D.map_comp u v).symm).symm

/-- The cone `𝔸(N)_{c}`. -/
noncomputable def cN : Cone (DN N D) where
  pt := PO N c.pt
  π :=
    { app := fun i => muC N D c i
      naturality := fun {i j} u => by
        change 𝟙 _ ≫ muC N D c j = muC N D c i ≫ muS N (D.map u)
        rw [Category.id_comp]
        exact (muS_comp (T₁ := c.pt) N _ _ _ (c.w u)).symm }

/-- The system `𝔸(N)_{D i} × D(M)`. -/
noncomputable def DM : I ⥤ BigFppfOver B S hS where
  obj i := PO2 (M := M) N (D.obj i)
  map u := piS N (D.map u)
  map_id i := by rw [D.map_id]; exact piS_id N
  map_comp u v := (piS_comp N (D.map u) (D.map v) _ (D.map_comp u v).symm).symm

/-- The cone `𝔸(N)_{c} × D(M)`. -/
noncomputable def cM : Cone (DM (M := M) N D) where
  pt := PO2 (M := M) N c.pt
  π :=
    { app := fun i => piC (M := M) N D c i
      naturality := fun {i j} u => by
        change 𝟙 _ ≫ piC (M := M) N D c j = piC N D c i ≫ piS N (D.map u)
        rw [Category.id_comp]
        exact (piS_comp (T₁ := c.pt) N _ _ _ (c.w u)).symm }

variable (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))

include hc in
set_option maxHeartbeats 4000000 in
lemma isLimit_cN : Nonempty (IsLimit ((BigFppfOver.toScheme B S hS).mapCone (cN N D c))) := by
  haveI : ∀ i, IsAffine ((D ⋙ BigFppfOver.toScheme B S hS).obj i) := fun i =>
    inferInstanceAs (IsAffine (τS (D.obj i)))
  haveI : IsAffine ((BigFppfOver.toScheme B S hS).mapCone c).pt :=
    inferInstanceAs (IsAffine (τS c.pt))
  exact ⟨isLimitMon (P := N) _ _ _ _ (isLimitBase (D ⋙ BigFppfOver.toScheme B S hS) _ hc)⟩

include hc in
set_option maxHeartbeats 4000000 in
lemma isLimit_cM : Nonempty (IsLimit ((BigFppfOver.toScheme B S hS).mapCone (cM (M := M) N D c))) := by
  haveI : ∀ i, IsAffine ((D ⋙ BigFppfOver.toScheme B S hS).obj i) := fun i =>
    inferInstanceAs (IsAffine (τS (D.obj i)))
  haveI : IsAffine ((BigFppfOver.toScheme B S hS).mapCone c).pt :=
    inferInstanceAs (IsAffine (τS c.pt))
  exact ⟨isLimitMon (P := M) _ _ _ _ (isLimitMon (P := N) _ _ _ _
    (isLimitBase (D ⋙ BigFppfOver.toScheme B S hS) _ hc))⟩

end Lim

variable {X Y Zx Zy : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {aX : AAction (fppfO B S hS) M X}
  {aY : AAction (fppfO B S hS) M Y}

/-- **Fact 3.19** for algebraic spaces: if `f` is equivariant and locally of finite presentation
and `X^N`, `Y^N` are representable by algebraic spaces, then `f^N` is locally of finite
presentation. Here `#M` is below the cutoff of the site. -/
theorem isLocallyOfFinitePresentation_repMap_spaces (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hZx : IsAlgebraicSpace B S hS Zx)
    (hZy : IsAlgebraicSpace B S hS Zy) (f : EquivariantHom aX aY)
    (hf : Space.IsLocallyOfFinitePresentation B S hS f.hom)
    (rx : RepresentsAttractor aX N Zx) (ry : RepresentsAttractor aY N Zy) (z : Zx ⟶ Zy)
    (hz : ∀ T w, ry.equiv T (z.app (op T) w) = AttractorPt.push f (rx.equiv T w)) :
    Space.IsLocallyOfFinitePresentation B S hS z := by
  have hrlp := relativelyLimitPreserving_of_isLocallyOfFinitePresentation B S hS hX hY hf
  refine Space.isLocallyOfFinitePresentation_of_affineLimit_surjective B S hS hZx hZy z ?_
  intro I _ _ D c hc hA hAp x y hxy
  haveI : ∀ i, IsAffine (τS (D.obj i)) := hA
  haveI : IsAffine (τS c.pt) := hAp
  obtain ⟨i₀', y₀, hy₀⟩ := Types.jointly_surjective_of_isColimit (colimit.isColimit (D.op ⋙ Zy)) y
  obtain ⟨i₀⟩ := i₀'
  subst hy₀
  have hxy' : z.app _ x = Zy.map (c.π.app i₀).op y₀ :=
    hxy.trans (ConcreteCategory.congr_hom (colimit.ι_desc (Zy.mapCocone c.op) (op i₀)) y₀)
  obtain ⟨lN⟩ := isLimit_cN N D c hc
  obtain ⟨lM⟩ := isLimit_cM (M := M) N D c hc
  obtain ⟨sq₁, -⟩ := limit_square hrlp lN (fun i => inferInstanceAs (IsAffine (Spec _)))
    (inferInstanceAs (IsAffine (Spec _)))
  obtain ⟨-, sq₂⟩ := limit_square hrlp lM (fun i => inferInstanceAs (IsAffine (Spec _)))
    (inferInstanceAs (IsAffine (Spec _)))
  let ψ := ry.equiv _ y₀
  let φ := rx.equiv c.pt x
  have nat : ∀ {T T₁ : BigFppfOver B S hS} (u : T₁ ⟶ T) (w : X.obj (op T)),
      f.hom.app _ (pb X u w) = pb Y u (f.hom.app _ w) := fun u w =>
    NatTrans.naturality_apply f.hom u.op w
  have vv_push : ∀ {T : BigFppfOver B S hS} [IsAffine (τS T)] (ξ : AttractorPt aX N T),
      vvS N (AttractorPt.push f ξ) = f.hom.app _ (vvS N ξ) := fun _ => rfl
  have vv_inj : ∀ {T : BigFppfOver B S hS} [IsAffine (τS T)] {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
      {a : AAction (fppfO B S hS) M F} (ξ ξ' : AttractorPt a N T), vvS N ξ = vvS N ξ' → ξ = ξ' :=
    fun _ _ h => (attractorPtEquivOfUniversal (specU N _ _ rfl)).injective (Subtype.ext h)
  have hcond : f.hom.app _ (vvS N φ) = pb Y (muC N D c i₀) (vvS N ψ) := by
    rw [← vv_push, vvS_base, ← hz]
    refine congrArg (vvS N) ?_
    rw [hxy']
    exact ry.naturality _ _
  obtain ⟨j, u, xj, hx₁, hx₂⟩ := sq₁ (vvS N φ) i₀ (vvS N ψ) hcond
  have hx₁' : pb X (muC N D c j) xj = vvS N φ := hx₁
  have hx₂' : f.hom.app (op (PO N (D.obj j))) xj = pb Y (muS N (D.map u)) (vvS N ψ) := hx₂
  obtain ⟨k, v, hk⟩ := sq₂ j (pb X (rrS N (D.obj j)) xj)
    (ss aX (eTS N (D.obj j)) (pb X (ccS N (D.obj j)) xj)) (by
      have e₁ : f.hom.app (op (PO2 (M := M) N (D.obj j))) (pb X (rrS N (D.obj j)) xj) =
          pb Y (rrS N (D.obj j)) (pb Y (muS N (D.map u)) (vvS N ψ)) :=
        (nat _ _).trans (congrArg _ hx₂')
      have e₂ : f.hom.app (op (PO2 (M := M) N (D.obj j)))
          (ss aX (eTS N (D.obj j)) (pb X (ccS N (D.obj j)) xj)) =
          ss aY (eTS N (D.obj j)) (pb Y (ccS N (D.obj j)) (pb Y (muS N (D.map u)) (vvS N ψ))) :=
        (f.map_smul _ _).trans (congrArg _ ((nat _ _).trans (congrArg _ hx₂')))
      have e₃ := vvS_equiv (M := M) N (ψ.baseChange (D.map u))
      rw [← vvS_base] at e₃
      exact e₁.trans (e₃.trans e₂.symm)) (by
      have h := equiv_pullS (M := M) (aX := aX) (T₀ := c.pt) (T := D.obj j) N (c.π.app j) xj
      refine h.1.trans (Eq.trans ?_ h.2.symm)
      rw [hx₁']
      exact vvS_equiv N φ)
  let xk := pb X (muS N (D.map v)) xj
  have heq : pb X (rrS N (D.obj k)) xk = ss aX (eTS N (D.obj k)) (pb X (ccS N (D.obj k)) xk) := by
    have h := equiv_pullS (M := M) (aX := aX) N (D.map v) xj
    exact h.1.symm.trans (Eq.trans hk h.2)
  let φk : AttractorPt aX N (D.obj k) := attPtOfS N _ rfl xk (rhoS N _ rfl) heq
  have a1 : vvS N φk = xk := attPtOfS_app N _ rfl xk (rhoS N _ rfl) heq
  have hxkf : f.hom.app _ xk = pb Y (muS N (D.map (v ≫ u))) (vvS N ψ) := by
    refine (nat (muS N (D.map v)) xj).trans ?_
    rw [hx₂', ← pb_comp, muS_comp N (D.map v) (D.map u) _ (D.map_comp v u).symm]
  let w : Zx.obj (op (D.obj k)) := (rx.equiv _).symm φk
  have hwe : rx.equiv _ w = φk := Equiv.apply_symm_apply _ _
  refine ⟨colimit.ι (D.op ⋙ Zx) (op k) w, ?_, ?_⟩
  · refine (ConcreteCategory.congr_hom (colimit.ι_desc (Zx.mapCocone c.op) (op k)) w).trans ?_
    refine (rx.equiv _).injective ?_
    refine (rx.naturality _ _).trans ?_
    rw [hwe]
    refine vv_inj _ _ ?_
    rw [← vvS_base, a1]
    exact (pb_comp X (muS (T₀ := c.pt) (T := D.obj k) N (c.π.app k)) (muS N (D.map v)) xj).symm.trans
      ((congrArg (fun m => pb X m xj)
        (muS_comp (T₁ := c.pt) N (c.π.app k) (D.map v) (c.π.app j) (c.w v))).trans hx₁')
  · refine (ConcreteCategory.congr_hom (ι_colimMap (Functor.whiskerLeft D.op z) (op k)) w).trans ?_
    have hzw : z.app _ w = Zy.map (D.map (v ≫ u)).op y₀ := by
      refine (ry.equiv _).injective ?_
      rw [hz, hwe]
      refine Eq.trans ?_ (ry.naturality _ _).symm
      refine vv_inj _ _ ?_
      rw [vv_push, ← vvS_base, a1]
      exact hxkf
    refine (congrArg _ hzw).trans ?_
    exact ConcreteCategory.congr_hom (colimit.w (D.op ⋙ Zy) (v ≫ u).op) y₀

end AlgMag.SpacesLift
