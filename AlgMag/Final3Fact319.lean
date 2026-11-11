/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec11SpacesFact

/-!
# Fact 3.19, functor form

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026), Fact 3.19. "Locally of finite
presentation" for `f^N : X^N → Y^N` is Stacks 049J (limit preserving transformation). This file
proves the converse of `limit_square`: the two halves of Tag 049J on every cofiltered limit of
affine objects give a limit preserving transformation (`rlp_of_squares`), and applies it to
`attractorMap f N` without representability of `X^N`, `Y^N` (`fact319_relativelyLimitPreserving`).
As printed, `M` is any commutative monoid; `#M` is below the cutoff of the site (`SM B M`).
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

namespace AlgMag.Final3Fact319

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Converse of `limit_square` (Stacks 049J / 06BC): the surjectivity and injectivity halves on
every cofiltered limit of affine objects make `f` limit preserving. -/
lemma rlp_of_squares {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v} (f : X ⟶ Y)
    (H : ∀ (I : Type u) [Category.{u} I] [IsCofiltered I] (D : I ⥤ BigFppfOver B S hS) (c : Cone D),
      IsLimit ((BigFppfOver.toScheme B S hS).mapCone c) →
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj i))) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt) →
      (∀ (x : X.obj (op c.pt)) (i : I) (y : Y.obj (op (D.obj i))),
        f.app _ x = Y.map (c.π.app i).op y → ∃ (j : I) (u : j ⟶ i) (xj : X.obj (op (D.obj j))),
          X.map (c.π.app j).op xj = x ∧ f.app _ xj = Y.map (D.map u).op y) ∧
      (∀ (i : I) (a b : X.obj (op (D.obj i))), f.app _ a = f.app _ b →
        X.map (c.π.app i).op a = X.map (c.π.app i).op b →
        ∃ (j : I) (u : j ⟶ i), X.map (D.map u).op a = X.map (D.map u).op b)) :
    RelativelyLimitPreserving.{u, v, u, u} B S hS f := by
  refine (relativelyLimitPreserving_iff_affineLimit_isPullback.{u, v, u, u} B S hS f).mpr ?_
  intro I _ _ D c hc hA hp
  obtain ⟨hsur, hinj⟩ := H I D c hc hA hp
  have desc_ι : ∀ {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v} (j : Iᵒᵖ) (v : (D.op ⋙ Q ⋙ uliftFunctor.{u, v}).obj j),
      colimit.desc (D.op ⋙ Q ⋙ uliftFunctor.{u, v}) ((Q ⋙ uliftFunctor.{u, v}).mapCocone c.op) (colimit.ι (D.op ⋙ Q ⋙ uliftFunctor.{u, v}) j v) =
        ULift.up (Q.map (c.π.app j.unop).op v.down) := fun {Q} j v => by
    exact ConcreteCategory.congr_hom (colimit.ι_desc ((Q ⋙ uliftFunctor.{u, v}).mapCocone c.op) j) v
  have map_ι : ∀ (j : Iᵒᵖ) (v : (D.op ⋙ (X ⋙ uliftFunctor.{u, v})).obj j),
      colimMap (Functor.whiskerLeft D.op (Functor.whiskerRight f uliftFunctor.{u, v})) (colimit.ι (D.op ⋙ (X ⋙ uliftFunctor.{u, v})) j v) =
        colimit.ι (D.op ⋙ (Y ⋙ uliftFunctor.{u, v})) j (ULift.up (f.app _ v.down)) := fun j v => by
    exact ConcreteCategory.congr_hom (ι_colimMap (Functor.whiskerLeft D.op (Functor.whiskerRight f uliftFunctor.{u, v})) j) v
  have w_ι : ∀ {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v} {j k : Iᵒᵖ} (g : j ⟶ k) (v : (D.op ⋙ Q ⋙ uliftFunctor.{u, v}).obj j),
      colimit.ι (D.op ⋙ Q ⋙ uliftFunctor.{u, v}) k (ULift.up (Q.map (D.map g.unop).op v.down)) =
        colimit.ι (D.op ⋙ Q ⋙ uliftFunctor.{u, v}) j v := fun {Q} {j k} g v =>
    ConcreteCategory.congr_hom (colimit.w (D.op ⋙ Q ⋙ uliftFunctor.{u, v}) g) v
  have trans_map : ∀ {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v} {j k : I} (g : k ⟶ j) (v : Q.obj (op (D.obj j))),
      Q.map (c.π.app k).op (Q.map (D.map g).op v) = Q.map (c.π.app j).op v := fun {Q} {j k} g v => by
    rw [← Functor.map_comp_apply, ← op_comp, c.w]
  refine (Types.isPullback_iff _ _ _ _).mpr ⟨?_, ?_, ?_⟩
  · refine colimit.hom_ext fun j => ?_
    ext v
    refine (congrArg (uliftFunctor.{u, v}.map (f.app _)) (desc_ι (Q := X) j v)).trans ?_
    refine Eq.trans ?_ (congrArg (colimit.desc (D.op ⋙ (Y ⋙ uliftFunctor.{u, v})) ((Y ⋙ uliftFunctor.{u, v}).mapCocone c.op)) (map_ι j v)).symm
    refine Eq.trans ?_ (desc_ι (Q := Y) j _).symm
    exact congrArg ULift.up (NatTrans.naturality_apply f _ v.down)
  · intro a b ⟨h₁, h₂⟩
    obtain ⟨j₁, v₁, rfl⟩ := Types.jointly_surjective_of_isColimit (colimit.isColimit (D.op ⋙ (X ⋙ uliftFunctor.{u, v}))) a
    obtain ⟨j₂, v₂, rfl⟩ := Types.jointly_surjective_of_isColimit (colimit.isColimit (D.op ⋙ (X ⋙ uliftFunctor.{u, v}))) b
    let k := IsFiltered.max j₁ j₂
    let a' := X.map (D.map (IsFiltered.leftToMax j₁ j₂).unop).op v₁.down
    let b' := X.map (D.map (IsFiltered.rightToMax j₁ j₂).unop).op v₂.down
    have ea : (colimit.cocone (D.op ⋙ (X ⋙ uliftFunctor.{u, v}))).ι.app j₁ v₁ = colimit.ι (D.op ⋙ (X ⋙ uliftFunctor.{u, v})) k (ULift.up a') :=
      (w_ι (Q := X) _ v₁).symm
    have eb : (colimit.cocone (D.op ⋙ (X ⋙ uliftFunctor.{u, v}))).ι.app j₂ v₂ = colimit.ι (D.op ⋙ (X ⋙ uliftFunctor.{u, v})) k (ULift.up b') :=
      (w_ι (Q := X) _ v₂).symm
    rw [ea, eb] at h₂ ⊢
    rw [ea, eb] at h₁
    have h₁' := (desc_ι (Q := X) k (ULift.up a')).symm.trans (h₁.trans (desc_ι (Q := X) k (ULift.up b')))
    have h₂' := (map_ι k (ULift.up a')).symm.trans (h₂.trans (map_ι k (ULift.up b')))
    obtain ⟨l, g₁, g₂, hl⟩ := (Types.FilteredColimit.colimit_eq_iff _).1 h₂'
    obtain ⟨m, h, e⟩ := IsFilteredOrEmpty.cocone_maps g₁ g₂
    let g := g₁ ≫ h
    have hfab : f.app _ (X.map (D.map g.unop).op a') = f.app _ (X.map (D.map g.unop).op b') := by
      have hl' : Y.map (D.map g₁.unop).op (f.app _ a') = Y.map (D.map g₂.unop).op (f.app _ b') :=
        congrArg ULift.down hl
      have s₁ : ∀ (g' : k ⟶ l) (w : Y.obj (op (D.obj k.unop))),
          Y.map (D.map (g' ≫ h).unop).op w = Y.map (D.map h.unop).op (Y.map (D.map g'.unop).op w) := by
        intro g' w
        change Y.map (D.map (h.unop ≫ g'.unop)).op w = _
        rw [D.map_comp, op_comp, Functor.map_comp_apply]
      refine (NatTrans.naturality_apply f _ a').trans (Eq.trans ?_ (NatTrans.naturality_apply f _ b').symm)
      exact (s₁ g₁ _).trans ((congrArg (Y.map (D.map h.unop).op) hl').trans ((s₁ g₂ _).symm.trans
        (congrArg (fun q => Y.map (D.map (unop q)).op (f.app _ b')) e.symm)))
    have hpab : X.map (c.π.app m.unop).op (X.map (D.map g.unop).op a') =
        X.map (c.π.app m.unop).op (X.map (D.map g.unop).op b') := by
      exact (trans_map (Q := X) g.unop a').trans ((congrArg ULift.down h₁').trans
        (trans_map (Q := X) g.unop b').symm)
    obtain ⟨n, u, hn⟩ := hinj m.unop _ _ hfab hpab
    refine (Types.FilteredColimit.colimit_eq_iff _).2 ⟨op n, g ≫ u.op, g ≫ u.op, ?_⟩
    refine congrArg ULift.up ?_
    change X.map (D.map (u ≫ g.unop)).op a' = X.map (D.map (u ≫ g.unop)).op b'
    rw [D.map_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply]
    exact hn
  · intro x y h
    obtain ⟨i', y₀, rfl⟩ := Types.jointly_surjective_of_isColimit (colimit.isColimit (D.op ⋙ (Y ⋙ uliftFunctor.{u, v}))) y
    have h' := h
    change _ = colimit.desc (D.op ⋙ (Y ⋙ uliftFunctor.{u, v})) ((Y ⋙ uliftFunctor.{u, v}).mapCocone c.op) (colimit.ι (D.op ⋙ (Y ⋙ uliftFunctor.{u, v})) i' y₀) at h'
    rw [desc_ι (Q := Y)] at h'
    obtain ⟨j, u, xj, hx₁, hx₂⟩ := hsur x.down i'.unop y₀.down (congrArg ULift.down h')
    refine ⟨colimit.ι (D.op ⋙ (X ⋙ uliftFunctor.{u, v})) (op j) (ULift.up xj), ?_, ?_⟩
    · exact (desc_ι (Q := X) (op j) (ULift.up xj)).trans (congrArg ULift.up hx₁)
    · exact (map_ι (op j) (ULift.up xj)).trans
        ((congrArg _ (congrArg ULift.up hx₂)).trans (w_ι (Q := Y) u.op y₀))

section Main

open AlgMag.GB AlgMag.Lifts AlgMag.SmoothSchemes AlgMag.SpacesLift

variable {M : Type u} [AddCommMonoid M] [SM B M] (N : AddSubmonoid M)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {aX : AAction (fppfO B S hS) M X}
  {aY : AAction (fppfO B S hS) M Y}

/-- **Fact 3.19** (functor form, Stacks 049J): if `f : X → Y` is an equivariant morphism of
algebraic spaces, locally of finite presentation, then `f^N : X^N → Y^N` is a limit preserving
transformation of functors, for any commutative monoid `M`. No representability of `X^N`, `Y^N`
is assumed. `#M` is below the cutoff of the site. -/
theorem fact319_relativelyLimitPreserving (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : EquivariantHom aX aY)
    (hf : Space.IsLocallyOfFinitePresentation B S hS f.hom) :
    RelativelyLimitPreserving.{u, u + 1, u, u} B S hS (attractorMap f N) := by
  have hrlp := relativelyLimitPreserving_of_isLocallyOfFinitePresentation B S hS hX hY hf
  refine rlp_of_squares _ fun I _ _ D c hc hA hAp => ?_
  have : ∀ i, IsAffine (τS (D.obj i)) := hA
  have : IsAffine (τS c.pt) := hAp
  obtain ⟨lN⟩ := isLimit_cN N D c hc
  obtain ⟨lM⟩ := isLimit_cM (M := M) N D c hc
  obtain ⟨sq₁, sq₁i⟩ := limit_square hrlp lN (fun i => inferInstanceAs (IsAffine (Spec _)))
    (inferInstanceAs (IsAffine (Spec _)))
  obtain ⟨-, sq₂⟩ := limit_square hrlp lM (fun i => inferInstanceAs (IsAffine (Spec _)))
    (inferInstanceAs (IsAffine (Spec _)))
  have nat : ∀ {T T₁ : BigFppfOver B S hS} (u : T₁ ⟶ T) (w : X.obj (op T)),
      f.hom.app _ (pb X u w) = pb Y u (f.hom.app _ w) := fun u w =>
    NatTrans.naturality_apply f.hom u.op w
  have vv_push : ∀ {T : BigFppfOver B S hS} [IsAffine (τS T)] (ξ : AttractorPt aX N T),
      vvS N (AttractorPt.push f ξ) = f.hom.app _ (vvS N ξ) := fun _ => rfl
  have vv_inj : ∀ {T : BigFppfOver B S hS} [IsAffine (τS T)] {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
      {a : AAction (fppfO B S hS) M F} (ξ ξ' : AttractorPt a N T), vvS N ξ = vvS N ξ' → ξ = ξ' :=
    fun _ _ h => (attractorPtEquivOfUniversal (specU N _ _ rfl)).injective (Subtype.ext h)
  refine ⟨fun x i₀ y hxy => ?_, fun i a b hab hres => ?_⟩
  · let φ : AttractorPt aX N c.pt := x
    let ψ : AttractorPt aY N (D.obj i₀) := y
    have hxy' : AttractorPt.push f φ = ψ.baseChange (c.π.app i₀) := hxy
    have hcond : f.hom.app _ (vvS N φ) = pb Y (muC N D c i₀) (vvS N ψ) := by
      rw [← vv_push, vvS_base, hxy']
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
    refine ⟨k, v ≫ u, φk, ?_, ?_⟩
    · change φk.baseChange (c.π.app k) = φ
      refine vv_inj (T := c.pt) _ _ ?_
      rw [← vvS_base, a1]
      exact (pb_comp X (muS (T₀ := c.pt) (T := D.obj k) N (c.π.app k)) (muS N (D.map v)) xj).symm.trans
        ((congrArg (fun m => pb X m xj)
          (muS_comp (T₁ := c.pt) N (c.π.app k) (D.map v) (c.π.app j) (c.w v))).trans hx₁')
    · change AttractorPt.push f φk = ψ.baseChange (D.map (v ≫ u))
      refine vv_inj _ _ ?_
      rw [vv_push, ← vvS_base, a1]
      exact hxkf
  · let a' : AttractorPt aX N (D.obj i) := a
    let b' : AttractorPt aX N (D.obj i) := b
    have hab' : AttractorPt.push f a' = AttractorPt.push f b' := hab
    have hres' : a'.baseChange (c.π.app i) = b'.baseChange (c.π.app i) := hres
    have h1 : f.hom.app _ (vvS N a') = f.hom.app _ (vvS N b') := by
      rw [← vv_push, ← vv_push, hab']
    have h2 : pb X (muC N D c i) (vvS N a') = pb X (muC N D c i) (vvS N b') := by
      rw [vvS_base, vvS_base, hres']
    obtain ⟨j, u, hj⟩ := sq₁i i (vvS N a') (vvS N b') h1 h2
    refine ⟨j, u, ?_⟩
    change a'.baseChange (D.map u) = b'.baseChange (D.map u)
    refine vv_inj _ _ ?_
    have hj' : pb X (muS N (D.map u)) (vvS N a') = pb X (muS N (D.map u)) (vvS N b') := hj
    rw [vvS_base, vvS_base] at hj'
    exact hj'

/-- **Fact 3.19** for a commutative monoid `M`. -/
alias fact319_relativelyLimitPreserving_monoid := fact319_relativelyLimitPreserving

end Main

end AlgMag.Final3Fact319
