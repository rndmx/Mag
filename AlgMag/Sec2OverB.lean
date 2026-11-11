/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec3Remaining
import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
import StacksFrontier.AlgebraicGeometry.Spaces.Flat
import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation

/-!
# Algebraic Magnetism, §2 over an algebraic space `B`

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026): Definition 2.4 (iii), Facts 2.7,
2.10 (vi), 2.12, 2.13, 2.15 and Proposition 2.8 (iv), for `B` an algebraic space over `S` in the
sense of the Stacks library, with the flat and finitely presented morphisms of that library.
`𝔸(N)_B` is the presheaf `AlgMag.AB` of `Sec3Remaining`.

The site has a size cutoff, so `𝔸(N)_S` has to lie in it: the hypothesis
`hN : B.Contains (GB.A N S).left`. The paper has no cutoff. Without it the presheaf `𝔸(N)_S` is not
representable on the site.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Space

namespace AlgMag.OverB

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-! ### Representing `𝔸(N)_S` on the site -/

/-- An object of the site, as a scheme over `S`. -/
abbrev toOverObj (U : BigFppfOver B S hS) : Over S := Over.mk U.hom.hom

/-- A morphism of the site, as a morphism of schemes over `S`. -/
abbrev toOverMap {U V : BigFppfOver B S hS} (g : U ⟶ V) : toOverObj U ⟶ toOverObj V :=
  Over.homMk g.left.hom (by
    have := congrArg (fun k => k.hom) (Over.w g)
    exact this)

/-- `𝔸(N)_S` as an object of the site. -/
noncomputable abbrev Aobj (N : Type u) [AddCommMonoid N] (hN : B.Contains (GB.A N S).left) :
    BigFppfOver B S hS :=
  Over.mk (ObjectProperty.homMk (GB.A N S).hom : B.obj hN ⟶ B.obj hS)

/-- `S` as the terminal object of the site. -/
abbrev T0 (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) : BigFppfOver B S hS :=
  Over.mk (𝟙 _)

/-- A morphism to `𝔸(N)_S` on the site is a morphism of schemes over `S`. -/
noncomputable def homEquiv {N : Type u} [AddCommMonoid N] (hN : B.Contains (GB.A N S).left)
    (U : BigFppfOver B S hS) : (U ⟶ Aobj N hN) ≃ (toOverObj U ⟶ GB.A N S) where
  toFun f := Over.homMk (show U.left.obj ⟶ (GB.A N S).left from f.left.hom) (by
    have := congrArg (fun k => k.hom) (Over.w f)
    exact this)
  invFun g := Over.homMk (ObjectProperty.homMk (show U.left.obj ⟶ (GB.A N S).left from g.left)) (by
    refine ObjectProperty.hom_ext _ ?_
    exact Over.w g)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The functor of points of `𝔸(N)_S` on the site. -/
noncomputable def ptsSite {N : Type u} [AddCommMonoid N] (hN : B.Contains (GB.A N S).left)
    (U : BigFppfOver B S hS) : (U ⟶ Aobj N hN) ≃ APt (fppfO B S hS) N (op U) :=
  (homEquiv hN U).trans (GB.pts (toOverObj U))

lemma ptsSite_comp {N : Type u} [AddCommMonoid N] (hN : B.Contains (GB.A N S).left)
    {U V : BigFppfOver B S hS} (g : U ⟶ V) (f : V ⟶ Aobj N hN) :
    ptsSite hN U (g ≫ f) = APt.res g.op (ptsSite hN V f) :=
  (GB.pts_comp (toOverMap g) (homEquiv hN V f)).trans (MonoidHom.ext fun _ => rfl)

/-- The site form of `GB.Amap`. -/
noncomputable def AmapS {P Q : Type u} [AddCommMonoid P] [AddCommMonoid Q] (φ : P →+ Q)
    (hP : B.Contains (GB.A P S).left) (hQ : B.Contains (GB.A Q S).left) :
    (Aobj Q hQ : BigFppfOver B S hS) ⟶ Aobj P hP :=
  Over.homMk (ObjectProperty.homMk (GB.Amap φ S).left) (by
    refine ObjectProperty.hom_ext _ ?_
    exact Over.w (GB.Amap φ S))

lemma ptsSite_AmapS {P Q : Type u} [AddCommMonoid P] [AddCommMonoid Q] (φ : P →+ Q)
    (hP : B.Contains (GB.A P S).left) (hQ : B.Contains (GB.A Q S).left)
    {U : BigFppfOver B S hS} (f : U ⟶ Aobj Q hQ) :
    ptsSite hP U (f ≫ AmapS φ hP hQ) =
      (ptsSite hQ U f).comp (AddMonoidHom.toMultiplicative φ) :=
  GB.pts_comp_Amap φ (homEquiv hQ U f)

/-- The structure morphism of `𝔸(N)_S` on the site. -/
noncomputable def strS {N : Type u} [AddCommMonoid N] (hN : B.Contains (GB.A N S).left) :
    Aobj N hN ⟶ T0 B S hS :=
  Over.homMk (Aobj N hN).hom (by simp)

/-! ### Morphisms of `𝔸(·)_B` -/

variable (Bs : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- The structure morphism `𝔸(N)_B → B`. -/
noncomputable def pr (N : Type u) [AddCommMonoid N] : AB Bs N ⟶ Bs where
  app _ := ↾ Prod.snd
  naturality _ _ _ := rfl

/-- The morphism `𝔸(Q)_B → 𝔸(P)_B` over `B` dual to `φ : P → Q`. -/
noncomputable def ABmap {P Q : Type u} [AddCommMonoid P] [AddCommMonoid Q] (φ : P →+ Q) :
    AB Bs Q ⟶ AB Bs P where
  app _ := ↾ fun x => (x.1.comp (AddMonoidHom.toMultiplicative φ), x.2)
  naturality _ _ _ := rfl

/-- The projection `𝔸(N)_B → 𝔸(N)_S`. -/
noncomputable def prY {N : Type u} [AddCommMonoid N] (hN : B.Contains (GB.A N S).left) :
    AB Bs N ⟶ yoneda.obj (Aobj N hN) where
  app U := ↾ fun x => (ptsSite hN (unop U)).symm x.1
  naturality U V f := by
    ext x
    refine (ptsSite hN (unop V)).injective ?_
    change ptsSite hN (unop V) ((ptsSite hN (unop V)).symm (APt.res f x.1)) =
      ptsSite hN (unop V) (f.unop ≫ (ptsSite hN (unop U)).symm x.1)
    rw [ptsSite_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rfl

/-- `B → S`. -/
noncomputable def toT0 : Bs ⟶ yoneda.obj (T0 B S hS) where
  app U := ↾ fun _ => Over.homMk (unop U).hom (by simp)
  naturality U V f := by
    ext x
    exact Over.OverMorphism.ext (Over.w f.unop).symm

lemma hom_T0_ext {U : BigFppfOver B S hS} (f g : U ⟶ T0 B S hS) : f = g :=
  Over.OverMorphism.ext (by
    have h₁ := Over.w f
    have h₂ := Over.w g
    simpa using h₁.trans h₂.symm)

/-- **Definition 2.4 (iii).** `𝔸(N)_B = 𝔸(N)_S ×_S B`. -/
theorem isPullback_AB (N : Type u) [AddCommMonoid N] (hN : B.Contains (GB.A N S).left) :
    IsPullback (pr Bs N) (prY Bs hN) (toT0 Bs) (yoneda.map (strS hN)) := by
  refine IsPullback.of_forall_isPullback_app fun U => ?_
  refine (Types.isPullback_iff _ _ _ _).mpr ⟨?_, ?_, ?_⟩
  · ext x
    exact hom_T0_ext _ _
  · rintro ⟨a, b⟩ ⟨a', b'⟩ ⟨h₁, h₂⟩
    exact Prod.ext ((ptsSite hN (unop U)).symm.injective h₂) h₁
  · intro b f _
    exact ⟨(ptsSite hN (unop U) f, b), rfl, (ptsSite hN (unop U)).symm_apply_apply f⟩

/-- `𝔸(φ)_B` is the base change of `𝔸(φ)_S`. -/
theorem isPullback_ABmap {P Q : Type u} [AddCommMonoid P] [AddCommMonoid Q] (φ : P →+ Q)
    (hP : B.Contains (GB.A P S).left) (hQ : B.Contains (GB.A Q S).left) :
    IsPullback (ABmap Bs φ) (prY Bs hQ) (prY Bs hP) (yoneda.map (AmapS φ hP hQ)) := by
  refine IsPullback.of_forall_isPullback_app fun U => ?_
  have key : ∀ x : (AB Bs Q).obj U, (prY Bs hP).app U ((ABmap Bs φ).app U x) =
      ((prY Bs hQ).app U x) ≫ AmapS φ hP hQ := fun x => by
    refine (ptsSite hP (unop U)).injective ?_
    rw [ptsSite_AmapS]
    change ptsSite hP (unop U) ((ptsSite hP (unop U)).symm _) =
      (ptsSite hQ (unop U) ((ptsSite hQ (unop U)).symm _)).comp _
    simp only [Equiv.apply_symm_apply]
    rfl
  refine (Types.isPullback_iff _ _ _ _).mpr ⟨?_, ?_, ?_⟩
  · ext x
    exact key x
  · rintro ⟨a, b⟩ ⟨a', b'⟩ ⟨h₁, h₂⟩
    exact Prod.ext ((ptsSite hQ (unop U)).symm.injective h₂)
      (congrArg (fun z => z.2) h₁ : b = b')
  · rintro ⟨c, b⟩ f h
    refine ⟨(ptsSite hQ (unop U) f, b), Prod.ext ?_ rfl, (ptsSite hQ (unop U)).symm_apply_apply f⟩
    have h' : (ptsSite hP (unop U)).symm c = f ≫ AmapS φ hP hQ := h
    have := ptsSite_AmapS φ hP hQ f
    rw [← h', Equiv.apply_symm_apply] at this
    exact this.symm

variable {Bs} in
/-- **Definition 2.4 (iii).** `𝔸(N)_B` is an algebraic space. -/
theorem isAlgebraicSpace_AB (hBs : IsAlgebraicSpace B S hS Bs) (N : Type u) [AddCommMonoid N]
    (hN : B.Contains (GB.A N S).left) : IsAlgebraicSpace B S hS (AB Bs N) :=
  have hT := isAlgebraicSpace_yoneda B S hS (T0 B S hS)
  isAlgebraicSpace_of_isPullback hBs (isAlgebraicSpace_yoneda B S hS _) hT.isSheaf
    hT.diagonal_representable (isPullback_AB Bs N hN)

/-- **Fact 2.7.** `𝔸(N × L)_B = 𝔸(N)_B ×_B 𝔸(L)_B`. -/
theorem isPullback_AB_prod (N L : Type u) [AddCommMonoid N] [AddCommMonoid L] :
    IsPullback (ABmap Bs (AddMonoidHom.inl N L)) (ABmap Bs (AddMonoidHom.inr N L))
      (pr Bs N) (pr Bs L) := by
  refine IsPullback.of_forall_isPullback_app fun U => ?_
  refine (Types.isPullback_iff _ _ _ _).mpr ⟨rfl, ?_, ?_⟩
  · rintro x y ⟨h₁, h₂⟩
    refine (prodEquivB Bs U).injective (Subtype.ext (Prod.ext h₁ h₂))
  · intro x y h
    obtain ⟨z, hz⟩ := (prodEquivB Bs U).surjective ⟨(x, y), h⟩
    exact ⟨z, congrArg (fun p => p.1.1) hz, congrArg (fun p => p.1.2) hz⟩

/-! ### Transfer from the site -/

section Transfer

variable {W Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V T : BigFppfOver B S hS}

/-- Base change, Stacks 0AMM, from a morphism of the site. -/
theorem chart_of_isPullback (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (hP : IsEtaleLocalOnSourceAndTarget P)
    {p : W ⟶ Z} {q : W ⟶ yoneda.obj V} {g : Z ⟶ yoneda.obj T} {k : V ⟶ T}
    (sq : IsPullback p q g (yoneda.map k)) (hW : IsAlgebraicSpace B S hS W)
    (hZ : IsAlgebraicSpace B S hS Z) (hk : P ((SCH).map k)) :
    HoldsOnEveryEtaleChart B S hS P p := by
  have hst := holdsOnEveryEtaleChart_isStableUnderBaseChange B S hS P hP
  let W' : AlgebraicSpaces B S hS := ⟨W, hW⟩
  let Z' : AlgebraicSpaces B S hS := ⟨Z, hZ⟩
  let V' : AlgebraicSpaces B S hS := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
  let T' : AlgebraicSpaces B S hS := ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩
  let p' : W' ⟶ Z' := ObjectProperty.homMk p
  let q' : W' ⟶ V' := ObjectProperty.homMk q
  let g' : Z' ⟶ T' := ObjectProperty.homMk g
  let k' : V' ⟶ T' := ObjectProperty.homMk (yoneda.map k)
  have sq' : IsPullback q' p' k' g' :=
    IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ sq.w.symm) sq.flip
  exact hst.of_isPullback sq' (holdsOnEveryEtaleChart_yoneda_map B S hS hP k hk)

/-- A quasi-compact morphism of the site gives a quasi-compact morphism of presheaves. -/
theorem isQuasiCompact_yoneda_map (k : V ⟶ T) (hk : QuasiCompact ((SCH).map k)) :
    IsQuasiCompact B S hS (yoneda.map k) := by
  intro Z _ hZ g
  obtain ⟨U₀, a, hU, hs, he⟩ := hZ
  have : CompactSpace ((SCH).obj U₀) := hU
  obtain ⟨t, ht⟩ := yoneda.map_surjective (a ≫ g)
  have hS' := IsPullback.of_hasPullback t k
  have hY : IsPullback (yoneda.map (pullback.fst t k)) (yoneda.map (pullback.snd t k))
      (a ≫ g) (yoneda.map k) := by
    rw [← ht]
    exact hS'.map yoneda
  obtain ⟨b, hb⟩ : ∃ b, IsPullback (yoneda.map (pullback.fst t k)) b a
      (pullback.fst g (yoneda.map k)) :=
    ⟨_, IsPullback.of_bot' hY (IsPullback.of_hasPullback g (yoneda.map k))⟩
  have key (Q : MorphismProperty Scheme.{u})
      (h : (Q.inverseImage (SCH)).presheaf a) : (Q.inverseImage (SCH)).presheaf b :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hb h
  have hqc : QuasiCompact ((SCH).map (pullback.fst t k)) :=
    (inverseImage_isStableUnderBaseChange B S hS
      (P := @QuasiCompact.{u}) inferInstance).of_isPullback hS'.flip hk
  exact ⟨pullback t k, b, QuasiCompact.compactSpace_of_compactSpace ((SCH).map (pullback.fst t k)),
    key _ hs, AlgebraicGeometry.Space.isEtale_of_presheaf_etale B S hS (key _ (AlgebraicGeometry.Space.presheaf_etale_of_isEtale B S hS he))⟩

/-- An affine morphism of the site gives a quasi-separated morphism of presheaves. -/
theorem isQuasiSeparated_yoneda_map (k : V ⟶ T) (hk : IsAffineHom ((SCH).map k)) :
    IsQuasiSeparated B S hS (yoneda.map k) := by
  have hfst : IsAffineHom ((SCH).map (pullback.fst k k)) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom.{u})
      ((IsPullback.of_hasPullback k k).flip.map (SCH)) hk
  have hd : QuasiCompact ((SCH).map (pullback.diagonal k)) := by
    have h1 : (SCH).map (pullback.diagonal k) ≫ (SCH).map (pullback.fst k k ≫ k) = (SCH).map k := by
      rw [← Functor.map_comp, pullback.diagonal_fst_assoc]
    have h2 : IsAffineHom ((SCH).map (pullback.fst k k ≫ k)) := by
      rw [Functor.map_comp]; infer_instance
    have h3 : QuasiCompact ((SCH).map (pullback.diagonal k) ≫ (SCH).map (pullback.fst k k ≫ k)) := by
      rw [h1]; infer_instance
    exact QuasiCompact.of_comp _ ((SCH).map (pullback.fst k k ≫ k))
  let e := PreservesPullback.iso yoneda k k
  have hdi : yoneda.map (pullback.diagonal k) ≫ e.hom = pullback.diagonal (yoneda.map k) := by
    apply pullback.hom_ext <;> simp [e, ← Functor.map_comp]
  have sq : IsPullback (𝟙 _) (pullback.diagonal (yoneda.map k)) (yoneda.map (pullback.diagonal k))
      e.inv := IsPullback.of_horiz_isIso ⟨by rw [← hdi]; simp⟩
  exact isQuasiCompact_of_isPullback B S hS sq (isQuasiCompact_yoneda_map _ hd)

/-- Quasi-separatedness is stable under base change: the relative diagonal of a base change is a
base change of the relative diagonal. -/
theorem isQuasiSeparated_of_isPullback {W X Z Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y} (sq : IsPullback p q g f)
    (hf : IsQuasiSeparated B S hS f) : IsQuasiSeparated B S hS p := by
  let Pr : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    fun _ _ f => IsQuasiCompact B S hS f
  have hPr : Pr.IsStableUnderBaseChange :=
    ⟨fun sq hg => isQuasiCompact_of_isPullback B S hS sq hg⟩
  have : Pr.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact (MorphismProperty.IsStableUnderBaseChange.diagonal (P := Pr)).of_isPullback sq.flip hf

/-- Finite presentation transfers from the site. -/
theorem isFinitePresentation_of_isPullback
    {p : W ⟶ Z} {q : W ⟶ yoneda.obj V} {g : Z ⟶ yoneda.obj T} {k : V ⟶ T}
    (sq : IsPullback p q g (yoneda.map k)) (hW : IsAlgebraicSpace B S hS W)
    (hZ : IsAlgebraicSpace B S hS Z) (hl : LocallyOfFinitePresentation ((SCH).map k))
    (ha : IsAffineHom ((SCH).map k)) : IsFinitePresentation B S hS p :=
  ⟨chart_of_isPullback _ LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget sq hW hZ hl,
    isQuasiCompact_of_isPullback B S hS sq.flip (isQuasiCompact_yoneda_map k inferInstance),
    isQuasiSeparated_of_isPullback sq (isQuasiSeparated_yoneda_map k ha)⟩

end Transfer

/-! ### The cutoff for `N × L` -/

/-- `𝔸(N × L)_S` lies in the site if `𝔸(N)_S` and `𝔸(L)_S` do. -/
theorem contains_prod {N L : Type u} [AddCommMonoid N] [AddCommMonoid L]
    (hN : B.Contains (GB.A N S).left) (hL : B.Contains (GB.A L S).left) :
    B.Contains (GB.A (N × L) S).left := by
  have hp := Scheme.size_pullback_lt (GB.A N S).hom (GB.A L S).hom hN hL
  have e := (GB.isPullback_A_prod N L S).isoPullback
  exact lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact e.hom) hp

/-! ### Proposition 2.8 (iv), Fact 2.10 (vi) -/

/-- The canonical comparison `𝔸(N)_B ×_B 𝔸(L)_B → 𝔸(N × L)_B` of Fact 2.7. -/
noncomputable def fibIso (N L : Type u) [AddCommMonoid N] [AddCommMonoid L] :
    pullback (pr Bs N) (pr Bs L) ≅ AB Bs (N × L) :=
  (isPullback_AB_prod Bs N L).isoPullback.symm

lemma fibIso_inl (N L : Type u) [AddCommMonoid N] [AddCommMonoid L] :
    (fibIso Bs N L).hom ≫ ABmap Bs (AddMonoidHom.inl N L) = pullback.fst _ _ :=
  (isPullback_AB_prod Bs N L).isoPullback_inv_fst

lemma fibIso_inr (N L : Type u) [AddCommMonoid N] [AddCommMonoid L] :
    (fibIso Bs N L).hom ≫ ABmap Bs (AddMonoidHom.inr N L) = pullback.snd _ _ :=
  (isPullback_AB_prod Bs N L).isoPullback_inv_snd

section Mul

variable (N : Type u) [AddCommMonoid N]

/-- The multiplication `m : 𝔸(N)_B ×_B 𝔸(N)_B → 𝔸(N)_B`. -/
noncomputable def mulB : pullback (pr Bs N) (pr Bs N) ⟶ AB Bs N :=
  (fibIso Bs N N).hom ≫ ABmap Bs (diag N)

/-- The formula for `m`: the product of the two points of `𝔸(N)`, over the same point of `B`. -/
theorem mulB_apply {U : (BigFppfOver B S hS)ᵒᵖ} (z : (pullback (pr Bs N) (pr Bs N)).obj U) :
    (mulB Bs N).app U z =
      (((pullback.fst (pr Bs N) (pr Bs N)).app U z).1 *
          ((pullback.snd (pr Bs N) (pr Bs N)).app U z).1,
        ((pullback.fst (pr Bs N) (pr Bs N)).app U z).2) := by
  rw [← fibIso_inl Bs N N, ← fibIso_inr Bs N N]
  set w := (fibIso Bs N N).hom.app U z with hw
  refine Prod.ext (MonoidHom.ext fun n => ?_) rfl
  change w.1 _ = w.1 _ * w.1 _
  rw [← map_mul]
  exact congrArg w.1 (Prod.ext (add_zero _).symm (zero_add _).symm)

variable (hN : B.Contains (GB.A N S).left)

/-- `m` is a base change of the morphism `𝔸(N × N)_S → 𝔸(N)_S`. -/
theorem isPullback_mulB :
    IsPullback (mulB Bs N) ((fibIso Bs N N).hom ≫ prY Bs (contains_prod hN hN)) (prY Bs hN)
      (yoneda.map (AmapS (diag N) hN (contains_prod hN hN))) :=
  (isPullback_ABmap Bs (diag N) hN (contains_prod hN hN)).of_iso (fibIso Bs N N).symm
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [mulB]) (by simp) (by simp) (by simp)

variable {Bs} (hBs : IsAlgebraicSpace B S hS Bs)

include hBs hN in
/-- **Proposition 2.8 (iv).** If `N` acts freely on `N × N`, the multiplication
`𝔸(N)_B ×_B 𝔸(N)_B → 𝔸(N)_B` is a flat morphism of algebraic spaces. Cancellativity is not
needed. -/
theorem isFlat_mulB (h : IsFreeAlong (diag N)) : IsFlat B S hS (mulB Bs N) :=
  chart_of_isPullback _ Flat.isEtaleLocalOnSourceAndTarget (isPullback_mulB Bs N hN)
    (isAlgebraicSpace_pullback B S hS _ _ (isAlgebraicSpace_AB hBs N hN)
      (isAlgebraicSpace_AB hBs N hN) hBs)
    (isAlgebraicSpace_AB hBs N hN)
    (GB.flat_Amap (S := S) (diag N) (flat_diag ℤ h))

include hBs hN in
/-- **Fact 2.10 (vi)**, the multiplication. -/
theorem isFinitePresentation_mulB [AddMonoid.FG N] : IsFinitePresentation B S hS (mulB Bs N) :=
  isFinitePresentation_of_isPullback (isPullback_mulB Bs N hN)
    (isAlgebraicSpace_pullback B S hS _ _ (isAlgebraicSpace_AB hBs N hN)
      (isAlgebraicSpace_AB hBs N hN) hBs)
    (isAlgebraicSpace_AB hBs N hN)
    (GB.lfp_Amap (S := S) (diag N) (GB.finitePresentation_diag N))
    (inferInstanceAs (IsAffineHom (GB.Amap (diag N) S).left))

include hBs hN in
/-- **Fact 2.10 (vi)**, the structure morphism `𝔸(N)_B → B`. -/
theorem isFinitePresentation_pr [AddMonoid.FG N] : IsFinitePresentation B S hS (pr Bs N) :=
  isFinitePresentation_of_isPullback (isPullback_AB Bs N hN) (isAlgebraicSpace_AB hBs N hN) hBs
    (inferInstanceAs (LocallyOfFinitePresentation (GB.A N S).hom))
    (inferInstanceAs (IsAffineHom (GB.A N S).hom))

end Mul

/-! ### Fact 2.12 -/

section Action

variable {M : Type u} [AddCommMonoid M] (N : AddSubmonoid M)

/-- **Fact 2.12.** The action of `𝔸(M)_B` on `𝔸(N)_B` on points, as an action of the monoid `𝔸(M)`:
`(h, b) · (a, b) = (h|_N a, b)`. It preserves the projection to `B`. -/
noncomputable def aActionB : AAction (fppfO B S hS) M (AB Bs N) where
  smul h x := actB Bs N h x
  one_smul x := Prod.ext (by
    change APt.toMagnet N 1 * x.1 = x.1
    exact (congrArg (· * x.1) (MonoidHom.ext fun _ => rfl)).trans (one_mul _)) rfl
  mul_smul g h x := Prod.ext (by
    change APt.toMagnet N (g * h) * x.1 = APt.toMagnet N g * (APt.toMagnet N h * x.1)
    rw [← mul_assoc]
    rfl) rfl
  map_smul f h x := Prod.ext (APt.res_mul f _ _) rfl

/-- The coaction `n ↦ (n, n)`, dual to `X^n ↦ X^n ⊗ X^n` of Fact 2.12. -/
def coactHom : N →+ M × N := (N.subtype).prod (AddMonoidHom.id N)

/-- **Fact 2.12.** The action morphism `𝔸(M)_B ×_B 𝔸(N)_B → 𝔸(N)_B` over `B`. -/
noncomputable def actMorB : pullback (pr Bs M) (pr Bs N) ⟶ AB Bs N :=
  (fibIso Bs M N).hom ≫ ABmap Bs (coactHom N)

/-- The action morphism computes `actB`. -/
theorem actMorB_apply {U : (BigFppfOver B S hS)ᵒᵖ} (z : (pullback (pr Bs M) (pr Bs N)).obj U) :
    (actMorB Bs N).app U z =
      actB Bs N ((pullback.fst (pr Bs M) (pr Bs N)).app U z).1
        ((pullback.snd (pr Bs M) (pr Bs N)).app U z) := by
  rw [← fibIso_inl Bs M N, ← fibIso_inr Bs M N]
  set w := (fibIso Bs M N).hom.app U z with hw
  refine Prod.ext (MonoidHom.ext fun n => ?_) rfl
  change w.1 _ = w.1 _ * w.1 _
  rw [← map_mul]
  exact congrArg w.1 (Prod.ext (add_zero _).symm (zero_add _).symm)

end Action

/-! ### Facts 2.13 and 2.15 -/

section Maps

variable {M : Type u} [AddCommMonoid M]

/-- **Fact 2.13.** For `N ⊆ N'`, the morphism `𝔸(N')_B → 𝔸(N)_B`. -/
noncomputable def restrictB {N N' : AddSubmonoid M} (h : N ≤ N') : AB Bs N' ⟶ AB Bs N :=
  ABmap Bs (AddSubmonoid.inclusion h)

/-- **Fact 2.13.** `𝔸(N')_B → 𝔸(N)_B` is `𝔸(M)_B`-equivariant. -/
theorem restrictB_equivariant {N N' : AddSubmonoid M} (h : N ≤ N') {U : (BigFppfOver B S hS)ᵒᵖ}
    (k : APt (fppfO B S hS) M U) (x : (AB Bs N').obj U) :
    (restrictB Bs h).app U (actB Bs N' k x) = actB Bs N k ((restrictB Bs h).app U x) := rfl

/-- **Fact 2.13.** `𝔸(N')_B → 𝔸(N)_B` is a morphism of monoid objects: it commutes with the
multiplications on the points over a point `b` of `B`. -/
theorem restrictB_mul {N N' : AddSubmonoid M} (h : N ≤ N') {U : (BigFppfOver B S hS)ᵒᵖ}
    (x y : APt (fppfO B S hS) N' U) (b : Bs.obj U) :
    (restrictB Bs h).app U (x * y, b) =
      (((restrictB Bs h).app U (x, b)).1 * ((restrictB Bs h).app U (y, b)).1, b) := rfl

/-- **Fact 2.15.** For a face `F` of `N`, the morphism `𝔸(F)_B → 𝔸(N)_B`, extension by zero. -/
noncomputable def faceB {F N : AddSubmonoid M} (hF : IsFace F N) : AB Bs F ⟶ AB Bs N where
  app _ := ↾ fun x => (APt.faceExt hF x.1, x.2)
  naturality U V f := by
    ext x
    exact Prod.ext (APt.faceExt_res hF f x.1) rfl

/-- **Fact 2.15.** `𝔸(F)_B → 𝔸(N)_B` is `𝔸(M)_B`-equivariant. -/
theorem faceB_equivariant {F N : AddSubmonoid M} (hF : IsFace F N) {U : (BigFppfOver B S hS)ᵒᵖ}
    (k : APt (fppfO B S hS) M U) (x : (AB Bs F).obj U) :
    (faceB Bs hF).app U (actB Bs F k x) = actB Bs N k ((faceB Bs hF).app U x) :=
  Prod.ext (APt.faceExt_mul hF k x.1) rfl

end Maps

end AlgMag.OverB
