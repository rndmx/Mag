/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartConclude
import AlgMag.ChartEtaleFlat
import StacksFrontier.AlgebraicGeometry.Descent.SurjectiveEtaleDescent

/-!
# §6: the étale locus of `φ̃` on `W` is open and stable

`etaleLocusStable` proves `AlgMag.ChartConclude.EtaleLocusStable` for `W → X` locally of finite
presentation, `X` an algebraic space.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry DirectSum

universe u

namespace AlgMag.ChartEtale

open ChartConclude

/-- An open immersion factoring through `O`, with `O → Z` étale, is étale over `Z`. -/
lemma etale_comp_of_range {A X Z : Scheme.{u}} (j : A ⟶ X) [IsOpenImmersion j] (O : X.Opens)
    (b : X ⟶ Z) (hj : Set.range j ⊆ O) (hO : Etale (O.ι ≫ b)) : Etale (j ≫ b) := by
  have hr : Set.range j ⊆ Set.range O.ι := by rw [Scheme.Opens.range_ι]; exact hj
  have ht : IsOpenImmersion.lift O.ι j hr ≫ O.ι = j := IsOpenImmersion.lift_fac _ _ _
  have : Etale (IsOpenImmersion.lift O.ι j hr ≫ O.ι) := by rw [ht]; infer_instance
  have : Etale (IsOpenImmersion.lift O.ι j hr) := Etale.of_comp _ O.ι
  rw [← ht, Category.assoc]; infer_instance

/-- Étaleness is local on the source. -/
lemma etale_of_forall_open {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ f)) : Etale f := by
  choose U hx hU using h
  have top : iSup U = ⊤ := top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hx x⟩
  have : IsZariskiLocalAtSource (@Etale.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale.{u}) (Q := RingHom.Etale)
  exact (IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @Etale) U top).2 hU

section Site

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- An open of an object of the site, as an object. -/
noncomputable abbrev openObj (V : BigFppfOver B S hS) (O : ((SCH).obj V).Opens) : BigFppfOver B S hS :=
  Chart.immObj V O.ι

/-- Its inclusion. -/
noncomputable abbrev openι (V : BigFppfOver B S hS) (O : ((SCH).obj V).Opens) : openObj V O ⟶ V :=
  Chart.immι V O.ι

instance openιOpen (V : BigFppfOver B S hS) (O : ((SCH).obj V).Opens) : IsOpenImmersion O.ι :=
  inferInstanceAs (IsOpenImmersion (Scheme.Opens.ι _))

lemma range_sub_ι {V T : BigFppfOver B S hS} (O : ((SCH).obj V).Opens) (τ : T ⟶ V)
    (h : Set.range ((SCH).map τ) ⊆ O) : Set.range ((SCH).map τ) ⊆ Set.range O.ι := by
  rw [Scheme.Opens.range_ι]; exact h

/-- The scheme map underlying `openLift`. -/
noncomputable def openLiftS {V T : BigFppfOver B S hS} (O : ((SCH).obj V).Opens) (τ : T ⟶ V)
    (h : Set.range ((SCH).map τ) ⊆ O) : (SCH).obj T ⟶ O.toScheme :=
  @IsOpenImmersion.lift _ _ _ O.ι ((SCH).map τ) (openιOpen V O) (range_sub_ι O τ h)

lemma openLiftS_fac {V T : BigFppfOver B S hS} (O : ((SCH).obj V).Opens) (τ : T ⟶ V)
    (h : Set.range ((SCH).map τ) ⊆ O) : openLiftS O τ h ≫ O.ι = (SCH).map τ :=
  @IsOpenImmersion.lift_fac _ _ _ O.ι ((SCH).map τ) (openιOpen V O) _

/-- A map landing in the open factors through it. -/
noncomputable def openLift {V T : BigFppfOver B S hS} (O : ((SCH).obj V).Opens) (τ : T ⟶ V)
    (h : Set.range ((SCH).map τ) ⊆ O) : T ⟶ openObj V O :=
  Over.homMk ⟨openLiftS O τ h⟩ (by
    apply InducedCategory.hom_ext
    change openLiftS O τ h ≫ O.ι ≫ V.hom.hom = T.hom.hom
    rw [← Category.assoc, openLiftS_fac]
    exact congrArg (fun z => z.hom) (Over.w τ))

@[simp, reassoc] lemma openLift_ι {V T : BigFppfOver B S hS} (O : ((SCH).obj V).Opens) (τ : T ⟶ V)
    (h : Set.range ((SCH).map τ) ⊆ O) : openLift O τ h ≫ openι V O = τ :=
  ChartMain.siteExt (by
    rw [Functor.map_comp]; exact openLiftS_fac O τ h)

instance (V : BigFppfOver B S hS) (O : ((SCH).obj V).Opens) : Mono (openι V O) := by
  refine ⟨fun a b e => ChartMain.siteExt ?_⟩
  have e' := congrArg (fun z => (SCH).map z) e
  simp only [Functor.map_comp] at e'
  exact (cancel_mono O.ι).1 e'

/-- The inverse image of an open is a pullback. -/
lemma isPullback_open {Q V : BigFppfOver B S hS} (φ : Q ⟶ V) (O : ((SCH).obj V).Opens) :
    IsPullback (openLift O (openι Q ((SCH).map φ ⁻¹ᵁ O) ≫ φ) (by
        rintro _ ⟨x, rfl⟩
        rw [Functor.map_comp]
        exact x.2))
      (openι Q ((SCH).map φ ⁻¹ᵁ O)) (openι V O) φ := by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => openLift _ s.snd ?_) ?_ ?_ ?_⟩⟩
  · rintro _ ⟨x, rfl⟩
    have e : (SCH).map s.snd ≫ (SCH).map φ = (SCH).map s.fst ≫ (SCH).map (openι V O) := by
      rw [← Functor.map_comp, ← Functor.map_comp, s.condition]
    change (SCH).map φ ((SCH).map s.snd x) ∈ O
    rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]
    exact ((SCH).map s.fst x).2
  · intro s
    refine (cancel_mono (openι V O)).1 ?_
    rw [Category.assoc]
    refine (congrArg _ (openLift_ι _ _ _)).trans ?_
    rw [← Category.assoc]
    refine (congrArg (· ≫ φ) (openLift_ι _ _ _)).trans ?_
    exact s.condition.symm
  · intro s; exact openLift_ι _ _ _
  · intro s m _ h2
    refine (cancel_mono (openι Q _)).1 ?_
    rw [h2]; exact (openLift_ι _ _ _).symm

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {W : BigFppfOver B S hS}

/-- Paste of the open square with a square of `f`. -/
lemma isPullback_preimage {f : yoneda.obj W ⟶ X} {Q T : BigFppfOver B S hS} {a : Q ⟶ W} {b : Q ⟶ T}
    {x : yoneda.obj T ⟶ X} (sq : IsPullback (yoneda.map a) (yoneda.map b) f x) (O : ((SCH).obj W).Opens) :
    IsPullback (yoneda.map (openLift O (openι Q ((SCH).map a ⁻¹ᵁ O) ≫ a) (by
        rintro _ ⟨x, rfl⟩
        rw [Functor.map_comp]
        exact x.2)))
      (yoneda.map (openι Q ((SCH).map a ⁻¹ᵁ O) ≫ b)) (yoneda.map (openι W O) ≫ f) x := by
  have := ((isPullback_open a O).map yoneda).paste_vert sq
  rwa [← yoneda.map_comp] at this

/-- `D(g) → X` étale gives étaleness of the inverse image of `D(g)`, for any square. -/
lemma etale_of_isEtaleOn [IsAffine ((SCH).obj W)] {f : yoneda.obj W ⟶ X} {g : Γ((SCH).obj W, ⊤)} (hg : IsEtaleOn f g)
    {Q T : BigFppfOver B S hS} {a : Q ⟶ W} {b : Q ⟶ T} {x : yoneda.obj T ⟶ X}
    (sq : IsPullback (yoneda.map a) (yoneda.map b) f x) :
    Etale (((SCH).map a ⁻¹ᵁ ((SCH).obj W).basicOpen g).ι ≫ (SCH).map b) := by
  have := hg.property x _ _ (isPullback_preimage sq (((SCH).obj W).basicOpen g))
  change Etale ((SCH).map (_ ≫ b)) at this
  rwa [Functor.map_comp] at this

/-- The criterion for `IsEtaleOn`, on the represented pullbacks of `f`. -/
lemma isEtaleOn_of_square [IsAffine ((SCH).obj W)] {f : yoneda.obj W ⟶ X}
    (hrep : yoneda.relativelyRepresentable f) (g : Γ((SCH).obj W, ⊤))
    (H : ∀ {T : BigFppfOver B S hS} (x : yoneda.obj T ⟶ X),
      Etale (((SCH).map (hrep.fst' x) ⁻¹ᵁ ((SCH).obj W).basicOpen g).ι ≫ (SCH).map (hrep.snd x))) :
    IsEtaleOn f g := by
  have : MorphismProperty.RespectsIso (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH)) :=
    MorphismProperty.RespectsIso.inverseImage _ _
  refine MorphismProperty.relative.of_exists fun T x => ⟨_, _, _,
    isPullback_preimage (hrep.isPullback' x) (((SCH).obj W).basicOpen g), ?_⟩
  change Etale ((SCH).map (_ ≫ hrep.snd x))
  rw [Functor.map_comp]
  exact H x

/-- `D(g)` covered by opens `D(h)` with `D(h) → X` étale: `D(g) → X` is étale. -/
lemma isEtaleOn_of_cover [IsAffine ((SCH).obj W)] {f : yoneda.obj W ⟶ X}
    (hrep : yoneda.relativelyRepresentable f) (g : Γ((SCH).obj W, ⊤))
    (H : ∀ w ∈ ((SCH).obj W).basicOpen g, ∃ h, w ∈ ((SCH).obj W).basicOpen h ∧ IsEtaleOn f h) :
    IsEtaleOn f g := by
  refine isEtaleOn_of_square hrep g fun {T} x => etale_of_forall_open _ fun y => ?_
  obtain ⟨h, hw, hE⟩ := H _ y.2
  have hO := etale_of_isEtaleOn hE (hrep.isPullback' x)
  set a := (SCH).map (hrep.fst' x)
  set U := a ⁻¹ᵁ ((SCH).obj W).basicOpen g
  refine ⟨U.ι ⁻¹ᵁ (a ⁻¹ᵁ ((SCH).obj W).basicOpen h), hw, ?_⟩
  rw [← Category.assoc]
  refine etale_comp_of_range _ (a ⁻¹ᵁ ((SCH).obj W).basicOpen h) _ ?_ hO
  rintro _ ⟨z, rfl⟩
  exact z.2

/-- **The étale local-on-source step.** If `e : E → W` is étale, `E → X` is étale, and `D(h)` lies in
the image of `e`, then `D(h) → X` is étale. -/
lemma isEtaleOn_of_range [IsAffine ((SCH).obj W)] {f : yoneda.obj W ⟶ X}
    (hrep : yoneda.relativelyRepresentable f) {E : BigFppfOver B S hS} (e : E ⟶ W)
    (he : Etale ((SCH).map e))
    (hE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) (yoneda.map e ≫ f))
    (h : Γ((SCH).obj W, ⊤))
    (hr : (((SCH).obj W).basicOpen h : Set ((SCH).obj W)) ⊆ Set.range ((SCH).map e)) :
    IsEtaleOn f h := by
  refine isEtaleOn_of_square hrep h fun {T} x => ?_
  have sq := hrep.isPullback' x
  have pb := IsPullback.of_hasPullback e (hrep.fst' x)
  have sq' := (pb.map yoneda).paste_vert sq
  rw [← yoneda.map_comp] at sq'
  have h1 : Etale ((SCH).map (pullback.snd e (hrep.fst' x) ≫ hrep.snd x)) := hE.property x _ _ sq'
  rw [Functor.map_comp] at h1
  have pbS := pb.map (SCH)
  have h2 : Etale ((SCH).map (pullback.snd e (hrep.fst' x))) :=
    MorphismProperty.of_isPullback (P := @Etale) pbS he
  set a := (SCH).map (hrep.fst' x)
  set U := a ⁻¹ᵁ ((SCH).obj W).basicOpen h
  set p := (SCH).map (pullback.snd e (hrep.fst' x))
  have hsurj : Surjective (p ∣_ U) := by
    refine ⟨fun y => ?_⟩
    obtain ⟨y₀, hy₀⟩ := hr y.2
    obtain ⟨z, hz1, hz2⟩ := exists_pt_of_isPullback pbS y₀ y.1 hy₀
    refine ⟨⟨z, ?_⟩, Subtype.ext ?_⟩
    · change p z ∈ U
      rw [show p z = y.1 from hz2]; exact y.2
    · exact (morphismRestrict_base_coe p U _).trans hz2
  have h3 : Etale ((p ∣_ U) ≫ U.ι ≫ (SCH).map (hrep.snd x)) := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]; infer_instance
  exact Stacks.Etale.etale_of_comp_surjective_etale (p ∣_ U) _

/-! ### The universal property of `U[M]`, and pullback squares from elements -/

section Twist

variable {M : Type u} [AddCommGroup M] [AddMonoid.FG M]

open ChartMain

/-- The group point carried by a map to `Spec Γ(U)[M]`. -/
noncomputable def ptOf {U Z : BigFppfOver B S hS} [IsAffine ((SCH).obj U)]
    (τ : Z ⟶ spObj U (ι1 U (M := M)) contains1) : Multiplicative M →* Γ((SCH).obj Z, ⊤) :=
  secPt ((SCH).map τ).appTop.hom (univPt1 (U := U))

lemma ptOf_comp {U Z Z' : BigFppfOver B S hS} [IsAffine ((SCH).obj U)] (m : Z' ⟶ Z)
    (τ : Z ⟶ spObj U (ι1 U (M := M)) contains1) :
    ptOf (m ≫ τ) = secPt ((SCH).map m).appTop.hom (ptOf τ) := by
  ext d
  simp only [ptOf, secPt, Functor.map_comp, Scheme.Hom.comp_appTop]
  rfl

/-- The map to `Spec Γ(U)[M]` given by a map to `U` and a group point. -/
noncomputable def lift1 {U Z : BigFppfOver B S hS} [IsAffine ((SCH).obj U)] (t : Z ⟶ U)
    (h : Multiplicative M →* Γ((SCH).obj Z, ⊤)) : Z ⟶ spObj U (ι1 U (M := M)) contains1 :=
  spLift U (ι1 U (M := M)) contains1 t (evalAt ((SCH).map t).appTop.hom h)
    (RingHom.ext fun b => evalAt_ι _ _ b)

lemma lift1_toT {U Z : BigFppfOver B S hS} [IsAffine ((SCH).obj U)] (t : Z ⟶ U)
    (h : Multiplicative M →* Γ((SCH).obj Z, ⊤)) :
    lift1 t h ≫ spToT U (ι1 U (M := M)) contains1 = t :=
  spLift_toT _ _ _ _ _ _

lemma ptOf_lift1 {U Z : BigFppfOver B S hS} [IsAffine ((SCH).obj U)] (t : Z ⟶ U)
    (h : Multiplicative M →* Γ((SCH).obj Z, ⊤)) : ptOf (lift1 t h) = h := by
  refine MonoidHom.ext fun m => ?_
  refine (spLift_appTop U (ι1 U (M := M)) contains1 t (evalAt _ h)
    (RingHom.ext fun b => evalAt_ι _ _ b) _).trans ?_
  refine (evalAt_single _ _ (Multiplicative.toAdd m) 1).trans ?_
  rw [map_one, one_mul]
  rfl

lemma ext1 {U Z : BigFppfOver B S hS} [IsAffine ((SCH).obj U)]
    {τ τ' : Z ⟶ spObj U (ι1 U (M := M)) contains1}
    (h₁ : τ ≫ spToT U (ι1 U (M := M)) contains1 = τ' ≫ spToT U (ι1 U (M := M)) contains1)
    (h₂ : ptOf τ = ptOf τ') : τ = τ' := by
  have hb : ∀ b, ((SCH).map τ).appTop.hom (spSec U (ι1 U (M := M)) contains1 (ι1 U b)) =
      ((SCH).map τ').appTop.hom (spSec U (ι1 U (M := M)) contains1 (ι1 U b)) := fun b => by
    have := congrArg (fun z => ((SCH).map z).appTop.hom b) h₁
    simp only [Functor.map_comp, Scheme.Hom.comp_appTop] at this
    rw [← spToT_appTop]
    exact this
  refine sp_hom_ext U fun x => ?_
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp only [map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]
  | single d b =>
    have e : (AddMonoidAlgebra.single d b : R1 U M) =
        ι1 U b * AddMonoidAlgebra.of (RT U) M (Multiplicative.ofAdd d) := by
      simp [AddMonoidAlgebra.single_mul_single]
    have h3 := DFunLike.congr_fun h₂ (Multiplicative.ofAdd d)
    rw [e, map_mul, map_mul, map_mul, hb]
    exact congrArg _ h3

/-- The inverse group point. -/
noncomputable def invPt {R : Type*} [CommRing R] (γ : Multiplicative M →* R) : Multiplicative M →* R :=
  γ.comp invMonoidHom

lemma mul_invPt {R : Type*} [CommRing R] (γ : Multiplicative M →* R) : γ * invPt γ = 1 := by
  refine MonoidHom.ext fun p => ?_
  change γ p * γ p⁻¹ = 1
  rw [← map_mul, mul_inv_cancel, map_one]

lemma invPt_mul {R : Type*} [CommRing R] (γ : Multiplicative M →* R) : invPt γ * γ = 1 := by
  rw [mul_comm]; exact mul_invPt γ

end Twist

/-- A square on represented objects is a pullback when it has the universal property on objects. -/
lemma isPullback_of_unique {f : yoneda.obj W ⟶ X} (hrep : yoneda.relativelyRepresentable f)
    {Q T : BigFppfOver B S hS} {x : yoneda.obj T ⟶ X} (a : Q ⟶ W) (b : Q ⟶ T)
    (hw : f.app (op Q) a = x.app (op Q) b)
    (H : ∀ {Z : BigFppfOver B S hS} (u : Z ⟶ W) (t : Z ⟶ T), f.app (op Z) u = x.app (op Z) t →
      ∃ m : Z ⟶ Q, m ≫ a = u ∧ m ≫ b = t)
    (U : ∀ {Z : BigFppfOver B S hS} (m m' : Z ⟶ Q), m ≫ a = m' ≫ a → m ≫ b = m' ≫ b → m = m') :
    IsPullback (yoneda.map a) (yoneda.map b) f x := by
  have sqR := hrep.isPullback' x
  have hwR : f.app (op _) (hrep.fst' x) = x.app (op _) (hrep.snd x) := by
    have t := congrArg (fun φ => φ.app (op (hrep.pullback x)) (𝟙 (hrep.pullback x))) sqR.w
    change f.app (op (hrep.pullback x)) (𝟙 _ ≫ hrep.fst' x) =
      x.app (op (hrep.pullback x)) (𝟙 _ ≫ hrep.snd x) at t
    rwa [Category.id_comp, Category.id_comp] at t
  obtain ⟨r, hr1, hr2⟩ := H (Z := hrep.pullback x) _ _ hwR
  have hwy : yoneda.map a ≫ f = yoneda.map b ≫ x := by
    ext ⟨Z⟩ m
    have e1 := NatTrans.naturality_apply f m.op a
    have e2 := NatTrans.naturality_apply x m.op b
    rw [hw] at e1
    exact e1.trans e2.symm
  let l : Q ⟶ hrep.pullback x := yoneda.preimage (sqR.lift (yoneda.map a) (yoneda.map b) hwy)
  have hl1 : l ≫ hrep.fst' x = a := yoneda.map_injective (by
    rw [yoneda.map_comp, Functor.map_preimage]; exact sqR.lift_fst _ _ _)
  have hl2 : l ≫ hrep.snd x = b := yoneda.map_injective (by
    rw [yoneda.map_comp, Functor.map_preimage]; exact sqR.lift_snd _ _ _)
  have e1 : l ≫ r = 𝟙 Q := U _ _ (by rw [Category.assoc, hr1, hl1, Category.id_comp])
    (by rw [Category.assoc, hr2, hl2, Category.id_comp])
  have e2 : r ≫ l = 𝟙 _ := yoneda.map_injective (sqR.hom_ext
    (by rw [← yoneda.map_comp, ← yoneda.map_comp, Category.assoc, hl1, hr1, Category.id_comp])
    (by rw [← yoneda.map_comp, ← yoneda.map_comp, Category.assoc, hl2, hr2, Category.id_comp]))
  let e : hrep.pullback x ≅ Q := ⟨r, l, e2, e1⟩
  exact IsPullback.of_iso sqR (yoneda.mapIso e) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp only [Iso.refl_hom, Category.comp_id, Functor.mapIso_hom, ← yoneda.map_comp]; exact (congrArg _ hr1).symm)
    (by simp only [Iso.refl_hom, Category.comp_id, Functor.mapIso_hom, ← yoneda.map_comp]; exact (congrArg _ hr2).symm)
    (by simp) (by simp)

section Key

variable {M : Type u} [AddCommGroup M] [AddMonoid.FG M]

open ChartMain

/-- Lift from an element-wise cone over a square on represented objects. -/
lemma exists_lift_of_square {f : yoneda.obj W ⟶ X} {Q T Z : BigFppfOver B S hS} {a : Q ⟶ W} {b : Q ⟶ T}
    {x : yoneda.obj T ⟶ X} (sq : IsPullback (yoneda.map a) (yoneda.map b) f x) (u : Z ⟶ W) (t : Z ⟶ T)
    (h : f.app (op Z) u = x.app (op Z) t) : ∃ m : Z ⟶ Q, m ≫ a = u ∧ m ≫ b = t := by
  have hw : yoneda.map u ≫ f = yoneda.map t ≫ x := by
    ext ⟨Z'⟩ m
    have e1 := NatTrans.naturality_apply f m.op u
    have e2 := NatTrans.naturality_apply x m.op t
    rw [h] at e1
    exact e1.trans e2.symm
  refine ⟨yoneda.preimage (sq.lift _ _ hw), yoneda.map_injective ?_, yoneda.map_injective ?_⟩
  · rw [yoneda.map_comp, Functor.map_preimage]; exact sq.lift_fst _ _ _
  · rw [yoneda.map_comp, Functor.map_preimage]; exact sq.lift_snd _ _ _

variable {actX : AAction (fppfO B S hS) M X} (actW : AAction (fppfO B S hS) M (yoneda.obj W))
  {f : yoneda.obj W ⟶ X}

/-- `γ⁻¹ (γ u) = u`. -/
lemma smulAt_inv_smulAt {Z : BigFppfOver B S hS} (γ : Multiplicative M →* Γ((SCH).obj Z, ⊤)) (u : Z ⟶ W) :
    smulAt actW (invPt γ) (smulAt actW γ u) = u := by
  rw [← smulAt_mul, invPt_mul, smulAt_one]

/-- `γ (γ⁻¹ u) = u`. -/
lemma smulAt_smulAt_inv {Z : BigFppfOver B S hS} (γ : Multiplicative M →* Γ((SCH).obj Z, ⊤)) (u : Z ⟶ W) :
    smulAt actW γ (smulAt actW (invPt γ) u) = u := by
  rw [← smulAt_mul, mul_invPt, smulAt_one]

/-- **The twist of §6**, and flat descent. Let `Y₀ = W ×_X T₀`, `T₀` affine, `w₁` a point of
`W[M]` at which `c(g) ≠ 0`, with `D(g) → X` étale, and `y₀` a point of `Y₀` over the image of `w₁` in `W`.
The twist `(u, r) ↦ (r⁻¹ u, r)` identifies `W ×_{X, γ·x} T₀[M]` with `Y₀[M]`, so `Y₀[M] → T₀[M]` is
étale above `D(g)`, and so `Y₀ → T₀` is étale at `y₀`. -/
theorem exists_open_etale_of_twist [hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    (hrep : yoneda.relativelyRepresentable f)
    (hf : IsEquivariant actW actX f) {g : Γ((SCH).obj W, ⊤)} (hg : IsEtaleOn f g)
    {T₀ Y₀ : BigFppfOver B S hS} [IsAffine ((SCH).obj T₀)] {x₀ : yoneda.obj T₀ ⟶ X} {a₀ : Y₀ ⟶ W}
    {b₀ : Y₀ ⟶ T₀} (sq₀ : IsPullback (yoneda.map a₀) (yoneda.map b₀) f x₀)
    [LocallyOfFinitePresentation ((SCH).map b₀)]
    (w₁ : (SCH).obj (spObj W (ι1 W (M := M)) contains1)) (y₀ : (SCH).obj Y₀)
    (hy : (SCH).map a₀ y₀ = (SCH).map (spToT W (ι1 W (M := M)) contains1) w₁)
    (hw₁ : w₁ ∈ ((SCH).obj (spObj W (ι1 W (M := M)) contains1)).basicOpen
      (spSec W (ι1 W (M := M)) contains1 (coact actW g))) :
    ∃ U : ((SCH).obj Y₀).Opens, y₀ ∈ U ∧ Etale (U.ι ≫ (SCH).map b₀) := by
  let pw := spToT W (ι1 W (M := M)) contains1
  let pt := spToT T₀ (ι1 T₀ (M := M)) contains1
  let fs := pullback.fst a₀ pw
  let sn := pullback.snd a₀ pw
  have pb : IsPullback fs sn a₀ pw := IsPullback.of_hasPullback _ _
  let γ := ptOf sn
  let bQ : pullback a₀ pw ⟶ spObj T₀ (ι1 T₀ (M := M)) contains1 := lift1 (fs ≫ b₀) γ
  have hbQ : bQ ≫ pt = fs ≫ b₀ := lift1_toT _ _
  have hptb : ptOf bQ = γ := ptOf_lift1 _ _
  have hk : ∀ {Z : BigFppfOver B S hS} (m : Z ⟶ pullback a₀ pw), ptOf (m ≫ sn) = ptOf (m ≫ bQ) :=
    fun m => by rw [ptOf_comp m bQ, hptb]; exact ptOf_comp m sn
  -- the square over `T₀`
  have sqi : IsPullback fs bQ b₀ pt := by
    refine ⟨⟨hbQ.symm⟩, ⟨PullbackCone.IsLimit.mk _
      (fun s => pullback.lift s.fst (lift1 (s.fst ≫ a₀) (ptOf s.snd)) (lift1_toT _ _).symm) ?_ ?_ ?_⟩⟩
    · intro s; exact pullback.lift_fst _ _ _
    · intro s
      refine ext1 ?_ ?_
      · rw [Category.assoc, hbQ, ← Category.assoc, pullback.lift_fst]
        exact s.condition
      · rw [ptOf_comp, hptb, ← ptOf_comp, pullback.lift_snd, ptOf_lift1]
    · intro s m h1 h2
      refine pullback.hom_ext (h1.trans (pullback.lift_fst _ _ _).symm) ?_
      rw [pullback.lift_snd]
      refine ext1 ?_ ?_
      · rw [Category.assoc, ← pb.w, ← Category.assoc, h1, lift1_toT]
      · rw [ptOf_lift1, ← h2]; exact hk m
  -- the twisted point
  let x'' : yoneda.obj (spObj T₀ (ι1 T₀ (M := M)) contains1) ⟶ X :=
    yonedaEquiv.symm (actX.smul (univPt1 (U := T₀) (M := M)) (x₀.app (op _) pt))
  have hx'' : ∀ {Z : BigFppfOver B S hS} (t : Z ⟶ spObj T₀ (ι1 T₀ (M := M)) contains1),
      x''.app (op Z) t = actX.smul (ptOf t) (x₀.app (op Z) (t ≫ pt)) := by
    intro Z t
    have e1 : x''.app (op Z) t =
        X.map t.op (actX.smul (univPt1 (U := T₀) (M := M)) (x₀.app (op _) pt)) :=
      yonedaEquiv_symm_app_apply _ _ _
    have e2 : X.map t.op (x₀.app (op _) pt) = x₀.app (op Z) (t ≫ pt) :=
      (NatTrans.naturality_apply x₀ t.op pt).symm
    refine e1.trans ((actX.map_smul t.op _ _).trans ?_)
    rw [e2]
    rfl
  have hw0 : ∀ {Z : BigFppfOver B S hS} (u : Z ⟶ Y₀),
      f.app (op Z) (u ≫ a₀) = x₀.app (op Z) (u ≫ b₀) := by
    intro Z u
    have t := congrArg (fun φ => φ.app (op Z) u) sq₀.w
    exact t
  have uniq₀ : ∀ {Z : BigFppfOver B S hS} (m m' : Z ⟶ Y₀), m ≫ a₀ = m' ≫ a₀ → m ≫ b₀ = m' ≫ b₀ →
      m = m' := fun m m' h1 h2 => yoneda.map_injective (sq₀.hom_ext
    (by rw [← yoneda.map_comp, ← yoneda.map_comp, h1])
    (by rw [← yoneda.map_comp, ← yoneda.map_comp, h2]))
  have hact : ∀ {Z : BigFppfOver B S hS} (m : Z ⟶ pullback a₀ pw),
      m ≫ sn ≫ univMap actW = smulAt actW (ptOf (m ≫ sn)) (m ≫ fs ≫ a₀) := by
    intro Z m
    rw [pb.w]
    exact (smulAt_eq_comp actW (m ≫ sn ≫ pw) (ptOf (m ≫ sn)) (m ≫ sn)
      (Category.assoc _ _ _) rfl).symm
  -- the twisted square
  have sqii : IsPullback (yoneda.map (sn ≫ univMap actW)) (yoneda.map bQ) f x'' := by
    refine isPullback_of_unique hrep _ _ ?_ ?_ ?_
    · have h1 := hact (𝟙 _)
      simp only [Category.id_comp] at h1
      rw [h1, hx'', hptb]
      refine (hf (T := op _) γ (fs ≫ a₀)).trans ?_
      rw [hw0, hbQ]
      rfl
    · intro Z u t h
      rw [hx''] at h
      let u' := smulAt actW (invPt (ptOf t)) u
      have hu' : f.app (op Z) u' = x₀.app (op Z) (t ≫ pt) := by
        refine (hf (T := op Z) (invPt (ptOf t)) u).trans ?_
        rw [h]
        refine (actX.mul_smul _ _ _).symm.trans ?_
        exact (congrArg (fun k => actX.smul k _) (invPt_mul (ptOf t))).trans (actX.one_smul _)
      obtain ⟨y', hy1, hy2⟩ := exists_lift_of_square sq₀ u' (t ≫ pt) hu'
      refine ⟨pullback.lift y' (lift1 u' (ptOf t)) (by rw [hy1, lift1_toT]), ?_, ?_⟩
      · rw [← Category.assoc, pullback.lift_snd]
        refine Eq.trans (smulAt_eq_comp actW u' (ptOf t) _ (lift1_toT _ _) (ptOf_lift1 _ _)).symm ?_
        exact smulAt_smulAt_inv actW _ _
      · refine ext1 ?_ ?_
        · rw [Category.assoc, hbQ, ← Category.assoc, pullback.lift_fst, hy2]
        · rw [ptOf_comp, hptb, ← ptOf_comp, pullback.lift_snd, ptOf_lift1]
    · intro Z m m' h1 h2
      have h3 : ptOf (m ≫ sn) = ptOf (m' ≫ sn) := by
        rw [hk, hk, h2]
      have h4 : m ≫ fs ≫ a₀ = m' ≫ fs ≫ a₀ := by
        have e1 := hact m
        have e2 := hact m'
        rw [h1, e2, h3] at e1
        have := congrArg (smulAt actW (invPt (ptOf (m' ≫ sn)))) e1
        rwa [smulAt_inv_smulAt, smulAt_inv_smulAt, eq_comm] at this
      have h5 : m ≫ fs = m' ≫ fs := uniq₀ _ _ (by simpa only [Category.assoc] using h4) (by
        rw [Category.assoc, Category.assoc, ← hbQ, ← Category.assoc, h2, Category.assoc])
      refine pullback.hom_ext h5 (ext1 ?_ h3)
      rw [Category.assoc, Category.assoc, ← pb.w, ← Category.assoc, h5, Category.assoc]
  have hO := etale_of_isEtaleOn hg sqii
  obtain ⟨z, hz1, hz2⟩ := exists_pt_of_isPullback (pb.map (SCH)) y₀ w₁ hy
  have hzO : z ∈ (SCH).map (sn ≫ univMap actW) ⁻¹ᵁ ((SCH).obj W).basicOpen g := by
    change (SCH).map (sn ≫ univMap actW) z ∈ ((SCH).obj W).basicOpen g
    rw [Functor.map_comp, Scheme.Hom.comp_apply, show (SCH).map sn z = w₁ from hz2]
    change w₁ ∈ (SCH).map (univMap actW) ⁻¹ᵁ ((SCH).obj W).basicOpen g
    rw [Scheme.preimage_basicOpen]
    have := spSec_coact actW g
    change w₁ ∈ ((SCH).obj _).basicOpen (((SCH).map (univMap actW)).appTop.hom g)
    rw [← this]
    exact hw₁
  let σ : Γ((SCH).obj T₀, ⊤) ⟶ CommRingCat.of (R1 T₀ M) := CommRingCat.ofHom (ι1 T₀ (M := M))
  have hσ : (SCH).map pt = Spec.map σ ≫ ((SCH).obj T₀).isoSpec.inv := rfl
  have hflat : Flat (Spec.map σ) := by
    refine (HasRingHomProperty.Spec_iff (P := @Flat)).2 ?_
    exact (RingHom.flat_algebraMap_iff (R := RT T₀) (S := R1 T₀ M)).2 inferInstance
  have sq2 : IsPullback ((SCH).map fs) (((SCH).map bQ : _ ⟶ Spec (CommRingCat.of (R1 T₀ M))))
      ((SCH).map b₀ ≫ ((SCH).obj T₀).isoSpec.hom) (Spec.map σ) := by
    refine IsPullback.of_iso (sqi.map (SCH)) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ((SCH).obj T₀).isoSpec ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp
    · rw [hσ]
      simp only [Iso.refl_hom]
      have e : (Spec.map σ ≫ ((SCH).obj T₀).isoSpec.inv) ≫ ((SCH).obj T₀).isoSpec.hom = Spec.map σ := by
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      exact e.trans (Category.id_comp _).symm
  obtain ⟨U, hU, hUe⟩ := exists_open_etale_of_isPullback_Spec σ sq2 z _ hzO hO
  refine ⟨U, ?_, ?_⟩
  · rw [← show (SCH).map fs z = y₀ from hz1]; exact hU
  · rw [← Category.assoc] at hUe
    exact (MorphismProperty.cancel_right_of_respectsIso @Etale _ _).1 hUe

end Key

section Main

variable {M : Type u} [AddCommGroup M] [AddMonoid.FG M]

open ChartMain

/-- Points of an affine-free scheme and vanishing of global functions. -/
lemma mem_basicOpen_iff (Y : Scheme.{u}) (y : Y) (r : Γ(Y, ⊤)) :
    y ∈ Y.basicOpen r ↔ r ∉ (Y.toSpecΓ y).asIdeal := by
  rw [← Scheme.toSpecΓ_preimage_basicOpen]
  exact Iff.rfl

/-- A prime of `R'` as a point of the object `Spec R'`. -/
def ptSp {U : BigFppfOver B S hS} {R' : Type u} [CommRing R'] [IsAffine ((SCH).obj U)]
    (ρ : RT U →+* R') (hC : B.Contains (Spec (.of R'))) (q : PrimeSpectrum R') :
    (SCH).obj (spObj U ρ hC) := by
  change PrimeSpectrum R'
  exact q

/-- Membership in the `D(r)` of `Spec`, for `r` in the ring. -/
lemma mem_basicOpen_spSec {U : BigFppfOver B S hS} {R' : Type u} [CommRing R'] [IsAffine ((SCH).obj U)]
    (ρ : RT U →+* R') (hC : B.Contains (Spec (.of R'))) (q : PrimeSpectrum R') (r : R') :
    ptSp ρ hC q ∈ ((SCH).obj (spObj U ρ hC)).basicOpen (spSec U ρ hC r) ↔ r ∉ q.asIdeal := by
  have e : (Spec (.of R')).basicOpen ((Scheme.ΓSpecIso (.of R')).inv r) =
      PrimeSpectrum.basicOpen r := by
    simp
    rfl
  change q ∈ (Spec (.of R')).basicOpen ((Scheme.ΓSpecIso (.of R')).inv r) ↔ _
  rw [e]
  exact Iff.rfl

variable {actX : AAction (fppfO B S hS) M X} (actW : AAction (fppfO B S hS) M (yoneda.obj W))
  {f : yoneda.obj W ⟶ X}

/-- **§6**: the key step. If `D(g) → X` is étale and `c(g) ∉ q'`, then the contraction of `q'` to `A` lies in
some `D(h)` with `D(h) → X` étale. -/
theorem exists_isEtaleOn_of_coact [hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    (hX : IsAlgebraicSpace B S hS X) (hf : IsEquivariant actW actX f)
    (hfp : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u}) (SCH))) f)
    {g : Γ((SCH).obj W, ⊤)} (hg : IsEtaleOn f g) (q : PrimeSpectrum (R1 W M))
    (hq : coact actW g ∉ q.asIdeal) :
    ∃ h : Γ((SCH).obj W, ⊤), IsEtaleOn f h ∧ ι1 W h ∉ q.asIdeal := by
  have hrep : yoneda.relativelyRepresentable f := hX.diagonal_representable.of_diag f
  obtain ⟨V, v, hs, he⟩ := hX.exists_atlas
  let w₁ : (SCH).obj (spObj W (ι1 W (M := M)) contains1) := ptSp _ _ q
  have hw₁ := (mem_basicOpen_spSec (ι1 W (M := M)) contains1 q (coact actW g)).2 hq
  let w := (SCH).map (spToT W (ι1 W (M := M)) contains1) w₁
  have hmemw : ∀ h : Γ((SCH).obj W, ⊤), w ∈ ((SCH).obj W).basicOpen h ↔ ι1 W h ∉ q.asIdeal := by
    intro h
    rw [← mem_basicOpen_spSec (ι1 W (M := M)) contains1 q (ι1 W h), ← spToT_appTop]
    have e : (SCH).map (spToT W (ι1 W (M := M)) contains1) ⁻¹ᵁ ((SCH).obj W).basicOpen h =
        ((SCH).obj _).basicOpen (((SCH).map (spToT W (ι1 W (M := M)) contains1)).appTop h) :=
      Scheme.preimage_basicOpen _ _
    change _ ↔ w₁ ∈ ((SCH).obj _).basicOpen (((SCH).map (spToT W (ι1 W (M := M)) contains1)).appTop h)
    rw [← e]
    exact Iff.rfl
  -- the atlas
  let sqp := hs.rep.isPullback' f
  have hsurj : Surjective ((SCH).map (hs.rep.snd f)) := hs.property_snd f
  have hEa : Etale ((SCH).map (hs.rep.snd f)) := he.property f _ _ (hs.rep.isPullback f)
  obtain ⟨yp, hyp⟩ := hsurj.surj w
  let bb := hs.rep.fst' f
  obtain ⟨O, hO, hvO, -⟩ := exists_isAffineOpen_mem_and_subset
    (TopologicalSpace.Opens.mem_top ((SCH).map bb yp))
  have : IsAffine ((SCH).obj (openObj V O)) := hO
  let x₀ : yoneda.obj (openObj V O) ⟶ X := yoneda.map (openι V O) ≫ v
  have hx₀ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) x₀ := by
    refine MorphismProperty.comp_mem _ _ _ ?_ he
    refine (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ _).2 ?_
    change Etale O.ι
    infer_instance
  let Oy : ((SCH).obj (hs.rep.pullback f)).Opens := (SCH).map bb ⁻¹ᵁ O
  let Y₀ := openObj (hs.rep.pullback f) Oy
  let a₀ : Y₀ ⟶ W := openι _ Oy ≫ hs.rep.snd f
  have sqo := isPullback_open bb O
  let b₀ : Y₀ ⟶ openObj V O := openLift O (openι _ Oy ≫ bb) (by
    rintro _ ⟨x, rfl⟩
    rw [Functor.map_comp]
    exact x.2)
  have sq₀ : IsPullback (yoneda.map a₀) (yoneda.map b₀) f x₀ := by
    have := (sqo.flip.map yoneda).paste_horiz sqp.flip
    rwa [← yoneda.map_comp] at this
  let y₀ : (SCH).obj Y₀ := (⟨yp, hvO⟩ : Oy)
  have hy₀ : (SCH).map a₀ y₀ = (SCH).map (spToT W (ι1 W (M := M)) contains1) w₁ := hyp
  have hb₀ : LocallyOfFinitePresentation ((SCH).map b₀) := hfp.property x₀ _ _ sq₀
  obtain ⟨U, hyU, hUe⟩ := exists_open_etale_of_twist actW hrep hf hg sq₀ w₁ y₀ hy₀ hw₁
  have hEa₀ : Etale ((SCH).map a₀) := by
    change Etale ((SCH).map (_ ≫ _))
    rw [Functor.map_comp]
    have : Etale ((SCH).map (openι (hs.rep.pullback f) Oy)) := by
      change Etale Oy.ι
      infer_instance
    infer_instance
  let e : openObj Y₀ U ⟶ W := openι Y₀ U ≫ a₀
  have hι : Etale ((SCH).map (openι Y₀ U)) := by
    change Etale U.ι
    infer_instance
  have hee : Etale ((SCH).map e) := by
    change Etale ((SCH).map (_ ≫ _))
    rw [Functor.map_comp]
    infer_instance
  have hyE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) (yoneda.map e ≫ f) := by
    have ew : yoneda.map e ≫ f = yoneda.map (openι Y₀ U ≫ b₀) ≫ x₀ := by
      rw [show e = openι Y₀ U ≫ a₀ from rfl, yoneda.map_comp, yoneda.map_comp (openι Y₀ U) b₀,
        Category.assoc, Category.assoc]
      exact congrArg (yoneda.map (openι Y₀ U) ≫ ·) sq₀.w
    rw [ew]
    refine MorphismProperty.comp_mem _ _ _ ?_ hx₀
    refine (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ _).2 ?_
    change Etale ((SCH).map (_ ≫ _))
    rw [Functor.map_comp]
    exact hUe
  have hopen : IsOpen (Set.range ((SCH).map e)) := ((SCH).map e).isOpenMap.isOpen_range
  have hwr : w ∈ Set.range ((SCH).map e) := by
    refine ⟨(⟨y₀, hyU⟩ : U), ?_⟩
    exact hy₀
  obtain ⟨h, hle, hwh⟩ := (isAffineOpen_top ((SCH).obj W)).exists_basicOpen_le
    (V := ⟨_, hopen⟩) ⟨w, hwr⟩ trivial
  refine ⟨h, isEtaleOn_of_range hrep e hee hyE h hle, (hmemw h).1 hwh⟩

omit [AddMonoid.FG M] in
/-- Coefficients of an element of `I · A[M]` lie in `I`. -/
lemma coeff_mem_of_mem_map {A : Type*} [CommRing A] (I : Ideal A) {x : AddMonoidAlgebra A M}
    (hx : x ∈ I.map (AddMonoidAlgebra.singleZeroRingHom : A →+* AddMonoidAlgebra A M)) (d : M) : x.coeff d ∈ I := by
  classical
  let φ := AddMonoidAlgebra.mapRingHom M (Ideal.Quotient.mk I)
  have hle : I.map (AddMonoidAlgebra.singleZeroRingHom : A →+* AddMonoidAlgebra A M) ≤ RingHom.ker φ := by
    refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
    change φ (AddMonoidAlgebra.single 0 a) = 0
    have : Ideal.Quotient.mk I a = 0 := Ideal.Quotient.eq_zero_iff_mem.2 ha
    simp [φ, this]
  have h0 : φ x = 0 := hle hx
  have := congrArg (fun z => z.coeff d) h0
  simpa [φ, Ideal.Quotient.eq_zero_iff_mem] using this

/-- The homogeneous components are the coefficients of the coaction. -/
lemma decompose_eq_coeff [hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W)] [DecidableEq M] (a : Γ((SCH).obj W, ⊤)) (d : M) :
    letI := gradedRingOfAction actW
    ((decompose (homog actW) a d : homog actW d) : Γ((SCH).obj W, ⊤)) = (coact actW a).coeff d := by
  letI := gradedRingOfAction actW
  have key : ∀ (w : ⨁ d, homog actW d),
      (coact actW (DirectSum.coeAddMonoidHom (homog actW) w)).coeff d = (w d : RT W) := by
    intro w
    induction w using DirectSum.induction_on with
    | zero => simp
    | of e x =>
      rw [DirectSum.coeAddMonoidHom_of, show coact actW _ = _ from x.2]
      by_cases hed : e = d
      · subst hed; simp
      · simp [DirectSum.of_eq_of_ne, hed, Ne.symm hed]
    | add x y hx hy => simp [map_add, hx, hy]
  have := key (decompose (homog actW) a)
  rw [show DirectSum.coeAddMonoidHom (homog actW) (decompose (homog actW) a) = a from
    (decompose (homog actW)).symm_apply_apply a] at this
  exact this.symm

/-- **§6**: "`Ω`, the étale locus of `φ̃` on `W`, is open and `G`-stable", for `X` an algebraic space and
`φ̃ : W → X` equivariant and locally of finite presentation. -/
theorem etaleLocusStable [DecidableEq M] [hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    (hX : IsAlgebraicSpace B S hS X) (hf : IsEquivariant actW actX f)
    (hfp : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u}) (SCH))) f) :
    EtaleLocusStable actW f := by
  have hrep : yoneda.relativelyRepresentable f := hX.diagonal_representable.of_diag f
  let I : Ideal Γ((SCH).obj W, ⊤) := Ideal.span {g | IsEtaleOn f g}
  have hgen : ∀ g, IsEtaleOn f g → g ∈ I := fun g hg => Ideal.subset_span hg
  have hI : ∀ g ∈ I, IsEtaleOn f g := by
    intro g hg
    refine isEtaleOn_of_cover hrep g fun w hw => ?_
    by_contra hno
    push_neg at hno
    have hle : I ≤ (((SCH).obj W).toSpecΓ w).asIdeal := Ideal.span_le.2 fun h hh => by
      by_contra hn
      exact hno h ((mem_basicOpen_iff _ w h).2 hn) hh
    exact (mem_basicOpen_iff _ w g).1 hw (hle hg)
  refine ⟨I, ?_, hI, fun g hg => Ideal.le_radical (hgen g hg)⟩
  letI := gradedRingOfAction actW
  intro g hg
  have hrad : coact actW g ∈ (I.map (ι1 W (M := M))).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro q ⟨hq, hqp⟩
    by_contra hn
    obtain ⟨h, hh, hhq⟩ := exists_isEtaleOn_of_coact actW hX hf hfp (hI g hg) ⟨q, hqp⟩ hn
    exact hhq (hq (Ideal.mem_map_of_mem _ (hgen h hh)))
  obtain ⟨e, he⟩ := hrad
  refine ⟨e, fun d => ?_⟩
  rw [decompose_eq_coeff actW, map_pow]
  exact coeff_mem_of_mem_map I he d

end Main

end Site

end AlgMag.ChartEtale

#print axioms AlgMag.ChartEtale.etaleLocusStable
