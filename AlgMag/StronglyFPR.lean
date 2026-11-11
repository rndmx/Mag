/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.StronglyFPRStab

/-!
# Existence of strongly-FPR atlases

Mayeux, *Existence of strongly-FPR atlases*.

* `AlgMag.StronglyFPR.exists_good_basicOpen`: **Lemma 2.3**: a point outside the bad locus has a
  neighbourhood `D(b)` with `b` homogeneous, inside `Ω`.
* `AlgMag.StronglyFPR.StrongChart`, `AlgMag.StronglyFPR.exists_strongChart`: §2.4: the chart
  `U(x) = D(a)`.
* `AlgMag.StronglyFPR.thm11_ft`: **Theorem 1.1 (2)** for `S` affine of finite type over `ℤ`, `X` of
  finite type.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.StronglyFPR

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {M : Type u} [AddCommGroup M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

section Open

variable {U : BigFppfOver B S hS} {actU : AAction (fppfO B S hS) M (yoneda.obj U)}
  {V : ((BigFppfOver.toScheme B S hS).obj U).Opens}

lemma range_openJ : Set.range ((SCH).map (openJ V)) = V :=
  Scheme.Opens.range_ι V

lemma exists_act_lift (hst : IsStableOpen actU V) {T : BigFppfOver B S hS}
    (h : APt (fppfO B S hS) M (op T)) (t : T ⟶ openObj V) :
    ∃ s : T ⟶ openObj V, s ≫ openJ V = actU.smul h (t ≫ openJ V) := by
  refine exists_factor_open (openJ V) _ ?_
  rw [range_openJ]
  refine hst (t ≫ openJ V) h ?_
  rintro _ ⟨y, rfl⟩
  rw [Functor.map_comp, Scheme.Hom.comp_apply]
  exact ((SCH).map t y).2

lemma mono_openJ : Mono (openJ V) :=
  (SCH).mono_of_mono_map (IsOpenImmersion.mono _)

/-- The action of `D(M)` on a stable open. -/
noncomputable def openAct (hst : IsStableOpen actU V) :
    AAction (fppfO B S hS) M (yoneda.obj (openObj V)) where
  smul {T} h t := (exists_act_lift hst (T := unop T) h t).choose
  one_smul {T} t := by
    have := mono_openJ (V := V)
    refine (cancel_mono (openJ V)).mp ?_
    refine (exists_act_lift hst (T := unop T) 1 t).choose_spec.trans ?_
    exact actU.one_smul _
  mul_smul {T} g h t := by
    have := mono_openJ (V := V)
    refine (cancel_mono (openJ V)).mp ?_
    refine (exists_act_lift hst (T := unop T) (g * h) t).choose_spec.trans ?_
    refine Eq.trans (actU.mul_smul _ _ _) ?_
    refine Eq.trans ?_ (exists_act_lift hst (T := unop T) g _).choose_spec.symm
    exact congrArg _ (exists_act_lift hst (T := unop T) h t).choose_spec.symm
  map_smul {T T'} s h t := by
    have := mono_openJ (V := V)
    refine (cancel_mono (openJ V)).mp ?_
    change (s.unop ≫ (exists_act_lift hst (T := unop T) h t).choose) ≫ openJ V = _
    rw [Category.assoc, (exists_act_lift hst (T := unop T) h t).choose_spec]
    refine Eq.trans (actU.map_smul s h (t ≫ openJ V)) ?_
    refine Eq.trans ?_ (exists_act_lift hst (T := unop T') (APt.res s h) (s.unop ≫ t)).choose_spec.symm
    rw [Category.assoc]
    rfl

lemma openAct_spec (hst : IsStableOpen actU V) {T : BigFppfOver B S hS}
    (h : APt (fppfO B S hS) M (op T)) (t : T ⟶ openObj V) :
    ((openAct hst).smul h t : T ⟶ openObj V) ≫ openJ V = actU.smul h (t ≫ openJ V) :=
  (exists_act_lift hst (T := T) h t).choose_spec

lemma openJ_equivariant (hst : IsStableOpen actU V) :
    IsEquivariant (openAct hst) actU (yoneda.map (openJ V)) :=
  fun {_} h t => openAct_spec hst h t

end Open

/-- The chart of §2.4: an affine scheme with an equivariant étale morphism to `X`, along which all
stabilizers are preserved. -/
structure StrongChart (actX : AAction (fppfO B S hS) M X) (W : BigFppfOver B S hS) where
  /-- The action. -/
  act : AAction (fppfO B S hS) M (yoneda.obj W)
  /-- The morphism to `X`. -/
  g : yoneda.obj W ⟶ X
  equivariant : IsEquivariant act actX g
  etale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) g
  affine : IsAffine ((BigFppfOver.toScheme B S hS).obj W)
  stab : ∀ {T : BigFppfOver B S hS} (t : T ⟶ W) (k : APt (fppfO B S hS) M (op T)),
    actX.smul k (g.app (op T) t) = g.app (op T) t → act.smul k t = t

/-- Preservation of stabilizers gives `Z`-FPR for every `Z`: Lemma 2.1 (2), (3). -/
theorem StrongChart.isStronglyFPR {actX : AAction (fppfO B S hS) M X} {W : BigFppfOver B S hS}
    (c : StrongChart actX W) : IsStronglyFPR c.equivariant := by
  intro Z
  refine (isFPR_iff (IsEquivariant.comap c.equivariant (QuotientAddGroup.mk' Z))).mpr fun T t hfix T' s h => ?_
  have h1 := hfix s h
  rw [← NatTrans.naturality_apply] at h1
  exact c.stab (T := unop T') ((yoneda.obj W).map s t) _ h1

section Good

variable [Countable M] {U : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  {actU : AAction (fppfO B S hS) M (yoneda.obj U)} {actX : AAction (fppfO B S hS) M X}
  {f : yoneda.obj U ⟶ X}

/-- **Lemma 2.3.** A point `x₀` of `Ω` has a neighbourhood `D(b)`, with `b` homogeneous, in `Ω`. -/
theorem StabData.exists_good_basicOpen (D : StabData actU actX f) (hf : IsEquivariant actU actX f)
    [IsNoetherianRing Γ((SCH).obj U, ⊤)] [AddMonoid.FG M] {x₀ : (SCH).obj U} (hx₀ : x₀ ∉ D.bad) :
    ∃ (b : Γ((SCH).obj U, ⊤)) (m : M), rhoMap actU b = AddMonoidAlgebra.single m b ∧
      x₀ ∈ ((SCH).obj U).basicOpen b ∧ ∀ x ∈ ((SCH).obj U).basicOpen b, x ∉ D.bad := by
  obtain ⟨I, e, he, hI, hbad⟩ := D.exists_ideal
  let iso := ((SCH).obj U).isoSpec
  have hinj : Function.Injective iso.hom := (Scheme.homeoOfIso iso).injective
  have hmem : ∀ x, iso.hom x ∈ badImage I e ↔ x ∈ D.bad := fun x => by
    rw [← hbad]; exact hinj.mem_set_image
  have hbo : ∀ (b : Γ((SCH).obj U, ⊤)) (x : (SCH).obj U), x ∈ ((SCH).obj U).basicOpen b ↔
      b ∉ (show PrimeSpectrum Γ((SCH).obj U, ⊤) from iso.hom x).asIdeal := fun b x => by
    rw [← Scheme.toSpecΓ_preimage_basicOpen]
    rfl
  obtain ⟨a, m, h1, h2⟩ := exists_coeff_notMem (rhoMap actU) rhoMap_aug (isClosed_badImage he hI)
    (fun w hw => by
      have h3 : (SCH).map (specPr M U) w ∈ D.bad := by
        rw [← hmem]
        exact (map_specPr_apply w).symm ▸ hw
      have h4 := D.act_mem_bad hf w h3
      rw [← hmem] at h4
      exact (map_actMap_apply w) ▸ h4)
    (q₀ := iso.hom x₀) (fun h => hx₀ ((hmem _).mp h))
  refine ⟨_, m, rhoMap_coeff a m, (hbo _ _).mpr h1, fun x hx hxb => ?_⟩
  exact (hbo _ _).mp hx (h2 _ ((hmem x).mpr hxb))

/-- **§2.4.** From a stabilizer-preserving affine chart at a point with one-point source, the chart
`U(x) = D(a)`, with `a` homogeneous. -/
theorem exists_strongChart (hf : IsEquivariant actU actX f)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) f)
    (hsep : Space.IsSeparatedOver B S hS X)
    [IsNoetherianRing Γ((SCH).obj U, ⊤)] [AddMonoid.FG M]
    {P : BigFppfOver B S hS} [Subsingleton ((SCH).obj P)] [Nonempty ((SCH).obj P)] (u : P ⟶ U)
    (hst : ∀ {T : BigFppfOver B S hS} (s : T ⟶ P) (k : APt (fppfO B S hS) M (op T)),
      actX.smul k (f.app (op T) (s ≫ u)) = f.app (op T) (s ≫ u) → actU.smul k (s ≫ u) = s ≫ u) :
    ∃ (W : BigFppfOver B S hS) (c : StrongChart actX W) (u' : P ⟶ W),
      yoneda.map u' ≫ c.g = yoneda.map u ≫ f := by
  obtain ⟨D⟩ := nonempty_stabData hf he hsep
  obtain ⟨x⟩ := ‹Nonempty ((SCH).obj P)›
  obtain ⟨b, m, hb, hxb, hgood⟩ := D.exists_good_basicOpen hf (D.notMem_bad u hst x)
  let V := ((SCH).obj U).basicOpen b
  have hV : IsStableOpen actU V := isStableOpen_basicOpen hb
  let j := openJ V
  have hjm : Mono j := mono_openJ
  have hmap := Space.isMultiplicative_presheaf_etale B S hS
  refine ⟨openObj V, ⟨openAct hV, yoneda.map j ≫ f, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro T h t
    change f.app T (((openAct hV).smul h t : unop T ⟶ openObj V) ≫ j) = actX.smul h (f.app T (t ≫ j))
    rw [openAct_spec]
    exact hf h (t ≫ j)
  · refine MorphismProperty.comp_mem _ _ _ ?_ he
    exact (Space.presheaf_yoneda_map_iff B S hS inferInstance j).2 inferInstance
  · exact (isAffineOpen_top _).basicOpen b
  · intro T t k hfix
    refine (cancel_mono j).mp ?_
    rw [openAct_spec]
    refine D.smul_eq (t ≫ j) k hfix fun τ => hgood _ ?_
    rw [Functor.map_comp, Scheme.Hom.comp_apply]
    exact ((SCH).map t τ).2
  · obtain ⟨u', hu'⟩ := exists_factor_open j u (by
      rintro _ ⟨y, rfl⟩
      rw [Subsingleton.elim y x]
      rw [range_openJ]
      exact hxb)
    refine ⟨u', ?_⟩
    rw [← Category.assoc, ← yoneda.map_comp, hu']

end Good

/-- A scheme affine and of finite type over `ℤ` has a noetherian ring of functions. -/
lemma isNoetherianRing_of_lft {Y : Scheme.{u}} [IsAffine Y]
    (h : LocallyOfFiniteType (terminal.from Y)) : IsNoetherianRing Γ(Y, ⊤) := by
  let e := terminalIsoIsTerminal specULiftZIsTerminal.{u}
  let g : Y ⟶ Spec (.of (ULift.{u} ℤ)) := terminal.from Y ≫ e.hom
  have hg : LocallyOfFiniteType g := inferInstance
  have hft := (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp hg
  have hZ : IsNoetherianRing (ULift.{u} ℤ) := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  have hR : IsNoetherianRing Γ(Spec (.of (ULift.{u} ℤ)), ⊤) :=
    isNoetherianRing_of_ringEquiv (ULift.{u} ℤ) (Scheme.ΓSpecIso (.of (ULift.{u} ℤ))).symm.commRingCatIsoToRingEquiv
  letI := (g.appTop.hom).toAlgebra
  have hft' : Algebra.FiniteType Γ(Spec (.of (ULift.{u} ℤ)), ⊤) Γ(Y, ⊤) := hft
  exact Algebra.FiniteType.isNoetherianRing Γ(Spec (.of (ULift.{u} ℤ)), ⊤) Γ(Y, ⊤)

section FT

variable [IsAffine S] [AddGroup.FG M]

/-- The source of an étale chart of `X`, of finite type over `S` of finite type over `ℤ`. -/
lemma isNoetherianRing_chart {U : BigFppfOver B S hS} [IsAffine ((SCH).obj U)]
    (hSft : LocallyOfFiniteType (terminal.from S))
    (hft : Space.IsFiniteType B S hS (terminal.from X)) {f : yoneda.obj U ⟶ X}
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) f) :
    IsNoetherianRing Γ((SCH).obj U, ⊤) := by
  let V₀ : BigFppfOver B S hS := Over.mk (𝟙 _)
  have hV₀ : IsTerminal V₀ := Over.mkIdTerminal
  have hY : IsTerminal (yoneda.obj V₀) := hV₀.isTerminalObj yoneda
  have hiso : IsIso (terminal.from (yoneda.obj V₀)) := by
    refine ⟨hY.from _, hY.hom_ext _ _, terminal.hom_ext _ _⟩
  have hmap := Space.isMultiplicative_presheaf_etale B S hS
  have hb : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) (terminal.from (yoneda.obj V₀)) :=
    MorphismProperty.of_isIso _ _
  have h1 : LocallyOfFiniteType ((SCH).map (hV₀.from U)) :=
    hft.1 U V₀ f (terminal.from _) (hV₀.from U) he hb (terminal.hom_ext _ _)
  have h2 : LocallyOfFiniteType (terminal.from ((SCH).obj U)) := by
    have e : terminal.from ((SCH).obj U) = (SCH).map (hV₀.from U) ≫ terminal.from S :=
      terminal.hom_ext _ _
    rw [e]
    exact @MorphismProperty.comp_mem _ _ @LocallyOfFiniteType _ _ _ _ _ _ h1 hSft
  exact isNoetherianRing_of_lft h2

instance (p : ChartPoint X) : Subsingleton ((SCH).obj p.P) :=
  (Scheme.homeoOfIso p.iso).injective.subsingleton

instance (p : ChartPoint X) : Nonempty ((SCH).obj p.P) :=
  letI := p.field
  have hne : Nonempty (Spec (.of p.k)) := by
    have : Nontrivial (CommRingCat.of p.k) := inferInstanceAs (Nontrivial p.k)
    exact inferInstanceAs (Nonempty (PrimeSpectrum (CommRingCat.of p.k)))
  ⟨(Scheme.homeoOfIso p.iso).symm hne.some⟩

/-- **Theorem 1.1 (2) for `S` affine of finite type over `ℤ`, `X` of finite type** (§2.4), given the
AHR charts and density of closed points. The atlas is a single affine scheme. -/
theorem thm11_ft [HasFiniteCoproducts (BigFppfOver B S hS)]
    (hSft : LocallyOfFiniteType (terminal.from S)) (hX : IsAlgebraicSpace B S hS X)
    (hsep : Space.IsSeparatedOver B S hS X) (hft : Space.IsFiniteType B S hS (terminal.from X))
    (actX : AAction (fppfO B S hS) M X) (hchart : ChartLemmaStatement B S hS M)
    (hcov : ClosedPointsDetectCovers X) :
    ∃ (V : BigFppfOver B S hS) (actV : AAction (fppfO B S hS) M (yoneda.obj V))
      (v : yoneda.obj V ⟶ X), IsStronglyFPRAtlas actV actX v ∧ IsSAffineAtlas actV actX v ∧
        IsAffine ((SCH).obj V) := by
  have : Countable M := by
    have : Module.Finite ℤ M := Module.Finite.iff_addGroup_fg.mpr inferInstance
    obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' ℤ M
    exact hf.countable
  have hc : ∀ p : ChartPoint X, ∃ (W : BigFppfOver B S hS) (c : StrongChart actX W) (u' : p.P ⟶ W),
      yoneda.map u' ≫ c.g = p.x := by
    intro p
    obtain ⟨U, actU, f, u, h⟩ := hchart inferInstance hSft X hX hsep hft actX p
    have := h.affine
    have := isNoetherianRing_chart hSft hft h.etale
    obtain ⟨W, c, u', hu⟩ := exists_strongChart h.equivariant h.etale hsep u h.stabilizer
    exact ⟨W, c, u', hu.trans h.lies_over⟩
  choose W c u' hu using hc
  obtain ⟨n, a, hcv⟩ := hcov (ChartPoint X) W (fun p => (c p).g) (fun p => (c p).etale)
    (fun p => ⟨p, u' p, hu p⟩)
  let U : ULift.{u} (Fin n) → BigFppfOver B S hS := fun i => W (a i.down)
  let L : EtaleChartFamily actX (ULift.{u} (Fin n)) U :=
    { act := fun i => (c (a i.down)).act
      f := fun i => (c (a i.down)).g
      equivariant := fun i => (c _).equivariant
      etale := fun i => (c _).etale
      isAffineHom := fun i => by
        have := (c (a i.down)).affine
        exact isAffineHom_of_isAffine _
      covers := fun T x t => by
        obtain ⟨i, hi⟩ := hcv T x t
        exact ⟨⟨i⟩, hi⟩ }
  have : Finite (ULift.{u} (Fin n)) := inferInstance
  have : HasColimit (Discrete.functor U) := inferInstance
  let V := ∐ U
  let j : ∀ i, U i ⟶ V := Sigma.ι U
  have hV : IsColimit (Cofan.mk V j) :=
    (coproductIsCoproduct U).ofIsoColimit (Cocone.ext (Iso.refl _) (by
      rintro ⟨a⟩; simp [j]))
  obtain ⟨v, hv, hat⟩ := exists_atlas_of_family hX L hV
  have hdec := coprod_decomposition L.act hV L.isAffineHom
  have hfin : HasFiniteAffineDecomposition (coprodAction L.act hV) :=
    ⟨ULift.{u} (Fin n), inferInstance, _, hdec⟩
  refine ⟨V, _, v, ⟨hat, fun Z => isZFPR_coprod hV L hv hat.equivariant
    (fun i => (c (a i.down)).isStronglyFPR Z)⟩, ⟨hat, hfin⟩, ?_⟩
  have := (hasFiniteAffineDecomposition_iff _).mp hfin
  exact isAffine_of_isAffineHom (structMap V)

end FT

end AlgMag.StronglyFPR
