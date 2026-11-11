/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec9OverBBridge3Glue

/-!
# The geometric input of the compatible families: `geo`

Comparison of two charts over an affine, by the fibre product of the charts over `B`.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits

noncomputable section

namespace AlgMag.B3

open AlgMag.S9B AlgMag.S9 AlgebraicGeometry.Space

variable {Bs : BigFppfSite.{u}} {S : Scheme.{u}} {hS : Bs.Contains S}
  {Bsp : (BigFppfOver Bs S hS)ᵒᵖ ⥤ Type u}

/-- An étale chart as an object over `B`. -/
def cBs (Q : SmallEtale Bs S hS Bsp) : SB Bsp :=
  ⟨(SmallEtale.toOver Bs S hS Bsp).obj Q, yonedaEquiv Q.obj.hom⟩

/-- A morphism of étale charts as a morphism over `B`. -/
def cBsm {Q' Q : SmallEtale Bs S hS Bsp} (φ : Q' ⟶ Q) : cBs Q' ⟶ cBs Q :=
  ⟨(SmallEtale.toOver Bs S hS Bsp).map φ, by
    have := CostructuredArrow.w ((SmallEtale.inclusion Bs S hS Bsp).map φ)
    exact (yonedaEquiv_naturality _ _).trans (congrArg yonedaEquiv this)⟩

lemma cBsm_comp {Q'' Q' Q : SmallEtale Bs S hS Bsp} (a : Q'' ⟶ Q') (b : Q' ⟶ Q) :
    cBsm (a ≫ b) = cBsm a ≫ cBsm b :=
  SB.Hom.ext ((SmallEtale.toOver Bs S hS Bsp).map_comp _ _)

/-- A map over `B` from its underlying morphism of schemes, when both objects map to `Z`. -/
lemma exists_hom_of_left {X Y Z : SB Bsp} (si : Y ⟶ Z) (t : X ⟶ Z) (u : X.left ⟶ Y.left)
    (hu : u ≫ SB.Hom.left si = SB.Hom.left t) : ∃ l : X ⟶ Y, SB.Hom.left l = u ∧ l ≫ si = t := by
  have e : ObjectProperty.homMk u ≫ si.hom.left = t.hom.left := (Bs.inclusion).map_injective hu
  let lo : X.obj ⟶ Y.obj := Over.homMk (ObjectProperty.homMk u) (by
    have h1 := Over.w si.hom
    have h2 := Over.w t.hom
    change _ ≫ Y.obj.hom = X.obj.hom
    rw [← h1, ← Category.assoc, e, h2])
  have el : lo ≫ si.hom = t.hom := Over.OverMorphism.ext e
  refine ⟨⟨lo, ?_⟩, rfl, SB.Hom.ext el⟩
  have h3 : Bsp.map lo.op (Bsp.map si.hom.op Z.pt) = Bsp.map (lo ≫ si.hom).op Z.pt := by
    rw [op_comp, FunctorToTypes.map_comp_apply]
  rw [← si.w, h3, el, t.w]

theorem geo_opn {A' A Ai : SB Bsp} (s : A' ⟶ A) (si : Ai ⟶ A)
    (_ : IsOpenImmersion (SB.Hom.left si)) (x : A'.left)
    (hx : SB.Hom.left s x ∈ Set.range (SB.Hom.left si)) :
    ∃ (A'' : SB Bsp) (t : A'' ⟶ A') (l : A'' ⟶ Ai), IsAffine A''.left ∧
      IsOpenImmersion (SB.Hom.left t) ∧ x ∈ Set.range (SB.Hom.left t) ∧ l ≫ si = t ≫ s := by
  let O : A.left.Opens := (SB.Hom.left si).opensRange
  obtain ⟨U, hU, hxU, hle⟩ := exists_isAffineOpen_mem_and_subset (X := A'.left) (x := x)
    (U := SB.Hom.left s ⁻¹ᵁ O) hx
  haveI := Scheme.Opens.instIsOpenImmersionι U
  have hC : Bs.Contains (U : Scheme.{u}) :=
    (Scheme.size_le_of_isOpenImmersion U.ι).trans_lt A'.obj.left.property
  let A'' := A'.ofMap hC U.ι
  let t : A'' ⟶ A' := A'.ofMapι hC U.ι
  have htl : SB.Hom.left t = U.ι := rfl
  have hr : Set.range (U.ι ≫ SB.Hom.left s) ⊆ Set.range (SB.Hom.left si) := by
    rintro _ ⟨y, rfl⟩
    exact hle y.2
  let u : A''.left ⟶ Ai.left := IsOpenImmersion.lift (SB.Hom.left si) (U.ι ≫ SB.Hom.left s) hr
  obtain ⟨l, -, hl⟩ := exists_hom_of_left si (t ≫ s) u (by
    rw [SB.comp_left, htl]
    exact IsOpenImmersion.lift_fac _ _ _)
  refine ⟨A'', t, l, hU, ?_, ?_, hl⟩
  · rw [htl]; exact Scheme.Opens.instIsOpenImmersionι U
  · rw [htl]; exact ⟨⟨x, hxU⟩, rfl⟩

/-- Through a point of `C ⟶ Q`, an affine chart of `Q`. -/
theorem exists_affine_chart {C : SB Bsp} {Q : SmallEtale Bs S hS Bsp} (c : C ⟶ cBs Q) (x : C.left) :
    ∃ (A' : SB Bsp) (t : A' ⟶ C) (W : AffineEtale Bs S hS Bsp) (i : W.obj ⟶ Q) (w : A' ⟶ cB W),
      IsAffine A'.left ∧ IsOpenImmersion (SB.Hom.left t) ∧ x ∈ Set.range (SB.Hom.left t) ∧
        w ≫ cBsm i = t ≫ c := by
  obtain ⟨O, hO, hxO, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := (BigFppfOver.toScheme Bs S hS).obj ((SmallEtale.toOver Bs S hS Bsp).obj Q))
    (x := SB.Hom.left c x) (U := ⊤) trivial
  let W₀ := openChart Bs S hS Bsp Q O
  let i := openChartInclusion Bs S hS Bsp Q O
  have hl : SB.Hom.left (cBsm i) = O.ι := toScheme_map_toOver_map_openChartInclusion Bs S hS Bsp Q O
  let W : AffineEtale Bs S hS Bsp := ⟨W₀, hO⟩
  obtain ⟨A', t, l, hA', hop, hx, he⟩ := geo_opn c (cBsm i) (by rw [hl]; exact Scheme.Opens.instIsOpenImmersionι O) x
    (by rw [hl]; exact ⟨⟨_, hxO⟩, rfl⟩)
  exact ⟨A', t, W, i, l, hA', hop, hx, he⟩

/-- The fibre product over `B` of two étale charts, as an étale chart. -/
theorem exists_chart_product (Q₁ Q₂ : SmallEtale Bs S hS Bsp) :
    ∃ (P : SmallEtale Bs S hS Bsp) (p₁ : P ⟶ Q₁) (p₂ : P ⟶ Q₂),
      ∀ {C : SB Bsp} (c₁ : C ⟶ cBs Q₁) (c₂ : C ⟶ cBs Q₂),
        ∃ m : C ⟶ cBs P, m ≫ cBsm p₁ = c₁ ∧ m ≫ cBsm p₂ = c₂ ∧
          ∀ m' : C ⟶ cBs P, m' ≫ cBsm p₁ = c₁ → m' ≫ cBsm p₂ = c₂ → m' = m := by
  have hQ₂ := Q₂.property
  have hr := hQ₂.rep
  let P₀ : BigFppfOver Bs S hS := hr.pullback Q₁.obj.hom
  let a : P₀ ⟶ Q₂.obj.left := hr.fst' Q₁.obj.hom
  let b : P₀ ⟶ Q₁.obj.left := hr.snd Q₁.obj.hom
  have hpb := hr.isPullback' Q₁.obj.hom
  have hb : Etale ((BigFppfOver.toScheme Bs S hS).map b) :=
    hQ₂.property Q₁.obj.hom (hr.fst Q₁.obj.hom) (hr.snd Q₁.obj.hom) (hr.isPullback Q₁.obj.hom)
  let P : SmallEtale Bs S hS Bsp := ⟨CostructuredArrow.mk (yoneda.map b ≫ Q₁.obj.hom),
    etale_comp_of_scheme Bs S hS b Q₁.obj.hom hb Q₁.property⟩
  let p₁ : P ⟶ Q₁ := ObjectProperty.homMk (CostructuredArrow.homMk b rfl)
  let p₂ : P ⟶ Q₂ := ObjectProperty.homMk (CostructuredArrow.homMk a hpb.w)
  refine ⟨P, p₁, p₂, fun {C} c₁ c₂ => ?_⟩
  have hw : yoneda.map c₂.hom ≫ Q₂.obj.hom = yoneda.map c₁.hom ≫ Q₁.obj.hom := by
    apply yonedaEquiv.injective
    exact (yonedaEquiv_naturality _ _).symm.trans
      (c₂.w.trans (c₁.w.symm.trans (yonedaEquiv_naturality _ _)))
  let lift := hpb.lift (yoneda.map c₂.hom) (yoneda.map c₁.hom) hw
  let m₀ : C.obj ⟶ P₀ := Yoneda.fullyFaithful.preimage lift
  have hm₀ : yoneda.map m₀ = lift := Yoneda.fullyFaithful.map_preimage lift
  have ha : m₀ ≫ a = c₂.hom := yoneda.map_injective (by
    rw [Functor.map_comp, hm₀]; exact hpb.lift_fst _ _ hw)
  have hb' : m₀ ≫ b = c₁.hom := yoneda.map_injective (by
    rw [Functor.map_comp, hm₀]; exact hpb.lift_snd _ _ hw)
  have hpt : Bsp.map m₀.op (cBs P).pt = C.pt := by
    refine (yonedaEquiv_naturality (yoneda.map b ≫ Q₁.obj.hom) m₀).trans ?_
    have e : yoneda.map m₀ ≫ yoneda.map b ≫ Q₁.obj.hom = yoneda.map c₁.hom ≫ Q₁.obj.hom := by
      rw [← Category.assoc, ← Functor.map_comp, hb']; rfl
    exact (congrArg yonedaEquiv e).trans ((yonedaEquiv_naturality _ _).symm.trans c₁.w)
  refine ⟨⟨m₀, hpt⟩, SB.Hom.ext hb', SB.Hom.ext ha, fun m' h1 h2 => SB.Hom.ext ?_⟩
  apply yoneda.map_injective
  have h1' : m'.hom ≫ b = c₁.hom := congrArg SB.Hom.hom h1
  have h2' : m'.hom ≫ a = c₂.hom := congrArg SB.Hom.hom h2
  refine hpb.hom_ext ?_ ?_
  · exact (yoneda.map_comp m'.hom a).symm.trans
      ((congrArg yoneda.map (h2'.trans ha.symm)).trans (yoneda.map_comp m₀ a))
  · exact (yoneda.map_comp m'.hom b).symm.trans
      ((congrArg yoneda.map (h1'.trans hb'.symm)).trans (yoneda.map_comp m₀ b))

lemma aux4 {C : Type*} [Category C] {X X' Y Z Z' : C} {w : X ⟶ Y} {i : Y ⟶ Z} {p : Z ⟶ Z'}
    {t : X ⟶ X'} {m : X' ⟶ Z} {v : X' ⟶ Z'} (he : w ≫ i = t ≫ m) (hm : m ≫ p = v) :
    w ≫ i ≫ p = t ≫ v := by rw [← Category.assoc, he, Category.assoc, hm]

lemma aux6 {C : Type*} [Category C] {X P₀ Y Y' Z Z' : C} {i : X ⟶ P₀} {a : P₀ ⟶ Y} {b : P₀ ⟶ Y'}
    {k : Y ⟶ Z} {k' : Y' ⟶ Z} {p : Z ⟶ Z'} {f : Y ⟶ Z'} {f' : Y' ⟶ Z'} (hc : a ≫ k = b ≫ k')
    (hn : k ≫ p = f) (hn' : k' ≫ p = f') : (i ≫ a) ≫ f = (i ≫ b) ≫ f' := by
  subst hn hn'
  rw [Category.assoc, Category.assoc, ← Category.assoc a, hc, Category.assoc]

theorem geo_tst {A : SB Bsp} {V V₀ : AffineEtale Bs S hS Bsp} (v : A ⟶ cB V) (v₀ : A ⟶ cB V₀)
    (x : A.left) : ∃ (A' : SB Bsp) (t : A' ⟶ A), IsAffine A'.left ∧
      IsOpenImmersion (SB.Hom.left t) ∧ x ∈ Set.range (SB.Hom.left t) ∧
        Nonempty (Test (t ≫ v) (t ≫ v₀)) := by
  obtain ⟨P, p₁, p₂, hP⟩ := exists_chart_product V.obj V₀.obj
  obtain ⟨m, hm₁, hm₂, -⟩ := hP (C := A) v v₀
  obtain ⟨A', t, W, i, w, hA', hop, hx, he⟩ := exists_affine_chart m x
  refine ⟨A', t, hA', hop, hx, ⟨⟨W, ObjectProperty.homMk (i ≫ p₁), ObjectProperty.homMk (i ≫ p₂), w, ?_, ?_⟩⟩⟩
  · exact (congrArg (fun k : cBs W.obj ⟶ cBs V.obj => (w ≫ k : A' ⟶ cBs V.obj))
      (cBsm_comp i p₁)).trans (aux4 he hm₁)
  · exact (congrArg (fun k : cBs W.obj ⟶ cBs V₀.obj => (w ≫ k : A' ⟶ cBs V₀.obj))
      (cBsm_comp i p₂)).trans (aux4 he hm₂)

/-- A lift to a fibre product of charts: the inclusion in scheme charts creates fibre products. -/
theorem exists_lift_pullback {Q₁ Q₂ Q : SmallEtale Bs S hS Bsp} (a : Q₁ ⟶ Q) (b : Q₂ ⟶ Q)
    {C : SB Bsp} (c₁ : C ⟶ cBs Q₁) (c₂ : C ⟶ cBs Q₂) (h : c₁ ≫ cBsm a = c₂ ≫ cBsm b) :
    ∃ m : C ⟶ cBs (pullback a b), m ≫ cBsm (pullback.fst a b) = c₁ ∧
      m ≫ cBsm (pullback.snd a b) = c₂ := by
  let I := SmallEtale.inclusion Bs S hS Bsp
  have hpb : IsPullback (I.map (pullback.fst a b)) (I.map (pullback.snd a b)) (I.map a) (I.map b) :=
    (IsPullback.of_hasPullback a b).map I
  let C₀ : CostructuredArrow yoneda Bsp := CostructuredArrow.mk (yonedaEquiv.symm C.pt)
  let d : ∀ {Q : SmallEtale Bs S hS Bsp} (c : C ⟶ cBs Q), C₀ ⟶ I.obj Q := fun {Q} c =>
    CostructuredArrow.homMk c.hom (by
      apply yonedaEquiv.injective
      exact (yonedaEquiv_naturality _ _).symm.trans (c.w.trans (Equiv.apply_symm_apply _ _).symm))
  have hd : d c₁ ≫ I.map a = d c₂ ≫ I.map b := by
    apply CostructuredArrow.hom_ext
    exact congrArg SB.Hom.hom h
  let m₀ := hpb.lift (d c₁) (d c₂) hd
  have hpt : Bsp.map m₀.left.op (cBs (pullback a b)).pt = C.pt := by
    have := CostructuredArrow.w m₀
    have h2 := congrArg yonedaEquiv this
    exact (yonedaEquiv_naturality _ _).trans (h2.trans (Equiv.apply_symm_apply _ _))
  refine ⟨⟨m₀.left, hpt⟩, SB.Hom.ext ?_, SB.Hom.ext ?_⟩
  · exact congrArg CommaMorphism.left (hpb.lift_fst (d c₁) (d c₂) hd)
  · exact congrArg CommaMorphism.left (hpb.lift_snd (d c₁) (d c₂) hd)

theorem geo_ref {A : SB Bsp} {V V₀ : AffineEtale Bs S hS Bsp} {v : A ⟶ cB V} {v₀ : A ⟶ cB V₀}
    (τ τ' : Test v v₀) (x : A.left) : ∃ (A' : SB Bsp) (t : A' ⟶ A) (W : AffineEtale Bs S hS Bsp)
      (g : W ⟶ τ.W) (g' : W ⟶ τ'.W) (w : A' ⟶ cB W), IsAffine A'.left ∧
      IsOpenImmersion (SB.Hom.left t) ∧ x ∈ Set.range (SB.Hom.left t) ∧
      g ≫ τ.f = g' ≫ τ'.f ∧ g ≫ τ.f₀ = g' ≫ τ'.f₀ ∧ w ≫ cBm g = t ≫ τ.w ∧ w ≫ cBm g' = t ≫ τ'.w := by
  obtain ⟨P, p₁, p₂, hP⟩ := exists_chart_product V.obj V₀.obj
  obtain ⟨n, hn₁, hn₂, -⟩ := hP (C := cB τ.W) (cBm τ.f) (cBm τ.f₀)
  obtain ⟨n', hn₁', hn₂', -⟩ := hP (C := cB τ'.W) (cBm τ'.f) (cBm τ'.f₀)
  -- `n`, `n'` are morphisms of charts
  have mk : ∀ (U : AffineEtale Bs S hS Bsp) (n : cB U ⟶ cBs P), ∃ k : U.obj ⟶ P, cBsm k = n := by
    intro U n
    refine ⟨ObjectProperty.homMk (CostructuredArrow.homMk n.hom ?_), SB.Hom.ext rfl⟩
    apply yonedaEquiv.injective
    exact (yonedaEquiv_naturality _ _).symm.trans n.w
  obtain ⟨k, rfl⟩ := mk _ n
  obtain ⟨k', rfl⟩ := mk _ n'
  obtain ⟨c, hc₁, hc₂, hcu⟩ := hP (C := A) v v₀
  have h1 : τ.w ≫ cBsm k = c := hcu _
    ((Category.assoc _ _ _).trans ((congrArg (τ.w ≫ ·) hn₁).trans τ.h))
    ((Category.assoc _ _ _).trans ((congrArg (τ.w ≫ ·) hn₂).trans τ.h₀))
  have h2 : τ'.w ≫ cBsm k' = c := hcu _
    ((Category.assoc _ _ _).trans ((congrArg (τ'.w ≫ ·) hn₁').trans τ'.h))
    ((Category.assoc _ _ _).trans ((congrArg (τ'.w ≫ ·) hn₂').trans τ'.h₀))
  obtain ⟨m, hm, hm'⟩ := exists_lift_pullback k k' (C := A) τ.w τ'.w (h1.trans h2.symm)
  obtain ⟨A', t, W, i, w, hA', hop, hx, he⟩ := exists_affine_chart m x
  have hcond := congrArg cBsm (pullback.condition (f := k) (g := k'))
  rw [cBsm_comp, cBsm_comp] at hcond
  have cBm_inj : ∀ {U U' : AffineEtale Bs S hS Bsp} {a b : U ⟶ U'}, cBm a = cBm b → a = b := by
    intro U U' a b h
    have h' : (cBm a).hom = (cBm b).hom := congrArg SB.Hom.hom h
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact CostructuredArrow.hom_ext _ _ h'
  let g : W ⟶ τ.W := ObjectProperty.homMk (i ≫ pullback.fst k k')
  let g' : W ⟶ τ'.W := ObjectProperty.homMk (i ≫ pullback.snd k k')
  have hg : cBm g = cBsm i ≫ cBsm (pullback.fst k k') := cBsm_comp _ _
  have hg' : cBm g' = cBsm i ≫ cBsm (pullback.snd k k') := cBsm_comp _ _
  refine ⟨A', t, W, g, g', w, hA', hop, hx, cBm_inj ?_, cBm_inj ?_, ?_, ?_⟩
  · exact (cBm_comp _ _).trans ((congrArg (· ≫ cBm τ.f) hg).trans ((aux6 hcond hn₁ hn₁').trans
      ((congrArg (· ≫ cBm τ'.f) hg').symm.trans (cBm_comp _ _).symm)))
  · exact (cBm_comp _ _).trans ((congrArg (· ≫ cBm τ.f₀) hg).trans ((aux6 hcond hn₂ hn₂').trans
      ((congrArg (· ≫ cBm τ'.f₀) hg').symm.trans (cBm_comp _ _).symm)))
  · exact (congrArg (w ≫ ·) hg).trans (aux4 he hm)
  · exact (congrArg (w ≫ ·) hg').trans (aux4 he hm')

/-- **The geometric input.** -/
theorem geo : Geo Bsp := ⟨geo_opn, geo_tst, geo_ref⟩

/-- Stacks `QuasicoherentCartesianOnAffineCharts`, read in the form used here. -/
theorem cartesian_of_qc {hB : IsAlgebraicSpace Bs S hS Bsp} (𝓜 : Space.Modules.{u, u} Bs S hS Bsp hB)
    (h𝓜 : 𝓜.IsQuasicoherentOnSite) : Cartesian 𝓜 := by
  intro V' V φ
  have h := bijective_sectionsBaseChange_of_isQuasicoherentOnSite Bs S hS Bsp hB 𝓜 h𝓜
    V.property V'.property ((AffineEtale.inclusion Bs S hS Bsp).map φ)
  have h2 := (bijective_sectionsBaseChange_iff_isIso_restrictionBaseChange.{u, u} Bs S hS Bsp hB 𝓜
    ((AffineEtale.inclusion Bs S hS Bsp).map φ)).1 h
  have h3 := (ConcreteCategory.isIso_iff_bijective _).1 h2
  exact AlgMag.B2.isBC_of_cart (R := structurePresheaf Bs S hS Bsp) (Pm 𝓜)
    ((AffineEtale.inclusion Bs S hS Bsp).map φ).op h3

end AlgMag.B3

#print axioms AlgMag.B3.geo
#print axioms AlgMag.B3.cartesian_of_qc
