/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.NotePtStab
import AlgMag.ChartEffectiveMain
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSeparated
import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable

/-!
# Existence of strongly-FPR atlases: Lemma 2.1 (2), (3)

Mayeux, *Existence of strongly-FPR atlases* (no journal version), Lemma 2.1.

* `AlgMag.NotePt.IsZFPRAt`: `f` is `Z`-FPR at `u`.
* `AlgMag.NotePt.isZFPR_iff_forall_at`: **Lemma 2.1 (2)**, `f` is `Z`-FPR iff it is `Z`-FPR at every point.
* `AlgMag.NotePt.isZFPRAt_iff`: **Lemma 2.1 (2)**, `f` is `Z`-FPR at `u` iff `Y_{f(u)} ⊆ Z` implies `Y_u ⊆ Z`.
* `AlgMag.NotePt.forall_isZFPRAt_iff`: **Lemma 2.1 (3)**.
* `AlgMag.NotePt.isClosed_badSet`: the locus where `U^Z → U ×_X X^Z` fails to be onto is closed in `U`.

The printed proof of (2) says "By (1), ... iff this holds at the point over `u`". When `u` is outside the image of
`U ×_X X^Z` this also needs that image closed, which the note obtains later from separatedness of `X`.
`AlgMag.NotePt.exists_fixLocus` supplies it directly: on an affine `W`, the fixed locus of `x ∈ X(W)` is the closed
subscheme cut out by the coefficients of the ideal of the stabilizer.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.NotePt

open AlgMag.StronglyFPR AlgMag.StronglyFPRNote AlgMag.StronglyFPRNote.SubgroupIdeal

noncomputable section

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- `x ∈ X^{D(L)}(T)`, as a structure so that the elaborator does not unfold it to a function. -/
structure Fx {L : Type u} [AddCommMonoid L] {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (act : AAction (fppfO B S hS) L F)
    {T : BigFppfOver B S hS} (x : F.obj (op T)) : Prop where
  mem : x ∈ (fixedPoints act).obj (op T)

lemma Fx.map {L : Type u} [AddCommMonoid L] {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {act : AAction (fppfO B S hS) L F}
    {T T' : BigFppfOver B S hS} {x : F.obj (op T)} (h : Fx act x) (r : T' ⟶ T) : Fx act (F.map r.op x) :=
  ⟨fun {_} s k => by
    have := h.mem (r.op ≫ s) k
    rwa [Functor.map_comp_apply] at this⟩

section FixLocus

variable {L : Type u} [AddCommGroup L] [Countable L] {W T : BigFppfOver B S hS}

lemma specRing_eq_zero_of_coeff (t : T ⟶ W) (k : APt (fppfO B S hS) L (op T)) (y : gRing L W)
    (h : ∀ n, ((SCH).map t).appTop.hom (y.coeff n) = 0) : specRing t k y = 0 := by
  rw [← AddMonoidAlgebra.sum_coeff_single y, Finsupp.sum, map_sum]
  refine Finset.sum_eq_zero fun n _ => ?_
  rw [specRing_single, h n, zero_mul]

lemma specRing_univ [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] (t : T ⟶ W) (y : gRing L W) :
    specRing (specPr L T ≫ t) (specPt L T) y = (Scheme.ΓSpecIso (.of (gRing L T))).inv.hom
      (baseMap ((SCH).map t).appTop.hom L y) := by
  have : specRing (specPr L T ≫ t) (specPt L T) = (Scheme.ΓSpecIso (.of (gRing L T))).inv.hom.comp
      (baseMap ((SCH).map t).appTop.hom L) := by
    refine AddMonoidAlgebra.ringHom_ext (fun r => ?_) (fun m => ?_)
    · rw [specRing_single]
      have h1 : (show Γ((SCH).obj (specObj L T), ⊤) from (specPt L T) (Multiplicative.ofAdd (0 : L))) = 1 :=
        map_one (specPt L T)
      rw [h1, mul_one, Functor.map_comp, Scheme.Hom.comp_appTop]
      change (specPrS L T).appTop.hom (((SCH).map t).appTop.hom r) =
        (Scheme.ΓSpecIso (.of (gRing L T))).inv.hom (baseMap ((SCH).map t).appTop.hom L (AddMonoidAlgebra.single 0 r))
      rw [baseMap_single]
      exact specPrS_appTop T _
    · rw [specRing_single, map_one, one_mul]
      change _ = (Scheme.ΓSpecIso (.of (gRing L T))).inv.hom
        (baseMap ((SCH).map t).appTop.hom L (AddMonoidAlgebra.single m 1))
      rw [baseMap_single, map_one]
      rfl
  exact congrArg (fun φ => φ y) this

/-- The fixed locus of `x ∈ X(W)`, `W` affine, under `D(M/Z)` is a closed subscheme of `W`. This is the input from the
separatedness of `X`, printed as [AM, Prop. 8.1, Thm. 6.8] in the proof of Lemma 2.3. -/
theorem exists_fixLocus [IsAffine ((BigFppfOver.toScheme B S hS).obj W)] (act : AAction (fppfO B S hS) L X)
    (hsep : Space.IsSeparatedOver B S hS X) (x : X.obj (op W)) :
    ∃ c : Ideal Γ((SCH).obj W, ⊤),
      (∀ {T : BigFppfOver B S hS} (t : T ⟶ W), (∀ r ∈ c, ((SCH).map t).appTop.hom r = 0) →
        Fx act (X.map t.op x)) ∧
      (∀ {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] (t : T ⟶ W),
        Fx act (X.map t.op x) → ∀ r ∈ c, ((SCH).map t).appTop.hom r = 0) := by
  obtain ⟨D⟩ := nonempty_stabIdeal act hsep x
  refine ⟨Ideal.span {r | ∃ y ∈ D.I, ∃ n, y.coeff n = r}, fun {T} t ht => ⟨?_⟩, fun {T} _ t hx => ?_⟩
  · intro T' s h
    have e : X.map s (X.map t.op x) = X.map (s.unop ≫ t).op x := by
      rw [op_comp, Functor.map_comp_apply]
      rfl
    rw [e]
    refine D.fix_of_kills (s.unop ≫ t) h fun y hy => specRing_eq_zero_of_coeff _ _ _ fun n => ?_
    rw [Functor.map_comp, Scheme.Hom.comp_appTop]
    change ((SCH).map s.unop).appTop.hom (((SCH).map t).appTop.hom _) = 0
    rw [ht _ (Ideal.subset_span ⟨y, hy, n, rfl⟩), map_zero]
  · have hle : Ideal.span {r | ∃ y ∈ D.I, ∃ n, y.coeff n = r} ≤ RingHom.ker ((SCH).map t).appTop.hom := by
      rw [Ideal.span_le]
      rintro _ ⟨y, hy, n, rfl⟩
      have h1 := hx.mem (specPr L T).op (specPt L T)
      have e : X.map (specPr L T).op (X.map t.op x) = X.map (specPr L T ≫ t).op x := by
        rw [op_comp, Functor.map_comp_apply]
      rw [e] at h1
      have h2 := D.kills (specPr L T ≫ t) (specPt L T) h1 hy
      rw [specRing_univ] at h2
      have h3 : baseMap ((SCH).map t).appTop.hom L y = 0 :=
        inv_injective_Γ (M := L) (U := T) (h2.trans (map_zero _).symm)
      have h4 := baseMap_coeff ((SCH).map t).appTop.hom y n
      rw [h3] at h4
      exact h4.symm
    exact fun r hr => hle hr

end FixLocus

section Points

variable [Countable M]

lemma fx_iff {act : AAction (fppfO B S hS) M X} (hsep : Space.IsSeparatedOver B S hS X) {V : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] (x : X.obj (op V)) (hV : IsField Γ((SCH).obj V, ⊤))
    (Z : AddSubgroup M) : Fx (quotientAction act Z) x ↔ stabY act x ≤ Z := by
  constructor
  · intro h
    have h' : x ∈ (fixedPoints (quotientAction act Z)).obj (op V) := h.mem
    exact (mem_fixed_iff hsep x hV Z).1 h'
  · intro h
    have h' : x ∈ (fixedPoints (quotientAction act Z)).obj (op V) := (mem_fixed_iff hsep x hV Z).2 h
    exact ⟨h'⟩

lemma value_apply {T : BigFppfOver B S hS} (r : Space.FieldValuedPoint B S hS (yoneda.obj T))
    (y : (SCH).obj r.siteObject) : (SCH).map r.value y = Space.schemePoint B S hS T r := by
  have hsub : Subsingleton ((SCH).obj r.siteObject) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of r.carrier)))
  exact congrArg (fun z => (SCH).map r.value z) (@Subsingleton.elim _ hsub y (IsLocalRing.closedPoint r.carrier))

variable {U : BigFppfOver B S hS}

/-- `Y_u`, for a point `u` of a scheme `U`. -/
abbrev Yu (actU : AAction (fppfO B S hS) M (yoneda.obj U)) (hsepU : Space.IsSeparatedOver B S hS (yoneda.obj U))
    (u : (SCH).obj U) : AddSubgroup M :=
  stabPt actU hsepU ((Space.pointsEquivScheme B S hS U).symm u)

/-- `Y_{f(u)}`, for a point `u` of a scheme `U` and `f : U → X`. -/
abbrev Yf (actX : AAction (fppfO B S hS) M X) (hsep : Space.IsSeparatedOver B S hS X) (f : yoneda.obj U ⟶ X)
    (u : (SCH).obj U) : AddSubgroup M :=
  stabPt actX hsep (Space.pointsMap B S hS _ f ((Space.pointsEquivScheme B S hS U).symm u))

lemma symm_schemePoint {T : BigFppfOver B S hS} (t : T ⟶ U) (r : Space.FieldValuedPoint B S hS (yoneda.obj T)) :
    (Space.pointsEquivScheme B S hS U).symm ((SCH).map t (Space.schemePoint B S hS T r)) =
      (Space.FieldValuedPoint.map B S hS _ (yoneda.map t) r).class B S hS _ := by
  rw [Equiv.symm_apply_eq]
  exact (Space.pointsToScheme_pointsMap_yoneda B S hS t (r.class B S hS _)).symm

variable {actU : AAction (fppfO B S hS) M (yoneda.obj U)} {actX : AAction (fppfO B S hS) M X}
  {f : yoneda.obj U ⟶ X} (hsepU : Space.IsSeparatedOver B S hS (yoneda.obj U))
  (hsep : Space.IsSeparatedOver B S hS X)

lemma Yu_eq {T : BigFppfOver B S hS} (t : T ⟶ U) (r : Space.FieldValuedPoint B S hS (yoneda.obj T)) :
    Yu actU hsepU ((SCH).map t (Space.schemePoint B S hS T r)) =
      stabY actU (V := r.siteObject) (show (yoneda.obj U).obj (op r.siteObject) from r.value ≫ t) := by
  rw [Yu, symm_schemePoint, stabPt_class]
  rfl

lemma Yf_eq {T : BigFppfOver B S hS} (t : T ⟶ U) (r : Space.FieldValuedPoint B S hS (yoneda.obj T)) :
    Yf actX hsep f ((SCH).map t (Space.schemePoint B S hS T r)) =
      stabY actX (V := r.siteObject) (f.app (op r.siteObject) (r.value ≫ t)) := by
  rw [Yf, symm_schemePoint, Space.pointsMap_class, stabPt_class]
  rfl

/-- A point of `U` over a field is in `U^Z` iff `Y_u ⊆ Z`. -/
lemma fixedU_iff {T : BigFppfOver B S hS} (t : T ⟶ U) (r : Space.FieldValuedPoint B S hS (yoneda.obj T))
    (Z : AddSubgroup M) :
    Fx (quotientAction actU Z) (T := r.siteObject) (show (yoneda.obj U).obj (op r.siteObject) from r.value ≫ t) ↔
      Yu actU hsepU ((SCH).map t (Space.schemePoint B S hS T r)) ≤ Z := by
  rw [Yu_eq]
  exact fx_iff hsepU _ (fvp_isField r) Z

/-- A point of `X` over a field is in `X^Z` iff `Y_x ⊆ Z`. -/
lemma fixedX_iff {T : BigFppfOver B S hS} (t : T ⟶ U) (r : Space.FieldValuedPoint B S hS (yoneda.obj T))
    (Z : AddSubgroup M) :
    Fx (quotientAction actX Z) (T := r.siteObject) (f.app (op r.siteObject) (r.value ≫ t)) ↔
      Yf actX hsep f ((SCH).map t (Space.schemePoint B S hS T r)) ≤ Z := by
  rw [Yf_eq]
  exact fx_iff hsep _ (fvp_isField r) Z

/-- `C_Z`, the points `u` with `K_Z ⊆ G_{f(u)}` and `K_Z ⊄ G_u`. -/
def badSet (actU : AAction (fppfO B S hS) M (yoneda.obj U)) (actX : AAction (fppfO B S hS) M X)
    (f : yoneda.obj U ⟶ X) (hsepU : Space.IsSeparatedOver B S hS (yoneda.obj U))
    (hsep : Space.IsSeparatedOver B S hS X) (Z : AddSubgroup M) : Set ((SCH).obj U) :=
  {v | Yf actX hsep f v ≤ Z ∧ ¬ Yu actU hsepU v ≤ Z}

/-- A morphism to `T` from a field point at `τ` has range `{τ}`: a point fixed on `Ω`. -/
lemma range_value_subset {T : BigFppfOver B S hS} (r : Space.FieldValuedPoint B S hS (yoneda.obj T))
    {A : Set ((SCH).obj T)} (h : Space.schemePoint B S hS T r ∈ A) : Set.range ((SCH).map r.value) ⊆ A := by
  rintro _ ⟨y, rfl⟩
  rw [value_apply]
  exact h

variable [AddGroup.FG M] (hf : IsEquivariant actU actX f)
  (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f)
  [IsSeparated (terminal.from ((BigFppfOver.toScheme B S hS).obj U))]

include hf he in
/-- Lemma 2.1 (1) with `Fx`. -/
lemma exists_clopen (Z : AddSubgroup M) {T : BigFppfOver B S hS} (t : T ⟶ U) (hx : Fx (quotientAction actX Z) (f.app (op T) t)) :
    ∃ Ω : ((SCH).obj T).Opens, IsClosed (Ω : Set ((SCH).obj T)) ∧ ∀ {T' : BigFppfOver B S hS} (s : T' ⟶ T),
      Fx (quotientAction actU Z) (T := T') (show (yoneda.obj U).obj (op T') from s ≫ t) ↔ Set.range ((SCH).map s) ⊆ Ω := by
  obtain ⟨Ω, hc, hΩ⟩ := lem21_1 hf he Z t hx.mem
  refine ⟨Ω, hc, fun {T'} s => ⟨fun h => (hΩ s).1 h.mem, fun h => ?_⟩⟩
  have h' : (show (yoneda.obj U).obj (op T') from s ≫ t) ∈ (fixedPoints (quotientAction actU Z)).obj (op T') :=
    (hΩ s).2 h
  exact ⟨h'⟩

omit [AddGroup.FG M] [IsSeparated (terminal.from ((BigFppfOver.toScheme B S hS).obj U))] [Countable M] in
lemma fx_f_comp {T T' : BigFppfOver B S hS} {L : Type u} [AddCommMonoid L] {a : AAction (fppfO B S hS) L X} {t : T ⟶ U} (hx : Fx a (f.app (op T) t)) (s : T' ⟶ T) :
    Fx a (f.app (op T') (s ≫ t)) := by
  have e : f.app (op T') (s ≫ t) = X.map s.op (f.app (op T) t) := NatTrans.naturality_apply f s.op t
  rw [e]
  exact hx.map s

lemma mem_zeroLocus_of_kills {W P : BigFppfOver B S hS} [IsAffine ((SCH).obj W)] [Nonempty ((SCH).obj P)]
    (c : Ideal Γ((SCH).obj W, ⊤)) (s : P ⟶ W) (hs : ∀ r ∈ c, ((SCH).map s).appTop.hom r = 0)
    (y : (SCH).obj P) : (SCH).map s y ∈ Set.range (Chart.closedι ((SCH).obj W) c) := by
  let iso := ((SCH).obj W).isoSpec
  have hbo : ∀ (b : Γ((SCH).obj W, ⊤)) (x : (SCH).obj W), x ∈ ((SCH).obj W).basicOpen b ↔
      b ∉ (show PrimeSpectrum Γ((SCH).obj W, ⊤) from iso.hom x).asIdeal := fun b x => by
    rw [← Scheme.toSpecΓ_preimage_basicOpen]
    rfl
  have hle : c ≤ (show PrimeSpectrum Γ((SCH).obj W, ⊤) from iso.hom ((SCH).map s y)).asIdeal := by
    intro r hr
    by_contra hn
    have h1 : (SCH).map s y ∈ ((SCH).obj W).basicOpen r := (hbo _ _).2 hn
    have h2 : y ∈ (SCH).map s ⁻¹ᵁ ((SCH).obj W).basicOpen r := h1
    rw [Scheme.preimage_basicOpen_top, hs r hr, Scheme.basicOpen_zero] at h2
    exact h2
  have hr : (show PrimeSpectrum Γ((SCH).obj W, ⊤) from iso.hom ((SCH).map s y)) ∈
      Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk c)) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    exact hle
  obtain ⟨p, hp⟩ := hr
  refine ⟨p, ?_⟩
  have e : iso.inv (iso.hom ((SCH).map s y)) = (SCH).map s y := by
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl
  rw [← e, ← (show _ = (iso.hom ((SCH).map s y)) from hp)]
  rfl

include hf he in
/-- `C_Z` is closed in `U`: locally on `U` it is the complement in the closed `U ×_X X^Z` of the open and closed
subscheme `U^Z` of Lemma 2.1 (1). -/
theorem isClosed_badSet (Z : AddSubgroup M) : IsClosed (badSet actU actX f hsepU hsep Z) := by
  have hc : Countable (M ⧸ Z) := inferInstance
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro v hv
  obtain ⟨A, hA, hvA, -⟩ := exists_isAffineOpen_mem_and_subset (x := v) (U := ⊤) trivial
  let W := openObj A
  let a : W ⟶ U := openJ A
  haveI : IsAffine ((SCH).obj W) := hA
  have hnat : ∀ {T : BigFppfOver B S hS} (t : T ⟶ W),
      X.map t.op (f.app (op W) a) = f.app (op T) (t ≫ a) := fun t =>
    (NatTrans.naturality_apply f t.op a).symm
  obtain ⟨c, h1, h2⟩ := exists_fixLocus (quotientAction actX Z) hsep (f.app (op W) a)
  let E := Chart.immObj W (Chart.closedι ((SCH).obj W) c)
  let e : E ⟶ W := Chart.immι W (Chart.closedι ((SCH).obj W) c)
  have hme : (SCH).map e = Chart.closedι ((SCH).obj W) c := rfl
  have hic : AlgebraicGeometry.IsClosedImmersion ((SCH).map e) :=
    inferInstanceAs (AlgebraicGeometry.IsClosedImmersion (Chart.closedι ((SCH).obj W) c))
  let t₀ : E ⟶ U := e ≫ a
  have hfix : Fx (quotientAction actX Z) (f.app (op E) t₀) := by
    rw [← hnat]
    exact h1 e fun r hr => ChartMain.closedι_appTop_of_mem c hr
  obtain ⟨Ω, -, hΩ⟩ := exists_clopen hf he Z t₀ hfix
  have hε : ∀ ε : (SCH).obj E, ε ∉ Ω ↔ (SCH).map t₀ ε ∈ badSet actU actX f hsepU hsep Z := by
    intro ε
    obtain ⟨r, rfl⟩ := Space.exists_fieldValuedPoint_schemePoint_eq B S hS E ε
    have hfx : Yf actX hsep f ((SCH).map t₀ (Space.schemePoint B S hS E r)) ≤ Z :=
      (fixedX_iff hsep t₀ r Z).1 (fx_f_comp hfix r.value)
    constructor
    · intro hn
      refine ⟨hfx, fun hu => hn ?_⟩
      have h3 := (hΩ r.value).1 ((fixedU_iff hsepU t₀ r Z).2 hu)
      exact h3 ⟨IsLocalRing.closedPoint r.carrier, value_apply r _⟩
    · rintro ⟨-, hu⟩ hm
      exact hu ((fixedU_iff hsepU t₀ r Z).1 ((hΩ r.value).2 (range_value_subset r hm)))
  let Cl : Set ((SCH).obj W) := (SCH).map e '' (Ω : Set ((SCH).obj E))ᶜ
  have hCl : IsClosed Cl := hic.isClosedEmbedding.isClosedMap _ Ω.isOpen.isClosed_compl
  have hw : ∀ w : (SCH).obj W, (SCH).map a w ∈ badSet actU actX f hsepU hsep Z → w ∈ Cl := by
    intro w hb
    obtain ⟨r, rfl⟩ := Space.exists_fieldValuedPoint_schemePoint_eq B S hS W w
    have hx0 : Fx (quotientAction actX Z) (f.app (op r.siteObject) (r.value ≫ a)) := (fixedX_iff hsep a r Z).2 hb.1
    rw [← hnat] at hx0
    haveI : Nonempty ((SCH).obj r.siteObject) := ⟨IsLocalRing.closedPoint r.carrier⟩
    have hk := h2 (T := r.siteObject) r.value hx0
    obtain ⟨ε, hε₀⟩ := mem_zeroLocus_of_kills (P := r.siteObject) c r.value hk (IsLocalRing.closedPoint r.carrier)
    have hε' : (SCH).map e ε = Space.schemePoint B S hS W r := hε₀
    refine ⟨ε, ?_, hε'⟩
    refine (hε ε).2 ?_
    have : (SCH).map t₀ ε = (SCH).map a (Space.schemePoint B S hS W r) := by
      change (SCH).map a ((SCH).map e ε) = _
      rw [hε']
    rw [this]
    exact hb
  have hw' : ∀ w ∈ Cl, (SCH).map a w ∈ badSet actU actX f hsepU hsep Z := by
    rintro _ ⟨ε, hn, rfl⟩
    have := (hε ε).1 hn
    rwa [Functor.map_comp, Scheme.Hom.comp_apply] at this
  have hrange : v ∈ Set.range ((SCH).map a) := by
    rw [range_openJ]; exact hvA
  obtain ⟨w₀, rfl⟩ := hrange
  have hop : IsOpenMap ((SCH).map a) := (Scheme.Opens.ι A).isOpenEmbedding.isOpenMap
  refine ⟨(SCH).map a '' Clᶜ, ?_, hop _ hCl.isOpen_compl, ⟨w₀, fun h => hv (hw' _ h), rfl⟩⟩
  rintro _ ⟨w, hwn, rfl⟩ hb
  exact hwn (hw w hb)

/-- **Lemma 2.1 (2)**: `f` is `Z`-FPR at `u`: `U^Z → U ×_X X^Z` is an isomorphism over a neighbourhood `W` of `u`. Since this
map is a monomorphism, this says that a `T`-point of `U ×_X X^Z` with image in `W` is a point of `U^Z`. -/
def IsZFPRAt (actU : AAction (fppfO B S hS) M (yoneda.obj U)) (actX : AAction (fppfO B S hS) M X)
    (f : yoneda.obj U ⟶ X) (Z : AddSubgroup M) (u : (SCH).obj U) : Prop :=
  ∃ W : ((SCH).obj U).Opens, u ∈ W ∧ ∀ {T : BigFppfOver B S hS} (t : T ⟶ U), Set.range ((SCH).map t) ⊆ W →
    Fx (quotientAction actX Z) (f.app (op T) t) →
      Fx (quotientAction actU Z) (T := T) (show (yoneda.obj U).obj (op T) from t)

include hf he in
/-- **Lemma 2.1 (2)**: `f` is `Z`-FPR iff it is `Z`-FPR at every point, by Lemma 2.1 (1), since a surjective open and
closed immersion is an isomorphism. -/
theorem isZFPR_iff_forall_at (Z : AddSubgroup M) :
    IsZFPR hf Z ↔ ∀ u, IsZFPRAt actU actX f Z u := by
  constructor
  · intro H u
    refine ⟨⊤, trivial, fun {T} t _ hx => ?_⟩
    exact ⟨(isFPR_iff (hf.comap (QuotientAddGroup.mk' Z))).1 H (op T) t hx.mem⟩
  · intro H
    refine (isFPR_iff (hf.comap (QuotientAddGroup.mk' Z))).2 fun T t hx => ?_
    obtain ⟨T⟩ := T
    have hx' : Fx (quotientAction actX Z) (f.app (op T) t) := ⟨hx⟩
    obtain ⟨Ω, -, hΩ⟩ := exists_clopen hf he Z (T := T) t hx'
    have hall : Set.range ((SCH).map (𝟙 T)) ⊆ Ω := by
      rintro _ ⟨τ, rfl⟩
      rw [(SCH).map_id]
      change τ ∈ Ω
      obtain ⟨W, huW, hW⟩ := H ((SCH).map t τ)
      let V : ((SCH).obj T).Opens := (SCH).map t ⁻¹ᵁ W
      let j : openObj V ⟶ T := openJ V
      have h1 : Set.range ((SCH).map (j ≫ t)) ⊆ W := by
        rintro _ ⟨y, rfl⟩
        rw [Functor.map_comp, Scheme.Hom.comp_apply]
        exact y.2
      have h3 := (hΩ j).1 (hW (j ≫ t) h1 (fx_f_comp hx' j))
      have hτ : τ ∈ V := huW
      exact h3 ⟨⟨τ, hτ⟩, rfl⟩
    have h5 := (hΩ (𝟙 T)).2 hall
    rw [show (show (yoneda.obj U).obj (op T) from 𝟙 T ≫ t) = t from Category.id_comp t] at h5
    obtain ⟨h6⟩ := h5
    exact @h6

include hf he in
/-- **Lemma 2.1 (2)**: `f` is `Z`-FPR at `u` iff `K_Z ⊆ G_{f(u)}` implies `K_Z ⊆ G_u`, that is, `Y_{f(u)} ⊆ Z` implies
`Y_u ⊆ Z`. The two forms are identified by `AlgMag.NotePt.mem_fixed_iff`. -/
theorem isZFPRAt_iff (Z : AddSubgroup M) (u : (SCH).obj U) :
    IsZFPRAt actU actX f Z u ↔ (Yf actX hsep f u ≤ Z → Yu actU hsepU u ≤ Z) := by
  constructor
  · rintro ⟨W, huW, hW⟩ hY
    obtain ⟨r, rfl⟩ := Space.exists_fieldValuedPoint_schemePoint_eq B S hS U u
    have e : (SCH).map (𝟙 U) (Space.schemePoint B S hS U r) = Space.schemePoint B S hS U r := by simp
    have h1 : Fx (quotientAction actX Z) (f.app (op r.siteObject) (r.value ≫ 𝟙 U)) :=
      (fixedX_iff (f := f) (actX := actX) hsep (𝟙 U) r Z).2 (by rw [e]; exact hY)
    rw [Category.comp_id] at h1
    have h2 := hW r.value (range_value_subset r huW) h1
    have h3 := (fixedU_iff (actU := actU) hsepU (𝟙 U) r Z).1 (by rw [Category.comp_id]; exact h2)
    rwa [e] at h3
  · intro h
    have hcl := isClosed_badSet hsepU hsep hf he Z
    refine ⟨⟨(badSet actU actX f hsepU hsep Z)ᶜ, hcl.isOpen_compl⟩, fun hb => hb.2 (h hb.1), fun {T} t hr hx => ?_⟩
    obtain ⟨Ω, -, hΩ⟩ := exists_clopen hf he Z t hx
    have hall : Set.range ((SCH).map (𝟙 T)) ⊆ Ω := by
      rintro _ ⟨τ, rfl⟩
      rw [(SCH).map_id]
      change τ ∈ Ω
      obtain ⟨q, rfl⟩ := Space.exists_fieldValuedPoint_schemePoint_eq B S hS T τ
      have h1 := (fixedX_iff (actX := actX) (f := f) hsep t q Z).1 (fx_f_comp hx q.value)
      have h2 : Yu actU hsepU ((SCH).map t (Space.schemePoint B S hS T q)) ≤ Z := by
        by_contra hn
        exact hr ⟨_, rfl⟩ ⟨h1, hn⟩
      have h3 := (hΩ q.value).1 ((fixedU_iff hsepU t q Z).2 h2)
      exact h3 ⟨IsLocalRing.closedPoint q.carrier, value_apply q _⟩
    have h5 := (hΩ (𝟙 T)).2 hall
    rwa [Category.id_comp] at h5

include hf in
/-- `G_u ⊆ G_{f(u)}` for a point of the scheme `U`. -/
lemma Yf_le_Yu (u : (SCH).obj U) : Yf actX hsep f u ≤ Yu actU hsepU u :=
  stabPt_map_le hf hsepU hsep _

include hf he in
/-- **Lemma 2.1 (3)**: `f` is `Z`-FPR at `u` for all subgroups `Z` iff `G_u = G_{f(u)}`, that is, `Y_u = Y_{f(u)}`. -/
theorem forall_isZFPRAt_iff (u : (SCH).obj U) :
    (∀ Z : AddSubgroup M, IsZFPRAt actU actX f Z u) ↔ Yu actU hsepU u = Yf actX hsep f u := by
  constructor
  · intro H
    exact le_antisymm ((isZFPRAt_iff hsepU hsep hf he _ u).1 (H _) le_rfl) (Yf_le_Yu hsepU hsep hf u)
  · intro h Z
    exact (isZFPRAt_iff hsepU hsep hf he Z u).2 fun hY => h ▸ hY

include hf hsepU hsep in
/-- **Lemma 2.1 (3)**, in terms of the stabilizers: on a field-valued point `s` of `U`, the groups `G_s` and `G_{f(s)}` have
the same points iff `Y` agree. -/
theorem stabilizers_eq_iff (r : Space.FieldValuedPoint B S hS (yoneda.obj U)) :
    (∀ {T : BigFppfOver B S hS} (t : T ⟶ r.siteObject) (k : APt (fppfO B S hS) M (op T)),
      actX.smul k (f.app (op T) (t ≫ r.value)) = f.app (op T) (t ≫ r.value) →
        actU.smul k (t ≫ r.value : T ⟶ U) = t ≫ r.value) ↔
      stabY actU (V := r.siteObject) (show (yoneda.obj U).obj (op r.siteObject) from r.value) =
        stabY actX (V := r.siteObject) (f.app (op r.siteObject) r.value) := by
  have hnat : ∀ {T : BigFppfOver B S hS} (t : T ⟶ r.siteObject),
      X.map t.op (f.app (op r.siteObject) r.value) = f.app (op T) (t ≫ r.value) := fun t =>
    (NatTrans.naturality_apply f t.op r.value).symm
  constructor
  · intro H
    refine le_antisymm ?_ (stabY_map_le hf (V := r.siteObject) _)
    intro m hm T t k hk
    rw [hnat] at hk
    exact hm t k (H t k hk)
  · intro h T t k hk
    refine (smul_eq_iff (act := actU) hsepU (V := r.siteObject) r.value (fvp_isField r) t k).2 ?_
    rw [h]
    refine fun m hm => hm t k ?_
    rw [hnat]
    exact hk

end Points

end

end AlgMag.NotePt

#print axioms AlgMag.NotePt.isClosed_badSet
#print axioms AlgMag.NotePt.isZFPR_iff_forall_at
#print axioms AlgMag.NotePt.isZFPRAt_iff
#print axioms AlgMag.NotePt.forall_isZFPRAt_iff
#print axioms AlgMag.NotePt.stabilizers_eq_iff
