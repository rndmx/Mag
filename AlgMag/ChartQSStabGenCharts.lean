/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartQSStabGenMain
import AlgMag.ChartQSStratGeneric
import AlgMag.ChartQSStab

/-!
# The generic stabilizer for quasi-separated `X`: the stabilizer is locally closed

For `p : V → D → X` with `D → X` an open immersion and `D` affine, the stabilizer of `p` is locally
closed in `D(M)_V`: on the open `{(h, v) : h p(v) ∈ D}` it is the equalizer of two maps to the affine `D`.
This is `exists_charts`: finitely many `D(f k)` cover that open, with `G k` cutting the stabilizer out of
`D(f k)`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgMag.StronglyFPR

universe u

namespace AlgMag.ChartQSStabGen

open AlgMag.ChartStratum AlgMag.ChartMain

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {M : Type u} [AddCommGroup M] [Countable M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- The ideal of a localization from generators of its contraction. -/
lemma kills_iff_gens {P L A : Type u} [CommRing P] [CommRing L] [CommRing A] (F : P) [Algebra P L]
    [IsLocalization.Away F L] (I : Ideal L) (Gs : Finset P)
    (hG : Ideal.span (Gs : Set P) = I.comap (algebraMap P L)) (ρ : L →+* A)
    (hu : IsUnit (ρ (algebraMap P L F))) :
    (∀ z ∈ I, ρ z = 0) ↔ ∀ x ∈ Gs, ρ (algebraMap P L x) = 0 := by
  constructor
  · intro h x hx
    refine h _ ?_
    have : x ∈ I.comap (algebraMap P L) := hG ▸ Ideal.subset_span hx
    exact this
  · intro h z hz
    obtain ⟨⟨y, s⟩, hy⟩ := IsLocalization.surj (Submonoid.powers F) z
    obtain ⟨n, hn⟩ := s.2
    have hy' : z * algebraMap P L (s : P) = algebraMap P L y := hy
    have hmem : y ∈ I.comap (algebraMap P L) := by
      change algebraMap P L y ∈ I
      rw [← hy']
      exact I.mul_mem_right _ hz
    rw [← hG] at hmem
    have hkill : ∀ w ∈ Ideal.span (Gs : Set P), ρ (algebraMap P L w) = 0 := by
      have : Ideal.span (Gs : Set P) ≤ RingHom.ker (ρ.comp (algebraMap P L)) :=
        Ideal.span_le.2 fun w hw => h w hw
      exact fun w hw => this hw
    have e := congrArg ρ hy'
    rw [map_mul, hkill y hmem, ← hn, map_pow, map_pow] at e
    exact (hu.pow n).mul_left_eq_zero.1 e

lemma mem_basicOpen_iff {T : Scheme.{u}} (τ : T) (r : Γ(T, ⊤)) :
    τ ∈ T.basicOpen r ↔ r ∉ (T.toSpecΓ τ).asIdeal := by
  rw [← Scheme.toSpecΓ_preimage_basicOpen]
  exact Iff.rfl

variable {V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]

/-- The universal translate of `p` on `D(M)_V`. -/
noncomputable def univA (act : AAction (fppfO B S hS) M X) (p : X.obj (op V)) :
    X.obj (op (specObj (B := B) (S := S) (hS := hS) M V)) :=
  act.smul (U := op (specObj (B := B) (S := S) (hS := hS) M V))
    (specPt (B := B) (S := S) (hS := hS) M V) (X.map (specPr M V).op p)

/-- The action in terms of the universal point. -/
lemma smul_eq_map_univ (act : AAction (fppfO B S hS) M X) (p : X.obj (op V)) {T : BigFppfOver B S hS}
    (t : T ⟶ V) (h : APt (fppfO B S hS) M (op T)) :
    X.map (specLift t h).op (univA act p) = act.smul h (X.map t.op p) := by
  have e1 : X.map (specLift t h).op (X.map (specPr M V).op p) = X.map t.op p := by
    rw [← Functor.map_comp_apply, ← op_comp, specLift_pr]
  rw [univA, act.map_smul, res_specLift, e1]

lemma specRing_C {T : BigFppfOver B S hS} (t : T ⟶ V) (h : APt (fppfO B S hS) M (op T))
    (r : Γ((SCH).obj V, ⊤)) :
    specRing t h (AddMonoidAlgebra.single 0 r) = ((SCH).map t).appTop.hom r := by
  rw [specRing_single]
  have : (show Γ((SCH).obj T, ⊤) from h (Multiplicative.ofAdd (0 : M))) = 1 := map_one h
  rw [this, mul_one]

/-- `Spec R[M]_F → Spec R[M]`. -/
noncomputable def locS (F : gRing M V) :
    Spec (.of (Localization.Away F)) ⟶ (SCH).obj (specObj (B := B) (S := S) (hS := hS) M V) :=
  Spec.map (CommRingCat.ofHom (algebraMap (gRing M V) (Localization.Away F)))

instance (F : gRing M V) : AlgebraicGeometry.IsOpenImmersion (locS (B := B) (S := S) (hS := hS) F) := by
  unfold locS
  exact IsOpenImmersion.of_isLocalization F

/-- `D(F)` in `D(M)_V`, as an object of the site. -/
noncomputable def locObj (F : gRing M V) : BigFppfOver B S hS :=
  Chart.immObj (specObj (B := B) (S := S) (hS := hS) M V) (locS (B := B) (S := S) (hS := hS) F)

/-- The inclusion of `D(F)`. -/
noncomputable def locι (F : gRing M V) : locObj (B := B) (S := S) (hS := hS) F ⟶ specObj M V :=
  Chart.immι (specObj (B := B) (S := S) (hS := hS) M V) (locS (B := B) (S := S) (hS := hS) F)

/-- **One chart**: where `F` is invertible, the stabilizer is cut out by finitely many functions, when
`a` lands in `D` on `D(F)`. -/
theorem exists_G_of_chart (act : AAction (fppfO B S hS) M X) [IsNoetherianRing (gRing M V)]
    {D : BigFppfOver B S hS} [IsAffine ((SCH).obj D)] (ξ : yoneda.obj D ⟶ X)
    (hinj : ∀ T, Function.Injective (ξ.app T)) (q : V ⟶ D) (F : gRing M V)
    (c : locObj (B := B) (S := S) (hS := hS) F ⟶ D)
    (hc : X.map (locι F).op (univA act (ξ.app (op V) q)) = ξ.app (op _) c) :
    ∃ Gs : Finset (gRing M V), ∀ (T : BigFppfOver B S hS) (t : T ⟶ V) (h : APt (fppfO B S hS) M (op T)),
      IsUnit (specRing t h F) →
        (act.smul h (X.map t.op (ξ.app (op V) q)) = X.map t.op (ξ.app (op V) q) ↔
          ∀ x ∈ Gs, specRing t h x = 0) := by
  classical
  let L := Localization.Away F
  let α : Γ((SCH).obj D, ⊤) →+* L :=
    (Scheme.ΓSpecIso (.of L)).hom.hom.comp ((SCH).map c).appTop.hom
  let β : Γ((SCH).obj D, ⊤) →+* L :=
    (algebraMap (gRing M V) L).comp
      ((algebraMap Γ((SCH).obj V, ⊤) (gRing M V)).comp ((SCH).map q).appTop.hom)
  let I : Ideal L := Ideal.span (Set.range fun b => α b - β b)
  obtain ⟨Gs, hGs⟩ := (IsNoetherian.noetherian (I.comap (algebraMap (gRing M V) L)) :
    (I.comap (algebraMap (gRing M V) L)).FG)
  refine ⟨Gs, fun T t h hu => ?_⟩
  let ρ : L →+* Γ((SCH).obj T, ⊤) := IsLocalization.Away.lift F hu
  have hρ : ∀ x, ρ (algebraMap (gRing M V) L x) = specRing t h x := fun x =>
    IsLocalization.Away.lift_eq F hu x
  let ν₀ : (SCH).obj T ⟶ Spec (.of L) := ((SCH).obj T).toSpecΓ ≫ Spec.map (CommRingCat.ofHom ρ)
  have hν₀ : ν₀ ≫ locS F = specLiftS t h := by
    have e : (CommRingCat.ofHom (algebraMap (gRing M V) L)) ≫ (CommRingCat.ofHom ρ) =
        CommRingCat.ofHom (specRing t h) := by
      refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
      exact hρ x
    change (((SCH).obj T).toSpecΓ ≫ Spec.map (CommRingCat.ofHom ρ)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (gRing M V) L)) = _
    rw [Category.assoc, ← Spec.map_comp, e]
    rfl
  let ν : T ⟶ locObj (B := B) (S := S) (hS := hS) F := overHom ν₀ (by
    change ν₀ ≫ locS F ≫ (specObj (B := B) (S := S) (hS := hS) M V).hom.hom = _
    rw [← Category.assoc, hν₀]
    exact congrArg (fun k => k.hom) (Over.w (specLift t h)))
  have hν : ν ≫ locι F = specLift t h := toScheme_map_injective (by
    rw [Functor.map_comp]
    exact hν₀)
  have νapp : ∀ y : L, ((SCH).map ν).appTop.hom ((Scheme.ΓSpecIso (.of L)).inv.hom y) = ρ y :=
    fun y => appTop_toSpec_comp ρ y
  have e1 : (act.smul h (X.map t.op (ξ.app (op V) q)) = X.map t.op (ξ.app (op V) q)) ↔
      ν ≫ c = t ≫ q := by
    have a1 : act.smul h (X.map t.op (ξ.app (op V) q)) = ξ.app (op T) (ν ≫ c) := by
      rw [← smul_eq_map_univ, ← hν, op_comp, Functor.map_comp_apply, hc]
      exact (NatTrans.naturality_apply ξ ν.op c).symm
    have a2 : X.map t.op (ξ.app (op V) q) = ξ.app (op T) (t ≫ q) :=
      (NatTrans.naturality_apply ξ t.op q).symm
    rw [a1, a2]
    exact (hinj _).eq_iff
  have e2 : (ν ≫ c = t ≫ q) ↔ ∀ b, ρ (α b - β b) = 0 := by
    have v1 : ∀ b, ((SCH).map (ν ≫ c)).appTop.hom b = ρ (α b) := fun b => by
      have hi : ∀ w, (Scheme.ΓSpecIso (.of L)).inv.hom ((Scheme.ΓSpecIso (.of L)).hom.hom w) = w :=
        fun w => by simpa using congrArg (fun k => k.hom w) (Scheme.ΓSpecIso (.of L)).hom_inv_id
      rw [← νapp, Functor.map_comp, Scheme.Hom.comp_appTop]
      change ((SCH).map ν).appTop.hom (((SCH).map c).appTop.hom b) =
        ((SCH).map ν).appTop.hom ((Scheme.ΓSpecIso (.of L)).inv.hom
          ((Scheme.ΓSpecIso (.of L)).hom.hom (((SCH).map c).appTop.hom b)))
      exact congrArg _ (hi _).symm
    have v2 : ∀ b, ((SCH).map (t ≫ q)).appTop.hom b = ρ (β b) := fun b => by
      rw [Functor.map_comp, Scheme.Hom.comp_appTop]
      change ((SCH).map t).appTop.hom (((SCH).map q).appTop.hom b) = _
      rw [← specRing_C t h, ← hρ]
      rfl
    constructor
    · intro e b
      have := congrArg (fun k => ((SCH).map k).appTop.hom b) e
      simp only [v1, v2] at this
      rw [map_sub, this, sub_self]
    · intro e
      refine site_hom_ext (toAffine_ext ?_)
      ext b
      change ((SCH).map (ν ≫ c)).appTop.hom b = ((SCH).map (t ≫ q)).appTop.hom b
      rw [v1, v2]
      have := e b
      rwa [map_sub, sub_eq_zero] at this
  have huρ : IsUnit (ρ (algebraMap (gRing M V) L F)) := by rw [hρ]; exact hu
  have e3 := kills_iff_gens F I Gs hGs ρ huρ
  have e4 : (∀ z ∈ I, ρ z = 0) ↔ ∀ b, ρ (α b - β b) = 0 := by
    constructor
    · exact fun h b => h _ (Ideal.subset_span ⟨b, rfl⟩)
    · intro h
      have : I ≤ RingHom.ker ρ := Ideal.span_le.2 (by
        rintro _ ⟨b, rfl⟩
        exact h b)
      exact fun z hz => this hz
  rw [e1, e2, ← e4, e3]
  simp only [hρ]

/-- **The stabilizer is locally closed.** -/
theorem exists_charts (act : AAction (fppfO B S hS) M X) [IsNoetherianRing (gRing M V)]
    {D : BigFppfOver B S hS} [IsAffine ((SCH).obj D)] (ξ : yoneda.obj D ⟶ X)
    (hξ : Space.IsOpenImmersion B S hS ξ) (q : V ⟶ D) :
    ∃ (ι : Type u) (_ : Fintype ι) (f : ι → gRing M V) (G : ι → Finset (gRing M V)),
      (∀ (T : BigFppfOver B S hS) (t : T ⟶ V) (h : APt (fppfO B S hS) M (op T)),
        act.smul h (X.map t.op (ξ.app (op V) q)) = X.map t.op (ξ.app (op V) q) →
          ∀ τ : (SCH).obj T, ∃ k, τ ∈ ((SCH).obj T).basicOpen (specRing t h (f k))) ∧
      (∀ (T : BigFppfOver B S hS) (t : T ⟶ V) (h : APt (fppfO B S hS) M (op T)) (k : ι),
        IsUnit (specRing t h (f k)) →
          (act.smul h (X.map t.op (ξ.app (op V) q)) = X.map t.op (ξ.app (op V) q) ↔
            ∀ x ∈ G k, specRing t h x = 0)) := by
  classical
  have hm : Mono ξ := Space.mono_of_isOpenImmersion B S hS ξ hξ
  have hinj : ∀ T, Function.Injective (ξ.app T) := fun T =>
    (CategoryTheory.mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 hm T)
  let a := univA act (ξ.app (op V) q)
  let ya : yoneda.obj (specObj (B := B) (S := S) (hS := hS) M V) ⟶ X := yonedaEquiv.symm a
  have hx : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}) (SCH))) ξ := hξ
  let Fo := hx.rep.pullback ya
  let j : Fo ⟶ specObj M V := hx.rep.snd ya
  let s : Fo ⟶ D := hx.rep.fst' ya
  have hj : AlgebraicGeometry.IsOpenImmersion ((SCH).map j) := hx.property_snd ya
  have hpb := hx.rep.isPullback' ya
  have hsq : yoneda.map s ≫ ξ = yoneda.map j ≫ ya := hpb.w
  have hnat : ∀ {W : BigFppfOver B S hS} (r : W ⟶ specObj M V), (yoneda.map r ≫ ya).app (op W) (𝟙 W) =
      X.map r.op a := fun r => by
    simp [ya, yonedaEquiv_symm_app_apply]
  -- the open is a finite union of `D(f k)`
  let P := gRing M V
  let Oc : Set (PrimeSpectrum P) := (Set.range ((SCH).map j))ᶜ
  have hOc : IsClosed Oc := isClosed_compl_iff.2 hj.base_open.isOpen_range
  obtain ⟨J, hJ⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal Oc).1 hOc
  obtain ⟨Js, hJs⟩ := (IsNoetherian.noetherian J : J.FG)
  have hO : ∀ x : PrimeSpectrum P, x ∈ Set.range ((SCH).map j) ↔ ∃ k : Js, (k : P) ∉ x.asIdeal := by
    intro x
    have e1 : x ∉ Oc ↔ x ∈ Set.range ((SCH).map j) := not_not
    rw [← e1, hJ, PrimeSpectrum.mem_zeroLocus, ← hJs]
    constructor
    · intro h
      by_contra hall
      push Not at hall
      refine h ?_
      exact Ideal.span_le.2 fun y hy => hall ⟨y, hy⟩
    · rintro ⟨k, hk⟩ h
      exact hk (h (Ideal.subset_span k.2))
  -- charts
  have hchart : ∀ k : Js, ∃ Gs : Finset (gRing M V), ∀ (T : BigFppfOver B S hS) (t : T ⟶ V)
      (h : APt (fppfO B S hS) M (op T)), IsUnit (specRing t h (k : P)) →
        (act.smul h (X.map t.op (ξ.app (op V) q)) = X.map t.op (ξ.app (op V) q) ↔
          ∀ x ∈ Gs, specRing t h x = 0) := by
    intro k
    have hr : Set.range ((SCH).map (locι (B := B) (S := S) (hS := hS) (k : P))) ⊆ Set.range ((SCH).map j) := by
      rintro _ ⟨y, rfl⟩
      refine (hO _).2 ⟨k, ?_⟩
      change (k : P) ∉ (PrimeSpectrum.comap (algebraMap P (Localization.Away (k : P))) y).asIdeal
      intro hk
      have hu : IsUnit (algebraMap P (Localization.Away (k : P)) (k : P)) :=
        IsLocalization.Away.algebraMap_isUnit _
      exact y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hk hu)
    let l₀ := AlgebraicGeometry.IsOpenImmersion.lift ((SCH).map j)
      ((SCH).map (locι (B := B) (S := S) (hS := hS) (k : P))) hr
    have hl₀ : l₀ ≫ (SCH).map j = (SCH).map (locι (B := B) (S := S) (hS := hS) (k : P)) :=
      AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _
    let l : locObj (B := B) (S := S) (hS := hS) (k : P) ⟶ Fo := overHom l₀ (by
      rw [← site_w j, ← Category.assoc, hl₀, site_w])
    have hl : l ≫ j = locι (k : P) := toScheme_map_injective (by rw [Functor.map_comp]; exact hl₀)
    refine exists_G_of_chart act ξ hinj q (k : P) (l ≫ s) ?_
    have h1 := congrArg (fun φ => φ.app (op _) l) hsq
    have h3 : ξ.app (op _) (l ≫ s) = ya.app (op _) (l ≫ j) := h1
    have h4 : ya.app (op _) (l ≫ j) = ya.app (op _) (locι (k : P)) := congrArg _ hl
    exact (h3.trans (h4.trans (yonedaEquiv_symm_app_apply a _ _))).symm
  choose G hG using hchart
  refine ⟨Js, inferInstance, fun k => (k : P), G, ?_, fun T t h k hu => hG k T t h hu⟩
  intro T t h hfix τ
  have hc : yoneda.map (t ≫ q) ≫ ξ = yoneda.map (specLift t h) ≫ ya := by
    apply yonedaEquiv.injective
    have e1 := hnat (specLift t h)
    simp only [yonedaEquiv_apply, FunctorToTypes.comp, yoneda_map_app, Category.comp_id] at e1 ⊢
    rw [e1, smul_eq_map_univ, hfix]
    exact NatTrans.naturality_apply ξ t.op q
  let l : T ⟶ Fo := hx.rep.lift' (t ≫ q) (specLift t h) hc
  have hl : l ≫ j = specLift t h := hx.rep.lift'_snd _ _ _
  have hm : (SCH).map (specLift t h) τ ∈ Set.range ((SCH).map j) := by
    refine ⟨(SCH).map l τ, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hl]
  obtain ⟨k, hk⟩ := (hO _).1 hm
  refine ⟨k, (mem_basicOpen_iff τ _).2 fun hin => hk hin⟩

end AlgMag.ChartQSStabGen
