/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartQSStabGenCharts

/-!
# The generic stabilizer for quasi-separated `X`: from the charts to the ring statement

`fix_iff`: on an affine `T`, fixing `p` is `FixP`. `tests_of_charts`: the stabilizer is a subgroup functor,
in the sense of `Tests`. `generic_of_open_immersion` concludes.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgMag.StronglyFPR

universe u

namespace AlgMag.ChartQSStabGen

open AlgMag.ChartStratum AlgMag.ChartMain

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {M : Type u} [AddCommGroup M] [Countable M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- Points of an algebraic space are determined on a Zariski cover. -/
theorem eq_of_family (hX : IsAlgebraicSpace B S hS X) {W : BigFppfOver B S hS} {ι : Type u}
    (Z : ι → BigFppfOver B S hS) (e : ∀ i, Z i ⟶ W)
    (hf : ∀ i, AlgebraicGeometry.IsOpenImmersion ((SCH).map (e i)))
    (hcov : ∀ y : (SCH).obj W, ∃ i, y ∈ Set.range ((SCH).map (e i)))
    (p q : X.obj (op W)) (h : ∀ i, X.map (e i).op p = X.map (e i).op q) : p = q := by
  have hXsh : Presieve.IsSheaf (BigFppfOver.topology B S hS) X :=
    (isSheaf_iff_isSheaf_of_type _ _).1 hX.isSheaf
  have hc : Sieve.ofArrows Z e ∈ BigFppfOver.topology B S hS W :=
    BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS e hf hcov
  refine (hXsh _ hc).isSeparatedFor.ext ?_
  rintro Y' g ⟨Z', a, b, ⟨i⟩, rfl⟩
  rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply]
  exact congrArg (X.map a.op) (h i)

/-- `D(u)` in an affine object of the site. -/
noncomputable def affS {T : Scheme.{u}} [IsAffine T] (u : Γ(T, ⊤)) :
    Spec (.of (Localization.Away u)) ⟶ T :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(T, ⊤) (Localization.Away u))) ≫ T.isoSpec.inv

instance {T : Scheme.{u}} [IsAffine T] (u : Γ(T, ⊤)) : AlgebraicGeometry.IsOpenImmersion (affS u) := by
  unfold affS
  haveI : AlgebraicGeometry.IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(T, ⊤) (Localization.Away u)))) :=
    IsOpenImmersion.of_isLocalization u
  infer_instance

lemma affS_appTop {T : Scheme.{u}} [IsAffine T] (u y : Γ(T, ⊤)) :
    (affS u).appTop.hom y = (Scheme.ΓSpecIso (.of (Localization.Away u))).inv.hom (algebraMap _ _ y) := by
  have hk : T.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(T, ⊤)).inv := by
    have h := congrArg (fun k => k.appTop) (Scheme.toSpecΓ_isoSpec_inv T)
    simp only [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Scheme.Hom.id_appTop] at h
    exact (Iso.comp_hom_eq_id _).mp h
  have h3 := Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (algebraMap Γ(T, ⊤) (Localization.Away u)))
  have h5 := congrArg (fun k => k.hom y) h3
  have h6 : (affS u).appTop = (Scheme.ΓSpecIso Γ(T, ⊤)).inv ≫
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(T, ⊤) (Localization.Away u)))).appTop := by
    rw [affS, Scheme.Hom.comp_appTop, hk]
  rw [h6]
  exact h5.symm

/-- `D(u)` as an object of the site. -/
noncomputable def affObj (T : BigFppfOver B S hS) [IsAffine ((SCH).obj T)] (u : Γ((SCH).obj T, ⊤)) :
    BigFppfOver B S hS :=
  Chart.immObj T (affS u)

/-- The inclusion of `D(u)`. -/
noncomputable def affι (T : BigFppfOver B S hS) [IsAffine ((SCH).obj T)] (u : Γ((SCH).obj T, ⊤)) :
    affObj T u ⟶ T :=
  Chart.immι T (affS u)

lemma affι_open (T : BigFppfOver B S hS) [IsAffine ((SCH).obj T)] (u : Γ((SCH).obj T, ⊤)) :
    AlgebraicGeometry.IsOpenImmersion ((SCH).map (affι T u)) :=
  inferInstanceAs (AlgebraicGeometry.IsOpenImmersion (affS u))

lemma affι_isUnit (T : BigFppfOver B S hS) [IsAffine ((SCH).obj T)] (u : Γ((SCH).obj T, ⊤)) :
    IsUnit (((SCH).map (affι T u)).appTop.hom u) := by
  change IsUnit ((affS u).appTop.hom u)
  rw [affS_appTop]
  exact (IsLocalization.Away.algebraMap_isUnit u).map _

lemma affι_pow (T : BigFppfOver B S hS) [IsAffine ((SCH).obj T)] (u y : Γ((SCH).obj T, ⊤))
    (h : ((SCH).map (affι T u)).appTop.hom y = 0) : ∃ n : ℕ, u ^ n * y = 0 := by
  have h1 : (affS u).appTop.hom y = 0 := h
  rw [affS_appTop] at h1
  have h2 : algebraMap _ (Localization.Away u) y = 0 :=
    (Scheme.ΓSpecIso (.of (Localization.Away u))).commRingCatIsoToRingEquiv.symm.injective
      (h1.trans (map_zero _).symm)
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers u) _ y).1 h2
  exact ⟨n, hn⟩

lemma affι_range (T : BigFppfOver B S hS) [IsAffine ((SCH).obj T)] (u : Γ((SCH).obj T, ⊤))
    (τ : (SCH).obj T) (hτ : τ ∈ ((SCH).obj T).basicOpen u) : τ ∈ Set.range ((SCH).map (affι T u)) := by
  have hτ' := (ChartQSStabGen.mem_basicOpen_iff τ u).1 hτ
  have hr := PrimeSpectrum.localization_away_comap_range (Localization.Away u) u
  have : ((SCH).obj T).toSpecΓ τ ∈ Set.range
      (PrimeSpectrum.comap (algebraMap Γ((SCH).obj T, ⊤) (Localization.Away u))) := by
    rw [hr]
    exact hτ'
  obtain ⟨y, hy⟩ := this
  let y' : Spec (.of (Localization.Away u)) := y
  refine ⟨y', ?_⟩
  change ((SCH).obj T).isoSpec.inv
    ((Spec.map (CommRingCat.ofHom (algebraMap Γ((SCH).obj T, ⊤) (Localization.Away u)))) y') = τ
  have e : (Spec.map (CommRingCat.ofHom (algebraMap Γ((SCH).obj T, ⊤) (Localization.Away u)))) y' =
      ((SCH).obj T).isoSpec.hom τ := by
    rw [Scheme.isoSpec_hom]
    exact hy
  rw [e, ← Scheme.Hom.comp_apply, Iso.hom_inv_id]
  rfl

variable {V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  {ι : Type u} [Fintype ι] {f : ι → gRing M V} {G : ι → Finset (gRing M V)}

/-- The two chart properties of a point `p`. -/
structure ChartData (act : AAction (fppfO B S hS) M X) (p : X.obj (op V)) (f : ι → gRing M V)
    (G : ι → Finset (gRing M V)) : Prop where
  cover : ∀ (T : BigFppfOver B S hS) (t : T ⟶ V) (h : APt (fppfO B S hS) M (op T)),
    act.smul h (X.map t.op p) = X.map t.op p →
      ∀ τ : (SCH).obj T, ∃ k, τ ∈ ((SCH).obj T).basicOpen (specRing t h (f k))
  chart : ∀ (T : BigFppfOver B S hS) (t : T ⟶ V) (h : APt (fppfO B S hS) M (op T)) (k : ι),
    IsUnit (specRing t h (f k)) →
      (act.smul h (X.map t.op p) = X.map t.op p ↔ ∀ x ∈ G k, specRing t h x = 0)

/-- `FixP` is fixing `p`, on affine objects. -/
theorem fix_iff (hX : IsAlgebraicSpace B S hS X) {act : AAction (fppfO B S hS) M X} {p : X.obj (op V)}
    (hD : ChartData act p f G) {T : BigFppfOver B S hS} [IsAffine ((SCH).obj T)] (t : T ⟶ V)
    (h : APt (fppfO B S hS) M (op T)) :
    act.smul h (X.map t.op p) = X.map t.op p ↔ FixP f G ((SCH).map t).appTop.hom h := by
  classical
  have hres : ∀ {T' : BigFppfOver B S hS} (i : T' ⟶ T) (x : gRing M V),
      ((SCH).map i).appTop.hom (specRing t h x) = specRing (i ≫ t) (APt.res i.op h) x :=
    fun i x => appTop_specRing i t h x
  have hmap : ∀ {T' : BigFppfOver B S hS} (i : T' ⟶ T),
      X.map i.op (act.smul h (X.map t.op p)) =
        act.smul (APt.res i.op h) (X.map (i ≫ t).op p) := fun i => by
    rw [act.map_smul, op_comp, Functor.map_comp_apply]
  have hmap2 : ∀ {T' : BigFppfOver B S hS} (i : T' ⟶ T),
      X.map i.op (X.map t.op p) = X.map (i ≫ t).op p := fun i => by
    rw [op_comp, Functor.map_comp_apply]
  constructor
  · intro hfix
    refine ⟨?_, fun k x hx => ?_⟩
    · by_contra hne
      obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
      let τ : (SCH).obj T := ((SCH).obj T).isoSpec.inv ⟨m, hm.isPrime⟩
      obtain ⟨k, hk⟩ := hD.cover T t h hfix τ
      have e : ((SCH).obj T).toSpecΓ τ = ⟨m, hm.isPrime⟩ := by
        rw [← Scheme.isoSpec_hom]
        have e0 := Scheme.Hom.comp_apply ((SCH).obj T).isoSpec.inv ((SCH).obj T).isoSpec.hom ⟨m, hm.isPrime⟩
        rw [Iso.inv_hom_id] at e0
        exact e0.symm
      refine (ChartQSStabGen.mem_basicOpen_iff τ _).1 hk ?_
      rw [e]
      exact hle (Ideal.subset_span ⟨k, rfl⟩)
    · let u := specRing t h (f k)
      let i := affι T u
      have hu : IsUnit (specRing (i ≫ t) (APt.res i.op h) (f k)) := by
        rw [← hres]; exact affι_isUnit T u
      have hfix' : act.smul (APt.res i.op h) (X.map (i ≫ t).op p) = X.map (i ≫ t).op p := by
        rw [← hmap, hfix, hmap2]
      have := (hD.chart _ _ _ k hu).1 hfix' x hx
      rw [← hres] at this
      exact affι_pow T u _ this
  · intro hF
    refine eq_of_family hX (fun k => affObj T (specRing t h (f k)))
      (fun k => affι T (specRing t h (f k))) (fun k => affι_open T _) (fun τ => ?_) _ _ fun k => ?_
    · by_contra hne
      push Not at hne
      have hle : Ideal.span (Set.range fun k => ev ((SCH).map t).appTop.hom h (f k)) ≤
          (((SCH).obj T).toSpecΓ τ).asIdeal := Ideal.span_le.2 (by
        rintro _ ⟨k, rfl⟩
        by_contra hk
        exact hne k (affι_range T _ τ ((ChartQSStabGen.mem_basicOpen_iff τ _).2 hk)))
      rw [hF.1] at hle
      exact (((SCH).obj T).toSpecΓ τ).isPrime.ne_top (top_le_iff.1 hle)
    · let u := specRing t h (f k)
      let i := affι T u
      have hu : IsUnit (specRing (i ≫ t) (APt.res i.op h) (f k)) := by
        rw [← hres]; exact affι_isUnit T u
      have hfix : act.smul (APt.res i.op h) (X.map (i ≫ t).op p) = X.map (i ≫ t).op p := by
        refine (hD.chart _ _ _ k hu).2 fun x hx => ?_
        obtain ⟨n, hn⟩ := hF.2 k x hx
        have e := congrArg ((SCH).map i).appTop.hom hn
        rw [map_mul, map_pow, map_zero] at e
        have e' : ((SCH).map i).appTop.hom (specRing t h (f k)) ^ n *
            ((SCH).map i).appTop.hom (specRing t h x) = 0 := e
        rw [← hres]
        exact ((affι_isUnit T u).pow n).mul_right_eq_zero.1 e'
      change X.map i.op _ = X.map i.op _
      rw [hmap, hfix, hmap2]

omit [AddCommGroup M] [Countable M] in
lemma spec_imm {A B' C : Type u} [CommRing A] [CommRing B'] [CommRing C] (φ : A →+* B')
    (hφ : Function.Surjective φ) (ψ : B' →+* C)
    (hψ : AlgebraicGeometry.IsOpenImmersion (Spec.map (CommRingCat.ofHom ψ))) :
    AlgebraicGeometry.IsImmersion (Spec.map (CommRingCat.ofHom (ψ.comp φ))) := by
  have e : Spec.map (CommRingCat.ofHom (ψ.comp φ)) =
      Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [← Spec.map_comp]
    rfl
  rw [e]
  haveI : AlgebraicGeometry.IsClosedImmersion (Spec.map (CommRingCat.ofHom φ)) :=
    IsClosedImmersion.spec_of_surjective _ hφ
  infer_instance

/-- `Spec (S/a)_b → D(M × M)_V`. -/
noncomputable def lcS (a : Ideal (gRing (M × M) V)) (b : gRing (M × M) V) :
    Spec (.of (Lc a b)) ⟶ (SCH).obj (specObj (B := B) (S := S) (hS := hS) (M × M) V) :=
  Spec.map (CommRingCat.ofHom (lcMap a b))

instance (a : Ideal (gRing (M × M) V)) (b : gRing (M × M) V) :
    AlgebraicGeometry.IsImmersion (lcS (B := B) (S := S) (hS := hS) a b) :=
  spec_imm (Ideal.Quotient.mk a) Ideal.Quotient.mk_surjective (algebraMap (gRing (M × M) V ⧸ a) (Lc a b))
    (IsOpenImmersion.of_isLocalization (Ideal.Quotient.mk a b))

/-- The locally closed subscheme, as an object of the site. -/
noncomputable def lcObj (a : Ideal (gRing (M × M) V)) (b : gRing (M × M) V) : BigFppfOver B S hS :=
  Chart.immObj (specObj (B := B) (S := S) (hS := hS) (M × M) V) (lcS (B := B) (S := S) (hS := hS) a b)

instance (a : Ideal (gRing (M × M) V)) (b : gRing (M × M) V) :
    IsAffine ((SCH).obj (lcObj (B := B) (S := S) (hS := hS) a b)) :=
  inferInstanceAs (IsAffine (Spec _))

/-- The map to `V`. -/
noncomputable def lct (a : Ideal (gRing (M × M) V)) (b : gRing (M × M) V) :
    lcObj (B := B) (S := S) (hS := hS) a b ⟶ V :=
  Chart.immι (specObj (B := B) (S := S) (hS := hS) (M × M) V) (lcS (B := B) (S := S) (hS := hS) a b) ≫
    specPr (M × M) V

/-- Sections of the locally closed subscheme. -/
noncomputable def lcΦ (a : Ideal (gRing (M × M) V)) (b : gRing (M × M) V) :
    Lc a b →+* Γ((SCH).obj (lcObj (B := B) (S := S) (hS := hS) a b), ⊤) :=
  (Scheme.ΓSpecIso (.of (Lc a b))).inv.hom

/-- Inverse of `lcΦ`. -/
noncomputable def lcΨ (a : Ideal (gRing (M × M) V)) (b : gRing (M × M) V) :
    Γ((SCH).obj (lcObj (B := B) (S := S) (hS := hS) a b), ⊤) →+* Lc a b :=
  (Scheme.ΓSpecIso (.of (Lc a b))).hom.hom

lemma lcΨ_Φ (a : Ideal (gRing (M × M) V)) (b : gRing (M × M) V) :
    (lcΨ (B := B) (S := S) (hS := hS) a b).comp (lcΦ a b) = RingHom.id _ := by
  refine RingHom.ext fun y => ?_
  exact congrArg (fun k => k.hom y) (Scheme.ΓSpecIso (.of (Lc a b))).inv_hom_id

lemma lct_appTop (a : Ideal (gRing (M × M) V)) (b : gRing (M × M) V) (r : Γ((SCH).obj V, ⊤)) :
    ((SCH).map (lct (B := B) (S := S) (hS := hS) a b)).appTop.hom r =
      (lcS (B := B) (S := S) (hS := hS) a b).appTop.hom
        ((Scheme.ΓSpecIso (.of (gRing (M × M) V))).inv.hom (AddMonoidAlgebra.single 0 r)) := by
  have e : (SCH).map (lct (B := B) (S := S) (hS := hS) a b) =
      lcS (B := B) (S := S) (hS := hS) a b ≫ specPrS (B := B) (S := S) (hS := hS) (M × M) V := rfl
  have e2 : ∀ {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (r : Γ(C, ⊤)),
      (f ≫ g).appTop.hom r = f.appTop.hom (g.appTop.hom r) := fun f g r => by
    rw [Scheme.Hom.comp_appTop]; rfl
  exact (congrArg (fun k => k.appTop.hom r) e).trans ((e2 _ _ r).trans
    (congrArg _ (specPrS_appTop (B := B) (S := S) (hS := hS) (P := M × M) V r)))

lemma lcS_inv (a : Ideal (gRing (M × M) V)) (b : gRing (M × M) V) (x : gRing (M × M) V) :
    (lcS (B := B) (S := S) (hS := hS) a b).appTop.hom ((Scheme.ΓSpecIso (.of (gRing (M × M) V))).inv.hom x) =
      lcΦ (B := B) (S := S) (hS := hS) a b (lcMap a b x) :=
  (congrArg (fun k => k.hom x) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (lcMap a b)))).symm

lemma lcΦ_cS (a : Ideal (gRing (M × M) V)) (b : gRing (M × M) V) (r : Γ((SCH).obj V, ⊤)) :
    lcΦ (B := B) (S := S) (hS := hS) a b (lcMap a b (AddMonoidAlgebra.single 0 r)) =
      ((SCH).map (lct a b)).appTop.hom r := by
  rw [lct_appTop, lcS_inv]

/-- A character on the locally closed subscheme. -/
noncomputable def lcH (a : Ideal (gRing (M × M) V)) (b : gRing (M × M) V)
    (χ : Multiplicative M →* gRing (M × M) V) :
    APt (fppfO B S hS) M (op (lcObj (B := B) (S := S) (hS := hS) a b)) :=
  (rm (lcΦ (B := B) (S := S) (hS := hS) a b)).comp ((rm (lcMap a b)).comp χ)

variable {act : AAction (fppfO B S hS) M X} {p : X.obj (op V)}

lemma fix_lc_iff (hX : IsAlgebraicSpace B S hS X) (hD : ChartData act p f G)
    (a : Ideal (gRing (M × M) V)) (b : gRing (M × M) V) (χ : Multiplicative M →* gRing (M × M) V) :
    FixP f G ((lcMap a b).comp cS) ((rm (lcMap a b)).comp χ) ↔
      act.smul (lcH a b χ) (X.map (lct a b).op p) = X.map (lct a b).op p := by
  have e0 : ((SCH).map (lct (B := B) (S := S) (hS := hS) a b)).appTop.hom =
      (lcΦ (B := B) (S := S) (hS := hS) a b).comp ((lcMap a b).comp (cS (R := Γ((SCH).obj V, ⊤)) (M := M))) :=
    RingHom.ext fun r => (lcΦ_cS a b r).symm
  rw [fix_iff hX hD (lct a b) (lcH a b χ), e0]
  constructor
  · intro h
    exact h.map (lcΦ a b)
  · intro h
    have := h.map (lcΨ (B := B) (S := S) (hS := hS) a b)
    have e1 : (lcΨ (B := B) (S := S) (hS := hS) a b).comp ((lcΦ a b).comp
        ((lcMap a b).comp (cS (R := Γ((SCH).obj V, ⊤)) (M := M)))) = (lcMap a b).comp cS := by
      rw [← RingHom.comp_assoc, lcΨ_Φ, RingHom.id_comp]
    have e2 : (rm (lcΨ (B := B) (S := S) (hS := hS) a b)).comp (lcH a b χ) = (rm (lcMap a b)).comp χ := by
      refine MonoidHom.ext fun m => ?_
      exact congrArg (fun k => k ((lcMap a b) (χ m))) (lcΨ_Φ (B := B) (S := S) (hS := hS) a b)
    rw [e1, e2] at this
    exact this

lemma lc_val (a : Ideal (gRing (M × M) V)) (b : gRing (M × M) V)
    (χ : Multiplicative M →* gRing (M × M) V) (x : gRing M V) :
    specRing (lct (B := B) (S := S) (hS := hS) a b) (lcH a b χ) x =
      lcΦ a b (ev ((lcMap a b).comp cS) ((rm (lcMap a b)).comp χ) x) := by
  have e0 : ((SCH).map (lct (B := B) (S := S) (hS := hS) a b)).appTop.hom =
      (lcΦ (B := B) (S := S) (hS := hS) a b).comp ((lcMap a b).comp (cS (R := Γ((SCH).obj V, ⊤)) (M := M))) :=
    RingHom.ext fun r => (lcΦ_cS a b r).symm
  rw [map_ev, ← e0]
  rfl

/-- **The stabilizer is a subgroup functor.** -/
theorem tests_of_charts (hX : IsAlgebraicSpace B S hS X) (hD : ChartData act p f G) :
    Tests (R := Γ((SCH).obj V, ⊤)) (M := M) f G where
  hone := by
    have h1 := (fix_iff hX hD (𝟙 V) (1 : APt (fppfO B S hS) M (op V))).1 (act.one_smul _)
    have e : ((SCH).map (𝟙 V)).appTop.hom = RingHom.id _ := by simp
    rw [e] at h1
    exact h1
  hs := fun a b χ i hu hG => by
    refine (fix_lc_iff hX hD a b χ).2 ((hD.chart _ _ _ i ?_).2 fun x hx => ?_)
    · rw [lc_val]; exact hu.map _
    · rw [lc_val, hG x hx, map_zero]
  hmul := fun a b χ₁ χ₂ h₁ h₂ => by
    have e₁ := (fix_lc_iff hX hD a b χ₁).1 h₁
    have e₂ := (fix_lc_iff hX hD a b χ₂).1 h₂
    refine (fix_lc_iff hX hD a b (χ₁ * χ₂)).2 ?_
    have e : lcH (B := B) (S := S) (hS := hS) a b (χ₁ * χ₂) = lcH a b χ₁ * lcH a b χ₂ := by
      refine MonoidHom.ext fun m => ?_
      change lcΦ a b (lcMap a b (χ₁ m * χ₂ m)) = lcΦ a b (lcMap a b (χ₁ m)) * lcΦ a b (lcMap a b (χ₂ m))
      rw [map_mul, map_mul]
    rw [e, act.mul_smul, e₂, e₁]
  hdiv := fun a b χ₁ χ₂ h₂ h₁₂ => by
    have e₂ := (fix_lc_iff hX hD a b χ₂).1 h₂
    have e₁₂ := (fix_lc_iff hX hD a b (χ₁ * χ₂)).1 h₁₂
    refine (fix_lc_iff hX hD a b χ₁).2 ?_
    have e : lcH (B := B) (S := S) (hS := hS) a b (χ₁ * χ₂) = lcH a b χ₁ * lcH a b χ₂ := by
      refine MonoidHom.ext fun m => ?_
      change lcΦ a b (lcMap a b (χ₁ m * χ₂ m)) = lcΦ a b (lcMap a b (χ₁ m)) * lcΦ a b (lcMap a b (χ₂ m))
      rw [map_mul, map_mul]
    rw [e, act.mul_smul, e₂] at e₁₂
    exact e₁₂

/-- **The generic stabilizer, for `p` factoring through an affine open `D` of `X`.** -/
theorem generic_of_open_immersion [AddMonoid.FG M] [IsDomain Γ((SCH).obj V, ⊤)]
    [IsNoetherianRing Γ((SCH).obj V, ⊤)] (hX : IsAlgebraicSpace B S hS X)
    (act : AAction (fppfO B S hS) M X) {D : BigFppfOver B S hS} [IsAffine ((SCH).obj D)]
    (ξ : yoneda.obj D ⟶ X) (hξ : Space.IsOpenImmersion B S hS ξ) (q : V ⟶ D) :
    ∃ (s : Γ((SCH).obj V, ⊤)) (_ : s ≠ 0) (Z : AddSubgroup M),
      ∀ (T : BigFppfOver B S hS) (t : T ⟶ V), IsUnit (((SCH).map t).appTop.hom s) →
        ∀ h : APt (fppfO B S hS) M (op T),
          act.smul h (X.map t.op (ξ.app (op V) q)) = X.map t.op (ξ.app (op V) q) ↔
            ∀ z ∈ Z, h (Multiplicative.ofAdd z) = 1 := by
  classical
  haveI : IsNoetherianRing (gRing M V) := Algebra.FiniteType.isNoetherianRing Γ((SCH).obj V, ⊤) _
  obtain ⟨ι, _, f, G, hA, hB⟩ := exists_charts act ξ hξ q
  have hD : ChartData act (ξ.app (op V) q) f G := ⟨hA, hB⟩
  obtain ⟨s, hs, Z, hZ⟩ := exists_generic_ring (tests_of_charts hX hD)
  refine ⟨s, hs, Z, fun T t hu h => ?_⟩
  let 𝒰 := ((SCH).obj T).affineCover
  let W : 𝒰.I₀ → BigFppfOver B S hS := fun i => Chart.immObj T (𝒰.f i)
  let e : ∀ i, W i ⟶ T := fun i => Chart.immι T (𝒰.f i)
  haveI hWa : ∀ i, IsAffine ((SCH).obj (W i)) := fun i => inferInstanceAs (IsAffine (Spec _))
  have hloc : ∀ i, (act.smul (APt.res (e i).op h) (X.map (e i ≫ t).op (ξ.app (op V) q)) =
      X.map (e i ≫ t).op (ξ.app (op V) q)) ↔ ∀ z ∈ Z, APt.res (e i).op h (Multiplicative.ofAdd z) = 1 := by
    intro i
    rw [fix_iff hX hD (e i ≫ t) (APt.res (e i).op h)]
    refine hZ _ _ _ ?_
    have : ((SCH).map (e i ≫ t)).appTop.hom s = ((SCH).map (e i)).appTop.hom (((SCH).map t).appTop.hom s) := by
      rw [Functor.map_comp, Scheme.Hom.comp_appTop]
      rfl
    rw [this]
    exact hu.map _
  have hmap : ∀ i, X.map (e i).op (act.smul h (X.map t.op (ξ.app (op V) q))) =
      act.smul (APt.res (e i).op h) (X.map (e i ≫ t).op (ξ.app (op V) q)) := fun i => by
    rw [act.map_smul, op_comp, Functor.map_comp_apply]
  have hmap2 : ∀ i, X.map (e i).op (X.map t.op (ξ.app (op V) q)) = X.map (e i ≫ t).op (ξ.app (op V) q) :=
    fun i => by rw [op_comp, Functor.map_comp_apply]
  constructor
  · intro hfix z hz
    let y : Γ((SCH).obj T, ⊤) := h (Multiplicative.ofAdd z)
    have hy : y - 1 = 0 := Scheme.zero_of_zero_cover (U := ⊤) _ 𝒰 fun i => by
      have h1 := (hloc i).1 (by rw [← hmap, hfix, hmap2]) z hz
      have h2 : ((SCH).map (e i)).appTop.hom y = 1 := h1
      change ((SCH).map (e i)).appTop.hom (y - 1) = 0
      rw [map_sub, h2, map_one, sub_self]
    exact sub_eq_zero.1 hy
  · intro hz
    refine eq_of_family hX W e (fun i => inferInstanceAs (AlgebraicGeometry.IsOpenImmersion (𝒰.f i)))
      (fun y => ?_) _ _ fun i => ?_
    · obtain ⟨i, y', hy⟩ := 𝒰.exists_eq y
      exact ⟨i, y', hy⟩
    · rw [hmap, hmap2]
      refine (hloc i).2 fun z hzz => ?_
      rw [APt.res_apply, hz z hzz]
      exact map_one _

end AlgMag.ChartQSStabGen
