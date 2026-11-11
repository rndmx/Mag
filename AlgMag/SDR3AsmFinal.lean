/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SDR3AsmPkg
import AlgMag.SDR3CoactAffine
import AlgMag.SDFinal
import AlgMag.SDLocSFactor

/-!
# Lemma D for algebraic spaces: assembling `SDLocS_InvChart`

Steps 4-5 and the base-change presentation `W ×_Q V = Spec (R₃ ⊗ A)`.
For Props. 3.31 (ii), 3.32 (ii), 15.1 of `Algebraic Magnetism`.

The results of Steps 1-3 are the single named input `SDR3Asm_ChartInput`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct

universe u

namespace AlgMag.SD

open AlgMag AlgMag.SQ AlgMag.SDTorus

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

section Assemble

variable {R A Γ' : Type u} [CommRing R] [CommRing A] [AddCommGroup Γ'] [UniqueSums Γ'] [Algebra R A]
  (c : Coact A Γ') (hc : ∀ r : R, c.σ (algebraMap R A r) = AddMonoidAlgebra.single 0 (algebraMap R A r))
  (hι : c.IsInv (algebraMap R A))

include hι hc in
/-- The final assembly, on the data of Steps 4-9. `R₃` is étale over `R'`, itself étale over `R`, and `Φ` is the output of
`SDR3Asm_closure`: base-change presentation of `W ×_Q V`, the map `g`, its invariance. -/
theorem SDR3Asm_assemble {W Q : BigFppfOver B S hS} (π : W ⟶ Q) (i : (SCH).obj W ≅ Spec (.of A))
    (i₀ : (SCH).obj Q ≅ Spec (.of R)) (hπ : (SCH).map π ≫ i₀.hom = i.hom ≫ sp (algebraMap R A))
    (hQ : B.Contains (Spec (.of R))) (x : X.obj (op W)) (q : PrimeSpectrum R)
    {R' R₃ : Type u} [CommRing R'] [CommRing R₃] [Algebra R R'] [Algebra.Etale R R'] [Algebra R' R₃]
    [Algebra.Etale R' R₃] (P₃ : Ideal R₃) [P₃.IsPrime]
    (hP₃ : ∀ s : R, algebraMap R' R₃ (algebraMap R R' s) ∈ P₃ ↔ s ∈ q.asIdeal)
    {𝒱 : Scheme.{u}} (f : 𝒱 ⟶ Spec (.of (R' ⊗[R] A)))
    (Φ : Spec (.of (R₃ ⊗[R'] (R' ⊗[R] A))) ⟶ 𝒱)
    (hΦ : Φ ≫ f = Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight :
      (R' ⊗[R] A) →ₐ[R'] R₃ ⊗[R'] (R' ⊗[R] A)) : (R' ⊗[R] A) →+* R₃ ⊗[R'] (R' ⊗[R] A))))
    (U : BigFppfOver B S hS) [IsAffine ((SCH).obj U)] (u : X.obj (op U)) (ψ : 𝒱 ⟶ (SCH).obj U)
    (hψS : ψ ≫ U.hom.hom = f ≫ Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight :
      A →ₐ[R] R' ⊗[R] A) : A →+* R' ⊗[R] A)) ≫ i.inv ≫ W.hom.hom)
    (hX : ∀ (Z : BigFppfOver B S hS) (a : Z ⟶ W) (b : Z ⟶ U) (z : (SCH).obj Z ⟶ 𝒱),
      (SCH).map a = z ≫ f ≫ Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight :
        A →ₐ[R] R' ⊗[R] A) : A →+* R' ⊗[R] A)) ≫ i.inv → (SCH).map b = z ≫ ψ → X.map b.op u = X.map a.op x)
    (hΦ0 : ∀ y : Γ((SCH).obj U, ⊤), ∃ r : R₃, SDR3Asm_ev Φ (ψ.appTop.hom y) = r ⊗ₜ[R'] (1 : R' ⊗[R] A)) :
    ∃ (V : BigFppfOver B S hS) (_ : IsAffine ((SCH).obj V)) (e : V ⟶ Q), Etale ((SCH).map e) ∧
      i₀.inv q ∈ Set.range ((SCH).map e) ∧
      ∃ (A' A₀' : Type u) (_ : CommRing A') (_ : CommRing A₀') (c' : Coact A' Γ') (ι' : A₀' →+* A') (_ : c'.IsInv ι')
        (i' : (SCH).obj (pullback π e) ≅ Spec (.of A')) (i₀' : (SCH).obj V ≅ Spec (.of A₀'))
        (_ : (SCH).map (pullback.snd π e) ≫ i₀'.hom = i'.hom ≫ sp ι')
        (U' : BigFppfOver B S hS) (u' : X.obj (op U')) (g : pullback π e ⟶ U'),
        IsInvariantF c' (i'.inv ≫ (SCH).map g) ∧ X.map g.op u' = X.map (pullback.fst π e).op x := by
  letI iR3 : Algebra R R₃ := ((algebraMap R' R₃).comp (algebraMap R R')).toAlgebra
  haveI tw : IsScalarTower R R' R₃ := .of_algebraMap_eq fun _ => rfl
  haveI : Algebra.Etale R R₃ := Algebra.Etale.comp R R' R₃
  have hC : B.Contains (Spec (.of R₃)) := SDR3Coact_contains_of_finiteType (R := R) hQ
  let ρ : R →+* R₃ := algebraMap R R₃
  let VS : Spec (.of R₃) ⟶ (SCH).obj Q := sp ρ ≫ i₀.inv
  let V : BigFppfOver B S hS := siteObject B S hS hC (VS ≫ Q.hom.hom)
  haveI hVa : IsAffine ((SCH).obj V) := inferInstanceAs (IsAffine (Spec _))
  let e : V ⟶ Q := overHom VS rfl
  have hee : (SCH).map e = VS := rfl
  have hEt : Etale (sp ρ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.2 inferInstance
  let c₁ := SDExist_bc R' c hc
  have hι₁ : c₁.IsInv (algebraMap R' (R' ⊗[R] A)) := SDExist_bc_isInv R' c hc hι
  have hc₁ : ∀ r : R', c₁.σ (algebraMap R' (R' ⊗[R] A) r) = AddMonoidAlgebra.single 0 (algebraMap R' (R' ⊗[R] A) r) :=
    fun r => (hι₁.range _).2 ⟨r, rfl⟩
  let c₃ := SDExist_bc R₃ c₁ hc₁
  have hι₃ : c₃.IsInv (Algebra.TensorProduct.includeLeftRingHom : R₃ →+* R₃ ⊗[R'] (R' ⊗[R] A)) :=
    SDExist_bc_isInv R₃ c₁ hc₁ hι₁
  let A₃ := R₃ ⊗[R'] (R' ⊗[R] A)
  let toB : A →+* R' ⊗[R] A := ((Algebra.TensorProduct.includeRight : A →ₐ[R] R' ⊗[R] A) : A →+* R' ⊗[R] A)
  let toA₃ : R' ⊗[R] A →+* A₃ := ((Algebra.TensorProduct.includeRight : (R' ⊗[R] A) →ₐ[R'] A₃) : (R' ⊗[R] A) →+* A₃)
  have hPO := (CommRingCat.isPushout_tensorProduct R R' A).paste_horiz
    (CommRingCat.isPushout_tensorProduct R' R₃ (R' ⊗[R] A))
  have hpb : IsPullback (sp (Algebra.TensorProduct.includeLeftRingHom : R₃ →+* A₃))
      (sp (toA₃.comp toB)) (sp ρ) (sp (algebraMap R A)) :=
    isPullback_SpecMap_of_isPushout _ _ _ _ hPO
  have hsite : IsPullback ((SCH).map (pullback.snd π e)) ((SCH).map (pullback.fst π e)) ((SCH).map e) ((SCH).map π) :=
    ((IsPullback.of_hasPullback π e).map (SCH)).flip
  have hsite2 : IsPullback ((SCH).map (pullback.snd π e)) ((SCH).map (pullback.fst π e) ≫ i.hom)
      (sp ρ) (sp (algebraMap R A)) := by
    refine IsPullback.of_iso hsite (Iso.refl _) (Iso.refl _) i i₀ (by simp) (by simp) ?_ hπ
    change VS ≫ i₀.hom = sp ρ
    simp [VS]
  let j := hsite2.isoIsPullback _ _ hpb
  have hj : (SCH).map (pullback.snd π e) = j.hom ≫ sp (Algebra.TensorProduct.includeLeftRingHom : R₃ →+* A₃) :=
    (hsite2.isoIsPullback_hom_fst _ _ hpb).symm
  have hj₂ : (SCH).map (pullback.fst π e) ≫ i.hom = j.hom ≫ sp (toA₃.comp toB) :=
    (hsite2.isoIsPullback_hom_snd _ _ hpb).symm
  have hfst : (SCH).map (pullback.fst π e) = j.hom ≫ sp toA₃ ≫ sp toB ≫ i.inv := by
    have : sp (toA₃.comp toB) = sp toA₃ ≫ sp toB := sp_comp _ _
    rw [← Category.assoc, ← Category.assoc, Category.assoc j.hom, ← this, ← hj₂]
    simp
  let G₀ : (SCH).obj (pullback π e) ⟶ (SCH).obj U := j.hom ≫ Φ ≫ ψ
  have hG₀ : G₀ ≫ U.hom.hom = (pullback π e).hom.hom := by
    have e3 := site_w (B := B) (S := S) (hS := hS) (pullback.fst π e)
    change _ = _ at e3
    change (j.hom ≫ Φ ≫ ψ) ≫ U.hom.hom = _
    rw [Category.assoc, Category.assoc, hψS, ← e3, hfst]
    simp only [Category.assoc]
    rw [← Category.assoc Φ f, hΦ]
  let g : pullback π e ⟶ U := overHom G₀ hG₀
  refine ⟨V, hVa, e, ?_, ?_, A₃, R₃, inferInstance, inferInstance, c₃, _, hι₃, j, Iso.refl _, ?_, U, u, g, ?_, ?_⟩
  · rw [hee]
    infer_instance
  · refine ⟨(⟨P₃, inferInstance⟩ : PrimeSpectrum R₃), ?_⟩
    change i₀.inv (sp ρ _) = _
    congr 1
    apply PrimeSpectrum.ext
    ext s
    exact hP₃ s
  · simpa using hj
  · -- invariance
    have hF : j.inv ≫ (SCH).map g = Φ ≫ ψ := by
      change j.inv ≫ j.hom ≫ Φ ≫ ψ = _
      simp
    rw [IsInvariantF, hF]
    apply ext_of_isAffine
    rw [← Category.assoc, ← Category.assoc, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
    refine CommRingCat.hom_ext (RingHom.ext fun y => ?_)
    apply (Scheme.ΓSpecIso (.of (AddMonoidAlgebra A₃ Γ'))).commRingCatIsoToRingEquiv.injective
    obtain ⟨r, hr⟩ := hΦ0 y
    have h1 := SDR3Asm_ev_comp c₃.σ Φ (ψ.appTop.hom y)
    have h2 := SDR3Asm_ev_comp (cC A₃ Γ') Φ (ψ.appTop.hom y)
    rw [hr] at h1 h2
    have h3 : c₃.σ (r ⊗ₜ[R'] (1 : R' ⊗[R] A)) = cC A₃ Γ' (r ⊗ₜ[R'] (1 : R' ⊗[R] A)) := (hι₃.range _).2 ⟨r, rfl⟩
    exact h1.trans (h3.trans h2.symm)
  · refine hX _ _ _ (j.hom ≫ Φ) ?_ rfl
    rw [hfst]
    simp only [Category.assoc]
    rw [← Category.assoc Φ f, hΦ]

end Assemble

/-- **The outcome of Steps 1-3**, at a point `q` of `Spec R`, for `W = Spec A → Spec R`, and `x` on `W`: an étale neighbourhood
`(R', P')` of `q`; the closed orbit `I` of `R' ⊗ A` over `P'`; a chart `𝒱 → Spec (R' ⊗ A)`, étale, separated, `𝒱`
quasi-compact, with a coaction compatible with the action on field-valued points (Steps 2-3); the section `s₀` over the
localized closed orbit (Steps 1-2); a map `ψ` from `𝒱` to an affine `U`, invariant, along which `x` comes from `u`. -/
def SDR3Asm_Data {R A Γ' : Type u} [CommRing R] [CommRing A] [AddCommGroup Γ'] [Algebra R A] (c : Coact A Γ')
    (hc : ∀ r : R, c.σ (algebraMap R A r) = AddMonoidAlgebra.single 0 (algebraMap R A r))
    {W : BigFppfOver B S hS} (i : (SCH).obj W ≅ Spec (.of A)) (x : X.obj (op W)) (q : PrimeSpectrum R) : Prop :=
  ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R') (P' : Ideal R') (_ : P'.IsPrime)
    (_ : P'.LiesOver q.asIdeal) (I : Ideal (R' ⊗[R] A)) (_ : I.IsPrime) (_ : (SDExist_bc R' c hc).IsHomIdeal I)
    (_ : ∀ a, algebraMap R' (R' ⊗[R] A) a ∈ I → a ∈ P')
    (_ : ∀ J, (SDExist_bc R' c hc).IsHomIdeal J → I < J → ∃ a, algebraMap R' (R' ⊗[R] A) a ∈ J ∧ a ∉ P')
    (T : Submonoid ((R' ⊗[R] A) ⧸ I))
    (_ : T = P'.primeCompl.map ((Ideal.Quotient.mk I).comp (algebraMap R' (R' ⊗[R] A))))
    (𝒱 : Scheme.{u}) (_ : CompactSpace 𝒱) (f : 𝒱 ⟶ Spec (.of (R' ⊗[R] A))) (_ : Etale f) (_ : IsSeparated f)
    (cV : Coact Γ(𝒱, ⊤) Γ')
    (_ : ∀ (d : Γ') (b : R' ⊗[R] A), cV.comp d (SDR3Asm_fs f b) = SDR3Asm_fs f ((SDExist_bc R' c hc).comp d b))
    (_ : SDR3Asm_ActsOnPoints cV)
    (s₀ : Spec (.of (Localization T)) ⟶ 𝒱)
    (_ : s₀ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap (R' ⊗[R] A) (Localization T))))
    (_ : ∀ z, SDR3Asm_ev s₀ z = 0 → ∀ d, SDR3Asm_ev s₀ (cV.comp d z) = 0)
    (U : BigFppfOver B S hS) (_ : IsAffine ((SCH).obj U)) (u : X.obj (op U)) (ψ : 𝒱 ⟶ (SCH).obj U),
    (∀ y : Γ((SCH).obj U, ⊤), cV.IsHom 0 (ψ.appTop.hom y)) ∧
    (ψ ≫ U.hom.hom = f ≫ Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight :
      A →ₐ[R] R' ⊗[R] A) : A →+* R' ⊗[R] A)) ≫ i.inv ≫ W.hom.hom) ∧
    ∀ (Z : BigFppfOver B S hS) (a : Z ⟶ W) (b : Z ⟶ U) (z : (SCH).obj Z ⟶ 𝒱),
      (SCH).map a = z ≫ f ≫ Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight :
        A →ₐ[R] R' ⊗[R] A) : A →+* R' ⊗[R] A)) ≫ i.inv → (SCH).map b = z ≫ ψ → X.map b.op u = X.map a.op x

/-- The named input: Steps 1-3 for `𝔸(P)_T → 𝔸(P₀)_T`, graded by `Lat r`. -/
def SDR3Asm_ChartInput (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (r : ℕ) : Prop :=
  ∀ {P P₀ : Type u} [AddCommMonoid P] [Countable P] [AddCommMonoid P₀] [Countable P₀]
    (δ : P →+ Lat.{u} r) (j : P₀ →+ P) (hj : Function.Injective j) (hk : ∀ p, δ p = 0 ↔ p ∈ Set.range j)
    (T : BigFppfOver B S hS) [IsAffine ((SCH).obj T)] (x : X.obj (op (specObj P T))), IsInvPt X δ x →
    ∀ q : PrimeSpectrum (gRing P₀ T),
      letI := (monι j Γ((SCH).obj T, ⊤)).toAlgebra
      SDR3Asm_Data (R := gRing P₀ T) (monCoact δ)
        (fun r => ((monCoact_isInv (R := Γ((SCH).obj T, ⊤)) (δ := δ) hj hk).range _).2 ⟨r, rfl⟩)
        (W := specObj P T) (Iso.refl _) x q

/-- **`SDLocS_InvChart`, from Steps 1-3.** -/
theorem SDR3Asm_invChart {r : ℕ} (h : SDR3Asm_ChartInput X r) : SDLocS_InvChart X (Lat.{u} r) := by
  intro P P₀ _ _ _ _ δ j hj hk T _ x hx q
  letI := (monι j Γ((SCH).obj T, ⊤)).toAlgebra
  have hι := monCoact_isInv (R := Γ((SCH).obj T, ⊤)) (δ := δ) hj hk
  have hc : ∀ r : gRing P₀ T, (monCoact δ).σ (algebraMap (gRing P₀ T) (gRing P T) r) =
      AddMonoidAlgebra.single 0 (algebraMap (gRing P₀ T) (gRing P T) r) := fun r => (hι.range _).2 ⟨r, rfl⟩
  obtain ⟨R', _, _, _, P', _, hP', I, _, hI, hIq, hmax, Sm, hSm, 𝒱, _, f, _, _, cV, hV, hact, s₀, hs₀, hs₀k, U, _, u, ψ,
    hψ0, hψS, hX⟩ := h δ j hj hk T x hx q
  let eΓ : Lat.{u} r ≃+ (Fin r → ℤ) := AddEquiv.ulift
  obtain ⟨R₃, _, _, _, P₃, _, hP₃, Φ, hΦ, hΦ0⟩ := SDR3Asm_closure (R := R') eΓ f (SDExist_bc R' (monCoact δ) hc) cV
    (fun r => ((SDExist_bc_isInv R' (monCoact δ) hc hι).range _).2 ⟨r, rfl⟩) hV (SDExist_bc_isInv R' (monCoact δ) hc hι)
    hact P' hI hIq hmax Sm hSm s₀ hs₀ hs₀k
  have hπ : (SCH).map (specAlong T j) ≫ (Iso.refl _ : (SCH).obj (specObj P₀ T) ≅ Spec (.of (gRing P₀ T))).hom =
      (Iso.refl _ : (SCH).obj (specObj P T) ≅ Spec (.of (gRing P T))).hom ≫ sp (algebraMap (gRing P₀ T) (gRing P T)) := by
    change (SCH).map (specAlong T j) ≫ 𝟙 _ = 𝟙 _ ≫ sp (monι j _)
    rw [Category.comp_id, Category.id_comp]
    rfl
  have hPq : ∀ s : gRing P₀ T, algebraMap R' R₃ (algebraMap (gRing P₀ T) R' s) ∈ P₃ ↔ s ∈ q.asIdeal := by
    intro s
    have ha : ∀ t : R', algebraMap R' R₃ t ∈ P₃ ↔ t ∈ P' := fun t => by
      rw [hP₃.over]
      rfl
    have hb : ∀ t : gRing P₀ T, algebraMap (gRing P₀ T) R' t ∈ P' ↔ t ∈ q.asIdeal := fun t => by
      rw [hP'.over]
      rfl
    exact (ha _).trans (hb s)
  obtain ⟨V, hVa, e, he, hq, A', A₀', _, _, c', ι', hι', i', i₀', hπ', U', u', g, hg, hgu⟩ :=
    SDR3Asm_assemble (R := gRing P₀ T) (A := gRing P T) (monCoact δ) hc hι (specAlong T j) (Iso.refl _) (Iso.refl _) hπ
      (contains_spec P₀ T) x q P₃ hPq f Φ hΦ U u ψ hψS hX (fun y => hΦ0 _ (hψ0 y))
  exact ⟨V, hVa, e, he, hq, A', A₀', inferInstance, inferInstance, c', ι', hι', i', i₀', hπ', U', u', g, hg, hgu⟩

/-- **The hypothesis `hL` of `SDFinal`**, from Steps 1-3. -/
theorem SDR3Asm_localFactorAll (h : ∀ r, SDR3Asm_ChartInput X r) : SDLocS_LocalFactorAll X :=
  fun r => SDLocS_localFactor (SDR3Asm_invChart (h r))

/-- **Proposition 3.32 (ii)** for an algebraic space, conditional only on Steps 1-3. -/
theorem SDR3Asm_prop332 (hX : IsAlgebraicSpace B S hS X) (h : ∀ r, SDR3Asm_ChartInput X r) {M : Type u}
    [AddCommGroup M] [AddGroup.FG M] {aX : AAction (fppfO B S hS) M X} {N L : AddSubmonoid M}
    (T : BigFppfOver B S hS) :
    Function.Bijective (iterOfInf : AttractorPt aX (N ⊓ L) T → IterPt aX N L T) :=
  prop332_space hX (SDR3Asm_localFactorAll h) T

/-- **Proposition 3.31 (ii)** for an algebraic space, conditional only on Steps 1-3. -/
theorem SDR3Asm_prop331 (hX : IsAlgebraicSpace B S hS X) (h : ∀ r, SDR3Asm_ChartInput X r) {M Z : Type u}
    [AddCommGroup M] [AddCommGroup Z] [AddGroup.FG M] [AddGroup.FG Z] {f : M →+ Z} {Y : AddSubmonoid Z}
    {aX : AAction (fppfO B S hS) M X} (T : BigFppfOver B S hS) :
    Function.Bijective (ptAlong aX : AttractorPt aX (Y.comap f) T → AttractorPt (actAlong f aX) Y T) :=
  prop331_space hX (SDR3Asm_localFactorAll h) T

/-- **Proposition 15.1** for a separated algebraic space and a finitely generated `M`, conditional only on Steps 1-3. -/
theorem SDR3Asm_prop151 (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X) (h : ∀ r, SDR3Asm_ChartInput X r)
    {M : Type u} [AddCommGroup M] [AddMonoid.FG M] {aX : AAction (fppfO B S hS) M X} (N : AddSubmonoid M) :
    IsPure (attractorImage aX) N ↔ ∀ L, L < N → attractorImage aX L < attractorImage aX N :=
  prop151_space hX hsep (SDR3Asm_localFactorAll h) N

end AlgMag.SD

#print axioms AlgMag.SD.SDR3Asm_closure
#print axioms AlgMag.SD.SDR3Asm_assemble
#print axioms AlgMag.SD.SDR3Asm_invChart
#print axioms AlgMag.SD.SDR3Asm_localFactorAll
#print axioms AlgMag.SD.SDR3Asm_prop332
#print axioms AlgMag.SD.SDR3Asm_prop331
#print axioms AlgMag.SD.SDR3Asm_prop151
