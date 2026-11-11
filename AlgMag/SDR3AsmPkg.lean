/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SDR3AsmStable
import AlgMag.SDR3OrbitField
import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Lemma D, Steps 4-9, as one statement about `𝒱 → Spec B`

For Props. 3.31 (ii), 3.32 (ii) of `Algebraic Magnetism`. `D` plays the part of the integral closure `C'`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct

universe u

namespace AlgMag.SD

open AlgMag.SQ

variable {R B D Γ' : Type u} [CommRing R] [CommRing B] [CommRing D] [AddCommGroup Γ'] [UniqueSums Γ']
  [Algebra R B] [Algebra R D] [Algebra B D] [IsScalarTower R B D]

/-- The sections of `Spec D_a → 𝒱 → Spec B` make `D_a` étale over `B`. -/
theorem SDR3Asm_etale_of_section {𝒱 : Scheme.{u}} (f : 𝒱 ⟶ Spec (.of B)) [Etale f] (φ : D →+* Γ(𝒱, ⊤))
    (hφB : f = SDR3Asm_j φ ≫ Spec.map (CommRingCat.ofHom (algebraMap B D))) (a : D)
    {θ : Spec (.of (Localization.Away a)) ⟶ 𝒱} [IsOpenImmersion θ]
    (hθj : θ ≫ SDR3Asm_j φ = Spec.map (CommRingCat.ofHom (algebraMap D (Localization.Away a)))) :
    Algebra.Etale B (Localization.Away a) := by
  have h : Etale (θ ≫ f) := inferInstance
  have e : θ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away a))) := by
    rw [hφB, ← Category.assoc, hθj, ← Spec.map_comp]
    congr 2
  rw [e, HasRingHomProperty.Spec_iff (P := @Etale)] at h
  exact (RingHom.etale_algebraMap).1 h

/-- `ev` of `Spec κ ≫ θ`. -/
lemma SDR3Asm_ev_comp {𝒱 : Scheme.{u}} {K K' : Type u} [CommRing K] [CommRing K'] (κ : K →+* K')
    (θ : Spec (.of K) ⟶ 𝒱) (z : Γ(𝒱, ⊤)) :
    SDR3Asm_ev (Spec.map (CommRingCat.ofHom κ) ≫ θ) z = κ (SDR3Asm_ev θ z) := by
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom κ)
  have h2 := congrArg (fun k => k.hom (θ.appTop.hom z)) h
  change (Scheme.ΓSpecIso (.of K')).hom.hom ((Spec.map (CommRingCat.ofHom κ) ≫ θ).appTop.hom z) = _
  rw [Scheme.Hom.comp_appTop]
  exact h2

/-- Homogeneity descends along an injective graded map. -/
lemma SDR3Asm_isHom_of_map {𝒱 : Scheme.{u}} (φ : D →+* Γ(𝒱, ⊤)) (hφ : Function.Injective φ) (cD : Coact D Γ')
    (cV : Coact Γ(𝒱, ⊤) Γ') (hgr : ∀ d y, cV.comp d (φ y) = φ (cD.comp d y)) {y : D} (h : cV.IsHom 0 (φ y)) :
    cD.IsHom 0 y := by
  classical
  have h' : cV.σ (φ y) = AddMonoidAlgebra.single 0 (φ y) := h
  change cD.σ y = _
  ext e
  apply hφ
  have e1 : φ ((cD.σ y).coeff e) = (cV.σ (φ y)).coeff e := (hgr e y).symm
  rw [e1, h', AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Finsupp.single_apply]
  split_ifs <;> simp

/-- **Steps 4-9** for an abstract `D` (the integral closure `C'` in the application), with the map `Φ` to `𝒱` from
`Spec (R₃ ⊗ B)`, sending functions of degree `0` into `R₃`. `E` is the localized closed orbit, `s₀` the section of Step 2. -/
theorem SDR3Asm_pkg {𝒱 : Scheme.{u}} [CompactSpace 𝒱] (f : 𝒱 ⟶ Spec (.of B)) [Etale f]
    (cB : Coact B Γ') (cD : Coact D Γ') (cV : Coact Γ(𝒱, ⊤) Γ')
    (hcB : ∀ r : R, cB.σ (algebraMap R B r) = AddMonoidAlgebra.single 0 (algebraMap R B r))
    (hBD : ∀ (d : Γ') (b : B), cD.comp d (algebraMap B D b) = algebraMap B D (cB.comp d b))
    (hιB : cB.IsInv (algebraMap R B)) [Algebra.IsIntegral B D]
    (φ : D →+* Γ(𝒱, ⊤)) (hφ : Function.Injective φ) (hgr : ∀ d y, cV.comp d (φ y) = φ (cD.comp d y))
    [hj : IsOpenImmersion (SDR3Asm_j φ)] (hact : SDR3Asm_ActsOnPoints cV)
    (hφB : f = SDR3Asm_j φ ≫ Spec.map (CommRingCat.ofHom (algebraMap B D)))
    (P : Ideal R) [P.IsPrime] {I : Ideal B} [I.IsPrime] (hI : cB.IsHomIdeal I)
    (hIq : ∀ a, algebraMap R B a ∈ I → a ∈ P)
    (hmax : ∀ J, cB.IsHomIdeal J → I < J → ∃ a, algebraMap R B a ∈ J ∧ a ∉ P)
    (S : Submonoid (B ⧸ I)) (hS : S = P.primeCompl.map ((Ideal.Quotient.mk I).comp (algebraMap R B)))
    (s₀ : Spec (.of (Localization S)) ⟶ 𝒱)
    (hs₀ : s₀ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap B (Localization S))))
    (hs₀k : ∀ z, SDR3Asm_ev s₀ z = 0 → ∀ d, SDR3Asm_ev s₀ (cV.comp d z) = 0) :
    ∃ (R₃ : Type u) (_ : CommRing R₃) (_ : Algebra R R₃) (_ : Algebra.Etale R R₃) (P₃ : Ideal R₃) (_ : P₃.IsPrime)
      (_ : P₃.LiesOver P) (Φ : Spec (.of (R₃ ⊗[R] B)) ⟶ 𝒱),
      Φ ≫ f = Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight : B →ₐ[R] R₃ ⊗[R] B) : B →+* R₃ ⊗[R] B)) ∧
      ∀ z, cV.IsHom 0 z → ∃ r : R₃, SDR3Asm_ev Φ z = r ⊗ₜ[R] (1 : B) := by
  classical
  let E := Localization S
  -- `E` and `π`
  have hevj : ((SDR3Asm_ev s₀).comp φ).comp (algebraMap B D) = algebraMap B E := by
    have h1 := SDR3Asm_comp_j φ s₀
    have h2 : s₀ ≫ SDR3Asm_j φ ≫ Spec.map (CommRingCat.ofHom (algebraMap B D)) =
        Spec.map (CommRingCat.ofHom (algebraMap B E)) := by
      rw [← hφB]
      exact hs₀
    rw [← Category.assoc, h1, ← Spec.map_comp] at h2
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h2)
  let π : D →ₐ[B] E :=
    { (SDR3Asm_ev s₀).comp φ with
      commutes' := fun b => congrArg (fun k => k b) hevj }
  have hπ : ∀ y, π y = SDR3Asm_ev s₀ (φ y) := fun _ => rfl
  haveI hdom : IsDomain E := by
    refine IsLocalization.isDomain_localization (M := S) ?_
    intro t ht
    have ht' := ht
    rw [hS] at ht'
    obtain ⟨s, hs, rfl⟩ := ht'
    refine mem_nonZeroDivisors_of_ne_zero fun h0 => hs (hIq s ?_)
    exact Ideal.Quotient.eq_zero_iff_mem.1 h0
  let 𝔫 : Ideal D := RingHom.ker π.toRingHom
  haveI h𝔫P : 𝔫.IsPrime := RingHom.ker_isPrime _
  have hmem𝔫 : ∀ y, y ∈ 𝔫 ↔ π y = 0 := fun y => Iff.rfl
  have hπB : ∀ b, π (algebraMap B D b) = algebraMap (B ⧸ I) E (Ideal.Quotient.mk I b) := fun b => π.commutes b
  have hπR : ∀ s : R, π (algebraMap R D s) = algebraMap (B ⧸ I) E (Ideal.Quotient.mk I (algebraMap R B s)) := fun s => by
    rw [IsScalarTower.algebraMap_apply R B D, hπB]
  have hSm : ∀ s, s ∉ P → Ideal.Quotient.mk I (algebraMap R B s) ∈ S := fun s hs => by
    rw [hS]
    exact ⟨s, hs, rfl⟩
  have h𝔫I : ∀ b, b ∈ I → algebraMap B D b ∈ 𝔫 := fun b hb => by
    rw [hmem𝔫, hπB, Ideal.Quotient.eq_zero_iff_mem.2 hb, map_zero]
  have h𝔫R : ∀ s, algebraMap R D s ∈ 𝔫 ↔ s ∈ P := by
    intro s
    rw [hmem𝔫, hπR]
    constructor
    · intro h0
      obtain ⟨⟨t, ht⟩, htm⟩ := (IsLocalization.map_eq_zero_iff S E _).1 h0
      have ht' := ht
      rw [hS] at ht'
      obtain ⟨t', ht'P, rfl⟩ := ht'
      have h1 : algebraMap R B t' * algebraMap R B s ∈ I := by
        apply Ideal.Quotient.eq_zero_iff_mem.1
        rw [map_mul]
        exact htm
      rw [← map_mul] at h1
      exact (Ideal.IsPrime.mem_or_mem ‹_› (hIq _ h1)).resolve_left ht'P
    · intro hs
      rw [Ideal.Quotient.eq_zero_iff_mem.2 (SDR3Orbit_q_mem hιB hI hIq hmax hs), map_zero]
  have hfib : ∀ y : D, ∃ s, s ∉ P ∧ ∃ β, algebraMap R D s * y - algebraMap B D β ∈ 𝔫 := by
    intro y
    obtain ⟨⟨q, s₁⟩, hq⟩ := IsLocalization.surj S (π y)
    obtain ⟨β, rfl⟩ := Ideal.Quotient.mk_surjective q
    have hs₂ : (s₁ : B ⧸ I) ∈ P.primeCompl.map ((Ideal.Quotient.mk I).comp (algebraMap R B)) := hS ▸ s₁.2
    obtain ⟨s, hs, hse⟩ := hs₂
    refine ⟨s, hs, β, ?_⟩
    rw [hmem𝔫, map_sub, map_mul, hπR, hπB, sub_eq_zero, mul_comm]
    have e : Ideal.Quotient.mk I (algebraMap R B s) = (s₁ : B ⧸ I) := hse
    rw [e]
    exact hq
  have h𝔫 : cD.IsHomIdeal 𝔫 := by
    intro y hy d
    rw [hmem𝔫, hπ, ← hgr]
    exact hs₀k _ hy d
  have hg : SDExist_IsGraded cB cD := hBD
  have hcD : ∀ r : R, cD.σ (algebraMap R D r) = AddMonoidAlgebra.single 0 (algebraMap R D r) := by
    intro r
    have h0 : cB.IsHom 0 (algebraMap R B r) := hcB r
    have h1 := hBD 0 (algebraMap R B r)
    rw [cB.comp_self_of_isHom h0, ← IsScalarTower.algebraMap_apply] at h1
    have h2 := cD.comp_isHom 0 (algebraMap R D r)
    rwa [h1] at h2
  -- the point `𝔫` lies in `V`
  have h𝔫V : (⟨𝔫, h𝔫P⟩ : PrimeSpectrum D) ∈ Set.range (SDR3Asm_j φ) := by
    refine ⟨s₀ ⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
    have h2 : SDR3Asm_j φ (s₀ ⟨⊥, Ideal.isPrime_bot⟩) = (s₀ ≫ SDR3Asm_j φ) ⟨⊥, Ideal.isPrime_bot⟩ := rfl
    rw [h2, SDR3Asm_comp_j]
    apply PrimeSpectrum.ext
    ext y
    change SDR3Asm_ev s₀ (φ y) ∈ (⊥ : Ideal E) ↔ π y = 0
    rw [Ideal.mem_bot]
    rfl
  have hVo : IsOpen (Set.range (SDR3Asm_j φ)) := (SDR3Asm_j φ).isOpenEmbedding.isOpen_range
  obtain ⟨_, ⟨a₀, rfl⟩, hm₀, hsub₀⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open h𝔫V hVo
  have hcompS : ∀ (d : Γ') (p : PrimeSpectrum D), p ∉ Set.range (SDR3Asm_j φ) → cD.comp d a₀ ∈ p.asIdeal :=
    fun d p hp => comp_mem_of_stable cD (Set.range (SDR3Asm_j φ))
      (fun p _ hp => SDR3Asm_stable φ hφ cD cV hgr hact p hp)
      (a₀ := a₀) (fun p hp => hsub₀ hp) d p hp
  obtain ⟨d₁, hd₁⟩ : ∃ d₁, cD.comp d₁ a₀ ∉ 𝔫 := by
    by_contra hn
    push Not at hn
    exact hm₀ (cD.mem_of_comp_mem 𝔫 a₀ hn)
  obtain ⟨a, haDef⟩ : ∃ a, a = cD.comp d₁ a₀ := ⟨_, rfl⟩
  have ha : cD.IsHom d₁ a := haDef ▸ cD.comp_isHom d₁ a₀
  have ha𝔫 : a ∉ 𝔫 := haDef ▸ hd₁
  have hDa : ∀ p : PrimeSpectrum D, a ∉ p.asIdeal → p ∈ Set.range (SDR3Asm_j φ) := by
    intro p hp
    by_contra hn
    exact hp (haDef ▸ hcompS d₁ p hn)
  obtain ⟨θa, hθa, hθaj⟩ := SDR3Asm_section φ a hDa
  haveI : Algebra.Etale B (Localization.Away a) := SDR3Asm_etale_of_section f φ hφB a hθaj
  -- `π a` is a unit
  have hau : IsUnit (π a) := by
    obtain ⟨x, b₀, hxa, -, h, hh, hxh⟩ := SDR3Asm_d₀ (ι := algebraMap R B) hg hιB hI hIq hmax 𝔫 h𝔫 h𝔫I
      (fun s hs => (h𝔫R s).1 (by rwa [← IsScalarTower.algebraMap_apply] at hs))
      (fun y => by
        obtain ⟨s, hs, β, hβ⟩ := hfib y
        exact ⟨s, hs, β, by rwa [← IsScalarTower.algebraMap_apply]⟩) ha ha𝔫
    have h1 : π x = algebraMap (B ⧸ I) E (Ideal.Quotient.mk I (algebraMap R B h)) := by
      have := (hmem𝔫 _).1 hxh
      rw [map_sub, hπB, sub_eq_zero] at this
      exact this
    have hu : IsUnit (π x) := by
      rw [h1]
      exact IsLocalization.map_units E (⟨_, hSm h hh⟩ : S)
    rw [hxa, map_mul] at hu
    exact isUnit_of_mul_isUnit_left hu
  obtain ⟨d', s', hd'0, hs', hd'𝔫, hJ⟩ := SDR3Asm_G3 hg hI hcD P S hS π h𝔫 a hau
  obtain ⟨R₃, _, _, _, P₃, hP₃, hP₃o, d, b₁, hdd, hd0, κ, hκ1, hκ2⟩ :=
    SDR3Asm_alg cB cD hcB hcD hBD hιB P hI hIq hmax 𝔫 h𝔫 h𝔫I h𝔫R hfib ha ha𝔫 hd'0 hs' hd'𝔫 hJ
  have hDd : ∀ p : PrimeSpectrum D, d ∉ p.asIdeal → p ∈ Set.range (SDR3Asm_j φ) := fun p hp =>
    hDa p fun hm => hp (hdd ▸ p.asIdeal.mul_mem_right _ hm)
  obtain ⟨θ, hθ, hθj⟩ := SDR3Asm_section φ d hDd
  have hθev : ∀ y, SDR3Asm_ev θ (φ y) = algebraMap D _ y := by
    intro y
    have h1 := SDR3Asm_comp_j φ θ
    rw [hθj] at h1
    exact (congrArg (fun k => k.hom y) (Spec.map_injective h1)).symm
  refine ⟨R₃, inferInstance, inferInstance, inferInstance, P₃, hP₃, hP₃o, Spec.map (CommRingCat.ofHom κ) ≫ θ, ?_, ?_⟩
  · rw [Category.assoc, hφB, ← Category.assoc θ, hθj, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext1
    apply RingHom.ext
    intro b
    exact hκ1 b
  · intro z hz
    rw [SDR3Asm_ev_comp]
    obtain ⟨⟨y₁, m⟩, hm⟩ := IsLocalization.surj (Submonoid.powers d) (SDR3Asm_ev θ z)
    obtain ⟨n, hn⟩ := m.2
    simp only at hm
    have hn' : algebraMap D (Localization.Away d) (m : D) = algebraMap D _ d ^ n := by
      rw [← hn, map_pow]
    have hw : θ.appTop.hom (φ y₁ - φ d ^ n * z) = 0 := by
      apply (Scheme.ΓSpecIso (.of (Localization.Away d))).commRingCatIsoToRingEquiv.injective
      rw [map_zero]
      change SDR3Asm_ev θ (φ y₁ - φ d ^ n * z) = 0
      rw [map_sub, map_mul, map_pow, hθev, hθev, ← hm, hn']
      ring
    obtain ⟨k, hk⟩ := SDR3Asm_torsion φ d hθj _ hw
    have hφd : cV.IsHom 0 (φ d) := by
      have h1 := cV.comp_isHom 0 (φ d)
      rwa [hgr, cD.comp_self_of_isHom hd0] at h1
    have hz' : φ (d ^ k * y₁) = φ d ^ (k + n) * z := by
      rw [map_mul, map_pow, pow_add]
      have := sub_eq_zero.1 ((mul_sub _ _ _).symm.trans hk)
      rw [this]
      ring
    have hy0 : cD.IsHom 0 (d ^ k * y₁) := by
      refine SDR3Asm_isHom_of_map φ hφ cD cV hgr ?_
      rw [hz']
      simpa using (hφd.pow (k + n)).mul hz
    refine hκ2 (d ^ k * y₁) (k + n) _ hy0 ?_
    rw [map_mul, map_pow, pow_add, ← hm, hn']
    ring

lemma SDR3Asm_lqf {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] : LocallyQuasiFinite f := by
  refine ⟨fun {U} hU {V} hV e => ?_⟩
  have h : (f.appLE U V e).hom.Etale := HasRingHomProperty.appLE (P := @Etale) f inferInstance ⟨U, hU⟩ ⟨V, hV⟩ e
  letI := (f.appLE U V e).hom.toAlgebra
  haveI : Algebra.Etale Γ(Y, U) Γ(X, V) := RingHom.etale_algebraMap.1 h
  haveI : Algebra.EssFiniteType Γ(Y, U) Γ(X, V) := inferInstance
  exact (inferInstance : Algebra.QuasiFinite Γ(Y, U) Γ(X, V))

/-- **Steps 4-9** for `𝒱 → Spec B` étale, separated, `𝒱` quasi-compact, with `C' = toNormalization`, graded by
`SDExist_comp_integral_free`. -/
theorem SDR3Asm_closure {r : ℕ} (eΓ : Γ' ≃+ (Fin r → ℤ)) {𝒱 : Scheme.{u}} [CompactSpace 𝒱] (f : 𝒱 ⟶ Spec (.of B))
    [Etale f] [IsSeparated f] (cB : Coact B Γ') (cV : Coact Γ(𝒱, ⊤) Γ')
    (hcB : ∀ r : R, cB.σ (algebraMap R B r) = AddMonoidAlgebra.single 0 (algebraMap R B r))
    (hV : ∀ (d : Γ') (b : B), cV.comp d (SDR3Asm_fs f b) = SDR3Asm_fs f (cB.comp d b))
    (hιB : cB.IsInv (algebraMap R B)) (hact : SDR3Asm_ActsOnPoints cV)
    (P : Ideal R) [P.IsPrime] {I : Ideal B} [I.IsPrime] (hI : cB.IsHomIdeal I)
    (hIq : ∀ a, algebraMap R B a ∈ I → a ∈ P)
    (hmax : ∀ J, cB.IsHomIdeal J → I < J → ∃ a, algebraMap R B a ∈ J ∧ a ∉ P)
    (S : Submonoid (B ⧸ I)) (hS : S = P.primeCompl.map ((Ideal.Quotient.mk I).comp (algebraMap R B)))
    (s₀ : Spec (.of (Localization S)) ⟶ 𝒱)
    (hs₀ : s₀ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap B (Localization S))))
    (hs₀k : ∀ z, SDR3Asm_ev s₀ z = 0 → ∀ d, SDR3Asm_ev s₀ (cV.comp d z) = 0) :
    ∃ (R₃ : Type u) (_ : CommRing R₃) (_ : Algebra R R₃) (_ : Algebra.Etale R R₃) (P₃ : Ideal R₃) (_ : P₃.IsPrime)
      (_ : P₃.LiesOver P) (Φ : Spec (.of (R₃ ⊗[R] B)) ⟶ 𝒱),
      Φ ≫ f = Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight : B →ₐ[R] R₃ ⊗[R] B) : B →+* R₃ ⊗[R] B)) ∧
      ∀ z, cV.IsHom 0 z → ∃ r : R₃, SDR3Asm_ev Φ z = r ⊗ₜ[R] (1 : B) := by
  letI iBC : Algebra B Γ(𝒱, ⊤) := (SDR3Asm_fs f).toAlgebra
  have hf : cV.σ.comp (algebraMap B Γ(𝒱, ⊤)) =
      (AddMonoidAlgebra.mapRingHom Γ' (algebraMap B Γ(𝒱, ⊤))).comp cB.σ := by
    apply RingHom.ext
    intro b
    ext d
    change cV.comp d (SDR3Asm_fs f b) = _
    rw [hV]
    rw [RingHom.comp_apply, AddMonoidAlgebra.coeff_mapRingHom]
    rfl
  let D := integralClosure B Γ(𝒱, ⊤)
  let cD : Coact D Γ' := SDR3Asm_closureCoact eΓ cB cV hf
  have hcomp : ∀ d (y : D), ((cD.comp d y : D) : Γ(𝒱, ⊤)) = cV.comp d y := fun d y =>
    SDR3Asm_subCoact_comp cV (integralClosure B Γ(𝒱, ⊤)).toSubring _ y d
  letI iRD : Algebra R D := ((algebraMap B D).comp (algebraMap R B)).toAlgebra
  haveI : IsScalarTower R B D := .of_algebraMap_eq fun _ => rfl
  let φ : D →+* Γ(𝒱, ⊤) := (integralClosure B Γ(𝒱, ⊤)).val.toRingHom
  have hφ : Function.Injective φ := Subtype.val_injective
  haveI : QuasiCompact f := by
    rw [SDR3Asm_to_spec f]
    infer_instance
  haveI : LocallyQuasiFinite f := SDR3Asm_lqf f
  haveI hj : IsOpenImmersion (SDR3Asm_j φ) := SDR3Asm_zmt f
  have hφB : f = SDR3Asm_j φ ≫ Spec.map (CommRingCat.ofHom (algebraMap B D)) := by
    refine (SDR3Asm_to_spec f).trans ?_
    rw [Category.assoc, ← Spec.map_comp]
    rfl
  exact SDR3Asm_pkg (D := D) f cB cD cV hcB
    (fun d b => Subtype.ext ((hcomp d _).trans (hV d b))) hιB φ hφ (fun d y => (hcomp d y).symm) hact hφB P hI hIq hmax
    S hS s₀ hs₀ hs₀k

end AlgMag.SD
