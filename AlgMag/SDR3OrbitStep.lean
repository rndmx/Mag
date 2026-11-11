/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SDR3OrbitField
import AlgMag.SDR3OrbitPoint
import AlgMag.SDR3OrbitNakayama
import AlgMag.Prop337General
import Mathlib.Algebra.AlgebraicCard

/-!
# Lemma D, Steps 1-2: the orbit point, its lift to a chart, the étale extension

For Props. 3.31 (ii), 3.32 (ii) of `Algebraic Magnetism`, Steps 1-2. `SDR3Orbit_step1` is the
closed orbit `Spec κ'[L]`, over a finite separable extension of the residue field, with the section `s₀` of the chart.
`SDR3Orbit_step2` is the étale `R'` with residue field `κ'`, from Stacks 00UD. `SDR3Orbit_bcOrbit` is the ideal
`I' = ker (R' ⊗ B → κ'[Γ])`, with the hypotheses `hI`, `hIq`, `hmax` of `SDR3Orbit_main`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct Cardinal

universe u

namespace AlgMag.SD

open AlgMag AlgMag.SQ AlgMag.SDTorus AlgMag.P337

section BaseChange

variable {R B R'' Γ : Type u} [CommRing R] [CommRing B] [CommRing R''] [AddCommGroup Γ] [Algebra R B] [Algebra R R'']
  (cB : Coact B Γ) (hcB : ∀ r : R, cB.σ (algebraMap R B r) = AddMonoidAlgebra.single 0 (algebraMap R B r))

/-- Step 2: the closed orbit of `R'' ⊗ B`, as the kernel of `θ`-coefficients, not from a second maximal ideal. -/
theorem SDR3Orbit_bcOrbit (hιB : cB.IsInv (algebraMap R B)) {q₀ : Ideal R} [q₀.IsPrime] {I : Ideal B}
    (hI : cB.IsHomIdeal I) (hIq : ∀ a, algebraMap R B a ∈ I → a ∈ q₀)
    (hmax : ∀ J, cB.IsHomIdeal J → I < J → ∃ a, algebraMap R B a ∈ J ∧ a ∉ q₀)
    {F : Type u} [Field F] (φ : B →+* F) (τ : R'' →+* F) (hc : ∀ r, τ (algebraMap R R'' r) = φ (algebraMap R B r))
    (hφ : ∀ d b, cB.IsHom d b → (φ b = 0 ↔ b ∈ I)) {q' : Ideal R''} (hτ : ∀ a, τ a = 0 ↔ a ∈ q') :
    ∃ (θ : R'' ⊗[R] B →+* F) (I' : Ideal (R'' ⊗[R] B)), (∀ r b, θ (r ⊗ₜ b) = τ r * φ b) ∧
      (∀ y, y ∈ I' ↔ ∀ d, θ ((SDExist_bc R'' cB hcB).comp d y) = 0) ∧
      (SDExist_bc R'' cB hcB).IsHomIdeal I' ∧ (∀ a : R'', a ⊗ₜ[R] (1 : B) ∈ I' → a ∈ q') ∧
      ∀ J, (SDExist_bc R'' cB hcB).IsHomIdeal J → I' < J → ∃ a : R'', a ⊗ₜ[R] (1 : B) ∈ J ∧ a ∉ q' := by
  classical
  let cT := SDExist_bc R'' cB hcB
  letI : Algebra R F := (φ.comp (algebraMap R B)).toAlgebra
  let τₐ : R'' →ₐ[R] F := { τ with commutes' := hc }
  let φₐ : B →ₐ[R] F := { φ with commutes' := fun _ => rfl }
  let θ : R'' ⊗[R] B →+* F := (Algebra.TensorProduct.productMap τₐ φₐ).toRingHom
  have hθ : ∀ r b, θ (r ⊗ₜ b) = τ r * φ b := fun r b => Algebra.TensorProduct.productMap_apply_tmul τₐ φₐ r b
  let Ω : R'' ⊗[R] B →+* AddMonoidAlgebra F Γ := (AddMonoidAlgebra.mapRingHom Γ θ).comp cT.σ
  have hco : ∀ y d, (Ω y).coeff d = θ (cT.comp d y) := fun y d => AddMonoidAlgebra.coeff_mapRingHom ..
  have hmem : ∀ y, y ∈ RingHom.ker Ω ↔ ∀ d, θ (cT.comp d y) = 0 := by
    intro y
    rw [RingHom.mem_ker]
    constructor
    · intro h d
      rw [← hco, h]
      rfl
    · intro h
      ext d
      rw [hco, h d]
      rfl
  refine ⟨θ, RingHom.ker Ω, hθ, hmem, ?_, ?_, ?_⟩
  · intro y hy d
    rw [hmem]
    intro e
    by_cases hde : e = d
    · subst hde
      rw [cT.comp_self_of_isHom (cT.comp_isHom e y)]
      exact (hmem y).1 hy e
    · have : cT.comp e (cT.comp d y) = 0 := by
        have h := cT.comp_isHom d y
        change (cT.σ (cT.comp d y)).coeff e = 0
        rw [h, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg (Ne.symm hde)]
      rw [this, map_zero]
  · intro a ha
    have h0 := (hmem _).1 ha 0
    have e1 : cB.comp 0 (1 : B) = 1 := cB.comp_self_of_isHom (SDR3Orbit_isHom_one cB)
    change θ ((SDExist_bc R'' cB hcB).comp 0 (a ⊗ₜ 1)) = 0 at h0
    rw [SDExist_bc_comp, e1, hθ, map_one, mul_one] at h0
    exact (hτ a).1 h0
  · intro J hJ hlt
    obtain ⟨y, hyJ, hyI⟩ := SetLike.exists_of_lt hlt
    have hex : ∃ d, θ (cT.comp d y) ≠ 0 := by
      by_contra hn
      push Not at hn
      exact hyI ((hmem y).2 hn)
    obtain ⟨d, hd⟩ := hex
    have hexa : ∃ a, cB.comp d a ∉ I := by
      by_contra hn
      push Not at hn
      apply hd
      generalize y = z
      induction z using TensorProduct.induction_on with
      | zero => simp [Coact.comp]
      | add u v hu hv => rw [Coact.comp_add, map_add, hu, hv, add_zero]
      | tmul r a =>
        change θ ((SDExist_bc R'' cB hcB).comp d (r ⊗ₜ a)) = 0
        rw [SDExist_bc_comp, hθ, (hφ d _ (cB.comp_isHom d a)).2 (hn a), mul_zero]
    obtain ⟨a, ha⟩ := hexa
    obtain ⟨h, hh, b', hb'⟩ := exists_inv_of_homog hιB hI hIq hmax (cB.comp_isHom d a) ha
    let b := cB.comp (0 - d) b'
    have hab : cB.comp d a * b = algebraMap R B h := by
      have e0 : cB.comp 0 (algebraMap R B h) = algebraMap R B h :=
        cB.comp_self_of_isHom ((hιB.range _).2 ⟨h, rfl⟩)
      rw [← e0, hb', cB.comp_mul_of_isHom (cB.comp_isHom d a)]
    have hb : cB.IsHom (0 - d) b := cB.comp_isHom _ _
    have hφh : φ (algebraMap R B h) ≠ 0 := fun h0 =>
      hh (hIq h ((hφ 0 _ ((hιB.range _).2 ⟨h, rfl⟩)).1 h0))
    have hφb : φ b ≠ 0 := fun h0 => hφh (by rw [← hab, map_mul, h0, mul_zero])
    have hs : ∀ z : R'' ⊗[R] B, ∃ s : R'', cT.comp d z * ((1 : R'') ⊗ₜ[R] b) = s ⊗ₜ[R] (1 : B) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => exact ⟨0, by simp [Coact.comp]⟩
      | add u v hu hv =>
        obtain ⟨s, hs⟩ := hu
        obtain ⟨s', hs'⟩ := hv
        exact ⟨s + s', by rw [Coact.comp_add, add_mul, hs, hs', TensorProduct.add_tmul]⟩
      | tmul r x =>
        have hdeg : cB.IsHom 0 (cB.comp d x * b) := by
          have := (cB.comp_isHom d x).mul hb
          simpa using this
        obtain ⟨w, hw⟩ := (hιB.range _).1 hdeg
        refine ⟨w • r, ?_⟩
        change (SDExist_bc R'' cB hcB).comp d (r ⊗ₜ x) * _ = _
        rw [SDExist_bc_comp, Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← hw]
        change r ⊗ₜ[R] algebraMap R B w = _
        rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    obtain ⟨s, hs₁⟩ := hs y
    refine ⟨s, ?_, fun hsq => ?_⟩
    · rw [← hs₁]
      exact J.mul_mem_right _ (hJ y hyJ d)
    · have h0 : θ (s ⊗ₜ[R] (1 : B)) = 0 := by rw [hθ, (hτ s).2 hsq, zero_mul]
      rw [← hs₁, map_mul, hθ, map_one, one_mul] at h0
      exact (mul_ne_zero hd hφb) h0

end BaseChange

/-- **Stacks 00UD**, for rings and fields in one universe: `StacksFrontier/RingTheory/Etale/ResidueFieldExtension.lean`,
`Algebra.exists_etale_liesOver_residueFieldRingEquiv`. Stated as a hypothesis: that module has no built olean here. -/
def SDR3Orbit_Stacks00UD : Prop :=
  ∀ {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] (L : Type u) [Field L] [Algebra p.ResidueField L]
    [Module.Finite p.ResidueField L] [Algebra.IsSeparable p.ResidueField L],
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R') (p' : Ideal R') (_ : p'.IsPrime)
      (_ : p'.LiesOver p) (e : p'.ResidueField ≃+* L),
      (e : p'.ResidueField →+* L).comp (Ideal.ResidueField.map p p' (algebraMap R R') (p'.over_def p)) =
        algebraMap p.ResidueField L

/-- **Step 2.** The étale `R'` with a prime over `q` whose residue field is `κ'`, for `K` a residue field of `q`. -/
theorem SDR3Orbit_step2 (h00UD : SDR3Orbit_Stacks00UD.{u}) {A₀ K κ' : Type u} [CommRing A₀] [Field K] [Field κ']
    [Algebra K κ'] [Module.Finite K κ'] [Algebra.IsSeparable K κ'] {q : Ideal A₀} [q.IsPrime] (ρ : A₀ →+* K)
    (hρ : ∀ a, ρ a = 0 ↔ a ∈ q) (hsurj : ∀ k, ∃ r s, s ∉ q ∧ k * ρ s = ρ r) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra A₀ R') (_ : Algebra.Etale A₀ R') (P' : Ideal R') (_ : P'.IsPrime)
      (_ : P'.LiesOver q) (τ : R' →+* κ'), (∀ a, τ a = 0 ↔ a ∈ P') ∧
        ∀ a, τ (algebraMap A₀ R' a) = algebraMap K κ' (ρ a) := by
  let τ₀ : q.ResidueField →+* K := Ideal.ResidueField.lift q ρ (fun a ha => (hρ a).2 ha)
    (fun a ha => isUnit_iff_ne_zero.2 fun h0 => ha ((hρ a).1 h0))
  have hτ₀ : ∀ a, τ₀ (algebraMap A₀ _ a) = ρ a := fun a => Ideal.ResidueField.lift_algebraMap ..
  have hbij : Function.Bijective τ₀ := by
    refine ⟨τ₀.injective, fun k => ?_⟩
    obtain ⟨r, s, hs, he⟩ := hsurj k
    have hs0 : ρ s ≠ 0 := fun h => hs ((hρ s).1 h)
    refine ⟨algebraMap A₀ _ r * (algebraMap A₀ _ s)⁻¹, ?_⟩
    rw [map_mul, map_inv₀, hτ₀, hτ₀, ← he]
    field_simp
  let e₀ : q.ResidueField ≃+* K := RingEquiv.ofBijective τ₀ hbij
  letI : Algebra q.ResidueField κ' := ((algebraMap K κ').comp τ₀).toAlgebra
  have hcomm : ((RingEquiv.refl κ' : κ' ≃+* κ') : κ' →+* κ').comp (algebraMap K κ') =
      (algebraMap q.ResidueField κ').comp (e₀.symm : K →+* q.ResidueField) := by
    ext k
    change algebraMap K κ' k = algebraMap K κ' (τ₀ (e₀.symm k))
    congr 1
    exact (e₀.apply_symm_apply k).symm
  have hfin : Module.Finite q.ResidueField κ' :=
    Module.Finite.of_equiv_equiv e₀.symm (RingEquiv.refl κ') hcomm.symm
  have hsep : Algebra.IsSeparable q.ResidueField κ' :=
    Algebra.IsSeparable.of_equiv_equiv e₀.symm (RingEquiv.refl κ') hcomm.symm
  obtain ⟨R', _, _, hE, P', hP', hL, e, he⟩ := h00UD q κ'
  refine ⟨R', inferInstance, inferInstance, hE, P', hP', hL,
    (e : P'.ResidueField →+* κ').comp (algebraMap R' P'.ResidueField), fun a => ?_, fun a => ?_⟩
  · change e _ = 0 ↔ _
    rw [map_eq_zero_iff _ e.injective, Ideal.algebraMap_residueField_eq_zero]
  · have h1 := congrArg (fun k => k (algebraMap A₀ q.ResidueField a)) he
    simp only [RingHom.comp_apply] at h1
    rw [Ideal.ResidueField.map_algebraMap] at h1
    change e _ = _
    refine h1.trans ?_
    change algebraMap K κ' (τ₀ _) = _
    rw [hτ₀]

section Step1

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Γ P P₀ : Type u} [AddCommGroup Γ] [Countable Γ] [AddGroup.FG Γ]
  [AddCommMonoid P] [Countable P] [AddCommMonoid P₀] [Countable P₀]

/-- **Step 1.** For `x` invariant over `𝔸(P)_T` and `q` a point of `𝔸(P₀)_T`: the closed orbit `I`, a residue field `K` of
`q`, a finite separable `κ'/K`, a point `u₀` of a chart `U` over `V' = Spec κ'`, and the orbit point over `𝔸(L)_{V'}`, on
which `x` is `f ∘ s₀`, with `s₀ = pr ≫ u₀`. Site membership of `Spec κ'` is proved here. -/
theorem SDR3Orbit_step1 (hX : IsAlgebraicSpace B S hS X) (hfree : ∀ L : AddSubgroup Γ, Module.Free ℤ L) (δ : P →+ Γ)
    (j : P₀ →+ P) (hj : Function.Injective j) (hk : ∀ p, δ p = 0 ↔ p ∈ Set.range j) (T : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] (x : X.obj (op (specObj P T))) (hx : IsInvPt X δ x)
    (q : PrimeSpectrum (gRing P₀ T)) :
    ∃ (I : Ideal (gRing P T)) (K : Type u) (_ : Field K) (ρ : gRing P₀ T →+* K) (φ : gRing P T →+* K),
      (monCoact δ).IsHomIdeal I ∧ (∀ a, monι j _ a ∈ I → a ∈ q.asIdeal) ∧
      (∀ J, (monCoact δ).IsHomIdeal J → I < J → ∃ a, monι j _ a ∈ J ∧ a ∉ q.asIdeal) ∧
      (∀ a, φ (monι j _ a) = ρ a) ∧ (∀ a, ρ a = 0 ↔ a ∈ q.asIdeal) ∧ (∀ k, ∃ r s, s ∉ q.asIdeal ∧ k * ρ s = ρ r) ∧
      (∀ d a, (monCoact δ).IsHom d a → (φ a = 0 ↔ a ∈ I)) ∧
      ∃ (κ' : Type u) (_ : Field κ') (_ : Algebra K κ') (_ : Module.Finite K κ') (_ : Algebra.IsSeparable K κ')
        (L : AddSubgroup Γ) (V' : BigFppfOver B S hS) (_ : IsAffine ((BigFppfOver.toScheme B S hS).obj V'))
        (t' : V' ⟶ T) (c' : APt (fppfO B S hS) P (op V')) (hL : ∀ p : Multiplicative P, δ p.toAdd ∉ L → c' p = 0)
        (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ X) (u₀ : V' ⟶ U),
        (MorphismProperty.presheaf (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) f ∧
        f.app (op V') u₀ = X.map (specLift t' c').op x ∧
        X.map (specLift (specPr (SDR3Orbit_OM L) V' ≫ t') (SDR3Orbit_c₀ L δ c' hL)).op x =
          f.app (op (specObj (SDR3Orbit_OM L) V')) (specPr (SDR3Orbit_OM L) V' ≫ u₀) ∧
        L = AddSubgroup.closure {d | ∃ n : Multiplicative P,
          φ (AddMonoidAlgebra.single n.toAdd 1) ≠ 0 ∧ δ n.toAdd = d} ∧
        ∃ iV' : (SCH).obj V' ≅ Spec (.of κ'),
          iV'.inv ≫ (SCH).map t' = sp ((algebraMap K κ').comp (φ.comp (algebraMap _ (gRing P T)))) ≫
            ((SCH).obj T).isoSpec.inv ∧
          ∀ n : Multiplicative P, iV'.inv.appTop.hom (c' n) =
            (Scheme.ΓSpecIso (.of κ')).inv.hom (algebraMap K κ' (φ (AddMonoidAlgebra.single n.toAdd 1))) := by
  classical
  have hι := monCoact_isInv (R := Γ((SCH).obj T, ⊤)) (δ := δ) hj hk
  obtain ⟨I, hI, hIq, hmax⟩ := exists_maximal_homIdeal (monCoact (R := Γ((SCH).obj T, ⊤)) δ) hι.inj q.asIdeal
  obtain ⟨K, _, ρ, φ, hφρ, hρ, hsurj, hφ⟩ := SDR3Orbit_closedOrbit hι hI hIq hmax hfree
  refine ⟨I, K, inferInstance, ρ, φ, hI, hIq, hmax, hφρ, hρ, hsurj, hφ, ?_⟩
  -- site membership of `Spec K`
  have hA₀ : #(gRing P₀ T) < B.cutoff := contains_iff.1 (contains_spec P₀ T)
  have hK : #K < B.cutoff := by
    have hs : Function.Surjective (fun z : gRing P₀ T × gRing P₀ T => ρ z.1 * (ρ z.2)⁻¹) := by
      intro k
      obtain ⟨r, s, hs, he⟩ := hsurj k
      have hs0 : ρ s ≠ 0 := fun h => hs ((hρ s).1 h)
      exact ⟨(r, s), by simp only; rw [← he]; field_simp⟩
    refine (mk_le_of_surjective hs).trans_lt ?_
    rw [mk_prod, lift_id]
    exact mul_lt_of_lt B.aleph0_lt_cutoff.le hA₀ hA₀
  let m : Spec (.of K) ⟶ (SCH).obj T :=
    Spec.map (CommRingCat.ofHom (φ.comp (algebraMap _ (gRing P T)))) ≫ ((SCH).obj T).isoSpec.inv
  let V : BigFppfOver B S hS := siteObject B S hS (contains_iff.2 hK) (m ≫ T.hom.hom)
  haveI hVa : IsAffine ((BigFppfOver.toScheme B S hS).obj V) := inferInstanceAs (IsAffine (Spec _))
  let t : V ⟶ T := overHom m rfl
  let mono : Multiplicative P →* K :=
    { toFun := fun n => φ (AddMonoidAlgebra.single n.toAdd 1)
      map_one' := by
        have : AddMonoidAlgebra.single (1 : Multiplicative P).toAdd (1 : Γ((SCH).obj T, ⊤)) = 1 := rfl
        rw [this, map_one]
      map_mul' := fun a b => by
        rw [← map_mul, AddMonoidAlgebra.single_mul_single, one_mul]
        rfl }
  let c₁ : APt (fppfO B S hS) P (op V) :=
    ((Scheme.ΓSpecIso (.of K)).inv.hom : K →+* _).toMonoidHom.comp mono
  let y₀ := X.map (specLift t c₁).op x
  obtain ⟨U, f, hsu, he⟩ := hX.exists_atlas
  obtain ⟨W', p, s, hpe, hps, hfs⟩ := SDR3Orbit_chart f he hsu y₀
  obtain ⟨w, -⟩ := hps.surj (show (SCH).obj V from (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K))
  let fp : (SCH).obj W' ⟶ Spec (.of K) := (SCH).map p
  haveI : Etale fp := hpe
  obtain ⟨κ', _, _, h1, h2, e, heq⟩ := SDR3Orbit_residue (K := K) fp w
  have hκ : #κ' < B.cutoff := by
    have halg : Algebra.IsAlgebraic K κ' := inferInstance
    have he : #κ' = #{x : κ' // IsAlgebraic K x} :=
      mk_congr (Equiv.subtypeUnivEquiv fun x => halg.isAlgebraic x).symm
    rw [he]
    exact (Algebraic.cardinalMk_le_max K κ').trans_lt (max_lt hK B.aleph0_lt_cutoff)
  let mb : Spec (.of κ') ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K κ'))
  let V' : BigFppfOver B S hS := siteObject B S hS (contains_iff.2 hκ) (mb ≫ V.hom.hom)
  haveI hVa' : IsAffine ((BigFppfOver.toScheme B S hS).obj V') := inferInstanceAs (IsAffine (Spec _))
  let b : V' ⟶ V := overHom mb rfl
  let a : V' ⟶ W' := overHom e (by
    change e ≫ W'.hom.hom = mb ≫ V.hom.hom
    have hw : (SCH).map p ≫ V.hom.hom = W'.hom.hom := site_w p
    rw [← hw, ← Category.assoc, heq])
  have hab : a ≫ p = b := toScheme_map_injective (by
    rw [Functor.map_comp]; exact heq)
  let c' := APt.res b.op c₁
  have hc'0 : ∀ n, mono n = 0 → c' n = 0 := fun n hn => by
    change ((fppfO B S hS).map b.op).hom ((Scheme.ΓSpecIso (.of K)).inv.hom (mono n)) = 0
    rw [hn, map_zero]
    exact map_zero _
  let L : AddSubgroup Γ := AddSubgroup.closure {d | ∃ n, mono n ≠ 0 ∧ δ n.toAdd = d}
  have hL : ∀ p : Multiplicative P, δ p.toAdd ∉ L → c' p = 0 := fun n hn => hc'0 n (by
    by_contra h0
    exact hn (AddSubgroup.subset_closure ⟨n, h0, rfl⟩))
  have hb : b ≫ specLift t c₁ = specLift (b ≫ t) c' := SDR3Orbit_comp_specLift _ _ _
  let u₀ : V' ⟶ U := a ≫ s
  have hu : f.app (op V') u₀ = X.map (specLift (b ≫ t) c').op x := by
    have h1 : f.app (op V') u₀ = X.map a.op (f.app (op W') s) := NatTrans.naturality_apply f a.op s
    rw [h1, hfs, ← hb, ← hab]
    simp only [y₀, op_comp, Functor.map_comp_apply, Category.assoc]
  refine ⟨κ', inferInstance, inferInstance, h1, h2, L, V', hVa', b ≫ t, c', hL, U, f, u₀, he, hu, ?_⟩
  have hF : Presieve.IsSheaf (BigFppfOver.topology B S hS) X := (isSheaf_iff_isSheaf_of_type _ _).1 hX.isSheaf
  refine ⟨?_, rfl, Iso.refl _, ?_, fun n => ?_⟩
  · rw [SDR3Orbit_const L δ c' hF x hx (b ≫ t) hL, ← hu]
    exact (NatTrans.naturality_apply f (specPr (SDR3Orbit_OM L) V').op u₀).symm
  · change 𝟙 _ ≫ mb ≫ m = _
    rw [Category.id_comp, ← Category.assoc]
    change (Spec.map _ ≫ Spec.map _) ≫ _ = _
    rw [← Spec.map_comp]
    rfl
  · exact appTop_sp_inv (algebraMap K κ') (mono n)

end Step1

end AlgMag.SD

#print axioms AlgMag.SD.SDR3Orbit_bcOrbit
#print axioms AlgMag.SD.SDR3Orbit_step2
#print axioms AlgMag.SD.SDR3Orbit_step1
