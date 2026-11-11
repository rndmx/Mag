/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartQSUnique

/-!
# §4 for quasi-separated targets

The statements of `AlgMag/ChartEffectiveMain.lean` that took `X` separated, proved for `X` any algebraic
space with the same proofs, by `AlgMag.ChartQS.eq_of_agree_basicOpen_of_agree_thickening`.
Not included: `thm41_unique`, whose non-equivariant form is false without separatedness.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Space

universe u

namespace AlgMag.ChartQS

open ChartMain

set_option linter.unusedSectionVars false

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

set_option maxHeartbeats 1000000 in
/-- **§4, Remark: the overlap.** Let `T` be affine with `C = Γ(T)` noetherian, `a` an ideal of `C`
and `p : Y → T` flat with `Y` affine, with `C → Γ(Y)/a^kΓ(Y)` onto. If `θ ∈ X(Y)` is such that, on
each `D(g)`, `g ∈ a`, its two pullbacks to `Y ×_T Y` agree, they agree. No separatedness. -/
theorem eq_on_kernelPair (hX : IsAlgebraicSpace B S hS X) {T Y : BigFppfOver B S hS}
    [IsAffine ((SCH).obj T)] [IsAffine ((SCH).obj Y)] (p : Y ⟶ T)
    [IsNoetherianRing Γ((SCH).obj T, ⊤)] (a : Ideal Γ((SCH).obj T, ⊤))
    (hp : Flat ((SCH).map p))
    (hsurj : ∀ (k : ℕ) (r : Γ((SCH).obj Y, ⊤)), ∃ c : Γ((SCH).obj T, ⊤),
      r - ((SCH).map p).appTop.hom c ∈ (a ^ k).map ((SCH).map p).appTop.hom)
    (θ : X.obj (op Y))
    (hopen : ∀ g ∈ a, ∀ ⦃W : BigFppfOver B S hS⦄ (g₁ g₂ : W ⟶ Y), g₁ ≫ p = g₂ ≫ p →
      (∀ y : (SCH).obj W, (SCH).map (g₁ ≫ p) y ∈ ((SCH).obj T).basicOpen g) →
      X.map g₁.op θ = X.map g₂.op θ)
    ⦃W : BigFppfOver B S hS⦄ (g₁ g₂ : W ⟶ Y) (hg : g₁ ≫ p = g₂ ≫ p) :
    X.map g₁.op θ = X.map g₂.op θ := by
  have : PreservesLimitsOfShape WalkingCospan (SCH) := inferInstance
  let P := pullback p p
  let pr₁ : P ⟶ Y := pullback.fst p p
  let pr₂ : P ⟶ Y := pullback.snd p p
  have hpr : pr₁ ≫ p = pr₂ ≫ p := pullback.condition
  have hPaff : IsAffine ((SCH).obj P) := by
    have : IsAffine (pullback ((SCH).map p) ((SCH).map p)) := inferInstance
    exact .of_isIso (pullbackComparison (SCH) p p)
  let π := (SCH).map (pr₁ ≫ p)
  have hπflat : Flat π := by
    have e : π = pullbackComparison (SCH) p p ≫ pullback.fst _ _ ≫ (SCH).map p := by
      simp only [π, pr₁, Functor.map_comp]
      rw [← Category.assoc, pullbackComparison_comp_fst]
    rw [e]
    infer_instance
  let _ : Algebra Γ((SCH).obj T, ⊤) Γ((SCH).obj P, ⊤) := π.appTop.hom.toAlgebra
  have hflat : Module.Flat Γ((SCH).obj T, ⊤) Γ((SCH).obj P, ⊤) :=
    (HasRingHomProperty.iff_of_isAffine (P := @Flat)).mp hπflat
  have halg : ∀ c, algebraMap Γ((SCH).obj T, ⊤) Γ((SCH).obj P, ⊤) c = π.appTop.hom c := fun _ => rfl
  have key : X.map pr₁.op θ = X.map pr₂.op θ := by
    refine eq_of_agree_basicOpen_of_agree_thickening hX P a (a : Set _)
      (Ideal.span_eq a).symm _ _ ?_ ?_
    · intro g hg
      rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp]
      refine hopen g hg _ _ (by simp only [Category.assoc, hpr]) fun y => ?_
      have hm := mem_basicOpen_of_range π g (((SCH).obj P).basicOpen (π.appTop.hom g)).ι
        (by rw [Scheme.Opens.range_ι]) y
      have e : (SCH).map ((Chart.immι P ((SCH).obj P |>.basicOpen
          (algebraMap Γ((SCH).obj T, ⊤) Γ((SCH).obj P, ⊤) g)).ι ≫ pr₁) ≫ p) =
          (SCH).map (Chart.immι P ((SCH).obj P |>.basicOpen
            (algebraMap Γ((SCH).obj T, ⊤) Γ((SCH).obj P, ⊤) g)).ι) ≫ π := by
        simp only [π, Category.assoc, Functor.map_comp]
      rw [e, Scheme.Hom.comp_apply]
      exact hm
    · intro k
      rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp]
      let J := (a ^ k).map (algebraMap Γ((SCH).obj T, ⊤) Γ((SCH).obj P, ⊤))
      have he : (Chart.immι P (Chart.closedι ((SCH).obj P) J)) ≫ pr₁ =
          (Chart.immι P (Chart.closedι ((SCH).obj P) J)) ≫ pr₂ := by
        refine siteExt (?_)
        simp only [Functor.map_comp]
        refine hom_eq_of_quot_surj _ _ ((SCH).map p) ?_ (a ^ k) (fun x hx => ?_) (hsurj k)
        · simp only [Category.assoc, ← Functor.map_comp, hpr]
        · have hx' := appTop_comp_eq_zero ((SCH).map (Chart.immι P (Chart.closedι ((SCH).obj P) J)))
            π x (closedι_appTop_of_mem J (Ideal.mem_map_of_mem _ hx))
          have e : ((SCH).map (Chart.immι P (Chart.closedι ((SCH).obj P) J)) ≫ (SCH).map pr₁) ≫
              (SCH).map p = (SCH).map (Chart.immι P (Chart.closedι ((SCH).obj P) J)) ≫ π := by
            simp only [π, Category.assoc, Functor.map_comp]
          rw [e]
          exact hx'
      rw [he]
  let m : W ⟶ P := pullback.lift g₁ g₂ hg
  have e₁ : m ≫ pr₁ = g₁ := pullback.lift_fst _ _ _
  have e₂ : m ≫ pr₂ = g₂ := pullback.lift_snd _ _ _
  rw [← e₁, ← e₂, op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, key]

/-- **Bhatt, Theorem 1.4(1), restricted form**, over `S` (§4, Remark): `T` affine noetherian,
`U → T` the open complement of `V(a)`, `Y → T` flat from an affine, covering `V(a)` and with
`C → Γ(Y)/a^k` onto. Then `T` is the pushout of `U` and `Y`, for maps to any algebraic space. -/
theorem existsUnique_pushout (hX : IsAlgebraicSpace B S hS X) {T U Y : BigFppfOver B S hS}
    [IsAffine ((SCH).obj T)] [IsAffine ((SCH).obj Y)] (j : U ⟶ T) (p : Y ⟶ T)
    [IsNoetherianRing Γ((SCH).obj T, ⊤)] (a : Ideal Γ((SCH).obj T, ⊤))
    (hj : IsOpenImmersion ((SCH).map j))
    (hjr : ∀ x : (SCH).obj T, x ∈ Set.range ((SCH).map j) ↔ ∃ g ∈ a, x ∈ ((SCH).obj T).basicOpen g)
    (hp : Flat ((SCH).map p))
    (hcov : ∀ x : (SCH).obj T, x ∉ Set.range ((SCH).map j) → x ∈ Set.range ((SCH).map p))
    (hsurj : ∀ (k : ℕ) (r : Γ((SCH).obj Y, ⊤)), ∃ c : Γ((SCH).obj T, ⊤),
      r - ((SCH).map p).appTop.hom c ∈ (a ^ k).map ((SCH).map p).appTop.hom)
    (τ : X.obj (op U)) (θ : X.obj (op Y))
    (huv : ∀ ⦃W : BigFppfOver B S hS⦄ (g₁ : W ⟶ U) (g₂ : W ⟶ Y), g₁ ≫ j = g₂ ≫ p →
      X.map g₁.op τ = X.map g₂.op θ) :
    ∃! φ : X.obj (op T), X.map j.op φ = τ ∧ X.map p.op φ = θ := by
  let Z : Fin 2 → BigFppfOver B S hS := Fin.cons U (fun _ => Y)
  let q : ∀ i, Z i ⟶ T := fun i => Fin.cases (motive := fun i => Z i ⟶ T) j (fun _ => p) i
  let x : ∀ i, X.obj (op (Z i)) := fun i =>
    Fin.cases (motive := fun i => X.obj (op (Z i))) τ (fun _ => θ) i
  have hN₀ : TopologicalSpace.NoetherianSpace ((SCH).obj T) :=
    (Scheme.homeoOfIso ((SCH).obj T).isoSpec).isInducing.noetherianSpace
  have hc : Presieve.ofArrows (fun i => (SCH).obj (Z i)) (fun i => (SCH).map (q i)) ∈
      Scheme.fpqcPrecoverage ((SCH).obj T) := by
    refine ChartSplit.ofArrows_two_mem_fpqcPrecoverage _ _ ?_ ?_ ?_
    · rw [Fin.forall_fin_two]
      exact ⟨inferInstanceAs (Flat ((SCH).map j)), hp⟩
    · rw [Fin.forall_fin_two]
      refine ⟨?_, inferInstanceAs (QuasiCompact ((SCH).map p))⟩
      have hN : TopologicalSpace.NoetherianSpace ((SCH).obj U) :=
        hj.base_open.isInducing.noetherianSpace
      exact quasiCompact_of_noetherianSpace_source ((SCH).map j)
    · intro y
      by_cases hy : y ∈ Set.range ((SCH).map j)
      · exact ⟨0, hy⟩
      · exact ⟨1, hcov y hy⟩
  have hjm : Mono j := (SCH).mono_of_mono_map inferInstance
  have hopen : ∀ g ∈ a, ∀ ⦃W : BigFppfOver B S hS⦄ (g₁ g₂ : W ⟶ Y), g₁ ≫ p = g₂ ≫ p →
      (∀ y : (SCH).obj W, (SCH).map (g₁ ≫ p) y ∈ ((SCH).obj T).basicOpen g) →
      X.map g₁.op θ = X.map g₂.op θ := by
    intro g hg W g₁ g₂ h hy
    obtain ⟨l, hl⟩ := exists_factor_open j (g₁ ≫ p) (by
      rintro _ ⟨y, rfl⟩
      exact (hjr _).2 ⟨g, hg, hy y⟩)
    exact (huv l g₁ hl).symm.trans (huv l g₂ (hl.trans h))
  have hcompat : ∀ i k ⦃W : BigFppfOver B S hS⦄ (g₁ : W ⟶ Z i) (g₂ : W ⟶ Z k),
      g₁ ≫ q i = g₂ ≫ q k → X.map g₁.op (x i) = X.map g₂.op (x k) := by
    rw [Fin.forall_fin_two]
    constructor <;> rw [Fin.forall_fin_two] <;> constructor
    · intro W g₁ g₂ h
      rw [(cancel_mono j).1 h]
    · intro W g₁ g₂ h
      exact huv g₁ g₂ h
    · intro W g₁ g₂ h
      exact (huv g₂ g₁ h.symm).symm
    · intro W g₁ g₂ h
      exact eq_on_kernelPair hX p a hp hsurj θ hopen g₁ g₂ h
  obtain ⟨φ, hφ, huniq⟩ := existsUnique_glue hX Z q hc x hcompat
  refine ⟨φ, ⟨hφ 0, hφ 1⟩, ?_⟩
  rintro φ' ⟨h₁, h₂⟩
  refine huniq φ' fun i => ?_
  revert i
  rw [Fin.forall_fin_two]
  exact ⟨h₁, h₂⟩

section Equivariance

variable {M : Type u} [AddCommGroup M] [AddMonoid.FG M] {T : BigFppfOver B S hS}
  [hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)] (actT : AAction (fppfO B S hS) M (yoneda.obj T))
  (actX : AAction (fppfO B S hS) M X)

set_option maxHeartbeats 1000000 in
/-- **§4, "φ is equivariant".** If `φ ∈ X(T)` restricts to equivariant points on each `D(g)`, `g`
homogeneous generators of `a`, and on each `V(a^k)`, then `φ` is equivariant. This is Lemma 4.5 with
`R = O(G) ⊗ C`. -/
theorem equivariant_of_agree (hX : IsAlgebraicSpace B S hS X)
    [IsNoetherianRing Γ((SCH).obj T, ⊤)] (a : Ideal Γ((SCH).obj T, ⊤))
    (gens : Set Γ((SCH).obj T, ⊤)) (hgens : a = Ideal.span gens)
    (hhom : ∀ g ∈ gens, ∃ d, g ∈ homog actT d)
    (hI : ∀ k, ∀ x ∈ a ^ k, ∀ d, (coact actT x).coeff d ∈ a ^ k) (φ : X.obj (op T))
    (hD : ∀ g ∈ gens, EquivAlong actT actX (Chart.immι T ((SCH).obj T |>.basicOpen g).ι)
      (X.map (Chart.immι T ((SCH).obj T |>.basicOpen g).ι).op φ))
    (hV : ∀ k, EquivAlong actT actX (Chart.immι T (Chart.closedι ((SCH).obj T) (a ^ k)))
      (X.map (Chart.immι T (Chart.closedι ((SCH).obj T) (a ^ k))).op φ))
    {W : BigFppfOver B S hS} (t : W ⟶ T) (h : Multiplicative M →* Γ((SCH).obj W, ⊤)) :
    X.map (smulAt actT h t).op φ = actX.smul (F := X) (U := op W) h (X.map t.op φ) := by
  let Tm := spObj T (ι1 T (M := M)) contains1
  let pr := spToT T (ι1 T (M := M)) contains1
  let ρ : Γ((SCH).obj T, ⊤) →+* Γ((SCH).obj Tm, ⊤) := ((SCH).map pr).appTop.hom
  let _ : Algebra Γ((SCH).obj T, ⊤) Γ((SCH).obj Tm, ⊤) := ρ.toAlgebra
  have hρ : ρ = (spSec T (ι1 T (M := M)) contains1).comp (ι1 T) :=
    RingHom.ext fun x => spToT_appTop T _ _ x
  have hflat : Module.Flat Γ((SCH).obj T, ⊤) Γ((SCH).obj Tm, ⊤) := by
    have f1 : (ι1 T (M := M)).Flat := by
      have h0 : Module.Flat (RT T) (AddMonoidAlgebra (RT T) M) := inferInstance
      exact (RingHom.flat_algebraMap_iff (R := RT T) (S := AddMonoidAlgebra (RT T) M)).2 h0
    have f2 := RingHom.Flat.of_bijective (spSec_bijective T (ι1 T (M := M)) contains1)
    have : ρ.Flat := by rw [hρ]; exact RingHom.Flat.comp f1 f2
    exact this
  have key : X.map (univMap actT).op φ =
      actX.smul (F := X) (U := op Tm) univPt1 (X.map pr.op φ) := by
    refine eq_of_agree_basicOpen_of_agree_thickening hX Tm a gens hgens _ _ ?_ ?_
    · intro g hg
      obtain ⟨d, hd⟩ := hhom g hg
      let i := Chart.immι Tm (((SCH).obj Tm).basicOpen (ρ g)).ι
      have : IsOpenImmersion ((SCH).map (Chart.immι T ((SCH).obj T |>.basicOpen g).ι)) :=
        inferInstanceAs (IsOpenImmersion (Scheme.Opens.ι _))
      have hr : Set.range ((SCH).map (Chart.immι T ((SCH).obj T |>.basicOpen g).ι)) =
          ((SCH).obj T).basicOpen g := Scheme.Opens.range_ι _
      have hm : ∀ y, (SCH).map (i ≫ pr) y ∈ ((SCH).obj T).basicOpen g := fun y => by
        have hm := mem_basicOpen_of_range ((SCH).map pr) g (((SCH).obj Tm).basicOpen (ρ g)).ι
          (by rw [Scheme.Opens.range_ι]) y
        rw [Functor.map_comp, Scheme.Hom.comp_apply]
        exact hm
      obtain ⟨s, hs⟩ := exists_factor_open (Chart.immι T ((SCH).obj T |>.basicOpen g).ι) (i ≫ pr) (by
        rw [hr]; rintro _ ⟨y, rfl⟩; exact hm y)
      have e₀ : i ≫ univMap actT = smulAt actT
          (secPt ((SCH).map i).appTop.hom (univPt1 (U := T))) (i ≫ pr) := comp_smulAt actT i _ _
      obtain ⟨s', hs'⟩ := exists_factor_open (Chart.immι T ((SCH).obj T |>.basicOpen g).ι)
        (i ≫ univMap actT) (by
          rw [hr]; rintro _ ⟨y, rfl⟩
          rw [e₀]
          exact (mem_basicOpen_smul_iff actT _ _ hd y).2 (hm y))
      exact agree_of_factor actT actX φ i _ (hD g hg) s s' hs hs'
    · intro k
      let J := (a ^ k).map ρ
      let i := Chart.immι Tm (Chart.closedι ((SCH).obj Tm) J)
      have ht : ∀ x ∈ a ^ k, ((SCH).map (i ≫ pr)).appTop.hom x = 0 := fun x hx =>
        appTop_comp_eq_zero ((SCH).map i) ((SCH).map pr) x
          (closedι_appTop_of_mem J (Ideal.mem_map_of_mem _ hx))
      obtain ⟨s, hs⟩ := exists_factor_closed (i ≫ pr) (a ^ k) ht
      have e₀ : i ≫ univMap actT = smulAt actT
          (secPt ((SCH).map i).appTop.hom (univPt1 (U := T))) (i ≫ pr) := comp_smulAt actT i _ _
      obtain ⟨s', hs'⟩ := exists_factor_closed (i ≫ univMap actT) (a ^ k) (fun x hx => by
        rw [e₀]
        exact appTop_smul_eq_zero actT _ _ _ (hI k) ht hx)
      exact agree_of_factor actT actX φ i _ (hV k) s s' hs hs'
  have hψ : (evalAt ((SCH).map t).appTop.hom h).comp (ι1 T (M := M)) = ((SCH).map t).appTop.hom :=
    RingHom.ext fun b => evalAt_ι _ _ b
  obtain ⟨τ, hτ₁, hτ₂⟩ := exists_spLift (R' := R1 T M) (ι1 T) contains1 t _ hψ
  have hres : secPt ((SCH).map τ).appTop.hom (univPt1 (U := T)) = h := MonoidHom.ext fun m => by
    refine (hτ₂ _).trans ?_
    refine (evalAt_single _ _ (Multiplicative.toAdd m) 1).trans ?_
    rw [map_one, one_mul]
    rfl
  rw [smulAt_eq_comp actT t h τ hτ₁ hres, op_comp, Functor.map_comp_apply, key]
  refine (actX.map_smul τ.op _ _).trans ?_
  have e : X.map τ.op (X.map pr.op φ) = X.map t.op φ := by
    rw [← Functor.map_comp_apply, ← op_comp, hτ₁]
  rw [e]
  exact congrArg (fun k => actX.smul (F := X) (U := op W) k (X.map t.op φ)) hres

set_option maxHeartbeats 2000000 in
/-- **The gluing of Theorem 4.1, existence** (§4 "Glue", Bhatt Theorem 1.1, Remark, and the checks
after Lemma 4.5). The open and closed strata provide `τ` and `χ`; `Y = Spec Ĉ` is the `a`-adic
completion (only its properties are used), and `hθ` is the compatibility on `V = Y \ V(a)`. -/
theorem exists_glue (hX : IsAlgebraicSpace B S hS X)
    (hB : NoetherianAlgebraization X)
    [IsNoetherianRing Γ((SCH).obj T, ⊤)] (a : Ideal Γ((SCH).obj T, ⊤))
    (gens : Set Γ((SCH).obj T, ⊤)) (hgens : a = Ideal.span gens)
    (hhom : ∀ g ∈ gens, ∃ d, g ∈ homog actT d)
    (hI : ∀ k, ∀ x ∈ a ^ k, ∀ d, (coact actT x).coeff d ∈ a ^ k)
    {U Y : BigFppfOver B S hS} [IsAffine ((SCH).obj Y)]
    [IsNoetherianRing Γ((SCH).obj Y, ⊤)] (j : U ⟶ T) (p : Y ⟶ T)
    (hj : IsOpenImmersion ((SCH).map j))
    (hjr : ∀ x : (SCH).obj T, x ∈ Set.range ((SCH).map j) ↔ ∃ g ∈ a, x ∈ ((SCH).obj T).basicOpen g)
    (hp : Flat ((SCH).map p))
    (hcov : ∀ x : (SCH).obj T, x ∉ Set.range ((SCH).map j) → x ∈ Set.range ((SCH).map p))
    (hsurj : ∀ (k : ℕ) (r : Γ((SCH).obj Y, ⊤)), ∃ c : Γ((SCH).obj T, ⊤),
      r - ((SCH).map p).appTop.hom c ∈ (a ^ k).map ((SCH).map p).appTop.hom)
    (hinj : ∀ (k : ℕ) (c : Γ((SCH).obj T, ⊤)),
      ((SCH).map p).appTop.hom c ∈ (a ^ k).map ((SCH).map p).appTop.hom → c ∈ a ^ k)
    [IsAdicComplete (a.map ((SCH).map p).appTop.hom) Γ((SCH).obj Y, ⊤)]
    (τ : X.obj (op U)) (hτ : EquivAlong actT actX j τ)
    (χ : ∀ k, X.obj (op (Chart.immObj T (Chart.closedι ((SCH).obj T) (a ^ k)))))
    (hχ : ∀ k, EquivAlong actT actX (Chart.immι T (Chart.closedι ((SCH).obj T) (a ^ k))) (χ k))
    (hχc : ∀ (n m : ℕ) (e : Chart.immObj T (Chart.closedι ((SCH).obj T) (a ^ n)) ⟶
        Chart.immObj T (Chart.closedι ((SCH).obj T) (a ^ m))),
        e ≫ Chart.immι T _ = Chart.immι T _ → X.map e.op (χ m) = χ n)
    (hθ : ∀ θ : X.obj (op Y),
      (∀ (k : ℕ) (W : BigFppfOver B S hS) (i : W ⟶ Y)
        (s : W ⟶ Chart.immObj T (Chart.closedι ((SCH).obj T) (a ^ k))),
        s ≫ Chart.immι T _ = i ≫ p → X.map i.op θ = X.map s.op (χ k)) →
      ∀ ⦃W : BigFppfOver B S hS⦄ (g₁ : W ⟶ U) (g₂ : W ⟶ Y), g₁ ≫ j = g₂ ≫ p →
        X.map g₁.op τ = X.map g₂.op θ) :
    ∃ φ : X.obj (op T), X.map j.op φ = τ ∧
      (∀ k, X.map (Chart.immι T (Chart.closedι ((SCH).obj T) (a ^ k))).op φ = χ k) ∧
      ∀ {W : BigFppfOver B S hS} (t : W ⟶ T) (h : Multiplicative M →* Γ((SCH).obj W, ⊤)),
        X.map (smulAt actT h t).op φ = actX.smul (F := X) (U := op W) h (X.map t.op φ) := by
  have hjm : Mono j := (SCH).mono_of_mono_map inferInstance
  obtain ⟨θ, hθk⟩ := exists_theta hB p a hinj χ hχc
  obtain ⟨φ, ⟨hφj, hφp⟩, -⟩ := existsUnique_pushout hX j p a hj hjr hp hcov hsurj τ θ (hθ θ hθk)
  have hφk : ∀ k, X.map (Chart.immι T (Chart.closedι ((SCH).obj T) (a ^ k))).op φ = χ k := by
    intro k
    obtain ⟨σ, hσ⟩ := exists_section_of_quot p (a ^ k) (hsurj k) (hinj k)
    have := hθk k _ σ (𝟙 _) (by rw [Category.id_comp, hσ])
    rw [CategoryTheory.op_id, FunctorToTypes.map_id_apply] at this
    rw [← this, ← hφp, ← Functor.map_comp_apply, ← op_comp, hσ]
  refine ⟨φ, hφj, hφk, fun t h => ?_⟩
  refine equivariant_of_agree actT actX hX a gens hgens hhom hI φ (fun g hg => ?_) (fun k => ?_) t h
  · have hga : g ∈ a := by rw [hgens]; exact Ideal.subset_span hg
    have : IsOpenImmersion ((SCH).map j) := hj
    obtain ⟨l, hl⟩ := exists_factor_open j (Chart.immι T ((SCH).obj T |>.basicOpen g).ι) (by
      rintro _ ⟨y, rfl⟩
      exact (hjr _).2 ⟨g, hga, y.2⟩)
    have e : X.map (Chart.immι T ((SCH).obj T |>.basicOpen g).ι).op φ = X.map l.op τ := by
      rw [← hφj, ← Functor.map_comp_apply, ← op_comp, hl]
    rw [e]
    exact EquivAlong.of_factor actT actX hτ l hl
  · rw [hφk]
    exact hχ k

set_option maxHeartbeats 1000000 in
lemma restrict_aux (hX : IsAlgebraicSpace B S hS X)
    {U E : BigFppfOver B S hS} [IsAffine ((SCH).obj E)] (j : U ⟶ T)
    (hj : IsOpenImmersion ((SCH).map j)) (ι : E ⟶ T) (a : Ideal Γ((SCH).obj T, ⊤))
    (hjr : ∀ x : (SCH).obj T, x ∈ Set.range ((SCH).map j) ↔ ∃ g ∈ a, x ∈ ((SCH).obj T).basicOpen g)
    [IsNoetherianRing Γ((SCH).obj E, ⊤)]
    (φ : X.obj (op T)) (τ : X.obj (op U)) (hφj : X.map j.op φ = τ)
    (χ : ∀ k, X.obj (op (Chart.immObj T (Chart.closedι ((SCH).obj T) (a ^ k)))))
    (hφk : ∀ k, X.map (Chart.immι T (Chart.closedι ((SCH).obj T) (a ^ k))).op φ = χ k)
    (x : X.obj (op E))
    (hτx : ∀ ⦃W : BigFppfOver B S hS⦄ (g₁ : W ⟶ U) (g₂ : W ⟶ E),
      g₁ ≫ j = g₂ ≫ ι → X.map g₁.op τ = X.map g₂.op x)
    (hχx : ∀ (k : ℕ) ⦃W : BigFppfOver B S hS⦄
      (g₁ : W ⟶ Chart.immObj T (Chart.closedι ((SCH).obj T) (a ^ k))) (g₂ : W ⟶ E),
      g₁ ≫ Chart.immι T _ = g₂ ≫ ι → X.map g₁.op (χ k) = X.map g₂.op x) :
    X.map ι.op φ = x := by
  have hd : ∀ (W : BigFppfOver B S hS) (i : W ⟶ E), (∃ l : W ⟶ U, l ≫ j = i ≫ ι) →
      X.map i.op (X.map ι.op φ) = X.map i.op x := by
    rintro W i ⟨l, hl⟩
    have e : X.map i.op (X.map ι.op φ) = X.map l.op τ := by
      rw [← hφj, ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, hl]
    exact e.trans (hτx l i hl)
  have hc : ∀ (k : ℕ) (W : BigFppfOver B S hS) (i : W ⟶ E),
      (∃ s : W ⟶ Chart.immObj T (Chart.closedι ((SCH).obj T) (a ^ k)), s ≫ Chart.immι T _ = i ≫ ι) →
      X.map i.op (X.map ι.op φ) = X.map i.op x := by
    rintro k W i ⟨s, hs⟩
    have e : X.map i.op (X.map ι.op φ) = X.map s.op (χ k) := by
      rw [← hφk, ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, hs]
    exact e.trans (hχx k s i hs)
  refine eq_of_agree_basicOpen_of_agree_thickening (C := Γ((SCH).obj E, ⊤)) hX E
    (a.map ((SCH).map ι).appTop.hom) (((SCH).map ι).appTop.hom '' (a : Set _)) rfl _ _ ?_ ?_
  · rintro _ ⟨g, hg, rfl⟩
    refine hd _ _ ?_
    have : IsOpenImmersion ((SCH).map j) := hj
    refine exists_factor_open j _ ?_
    rintro _ ⟨y, rfl⟩
    refine (hjr _).2 ⟨g, hg, ?_⟩
    have hm := mem_basicOpen_of_range ((SCH).map ι) g
      (((SCH).obj E).basicOpen (((SCH).map ι).appTop.hom g)).ι (by rw [Scheme.Opens.range_ι]) y
    rw [Functor.map_comp, Scheme.Hom.comp_apply]
    exact hm
  · intro k
    have hV : ∀ J : Ideal Γ((SCH).obj E, ⊤), (∀ z ∈ a ^ k, ((SCH).map ι).appTop.hom z ∈ J) →
        ∃ s : Chart.immObj E (Chart.closedι ((SCH).obj E) J) ⟶
          Chart.immObj T (Chart.closedι ((SCH).obj T) (a ^ k)),
          s ≫ Chart.immι T _ = Chart.immι E (Chart.closedι ((SCH).obj E) J) ≫ ι := by
      intro J hJ
      refine exists_factor_closed _ (a ^ k) fun z hz => ?_
      rw [Functor.map_comp]
      exact appTop_comp_eq_zero (Chart.closedι ((SCH).obj E) J) ((SCH).map ι) z
        (closedι_appTop_of_mem J (hJ z hz))
    refine hc k _ _ (hV _ fun z hz => ?_)
    have h1 : ((SCH).map ι).appTop.hom z ∈ ((a.map ((SCH).map ι).appTop.hom) ^ k) := by
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hz
    exact Ideal.mem_map_of_mem (algebraMap _ _) h1

/-- `φ` restricts to `x` on a closed `V(J)`, if the restrictions agree over the open and closed
strata of `a` (`R = Γ(V(J))` in Lemma 4.5). This is "`φ` extends `φₙ`" in §4. -/
theorem restrict_eq_of_strata (hX : IsAlgebraicSpace B S hS X)
    {U : BigFppfOver B S hS} (j : U ⟶ T) (hj : IsOpenImmersion ((SCH).map j))
    (a : Ideal Γ((SCH).obj T, ⊤))
    (hjr : ∀ x : (SCH).obj T, x ∈ Set.range ((SCH).map j) ↔ ∃ g ∈ a, x ∈ ((SCH).obj T).basicOpen g)
    (J : Ideal Γ((SCH).obj T, ⊤))
    [IsNoetherianRing Γ((SCH).obj (Chart.immObj T (Chart.closedι ((SCH).obj T) J)), ⊤)]
    (φ : X.obj (op T)) (τ : X.obj (op U)) (hφj : X.map j.op φ = τ)
    (χ : ∀ k, X.obj (op (Chart.immObj T (Chart.closedι ((SCH).obj T) (a ^ k)))))
    (hφk : ∀ k, X.map (Chart.immι T (Chart.closedι ((SCH).obj T) (a ^ k))).op φ = χ k)
    (x : X.obj (op (Chart.immObj T (Chart.closedι ((SCH).obj T) J))))
    (hτx : ∀ ⦃W : BigFppfOver B S hS⦄ (g₁ : W ⟶ U)
      (g₂ : W ⟶ Chart.immObj T (Chart.closedι ((SCH).obj T) J)),
      g₁ ≫ j = g₂ ≫ Chart.immι T _ → X.map g₁.op τ = X.map g₂.op x)
    (hχx : ∀ (k : ℕ) ⦃W : BigFppfOver B S hS⦄
      (g₁ : W ⟶ Chart.immObj T (Chart.closedι ((SCH).obj T) (a ^ k)))
      (g₂ : W ⟶ Chart.immObj T (Chart.closedι ((SCH).obj T) J)),
      g₁ ≫ Chart.immι T _ = g₂ ≫ Chart.immι T _ → X.map g₁.op (χ k) = X.map g₂.op x) :
    X.map (Chart.immι T (Chart.closedι ((SCH).obj T) J)).op φ = x :=
  have hE : IsAffine ((SCH).obj (Chart.immObj T (Chart.closedι ((SCH).obj T) J))) :=
    inferInstanceAs (IsAffine (Spec _))
  restrict_aux hX j hj _ a hjr φ τ hφj χ hφk x hτx hχx

/-- **Theorem 4.1, existence, from the two strata.** Given the map on the open stratum (Lemma 4.3)
and the maps on the closed strata (Lemma 4.4), with their compatibilities, `φ` exists, is equivariant,
and extends the given system `x`. -/
theorem thm41_exists_of_strata (hX : IsAlgebraicSpace B S hS X) (hB : NoetherianAlgebraization X)
    [IsNoetherianRing Γ((SCH).obj T, ⊤)] (a : Ideal Γ((SCH).obj T, ⊤))
    (gens : Set Γ((SCH).obj T, ⊤)) (hgens : a = Ideal.span gens)
    (hhom : ∀ g ∈ gens, ∃ d, g ∈ homog actT d)
    (hI : ∀ k, ∀ x ∈ a ^ k, ∀ d, (coact actT x).coeff d ∈ a ^ k)
    {U Y : BigFppfOver B S hS} [IsAffine ((SCH).obj Y)]
    [IsNoetherianRing Γ((SCH).obj Y, ⊤)] (j : U ⟶ T) (p : Y ⟶ T)
    (hj : IsOpenImmersion ((SCH).map j))
    (hjr : ∀ x : (SCH).obj T, x ∈ Set.range ((SCH).map j) ↔ ∃ g ∈ a, x ∈ ((SCH).obj T).basicOpen g)
    (hp : Flat ((SCH).map p))
    (hcov : ∀ x : (SCH).obj T, x ∉ Set.range ((SCH).map j) → x ∈ Set.range ((SCH).map p))
    (hsurj : ∀ (k : ℕ) (r : Γ((SCH).obj Y, ⊤)), ∃ c : Γ((SCH).obj T, ⊤),
      r - ((SCH).map p).appTop.hom c ∈ (a ^ k).map ((SCH).map p).appTop.hom)
    (hinj : ∀ (k : ℕ) (c : Γ((SCH).obj T, ⊤)),
      ((SCH).map p).appTop.hom c ∈ (a ^ k).map ((SCH).map p).appTop.hom → c ∈ a ^ k)
    [IsAdicComplete (a.map ((SCH).map p).appTop.hom) Γ((SCH).obj Y, ⊤)]
    (τ : X.obj (op U)) (hτ : EquivAlong actT actX j τ)
    (χ : ∀ k, X.obj (op (Chart.immObj T (Chart.closedι ((SCH).obj T) (a ^ k)))))
    (hχ : ∀ k, EquivAlong actT actX (Chart.immι T (Chart.closedι ((SCH).obj T) (a ^ k))) (χ k))
    (hχc : ∀ (n m : ℕ) (e : Chart.immObj T (Chart.closedι ((SCH).obj T) (a ^ n)) ⟶
        Chart.immObj T (Chart.closedι ((SCH).obj T) (a ^ m))),
        e ≫ Chart.immι T _ = Chart.immι T _ → X.map e.op (χ m) = χ n)
    (hθ : ∀ θ : X.obj (op Y),
      (∀ (k : ℕ) (W : BigFppfOver B S hS) (i : W ⟶ Y)
        (s : W ⟶ Chart.immObj T (Chart.closedι ((SCH).obj T) (a ^ k))),
        s ≫ Chart.immι T _ = i ≫ p → X.map i.op θ = X.map s.op (χ k)) →
      ∀ ⦃W : BigFppfOver B S hS⦄ (g₁ : W ⟶ U) (g₂ : W ⟶ Y), g₁ ≫ j = g₂ ≫ p →
        X.map g₁.op τ = X.map g₂.op θ)
    (m : Ideal Γ((SCH).obj T, ⊤))
    (x : ∀ n, X.obj (op (Chart.immObj T (Chart.closedι ((SCH).obj T) (m ^ n)))))
    (hτx : ∀ (n : ℕ) ⦃W : BigFppfOver B S hS⦄ (g₁ : W ⟶ U)
      (g₂ : W ⟶ Chart.immObj T (Chart.closedι ((SCH).obj T) (m ^ n))),
      g₁ ≫ j = g₂ ≫ Chart.immι T _ → X.map g₁.op τ = X.map g₂.op (x n))
    (hχx : ∀ (n k : ℕ) ⦃W : BigFppfOver B S hS⦄
      (g₁ : W ⟶ Chart.immObj T (Chart.closedι ((SCH).obj T) (a ^ k)))
      (g₂ : W ⟶ Chart.immObj T (Chart.closedι ((SCH).obj T) (m ^ n))),
      g₁ ≫ Chart.immι T _ = g₂ ≫ Chart.immι T _ → X.map g₁.op (χ k) = X.map g₂.op (x n)) :
    ∃ φ : X.obj (op T),
      (∀ n, X.map (Chart.immι T (Chart.closedι ((SCH).obj T) (m ^ n))).op φ = x n) ∧
      ∀ {W : BigFppfOver B S hS} (t : W ⟶ T) (h : Multiplicative M →* Γ((SCH).obj W, ⊤)),
        X.map (smulAt actT h t).op φ = actX.smul (F := X) (U := op W) h (X.map t.op φ) := by
  obtain ⟨φ, hφj, hφk, heq⟩ := exists_glue actT actX hX hB a gens hgens hhom hI j p hj hjr hp
    hcov hsurj hinj τ hτ χ hχ hχc hθ
  refine ⟨φ, fun n => ?_, heq⟩
  have := isNoetherianRing_closed (m ^ n)
  exact restrict_eq_of_strata hX j hj a hjr (m ^ n) φ τ hφj χ hφk (x n) (hτx n) (hχx n)

end Equivariance

end AlgMag.ChartQS

#print axioms AlgMag.ChartQS.existsUnique_pushout
#print axioms AlgMag.ChartQS.equivariant_of_agree
#print axioms AlgMag.ChartQS.exists_glue
#print axioms AlgMag.ChartQS.thm41_exists_of_strata
