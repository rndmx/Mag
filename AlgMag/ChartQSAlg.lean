/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartQSMain

/-!
# Noetherian algebraization for an algebraic space: the formal part

Step 4 of the chart-lemma proof without separatedness. Steps 1 and 3 are `ChartQS.eq_of_agree_basicOpen_of_agree_thickening`
and `ChartQS.eq_of_agree_pow`.

* `ChartQSAlg.existsUnique_pushout_flat`: `existsUnique_pushout` for `Y → T` flat covering `V(a)`, without
  `C → Γ(Y)/a^k` onto: the two pullbacks of `θ` are asked to agree on the thickenings of the kernel pair.
  This is what allows `Y` the completion of an étale `C`-algebra.
* `ChartQSAlg.noetherianAlgebraization_of_exists`: uniqueness in `NoetherianAlgebraization`, any `X`.
* `ChartQSAlg.noetherianAlgebraization_of_localModel`: `NoetherianAlgebraization X` from `LocalModelStep X`,
  the statement that Lemma 3.4, Lemma 4.3 and the induction of Step 4 have to provide.

Route for `LocalModelStep`, simpler than `S(X, Z)`, not yet formalized (noetherian induction on `|X|`,
`C = Γ(W)`, ideal `I`): `U` affine open of `X`, `b`, `τ` on `D(b)` (Lemmas 3.4, 4.3), `ψ_l` on `C/b^l` by
induction on the smaller closed thickenings. Over `D`, the `b`-completion of `C`: étale charts of `X` over
`D/b`, lifted to étale `D'` over `D` (Stacks 057R), `Y` the `b`-completion of `D'` with `1 + I` inverted,
`θ : Y → chart` by the limit of the étale lifts. No filtration 07ST and no induction in `S`. `I` is then in
the Jacobson radical of `Y` (`map_le_jacobson_localization`), so `θ = φ_k` on `Y/I^k` needs only Step 3
(`b` is Jacobson on `Y/I^k`), and `θ = τ` on `D(b)Y` comes from: for `β ∈ b^n`, the elements `τ(f)β`, `θ(f)β`
of `Γ(Y)` are equal modulo all `I^k` by the formula of Lemma 4.3, so equal (`eq_zero_of_mem_pow`).
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Space

universe u

namespace AlgMag.ChartQSAlg

open ChartMain ChartQS

set_option linter.unusedSectionVars false

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

set_option maxHeartbeats 1000000 in
/-- Kernel pair of a flat `p`, no surjectivity: agreement on each `D(g)`, `g ∈ a`, and on the thickenings
of `V(a)` gives agreement. Proof of `ChartQS.eq_on_kernelPair`. -/
theorem eq_on_kernelPair_flat (hX : IsAlgebraicSpace B S hS X) {T Y : BigFppfOver B S hS}
    [IsAffine ((SCH).obj T)] [IsAffine ((SCH).obj Y)] (p : Y ⟶ T)
    [IsNoetherianRing Γ((SCH).obj T, ⊤)] (a : Ideal Γ((SCH).obj T, ⊤))
    (hp : Flat ((SCH).map p)) (θ : X.obj (op Y))
    (hopen : ∀ g ∈ a, ∀ ⦃W : BigFppfOver B S hS⦄ (g₁ g₂ : W ⟶ Y), g₁ ≫ p = g₂ ≫ p →
      (∀ y : (SCH).obj W, (SCH).map (g₁ ≫ p) y ∈ ((SCH).obj T).basicOpen g) →
      X.map g₁.op θ = X.map g₂.op θ)
    (hthick : ∀ (k : ℕ) ⦃W : BigFppfOver B S hS⦄ (g₁ g₂ : W ⟶ Y), g₁ ≫ p = g₂ ≫ p →
      (∀ c ∈ a ^ k, ((SCH).map (g₁ ≫ p)).appTop.hom c = 0) →
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
      let i := Chart.immι P (Chart.closedι ((SCH).obj P) J)
      have hii : (i ≫ pr₁) ≫ p = (i ≫ pr₂) ≫ p := by
        rw [Category.assoc, Category.assoc, hpr]
      refine hthick k (i ≫ pr₁) (i ≫ pr₂) hii fun x hx => ?_
      have hx' : ((SCH).map i ≫ π).appTop x = 0 :=
        appTop_comp_eq_zero ((SCH).map i) π x (closedι_appTop_of_mem J (Ideal.mem_map_of_mem _ hx))
      have e : (SCH).map ((i ≫ pr₁) ≫ p) = (SCH).map i ≫ π := by
        rw [Category.assoc, Functor.map_comp]
      rw [e]
      exact hx'
  let m : W ⟶ P := pullback.lift g₁ g₂ hg
  have e₁ : m ≫ pr₁ = g₁ := pullback.lift_fst _ _ _
  have e₂ : m ≫ pr₂ = g₂ := pullback.lift_snd _ _ _
  rw [← e₁, ← e₂, op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, key]

/-- The cover `{U, Y}` of `T` is fpqc. -/
lemma cover_two {T U Y : BigFppfOver B S hS}
    [IsAffine ((SCH).obj T)] [IsAffine ((SCH).obj Y)] (j : U ⟶ T) (p : Y ⟶ T)
    [IsNoetherianRing Γ((SCH).obj T, ⊤)]
    (hj : IsOpenImmersion ((SCH).map j)) (hp : Flat ((SCH).map p))
    (hcov : ∀ x : (SCH).obj T, x ∉ Set.range ((SCH).map j) → x ∈ Set.range ((SCH).map p)) :
    Presieve.ofArrows (fun i => (SCH).obj ((Fin.cons U (fun _ => Y) : Fin 2 → BigFppfOver B S hS) i))
      (fun i => (SCH).map (Fin.cases (motive := fun i =>
        (Fin.cons U (fun _ => Y) : Fin 2 → BigFppfOver B S hS) i ⟶ T) j (fun _ => p) i)) ∈
      Scheme.fpqcPrecoverage ((SCH).obj T) := by
  have hN₀ : TopologicalSpace.NoetherianSpace ((SCH).obj T) :=
    (Scheme.homeoOfIso ((SCH).obj T).isoSpec).isInducing.noetherianSpace
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

/-- **Step 1, full form of the chart-lemma proof without separatedness.** `T` affine noetherian, `U` the complement of `V(a)`,
`Y → T` flat from an affine, covering `V(a)`. A point on `U` and a point on `Y`, compatible, whose
pullbacks to the kernel pair of `Y` agree on the thickenings of `V(a)`, glue uniquely. -/
theorem existsUnique_pushout_flat (hX : IsAlgebraicSpace B S hS X) {T U Y : BigFppfOver B S hS}
    [IsAffine ((SCH).obj T)] [IsAffine ((SCH).obj Y)] (j : U ⟶ T) (p : Y ⟶ T)
    [IsNoetherianRing Γ((SCH).obj T, ⊤)] (a : Ideal Γ((SCH).obj T, ⊤))
    (hj : IsOpenImmersion ((SCH).map j))
    (hjr : ∀ x : (SCH).obj T, x ∈ Set.range ((SCH).map j) ↔ ∃ g ∈ a, x ∈ ((SCH).obj T).basicOpen g)
    (hp : Flat ((SCH).map p))
    (hcov : ∀ x : (SCH).obj T, x ∉ Set.range ((SCH).map j) → x ∈ Set.range ((SCH).map p))
    (τ : X.obj (op U)) (θ : X.obj (op Y))
    (huv : ∀ ⦃W : BigFppfOver B S hS⦄ (g₁ : W ⟶ U) (g₂ : W ⟶ Y), g₁ ≫ j = g₂ ≫ p →
      X.map g₁.op τ = X.map g₂.op θ)
    (hthick : ∀ (k : ℕ) ⦃W : BigFppfOver B S hS⦄ (g₁ g₂ : W ⟶ Y), g₁ ≫ p = g₂ ≫ p →
      (∀ c ∈ a ^ k, ((SCH).map (g₁ ≫ p)).appTop.hom c = 0) →
      X.map g₁.op θ = X.map g₂.op θ) :
    ∃! φ : X.obj (op T), X.map j.op φ = τ ∧ X.map p.op φ = θ := by
  let Z : Fin 2 → BigFppfOver B S hS := Fin.cons U (fun _ => Y)
  let q : ∀ i, Z i ⟶ T := fun i => Fin.cases (motive := fun i => Z i ⟶ T) j (fun _ => p) i
  let x : ∀ i, X.obj (op (Z i)) := fun i =>
    Fin.cases (motive := fun i => X.obj (op (Z i))) τ (fun _ => θ) i
  have hc := cover_two j p hj hp hcov
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
      exact eq_on_kernelPair_flat hX p a hp θ hopen hthick g₁ g₂ h
  obtain ⟨φ, hφ, huniq⟩ := existsUnique_glue hX Z q hc x hcompat
  refine ⟨φ, ⟨hφ 0, hφ 1⟩, ?_⟩
  rintro φ' ⟨h₁, h₂⟩
  refine huniq φ' fun i => ?_
  revert i
  rw [Fin.forall_fin_two]
  exact ⟨h₁, h₂⟩

/-- Existence part of `NoetherianAlgebraization`. -/
def NoetherianAlgebraizationExists (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∀ (W : BigFppfOver B S hS) [IsAffine ((SCH).obj W)] [IsNoetherianRing Γ((SCH).obj W, ⊤)]
    (I : Ideal Γ((SCH).obj W, ⊤)) [IsAdicComplete I Γ((SCH).obj W, ⊤)]
    (x : ∀ n : ℕ, X.obj (op (Chart.immObj W (Chart.closedι ((SCH).obj W) (I ^ n))))),
    (∀ (n m : ℕ) (t : Chart.immObj W (Chart.closedι ((SCH).obj W) (I ^ n)) ⟶
        Chart.immObj W (Chart.closedι ((SCH).obj W) (I ^ m))),
        t ≫ Chart.immι W _ = Chart.immι W _ → X.map t.op (x m) = x n) →
    ∃ y : X.obj (op W), ∀ n, X.map (Chart.immι W (Chart.closedι ((SCH).obj W) (I ^ n))).op y = x n

/-- **Step 3 gives uniqueness.** For `X` any algebraic space, `NoetherianAlgebraization` is its existence
part: an ideal for which the ring is complete lies in the Jacobson radical, and `eq_of_agree_pow`. -/
theorem noetherianAlgebraization_of_exists (hX : IsAlgebraicSpace B S hS X)
    (h : NoetherianAlgebraizationExists X) : NoetherianAlgebraization X := by
  intro W _ _ I _ x hx
  obtain ⟨y, hy⟩ := h W I x hx
  refine ⟨y, hy, fun y' hy' => ?_⟩
  refine eq_of_agree_pow hX W I (IsAdicComplete.le_jacobson_bot I) y' y fun k => ?_
  rw [hy' k, hy k]

/-- **What Step 4 has to provide.** For a compatible system on a noetherian `I`-complete affine `W`: an
ideal `b`, a point `τ` on the open `D(b)` of `W` (Lemma 3.4 and Lemma 4.3, non-graded), a flat `Y → W`
from an affine, covering `V(b)`, with a point `θ` (the induction of Step 4 on the smaller closed subset,
and an étale chart), which are compatible, have agreeing pullbacks on the thickenings of `V(b)` in the
kernel pair, and restrict to the system. -/
def LocalModelStep (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∀ (W : BigFppfOver B S hS) [IsAffine ((SCH).obj W)] [IsNoetherianRing Γ((SCH).obj W, ⊤)]
    (I : Ideal Γ((SCH).obj W, ⊤)) [IsAdicComplete I Γ((SCH).obj W, ⊤)]
    (x : ∀ n : ℕ, X.obj (op (Chart.immObj W (Chart.closedι ((SCH).obj W) (I ^ n))))),
    (∀ (n m : ℕ) (t : Chart.immObj W (Chart.closedι ((SCH).obj W) (I ^ n)) ⟶
        Chart.immObj W (Chart.closedι ((SCH).obj W) (I ^ m))),
        t ≫ Chart.immι W _ = Chart.immι W _ → X.map t.op (x m) = x n) →
    ∃ (b : Ideal Γ((SCH).obj W, ⊤)) (U Y : BigFppfOver B S hS) (j : U ⟶ W) (p : Y ⟶ W)
      (τ : X.obj (op U)) (θ : X.obj (op Y)),
      IsAffine ((SCH).obj Y) ∧ IsOpenImmersion ((SCH).map j) ∧
      (∀ y : (SCH).obj W, y ∈ Set.range ((SCH).map j) ↔ ∃ g ∈ b, y ∈ ((SCH).obj W).basicOpen g) ∧
      Flat ((SCH).map p) ∧
      (∀ y : (SCH).obj W, y ∉ Set.range ((SCH).map j) → y ∈ Set.range ((SCH).map p)) ∧
      (∀ ⦃V : BigFppfOver B S hS⦄ (g₁ : V ⟶ U) (g₂ : V ⟶ Y), g₁ ≫ j = g₂ ≫ p →
        X.map g₁.op τ = X.map g₂.op θ) ∧
      (∀ (k : ℕ) ⦃V : BigFppfOver B S hS⦄ (g₁ g₂ : V ⟶ Y), g₁ ≫ p = g₂ ≫ p →
        (∀ c ∈ b ^ k, ((SCH).map (g₁ ≫ p)).appTop.hom c = 0) →
        X.map g₁.op θ = X.map g₂.op θ) ∧
      (∀ (n : ℕ) ⦃V : BigFppfOver B S hS⦄ (g₁ : V ⟶ U)
        (g₂ : V ⟶ Chart.immObj W (Chart.closedι ((SCH).obj W) (I ^ n))),
        g₁ ≫ j = g₂ ≫ Chart.immι W _ → X.map g₁.op τ = X.map g₂.op (x n)) ∧
      (∀ (n : ℕ) ⦃V : BigFppfOver B S hS⦄ (g₁ : V ⟶ Y)
        (g₂ : V ⟶ Chart.immObj W (Chart.closedι ((SCH).obj W) (I ^ n))),
        g₁ ≫ p = g₂ ≫ Chart.immι W _ → X.map g₁.op θ = X.map g₂.op (x n))

set_option maxHeartbeats 2000000 in
/-- **Step 4, final assembly.** `LocalModelStep X` gives `NoetherianAlgebraization X`, for `X` any algebraic
space: glue by `existsUnique_pushout_flat`; the point restricts to the system by descent along the
pullback to `V(I^n)` of the cover `{U, Y}`; uniqueness is Step 3. -/
theorem noetherianAlgebraization_of_localModel (hX : IsAlgebraicSpace B S hS X)
    (h : LocalModelStep X) : NoetherianAlgebraization X := by
  refine noetherianAlgebraization_of_exists hX ?_
  intro W _ _ I _ x hx
  obtain ⟨b, U, Y, j, p, τ, θ, hYa, hj, hjr, hp, hcov, huv, hthick, hτx, hθx⟩ := h W I x hx
  haveI := hYa
  haveI := hj
  obtain ⟨φ, ⟨hφj, hφp⟩, -⟩ := existsUnique_pushout_flat hX j p b hj hjr hp hcov τ θ huv hthick
  refine ⟨φ, fun n => ?_⟩
  let E := Chart.immObj W (Chart.closedι ((SCH).obj W) (I ^ n))
  let i : E ⟶ W := Chart.immι W (Chart.closedι ((SCH).obj W) (I ^ n))
  haveI hEa : IsAffine ((SCH).obj E) := by
    change IsAffine (Spec _)
    infer_instance
  have hcl : IsClosedImmersion ((SCH).map i) :=
    inferInstanceAs (IsClosedImmersion (Chart.closedι ((SCH).obj W) (I ^ n)))
  haveI hEn : IsNoetherianRing Γ((SCH).obj E, ⊤) :=
    isNoetherianRing_of_surjective _ _ ((SCH).map i).appTop.hom
      (IsClosedImmersion.isAffine_surjective_of_isAffine ((SCH).map i)).2
  have : PreservesLimitsOfShape WalkingCospan (SCH) := inferInstance
  let U' := pullback j i
  let Y' := pullback p i
  have eU : (SCH).map (pullback.snd j i) =
      pullbackComparison (SCH) j i ≫ pullback.snd ((SCH).map j) ((SCH).map i) :=
    (pullbackComparison_comp_snd (SCH) j i).symm
  have eY : (SCH).map (pullback.snd p i) =
      pullbackComparison (SCH) p i ≫ pullback.snd ((SCH).map p) ((SCH).map i) :=
    (pullbackComparison_comp_snd (SCH) p i).symm
  haveI hY'a : IsAffine ((SCH).obj Y') := by
    have : IsAffine (pullback ((SCH).map p) ((SCH).map i)) := inferInstance
    exact .of_isIso (pullbackComparison (SCH) p i)
  have hj' : IsOpenImmersion ((SCH).map (pullback.snd j i)) := by
    rw [eU]
    infer_instance
  have hp' : Flat ((SCH).map (pullback.snd p i)) := by
    rw [eY]
    infer_instance
  have hcov' : ∀ y : (SCH).obj E, y ∉ Set.range ((SCH).map (pullback.snd j i)) →
      y ∈ Set.range ((SCH).map (pullback.snd p i)) := by
    intro y hy
    have hy0 : (SCH).map i y ∉ Set.range ((SCH).map j) := by
      rintro ⟨u, hu⟩
      obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback u y hu
      refine hy ⟨inv (pullbackComparison (SCH) j i) z, ?_⟩
      have hzz : pullbackComparison (SCH) j i (inv (pullbackComparison (SCH) j i) z) = z := by
        rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
        rfl
      rw [eU, Scheme.Hom.comp_apply, hzz]
      exact hz
    obtain ⟨u, hu⟩ := hcov _ hy0
    obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback u y hu
    refine ⟨inv (pullbackComparison (SCH) p i) z, ?_⟩
    have hzz : pullbackComparison (SCH) p i (inv (pullbackComparison (SCH) p i) z) = z := by
      rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
      rfl
    rw [eY, Scheme.Hom.comp_apply, hzz]
    exact hz
  have hc := cover_two (pullback.snd j i) (pullback.snd p i) hj' hp' hcov'
  let Z : Fin 2 → BigFppfOver B S hS := Fin.cons U' (fun _ => Y')
  let q : ∀ a, Z a ⟶ E := fun a => Fin.cases (motive := fun a => Z a ⟶ E)
    (pullback.snd j i) (fun _ => pullback.snd p i) a
  obtain ⟨_, -, huq⟩ := existsUnique_glue hX Z q hc (fun a => X.map (q a).op (x n))
    (fun a c V g₁ g₂ hg => by
      rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, hg])
  have h1 : ∀ a, X.map (q a).op (X.map i.op φ) = X.map (q a).op (x n) := by
    rw [Fin.forall_fin_two]
    constructor
    · change X.map (pullback.snd j i).op (X.map i.op φ) = X.map (pullback.snd j i).op (x n)
      rw [← Functor.map_comp_apply, ← op_comp, ← pullback.condition, op_comp, Functor.map_comp_apply,
        hφj]
      exact hτx n _ _ pullback.condition
    · change X.map (pullback.snd p i).op (X.map i.op φ) = X.map (pullback.snd p i).op (x n)
      rw [← Functor.map_comp_apply, ← op_comp, ← pullback.condition, op_comp, Functor.map_comp_apply,
        hφp]
      exact hθx n _ _ pullback.condition
  exact (huq _ h1).trans (huq _ (fun _ => rfl)).symm

/-- The elements `1 - r`, `r ∈ a`. -/
def oneSub {R : Type*} [CommRing R] (a : Ideal R) : Submonoid R where
  carrier := {x | ∃ r ∈ a, x = 1 - r}
  one_mem' := ⟨0, a.zero_mem, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨r, hr, rfl⟩ ⟨t, ht, rfl⟩
    exact ⟨r + t - r * t, a.sub_mem (a.add_mem hr ht) (a.mul_mem_right _ hr), by ring⟩

/-- After inverting `1 + a`, the ideal `a` lies in the Jacobson radical. This makes `a` Jacobson on the local
model `Y` of `LocalModelStep`, where Krull then applies, while `Y` still covers `V(b)`. -/
theorem map_le_jacobson_localization {R L : Type*} [CommRing R] [CommRing L] [Algebra R L]
    (a : Ideal R) [IsLocalization (oneSub a) L] :
    a.map (algebraMap R L) ≤ Ideal.jacobson ⊥ := by
  refine le_sInf ?_
  rintro m ⟨-, hm⟩
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  by_contra hrm
  obtain ⟨c, u, hu, hc'⟩ := hm.exists_inv (x := algebraMap R L r) hrm
  obtain ⟨⟨z, s⟩, hzs⟩ := IsLocalization.surj (oneSub a) c
  simp only at hzs
  have hy : u * algebraMap R L (s : R) ∈ m := m.mul_mem_right _ hu
  have hs : algebraMap R L ((s : R) - z * r) = u * algebraMap R L (s : R) := by
    rw [map_sub, map_mul, ← hzs]
    linear_combination (-algebraMap R L (s : R)) * hc'
  obtain ⟨t, ht, hst⟩ := s.2
  have hin : (1 : R) - (t + z * r) = (s : R) - z * r := by rw [hst]; ring
  have hmem : (t + z * r) ∈ a := a.add_mem ht (a.mul_mem_left _ hr)
  have hU : IsUnit (algebraMap R L (1 - (t + z * r))) :=
    IsLocalization.map_units L (⟨_, t + z * r, hmem, rfl⟩ : oneSub a)
  rw [hin, hs] at hU
  exact hm.ne_top (Ideal.eq_top_of_isUnit_mem _ hy hU)

/-- Krull: an element in all `a^k`, `a` in the Jacobson radical of a noetherian ring, is zero. This is the
end of the comparison of `τ` and `θ` by the formula of Lemma 4.3. -/
theorem eq_zero_of_mem_pow {R : Type*} [CommRing R] [IsNoetherianRing R] (a : Ideal R)
    (ha : a ≤ Ideal.jacobson ⊥) (e : R) (he : ∀ k : ℕ, e ∈ a ^ k) : e = 0 := by
  obtain ⟨r, hr, h⟩ := exists_one_sub_mul_eq_zero a (Ideal.span {e})
    (fun i hi k => (Ideal.span_singleton_le_iff_mem _).2 (he k) hi)
  have h0 := h e (Ideal.mem_span_singleton_self e)
  have hu : IsUnit (1 - r) := by
    have := (Ideal.mem_jacobson_bot.1 (ha hr)) (-1)
    convert this using 1
    ring
  exact (hu.mul_right_eq_zero).1 h0

/-- `LocalModelStep`, with the agreement on the kernel pair coming from a point `ψ k` on each `V(b^k)` under
`θ`. -/
theorem hthick_of_psi {W Y : BigFppfOver B S hS} [IsAffine ((SCH).obj W)] (p : Y ⟶ W)
    (b : Ideal Γ((SCH).obj W, ⊤)) (θ : X.obj (op Y))
    (ψ : ∀ k : ℕ, X.obj (op (Chart.immObj W (Chart.closedι ((SCH).obj W) (b ^ k)))))
    (hψ : ∀ (k : ℕ) ⦃V : BigFppfOver B S hS⦄ (g₁ : V ⟶ Y)
      (g₂ : V ⟶ Chart.immObj W (Chart.closedι ((SCH).obj W) (b ^ k))),
      g₁ ≫ p = g₂ ≫ Chart.immι W _ → X.map g₁.op θ = X.map g₂.op (ψ k))
    (k : ℕ) ⦃V : BigFppfOver B S hS⦄ (g₁ g₂ : V ⟶ Y) (hg : g₁ ≫ p = g₂ ≫ p)
    (hk : ∀ c ∈ b ^ k, ((SCH).map (g₁ ≫ p)).appTop.hom c = 0) :
    X.map g₁.op θ = X.map g₂.op θ := by
  obtain ⟨s, hs⟩ := exists_factor_closed (g₁ ≫ p) (b ^ k) hk
  exact (hψ k g₁ s hs.symm).trans (hψ k g₂ s (hg.symm.trans hs.symm)).symm

end AlgMag.ChartQSAlg

#print axioms AlgMag.ChartQSAlg.existsUnique_pushout_flat
#print axioms AlgMag.ChartQSAlg.noetherianAlgebraization_of_exists
#print axioms AlgMag.ChartQSAlg.noetherianAlgebraization_of_localModel
#print axioms AlgMag.ChartQSAlg.map_le_jacobson_localization
#print axioms AlgMag.ChartQSAlg.eq_zero_of_mem_pow
#print axioms AlgMag.ChartQSAlg.hthick_of_psi
