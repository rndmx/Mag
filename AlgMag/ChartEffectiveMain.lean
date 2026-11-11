/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartActionGrading
import AlgMag.ChartGraded
import AlgMag.ChartEffective
import AlgMag.ChartSplit

/-!
# Existence in Theorem 4.1 of the chart-lemma proof: the gluing

Over an arbitrary base `S` of the site (`AlgMag.ChartSplit.bhatt14` is over `Spec C`).

* `AlgMag.ChartMain.existsUnique_glue`: the fpqc sheaf property for a two-member family.
* `AlgMag.ChartMain.eq_on_kernelPair`: the overlap `Y ×_T Y` (§4, Remark), from Lemma 4.5.
* `AlgMag.ChartMain.existsUnique_pushout`: Bhatt, Theorem 1.4(1), restricted form, for a separated
  target over `S`.
* `AlgMag.ChartMain.exists_theta`: the Bhatt Theorem 1.1 step, from `NoetherianAlgebraization` (Stacks 0GHK).
* `AlgMag.ChartMain.equivariant_of_agree`: "φ is equivariant", Lemma 4.5 with `R = O(G) ⊗ C`.
* `AlgMag.ChartMain.thm41_unique`: Theorem 4.1, uniqueness.
* `AlgMag.ChartMain.thm41_exists_of_strata`: Theorem 4.1, existence, from the open stratum map
  (Lemma 4.3), the closed strata maps (Lemma 4.4) and the compatibilities.

Not proved: Lemmas 4.2, 4.3, 4.4 on algebraic spaces and the noetherian induction.
`AlgMag.ChartMain.AffineStratum` states Lemma 4.2.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Space

universe u

namespace AlgMag.ChartMain

set_option linter.unusedSectionVars false

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- The fpqc sheaf property of an algebraic space for a two-member family. -/
theorem existsUnique_glue (hX : IsAlgebraicSpace B S hS X)
    {T : BigFppfOver B S hS} (Z : Fin 2 → BigFppfOver B S hS) (q : ∀ i, Z i ⟶ T)
    (hcov : Presieve.ofArrows (fun i => (SCH).obj (Z i)) (fun i => (SCH).map (q i)) ∈
      Scheme.fpqcPrecoverage ((SCH).obj T))
    (x : ∀ i, X.obj (op (Z i)))
    (hx : ∀ i j ⦃W : BigFppfOver B S hS⦄ (g₁ : W ⟶ Z i) (g₂ : W ⟶ Z j),
      g₁ ≫ q i = g₂ ≫ q j → X.map g₁.op (x i) = X.map g₂.op (x j)) :
    ∃! φ : X.obj (op T), ∀ i, X.map (q i).op φ = x i := by
  have hsh := IsAlgebraicSpace.isSheaf_fpqc hX
  rw [isSheaf_iff_isSheaf_of_type,
    Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange] at hsh
  have hR : Presieve.ofArrows Z q ∈ Scheme.fpqcPrecoverage.comap (SCH) T := by
    rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows]
    exact hcov
  have hF := (Presieve.isSheafFor_arrows_iff X q).1 (hsh _ hR)
  obtain ⟨t, ht, hu⟩ := hF x (fun i j W g₁ g₂ h => hx i j g₁ g₂ h)
  exact ⟨t, ht, fun y hy => hu y hy⟩

/-- **Stacks 0GHK, section form on `X`**: `A = Γ(W)` noetherian and `I`-adically complete. A compatible
system of points of `X` over `A/Iⁿ` comes from a unique point over `A`. This is the restriction of
Bhatt's Theorem 1.1 to noetherian `A`, which is what 0GHK gives for `X` separated and locally of
finite type (`ChartSplit.existsUnique_section_of_algebraization`). -/
def NoetherianAlgebraization (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∀ (W : BigFppfOver B S hS) [IsAffine ((SCH).obj W)] [IsNoetherianRing Γ((SCH).obj W, ⊤)]
    (I : Ideal Γ((SCH).obj W, ⊤)) [IsAdicComplete I Γ((SCH).obj W, ⊤)]
    (x : ∀ n : ℕ, X.obj (op (Chart.immObj W (Chart.closedι ((SCH).obj W) (I ^ n))))),
    (∀ (n m : ℕ) (t : Chart.immObj W (Chart.closedι ((SCH).obj W) (I ^ n)) ⟶
        Chart.immObj W (Chart.closedι ((SCH).obj W) (I ^ m))),
        t ≫ Chart.immι W _ = Chart.immι W _ → X.map t.op (x m) = x n) →
    ∃! y : X.obj (op W), ∀ n, X.map (Chart.immι W (Chart.closedι ((SCH).obj W) (I ^ n))).op y = x n

/-- `closedι Y I` kills `I`. -/
lemma closedι_appTop_of_mem {Y : Scheme.{u}} [IsAffine Y] (I : Ideal Γ(Y, ⊤)) {r : Γ(Y, ⊤)}
    (hr : r ∈ I) : (Chart.closedι Y I).appTop r = 0 := by
  have e : (Scheme.ΓSpecIso Γ(Y, ⊤)).hom ≫ Y.isoSpec.inv.appTop = 𝟙 _ := by
    rw [← Scheme.toSpecΓ_appTop, ← Scheme.isoSpec_hom, ← Scheme.Hom.comp_appTop, Iso.inv_hom_id]
    simp
  have hinv : Y.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(Y, ⊤)).inv := (Iso.hom_comp_eq_id _).mp e
  have this : (Chart.closedι Y I).appTop r = (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop
      ((Scheme.ΓSpecIso Γ(Y, ⊤)).inv r) := by
    rw [Chart.closedι, Scheme.Hom.comp_appTop, hinv]; rfl
  have hnat := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have h1 := ConcreteCategory.congr_hom hnat r
  rw [this]
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h1
  refine h1.symm.trans ?_
  have : (CommRingCat.ofHom (Ideal.Quotient.mk I)) r = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hr
  rw [this, map_zero]

lemma hom_eq_of_quot_surj {E Y T : Scheme.{u}} [IsAffine Y] (e₁ e₂ : E ⟶ Y) (p : Y ⟶ T)
    (he : e₁ ≫ p = e₂ ≫ p) (J : Ideal Γ(T, ⊤))
    (hk : ∀ x ∈ J, (e₁ ≫ p).appTop x = 0)
    (hsurj : ∀ r : Γ(Y, ⊤), ∃ c : Γ(T, ⊤), r - p.appTop.hom c ∈ J.map p.appTop.hom) : e₁ = e₂ := by
  have hi : ∀ q : E ⟶ Y, q ≫ p = e₁ ≫ p → ∀ c ∈ J.map p.appTop.hom, q.appTop.hom c = 0 := by
    intro q hq c hc
    induction hc using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, hx, rfl⟩ := hz
      have := hk x hx
      rw [← hq, Scheme.Hom.comp_appTop] at this
      exact this
    | zero => simp
    | add u v _ _ hu hv => rw [map_add, hu, hv, add_zero]
    | smul b u _ hu => rw [smul_eq_mul, map_mul, hu, mul_zero]
  refine toAffine_ext (RingHom.ext fun r => ?_)
  obtain ⟨c, hc⟩ := hsurj r
  have h1 := hi e₁ rfl _ hc
  have h2 := hi e₂ he.symm _ hc
  rw [map_sub, sub_eq_zero] at h1 h2
  refine h1.trans (Eq.trans ?_ h2.symm)
  have h : (e₁ ≫ p).appTop.hom c = (e₂ ≫ p).appTop.hom c := by rw [he]
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] using h

lemma appTop_comp_eq_zero {E P T : Scheme.{u}} (e : E ⟶ P) (π : P ⟶ T) (x : Γ(T, ⊤))
    (h : e.appTop (π.appTop.hom x) = 0) : (e ≫ π).appTop x = 0 := by
  rw [Scheme.Hom.comp_appTop]
  exact h

lemma mem_basicOpen_of_range {Y T W : Scheme.{u}} (π : Y ⟶ T) (g : Γ(T, ⊤)) (f : W ⟶ Y)
    (h : Set.range f ⊆ Y.basicOpen (π.appTop.hom g)) (y : W) : π (f y) ∈ T.basicOpen g := by
  have := h ⟨y, rfl⟩
  have e : Y.basicOpen (π.appTop.hom g) = π ⁻¹ᵁ T.basicOpen g := (Scheme.preimage_basicOpen _ g).symm
  rw [e] at this
  exact this

set_option maxHeartbeats 1000000 in
/-- **§4, Remark: the overlap.** Let `T` be affine with `C = Γ(T)` noetherian, `a` an ideal of `C`
and `p : Y → T` flat with `Y` affine, with `C → Γ(Y)/a^kΓ(Y)` onto. If `θ ∈ X(Y)` is such that, on
each `D(g)`, `g ∈ a`, its two pullbacks to `Y ×_T Y` agree, they agree. `X` is separated. -/
theorem eq_on_kernelPair (hsep : Space.IsSeparatedOver B S hS X) {T Y : BigFppfOver B S hS}
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
    refine Chart.eq_of_agree_basicOpen_of_agree_thickening hsep P a (a : Set _)
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
`C → Γ(Y)/a^k` onto. Then `T` is the pushout of `U` and `Y`, for maps to a separated space. -/
theorem existsUnique_pushout (hX : IsAlgebraicSpace B S hS X)
    (hsep : Space.IsSeparatedOver B S hS X) {T U Y : BigFppfOver B S hS}
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
      exact eq_on_kernelPair hsep p a hp hsurj θ hopen g₁ g₂ h
  obtain ⟨φ, hφ, huniq⟩ := existsUnique_glue hX Z q hc x hcompat
  refine ⟨φ, ⟨hφ 0, hφ 1⟩, ?_⟩
  rintro φ' ⟨h₁, h₂⟩
  refine huniq φ' fun i => ?_
  revert i
  rw [Fin.forall_fin_two]
  exact ⟨h₁, h₂⟩

/-! ### Equivariance (§4, after Lemma 4.5) -/

section Equivariance

variable {M : Type u} [AddCommGroup M] [AddMonoid.FG M] {T : BigFppfOver B S hS}
  [hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)] (actT : AAction (fppfO B S hS) M (yoneda.obj T))
  (actX : AAction (fppfO B S hS) M X)

/-- `x ∈ X(E)`, for `i : E → T`, is equivariant: for `t, t' : W → E` with `t' i = h • (t i)`, one has
`t'^* x = h • t^* x`. This needs no action on `E`. -/
def EquivAlong {E : BigFppfOver B S hS} (i : E ⟶ T) (x : X.obj (op E)) : Prop :=
  ∀ ⦃W : BigFppfOver B S hS⦄ (t t' : W ⟶ E) (h : Multiplicative M →* Γ((SCH).obj W, ⊤)),
    t' ≫ i = smulAt actT h (t ≫ i) →
    X.map t'.op x = actX.smul (F := X) (U := op W) h (X.map t.op x)

/-- An element of `Γ(T)` of degree `d` is invertible on `W` along `t` iff it is along `h • t`. -/
lemma mem_basicOpen_smul_iff {W : BigFppfOver B S hS} (t : W ⟶ T)
    (h : Multiplicative M →* Γ((SCH).obj W, ⊤)) {d : M} {g : Γ((SCH).obj T, ⊤)}
    (hg : g ∈ homog actT d) (y : (SCH).obj W) :
    (SCH).map (smulAt actT h t) y ∈ ((SCH).obj T).basicOpen g ↔
      (SCH).map t y ∈ ((SCH).obj T).basicOpen g := by
  have hu : IsUnit (h (Multiplicative.ofAdd d)) := by
    refine IsUnit.map h ?_
    exact Group.isUnit _
  have e : ((SCH).obj W).basicOpen (((SCH).map (smulAt actT h t)).appTop.hom g) =
      ((SCH).obj W).basicOpen (((SCH).map t).appTop.hom g) := by
    rw [appTop_smul_of_mem actT t h hg, Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ hu]
    simp
  have h₁ : ∀ f : (SCH).obj W ⟶ (SCH).obj T, f y ∈ ((SCH).obj T).basicOpen g ↔
      y ∈ ((SCH).obj W).basicOpen (f.appTop.hom g) := fun f => by
    rw [← show f ⁻¹ᵁ ((SCH).obj T).basicOpen g = ((SCH).obj W).basicOpen (f.appTop.hom g) from
      Scheme.preimage_basicOpen f g]
    rfl
  rw [h₁, h₁, e]

lemma evalAt_eq_zero {A R M' : Type*} [CommRing A] [CommRing R] [AddCommGroup M'] (x : A →+* R)
    (h : Multiplicative M' →* R) (p : AddMonoidAlgebra A M') (hp : ∀ d, x (p.coeff d) = 0) :
    evalAt x h p = 0 := by
  classical
  have e : p = ∑ d ∈ p.coeff.support, AddMonoidAlgebra.single d (p.coeff d) := by
    ext d
    simp [AddMonoidAlgebra.coeff_sum, Finsupp.single_apply]
  rw [e, map_sum]
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [evalAt_single, hp, zero_mul]

/-- A homogeneous ideal (in the form: closed under components) killed by `t` is killed by `h • t`. -/
lemma appTop_smul_eq_zero {W : BigFppfOver B S hS} (t : W ⟶ T)
    (h : Multiplicative M →* Γ((SCH).obj W, ⊤)) (I : Ideal Γ((SCH).obj T, ⊤))
    (hI : ∀ x ∈ I, ∀ d, (coact actT x).coeff d ∈ I)
    (ht : ∀ x ∈ I, ((SCH).map t).appTop.hom x = 0) {x : Γ((SCH).obj T, ⊤)} (hx : x ∈ I) :
    ((SCH).map (smulAt actT h t)).appTop.hom x = 0 := by
  rw [appTop_smul]
  exact evalAt_eq_zero _ _ _ fun d => ht _ (hI x hx d)

/-- A map killing `I` factors through the closed subscheme `V(I)`, on the site. -/
lemma exists_factor_closed {W : BigFppfOver B S hS} (t : W ⟶ T) (I : Ideal Γ((SCH).obj T, ⊤))
    (ht : ∀ x ∈ I, ((SCH).map t).appTop.hom x = 0) :
    ∃ s : W ⟶ Chart.immObj T (Chart.closedι ((SCH).obj T) I),
      s ≫ Chart.immι T (Chart.closedι ((SCH).obj T) I) = t := by
  let φ : Γ((SCH).obj T, ⊤) ⧸ I →+* Γ((SCH).obj W, ⊤) := Ideal.Quotient.lift I _ ht
  let s₀ : (SCH).obj W ⟶ Spec (.of (Γ((SCH).obj T, ⊤) ⧸ I)) :=
    ((SCH).obj W).toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)
  have hs : s₀ ≫ Chart.closedι ((SCH).obj T) I = (SCH).map t := by
    refine toAffine_ext (?_)
    have : s₀ ≫ Chart.closedι ((SCH).obj T) I = toAffine ((SCH).map t).appTop.hom := by
      simp only [s₀, Chart.closedι, toAffine, Category.assoc]
      rw [← Category.assoc (Spec.map _) (Spec.map _), ← Spec.map_comp]
      rfl
    rw [this, toAffine_appTop]
  refine ⟨Over.homMk ⟨s₀⟩ ?_, siteExt hs⟩
  apply InducedCategory.hom_ext
  have := congrArg (fun z => z.hom) (Over.w t)
  change s₀ ≫ Chart.closedι ((SCH).obj T) I ≫ T.hom.hom = W.hom.hom
  rw [← Category.assoc, hs]
  exact this

include hT in
lemma agree_of_factor {E E' : BigFppfOver B S hS} (φ : X.obj (op T))
    (i : E ⟶ spObj T (ι1 T (M := M)) contains1) (e : E' ⟶ T)
    (hx : EquivAlong actT actX e (X.map e.op φ)) (s s' : E ⟶ E')
    (hs : s ≫ e = i ≫ spToT T (ι1 T (M := M)) contains1) (hs' : s' ≫ e = i ≫ univMap actT) :
    X.map i.op (X.map (univMap actT).op φ) =
      X.map i.op (actX.smul (F := X) (U := op _) univPt1
        (X.map (spToT T (ι1 T (M := M)) contains1).op φ)) := by
  have e₀ : i ≫ univMap actT = smulAt actT
      (secPt ((SCH).map i).appTop.hom (univPt1 (U := T))) (s ≫ e) := by
    rw [hs]
    exact comp_smulAt actT i _ _
  have hE := hx s s' (secPt ((SCH).map i).appTop.hom (univPt1 (U := T))) (hs'.trans e₀)
  have l₁ : X.map i.op (X.map (univMap actT).op φ) = X.map s'.op (X.map e.op φ) := by
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, hs']
  have l₂ : X.map s.op (X.map e.op φ) =
      X.map i.op (X.map (spToT T (ι1 T (M := M)) contains1).op φ) := by
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, hs]
  rw [l₁, hE, l₂]
  exact (actX.map_smul i.op _ _).symm

set_option maxHeartbeats 1000000 in
/-- **§4, "φ is equivariant".** If `φ ∈ X(T)` restricts to equivariant points on each `D(g)`, `g`
homogeneous generators of `a`, and on each `V(a^k)`, then `φ` is equivariant. This is Lemma 4.5 with
`R = O(G) ⊗ C`. -/
theorem equivariant_of_agree (hsep : Space.IsSeparatedOver B S hS X)
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
    refine Chart.eq_of_agree_basicOpen_of_agree_thickening hsep Tm a gens hgens _ _ ?_ ?_
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

/-- A map `p : Y → T` of affines with `Γ(T)/J ≅ Γ(Y)/JΓ(Y)` has a section over `V(J)`. -/
lemma exists_section_of_quot {T Y : BigFppfOver B S hS} [IsAffine ((SCH).obj T)]
    [IsAffine ((SCH).obj Y)] (p : Y ⟶ T) (J : Ideal Γ((SCH).obj T, ⊤))
    (hsurj : ∀ r : Γ((SCH).obj Y, ⊤), ∃ c : Γ((SCH).obj T, ⊤),
      r - ((SCH).map p).appTop.hom c ∈ J.map ((SCH).map p).appTop.hom)
    (hinj : ∀ c : Γ((SCH).obj T, ⊤),
      ((SCH).map p).appTop.hom c ∈ J.map ((SCH).map p).appTop.hom → c ∈ J) :
    ∃ σ : Chart.immObj T (Chart.closedι ((SCH).obj T) J) ⟶ Y,
      σ ≫ p = Chart.immι T (Chart.closedι ((SCH).obj T) J) := by
  let P := ((SCH).map p).appTop.hom
  let qm : Γ((SCH).obj T, ⊤) ⧸ J →+* Γ((SCH).obj Y, ⊤) ⧸ J.map P :=
    Ideal.quotientMap _ P Ideal.le_comap_map
  have hb : Function.Bijective qm := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro z hz
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
      have : Ideal.Quotient.mk (J.map P) (P c) = 0 := hz
      exact Ideal.Quotient.eq_zero_iff_mem.2 (hinj c (Ideal.Quotient.eq_zero_iff_mem.1 this))
    · intro z
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
      obtain ⟨c, hc⟩ := hsurj r
      exact ⟨Ideal.Quotient.mk J c, (Ideal.Quotient.eq.2 hc).symm⟩
  let E := Chart.immObj T (Chart.closedι ((SCH).obj T) J)
  let ι₀ : (SCH).obj E ⟶ (SCH).obj T := Chart.closedι ((SCH).obj T) J
  let L : Γ((SCH).obj T, ⊤) ⧸ J →+* Γ((SCH).obj E, ⊤) :=
    Ideal.Quotient.lift J ι₀.appTop.hom (fun c hc => closedι_appTop_of_mem J hc)
  let ψ : Γ((SCH).obj Y, ⊤) →+* Γ((SCH).obj E, ⊤) :=
    L.comp (((RingEquiv.ofBijective qm hb).symm : _ →+* _).comp (Ideal.Quotient.mk (J.map P)))
  have hψ : ψ.comp P = ι₀.appTop.hom := RingHom.ext fun c => by
    have : (RingEquiv.ofBijective qm hb).symm (Ideal.Quotient.mk (J.map P) (P c)) =
        Ideal.Quotient.mk J c := (RingEquiv.ofBijective qm hb).symm_apply_apply (Ideal.Quotient.mk J c)
    simp only [ψ, RingHom.comp_apply]
    change L ((RingEquiv.ofBijective qm hb).symm (Ideal.Quotient.mk (J.map P) (P c))) = _
    rw [this]
    rfl
  have hc₀ : toAffine (T := (SCH).obj E) (U := (SCH).obj Y) ψ ≫ (SCH).map p = ι₀ :=
    toAffine_ext (by
      rw [Scheme.Hom.comp_appTop]
      refine Eq.trans ?_ hψ
      change (toAffine (T := (SCH).obj E) (U := (SCH).obj Y) ψ).appTop.hom.comp P = ψ.comp P
      rw [toAffine_appTop])
  have hw : toAffine (T := (SCH).obj E) (U := (SCH).obj Y) ψ ≫ Y.hom.hom = E.hom.hom := by
    have e : (SCH).map p ≫ T.hom.hom = Y.hom.hom := congrArg (fun z => z.hom) (Over.w p)
    rw [← e, ← Category.assoc, hc₀]
    rfl
  exact ⟨Over.homMk ⟨toAffine (T := (SCH).obj E) (U := (SCH).obj Y) ψ⟩ (InducedCategory.hom_ext hw),
    siteExt hc₀⟩

include hT in
/-- A point equivariant along an open `j` is equivariant along any map factoring through `j`. -/
lemma EquivAlong.of_factor {E E' : BigFppfOver B S hS} {j : E' ⟶ T} {e : E ⟶ T} {τ : X.obj (op E')}
    [Mono j] (hτ : EquivAlong actT actX j τ) (l : E ⟶ E') (hl : l ≫ j = e) :
    EquivAlong actT actX e (X.map l.op τ) := by
  intro W t t' h ht
  have := hτ (t ≫ l) (t' ≫ l) h (by
    simpa only [Category.assoc, hl] using ht)
  simpa only [op_comp, Functor.map_comp_apply] using this

lemma kill_scheme {W Y E T : Scheme.{u}} (i : W ⟶ Y) (p : Y ⟶ T) (s : W ⟶ E) (ι : E ⟶ T)
    (h : s ≫ ι = i ≫ p) (J : Ideal Γ(T, ⊤)) (hι : ∀ c ∈ J, ι.appTop c = 0) :
    ∀ y ∈ J.map p.appTop.hom, i.appTop.hom y = 0 := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨c, hc, rfl⟩ := hz
    have h1 : (i ≫ p).appTop c = (s ≫ ι).appTop c := by rw [h]
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h1
    refine Eq.trans h1 ?_
    change s.appTop (ι.appTop c) = 0
    rw [hι c hc, map_zero]
  | zero => simp
  | add u v _ _ hu hv => rw [map_add, hu, hv, add_zero]
  | smul b u _ hu => rw [smul_eq_mul, map_mul, hu, mul_zero]

set_option maxHeartbeats 2000000 in
/-- **Bhatt, Theorem 1.1 step** (§4 "Glue"): the system `χ` on `V(a^k)` extends to `θ` on `Y`. -/
theorem exists_theta {T Y : BigFppfOver B S hS} [IsAffine ((SCH).obj T)] [IsAffine ((SCH).obj Y)]
    [IsNoetherianRing Γ((SCH).obj Y, ⊤)]
    (hB : NoetherianAlgebraization X) (p : Y ⟶ T) (a : Ideal Γ((SCH).obj T, ⊤))
    (hinj : ∀ (k : ℕ) (c : Γ((SCH).obj T, ⊤)),
      ((SCH).map p).appTop.hom c ∈ (a ^ k).map ((SCH).map p).appTop.hom → c ∈ a ^ k)
    [IsAdicComplete (a.map ((SCH).map p).appTop.hom) Γ((SCH).obj Y, ⊤)]
    (χ : ∀ k, X.obj (op (Chart.immObj T (Chart.closedι ((SCH).obj T) (a ^ k)))))
    (hχc : ∀ (n m : ℕ) (e : Chart.immObj T (Chart.closedι ((SCH).obj T) (a ^ n)) ⟶
        Chart.immObj T (Chart.closedι ((SCH).obj T) (a ^ m))),
        e ≫ Chart.immι T _ = Chart.immι T _ → X.map e.op (χ m) = χ n) :
    ∃ θ : X.obj (op Y), ∀ (k : ℕ) (W : BigFppfOver B S hS) (i : W ⟶ Y)
      (s : W ⟶ Chart.immObj T (Chart.closedι ((SCH).obj T) (a ^ k))),
      s ≫ Chart.immι T _ = i ≫ p → X.map i.op θ = X.map s.op (χ k) := by
  have hIpow : ∀ n, (a.map ((SCH).map p).appTop.hom) ^ n = (a ^ n).map ((SCH).map p).appTop.hom :=
    fun n => (Ideal.map_pow _ a n).symm
  generalize hIdef : a.map ((SCH).map p).appTop.hom = I at hIpow
  have hmonoT : ∀ J : Ideal Γ((SCH).obj T, ⊤), Mono (Chart.immι T (Chart.closedι ((SCH).obj T) J)) :=
    fun J => (SCH).mono_of_mono_map (inferInstanceAs (Mono (Chart.closedι ((SCH).obj T) J)))
  have hk : ∀ n, ∀ x ∈ a ^ n, ((SCH).map (Chart.immι Y (Chart.closedι ((SCH).obj Y) (I ^ n)) ≫ p)).appTop.hom x = 0 :=
    fun n x hx => by
      have hm : ((SCH).map p).appTop.hom x ∈ I ^ n := by
        rw [hIpow]
        exact Ideal.mem_map_of_mem _ hx
      have h0 := appTop_comp_eq_zero (Chart.closedι ((SCH).obj Y) (I ^ n)) ((SCH).map p) x
        (closedι_appTop_of_mem (I ^ n) hm)
      exact (congrArg (fun z => z.appTop.hom x)
        ((SCH).map_comp (Chart.immι Y (Chart.closedι ((SCH).obj Y) (I ^ n))) p)).trans h0
  choose f hf using fun n => exists_factor_closed (Chart.immι Y (Chart.closedι ((SCH).obj Y) (I ^ n)) ≫ p) (a ^ n) (hk n)
  have hcompat : ∀ (n m : ℕ) (t : Chart.immObj Y (Chart.closedι ((SCH).obj Y) (I ^ n)) ⟶
      Chart.immObj Y (Chart.closedι ((SCH).obj Y) (I ^ m))),
      t ≫ Chart.immι Y _ = Chart.immι Y _ → X.map t.op (X.map (f m).op (χ m)) = X.map (f n).op (χ n) := by
    intro n m t ht
    have hle : a ^ m ≤ a ^ n := by
      intro c hc
      refine hinj n c ?_
      rw [← hIpow]
      refine Chart.closedι_appTop_eq_zero (I ^ n) _ ?_
      have h3 : (Chart.closedι ((SCH).obj Y) (I ^ m)).appTop (((SCH).map p).appTop.hom c) = 0 :=
        closedι_appTop_of_mem (I ^ m) (by rw [hIpow]; exact Ideal.mem_map_of_mem _ hc)
      have h5 : (SCH).map t ≫ Chart.closedι ((SCH).obj Y) (I ^ m) =
          Chart.closedι ((SCH).obj Y) (I ^ n) :=
        ((SCH).map_comp t _).symm.trans (congrArg (fun z => (SCH).map z) ht)
      have h7 := appTop_comp_eq_zero ((SCH).map t) (Chart.closedι ((SCH).obj Y) (I ^ m))
        (((SCH).map p).appTop.hom c)
        ((congrArg (fun z => ((SCH).map t).appTop z) h3).trans (map_zero _))
      have h8 := congrArg (fun z => z.appTop.hom (((SCH).map p).appTop.hom c)) h5
      exact h8.symm.trans h7
    obtain ⟨e, he⟩ := exists_factor_closed (Chart.immι T (Chart.closedι ((SCH).obj T) (a ^ n)))
      (a ^ m) (fun c hc => closedι_appTop_of_mem (a ^ n) (hle hc))
    have := hmonoT (a ^ m)
    have h4 : f n ≫ e = t ≫ f m := by
      refine (cancel_mono (Chart.immι T (Chart.closedι ((SCH).obj T) (a ^ m)))).1 ?_
      rw [Category.assoc, he, hf, Category.assoc, hf, ← Category.assoc, ht]
    rw [← hχc n m e he, ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, h4]
  subst hIdef
  obtain ⟨θ, hθx, -⟩ := hB Y _ (fun n => X.map (f n).op (χ n)) (fun n m t ht => hcompat n m t ht)
  refine ⟨θ, fun k W i s hs => ?_⟩
  have h0 : (SCH).map s ≫ Chart.closedι ((SCH).obj T) (a ^ k) = (SCH).map i ≫ (SCH).map p :=
    ((SCH).map_comp s _).symm.trans ((congrArg (fun z => (SCH).map z) hs).trans ((SCH).map_comp i p))
  have hkill := kill_scheme _ _ _ _ h0 (a ^ k) (fun c hc => closedι_appTop_of_mem (a ^ k) hc)
  obtain ⟨i', hi'⟩ := exists_factor_closed i ((a.map ((SCH).map p).appTop.hom) ^ k) (fun y hy => by
    rw [hIpow] at hy
    exact hkill y hy)
  have := hmonoT (a ^ k)
  have h₂ : i' ≫ f k = s := by
    refine (cancel_mono (Chart.immι T (Chart.closedι ((SCH).obj T) (a ^ k)))).1 ?_
    rw [Category.assoc, hf, hs, ← Category.assoc]
    exact congrArg (· ≫ p) hi'
  have e₁ := hθx k
  rw [← hi', ← h₂, op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply]
  exact congrArg _ e₁

set_option maxHeartbeats 2000000 in
/-- **The gluing of Theorem 4.1, existence** (§4 "Glue", Bhatt Theorem 1.1, Remark, and the checks
after Lemma 4.5). The open and closed strata provide `τ` and `χ`; `Y = Spec Ĉ` is the `a`-adic
completion (only its properties are used), and `hθ` is the compatibility on `V = Y \ V(a)`. -/
theorem exists_glue (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X)
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
  obtain ⟨φ, ⟨hφj, hφp⟩, -⟩ := existsUnique_pushout hX hsep j p a hj hjr hp hcov hsurj τ θ (hθ θ hθk)
  have hφk : ∀ k, X.map (Chart.immι T (Chart.closedι ((SCH).obj T) (a ^ k))).op φ = χ k := by
    intro k
    obtain ⟨σ, hσ⟩ := exists_section_of_quot p (a ^ k) (hsurj k) (hinj k)
    have := hθk k _ σ (𝟙 _) (by rw [Category.id_comp, hσ])
    rw [CategoryTheory.op_id, FunctorToTypes.map_id_apply] at this
    rw [← this, ← hφp, ← Functor.map_comp_apply, ← op_comp, hσ]
  refine ⟨φ, hφj, hφk, fun t h => ?_⟩
  refine equivariant_of_agree actT actX hsep a gens hgens hhom hI φ (fun g hg => ?_) (fun k => ?_) t h
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

/-- **Theorem 4.1, uniqueness**, for a complete pair on `Γ(T)` graded by the action of `D(M)`. -/
theorem thm41_unique [DecidableEq M] (hsep : Space.IsSeparatedOver B S hS X)
    (m : Ideal Γ((SCH).obj T, ⊤))
    (hP : letI := gradedRingOfAction actT; ChartGraded.IsCompletePair (homog actT) m)
    (φ ψ : X.obj (op T))
    (h : ∀ n, X.map (Chart.immι T (Chart.closedι ((SCH).obj T) (m ^ n))).op φ =
      X.map (Chart.immι T (Chart.closedι ((SCH).obj T) (m ^ n))).op ψ) : φ = ψ := by
  letI := gradedRingOfAction actT
  exact Chart.eq_of_agree_of_iInf hsep T (fun n => m ^ n)
    (Chart.iInf_pow_eq_bot (homog actT) m hP.hom hP.sep) φ ψ h

set_option maxHeartbeats 1000000 in
lemma restrict_aux (hsep : Space.IsSeparatedOver B S hS X)
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
  refine Chart.eq_of_agree_basicOpen_of_agree_thickening (C := Γ((SCH).obj E, ⊤)) hsep E
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
theorem restrict_eq_of_strata (hsep : Space.IsSeparatedOver B S hS X)
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
  restrict_aux hsep j hj _ a hjr φ τ hφj χ hφk x hτx hχx

/-- `Γ(V(J))` is noetherian when `Γ(T)` is. -/
lemma isNoetherianRing_closed [IsNoetherianRing Γ((SCH).obj T, ⊤)] (J : Ideal Γ((SCH).obj T, ⊤)) :
    IsNoetherianRing Γ((SCH).obj (Chart.immObj T (Chart.closedι ((SCH).obj T) J)), ⊤) :=
  isNoetherianRing_of_ringEquiv (Γ((SCH).obj T, ⊤) ⧸ J)
    (Scheme.ΓSpecIso (.of (Γ((SCH).obj T, ⊤) ⧸ J))).symm.commRingCatIsoToRingEquiv

/-- **Theorem 4.1, existence, from the two strata.** Given the map on the open stratum (Lemma 4.3)
and the maps on the closed strata (Lemma 4.4), with their compatibilities, `φ` exists, is equivariant,
and extends the given system `x`. -/
theorem thm41_exists_of_strata (hX : IsAlgebraicSpace B S hS X)
    (hsep : Space.IsSeparatedOver B S hS X) (hB : NoetherianAlgebraization X)
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
  obtain ⟨φ, hφj, hφk, heq⟩ := exists_glue actT actX hX hsep hB a gens hgens hhom hI j p hj hjr hp
    hcov hsurj hinj τ hτ χ hχ hχc hθ
  refine ⟨φ, fun n => ?_, heq⟩
  have := isNoetherianRing_closed (m ^ n)
  exact restrict_eq_of_strata hsep j hj a hjr (m ^ n) φ τ hφj χ hφk (x n) (hτx n) (hχx n)

section ClosedAction

lemma exists_closed_lift {J : Ideal Γ((SCH).obj T, ⊤)} (hJ : ∀ x ∈ J, ∀ d, (coact actT x).coeff d ∈ J) {W : BigFppfOver B S hS}
    (h : Multiplicative M →* Γ((SCH).obj W, ⊤))
    (t : W ⟶ Chart.immObj T (Chart.closedι ((SCH).obj T) J)) :
    ∃ s : W ⟶ Chart.immObj T (Chart.closedι ((SCH).obj T) J),
      s ≫ Chart.immι T _ = smulAt actT h (t ≫ Chart.immι T _) := by
  refine exists_factor_closed _ J fun x hx => ?_
  refine appTop_smul_eq_zero actT _ h J hJ (fun y hy => ?_) hx
  rw [Functor.map_comp]
  exact appTop_comp_eq_zero _ _ y
    (by
      have := closedι_appTop_of_mem J hy
      exact (congrArg (fun z => ((SCH).map t).appTop z) this).trans (map_zero _))

lemma mono_immι (J : Ideal Γ((SCH).obj T, ⊤)) : Mono (Chart.immι T (Chart.closedι ((SCH).obj T) J)) :=
  (SCH).mono_of_mono_map (inferInstanceAs (Mono (Chart.closedι ((SCH).obj T) J)))

/-- The action of `D(M)` on the stable closed `V(J)`, by restriction. -/
noncomputable def closedAct {J : Ideal Γ((SCH).obj T, ⊤)} (hJ : ∀ x ∈ J, ∀ d, (coact actT x).coeff d ∈ J) :
    AAction (fppfO B S hS) M (yoneda.obj (Chart.immObj T (Chart.closedι ((SCH).obj T) J))) where
  smul {W} h t := (exists_closed_lift actT hJ (W := unop W) h t).choose
  one_smul {W} t := by
    have := mono_immι (T := T) J
    refine (cancel_mono (Chart.immι T _)).1 ?_
    exact (exists_closed_lift actT hJ (W := unop W) 1 t).choose_spec.trans (smulAt_one actT _)
  mul_smul {W} g h t := by
    have := mono_immι (T := T) J
    refine (cancel_mono (Chart.immι T _)).1 ?_
    refine (exists_closed_lift actT hJ (W := unop W) (g * h) t).choose_spec.trans ?_
    refine (smulAt_mul actT g h _).trans ?_
    refine Eq.trans ?_ (exists_closed_lift actT hJ (W := unop W) g _).choose_spec.symm
    exact congrArg _ (exists_closed_lift actT hJ (W := unop W) h t).choose_spec.symm
  map_smul {W V} e h t := by
    have := mono_immι (T := T) J
    refine (cancel_mono (Chart.immι T _)).1 ?_
    change (e.unop ≫ (exists_closed_lift actT hJ (W := unop W) h t).choose) ≫ _ = _
    rw [Category.assoc, (exists_closed_lift actT hJ (W := unop W) h t).choose_spec]
    refine (comp_smulAt actT e.unop h _).trans ?_
    refine Eq.trans ?_ (exists_closed_lift actT hJ (W := unop V) _ (e.unop ≫ t)).choose_spec.symm
    rw [Category.assoc]
    rfl

lemma closedAct_spec {J : Ideal Γ((SCH).obj T, ⊤)} (hJ : ∀ x ∈ J, ∀ d, (coact actT x).coeff d ∈ J) {W : BigFppfOver B S hS} (h : Multiplicative M →* Γ((SCH).obj W, ⊤))
    (t : W ⟶ Chart.immObj T (Chart.closedι ((SCH).obj T) J)) :
    smulAt (closedAct actT hJ) h t ≫ Chart.immι T _ = smulAt actT h (t ≫ Chart.immι T _) :=
  (exists_closed_lift actT hJ (W := W) h t).choose_spec

end ClosedAction

end Equivariance

/-- **Lemma 4.2**, as a named proposition (not proved here): `X` nonempty, with an action of `D(M)`,
has a nonempty stable affine open. -/
def AffineStratum {M : Type u} [AddCommGroup M] (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (actX : AAction (fppfO B S hS) M X) : Prop :=
  (∃ W : BigFppfOver B S hS, Nonempty ((SCH).obj W) ∧ Nonempty (X.obj (op W))) →
  ∃ (U : BigFppfOver B S hS) (actU : AAction (fppfO B S hS) M (yoneda.obj U))
    (f : yoneda.obj U ⟶ X), IsAffine ((SCH).obj U) ∧ Nonempty ((SCH).obj U) ∧
      IsEquivariant actU actX f ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@IsOpenImmersion.{u} : MorphismProperty Scheme.{u}) (SCH))) f

end AlgMag.ChartMain

#print axioms AlgMag.ChartMain.existsUnique_pushout
#print axioms AlgMag.ChartMain.equivariant_of_agree
#print axioms AlgMag.ChartMain.thm41_unique
#print axioms AlgMag.ChartMain.thm41_exists_of_strata
