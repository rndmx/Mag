/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartBridge
import AlgMag.ChartEffective
import AlgMag.ChartAlgebraize

/-!
# Conclusion of the chart: the geometric part of §§5–6 of the chart-lemma proof

* `IsCompletePair.toCompletePair`: the bridge between the two forms of a complete pair.
* `EquivariantEffectivity`: **Theorem 4.1**, as a named statement (left to the §4 work).
* `ArtinApproxFP`: Artin approximation (§5), as a named statement, in the finitely presented form.
* `basicOpenAction`: the action of `D(M)` on `D(h)`, for `h` of degree `0`.
* `isChartAt_basicOpen`, `exists_chart_of_stable`: **§6, Conclusion**, on the site.

* `syzygies_homogeneous`: homogeneous syzygies of `f` over `Q`.
* `sup_eq_top_of_orbit`, `exists_chart_of_etaleAt`, `exists_chart_of_section5`.

The functor `F` of §5 and the construction of `W` are not carried out here: `Section5Output` and
`EtaleLocusStable` are the exact statements left open by this file.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry DirectSum

universe u

namespace AlgMag.ChartConclude

/-- Bridge between `AlgMag.ChartGraded.IsCompletePair` (§3) and `AlgMag.ChartAlg.CompletePair` (§5).
-/
theorem toCompletePair {M C : Type*} [AddCommGroup M] [DecidableEq M] [CommRing C]
    {𝒞 : M → AddSubgroup C} [GradedRing 𝒞] {m : Ideal C}
    (h : ChartGraded.IsCompletePair 𝒞 m) : ChartAlg.CompletePair 𝒞 m :=
  ⟨h.hom, h.sep, h.exists_lim⟩

/-- **Artin 1969, Cor 2.2** (§5 of the note, input I2) at a maximal ideal `𝔭` of a finite type
`ℤ`-algebra `A`, for a finitely presented `A`-algebra `B₀` with a map `h : B₀ → Â` to the `𝔭`-adic
completion: there are an étale `A → A'` with an `A`-algebra map `σ : A' → A/𝔭^N` (the point `𝔮` of the
note over `𝔭` is `σ⁻¹(𝔭/𝔭^N)`, with trivial residue extension) and `θ : B₀ → A'` congruent to `h` modulo
`𝔭^N`.

This is the functor form `AlgMag.ChartArtin.artinApprox_of_finiteType_int` for the functor
`Hom_A(B₀, -)`, stated without that file because its Stacks modules have no oleans here. Limit
preservation is used in that proof only over `Â`, which is why it is not an argument here. -/
def ArtinApproxFP : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra.FiniteType ℤ A] (𝔭 : Ideal A) [𝔭.IsMaximal]
    (B₀ : Type u) [CommRing B₀] [Algebra A B₀] [Algebra.FinitePresentation A B₀]
    (h : B₀ →ₐ[A] AdicCompletion 𝔭 A) (N : ℕ),
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Algebra.Etale A A')
      (σ : A' →ₐ[A] A ⧸ 𝔭 ^ N) (θ : B₀ →ₐ[A] A'),
      ∀ b : B₀, σ (θ b) = AdicCompletion.evalₐ 𝔭 N (h b)

section Syzygies

open MvPolynomial ChartAlg TensorProduct

variable {C M ι : Type*} [CommRing C] [AddCommGroup M] [DecidableEq M] [Finite ι]
  {m : Ideal C} {w : ι → M} {x : ι → C}

omit [Finite ι] in
lemma piP_mul (d e : M) (p q : MvPolynomial ι ℤ) :
    piP w (d + e) (p * piP w e q) = piP w d p * piP w e q := by
  classical
  have hq : IsWeightedHomogeneous w (piP w e q) e :=
    weightedHomogeneousComponent_isWeightedHomogeneous e q
  induction p using MvPolynomial.induction_on' with
  | monomial a c =>
    have hm : IsWeightedHomogeneous w (monomial a c) (Finsupp.weight w a) :=
      isWeightedHomogeneous_monomial w a c rfl
    have hmq := hm.mul hq
    change weightedHomogeneousComponent w (d + e) _ = weightedHomogeneousComponent w d _ * _
    by_cases h : Finsupp.weight w a = d
    · subst h
      rw [hmq.weightedHomogeneousComponent_same, hm.weightedHomogeneousComponent_same]
    · rw [hmq.weightedHomogeneousComponent_ne (d + e) (fun e' => h (add_right_cancel e'.symm)),
        hm.weightedHomogeneousComponent_ne d (Ne.symm h), zero_mul]
  | add p q' hp hq' =>
    rw [add_mul, (piP w (d + e)).map_add, (piP w d).map_add, add_mul, hp, hq']

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
lemma qProj_mul (d e : M) (a b : Qring w x m) :
    qProj (d + e) (a * qProj e b) = qProj d a * qProj e b := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add a a' h h' => rw [add_mul, map_add, map_add, add_mul, h, h']
  | tmul p y =>
    induction b using TensorProduct.induction_on with
    | zero => simp
    | add b b' h h' => simp only [map_add, mul_add, h, h']
    | tmul q z =>
      rw [qProj_tmul, qProj_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, qProj_tmul, piP_mul]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
/-- **§5**: "Let `(r_tℓ)` be homogeneous generators of the syzygies of `f` over `Q`." `r_jℓ` has degree
`dr j - deg ℓ`. Noetherianity of `Q` is the hypothesis of `AlgMag.ChartAlg.Qmap_ker_homogeneous`. -/
theorem syzygies_homogeneous [IsNoetherianRing (Qring w x m)] {s : ℕ} (f : Fin s → Qring w x m)
    (deg : Fin s → M) (hf : ∀ ℓ, qProj (deg ℓ) (f ℓ) = f ℓ) :
    ∃ (t : ℕ) (r : Fin t → Fin s → Qring w x m) (dr : Fin t → M),
      (∀ j ℓ, qProj (dr j - deg ℓ) (r j ℓ) = r j ℓ) ∧
      Submodule.span (Qring w x m) (Set.range r) =
        LinearMap.ker (Fintype.linearCombination (Qring w x m) f) := by
  classical
  let θ := Fintype.linearCombination (Qring w x m) f
  have θapp : ∀ a, θ a = ∑ ℓ, a ℓ * f ℓ := fun a => by
    simp [θ, Fintype.linearCombination_apply]
  obtain ⟨T, hT⟩ := (IsNoetherian.noetherian (LinearMap.ker θ) : (LinearMap.ker θ).FG)
  -- the degree `D` part of a vector
  let pr : M → (Fin s → Qring w x m) → (Fin s → Qring w x m) :=
    fun D g ℓ => qProj (D - deg ℓ) (g ℓ)
  have hpr : ∀ D g, θ (pr D g) = qProj D (θ g) := by
    intro D g
    rw [θapp, θapp, map_sum]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    have := qProj_mul (w := w) (x := x) (m := m) (D - deg ℓ) (deg ℓ) (g ℓ) (f ℓ)
    rw [hf ℓ, sub_add_cancel] at this
    exact this.symm
  have hprI : ∀ D g ℓ, qProj (D - deg ℓ) (pr D g ℓ) = pr D g ℓ := fun D g ℓ => qProj_idem _ _
  -- finiteness of the components
  have hsum : ∀ g : Fin s → Qring w x m, ∃ S : Finset M, ∑ D ∈ S, pr D g = g := by
    intro g
    choose S₀ hS₀ using fun ℓ => sum_qProj (w := w) (x := x) (m := m) (g ℓ)
    let S : Finset M := Finset.univ.biUnion fun ℓ => (S₀ ℓ).image (· + deg ℓ)
    refine ⟨S, funext fun ℓ => ?_⟩
    rw [Finset.sum_apply]
    have hsub : S₀ ℓ ⊆ S.image (· - deg ℓ) := fun d hd => Finset.mem_image.2
      ⟨d + deg ℓ, Finset.mem_biUnion.2 ⟨ℓ, Finset.mem_univ _, Finset.mem_image_of_mem _ hd⟩,
        add_sub_cancel_right _ _⟩
    conv_rhs => rw [← hS₀ ℓ _ hsub]
    rw [Finset.sum_image (fun a _ b _ h => sub_left_injective h)]
  choose S hS using hsum
  let G : Finset (M × (Fin s → Qring w x m)) :=
    T.biUnion fun g => (S g).image fun D => (D, pr D g)
  let e := G.equivFin
  refine ⟨G.card, fun j => (e.symm j).1.2, fun j => (e.symm j).1.1, fun j ℓ => ?_,
    le_antisymm ?_ ?_⟩
  · obtain ⟨g, _, hg⟩ := Finset.mem_biUnion.1 (e.symm j).2
    obtain ⟨D, _, hD⟩ := Finset.mem_image.1 hg
    beta_reduce
    rw [← hD]
    exact hprI D g ℓ
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨g, hgT, hg⟩ := Finset.mem_biUnion.1 (e.symm j).2
    obtain ⟨D, _, hD⟩ := Finset.mem_image.1 hg
    beta_reduce
    rw [← hD]
    have h0 : θ g = 0 := by
      have : g ∈ LinearMap.ker θ := by rw [← hT]; exact Submodule.subset_span hgT
      exact this
    change θ (pr D g) = 0
    rw [hpr, h0, map_zero]
  · rw [← hT, Submodule.span_le]
    intro g hg
    rw [← hS g]
    refine Submodule.sum_mem _ fun D hD => Submodule.subset_span ?_
    have hmem : (D, pr D g) ∈ G :=
      Finset.mem_biUnion.2 ⟨g, hg, Finset.mem_image_of_mem _ hD⟩
    exact ⟨e ⟨_, hmem⟩, by simp⟩

end Syzygies

/-- Ring lemma of §6: "`Ω` contains `w` and so `O`". If every homogeneous element outside `I_O` is a
unit modulo `I_O` (`O` is one orbit), `I` is stable and `g ∈ I` does not vanish at the point
`u : A → k` with `u(I_O) = 0`, then `I_O + I = 1`. -/
theorem sup_eq_top_of_orbit {A M k : Type*} [CommRing A] [AddCommGroup M] [DecidableEq M]
    (𝒜 : M → AddSubgroup A) [GradedRing 𝒜] [CommRing k] [IsDomain k] (u : A →+* k) {I IO : Ideal A}
    (hI : ChartAlg.IsStableClosed 𝒜 I) (hu : ∀ a ∈ IO, u a = 0)
    (hO : ∀ d, ∀ c ∈ 𝒜 d, c ∉ IO → ∃ c', c * c' - 1 ∈ IO) {g : A} (hg : g ∈ I) (hgu : u g ≠ 0) :
    IO ⊔ I = ⊤ := by
  classical
  obtain ⟨e, he⟩ := hI g hg
  have hne : u (g ^ e) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ hgu
  have : ∃ d, u ((decompose 𝒜 (g ^ e) d : 𝒜 d) : A) ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    apply hne
    rw [← DirectSum.sum_support_decompose 𝒜 (g ^ e), map_sum]
    exact Finset.sum_eq_zero fun d _ => hall d
  obtain ⟨d, hd⟩ := this
  have hcO : ((decompose 𝒜 (g ^ e) d : 𝒜 d) : A) ∉ IO := fun h => hd (hu _ h)
  obtain ⟨c', hc'⟩ := hO d _ (SetLike.coe_mem _) hcO
  rw [Ideal.eq_top_iff_one]
  have h1 : ((decompose 𝒜 (g ^ e) d : 𝒜 d) : A) * c' ∈ IO ⊔ I :=
    Submodule.mem_sup_right (Ideal.mul_mem_right c' I (he d))
  have h2 : ((decompose 𝒜 (g ^ e) d : 𝒜 d) : A) * c' - 1 ∈ IO ⊔ I := Submodule.mem_sup_left hc'
  have := sub_mem h1 h2
  rwa [sub_sub_cancel] at this

section Site

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M]

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- **Theorem 4.1** for `X` (equivariant effectivity), as a named statement: every compatible system
of equivariant maps `Spec C/mⁿ → X` from the truncations of a complete pair `(C, m)` extends to an
equivariant `Spec C → X` (existence only; uniqueness of the note's statement is not needed here). `T` is the object `Spec C`, with `Γ(T) = C` graded by `actT`. -/
def EquivariantEffectivity [AddMonoid.FG M] (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (actX : AAction (fppfO B S hS) M X) : Prop :=
  ∀ (T : BigFppfOver B S hS) [IsAffine ((SCH).obj T)] (actT : AAction (fppfO B S hS) M (yoneda.obj T))
    [DecidableEq M] (m : Ideal Γ((SCH).obj T, ⊤)),
    (letI := ChartMain.gradedRingOfAction actT
     ChartGraded.IsCompletePair (ChartMain.homog actT) m) →
    ∀ (φ : ∀ n : ℕ, X.obj (op (Chart.immObj T (Chart.closedι ((SCH).obj T) (m ^ n))))),
      (∀ (n k : ℕ) (t : Chart.immObj T (Chart.closedι ((SCH).obj T) (m ^ n)) ⟶
          Chart.immObj T (Chart.closedι ((SCH).obj T) (m ^ k))),
        t ≫ Chart.immι T _ = Chart.immι T _ → X.map t.op (φ k) = φ n) →
      (∀ (n : ℕ) (Y : BigFppfOver B S hS) (t : Y ⟶ Chart.immObj T (Chart.closedι ((SCH).obj T) (m ^ n)))
        (g : APt (fppfO B S hS) M (op Y)) (t' : Y ⟶ Chart.immObj T (Chart.closedι ((SCH).obj T) (m ^ n))),
        t' ≫ Chart.immι T _ = actT.smul g (t ≫ Chart.immι T _) →
          X.map t'.op (φ n) = actX.smul g (X.map t.op (φ n))) →
      ∃ φ' : yoneda.obj T ⟶ X, IsEquivariant actT actX φ' ∧
        ∀ n, φ'.app _ (Chart.immι T (Chart.closedι ((SCH).obj T) (m ^ n))) = φ n

/-! ### The open `D(h)`, for `h` of degree `0` -/

section BasicOpen

variable (W : BigFppfOver B S hS)

/-- `D(h) ⊆ W`, as an object of the site. -/
noncomputable abbrev dObj (h : Γ((SCH).obj W, ⊤)) : BigFppfOver B S hS :=
  Chart.immObj W ((SCH).obj W |>.basicOpen h).ι

/-- The inclusion `D(h) ⟶ W`. -/
noncomputable abbrev dι (h : Γ((SCH).obj W, ⊤)) : dObj W h ⟶ W := Chart.immι W ((SCH).obj W |>.basicOpen h).ι

instance dιOpen (h : Γ((SCH).obj W, ⊤)) : IsOpenImmersion ((SCH).obj W |>.basicOpen h).ι :=
  inferInstanceAs (IsOpenImmersion (Scheme.Opens.ι _))

instance (h : Γ((SCH).obj W, ⊤)) : Mono (dι W h) := by
  refine ⟨fun a b e => ChartMain.siteExt ?_⟩
  have e' := congrArg (fun z => (SCH).map z) e
  simp only [Functor.map_comp] at e'
  exact (cancel_mono (((SCH).obj W |>.basicOpen h).ι)).1 e'

variable {W}

lemma isUnit_of_factors [IsAffine ((BigFppfOver.toScheme B S hS).obj W)] {h : Γ((SCH).obj W, ⊤)} {T : BigFppfOver B S hS} (t : T ⟶ dObj W h) :
    IsUnit (((SCH).map (t ≫ dι W h)).appTop.hom h) := by
  have hunit : IsUnit ((((SCH).obj W |>.basicOpen h).ι).appTop.hom h) := by
    have := (isAffineOpen_top ((SCH).obj W)).isLocalization_basicOpen h
    have h2 := IsLocalization.Away.algebraMap_isUnit (S := Γ((SCH).obj W, ((SCH).obj W).basicOpen h)) h
    simp only [Scheme.Opens.ι_appTop]
    rw [RingHom.algebraMap_toAlgebra] at h2
    have key : ∀ (V : ((SCH).obj W).Opens) (_ : V = ((SCH).obj W).basicOpen h)
        (le : V ≤ ⊤), IsUnit ((((SCH).obj W).presheaf.map (homOfLE le).op).hom h) := by
      rintro _ rfl le
      exact h2
    exact key _ (by simp) _
  rw [Functor.map_comp, Scheme.Hom.comp_appTop]
  exact hunit.map ((SCH).map t).appTop.hom

lemma range_sub_of_isUnit {h : Γ((SCH).obj W, ⊤)} {T : BigFppfOver B S hS} (τ : T ⟶ W)
    (hu : IsUnit (((SCH).map τ).appTop.hom h)) :
    Set.range ((SCH).map τ) ⊆ Set.range ((SCH).obj W |>.basicOpen h).ι := by
  rintro _ ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι]
  have e : (SCH).map τ ⁻¹ᵁ ((SCH).obj W).basicOpen h =
      ((SCH).obj T).basicOpen (((SCH).map τ).appTop h) := Scheme.preimage_basicOpen _ _
  have e2 : ((SCH).obj T).basicOpen (((SCH).map τ).appTop h) = ⊤ :=
    Scheme.basicOpen_of_isUnit _ hu
  have : x ∈ (SCH).map τ ⁻¹ᵁ ((SCH).obj W).basicOpen h := by rw [e, e2]; trivial
  exact this

/-- The scheme map underlying `dLift`. -/
noncomputable def dLiftS {h : Γ((SCH).obj W, ⊤)} {T : BigFppfOver B S hS} (τ : T ⟶ W)
    (hu : IsUnit (((SCH).map τ).appTop.hom h)) :
    (SCH).obj T ⟶ (((SCH).obj W).basicOpen h).toScheme :=
  @IsOpenImmersion.lift _ _ _ (((SCH).obj W).basicOpen h).ι ((SCH).map τ) (dιOpen W h)
    (range_sub_of_isUnit τ hu)

lemma dLiftS_fac {h : Γ((SCH).obj W, ⊤)} {T : BigFppfOver B S hS} (τ : T ⟶ W)
    (hu : IsUnit (((SCH).map τ).appTop.hom h)) :
    dLiftS τ hu ≫ ((SCH).obj W |>.basicOpen h).ι = (SCH).map τ :=
  @IsOpenImmersion.lift_fac _ _ _ (((SCH).obj W).basicOpen h).ι ((SCH).map τ) (dιOpen W h) _

/-- A map to `W` on which `h` is a unit factors through `D(h)`. -/
noncomputable def dLift {h : Γ((SCH).obj W, ⊤)} {T : BigFppfOver B S hS} (τ : T ⟶ W)
    (hu : IsUnit (((SCH).map τ).appTop.hom h)) : T ⟶ dObj W h :=
  Over.homMk ⟨dLiftS τ hu⟩ (by
    apply InducedCategory.hom_ext
    change dLiftS τ hu ≫ ((SCH).obj W |>.basicOpen h).ι ≫ W.hom.hom = T.hom.hom
    rw [← Category.assoc, dLiftS_fac]
    exact congrArg (fun z => z.hom) (Over.w τ))

@[simp]
lemma dLift_ι {h : Γ((SCH).obj W, ⊤)} {T : BigFppfOver B S hS} (τ : T ⟶ W)
    (hu : IsUnit (((SCH).map τ).appTop.hom h)) : dLift τ hu ≫ dι W h = τ :=
  ChartMain.siteExt (by
    rw [Functor.map_comp]; exact dLiftS_fac τ hu)

variable [AddMonoid.FG M] [IsAffine ((BigFppfOver.toScheme B S hS).obj W)] (actW : AAction (fppfO B S hS) M (yoneda.obj W))

/-- `h` of degree `0` stays a unit under the action. -/
lemma isUnit_smul {h : Γ((SCH).obj W, ⊤)} (h0 : h ∈ ChartMain.homog actW 0) {T : BigFppfOver B S hS}
    (g : Multiplicative M →* Γ((SCH).obj T, ⊤)) (t : T ⟶ dObj W h) :
    IsUnit (((SCH).map (ChartMain.smulAt actW g (t ≫ dι W h))).appTop.hom h) := by
  rw [ChartMain.appTop_smul_of_mem actW (t ≫ dι W h) (T := T) g h0]
  have : (g (Multiplicative.ofAdd (0 : M))) = 1 := by simp
  rw [this, mul_one]
  exact isUnit_of_factors t

/-- The action of `D(M)` on `D(h)`, for `h` of degree `0`. -/
noncomputable def basicOpenAction {h : Γ((SCH).obj W, ⊤)} (h0 : h ∈ ChartMain.homog actW 0) :
    AAction (fppfO B S hS) M (yoneda.obj (dObj W h)) where
  smul {T} g t := dLift (ChartMain.smulAt actW (T := T.unop) g (t ≫ dι W h)) (isUnit_smul actW h0 g t)
  one_smul {T} t := (cancel_mono (dι W h)).1 (by
    rw [dLift_ι]; exact ChartMain.smulAt_one actW _)
  mul_smul {T} g k t := (cancel_mono (dι W h)).1 (by
    rw [dLift_ι, dLift_ι, dLift_ι]
    exact actW.mul_smul (U := T) g k (t ≫ dι W h))
  map_smul {T V} e g t := (cancel_mono (dι W h)).1 (by
    change (e.unop ≫ dLift _ _) ≫ dι W h = dLift _ _ ≫ dι W h
    rw [Category.assoc, dLift_ι, dLift_ι]
    have := actW.map_smul (F := yoneda.obj W) e g (t ≫ dι W h)
    simpa [ChartMain.smulAt] using this)

lemma basicOpenAction_ι {h : Γ((SCH).obj W, ⊤)} (h0 : h ∈ ChartMain.homog actW 0) {T : (BigFppfOver B S hS)ᵒᵖ}
    (g : APt (fppfO B S hS) M T) (t : T.unop ⟶ dObj W h) :
    ((basicOpenAction actW h0).smul (F := yoneda.obj (dObj W h)) g t) ≫ dι W h =
      actW.smul (F := yoneda.obj W) g (t ≫ dι W h) :=
  dLift_ι _ (isUnit_smul actW h0 (T := T.unop) g t)

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {actX : AAction (fppfO B S hS) M X}

/-- **§6, Conclusion**: `U := D(h)`. Let `W` be affine with action, `f : W → X` equivariant, `h ∈ A₀`
with `D(h) → X` étale, and `u₀ : Spec k → W` a point over `x` at which `h` is a unit and whose
stabilizer is that of `x`. Then `D(h)` is a chart at `x`. -/
theorem isChartAt_basicOpen {h : Γ((SCH).obj W, ⊤)} (p : ChartPoint X) (f : yoneda.obj W ⟶ X)
    (hf : IsEquivariant actW actX f) (h0 : h ∈ ChartMain.homog actW 0)
    (het : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) (yoneda.map (dι W h) ≫ f))
    (u₀ : p.P ⟶ W) (hover : yoneda.map u₀ ≫ f = p.x)
    (hu : IsUnit (((SCH).map u₀).appTop.hom h))
    (hstab : ∀ {T : BigFppfOver B S hS} (t : T ⟶ p.P) (g : APt (fppfO B S hS) M (op T)),
      actX.smul g (f.app (op T) (t ≫ u₀)) = f.app (op T) (t ≫ u₀) →
        actW.smul (F := yoneda.obj W) g (t ≫ u₀) = t ≫ u₀) :
    IsChartAt actX p (dObj W h) (basicOpenAction actW h0) (yoneda.map (dι W h) ≫ f) (dLift u₀ hu) where
  affine := by
    have : IsAffineOpen (((SCH).obj W).basicOpen h) := (isAffineOpen_top _).basicOpen h
    exact this
  equivariant := by
    intro T g t
    change f.app T ((basicOpenAction actW h0).smul (F := yoneda.obj (dObj W h)) g t ≫ dι W h) = _
    rw [basicOpenAction_ι]
    exact hf g _
  etale := het
  lies_over := by
    rw [← Functor.map_comp_assoc, dLift_ι]; exact hover
  stabilizer := by
    intro T t g hg
    refine (cancel_mono (dι W h)).1 ?_
    rw [basicOpenAction_ι, Category.assoc, dLift_ι]
    refine hstab t g ?_
    have e : ∀ s : T ⟶ dObj W h, (yoneda.map (dι W h) ≫ f).app (op T) s = f.app (op T) (s ≫ dι W h) :=
      fun _ => rfl
    have hg' := hg
    rw [e, Category.assoc, dLift_ι] at hg'
    exact hg'

end BasicOpen

/-- **§6, Conclusion, with the Shrinking Lemma.** `W` is affine with action, `f : W → X` equivariant,
`V(I)` a stable closed subset off which `f` is étale, disjoint from the closed stable orbit `V(I_O)`,
through which `u₀ : Spec k → W` factors. Then `X` has a chart at `x`. -/
theorem exists_chart_of_stable [AddMonoid.FG M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {actX : AAction (fppfO B S hS) M X} (p : ChartPoint X) (W : BigFppfOver B S hS)
    [IsAffine ((SCH).obj W)] (actW : AAction (fppfO B S hS) M (yoneda.obj W))
    (f : yoneda.obj W ⟶ X) (hf : IsEquivariant actW actX f) [DecidableEq M]
    (I IO : Ideal Γ((SCH).obj W, ⊤))
    (hI : letI := ChartMain.gradedRingOfAction actW
      ChartAlg.IsStableClosed (ChartMain.homog actW) I)
    (hO : letI := ChartMain.gradedRingOfAction actW; IO.IsHomogeneous (ChartMain.homog actW))
    (hdisj : IO ⊔ I = ⊤)
    (het : ∀ g ∈ I, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) (yoneda.map (dι W g) ≫ f))
    (u₀ : p.P ⟶ W) (hover : yoneda.map u₀ ≫ f = p.x)
    (huO : ∀ a ∈ IO, ((SCH).map u₀).appTop.hom a = 0)
    (hstab : ∀ {T : BigFppfOver B S hS} (t : T ⟶ p.P) (g : APt (fppfO B S hS) M (op T)),
      actX.smul g (f.app (op T) (t ≫ u₀)) = f.app (op T) (t ≫ u₀) →
        actW.smul (F := yoneda.obj W) g (t ≫ u₀) = t ≫ u₀) :
    ∃ (U : BigFppfOver B S hS) (actU : AAction (fppfO B S hS) M (yoneda.obj U))
      (f' : yoneda.obj U ⟶ X) (u : p.P ⟶ U), IsChartAt actX p U actU f' u := by
  let _ := ChartMain.gradedRingOfAction actW
  obtain ⟨h, h0, hI', h1⟩ := ChartAlg.shrinking (ChartMain.homog actW) hI hO hdisj
  have hu : IsUnit (((SCH).map u₀).appTop.hom h) := by
    have := huO _ h1
    rw [map_sub, map_one, sub_eq_zero] at this
    rw [← this]; exact isUnit_one
  exact ⟨_, _, _, _, isChartAt_basicOpen actW p f hf h0 (het h hI') u₀ hover hu hstab⟩


/-- `D(g) → X` is étale. -/
def IsEtaleOn {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {W : BigFppfOver B S hS}
    (f : yoneda.obj W ⟶ X) (g : Γ((SCH).obj W, ⊤)) : Prop :=
  (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) (yoneda.map (dι W g) ≫ f)

/-- **§6**: "`Ω`, the étale locus of `φ̃` on `W`, is open and `G`-stable." The ideal `I` cuts out the
complement of the étale locus. NOT PROVED here: stability needs the fpqc descent of étaleness along
`W × D(M) → W`, and the last clause needs that étaleness over `X` is local on the source. -/
def EtaleLocusStable [AddMonoid.FG M] [DecidableEq M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {W : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    (actW : AAction (fppfO B S hS) M (yoneda.obj W)) (f : yoneda.obj W ⟶ X) : Prop :=
  ∃ I : Ideal Γ((SCH).obj W, ⊤),
    (letI := ChartMain.gradedRingOfAction actW; ChartAlg.IsStableClosed (ChartMain.homog actW) I) ∧
    (∀ g ∈ I, IsEtaleOn f g) ∧ ∀ g, IsEtaleOn f g → g ∈ I.radical

/-- `Γ(Spec k)` is a domain. -/
lemma isDomain_point {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : ChartPoint X) :
    IsDomain Γ((SCH).obj p.P, ⊤) := by
  letI := p.field
  let e1 : Γ((SCH).obj p.P, ⊤) ≃+* Γ(Spec (.of p.k), ⊤) :=
    (Scheme.Γ.mapIso p.iso.symm.op).commRingCatIsoToRingEquiv
  let e2 : Γ(Spec (.of p.k), ⊤) ≃+* p.k := (Scheme.ΓSpecIso (.of p.k)).commRingCatIsoToRingEquiv
  exact (e1.trans e2).injective.isDomain (e1.trans e2).toRingHom

/-- **§§5–6, Étale + Conclusion.** `W` affine with action, `φ̃ : W → X` equivariant, with `w` over `x`,
`O = V(I_O)` the orbit, the stabilizer of `w` that of `x`, `φ̃` étale at `w` and the étale locus
stable: then `X` has a chart at `x`. -/
theorem exists_chart_of_etaleAt [AddMonoid.FG M] [DecidableEq M]
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {actX : AAction (fppfO B S hS) M X} (p : ChartPoint X)
    (W : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    (actW : AAction (fppfO B S hS) M (yoneda.obj W))
    (f : yoneda.obj W ⟶ X) (hf : IsEquivariant actW actX f) (IO : Ideal Γ((SCH).obj W, ⊤))
    (hO : letI := ChartMain.gradedRingOfAction actW; IO.IsHomogeneous (ChartMain.homog actW))
    (hOf : ∀ d, ∀ c ∈ ChartMain.homog actW d, c ∉ IO → ∃ c', c * c' - 1 ∈ IO)
    (hΩ : EtaleLocusStable actW f)
    (u₀ : p.P ⟶ W) (hover : yoneda.map u₀ ≫ f = p.x)
    (huO : ∀ a ∈ IO, ((SCH).map u₀).appTop.hom a = 0)
    (g₀ : Γ((SCH).obj W, ⊤)) (hg₀ : IsEtaleOn f g₀) (hug₀ : ((SCH).map u₀).appTop.hom g₀ ≠ 0)
    (hstab : ∀ {T : BigFppfOver B S hS} (t : T ⟶ p.P) (g : APt (fppfO B S hS) M (op T)),
      actX.smul g (f.app (op T) (t ≫ u₀)) = f.app (op T) (t ≫ u₀) →
        actW.smul (F := yoneda.obj W) g (t ≫ u₀) = t ≫ u₀) :
    ∃ (U : BigFppfOver B S hS) (actU : AAction (fppfO B S hS) M (yoneda.obj U))
      (f' : yoneda.obj U ⟶ X) (u : p.P ⟶ U), IsChartAt actX p U actU f' u := by
  let _ := ChartMain.gradedRingOfAction actW
  obtain ⟨I, hIs, hIe, hIr⟩ := hΩ
  obtain ⟨e, he⟩ := hIr g₀ hg₀
  have := isDomain_point p
  have hne : ((SCH).map u₀).appTop.hom (g₀ ^ e) ≠ 0 := by
    rw [map_pow]; exact pow_ne_zero _ hug₀
  have top := sup_eq_top_of_orbit (ChartMain.homog actW) ((SCH).map u₀).appTop.hom hIs huO hOf he hne
  exact exists_chart_of_stable p W actW f hf I IO hIs hO top hIe u₀ hover huO hstab

/-- **What §5 has to produce**, and which this file does not construct: from the complete pair `C`,
`φ : Spec C → X` of Theorem 4.1 and Artin approximation, the affine `W`, the map `φ̃`, the orbit and
the point `w`, with `φ̃` étale at `w`. -/
def Section5Output [AddMonoid.FG M] [DecidableEq M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (actX : AAction (fppfO B S hS) M X) (p : ChartPoint X) : Prop :=
  ∃ (W : BigFppfOver B S hS) (_ : IsAffine ((BigFppfOver.toScheme B S hS).obj W))
    (actW : AAction (fppfO B S hS) M (yoneda.obj W)) (f : yoneda.obj W ⟶ X)
    (IO : Ideal Γ((SCH).obj W, ⊤)) (u₀ : p.P ⟶ W) (g₀ : Γ((SCH).obj W, ⊤)),
    IsEquivariant actW actX f ∧
    (letI := ChartMain.gradedRingOfAction actW; IO.IsHomogeneous (ChartMain.homog actW)) ∧
    (∀ d, ∀ c ∈ ChartMain.homog actW d, c ∉ IO → ∃ c', c * c' - 1 ∈ IO) ∧
    EtaleLocusStable actW f ∧
    yoneda.map u₀ ≫ f = p.x ∧
    (∀ a ∈ IO, ((SCH).map u₀).appTop.hom a = 0) ∧
    IsEtaleOn f g₀ ∧ ((SCH).map u₀).appTop.hom g₀ ≠ 0 ∧
    ∀ {T : BigFppfOver B S hS} (t : T ⟶ p.P) (g : APt (fppfO B S hS) M (op T)),
      actX.smul g (f.app (op T) (t ≫ u₀)) = f.app (op T) (t ≫ u₀) →
        actW.smul (F := yoneda.obj W) g (t ≫ u₀) = t ≫ u₀

/-- `IsChartAt` from `Section5Output`. -/
theorem exists_chart_of_section5 [AddMonoid.FG M] [DecidableEq M]
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {actX : AAction (fppfO B S hS) M X} (p : ChartPoint X)
    (h : Section5Output actX p) :
    ∃ (U : BigFppfOver B S hS) (actU : AAction (fppfO B S hS) M (yoneda.obj U))
      (f' : yoneda.obj U ⟶ X) (u : p.P ⟶ U), IsChartAt actX p U actU f' u := by
  obtain ⟨W, _, actW, f, IO, u₀, g₀, hf, hO, hOf, hΩ, hover, huO, hg₀, hug₀, hstab⟩ := h
  exact exists_chart_of_etaleAt p W actW f hf IO hO hOf hΩ u₀ hover huO g₀ hg₀ hug₀ hstab

end Site

end AlgMag.ChartConclude

#print axioms AlgMag.ChartConclude.isChartAt_basicOpen
#print axioms AlgMag.ChartConclude.exists_chart_of_stable
#print axioms AlgMag.ChartConclude.syzygies_homogeneous
#print axioms AlgMag.ChartConclude.exists_chart_of_section5
