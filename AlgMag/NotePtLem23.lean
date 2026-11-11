/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.NotePtLem22

/-!
# Existence of strongly-FPR atlases: Lemma 2.3 as printed

Mayeux, *Existence of strongly-FPR atlases* (no journal version), Lemma 2.3.

`AlgMag.NotePt.lem23`: for `f : U = Spec A → X` equivariant étale, `Ω = {u | G_u = G_{f(u)}}` is the union of the `D(a)`, over
the homogeneous elements `a` of a graded ideal `J ⊆ A`; each such `D(a)` is an affine `D(M)`-stable open subscheme, and
`D(a) → X` is strongly-FPR. As printed: `C_Y = (U ×_X X^Y) ∖ U^Y` is a `D(M)`-stable closed subscheme of `U`, with graded ideal
`J_Y` (`AlgMag.NotePt.exists_idealY`), `U ∖ Ω = ⋃_{Y ∈ 𝒴} C_Y`, and `J = ∏ J_Y`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.NotePt

open AlgMag.StronglyFPR AlgMag.StronglyFPRNote AlgMag.StronglyFPRNote.SubgroupIdeal

noncomputable section

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [Countable M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- `D(M)` acting on a point does not change its stabilizer: `D(M)` is commutative. -/
lemma stabY_smul {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (act : AAction (fppfO B S hS) M F) {V : BigFppfOver B S hS}
    (g : APt (fppfO B S hS) M (op V)) (y : F.obj (op V)) : stabY act (act.smul g y) = stabY act y := by
  have key : ∀ {T : BigFppfOver B S hS} (t : T ⟶ V) (k : APt (fppfO B S hS) M (op T)),
      act.smul k (F.map t.op (act.smul g y)) = F.map t.op (act.smul g y) ↔
        act.smul k (F.map t.op y) = F.map t.op y := by
    intro T t k
    rw [act.map_smul, ← act.mul_smul, mul_comm, act.mul_smul]
    constructor
    · intro h
      exact smul_injective act _ h
    · intro h
      rw [h]
  ext m
  exact ⟨fun hm T t k h => hm t k ((key t k).2 h), fun hm T t k h => hm t k ((key t k).1 h)⟩

/-- The prime of `Γ(W)` at a point of an affine `W`. -/
abbrev primeAt {W : Scheme.{u}} [IsAffine W] (x : W) : Ideal Γ(W, ⊤) :=
  (show PrimeSpectrum Γ(W, ⊤) from W.isoSpec.hom x).asIdeal

lemma mem_basicOpen_iff {W : Scheme.{u}} [IsAffine W] (b : Γ(W, ⊤)) (x : W) :
    x ∈ W.basicOpen b ↔ b ∉ primeAt x := by
  rw [← Scheme.toSpecΓ_preimage_basicOpen]
  rfl

lemma le_primeAt_of_kills {W P : Scheme.{u}} [IsAffine W] (s : P ⟶ W) (c : Ideal Γ(W, ⊤))
    (hs : ∀ r ∈ c, s.appTop.hom r = 0) (y : P) : c ≤ primeAt (s y) := by
  intro r hr
  by_contra hn
  have h1 : s y ∈ W.basicOpen r := (mem_basicOpen_iff _ _).2 hn
  have h2 : y ∈ s ⁻¹ᵁ W.basicOpen r := h1
  rw [Scheme.preimage_basicOpen_top, hs r hr, Scheme.basicOpen_zero] at h2
  exact h2

lemma primeAt_closedι {W : Scheme.{u}} [IsAffine W] (c : Ideal Γ(W, ⊤)) (p : Spec (.of (Γ(W, ⊤) ⧸ c))) :
    (show PrimeSpectrum Γ(W, ⊤) from W.isoSpec.hom (Chart.closedι W c p)) =
      PrimeSpectrum.comap (Ideal.Quotient.mk c) (show PrimeSpectrum (Γ(W, ⊤) ⧸ c) from p) := by
  change W.isoSpec.hom (W.isoSpec.inv _) = _
  rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
  rfl

lemma primeAt_closedι' {W : Scheme.{u}} [IsAffine W] (c : Ideal Γ(W, ⊤)) (p : Spec (.of (Γ(W, ⊤) ⧸ c))) :
    primeAt (Chart.closedι W c p) = (show PrimeSpectrum (Γ(W, ⊤) ⧸ c) from p).asIdeal.comap (Ideal.Quotient.mk c) :=
  congrArg PrimeSpectrum.asIdeal (primeAt_closedι c p)

lemma mem_range_closedι {W : Scheme.{u}} [IsAffine W] (c : Ideal Γ(W, ⊤)) (x : W) (h : c ≤ primeAt x) :
    x ∈ Set.range (Chart.closedι W c) := by
  have hr : (show PrimeSpectrum Γ(W, ⊤) from W.isoSpec.hom x) ∈
      Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk c)) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    exact h
  obtain ⟨p, hp⟩ := hr
  refine ⟨p, ?_⟩
  apply (Scheme.homeoOfIso W.isoSpec).injective
  exact (primeAt_closedι c p).trans hp

/-- A function with idempotent image, nonvanishing everywhere on an affine scheme, is `1`. -/
lemma eq_one_of_idempotent {W : Scheme.{u}} [IsAffine W] (E : Γ(W, ⊤)) (hE : E * E = E)
    (h : ∀ x : W, E ∉ primeAt x) : E = 1 := by
  have hu : IsUnit E := by
    by_contra hn
    obtain ⟨m, hm, hEm⟩ := exists_max_ideal_of_mem_nonunits hn
    let q : PrimeSpectrum Γ(W, ⊤) := ⟨m, hm.isPrime⟩
    refine h (W.isoSpec.inv q) ?_
    have : W.isoSpec.hom (W.isoSpec.inv q) = q := by
      change (W.isoSpec.inv ≫ W.isoSpec.hom) q = q
      rw [Iso.inv_hom_id]
      rfl
    change E ∈ (show PrimeSpectrum Γ(W, ⊤) from W.isoSpec.hom (W.isoSpec.inv q)).asIdeal
    rw [this]
    exact hEm
  exact (IsUnit.mul_left_inj hu).1 (hE.trans (one_mul E).symm)

variable {U : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  {actU : AAction (fppfO B S hS) M (yoneda.obj U)} {actX : AAction (fppfO B S hS) M X}
  {f : yoneda.obj U ⟶ X}

/-- `J ⊆ A` is graded: `J` contains the homogeneous components of its elements, for the coaction `A → A[M]`. -/
def IsGradedIdeal (actU : AAction (fppfO B S hS) M (yoneda.obj U)) (J : Ideal Γ((SCH).obj U, ⊤)) : Prop :=
  ∀ a ∈ J, ∀ m, (rhoMap actU a).coeff m ∈ J

/-- A product of graded ideals is graded. -/
lemma IsGradedIdeal.mul {J₁ J₂ : Ideal Γ((SCH).obj U, ⊤)} (h₁ : IsGradedIdeal actU J₁) (h₂ : IsGradedIdeal actU J₂) :
    IsGradedIdeal actU (J₁ * J₂) := by
  classical
  intro a ha m
  rw [← smul_eq_mul] at ha
  refine Submodule.smul_induction_on (p := fun a => ∀ m, (rhoMap actU a).coeff m ∈ J₁ * J₂) ha ?_ ?_ m
  · intro x hx y hy m
    rw [smul_eq_mul]
    rw [map_mul, AddMonoidAlgebra.mul_def]
    simp only [Finsupp.sum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, AddMonoidAlgebra.coeff_single,
      Finsupp.single_apply]
    refine Ideal.sum_mem _ fun i _ => Ideal.sum_mem _ fun j _ => ?_
    split_ifs
    · exact Ideal.mul_mem_mul (h₁ x hx i) (h₂ y hy j)
    · exact Ideal.zero_mem _
  · intro x y hx hy m
    rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    exact Ideal.add_mem _ (hx m) (hy m)

lemma isGradedIdeal_top : IsGradedIdeal actU (⊤ : Ideal Γ((SCH).obj U, ⊤)) := fun _ _ _ => trivial

/-- A prime not containing a graded `J` misses a homogeneous element of `J`. -/
lemma exists_homogeneous_notMem {J : Ideal Γ((SCH).obj U, ⊤)} (hJ : IsGradedIdeal actU J)
    {p : Ideal Γ((SCH).obj U, ⊤)} (hp : ¬ J ≤ p) :
    ∃ (b : Γ((SCH).obj U, ⊤)) (m : M), b ∈ J ∧ rhoMap actU b = AddMonoidAlgebra.single m b ∧ b ∉ p := by
  obtain ⟨a, haJ, hap⟩ := Set.not_subset.1 hp
  by_contra hn
  push Not at hn
  apply hap
  rw [← rhoMap_aug (actU := actU) a, Finsupp.sum]
  exact Ideal.sum_mem _ fun m _ => hn _ m (hJ a haJ m) (rhoMap_coeff a m)

variable [AddGroup.FG M] (hsepU : Space.IsSeparatedOver B S hS (yoneda.obj U))
  (hsep : Space.IsSeparatedOver B S hS X) (hf : IsEquivariant actU actX f)
  (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f)

/-- A point of `D(M)` preserves `X^Y`. -/
lemma Fx.smul {L : Type u} [AddCommGroup L] (φ : M →+ L) {T : BigFppfOver B S hS} {y : X.obj (op T)}
    (hy : Fx (actX.comap φ) y) (g : APt (fppfO B S hS) M (op T)) : Fx (actX.comap φ) (actX.smul g y) := by
  refine ⟨fun {T'} s h => ?_⟩
  have h1 := hy.mem s h
  have e : X.map s (actX.smul g y) = actX.smul (APt.res s g) (X.map s y) := actX.map_smul s g y
  change actX.smul (h.comp (AddMonoidHom.toMultiplicative φ)) (X.map s (actX.smul g y)) = X.map s (actX.smul g y)
  rw [e, ← actX.mul_smul, mul_comm, actX.mul_smul]
  exact congrArg _ h1

include hf he in
/-- **Lemma 2.3, proof.** `C_Y = (U ×_X X^Y) ∖ U^Y` is a `D(M)`-stable closed subscheme of `U`, and its ideal `J_Y` is graded.
The set of points of `V(J_Y)` is `AlgMag.NotePt.badSet`. -/
theorem exists_idealY [IsSeparated (terminal.from ((BigFppfOver.toScheme B S hS).obj U))] (Y : AddSubgroup M) : ∃ J : Ideal Γ((SCH).obj U, ⊤),
    (∀ u : (SCH).obj U, J ≤ primeAt u ↔ u ∈ badSet actU actX f hsepU hsep Y) ∧ IsGradedIdeal actU J := by
  let x : X.obj (op U) := f.app (op U) (𝟙 U)
  have hnat : ∀ {T : BigFppfOver B S hS} (t : T ⟶ U), X.map t.op x = f.app (op T) t := fun {T} t => by
    have h := (NatTrans.naturality_apply f t.op (𝟙 U)).symm
    refine h.trans ?_
    congr 1
  obtain ⟨c, h1, h2⟩ := exists_fixLocus (quotientAction actX Y) hsep x
  let E := Chart.immObj U (Chart.closedι ((SCH).obj U) c)
  let e : E ⟶ U := Chart.immι U (Chart.closedι ((SCH).obj U) c)
  have hme : (SCH).map e = Chart.closedι ((SCH).obj U) c := rfl
  have hfix : Fx (quotientAction actX Y) (f.app (op E) e) := by
    rw [← hnat]
    exact h1 e fun r hr => ChartMain.closedι_appTop_of_mem c hr
  obtain ⟨Ω, hΩc, hΩ⟩ := exists_clopen hf he Y e hfix
  have hε : ∀ ε : (SCH).obj E, ε ∉ Ω ↔ (SCH).map e ε ∈ badSet actU actX f hsepU hsep Y := by
    intro ε
    obtain ⟨r, rfl⟩ := Space.exists_fieldValuedPoint_schemePoint_eq B S hS E ε
    have hfx : Yf actX hsep f ((SCH).map e (Space.schemePoint B S hS E r)) ≤ Y :=
      (fixedX_iff hsep e r Y).1 (fx_f_comp hfix r.value)
    constructor
    · intro hn
      refine ⟨hfx, fun hu => hn ?_⟩
      have h3 := (hΩ r.value).1 ((fixedU_iff hsepU e r Y).2 hu)
      exact h3 ⟨IsLocalRing.closedPoint r.carrier, value_apply r _⟩
    · rintro ⟨-, hu⟩ hm
      exact hu ((fixedU_iff hsepU e r Y).1 ((hΩ r.value).2 (range_value_subset r hm)))
  have hbadc : ∀ u ∈ badSet actU actX f hsepU hsep Y, c ≤ primeAt u := by
    intro u hb
    obtain ⟨r, rfl⟩ := Space.exists_fieldValuedPoint_schemePoint_eq B S hS U u
    have hid : (SCH).map (𝟙 U) (Space.schemePoint B S hS U r) = Space.schemePoint B S hS U r := by simp
    have hx0 : Fx (quotientAction actX Y) (f.app (op r.siteObject) (r.value ≫ 𝟙 U)) :=
      (fixedX_iff hsep (𝟙 U) r Y).2 (by rw [hid]; exact hb.1)
    rw [← hnat] at hx0
    have hk := h2 (T := r.siteObject) (r.value ≫ 𝟙 U) hx0
    rw [Category.comp_id] at hk
    exact le_primeAt_of_kills ((SCH).map r.value) c hk (IsLocalRing.closedPoint r.carrier)
  -- the idempotent
  let A := Γ((SCH).obj U, ⊤) ⧸ c
  let Ωs : Set (PrimeSpectrum A) := (Ω : Set ((SCH).obj E))ᶜ
  have hcl : IsClopen Ωs := ⟨Ω.isOpen.isClosed_compl, hΩc.isOpen_compl⟩
  obtain ⟨εb, hεb, hs⟩ := PrimeSpectrum.isClopen_iff.mp hcl
  obtain ⟨e₀, he₀⟩ := Ideal.Quotient.mk_surjective εb
  have hidem : e₀ * e₀ - e₀ ∈ c := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, he₀, hεb.eq, sub_self]
  let J : Ideal Γ((SCH).obj U, ⊤) := c ⊔ Ideal.span {1 - e₀}
  have hmemΩ : ∀ p : PrimeSpectrum A, εb ∉ p.asIdeal ↔ p ∈ Ωs := fun p => by
    rw [hs]; rfl
  have hJ : ∀ u : (SCH).obj U, J ≤ primeAt u ↔ u ∈ badSet actU actX f hsepU hsep Y := by
    intro u
    constructor
    · intro hle
      have hc : c ≤ primeAt u := le_sup_left.trans hle
      obtain ⟨p, rfl⟩ := mem_range_closedι c u hc
      have h1e : 1 - e₀ ∈ primeAt (Chart.closedι ((SCH).obj U) c p) :=
        hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
      have hp0 := primeAt_closedι' c p
      have h3 : e₀ ∉ primeAt (Chart.closedι ((SCH).obj U) c p) := fun h => by
        have h4 := Ideal.add_mem _ h1e h
        rw [sub_add_cancel] at h4
        exact (show PrimeSpectrum Γ((SCH).obj U, ⊤) from _).2.ne_top ((Ideal.eq_top_iff_one _).2 h4)
      have hq : (show PrimeSpectrum A from p) ∈ Ωs := (hmemΩ _).1 fun h4 => h3 (by
        rw [hp0, Ideal.mem_comap, he₀]
        exact h4)
      exact (hε p).1 hq
    · intro hb
      have hc := hbadc u hb
      obtain ⟨p, rfl⟩ := mem_range_closedι c u hc
      have hnΩ : p ∉ Ω := (hε p).2 hb
      have h3 : εb ∉ (show PrimeSpectrum A from p).asIdeal := (hmemΩ _).2 hnΩ
      have hp0 := primeAt_closedι' c p
      refine sup_le hc ((Ideal.span_singleton_le_iff_mem _).2 ?_)
      rw [hp0, Ideal.mem_comap]
      have h0 : εb * (1 - εb) = 0 := by rw [mul_sub, mul_one, hεb.eq, sub_self]
      have h5 := (show PrimeSpectrum A from p).2.mem_or_mem (x := εb) (y := 1 - εb) (by
        rw [h0]; exact Ideal.zero_mem _)
      rw [map_sub, map_one, he₀]
      exact h5.resolve_left h3
  refine ⟨J, hJ, ?_⟩
  -- gradedness
  intro a haJ m
  let C := Chart.immObj U (Chart.closedι ((SCH).obj U) J)
  let q : C ⟶ U := Chart.immι U (Chart.closedι ((SCH).obj U) J)
  haveI : IsAffine ((SCH).obj C) := inferInstanceAs (IsAffine (Spec _))
  have hqJ : ∀ r ∈ J, ((SCH).map q).appTop.hom r = 0 := fun r hr => ChartMain.closedι_appTop_of_mem J hr
  let T := specObj M C
  let h : APt (fppfO B S hS) M (op T) := specPt M C
  let t : T ⟶ U := specPr M C ≫ q
  let t' : T ⟶ U := actU.smul h t
  have htJ : ∀ τ : (SCH).obj T, (SCH).map t τ ∈ badSet actU actX f hsepU hsep Y := by
    intro τ
    refine (hJ _).1 ?_
    rw [Functor.map_comp]
    exact le_primeAt_of_kills ((SCH).map q) J hqJ _
  have hbad' : ∀ τ : (SCH).obj T, (SCH).map t' τ ∈ badSet actU actX f hsepU hsep Y := by
    intro τ
    obtain ⟨r, rfl⟩ := Space.exists_fieldValuedPoint_schemePoint_eq B S hS T τ
    have hb := htJ (Space.schemePoint B S hS T r)
    let g : APt (fppfO B S hS) M (op r.siteObject) := APt.res r.value.op h
    have e1 : (show (yoneda.obj U).obj (op r.siteObject) from r.value ≫ t') =
        actU.smul g (show (yoneda.obj U).obj (op r.siteObject) from r.value ≫ t) :=
      actU.map_smul r.value.op h t
    have e2 : Yu actU hsepU ((SCH).map t' (Space.schemePoint B S hS T r)) =
        Yu actU hsepU ((SCH).map t (Space.schemePoint B S hS T r)) := by
      rw [Yu_eq, Yu_eq, e1, stabY_smul]
    have e3 : Yf actX hsep f ((SCH).map t' (Space.schemePoint B S hS T r)) =
        Yf actX hsep f ((SCH).map t (Space.schemePoint B S hS T r)) := by
      rw [Yf_eq, Yf_eq]
      change stabY actX (f.app (op r.siteObject) (show (yoneda.obj U).obj (op r.siteObject) from r.value ≫ t')) = _
      rw [e1, hf, stabY_smul]
    refine ⟨?_, ?_⟩
    · rw [e3]; exact hb.1
    · rw [e2]; exact hb.2
  have hfixT : Fx (quotientAction actX Y) (f.app (op T) t') := by
    have h0 : Fx (quotientAction actX Y) (f.app (op C) q) := by
      rw [← hnat]
      exact h1 q fun r hr => hqJ r (Ideal.mem_sup_left hr)
    have h3 : f.app (op T) t' = actX.smul h (f.app (op T) t) := hf h t
    rw [h3]
    exact Fx.smul _ (fx_f_comp h0 (specPr M C)) h
  have hc' : ∀ r ∈ c, ((SCH).map t').appTop.hom r = 0 := h2 t' (by rw [hnat]; exact hfixT)
  have he1 : ((SCH).map t').appTop.hom e₀ = 1 := by
    refine eq_one_of_idempotent (W := (SCH).obj T) _ ?_ fun τ hτ => ?_
    · have := hc' _ hidem
      rw [map_sub, map_mul, sub_eq_zero] at this
      exact this
    · have h5 := (hJ _).2 (hbad' τ)
      have h6 : 1 - e₀ ∈ primeAt ((SCH).map t' τ) := h5 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
      have h7 : τ ∉ ((SCH).obj T).basicOpen (((SCH).map t').appTop.hom e₀) := (mem_basicOpen_iff _ _).not_left.2 hτ
      rw [← Scheme.preimage_basicOpen_top] at h7
      have h8 : e₀ ∈ primeAt ((SCH).map t' τ) := by
        by_contra hn
        exact h7 ((mem_basicOpen_iff _ _).2 hn)
      have h4 := Ideal.add_mem _ h6 h8
      rw [sub_add_cancel] at h4
      exact (show PrimeSpectrum Γ((SCH).obj U, ⊤) from _).2.ne_top ((Ideal.eq_top_iff_one _).2 h4)
  have hker : J ≤ RingHom.ker ((SCH).map t').appTop.hom := by
    refine sup_le (fun r hr => hc' r hr) ((Ideal.span_singleton_le_iff_mem _).2 ?_)
    change ((SCH).map t').appTop.hom (1 - e₀) = 0
    rw [map_sub, map_one, he1, sub_self]
  have h10 : ((SCH).map t').appTop.hom a = 0 := hker haJ
  have h11 := appTop_smul (actU := actU) t h a
  have h12 : ((SCH).map (actU.smul h t : T ⟶ U)).appTop.hom a = 0 := h10
  have h15 := specRing_univ (L := M) (T := C) q (rhoMap actU a)
  have h16 := h15.symm.trans (h11.symm.trans h12)
  have h13 : baseMap ((SCH).map q).appTop.hom M (rhoMap actU a) = 0 :=
    inv_injective_Γ (M := M) (U := C) (h16.trans (map_zero _).symm)
  have h14 := baseMap_coeff ((SCH).map q).appTop.hom (rhoMap actU a) m
  rw [h13] at h14
  exact Chart.closedι_appTop_eq_zero J _ h14.symm

include hf in
/-- `U ∖ Ω = ⋃_{Y ∈ 𝒴} C_Y`. -/
lemma compl_omega_iff (𝒴 : Set (AddSubgroup M)) (h𝒴 : Set.range (stabPt actX hsep) ⊆ 𝒴) (u : (SCH).obj U) :
    Yu actU hsepU u ≠ Yf actX hsep f u ↔ ∃ Y ∈ 𝒴, u ∈ badSet actU actX f hsepU hsep Y := by
  constructor
  · intro hne
    refine ⟨_, h𝒴 ⟨_, rfl⟩, le_rfl, fun hle => hne (le_antisymm hle (Yf_le_Yu hsepU hsep hf u))⟩
  · rintro ⟨Y, -, h1, h2⟩ he
    exact h2 (he ▸ h1)

include hf in
/-- The open `D(a)`, for `a` homogeneous, as an equivariant morphism to `X`. -/
lemma basicOpen_equivariant {a : Γ((SCH).obj U, ⊤)} (hst : IsStableOpen actU (((SCH).obj U).basicOpen a)) :
    IsEquivariant (openAct hst) actX (yoneda.map (openJ (((SCH).obj U).basicOpen a)) ≫ f) := by
  intro T k t
  change f.app T (((openAct hst).smul k t : unop T ⟶ openObj _) ≫ openJ _) = actX.smul k (f.app T (t ≫ openJ _))
  rw [openAct_spec]
  exact hf k (t ≫ openJ _)

/-- `Y` is unchanged by passing to a stable open. -/
lemma stabY_open {D : ((SCH).obj U).Opens} (hst : IsStableOpen actU D) {V : BigFppfOver B S hS}
    (y : V ⟶ openObj D) :
    stabY (openAct hst) (show (yoneda.obj (openObj D)).obj (op V) from y) =
      stabY actU (show (yoneda.obj U).obj (op V) from y ≫ openJ D) := by
  have hm : Mono (openJ D) := mono_openJ
  have key : ∀ {T : BigFppfOver B S hS} (t : T ⟶ V) (k : APt (fppfO B S hS) M (op T)),
      (openAct hst).smul k (t ≫ y) = t ≫ y ↔ actU.smul k (t ≫ y ≫ openJ D) = t ≫ y ≫ openJ D := by
    intro T t k
    constructor
    · intro h
      have := openAct_spec hst k (t ≫ y)
      rw [h, Category.assoc] at this
      exact this.symm
    · intro h
      refine (cancel_mono (openJ D)).1 ?_
      rw [openAct_spec, Category.assoc]
      exact h
  ext m
  exact ⟨fun hm' T t k h => hm' t k ((key t k).2 h), fun hm' T t k h => hm' t k ((key t k).1 h)⟩

include he in
/-- **Lemma 2.3.** `S` affine of finite type over `ℤ`, `X` separated of finite type, `f : U = Spec A → X` equivariant étale,
`Ω = {u | G_u = G_{f(u)}}`. Then `Ω = ⋃ D(a)`, the union over the homogeneous elements `a` of a graded ideal `J ⊆ A`.
Each such `D(a)` is an affine `D(M)`-stable open subscheme, and `D(a) → X` is strongly-FPR. -/
theorem lem23 [IsAffine S] (hSft : LocallyOfFiniteType (terminal.from S)) (hX : IsAlgebraicSpace B S hS X)
    (hft : Space.IsFiniteType B S hS (terminal.from X)) :
    ∃ J : Ideal Γ((SCH).obj U, ⊤), IsGradedIdeal actU J ∧
      (∀ u : (SCH).obj U, Yu actU hsepU u = Yf actX hsep f u ↔
        ∃ (a : Γ((SCH).obj U, ⊤)) (m : M), a ∈ J ∧ rhoMap actU a = AddMonoidAlgebra.single m a ∧
          u ∈ ((SCH).obj U).basicOpen a) ∧
      ∀ (a : Γ((SCH).obj U, ⊤)) (m : M), a ∈ J → rhoMap actU a = AddMonoidAlgebra.single m a →
        IsAffine ((SCH).obj (openObj (((SCH).obj U).basicOpen a))) ∧
        ∃ hst : IsStableOpen actU (((SCH).obj U).basicOpen a), IsStronglyFPR (basicOpen_equivariant hf hst) := by
  classical
  haveI : IsSeparated (terminal.from ((SCH).obj U)) := Scheme.IsSeparated.isSeparated_terminal_from
  obtain hfin := lem22_points hSft hX hsep hft actX
  choose Jf hJf hJg using exists_idealY (actU := actU) (actX := actX) (f := f) hsepU hsep hf he
  let s := hfin.toFinset
  let J : Ideal Γ((SCH).obj U, ⊤) := ∏ Y ∈ s, Jf Y
  have hgr : IsGradedIdeal actU J :=
    Finset.prod_induction _ (IsGradedIdeal actU) (fun _ _ h₁ h₂ => h₁.mul h₂) (by rw [Ideal.one_eq_top]; exact isGradedIdeal_top)
      (fun Y _ => hJg Y)
  have hprime : ∀ u : (SCH).obj U, (primeAt u).IsPrime := fun u =>
    (show PrimeSpectrum Γ((SCH).obj U, ⊤) from ((SCH).obj U).isoSpec.hom u).2
  have hne : ∀ u : (SCH).obj U, Yu actU hsepU u ≠ Yf actX hsep f u ↔ J ≤ primeAt u := by
    intro u
    rw [compl_omega_iff hsepU hsep hf (Set.range (stabPt actX hsep)) subset_rfl]
    haveI := hprime u
    rw [Ideal.IsPrime.prod_le inferInstance]
    constructor
    · rintro ⟨Y, hY, hu⟩
      exact ⟨Y, hfin.mem_toFinset.2 hY, (hJf Y u).2 hu⟩
    · rintro ⟨Y, hY, hu⟩
      exact ⟨Y, hfin.mem_toFinset.1 hY, (hJf Y u).1 hu⟩
  have hΩ : ∀ u : (SCH).obj U, Yu actU hsepU u = Yf actX hsep f u ↔
      ∃ (a : Γ((SCH).obj U, ⊤)) (m : M), a ∈ J ∧ rhoMap actU a = AddMonoidAlgebra.single m a ∧
        u ∈ ((SCH).obj U).basicOpen a := by
    intro u
    constructor
    · intro h
      have hnle : ¬ J ≤ primeAt u := fun hle => (hne u).2 hle h
      obtain ⟨b, m, hb, hbm, hbp⟩ := exists_homogeneous_notMem hgr hnle
      exact ⟨b, m, hb, hbm, (mem_basicOpen_iff _ _).2 hbp⟩
    · rintro ⟨a, m, ha, -, hu⟩
      by_contra hn
      exact (mem_basicOpen_iff _ _).1 hu ((hne u).1 hn ha)
  refine ⟨J, hgr, hΩ, fun a m ha hm => ?_⟩
  let D := ((SCH).obj U).basicOpen a
  have hst : IsStableOpen actU D := isStableOpen_basicOpen hm
  have hA : IsAffine ((SCH).obj (openObj D)) := (isAffineOpen_top _).basicOpen a
  refine ⟨hA, hst, fun Z => ?_⟩
  let U' := openObj D
  let j : U' ⟶ U := openJ D
  haveI : IsSeparated (terminal.from ((SCH).obj U')) := Scheme.IsSeparated.isSeparated_terminal_from
  have hsepU' : Space.IsSeparatedOver B S hS (yoneda.obj U') :=
    Space.isSeparatedOver_yoneda_obj B S hS U' inferInstance
  have heq : IsEquivariant (openAct hst) actX (yoneda.map j ≫ f) := fun {T} k t => basicOpen_equivariant hf hst k t
  have he' : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) (yoneda.map j ≫ f) := by
    have hmap := Space.isMultiplicative_presheaf_etale B S hS
    refine MorphismProperty.comp_mem _ _ _ ?_ he
    exact (Space.presheaf_yoneda_map_iff B S hS inferInstance j).2 inferInstance
  refine (isZFPR_iff_forall_at heq he' Z).2 fun u' => (isZFPRAt_iff hsepU' hsep heq he' Z u').2 ?_
  obtain ⟨r, rfl⟩ := Space.exists_fieldValuedPoint_schemePoint_eq B S hS U' u'
  have hid : (SCH).map (𝟙 U') (Space.schemePoint B S hS U' r) = Space.schemePoint B S hS U' r := by simp
  have e1 := Yf_eq (actX := actX) (f := yoneda.map j ≫ f) hsep (𝟙 U') r
  have e2 := Yu_eq (actU := openAct hst) hsepU' (𝟙 U') r
  rw [hid] at e1 e2
  have e3 := Yf_eq (actX := actX) (f := f) hsep j r
  have e4 := Yu_eq (actU := actU) hsepU j r
  have e5 : (show (yoneda.obj U').obj (op r.siteObject) from r.value ≫ 𝟙 U') = r.value := Category.comp_id _
  have hv : (SCH).map j (Space.schemePoint B S hS U' r) ∈ D := by
    have hr : (SCH).map j (Space.schemePoint B S hS U' r) ∈ Set.range ((SCH).map j) := ⟨_, rfl⟩
    rw [show Set.range ((SCH).map j) = D from range_openJ] at hr
    exact hr
  have hom := (hΩ _).2 ⟨a, m, ha, hm, hv⟩
  rw [e1, e2, e5, stabY_open hst]
  intro hY
  rw [← e4, hom, e3]
  refine le_trans (le_of_eq ?_) hY
  congr 1

end

end AlgMag.NotePt

#print axioms AlgMag.NotePt.exists_idealY
#print axioms AlgMag.NotePt.lem23
