/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec3SchemeQuotient
import AlgMag.Prop337General

/-!
# Proposition 3.32 (ii) for schemes without finite generation of `M`

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026). The proof of `AlgMag.prop332_scheme` uses that
`M` is finitely generated at two places only: `UniqueSums` of the torsion-free quotient of the grading group,
and the site membership of `𝔸(M)_T`. The first is a statement on finite sets, hence holds for every torsion-free
abelian group (`uniqueSums_of_torsionFree`). The second holds for `M` countable, the site cutoff of
`AlgMag.specObj`. The rest of the proof is that of `AlgMag.Sec3SchemeQuotient`, restated here because
the section variables there carry `AddMonoid.FG M`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgMag.SQ

/-- A torsion-free abelian group has unique sums, with no finite generation: the property concerns two finite
sets, which lie in a finitely generated subgroup. -/
theorem uniqueSums_of_torsionFree (G : Type*) [AddCommGroup G] [IsAddTorsionFree G] : UniqueSums G := by
  classical
  refine ⟨fun {A B} hA hB => ?_⟩
  let H : AddSubgroup G := AddSubgroup.closure ((A ∪ B : Finset G) : Set G)
  have hfg : AddGroup.FG H := (AddGroup.fg_iff_addSubgroup_fg H).2 ⟨A ∪ B, rfl⟩
  have hmfg : AddMonoid.FG H := AddGroup.fg_iff_addMonoid_fg.mp hfg
  have hAH : ∀ a ∈ A, a ∈ H := fun a ha =>
    AddSubgroup.subset_closure (by simp [ha])
  have hBH : ∀ b ∈ B, b ∈ H := fun b hb =>
    AddSubgroup.subset_closure (by simp [hb])
  let A' : Finset H := A.subtype (· ∈ H)
  let B' : Finset H := B.subtype (· ∈ H)
  have hA' : A'.Nonempty := by
    obtain ⟨a, ha⟩ := hA
    exact ⟨⟨a, hAH a ha⟩, by simpa [A'] using ha⟩
  have hB' : B'.Nonempty := by
    obtain ⟨b, hb⟩ := hB
    exact ⟨⟨b, hBH b hb⟩, by simpa [B'] using hb⟩
  obtain ⟨a, ha, b, hb, hu⟩ := UniqueSums.uniqueAdd_of_nonempty hA' hB'
  refine ⟨a, by simpa [A'] using ha, b, by simpa [B'] using hb, ?_⟩
  intro x y hx hy e
  have := hu (a := ⟨x, hAH x hx⟩) (b := ⟨y, hBH y hy⟩) (by simpa [A'] using hx) (by simpa [B'] using hy)
    (Subtype.ext e)
  exact ⟨congrArg Subtype.val this.1, congrArg Subtype.val this.2⟩

section TwoStageGen

variable {X : Scheme.{u}} {R P P₀ Γ : Type u} [CommRing R] [AddCommMonoid P] [AddCommMonoid P₀]
  [AddCommGroup Γ]


/-- **The descent**: `F : Spec R[P] → X` invariant under `D(Γ)` factors through `Spec R[ker δ]`. First
through the invariants of the torsion-free quotient of `Γ` (the Reynolds argument), then through
those of the torsion part (`R[P'] → R[ker δ]` is integral, and fibres are orbits). -/
theorem exists_desc_gen (δ : P →+ Γ) {j : P₀ →+ P} (hj : Function.Injective j)
    (hk : ∀ p, δ p = 0 ↔ p ∈ Set.range j) {F : Spec (.of (AddMonoidAlgebra R P)) ⟶ X}
    (hF : IsInvariantF (monCoact δ) F) :
    ∃ f : Spec (.of (AddMonoidAlgebra R P₀)) ⟶ X, sp (monι j R) ≫ f = F := by
  classical
  let T := AddCommGroup.torsion Γ
  let π : Γ →+ Γ ⧸ T := QuotientAddGroup.mk' T
  let δ' : P →+ Γ ⧸ T := π.comp δ
  let P' : AddSubmonoid P := AddMonoidHom.mker δ'
  have : UniqueSums (Γ ⧸ T) := uniqueSums_of_torsionFree _
  have hιA : (monCoact (R := R) δ').IsInv (monι P'.subtype R) :=
    monCoact_isInv Subtype.val_injective fun p =>
      ⟨fun h => ⟨⟨p, h⟩, rfl⟩, by rintro ⟨q, rfl⟩; exact q.2⟩
  have hF' : IsInvariantF (monCoact (R := R) δ') F := by
    have e := hF.test (AddMonoidAlgebra.mapDomainRingHom (AddMonoidAlgebra R P) π)
    have e1 : (AddMonoidAlgebra.mapDomainRingHom (AddMonoidAlgebra R P) π).comp (monCoact δ).σ =
        (monCoact (R := R) δ').σ := by
      refine RingHom.ext fun y => ?_
      induction y using AddMonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [map_add, ha, hb]
      | single m c =>
        change AddMonoidAlgebra.mapDomainRingHom _ π (monσ δ _) = monσ δ' _
        rw [monσ_single, monσ_single]
        simp [δ']
    have e2 : (AddMonoidAlgebra.mapDomainRingHom (AddMonoidAlgebra R P) π).comp
        (cC (AddMonoidAlgebra R P) Γ) = cC _ _ := by
      refine RingHom.ext fun a => ?_
      simp [cC]
    rw [e1, e2] at e
    exact e
  obtain ⟨f', hf'⟩ := exists_desc_of_torsionFree hιA hF'
  let δ₁ : P' →+ Γ := δ.comp P'.subtype
  let j₁ : P₀ →+ P' := AddMonoidHom.codRestrict j P' (fun k => by
    have : δ (j k) = 0 := (hk _).2 ⟨k, rfl⟩
    change π (δ (j k)) = 0
    rw [this, map_zero])
  have hιB : (monCoact (R := R) δ₁).IsInv (monι j₁ R) :=
    monCoact_isInv (fun a b e => hj (congrArg Subtype.val e)) fun p => by
      constructor
      · intro h
        obtain ⟨k, hk'⟩ := (hk _).1 h
        exact ⟨k, Subtype.ext hk'⟩
      · rintro ⟨k, rfl⟩
        exact (hk _).2 ⟨k, rfl⟩
  have ht : (monCoact (R := R) δ₁).IsTors := by
    intro d a ha h0
    obtain ⟨p, rfl⟩ := monCoact_deg ha h0
    have hp : π (δ₁ p) = 0 := p.2
    have htor : δ₁ p ∈ T := (QuotientAddGroup.eq_zero_iff _).1 hp
    obtain ⟨n, hn, hd⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 htor
    exact ⟨n, hn, hd⟩
  have hF₁ : IsInvariantF (monCoact (R := R) δ₁) f' := by
    let ιΓ := AddMonoidAlgebra.mapRingHom Γ (monι P'.subtype R)
    have hs : IsSplit ιΓ hιA.isSplit.rΓ := hιA.isSplit.mapRing
    refine desc_unique hs ?_
    have e1 : ιΓ.comp (monCoact (R := R) δ₁).σ = (monCoact (R := R) δ).σ.comp (monι P'.subtype R) := by
      refine RingHom.ext fun y => ?_
      induction y using AddMonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [map_add, ha, hb]
      | single m c =>
        change ιΓ (monσ δ₁ _) = monσ δ _
        rw [monι_single, monσ_single, monσ_single]
        simp [ιΓ, monι_single]
        rfl
    have e2 : ιΓ.comp (cC _ Γ) = (cC _ Γ).comp (monι P'.subtype R) := by
      refine RingHom.ext fun y => ?_
      simp [ιΓ, cC]
    change sp ιΓ ≫ sp _ ≫ f' = sp ιΓ ≫ sp _ ≫ f'
    rw [← Category.assoc, ← Category.assoc, ← sp_comp, ← sp_comp, e1, e2, sp_comp, sp_comp,
      Category.assoc, Category.assoc, hf']
    exact hF
  obtain ⟨f, hf⟩ := exists_desc_of_tors hιB ht hF₁
  refine ⟨f, ?_⟩
  have e : monι j R = (monι P'.subtype R).comp (monι j₁ R) := by
    rw [monι, monι, monι, ← AddMonoidAlgebra.mapDomainRingHom_comp]
    rfl
  rw [e, sp_comp, Category.assoc, hf, hf']

end TwoStageGen

end AlgMag.SQ

namespace AlgMag.GenM

open AlgMag.SQ
open AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

/-- `𝔸(M)` over a site object, `M` countable. -/
lemma contains_M {M : Type u} [AddCommMonoid M] [Countable M] {R' : Type u} [CommRing R']
    (h : B.Contains (Spec (.of R'))) : B.Contains (Spec (.of (AddMonoidAlgebra R' M))) :=
  P337.contains_alg (lt_of_le_of_lt Cardinal.mk_le_aleph0 B.aleph0_lt_cutoff) h

section Bi

variable {M : Type u} [AddCommGroup M] [Countable M]
variable {U : BigFppfOver B S hS} {aX : AAction (fppfO B S hS) M (yoneda.obj U)}
  {N L : AddSubmonoid M} {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]

/-- The morphism `F : 𝔸(N)_T × 𝔸(L)_T → X` of the statement. -/
noncomputable def biX (φ : AttractorPt (biAct aX) (N.prod L) T) : specObj ↥(N.prod L) T ⟶ U :=
  φ.app (specPr _ T) (specPt _ T)

lemma app_eq_biX (φ : AttractorPt (biAct aX) (N.prod L) T) {T' : BigFppfOver B S hS} (t : T' ⟶ T)
    (c : APt (fppfO B S hS) ↥(N.prod L) (op T')) : φ.app t c = specLift t c ≫ biX φ :=
  φ.app_eq_of_universal (specUniversal (N.prod L) T) t c

/-- `F` is invariant under `D(N^gp + L^gp)`, through `D(M)`. -/
theorem isInvariant_biX (φ : AttractorPt (biAct aX) (N.prod L) T) :
    IsInvariantF (monCoact (R := Γ((SCH).obj T, ⊤)) (dlt N L)) ((SCH).map (biX φ)) := by
  let A := gRing ↥(N.prod L) T
  let ρ : RT T →+* AddMonoidAlgebra A M := (cC A M).comp (algebraMap _ _)
  have hC : B.Contains (Spec (.of (AddMonoidAlgebra A M))) := contains_M (contains_spec _ T)
  let t := spToT T ρ hC
  let σ : A →+* AddMonoidAlgebra A M := (monCoact (R := Γ((SCH).obj T, ⊤)) (dlt N L)).σ
  have hσ : σ.comp (algebraMap _ _) = ρ := by
    refine RingHom.ext fun r => ?_
    change monσ _ (AddMonoidAlgebra.single 0 r) = _
    rw [monσ_single, map_zero]
    rfl
  let a₁ := spPt (T := T) (ρ := ρ) (hC := hC) (σ.toMonoidHom.comp (AddMonoidAlgebra.of _ _))
  let a₂ := spPt (T := T) (ρ := ρ) (hC := hC) ((cC A M).toMonoidHom.comp (AddMonoidAlgebra.of _ _))
  let E : Multiplicative M →* AddMonoidAlgebra A M := AddMonoidAlgebra.of _ _
  let e := spPt (T := T) (ρ := ρ) (hC := hC) E
  let h : APt (fppfO B S hS) (M × M) (op (spObj T ρ hC)) :=
    e.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst M M - AddMonoidHom.snd M M))
  have ha : a₁ = APt.toMagnet (N.prod L) h * a₂ := by
    refine MonoidHom.ext fun p => ?_
    change spSec T ρ hC (σ (AddMonoidAlgebra.single (Multiplicative.toAdd p) 1)) =
      spSec T ρ hC _ * spSec T ρ hC _
    rw [← map_mul]
    congr 1
    change monσ _ _ = _
    rw [monσ_single]
    simp [E, cC, AddMonoidAlgebra.single_mul_single]
    rfl
  have hdiag : h.comp (AddMonoidHom.toMultiplicative (diagHom M)) = 1 := by
    refine MonoidHom.ext fun m => ?_
    have h0 : ((AddMonoidHom.fst M M - AddMonoidHom.snd M M) (diagHom M (Multiplicative.toAdd m))) = 0 :=
      sub_self _
    change e (Multiplicative.ofAdd ((AddMonoidHom.fst M M - AddMonoidHom.snd M M)
      (diagHom M (Multiplicative.toAdd m)))) = 1
    rw [h0]
    exact map_one e
  have heq : φ.app t a₁ = φ.app t a₂ := by
    rw [ha]
    refine (φ.equivariant t h a₂).trans ?_
    change aX.smul (h.comp (AddMonoidHom.toMultiplicative (diagHom M))) _ = _
    rw [hdiag]
    exact aX.one_smul _
  rw [app_eq_biX, app_eq_biX] at heq
  have h1 := congrArg (fun k => (SCH).map k) heq
  simp only [Functor.map_comp] at h1
  rw [map_specLift_spPt σ hσ, map_specLift_spPt (cC A M) rfl] at h1
  exact h1

end Bi

section Bi

variable {M : Type u} [AddCommGroup M] [Countable M]
variable {U : BigFppfOver B S hS} {aX : AAction (fppfO B S hS) M (yoneda.obj U)}
  {N L : AddSubmonoid M} {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]

/-- **The descent**, on the universal point: `F = f ∘ m` for a morphism `f : 𝔸(N ∩ L)_T → X` over `S`. -/
theorem exists_x₀ (φ : AttractorPt (biAct aX) (N.prod L) T) :
    ∃ x₀ : specObj ↥(N ⊓ L) T ⟶ U, specAlong T (jD N L) ≫ x₀ = biX φ := by
  let R := Γ((SCH).obj T, ⊤)
  have hι := monCoact_isInv (R := R) (δ := dlt N L) jD_inj dlt_eq_zero
  obtain ⟨f, hf⟩ := exists_desc_gen (R := R) (dlt N L) jD_inj dlt_eq_zero (isInvariant_biX φ)
  refine ⟨overHom f ?_, toScheme_map_injective ?_⟩
  · refine desc_unique hι.isSplit ?_
    have e1 : sp (monι (jD N L) R) ≫ specPrS ↥(N ⊓ L) T = specPrS ↥(N.prod L) T := by
      rw [sp_specPrS, monι_comp_algebraMap]
      rfl
    have e2 : (SCH).map (biX φ) ≫ U.hom.hom = specPrS ↥(N.prod L) T ≫ T.hom.hom := site_w (biX φ)
    change sp (monι (jD N L) R) ≫ f ≫ U.hom.hom = sp (monι (jD N L) R) ≫ specPrS ↥(N ⊓ L) T ≫ T.hom.hom
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ U.hom.hom) hf).trans (e2.trans
      ((congrArg (· ≫ T.hom.hom) e1).symm.trans (Category.assoc _ _ _))))
  · rw [Functor.map_comp]
    exact hf

lemma lift_x₀ {φ : AttractorPt (biAct aX) (N.prod L) T} {x₀ : specObj ↥(N ⊓ L) T ⟶ U}
    (hx : specAlong T (jD N L) ≫ x₀ = biX φ) {T' : BigFppfOver B S hS} (t : T' ⟶ T)
    (c : APt (fppfO B S hS) ↥(N.prod L) (op T')) :
    specLift t (APt.along (jD N L) c) ≫ x₀ = φ.app t c := by
  rw [specLift_along, Category.assoc, hx, app_eq_biX]

/-- Equivariance of `f`: it suffices to check it on the universal point of `𝔸(N ∩ L) × 𝔸(M)`, and
there after pulling back to `𝔸(N) × 𝔸(L) × 𝔸(M)`, by step (4). -/
theorem equivariant_x₀ {φ : AttractorPt (biAct aX) (N.prod L) T} {x₀ : specObj ↥(N ⊓ L) T ⟶ U}
    (hx : specAlong T (jD N L) ≫ x₀ = biX φ) {T' : BigFppfOver B S hS} (t : T' ⟶ T)
    (h : APt (fppfO B S hS) M (op T')) (a : APt (fppfO B S hS) ↥(N ⊓ L) (op T')) :
    specLift t (APt.toMagnet (N ⊓ L) h * a) ≫ x₀ = aX.smul h (specLift t a ≫ x₀) := by
  let R := Γ((SCH).obj T, ⊤)
  let P₂ := ↥(N ⊓ L) × M
  let Pm := ↥(N.prod L) × M
  let Q := specObj P₂ T
  let tQ : Q ⟶ T := specPr P₂ T
  let aU : APt (fppfO B S hS) ↥(N ⊓ L) (op Q) := APt.along (AddMonoidHom.inl _ _) (specPt P₂ T)
  let hU : APt (fppfO B S hS) M (op Q) := APt.along (AddMonoidHom.inr _ _) (specPt P₂ T)
  let jh : P₂ →+ Pm := (jD N L).prodMap (AddMonoidHom.id M)
  let δh : Pm →+ M := (dlt N L).comp (AddMonoidHom.fst _ _)
  have hι : (monCoact (R := R) δh).IsInv (monι jh R) := monCoact_isInv
    (Function.Injective.prodMap jD_inj Function.injective_id) (fun p => by
      constructor
      · intro hp
        obtain ⟨k, hk⟩ := (dlt_eq_zero p.1).1 hp
        exact ⟨(k, p.2), Prod.ext hk rfl⟩
      · rintro ⟨k, rfl⟩
        exact (dlt_eq_zero _).2 ⟨k.1, rfl⟩)
  let π : specObj Pm T ⟶ Q := specAlong T jh
  let tm : specObj Pm T ⟶ T := specPr Pm T
  let ch : APt (fppfO B S hS) ↥(N.prod L) (op (specObj Pm T)) :=
    APt.along (AddMonoidHom.inl _ _) (specPt Pm T)
  let eh : APt (fppfO B S hS) M (op (specObj Pm T)) :=
    APt.along (AddMonoidHom.inr _ _) (specPt Pm T)
  have hπt : π ≫ tQ = tm := specAlong_pr T jh
  have hra : APt.res π.op aU = APt.along (jD N L) ch := by
    have e := res_specAlong T jh
    refine MonoidHom.ext fun p => ?_
    exact congrArg (fun z => z (AddMonoidHom.toMultiplicative (AddMonoidHom.inl _ _) p)) e
  have hrh : APt.res π.op hU = eh := by
    have e := res_specAlong T jh
    refine MonoidHom.ext fun p => ?_
    exact congrArg (fun z => z (AddMonoidHom.toMultiplicative (AddMonoidHom.inr _ _) p)) e
  have hmag : APt.along (jD N L) (APt.toMagnet (N.prod L)
      (eh.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst M M))) * ch) =
      APt.toMagnet (N ⊓ L) eh * APt.along (jD N L) ch := MonoidHom.ext fun p => rfl
  have hφsm : φ.app tm (APt.toMagnet (N.prod L)
      (eh.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst M M))) * ch) =
      aX.smul eh (φ.app tm ch) := by
    refine (φ.equivariant tm _ ch).trans ?_
    change aX.smul ((eh.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst M M))).comp
      (AddMonoidHom.toMultiplicative (diagHom M))) _ = _
    rfl
  -- the universal equation
  have huniv : specLift tQ (APt.toMagnet (N ⊓ L) hU * aU) ≫ x₀ = aX.smul hU (specLift tQ aU ≫ x₀) := by
    apply toScheme_map_injective
    refine desc_unique hι.isSplit ?_
    have e0 : ∀ w : Q ⟶ U, sp (monι jh R) ≫ (SCH).map w = (SCH).map (π ≫ w) := fun w => by
      rw [Functor.map_comp]
      rfl
    rw [e0, e0]
    congr 1
    have e1 : π ≫ specLift tQ (APt.toMagnet (N ⊓ L) hU * aU) =
        specLift tm (APt.along (jD N L) (APt.toMagnet (N.prod L)
          (eh.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst M M))) * ch)) := by
      rw [← specLift_comp, hπt, hmag, APt.res_mul, hra, ← APt.toMagnet_res, hrh]
    have e2 : π ≫ specLift tQ aU = specLift tm (APt.along (jD N L) ch) := by
      rw [← specLift_comp, hπt, hra]
    have e3 : (yoneda.obj U).map π.op (aX.smul hU (specLift tQ aU ≫ x₀)) =
        aX.smul (APt.res π.op hU) ((yoneda.obj U).map π.op (specLift tQ aU ≫ x₀)) :=
      aX.map_smul π.op hU _
    change _ = (yoneda.obj U).map π.op (aX.smul hU (specLift tQ aU ≫ x₀))
    rw [e3, hrh]
    change _ = aX.smul eh (π ≫ specLift tQ aU ≫ x₀)
    have eL : π ≫ specLift tQ (APt.toMagnet (N ⊓ L) hU * aU) ≫ x₀ = aX.smul eh (φ.app tm ch) := by
      rw [← Category.assoc, e1, lift_x₀ hx, hφsm]
    have eR : π ≫ specLift tQ aU ≫ x₀ = φ.app tm ch := by
      rw [← Category.assoc, e2, lift_x₀ hx]
    rw [eL, eR]
  -- pull back along the classifying morphism
  let pt : APt (fppfO B S hS) P₂ (op T') :=
    APt.along (AddMonoidHom.fst _ _) a * APt.along (AddMonoidHom.snd _ _) h
  let ξ : T' ⟶ Q := specLift t pt
  have hξt : ξ ≫ tQ = t := specLift_pr t pt
  have hξa : APt.res ξ.op aU = a := by
    refine MonoidHom.ext fun p => ?_
    have e := res_specLift t pt
    refine (congrArg (fun z => z (AddMonoidHom.toMultiplicative (AddMonoidHom.inl _ _) p)) e).trans ?_
    change a p * h (Multiplicative.ofAdd 0) = a p
    have : h (Multiplicative.ofAdd (0 : M)) = 1 := map_one h
    rw [this, mul_one]
  have hξh : APt.res ξ.op hU = h := by
    refine MonoidHom.ext fun p => ?_
    have e := res_specLift t pt
    refine (congrArg (fun z => z (AddMonoidHom.toMultiplicative (AddMonoidHom.inr _ _) p)) e).trans ?_
    change a (Multiplicative.ofAdd 0) * h p = h p
    have : a (Multiplicative.ofAdd (0 : ↥(N ⊓ L))) = 1 := map_one a
    rw [this, one_mul]
  have e1 := congrArg (fun w => ξ ≫ w) huniv
  have e3 : (yoneda.obj U).map ξ.op (aX.smul hU (specLift tQ aU ≫ x₀)) =
      aX.smul (APt.res ξ.op hU) ((yoneda.obj U).map ξ.op (specLift tQ aU ≫ x₀)) :=
    aX.map_smul ξ.op hU _
  have e4 : ξ ≫ specLift tQ (APt.toMagnet (N ⊓ L) hU * aU) = specLift t (APt.toMagnet (N ⊓ L) h * a) := by
    rw [← specLift_comp, hξt, APt.res_mul, hξa, ← APt.toMagnet_res, hξh]
  have e5 : ξ ≫ specLift tQ aU = specLift t a := by
    rw [← specLift_comp, hξt, hξa]
  simp only at e1
  rw [← Category.assoc, e4] at e1
  refine e1.trans ?_
  refine Eq.trans e3 ?_
  rw [hξh]
  change aX.smul h (ξ ≫ specLift tQ aU ≫ x₀) = _
  rw [← Category.assoc, e5]

/-- The point of `X^{N ∩ L}` given by `f`. -/
noncomputable def chiOf {φ : AttractorPt (biAct aX) (N.prod L) T} {x₀ : specObj ↥(N ⊓ L) T ⟶ U}
    (hx : specAlong T (jD N L) ≫ x₀ = biX φ) : AttractorPt aX (N ⊓ L) T where
  app t a := specLift t a ≫ x₀
  naturality s t a := by
    rw [specLift_comp, Category.assoc]
    rfl
  equivariant t h a := equivariant_x₀ hx t h a

/-- **Proposition 3.32 (ii)** for `T` affine: existence and uniqueness of `f` with `F = f ∘ m`.
Case of schemes. -/
theorem existsUnique_toBi_affine (φ : AttractorPt (biAct aX) (N.prod L) T) :
    ∃! χ : AttractorPt aX (N ⊓ L) T, χ.toBi (hKinf N L) = φ := by
  obtain ⟨x₀, hx⟩ := exists_x₀ φ
  refine ⟨chiOf hx, ?_, fun χ hχ => ?_⟩
  · refine AttractorPt.ext ?_
    funext T' t c
    exact lift_x₀ hx t c
  · refine AttractorPt.ext ?_
    funext T' t a
    have e1 : ∀ {T' : BigFppfOver B S hS} (t : T' ⟶ T) (a : APt (fppfO B S hS) ↥(N ⊓ L) (op T')),
        χ.app t a = specLift t a ≫ χ.app (specPr _ T) (specPt _ T) :=
      fun t a => χ.app_eq_of_universal (specUniversal (N ⊓ L) T) t a
    have e2 : χ.app (specPr _ T) (specPt _ T) = x₀ := by
      apply toScheme_map_injective
      refine desc_unique (monCoact_isInv (R := Γ((SCH).obj T, ⊤)) (δ := dlt N L) jD_inj
        dlt_eq_zero).isSplit ?_
      have e0 : ∀ w : specObj ↥(N ⊓ L) T ⟶ U, sp (monι (jD N L) Γ((SCH).obj T, ⊤)) ≫ (SCH).map w =
          (SCH).map (specAlong T (jD N L) ≫ w) := fun w => by
        rw [Functor.map_comp]
        rfl
      rw [e0, e0, hx]
      congr 1
      have e3 : specAlong T (jD N L) ≫ χ.app (specPr _ T) (specPt _ T) = biX φ := by
        have e4 := e1 (specPr _ T) (APt.along (jD N L) (specPt ↥(N.prod L) T))
        rw [specLift_along] at e4
        have e5 : specLift (specPr ↥(N.prod L) T) (specPt ↥(N.prod L) T) = 𝟙 _ :=
          (specLift_uniq _ _ _ (Category.id_comp _) (by simp)).symm
        rw [e5, Category.id_comp] at e4
        rw [← e4, ← hχ]
        rfl
      exact e3
    exact (e1 t a).trans (congrArg (specLift t a ≫ ·) e2)

end Bi

section Glue

variable {M : Type u} [AddCommGroup M] [Countable M]
variable {U : BigFppfOver B S hS} {aX : AAction (fppfO B S hS) M (yoneda.obj U)}
  {N L : AddSubmonoid M}

lemma baseChange_comp' {M' : Type*} [AddCommMonoid M'] {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {act : AAction (fppfO B S hS) M' F} {K : AddSubmonoid M'} {T Y W : BigFppfOver B S hS}
    (a : W ⟶ Y) (b : Y ⟶ T) (φ : AttractorPt act K T) :
    AttractorPt.baseChange (a ≫ b) φ = AttractorPt.baseChange a (AttractorPt.baseChange b φ) := by
  refine AttractorPt.ext ?_
  funext T' t c
  change φ.app (t ≫ a ≫ b) c = φ.app ((t ≫ a) ≫ b) c
  rw [Category.assoc]

lemma toBi_baseChange {T Y : BigFppfOver B S hS} (s : Y ⟶ T) (χ : AttractorPt aX (N ⊓ L) T) :
    (AttractorPt.baseChange s χ).toBi (hKinf N L) =
      AttractorPt.baseChange s (χ.toBi (hKinf N L)) := rfl

/-- **Step (4), uniqueness**, for an arbitrary `T`. Case of schemes. -/
theorem toBi_injective (T : BigFppfOver B S hS) :
    Function.Injective fun χ : AttractorPt aX (N ⊓ L) T => χ.toBi (hKinf N L) := by
  intro χ χ' h
  obtain ⟨I, V, π, hV, hcov⟩ := exists_affine_cover T
  have hsh := isSheaf_attractor aX (N ⊓ L) _ (BigFppfOver.isSheaf_of_type_yoneda_obj U)
  refine (hsh _ hcov).isSeparatedFor.ext ?_
  rintro Y g ⟨W, a, b, ⟨i⟩, rfl⟩
  have := hV i
  have e : AttractorPt.baseChange (π i) χ = AttractorPt.baseChange (π i) χ' :=
    (existsUnique_toBi_affine (AttractorPt.baseChange (π i) (χ.toBi (hKinf N L)))).unique
      (toBi_baseChange _ _) ((toBi_baseChange _ _).trans (congrArg _ h.symm))
  change AttractorPt.baseChange (a ≫ π i) χ = AttractorPt.baseChange (a ≫ π i) χ'
  rw [baseChange_comp', baseChange_comp', e]

/-- **Proposition 3.32 (ii)**, the descent for an arbitrary `T`, glued from affine `T`.
Case of schemes. -/
theorem exists_toBi {T : BigFppfOver B S hS} (φ : AttractorPt (biAct aX) (N.prod L) T) :
    ∃ χ : AttractorPt aX (N ⊓ L) T, χ.toBi (hKinf N L) = φ := by
  obtain ⟨I, V, π, hV, hcov⟩ := exists_affine_cover T
  have hsh := isSheaf_attractor aX (N ⊓ L) _ (BigFppfOver.isSheaf_of_type_yoneda_obj U)
  have hshB := isSheaf_attractor (biAct aX) (N.prod L) _ (BigFppfOver.isSheaf_of_type_yoneda_obj U)
  have key : ∀ {Y : BigFppfOver B S hS} (g : Y ⟶ T), (Sieve.ofArrows V π) g →
      ∃ χ : AttractorPt aX (N ⊓ L) Y, χ.toBi (hKinf N L) = AttractorPt.baseChange g φ := by
    rintro Y g ⟨W, a, b, ⟨i⟩, rfl⟩
    have := hV i
    obtain ⟨χ, hχ, -⟩ := existsUnique_toBi_affine (AttractorPt.baseChange (π i) φ)
    refine ⟨AttractorPt.baseChange a χ, ?_⟩
    rw [toBi_baseChange, hχ, baseChange_comp']
  choose x hx using @key
  have hcomp : Presieve.FamilyOfElements.Compatible (P := attractor aX (N ⊓ L))
      (R := (Sieve.ofArrows V π).arrows) (fun _ g hg => x g hg) := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ comm
    apply toBi_injective Z
    change (AttractorPt.baseChange g₁ (x f₁ h₁)).toBi _ = (AttractorPt.baseChange g₂ (x f₂ h₂)).toBi _
    rw [toBi_baseChange, toBi_baseChange, hx, hx, ← baseChange_comp', ← baseChange_comp', comm]
  have hamal := (hsh _ hcov).isAmalgamation hcomp
  let t : AttractorPt aX (N ⊓ L) T := (hsh _ hcov).amalgamate _ hcomp
  refine ⟨t, (hshB _ hcov).isSeparatedFor.ext ?_⟩
  intro Y g hg
  have e : AttractorPt.baseChange g t = x g hg := hamal g hg
  exact (toBi_baseChange g t).symm.trans
    ((congrArg (fun χ => AttractorPt.toBi (hKinf N L) χ) e).trans (hx g hg))

/-- **Proposition 3.32 (ii)**: `(X^N)^L = X^{N ∩ L}`, `F = f ∘ m` and `f ↦ F` is bijective. `X` is a
scheme over an arbitrary `S`, with no atlas; `M` is a countable abelian group.
The printed step *free action, fpqc quotient* is replaced by the descent `AlgMag.SQ.exists_desc`
along the Reynolds operator. -/
theorem prop332_scheme (T : BigFppfOver B S hS) :
    Function.Bijective (iterOfInf : AttractorPt aX (N ⊓ L) T → IterPt aX N L T) := by
  constructor
  · intro χ χ' h
    exact toBi_injective T ((iterEquivBi T).symm.injective h)
  · intro Ψ
    obtain ⟨χ, hχ⟩ := exists_toBi Ψ.toBi
    refine ⟨χ, ?_⟩
    apply (iterEquivBi T).injective
    rw [iterOfInf, Equiv.apply_symm_apply]
    exact hχ

end Glue

end AlgMag.GenM

#print axioms AlgMag.SQ.uniqueSums_of_torsionFree
#print axioms AlgMag.SQ.exists_desc_gen
#print axioms AlgMag.GenM.prop332_scheme
