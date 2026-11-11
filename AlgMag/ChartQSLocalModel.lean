/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartQSLocalLift

/-!
# The flat model `Y`: completion along `b` of a flat `C`-algebra `L`

For `LocalModelStep`, the part that does not depend on how `L` is made
(`ChartQSLocalEtale` builds `L`, an étale `C`-algebra with `1 + I` inverted). Given `L` flat over `C = Γ(T)`, noetherian,
with `I` in its Jacobson radical, with the points `ψ l` on `V(b^l)` lifted to the chart `V` on `V(bL)`:
`Y = Spec L^` (the `b`-completion), `θ : Y → X`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Space

universe u

namespace AlgMag.ChartMain.DeligneQS.ChartQSLocal

/-- The Jacobson radical lifts along a map onto modulo an ideal in the radical. -/
lemma jac_lift {A D : Type*} [CommRing A] [CommRing D] (π : A →+* D) (K : Ideal D)
    (hK : K ≤ Ideal.jacobson ⊥) (hs : ∀ r, ∃ c, r - π c ∈ K) {x : A} (hx : x ∈ Ideal.jacobson (⊥ : Ideal A)) :
    π x ∈ Ideal.jacobson (⊥ : Ideal D) := by
  rw [Ideal.mem_jacobson_bot] at hx ⊢
  intro r
  obtain ⟨c, hc⟩ := hs r
  have hu : IsUnit (π (x * c + 1)) := (hx c).map π
  obtain ⟨u, hu'⟩ := hu
  have hβ := Ideal.mem_jacobson_bot.1 (hK hc) (π x * ↑u⁻¹)
  have e : π x * r + 1 = ((r - π c) * (π x * ↑u⁻¹) + 1) * ↑u := by
    have h1 : (↑u⁻¹ : D) * ↑u = 1 := Units.inv_mul u
    have h2 : (u : D) = π x * π c + 1 := by rw [hu']; simp
    calc π x * r + 1 = (r - π c) * π x + (π x * π c + 1) := by ring
      _ = (r - π c) * π x * (↑u⁻¹ * ↑u) + ↑u := by rw [h1, h2]; ring
      _ = _ := by ring
  rw [e]
  exact hβ.mul u.isUnit

/-- The prime of the image of a point. -/
lemma prime_comap {A A' : Scheme.{u}} [IsAffine A] [IsAffine A'] (f : A ⟶ A') (u : A) :
    (A'.isoSpec.hom (f u)).asIdeal = (A.isoSpec.hom u).asIdeal.comap f.appTop.hom := by
  have e := Scheme.isoSpec_hom_naturality f
  have h := congrArg (fun z : A ⟶ Spec Γ(A', ⊤) => z u) e
  simp only [Scheme.Hom.comp_apply] at h
  exact (congrArg PrimeSpectrum.asIdeal h).symm

/-- A point of `A'` whose prime is a contraction is in the image. -/
lemma mem_range_of_prime {A A' : Scheme.{u}} [IsAffine A] [IsAffine A'] (f : A ⟶ A') (y : A')
    (Q : Ideal Γ(A, ⊤)) [hQ : Q.IsPrime] (h : Q.comap f.appTop.hom = (A'.isoSpec.hom y).asIdeal) :
    y ∈ Set.range f := by
  let u : A := A.isoSpec.inv ⟨Q, hQ⟩
  have hu : A.isoSpec.hom u = ⟨Q, hQ⟩ := by
    change (A.isoSpec.inv ≫ A.isoSpec.hom) _ = _
    rw [Iso.inv_hom_id]
    rfl
  refine ⟨u, ?_⟩
  have h1 : A'.isoSpec.hom (f u) = A'.isoSpec.hom y := PrimeSpectrum.ext (by
    rw [prime_comap, hu]
    exact h)
  have inj : Function.Injective A'.isoSpec.hom := (Scheme.homeoOfIso A'.isoSpec).injective
  exact inj h1

/-- Flat: the image contains generizations. -/
lemma range_generize {A A' : Scheme.{u}} [IsAffine A] [IsAffine A'] (f : A ⟶ A') (hf : Flat f)
    (y : A') (m : Ideal Γ(A', ⊤)) [hm : m.IsPrime] (hle : (A'.isoSpec.hom y).asIdeal ≤ m)
    (Q : Ideal Γ(A, ⊤)) [hQ : Q.IsPrime] (hQm : Q.comap f.appTop.hom = m) : y ∈ Set.range f := by
  have hflat : f.appTop.hom.Flat := (HasRingHomProperty.iff_of_isAffine (P := @Flat)).mp hf
  have hgen := RingHom.Flat.generalizingMap_comap hflat
  let qq : PrimeSpectrum Γ(A, ⊤) := ⟨Q, hQ⟩
  have hs : (A'.isoSpec.hom y) ⤳ PrimeSpectrum.comap f.appTop.hom qq :=
    (PrimeSpectrum.le_iff_specializes _ _).1 (by
      change _ ≤ Q.comap f.appTop.hom
      rw [hQm]
      exact hle)
  obtain ⟨z, -, hz⟩ := hgen hs
  have := z.2
  exact mem_range_of_prime f y z.asIdeal (congrArg PrimeSpectrum.asIdeal hz)

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

variable {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)]

set_option maxHeartbeats 8000000 in
/-- **The flat model.** -/
theorem exists_model_of_ring [IsAffine S] {V : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] {φ : yoneda.obj V ⟶ X}
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
    (I b : Ideal Γ((SCH).obj T, ⊤))
    (ψ : ∀ l : ℕ, X.obj (op (Vc T (b ^ l))))
    (hψ : ∀ (n k : ℕ) (e : Vc T (b ^ n) ⟶ Vc T (b ^ k)), e ≫ ιc T (b ^ k) = ιc T (b ^ n) →
      X.map e.op (ψ k) = ψ n)
    (L : Type u) [CommRing L] [IsNoetherianRing L] (ρ : Γ((SCH).obj T, ⊤) →+* L)
    (hC : B.Contains (Spec (.of L)))
    (hflat : Flat ((SCH).map (spToT T ρ hC)))
    (hI : ∀ c ∈ I, ρ c ∈ Ideal.jacobson (⊥ : Ideal L))
    (hc₁ : ∀ (W : BigFppfOver B S hS) (u : W ⟶ spObj T ρ hC) (s : W ⟶ Vc T (b ^ (0 + 1))),
      s ≫ ιc T (b ^ (0 + 1)) = u ≫ spToT T ρ hC → ∃ c : W ⟶ V, φ.app (op W) c = X.map s.op (ψ (0 + 1)))
    (hcov : ∀ m : Ideal Γ((SCH).obj T, ⊤), m.IsMaximal → b ≤ m → I ≤ m →
      ∃ Q : Ideal L, Q.IsPrime ∧ b.map ρ ≤ Q ∧ Q.comap ρ = m)
    (hIJ : I ≤ Ideal.jacobson ⊥) :
    ∃ (Y : BigFppfOver B S hS) (p : Y ⟶ T) (θ : X.obj (op Y)),
      IsAffine ((SCH).obj Y) ∧ IsNoetherianRing Γ((SCH).obj Y, ⊤) ∧ Flat ((SCH).map p) ∧
      (∀ y : (SCH).obj T, (∀ g ∈ b, y ∉ ((SCH).obj T).basicOpen g) → y ∈ Set.range ((SCH).map p)) ∧
      I.map (sec p) ≤ Ideal.jacobson ⊥ ∧ b.map (sec p) ≤ Ideal.jacobson ⊥ ∧
      ∀ (l : ℕ) ⦃W : BigFppfOver B S hS⦄ (i : W ⟶ Y) (s : W ⟶ Vc T (b ^ l)),
        s ≫ ιc T (b ^ l) = i ≫ p → X.map i.op θ = X.map s.op (ψ l) := by
  let T' : BigFppfOver B S hS := spObj T ρ hC
  let π' : T' ⟶ T := spToT T ρ hC
  have hbij := spSec_bijective T ρ hC
  let κ : L ≃+* Γ((SCH).obj T', ⊤) := RingEquiv.ofBijective (spSec T ρ hC) hbij
  have hπ' : ∀ c, (sec π') c = κ (ρ c) := fun c => spToT_appTop T ρ hC c
  haveI : IsAffine ((SCH).obj T') := inferInstance
  haveI hNT' : IsNoetherianRing Γ((SCH).obj T', ⊤) := isNoetherianRing_of_ringEquiv L κ
  let a' : Ideal Γ((SCH).obj T', ⊤) := b.map (sec π')
  let Y : BigFppfOver B S hS := complObj T' a'
  let q : Y ⟶ T' := complMap T' a'
  let p : Y ⟶ T := q ≫ π'
  haveI hNY : IsNoetherianRing Γ((SCH).obj Y, ⊤) := inferInstance
  let J : Ideal Γ((SCH).obj Y, ⊤) := b.map (sec p)
  have hJ : J = a'.map (sec q) := by
    change b.map (sec (q ≫ π')) = (b.map (sec π')).map (sec q)
    rw [Ideal.map_map]
    congr 1
  haveI hJc : IsAdicComplete J Γ((SCH).obj Y, ⊤) := by
    rw [hJ]
    exact complComplete T' a'
  have hJjac : J ≤ Ideal.jacobson ⊥ := IsAdicComplete.le_jacobson_bot J
  -- the points `t l`
  have hs : ∀ l, ∃ s : Vc Y (J ^ (l + 1)) ⟶ Vc T (b ^ (l + 1)),
      s ≫ ιc T (b ^ (l + 1)) = ιc Y (J ^ (l + 1)) ≫ p := fun l =>
    exists_factor_closed _ _ fun z hz => by
      refine (sec_comp _ p z).trans ?_
      refine closedι_appTop_of_mem _ ?_
      have : (b ^ (l + 1)).map (sec p) = J ^ (l + 1) := Ideal.map_pow _ _ _
      exact this ▸ Ideal.mem_map_of_mem _ hz
  choose s hsc using hs
  have htr : ∀ n k : ℕ, n ≤ k → ∃ e : Vc T (b ^ n) ⟶ Vc T (b ^ k),
      e ≫ ιc T (b ^ k) = ιc T (b ^ n) := fun n k h =>
    exists_factor_closed _ _ fun z hz =>
      closedι_appTop_of_mem _ (Ideal.pow_le_pow_right h hz)
  have hιT : ∀ K : Ideal Γ((SCH).obj T, ⊤), Mono (ιc T K) := fun K =>
    (SCH).mono_of_mono_map (inferInstanceAs (Mono (Chart.closedι ((SCH).obj T) K)))
  let t : ∀ l : ℕ, X.obj (op (Vc Y (J ^ (l + 1)))) := fun l => X.map (s l).op (ψ (l + 1))
  have ht : ∀ l (k : Vc Y (J ^ (l + 1)) ⟶ Vc Y (J ^ (l + 1 + 1))),
      k ≫ ιc Y (J ^ (l + 1 + 1)) = ιc Y (J ^ (l + 1)) → X.map k.op (t (l + 1)) = t l := by
    intro l k hk
    obtain ⟨e, he'⟩ := htr (l + 1) (l + 1 + 1) (Nat.le_succ _)
    haveI := hιT (b ^ (l + 1 + 1))
    have hcomm : k ≫ s (l + 1) = s l ≫ e := (cancel_mono (ιc T (b ^ (l + 1 + 1)))).1 (by
      rw [Category.assoc, hsc, ← Category.assoc, hk, Category.assoc, he', hsc])
    change X.map k.op (X.map (s (l + 1)).op (ψ (l + 1 + 1))) = X.map (s l).op (ψ (l + 1))
    rw [← Functor.map_comp_apply, ← op_comp, hcomm, op_comp, Functor.map_comp_apply, hψ _ _ e he']
  obtain ⟨c₀, hc₀⟩ := hc₁ _ (ιc Y (J ^ (0 + 1)) ≫ q) (s 0) (by
    rw [hsc, Category.assoc])
  obtain ⟨c, hc⟩ := exists_map_chart he J t ht c₀ hc₀
  let θ : X.obj (op Y) := φ.app (op Y) c
  haveI hYa : IsAffine ((SCH).obj Y) := inferInstance
  refine ⟨Y, p, θ, hYa, hNY, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : Flat ((SCH).map q) := compl_flat T' a'
    change Flat ((SCH).map (q ≫ π'))
    rw [Functor.map_comp]
    haveI : Flat ((SCH).map π') := hflat
    infer_instance
  · -- the cover
    intro y hy
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (((SCH).obj T).isoSpec.hom y).asIdeal
      (((SCH).obj T).isoSpec.hom y).2.ne_top
    have hyb : b ≤ ((((SCH).obj T).isoSpec.hom y).asIdeal) := fun g hg => by
      by_contra hn
      exact hy g hg ((ChartQS.mem_basicOpen_iff y g).2 hn)
    have hIm : I ≤ m := hIJ.trans (sInf_le ⟨bot_le, hm⟩)
    obtain ⟨QL, hQL, hbQ, hQc⟩ := hcov m hm (hyb.trans hle) hIm
    let Q' : Ideal Γ((SCH).obj T', ⊤) := QL.comap κ.symm.toRingHom
    haveI hQ'p : Q'.IsPrime := Ideal.comap_isPrime _ _
    have hQ'c : ∀ c, (sec π') c ∈ Q' ↔ ρ c ∈ QL := fun c => by
      change κ.symm ((sec π') c) ∈ QL ↔ _
      rw [hπ', RingEquiv.symm_apply_apply]
    have ha'Q : a' ≤ Q' := Ideal.map_le_iff_le_comap.2 fun g hg => by
      exact (hQ'c g).2 (hbQ (Ideal.mem_map_of_mem _ hg))
    let x : (SCH).obj T' := ((SCH).obj T').isoSpec.inv ⟨Q', hQ'p⟩
    have hxp : ((SCH).obj T').isoSpec.hom x = ⟨Q', hQ'p⟩ := by
      change (((SCH).obj T').isoSpec.inv ≫ ((SCH).obj T').isoSpec.hom) _ = _
      rw [Iso.inv_hom_id]
      rfl
    obtain ⟨w, hw⟩ := compl_hcov T' a' x (fun g hg hx => by
      have := (ChartQS.mem_basicOpen_iff x g).1 hx
      rw [hxp] at this
      exact this (ha'Q hg))
    have hwp : (((SCH).obj Y).isoSpec.hom w).asIdeal.comap (sec q) = Q' := by
      rw [← prime_comap ((SCH).map q) w]
      change (((SCH).obj T').isoSpec.hom ((SCH).map (complMap T' a') w)).asIdeal = Q'
      rw [hw, hxp]
    haveI := (((SCH).obj Y).isoSpec.hom w).2
    haveI : m.IsPrime := hm.isPrime
    refine range_generize ((SCH).map p) ?_ y m hle (((SCH).obj Y).isoSpec.hom w).asIdeal ?_
    · have h1 : Flat ((SCH).map q) := compl_flat T' a'
      change Flat ((SCH).map (q ≫ π'))
      rw [Functor.map_comp]
      haveI : Flat ((SCH).map π') := hflat
      infer_instance
    · ext z
      have e1 : ((SCH).map p).appTop.hom z = (sec q) ((sec π') z) := sec_comp q π' z
      rw [Ideal.mem_comap, e1, ← Ideal.mem_comap, hwp, hQ'c, ← Ideal.mem_comap, hQc]
  · -- `I` in the radical
    refine Ideal.map_le_iff_le_comap.2 fun c hc' => ?_
    rw [Ideal.mem_comap]
    have hc2 : (sec π') c ∈ Ideal.jacobson (⊥ : Ideal Γ((SCH).obj T', ⊤)) := by
      rw [Ideal.mem_jacobson_bot]
      intro r
      have h1 := Ideal.mem_jacobson_bot.1 (hI c hc') (κ.symm r)
      have h2 := h1.map κ.toRingHom
      have e : κ.toRingHom (ρ c * κ.symm r + 1) = (sec π') c * r + 1 := by
        change κ (ρ c * κ.symm r + 1) = _
        rw [map_add, map_mul, RingEquiv.apply_symm_apply, map_one, hπ']
      exact e ▸ h2
    have hs' : ∀ r, ∃ c, r - (sec q) c ∈ J := fun r => by
      obtain ⟨c', hc'⟩ := compl_hsurj T' a' 1 r
      refine ⟨c', ?_⟩
      rw [pow_one] at hc'
      rw [hJ]
      exact hc'
    have := jac_lift (sec q) J hJjac hs' hc2
    exact (sec_comp q π' c).symm ▸ this
  · exact hJjac
  · -- restriction to the `ψ l`
    intro l W i s' hs'
    obtain ⟨e, he'⟩ := htr l (l + 1) (Nat.le_succ _)
    have hk : ∀ z ∈ J ^ (l + 1), ((SCH).map i).appTop.hom z = 0 := by
      have : J ^ (l + 1) = (b ^ (l + 1)).map (sec p) := (Ideal.map_pow _ _ _).symm
      rw [this]
      intro z hz
      refine Submodule.span_induction ?_ (by simp) (fun _ _ _ _ h₁ h₂ => by rw [map_add, h₁, h₂, add_zero])
        (fun r _ _ h => by rw [smul_eq_mul, map_mul, h, mul_zero]) hz
      rintro _ ⟨g, hg, rfl⟩
      have hgz := sec_comp i p g
      have hgs := sec_comp (s' ≫ e) (ιc T (b ^ (l + 1))) g
      rw [(ιc_ker _ g).2 hg, map_zero] at hgs
      rw [← hgz]
      rw [Category.assoc, he', hs'] at hgs
      exact hgs
    obtain ⟨g, hg⟩ := exists_factor_closed i (J ^ (l + 1)) hk
    haveI := hιT (b ^ (l + 1))
    have hcomm : g ≫ s l = s' ≫ e := (cancel_mono (ιc T (b ^ (l + 1)))).1 (by
      rw [Category.assoc, hsc, ← Category.assoc, hg, Category.assoc, he', hs'])
    have h1 : X.map (ιc Y (J ^ (l + 1))).op θ = t l := hc l
    change X.map i.op θ = _
    rw [← hg, op_comp, Functor.map_comp_apply, h1]
    change X.map g.op (X.map (s l).op (ψ (l + 1))) = _
    rw [← Functor.map_comp_apply, ← op_comp, hcomm, op_comp, Functor.map_comp_apply, hψ _ _ e he']

end AlgMag.ChartMain.DeligneQS.ChartQSLocal
