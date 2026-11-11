/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartEffectiveMain
import AlgMag.ChartBridge

/-!
# The complete pair of a stable closed subscheme

* `AlgMag.ChartGraded.IsCompletePair.of_surjective`: a graded surjection from a complete pair, onto
  on each degree, gives a complete pair (Lemma 3.3).
* `AlgMag.ChartMain.isCompletePair_closedAct`: `(Γ(V(J)), m)` is a complete pair for the grading of
  the restricted action `AlgMag.ChartMain.closedAct`, as used in Lemma 4.4.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry DirectSum

universe u

namespace AlgMag.ChartGraded

variable {M C C' : Type*} [AddCommGroup M] [DecidableEq M] [CommRing C] [CommRing C']
  {𝒞 : M → AddSubgroup C} [GradedRing 𝒞] {𝒞' : M → AddSubgroup C'} [GradedRing 𝒞']

/-- **Lemma 3.3**, for a graded surjection. -/
theorem IsCompletePair.of_surjective {m : Ideal C} (hP : IsCompletePair 𝒞 m) (ρ : C →+* C')
    (hρ : Function.Surjective ρ) (hg : ∀ d, ∀ a ∈ 𝒞 d, ρ a ∈ 𝒞' d) :
    IsCompletePair 𝒞' (m.map ρ) := by
  classical
  have hd : ∀ (r : C) (e : M), (decompose 𝒞' (ρ r) e : C') = ρ (decompose 𝒞 r e : C) :=
    fun r e => ChartMain.decompose_map 𝒞 𝒞' ρ hg r e
  have hmem : ∀ {d : M} {a : C'}, a ∈ 𝒞' d → ∀ w : C, ρ w = a →
      ρ (decompose 𝒞 w d : C) = a := by
    intro d a ha w hw
    rw [← hd, hw, decompose_of_mem_same 𝒞' ha]
  have hpow : ∀ n : ℕ, (m.map ρ) ^ n = (m ^ n).map ρ := fun n => (Ideal.map_pow ρ m n).symm
  have hhomm : ∀ n : ℕ, (m ^ n).IsHomogeneous 𝒞 := fun n =>
    pow_homogeneous hP.hom n
  have hlift : ∀ (n : ℕ) {d : M} {a : C'}, a ∈ 𝒞' d → a ∈ (m.map ρ) ^ n →
      ∃ w ∈ 𝒞 d, w ∈ m ^ n ∧ ρ w = a := by
    intro n d a ha han
    rw [hpow, Ideal.mem_map_iff_of_surjective ρ hρ] at han
    obtain ⟨w, hw, rfl⟩ := han
    exact ⟨_, SetLike.coe_mem _, hhomm n d hw, hmem ha w rfl⟩
  have := hP.noeth
  refine ⟨isNoetherianRing_of_surjective C C' ρ hρ, ?_, ?_, ?_⟩
  · intro i x hx
    rw [Ideal.mem_map_iff_of_surjective ρ hρ] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    rw [hd]
    exact Ideal.mem_map_of_mem _ (hP.hom i hw)
  · intro d y hy hc
    have hstep : ∀ n, ∃ w ∈ 𝒞 d, w ∈ m ^ n ∧ ρ w = y (n + 1) - y n := fun n =>
      hlift n (sub_mem (hy _) (hy _)) (hc n)
    choose w hw₁ hw₂ hw₃ using hstep
    obtain ⟨c₀, hc₀, hc₀'⟩ : ∃ c ∈ 𝒞 d, ρ c = y 0 := by
      obtain ⟨c, h⟩ := hρ (y 0)
      exact ⟨_, SetLike.coe_mem _, hmem (hy 0) c h⟩
    let z : ℕ → C := fun n => Nat.rec c₀ (fun k zk => zk + w k) n
    have hz : ∀ n, z n ∈ 𝒞 d ∧ ρ (z n) = y n := by
      intro n
      induction n with
      | zero => exact ⟨hc₀, hc₀'⟩
      | succ k ih =>
        refine ⟨add_mem ih.1 (hw₁ k), ?_⟩
        change ρ (z k + w k) = _
        rw [map_add, ih.2, hw₃]
        ring
    obtain ⟨c, hc, hcn⟩ := hP.exists_lim d z (fun n => (hz n).1) (fun n => by
      change z n + w n - z n ∈ _
      simpa using hw₂ n)
    refine ⟨ρ c, hg d c hc, fun n => ?_⟩
    rw [← (hz n).2, ← map_sub, hpow]
    exact Ideal.mem_map_of_mem _ (hcn n)
  · intro d a ha han
    obtain ⟨c, hc, hca⟩ : ∃ c ∈ 𝒞 d, ρ c = a := by
      obtain ⟨c, h⟩ := hρ a
      exact ⟨_, SetLike.coe_mem _, hmem ha c h⟩
    have hb : (RingHom.ker ρ).IsHomogeneous 𝒞 := ChartMain.ker_isHomogeneous 𝒞 𝒞' ρ hg
    letI := quotGradedRing hb
    have hQ := lemma_3_3_quot hP hb
    have h0 := hQ.sep d _ (mk_mem_quotGrade hc) (fun n => by
      obtain ⟨w, -, hw, hwa⟩ := hlift n ha (han n)
      rw [← Ideal.map_pow]
      have e : Ideal.Quotient.mk (RingHom.ker ρ) c = Ideal.Quotient.mk (RingHom.ker ρ) w :=
        Ideal.Quotient.eq.2 (by rw [RingHom.mem_ker, map_sub, hca, hwa, sub_self])
      rw [e]
      exact Ideal.mem_map_of_mem _ hw)
    rw [← hca]
    exact (Ideal.Quotient.eq_zero_iff_mem.1 h0)

end AlgMag.ChartGraded

namespace AlgMag.ChartMain

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [AddMonoid.FG M] {T : BigFppfOver B S hS}
  [hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)]

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- `V(J)` is affine. -/
instance instAffineClosed (J : Ideal Γ((SCH).obj T, ⊤)) :
    IsAffine ((SCH).obj (Chart.immObj T (Chart.closedι ((SCH).obj T) J))) :=
  inferInstanceAs (IsAffine (Spec _))

/-- **Lemma 4.4, the complete pair.** `(Γ(V(J)), m)` is a complete pair for the restricted action. -/
theorem isCompletePair_closedAct [DecidableEq M] (actT : AAction (fppfO B S hS) M (yoneda.obj T))
    {J : Ideal Γ((SCH).obj T, ⊤)} (hJ : ∀ x ∈ J, ∀ d, (coact actT x).coeff d ∈ J)
    {m : Ideal Γ((SCH).obj T, ⊤)}
    (hP : letI := gradedRingOfAction actT; ChartGraded.IsCompletePair (homog actT) m) :
    letI := gradedRingOfAction (closedAct actT hJ)
    ChartGraded.IsCompletePair (homog (closedAct actT hJ))
      (m.map ((SCH).map (Chart.immι T (Chart.closedι ((SCH).obj T) J))).appTop.hom) := by
  letI := gradedRingOfAction actT
  letI := gradedRingOfAction (closedAct actT hJ)
  have heq : IsEquivariant (closedAct actT hJ) actT
      (yoneda.map (Chart.immι T (Chart.closedι ((SCH).obj T) J))) :=
    fun {_} h t => closedAct_spec actT hJ h t
  refine hP.of_surjective _ ?_ (fun d a ha => map_mem_homog _ _ heq ha)
  exact (IsClosedImmersion.isAffine_surjective_of_isAffine
    (Chart.closedι ((SCH).obj T) J)).2

end AlgMag.ChartMain

#print axioms AlgMag.ChartMain.isCompletePair_closedAct
