/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartQSIndOpen

/-!
# Lemma 4.3 of the chart-lemma proof: compatibility on `V`

`χ_k` on `V(a^k)` restricting to `x` is equivariant (`chi_univ`), so `J·C/a^k ⊃ a` (`le_idl_chi`).
On `θ : Y → X`, Nakayama gives `a Γ(Y) ⊂ J Γ(Y)` (`le_idl_theta`), and `τ` and `θ` have the same
formula (`tau_theta`).
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Space

universe u

namespace AlgMag.ChartMain.DeligneQS

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [AddMonoid.FG M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

variable {actX : AAction (fppfO B S hS) M X} {U₀ : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U₀)] {actU : AAction (fppfO B S hS) M (yoneda.obj U₀)}
  {fU : yoneda.obj U₀ ⟶ X} {V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  {φ : yoneda.obj V ⟶ X} (C : Ctx actX actU fU φ)
  [DecidableEq M] {T : BigFppfOver B S hS} [hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  {actT : AAction (fppfO B S hS) M (yoneda.obj T)}
  {m : Ideal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)}
  (hP : letI := gradedRingOfAction actT; ChartGraded.IsCompletePair (homog actT) m)
  {x : ∀ n, X.obj (op (Vc T (m ^ n)))} (hx : IsEquivSystem actT actX m x)

/-! ### Algebra -/

lemma ring_nak {R : Type*} [CommRing R] [IsNoetherianRing R] {N Ib : Ideal R} [IsAdicComplete N R]
    (h : N ≤ Ib ⊔ N ^ 2) : N ≤ Ib := by
  have hj := IsAdicComplete.le_jacobson_bot N
  have h' : N ≤ Ib ⊔ N • N := by rwa [pow_two] at h
  have := Submodule.sup_eq_sup_smul_of_le_smul_of_le_jacobson (IsNoetherian.noetherian N) hj h'
  rw [Submodule.bot_smul, sup_bot_eq] at this
  rw [← this]
  exact le_sup_right

include hP in
/-- The closure of a stable ideal: `∩ (Q + mⁿ) = Q`. -/
lemma closed_of_coeff (Q : Ideal Γ((SCH).obj T, ⊤)) (hQ : ∀ x ∈ Q, ∀ d, (coact actT x).coeff d ∈ Q) (z)
    (hz : ∀ n, z ∈ Q ⊔ m ^ n) : z ∈ Q := by
  letI := gradedRingOfAction (closedAct actT hQ)
  have hC := isCompletePair_closedAct actT hQ hP
  have hb := Chart.iInf_pow_eq_bot (homog (closedAct actT hQ)) _ hC.hom hC.sep
  have : (sec (ιc T Q)) z ∈ ⨅ n : ℕ, (m.map (sec (ιc T Q))) ^ n := by
    refine Ideal.mem_iInf.2 fun n => ?_
    obtain ⟨u, hu, v, hv, e⟩ := Submodule.mem_sup.1 (hz n)
    rw [← e, map_add, (ιc_ker _ u).2 hu, zero_add, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hv
  rw [hb] at this
  exact (ιc_ker _ z).1 this

/-! ### `J ⊃ a` on `χ` and on `θ` -/

variable {a : Ideal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)}
  (hax : ∀ n, C.idl (x n) = a.map (sec (ιc T (m ^ n))))
  (hak : ∀ k, ∀ y ∈ a ^ k, ∀ d, (coact actT y).coeff d ∈ a ^ k)

/-- The ring step of `le_idl_chi`. -/
lemma ring_chi {R D₁ D₂ E : Type*} [CommRing R] [CommRing D₁] [CommRing D₂] [CommRing E]
    (ι₁ : R →+* D₁) (ι₂ : R →+* D₂) (e₁ : D₁ →+* E) (e₂ : D₂ →+* E) (ρ : R →+* E)
    (h₁ : ∀ z, e₁ (ι₁ z) = ρ z) (h₂ : ∀ z, e₂ (ι₂ z) = ρ z)
    (hs₁ : Function.Surjective ι₁) (he₁ : Function.Surjective e₁)
    (I₁ : Ideal D₁) (I₂ : Ideal D₂) (a J Mn : Ideal R) (hker : ∀ z, ρ z = 0 → z ∈ J ⊔ Mn)
    (hJ : J ≤ I₁.comap ι₁) (ha : ∀ g ∈ a, ι₂ g ∈ I₂) (hid : I₂.map e₂ = I₁.map e₁) (g) (hg : g ∈ a) :
    g ∈ I₁.comap ι₁ ⊔ Mn := by
  have h1 : ρ g ∈ I₁.map e₁ := by
    rw [← hid, ← h₂]
    exact Ideal.mem_map_of_mem _ (ha g hg)
  rw [Ideal.mem_map_iff_of_surjective _ he₁] at h1
  obtain ⟨w, hw, hwe⟩ := h1
  obtain ⟨c, rfl⟩ := hs₁ w
  have h2 : ρ (g - c) = 0 := by
    rw [map_sub, ← hwe, h₁, sub_self]
  obtain ⟨u, hu, v, hv, e⟩ := Submodule.mem_sup.1 (hker _ h2)
  refine Submodule.mem_sup.2 ⟨c + u, add_mem hw (hJ hu), v, hv, ?_⟩
  linear_combination e

set_option maxHeartbeats 4000000 in
include hP hx hax hak in
/-- **`a ⊂ J` on `V(a^k)`.** `χ` is equivariant by hypothesis (review gap 4): it comes from the induction. -/
theorem le_idl_chi (k : ℕ) (χ : X.obj (op (Vc T (a ^ k))))
    (hχe : EquivAlong actT actX (ιc T (a ^ k)) χ)
    (hχ : ∀ (n : ℕ) ⦃W : BigFppfOver B S hS⦄ (g₁ : W ⟶ Vc T (a ^ k)) (g₂ : W ⟶ Vc T (m ^ n)),
      g₁ ≫ ιc T (a ^ k) = g₂ ≫ ιc T (m ^ n) → X.map g₁.op χ = X.map g₂.op (x n)) {g} (hg : g ∈ a) :
    (sec (ιc T (a ^ k))) g ∈ C.idl χ := by
  let Q : Ideal Γ((SCH).obj T, ⊤) := (C.idl χ).comap (sec (ιc T (a ^ k)))
  have hQ : ∀ c ∈ Q, ∀ d, (coact actT c).coeff d ∈ Q := fun c hc d =>
    comap_idl_coeff C actT (hak k) χ (fun t' ht' => hχe _ t' _ ht') hc d
  refine closed_of_coeff hP Q hQ g fun n => ?_
  let R := a ^ k ⊔ m ^ n
  obtain ⟨g₁, hg₁⟩ := exists_factor_closed (ιc T R) (a ^ k) (fun z hz =>
    closedι_appTop_of_mem _ (Ideal.mem_sup_left hz))
  obtain ⟨g₂, hg₂⟩ := exists_factor_closed (ιc T R) (m ^ n) (fun z hz =>
    closedι_appTop_of_mem _ (Ideal.mem_sup_right hz))
  have hpt := hχ n g₁ g₂ (hg₁.trans hg₂.symm)
  have hid : (C.idl (x n)).map (sec g₂) = (C.idl χ).map (sec g₁) := by
    rw [← C.idl_map, ← C.idl_map, hpt]
  refine ring_chi (sec (ιc T (a ^ k))) (sec (ιc T (m ^ n))) (sec g₁) (sec g₂) (sec (ιc T R))
    (fun z => by rw [← sec_comp, hg₁]) (fun z => by rw [← sec_comp, hg₂])
    (ιc_surj _) ?_ (C.idl χ) (C.idl (x n)) a (a ^ k) (m ^ n) (fun z hz => (ιc_ker _ z).1 hz)
    (fun z hz => by
      rw [Ideal.mem_comap, (ιc_ker _ z).2 hz]
      exact zero_mem _)
    (fun z hz => by
      rw [hax]
      exact Ideal.mem_map_of_mem _ hz) hid g hg
  intro w
  obtain ⟨c, rfl⟩ := ιc_surj R w
  exact ⟨_, by rw [← sec_comp, hg₁]⟩

variable {Y : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj Y)]
  [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤)] (p : Y ⟶ T)
  [hcomp : IsAdicComplete (a.map (sec p)) Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤)]
  {χ : ∀ k, X.obj (op (Vc T (a ^ k)))}
  (hχ : ∀ (k n : ℕ) ⦃W : BigFppfOver B S hS⦄ (g₁ : W ⟶ Vc T (a ^ k)) (g₂ : W ⟶ Vc T (m ^ n)),
    g₁ ≫ ιc T (a ^ k) = g₂ ≫ ιc T (m ^ n) → X.map g₁.op (χ k) = X.map g₂.op (x n))
  (hχe : ∀ k, EquivAlong actT actX (ιc T (a ^ k)) (χ k))
  {θ : X.obj (op Y)}
  (hθ : ∀ (k : ℕ) (W : BigFppfOver B S hS) (i : W ⟶ Y) (s : W ⟶ Vc T (a ^ k)),
    s ≫ ιc T (a ^ k) = i ≫ p → X.map i.op θ = X.map s.op (χ k))

/-- `s : V(a^k Γ(Y)) → V(a^k)`. -/
lemma exists_s (k : ℕ) : ∃ s : Vc Y ((a ^ k).map (sec p)) ⟶ Vc T (a ^ k),
    s ≫ ιc T (a ^ k) = ιc Y ((a ^ k).map (sec p)) ≫ p :=
  exists_factor_closed _ _ fun z hz => by
    rw [sec_comp]
    exact closedι_appTop_of_mem _ (Ideal.mem_map_of_mem _ hz)

set_option maxHeartbeats 4000000 in
include hP hx hax hak hχe hχ hθ in
/-- **Nakayama**: `a Γ(Y) ⊂ J Γ(Y)`. -/
theorem le_idl_theta : a.map (sec p) ≤ C.idl θ := by
  refine ring_nak (N := a.map (sec p)) ?_
  rw [Ideal.map_le_iff_le_comap]
  intro g hg
  rw [Ideal.mem_comap]
  have e2 : (a.map (sec p)) ^ 2 = (a ^ 2).map (sec p) := (Ideal.map_pow _ _ _).symm
  rw [e2]
  obtain ⟨s, hs⟩ := exists_s p 2 (a := a)
  let i := ιc Y ((a ^ 2).map (sec p))
  have hpt : X.map i.op θ = X.map s.op (χ 2) := hθ 2 _ i s hs
  have h1 : (sec s) ((sec (ιc T (a ^ 2))) g) ∈ (C.idl θ).map (sec i) := by
    rw [← C.idl_map, hpt, C.idl_map]
    exact Ideal.mem_map_of_mem _ (le_idl_chi C hP hx hax hak 2 (χ 2) (hχe 2) (hχ 2) hg)
  have h2 : (sec i) ((sec p) g) = (sec s) ((sec (ιc T (a ^ 2))) g) := by
    rw [← sec_comp, ← sec_comp, hs]
  rw [← h2, Ideal.mem_map_iff_of_surjective _ (ιc_surj _)] at h1
  obtain ⟨w, hw, hwe⟩ := h1
  have h3 : (sec p) g - w ∈ (a ^ 2).map (sec p) := by
    refine (ιc_ker _ _).1 ?_
    rw [map_sub, hwe, sub_self]
  exact Submodule.mem_sup.2 ⟨w, hw, _, h3, by ring⟩

end AlgMag.ChartMain.DeligneQS
