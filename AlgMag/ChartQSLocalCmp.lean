/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartQSLocalInst
import AlgMag.ChartQSLocalTriv

/-!
# `τ = θ` on `D(a) Y`, for `Y` flat with `m` in the Jacobson radical

For `LocalModelStep`: no surjectivity of `Γ(T) → Γ(Y)/a^k` is used,
no point `χ` on `V(a^k)`: the comparison is modulo `mⁿ` directly, and Krull in `Γ(Y)` concludes.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Space

universe u

namespace AlgMag.ChartMain.DeligneQS.ChartQSLocal

/-- Krull: an ideal of a noetherian ring is closed for `m` in the Jacobson radical. -/
lemma mem_of_forall_sup {R : Type*} [CommRing R] [IsNoetherianRing R] (m K : Ideal R)
    (hm : m ≤ Ideal.jacobson ⊥) (z : R) (h : ∀ n : ℕ, z ∈ K ⊔ m ^ n) : z ∈ K := by
  let π := Ideal.Quotient.mk K
  have hj : m.map π ≤ Ideal.jacobson ⊥ := by
    refine Ideal.map_le_iff_le_comap.2 fun r hr => ?_
    rw [Ideal.mem_comap, Ideal.mem_jacobson_bot]
    intro y
    obtain ⟨y', rfl⟩ := Ideal.Quotient.mk_surjective y
    have := (Ideal.mem_jacobson_bot.1 (hm hr)) y'
    have h2 := this.map π
    simpa [π] using h2
  have h0 : π z = 0 := by
    refine ChartQSAlg.eq_zero_of_mem_pow (m.map π) hj (π z) fun k => ?_
    rw [← Ideal.map_pow]
    obtain ⟨u, hu, v, hv, e⟩ := Submodule.mem_sup.1 (h k)
    have : π z = π v := by
      rw [← e, map_add, Ideal.Quotient.eq_zero_iff_mem.2 hu, zero_add]
    rw [this]
    exact Ideal.mem_map_of_mem _ hv
  exact Ideal.Quotient.eq_zero_iff_mem.1 h0

lemma mem_of_eq' {R : Type*} [CommRing R] {K : Ideal R} {a b : R} (h : a = b) (hb : b ∈ K) : a ∈ K :=
  h ▸ hb

lemma mem_sup_congr {R : Type*} [CommRing R] {K L L' : Ideal R} {z : R} (h : L = L') (hz : z ∈ K ⊔ L') :
    z ∈ K ⊔ L := h ▸ hz

lemma mem_sup_of_map {R R' : Type*} [CommRing R] [CommRing R'] (π : R →+* R')
    (hs : Function.Surjective π) (K L : Ideal R) (hk : ∀ c, π c = 0 ↔ c ∈ L) (z : R)
    (h : π z ∈ K.map π) : z ∈ K ⊔ L := by
  rw [Ideal.mem_map_iff_of_surjective _ hs] at h
  obtain ⟨w, hw, hwe⟩ := h
  have h3 : z - w ∈ L := (hk _).1 (by rw [map_sub, hwe, sub_self])
  exact Submodule.mem_sup.2 ⟨w, hw, _, h3, by ring⟩

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [AddMonoid.FG M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

variable {actX : AAction (fppfO B S hS) M X} {U₀ : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U₀)] {actU : AAction (fppfO B S hS) M (yoneda.obj U₀)}
  {fU : yoneda.obj U₀ ⟶ X} {V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  {φ : yoneda.obj V ⟶ X} (C : Ctx actX actU fU φ)
  {T : BigFppfOver B S hS} [hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  {m a : Ideal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)}
  {x : ∀ n, X.obj (op (Vc T (m ^ n)))}
  (hax : ∀ n, C.idl (x n) = a.map (sec (ιc T (m ^ n))))
  {Y : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj Y)]
  [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤)] (p : Y ⟶ T)
  (hJ : m.map (sec p) ≤ Ideal.jacobson ⊥)
  {θ : X.obj (op Y)}
  (hθ : ∀ (n : ℕ) (W : BigFppfOver B S hS) (i : W ⟶ Y) (s : W ⟶ Vc T (m ^ n)),
    s ≫ ιc T (m ^ n) = i ≫ p → X.map i.op θ = X.map s.op (x n))

/-- `s : V(mⁿ Γ(Y)) → V(mⁿ)`. -/
lemma exists_sY (n : ℕ) : ∃ s : Vc Y ((m ^ n).map (sec p)) ⟶ Vc T (m ^ n),
    s ≫ ιc T (m ^ n) = ιc Y ((m ^ n).map (sec p)) ≫ p :=
  exists_factor_closed _ _ fun z hz => by
    rw [sec_comp]
    exact closedι_appTop_of_mem _ (Ideal.mem_map_of_mem _ hz)

include hax hJ hθ in
set_option maxHeartbeats 2000000 in
/-- `a Γ(Y) ⊂ J Γ(Y)`, by Krull. -/
theorem le_idl_thetaY : a.map (sec p) ≤ C.idl θ := by
  refine Ideal.map_le_iff_le_comap.2 fun g hg => ?_
  refine Ideal.mem_comap.2 (mem_of_forall_sup (m.map (sec p)) _ hJ _ fun n => ?_)
  have en : (m.map (sec p)) ^ n = (m ^ n).map (sec p) := (Ideal.map_pow _ _ _).symm
  obtain ⟨s, hs⟩ := exists_sY p n (m := m)
  have hpt : X.map (ιc Y ((m ^ n).map (sec p))).op θ = X.map s.op (x n) := hθ n _ _ s hs
  have e₁ : C.idl (X.map s.op (x n)) = (C.idl (x n)).map (sec s) := C.idl_map s (x n)
  have e₂ : C.idl (X.map (ιc Y ((m ^ n).map (sec p))).op θ) =
      (C.idl θ).map (sec (ιc Y ((m ^ n).map (sec p)))) := C.idl_map _ θ
  have h2 : (sec (ιc Y ((m ^ n).map (sec p)))) ((sec p) g) = (sec s) ((sec (ιc T (m ^ n))) g) :=
    (sec_comp _ p g).symm.trans ((congrArg (fun c => (sec c) g) hs.symm).trans
      (sec_comp s (ιc T (m ^ n)) g))
  have h1 : (sec (ιc Y ((m ^ n).map (sec p)))) ((sec p) g) ∈
      (C.idl θ).map (sec (ιc Y ((m ^ n).map (sec p)))) :=
    mem_of_eq' h2 (e₂.le (((congrArg C.idl hpt).ge) (e₁.ge
      (Ideal.mem_map_of_mem _ ((hax n).ge (Ideal.mem_map_of_mem _ hg))))))
  exact mem_sup_congr en (mem_sup_of_map _ (ιc_surj _) _ _ (fun c => ιc_ker _ c) _ h1)

include hax hJ hθ in
set_option maxHeartbeats 4000000 in
/-- The separation in `Γ(Y)`: the values of `f` from `T` and from `θ` agree. -/
theorem cmp_Y' {f g} (hg : g ∈ a) {N : ℕ} {t} (ht : LL C x f (g ^ N) t) {E : ℕ} {tθ}
    (htθ : Lift C θ f ((sec p) g ^ E) tθ) :
    (sec p) g ^ E₀ C f * ((sec p) g ^ E * (sec p) t - (sec p) g ^ N * tθ) = 0 := by
  refine ChartQSAlg.eq_zero_of_mem_pow (m.map (sec p)) hJ _ fun n => ?_
  rw [← Ideal.map_pow]
  refine (ιc_ker _ _).1 ?_
  obtain ⟨s, hs⟩ := exists_sY p n (m := m)
  let i := ιc Y ((m ^ n).map (sec p))
  have hpt : X.map i.op θ = X.map s.op (x n) := hθ n _ i s hs
  have hcs : ∀ z, (sec s) ((sec (ιc T (m ^ n))) z) = (sec i) ((sec p) z) := fun z =>
    (sec_comp s (ιc T (m ^ n)) z).symm.trans ((congrArg (fun c => (sec c) z) hs).trans
      (sec_comp i p z))
  have l₁ : Lift C (X.map i.op θ) f ((sec i) ((sec p) g ^ E)) ((sec i) tθ) := lift_map C i htθ
  have l₂ : Lift C (X.map i.op θ) f ((sec i) ((sec p) g ^ N)) ((sec i) ((sec p) t)) := by
    have := lift_map C s (ht n)
    rw [← hpt, hcs, map_pow, hcs] at this
    exact this
  have hpg : (sec i) ((sec p) g) ∈ C.idl (X.map i.op θ) := by
    rw [C.idl_map]
    exact Ideal.mem_map_of_mem _ (le_idl_thetaY C hax p hJ hθ (Ideal.mem_map_of_mem _ hg))
  have hc := lift_cross C l₂ l₁ (Ideal.pow_mem_pow hpg (E₀ C f))
  simp only [map_mul, map_sub, map_pow] at hc ⊢
  exact hc

variable {gens : Set Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)} (hgens : a = Ideal.span gens)
  (y₀ : UTo gens ⟶ U₀)
  (hy₀ : ∀ f r t, LL C x f r t → (sec (jo gens)) r * (sec y₀) f = (sec (jo gens)) t)
  (hval : ∀ (g : gens) (f), ∃ (N : ℕ) (t : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)),
    LL C x f ((g : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) ^ N) t)

include hax hJ hθ hgens hy₀ hval in
set_option maxHeartbeats 4000000 in
/-- Compatibility on `V`, on an affine `W` where `g` is a unit. -/
theorem tau_thetaY_aff {W : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    (g₁ : W ⟶ UTo gens) (g₂ : W ⟶ Y) (hc : g₁ ≫ jo gens = g₂ ≫ p) (g : gens)
    (hu : IsUnit ((sec (g₁ ≫ jo gens)) (g : Γ((SCH).obj T, ⊤)))) :
    X.map g₁.op (fU.app (op _) y₀) = X.map g₂.op θ := by
  have hga : (g : Γ((SCH).obj T, ⊤)) ∈ a := hgens ▸ Ideal.subset_span g.2
  have hpg : (sec p) (g : Γ((SCH).obj T, ⊤)) ∈ C.idl θ :=
    le_idl_thetaY C hax p hJ hθ (Ideal.mem_map_of_mem _ hga)
  have hcs : ∀ z, (sec g₁) ((sec (jo gens)) z) = (sec g₂) ((sec p) z) := fun z =>
    (sec_comp g₁ (jo gens) z).symm.trans ((congrArg (fun c => (sec c) z) hc).trans
      (sec_comp g₂ p z))
  rw [sec_comp, hcs] at hu
  have hmem : (sec g₂) ((sec p) (g : Γ((SCH).obj T, ⊤))) ∈ C.idl (X.map g₂.op θ) := by
    rw [C.idl_map]
    exact Ideal.mem_map_of_mem _ hpg
  obtain ⟨y₁, hy₁⟩ := C.lift_U (X.map g₂.op θ) (Ideal.eq_top_of_isUnit_mem _ hmem hu)
  have hsec : ∀ f, (sec y₁) f = (sec (g₁ ≫ y₀)) f := by
    intro f
    obtain ⟨N, t, ht⟩ := hval g f
    obtain ⟨tθ, htθ⟩ := lift_exists C θ f (r := (sec p) (g : Γ((SCH).obj T, ⊤)) ^ expo C f)
      (Ideal.pow_mem_pow hpg _)
    have k := congrArg (sec g₂) (cmp_Y' C hax p hJ hθ hga ht htθ)
    have l := lift_map C g₂ htθ
    rw [← hy₁, map_pow] at l
    have e₁ := lift_formula C y₁ l
    have e₂ := congrArg (sec g₁) (hy₀ f _ _ ht)
    rw [map_mul, hcs, hcs, map_pow, map_pow] at e₂
    simp only [map_mul, map_sub, map_pow, map_zero] at k
    set w := (sec g₂) ((sec p) (g : Γ((SCH).obj T, ⊤))) with hw
    have k' := (hu.pow (E₀ C f)).mul_left_cancel (k.trans (mul_zero _).symm)
    rw [sec_comp g₁ y₀]
    apply ((hu.pow N).mul (hu.pow (expo C f))).mul_left_cancel
    rw [e₁] at k'
    rw [sub_eq_zero] at k'
    calc _ = w ^ N * (w ^ expo C f * (sec y₁) f) := by ring
      _ = w ^ expo C f * (sec g₂) ((sec p) t) := k'.symm
      _ = w ^ expo C f * (w ^ N * (sec g₁) ((sec y₀) f)) := by rw [e₂]
      _ = _ := by ring
  have : y₁ = g₁ ≫ y₀ := eq_of_sec hsec
  rw [← hy₁, this, map_yoneda_app (φ := fU) g₁ y₀]

include hax hJ hθ hgens hy₀ hval in
/-- **`τ = θ` on `D(a) Y`.** -/
theorem tau_thetaY (hX : IsAlgebraicSpace B S hS X) ⦃W : BigFppfOver B S hS⦄ (g₁ : W ⟶ UTo gens)
    (g₂ : W ⟶ Y) (hc : g₁ ≫ jo gens = g₂ ≫ p) :
    X.map g₁.op (fU.app (op _) y₀) = X.map g₂.op θ := by
  refine eq_of_unit hX g₁ fun {A} _ i g hu => ?_
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp]
  refine tau_thetaY_aff C hax p hJ hθ hgens y₀ hy₀ hval (i ≫ g₁) (i ≫ g₂) ?_ g ?_
  · rw [Category.assoc, Category.assoc, hc]
  · rwa [Category.assoc]

end AlgMag.ChartMain.DeligneQS.ChartQSLocal
