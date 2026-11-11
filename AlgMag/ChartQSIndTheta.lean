/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartQSIndCompat

/-!
# Lemma 4.3 of the chart-lemma proof (§4 of Algebraic Magnetism): `τ` and `θ` agree on `V`
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
  {a : Ideal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)}
  (hax : ∀ n, C.idl (x n) = a.map (sec (ιc T (m ^ n))))
  (hak : ∀ k, ∀ y ∈ a ^ k, ∀ d, (coact actT y).coeff d ∈ a ^ k)
  {χ : ∀ k, X.obj (op (Vc T (a ^ k)))}
  (hχ : ∀ (k n : ℕ) ⦃W : BigFppfOver B S hS⦄ (g₁ : W ⟶ Vc T (a ^ k)) (g₂ : W ⟶ Vc T (m ^ n)),
    g₁ ≫ ιc T (a ^ k) = g₂ ≫ ιc T (m ^ n) → X.map g₁.op (χ k) = X.map g₂.op (x n))
  (hχe : ∀ k, EquivAlong actT actX (ιc T (a ^ k)) (χ k))

include hP in
/-- `∩ mⁿ = 0` on a stable closed `V(J)`. -/
lemma sep_closed {J : Ideal Γ((SCH).obj T, ⊤)} (hJ : ∀ x ∈ J, ∀ d, (coact actT x).coeff d ∈ J)
    (z : Γ((SCH).obj (Vc T J), ⊤)) (hz : ∀ n : ℕ, z ∈ (m.map (sec (ιc T J))) ^ n) : z = 0 := by
  letI := gradedRingOfAction (closedAct actT hJ)
  have hC := isCompletePair_closedAct actT hJ hP
  have hb := Chart.iInf_pow_eq_bot (homog (closedAct actT hJ)) _ hC.hom hC.sep
  have : z ∈ ⨅ n : ℕ, (m.map (sec (ιc T J))) ^ n := Ideal.mem_iInf.2 hz
  rw [hb] at this
  exact this

include hP in
lemma sep_closed' {J : Ideal Γ((SCH).obj T, ⊤)} (hJ : ∀ x ∈ J, ∀ d, (coact actT x).coeff d ∈ J)
    (z : Γ((SCH).obj (Vc T J), ⊤))
    (hz : ∀ n : ℕ, (sec (ιc (Vc T J) ((m.map (sec (ιc T J))) ^ n))) z = 0) : z = 0 :=
  sep_closed hP hJ z fun n => (ιc_ker _ _).1 (hz n)

omit [AddMonoid.FG M] [DecidableEq M] in
lemma exists_sn (J : Ideal Γ((SCH).obj T, ⊤)) (n : ℕ) :
    ∃ sn : Vc (Vc T J) ((m.map (sec (ιc T J))) ^ n) ⟶ Vc T (m ^ n),
      sn ≫ ιc T (m ^ n) = ιc (Vc T J) ((m.map (sec (ιc T J))) ^ n) ≫ ιc T J := by
  have hk : ∀ z ∈ m ^ n, (sec (ιc (Vc T J) ((m.map (sec (ιc T J))) ^ n) ≫ ιc T J)) z = 0 := fun z hz => by
    rw [sec_comp]
    refine (ιc_ker _ _).2 ?_
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hz
  exact exists_factor_closed _ (m ^ n) hk

set_option maxHeartbeats 400000 in
include hP in
lemma cmp_gen {J : Ideal Γ((SCH).obj T, ⊤)} (hJ : ∀ x ∈ J, ∀ d, (coact actT x).coeff d ∈ J)
    (z : Γ((SCH).obj (Vc T J), ⊤))
    (H : ∀ (n : ℕ) (sn : Vc (Vc T J) ((m.map (sec (ιc T J))) ^ n) ⟶ Vc T (m ^ n)),
      sn ≫ ιc T (m ^ n) = ιc (Vc T J) ((m.map (sec (ιc T J))) ^ n) ≫ ιc T J →
      (sec (ιc (Vc T J) ((m.map (sec (ιc T J))) ^ n))) z = 0) : z = 0 := by
  exact sep_closed' (m := m) hP hJ z fun n => (exists_sn (m := m) J n).elim fun sn hsn => H n sn hsn

lemma rh_expand {R R' : Type*} [CommRing R] [CommRing R'] (ψ : R →+* R') (A b c : R) (e e₁ n : ℕ) :
    ψ (A ^ e * (A ^ e₁ * b - A ^ n * c)) = ψ A ^ e * (ψ A ^ e₁ * ψ b - ψ A ^ n * ψ c) := by
  simp only [map_mul, map_sub, map_pow]


/-- Transport of `Lift` along equalities, without `rw` (whose motive search is very slow here). -/
lemma lift_congr {W : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    {y y' : X.obj (op W)} {f : Γ((SCH).obj U₀, ⊤)} {r r' t t' : Γ((SCH).obj W, ⊤)}
    (hy : y = y') (hr : r = r') (ht : t = t') (h : Lift C y f r t) : Lift C y' f r' t' := by
  subst hy hr ht
  exact h

set_option maxHeartbeats 400000 in
include hP hx hax hak hχ hχe in
/-- Step (A) on a piece `W` of `V(a^k) ∩ V(mⁿ)`. -/
theorem cmp_n (k n : ℕ) {W : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    (u : W ⟶ Vc T (a ^ k)) (sn : W ⟶ Vc T (m ^ n)) (hsn : sn ≫ ιc T (m ^ n) = u ≫ ιc T (a ^ k))
    {f g} (hg : g ∈ a) {N : ℕ} {t} (ht : LL C x f (g ^ N) t) {E : ℕ} {tk}
    (htk : Lift C (χ k) f ((sec (ιc T (a ^ k))) g ^ E) tk) :
    (sec u) ((sec (ιc T (a ^ k))) g) ^ E₀ C f * ((sec u) ((sec (ιc T (a ^ k))) g) ^ E *
      (sec u) ((sec (ιc T (a ^ k))) t) - (sec u) ((sec (ιc T (a ^ k))) g) ^ N * (sec u) tk) = 0 := by
  have hpt : X.map u.op (χ k) = X.map sn.op (x n) := hχ k n u sn hsn.symm
  have hcs : ∀ z, (sec sn) ((sec (ιc T (m ^ n))) z) = (sec u) ((sec (ιc T (a ^ k))) z) := fun z => by
    rw [← sec_comp, ← sec_comp, hsn]
  have l₁ : Lift C (X.map u.op (χ k)) f ((sec u) ((sec (ιc T (a ^ k))) g) ^ E) ((sec u) tk) :=
    lift_congr C rfl (map_pow (sec u) _ _) rfl (lift_map C u htk)
  have l₂ : Lift C (X.map u.op (χ k)) f ((sec u) ((sec (ιc T (a ^ k))) g) ^ N)
      ((sec u) ((sec (ιc T (a ^ k))) t)) :=
    lift_congr C hpt.symm
      (((congrArg (sec sn) (map_pow (sec (ιc T (m ^ n))) g N)).trans
        (map_pow (sec sn) _ _)).trans (congrArg (· ^ N) (hcs g))) (hcs t) (lift_map C sn (ht n))
  have hgi : (sec (ιc T (a ^ k))) g ∈ C.idl (χ k) := le_idl_chi C hP hx hax hak k (χ k) (hχe k) (hχ k) hg
  have hmem : ∀ e, (sec u) ((sec (ιc T (a ^ k))) g) ^ e ∈ C.idl (X.map u.op (χ k)) ^ e := fun e => by
    refine Ideal.pow_mem_pow ?_ e
    exact (C.idl_map u (χ k)).ge (Ideal.mem_map_of_mem (sec u) hgi)
  exact lift_cross C l₂ l₁ (hmem (E₀ C f))

set_option maxHeartbeats 400000 in
include hP hx hax hak hχ hχe in
/-- `cmp_n` as the image of the element of `Γ(V(a^k))`. -/
theorem cmp_n' (k n : ℕ) {W : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    (u : W ⟶ Vc T (a ^ k)) (sn : W ⟶ Vc T (m ^ n)) (hsn : sn ≫ ιc T (m ^ n) = u ≫ ιc T (a ^ k))
    {f g} (hg : g ∈ a) {N : ℕ} {t} (ht : LL C x f (g ^ N) t) {E : ℕ} {tk}
    (htk : Lift C (χ k) f ((sec (ιc T (a ^ k))) g ^ E) tk) :
    (sec u) ((sec (ιc T (a ^ k))) g ^ E₀ C f * ((sec (ιc T (a ^ k))) g ^ E * (sec (ιc T (a ^ k))) t -
      (sec (ιc T (a ^ k))) g ^ N * tk)) = 0 :=
  (rh_expand (sec u) _ _ _ _ _ _).trans (cmp_n C hP hx hax hak hχ hχe k n u sn hsn hg ht htk)

set_option maxHeartbeats 400000 in
include hP hx hax hak hχ hχe in
/-- Step (A): the value on `V(a^k)` agrees with `t` from `C`, by separation modulo `mⁿ`. -/
theorem cmp_k (k : ℕ) {f g} (hg : g ∈ a) {N : ℕ} {t} (ht : LL C x f (g ^ N) t) {E : ℕ} {tk}
    (htk : Lift C (χ k) f ((sec (ιc T (a ^ k))) g ^ E) tk) :
    (sec (ιc T (a ^ k))) g ^ E₀ C f * ((sec (ιc T (a ^ k))) g ^ E * (sec (ιc T (a ^ k))) t -
      (sec (ιc T (a ^ k))) g ^ N * tk) = 0 := by
  refine cmp_gen hP (hak k) _ fun n sn hsn => ?_
  exact cmp_n' C hP hx hax hak hχ hχe k n _ sn hsn hg ht htk

variable {Y : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj Y)]
  [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤)] (p : Y ⟶ T)
  [hcomp : IsAdicComplete (a.map (sec p)) Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤)]
  {θ : X.obj (op Y)}
  (hθ : ∀ (k : ℕ) (W : BigFppfOver B S hS) (i : W ⟶ Y) (s : W ⟶ Vc T (a ^ k)),
    s ≫ ιc T (a ^ k) = i ≫ p → X.map i.op θ = X.map s.op (χ k))

lemma rh_Y {R Y' Z' : Type*} [CommRing R] [CommRing Y'] [CommRing Z'] (ψ : R →+* Z') (ι : Y' →+* Z')
    {A₀ t₀ tk : R} {A ty tθ : Y'} {e E N : ℕ} (hA : ψ A₀ = ι A) (ht : ψ t₀ = ι ty)
    (c : ψ (A₀ ^ e * (A₀ ^ E * t₀ - A₀ ^ N * tk)) = 0) (u : ι A ^ e * (ι tθ - ψ tk) = 0) :
    ι (A ^ (e + e) * (A ^ N * tθ - A ^ E * ty)) = 0 := by
  simp only [map_mul, map_sub, map_pow, hA, ht] at c ⊢
  linear_combination (ι A ^ e * ι A ^ N) * u - ι A ^ e * c

lemma sec_square {A₁ A₂ A₃ A₄ : BigFppfOver B S hS} (s : A₁ ⟶ A₂) (j : A₂ ⟶ A₄) (i : A₁ ⟶ A₃) (p : A₃ ⟶ A₄)
    (h : s ≫ j = i ≫ p) (z) : (sec s) ((sec j) z) = (sec i) ((sec p) z) := by
  rw [← sec_comp, ← sec_comp, h]

set_option maxHeartbeats 400000 in
include hP hx hax hak hχ hχe hθ in
/-- Step (B) on a piece over `V(a^k)`. -/
theorem cmp_Y_piece (k : ℕ) {W : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    (i : W ⟶ Y) (s : W ⟶ Vc T (a ^ k)) (hs : s ≫ ιc T (a ^ k) = i ≫ p)
    {f g} (hg : g ∈ a) {N : ℕ} {t} (ht : LL C x f (g ^ N) t) {E : ℕ} {tθ}
    (hE : expo C f ≤ E) (htθ : Lift C θ f ((sec p) g ^ E) tθ) :
    (sec i) ((sec p) g ^ (E₀ C f + E₀ C f) * ((sec p) g ^ N * tθ - (sec p) g ^ E * (sec p) t)) = 0 := by
  have hpt : X.map i.op θ = X.map s.op (χ k) := hθ k _ i s hs
  have hcs : ∀ z, (sec s) ((sec (ιc T (a ^ k))) z) = (sec i) ((sec p) z) := sec_square s _ i p hs
  have hgi : (sec (ιc T (a ^ k))) g ∈ C.idl (χ k) :=
    le_idl_chi C hP hx hax hak k (χ k) (hχe k) (hχ k) hg
  obtain ⟨tk, htk⟩ := lift_exists C (χ k) f (r := (sec (ιc T (a ^ k))) g ^ E)
    (Ideal.pow_le_pow_right hE (Ideal.pow_mem_pow hgi E))
  have c₁ := (congrArg (sec s) (cmp_k C hP hx hax hak hχ hχe k hg ht htk)).trans (map_zero (sec s))
  have l₁ : Lift C (X.map s.op (χ k)) f ((sec i) ((sec p) g) ^ E) ((sec i) tθ) :=
    lift_congr C hpt (map_pow (sec i) _ _) rfl (lift_map C i htθ)
  have l₂ : Lift C (X.map s.op (χ k)) f ((sec i) ((sec p) g) ^ E) ((sec s) tk) :=
    lift_congr C rfl ((map_pow (sec s) _ _).trans (congrArg (· ^ E) (hcs g))) rfl (lift_map C s htk)
  have h0 : (sec s) ((sec (ιc T (a ^ k))) g) ∈ C.idl (X.map s.op (χ k)) :=
    (C.idl_map s (χ k)).ge (Ideal.mem_map_of_mem (sec s) hgi)
  have hm : (sec i) ((sec p) g) ^ E₀ C f ∈ C.idl (X.map s.op (χ k)) ^ E₀ C f :=
    Ideal.pow_mem_pow (hcs g ▸ h0) _
  have u := lift_unique C l₁ l₂ hm
  exact rh_Y (sec s) (sec i) (hcs g) (hcs t) c₁ u

set_option maxHeartbeats 400000 in
include hP hx hax hak hχ hχe hθ in
/-- Step (B): the separation in `Γ(Y)`. -/
theorem cmp_Y {f g} (hg : g ∈ a) {N : ℕ} {t} (ht : LL C x f (g ^ N) t) {E : ℕ} {tθ}
    (hE : expo C f ≤ E) (htθ : Lift C θ f ((sec p) g ^ E) tθ) :
    (sec p) g ^ (E₀ C f + E₀ C f) * ((sec p) g ^ N * tθ - (sec p) g ^ E * (sec p) t) = 0 := by
  refine IsHausdorff.haus (hcomp.toIsHausdorff) _ fun k => ?_
  rw [SModEq.zero]
  have hmem : ∀ q : Γ((SCH).obj Y, ⊤), q ∈ (a ^ k).map (sec p) →
      q ∈ ((a.map (sec p)) ^ k • ⊤ : Submodule Γ((SCH).obj Y, ⊤) Γ((SCH).obj Y, ⊤)) := by
    intro q hq
    rw [Ideal.map_pow] at hq
    simpa [Ideal.mul_top] using hq
  refine hmem _ ((ιc_ker _ _).1 ?_)
  obtain ⟨s, hs⟩ := exists_s p k (a := a)
  exact cmp_Y_piece C hP hx hax hak hχ hχe p hθ k _ s hs hg ht hE htθ

variable {gens : Set Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)} (hgens : a = Ideal.span gens)
  (hhom : ∀ g ∈ gens, ∃ d, g ∈ homog actT d)
  (y₀ : UTo gens ⟶ U₀)
  (hy₀ : ∀ f r t, LL C x f r t → (sec (jo gens)) r * (sec y₀) f = (sec (jo gens)) t)

set_option maxHeartbeats 400000 in
include hP hx hax hak hχ hχe hθ hgens hhom hy₀ in
/-- **Compatibility on `V`**, on an affine `W` where `g` is a unit. -/
theorem tau_theta_aff {W : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    (g₁ : W ⟶ UTo gens) (g₂ : W ⟶ Y) (hc : g₁ ≫ jo gens = g₂ ≫ p) (g : gens)
    (hu : IsUnit ((sec (g₁ ≫ jo gens)) (g : Γ((SCH).obj T, ⊤)))) :
    X.map g₁.op (fU.app (op _) y₀) = X.map g₂.op θ := by
  have hga : (g : Γ((SCH).obj T, ⊤)) ∈ a := hgens ▸ Ideal.subset_span g.2
  have hNl := le_idl_theta C hP hx hax hak p hχ hχe hθ
  have hpg : (sec p) (g : Γ((SCH).obj T, ⊤)) ∈ C.idl θ := hNl (Ideal.mem_map_of_mem _ hga)
  have hcs : ∀ z, (sec g₁) ((sec (jo gens)) z) = (sec g₂) ((sec p) z) := fun z => by
    rw [← sec_comp, ← sec_comp, hc]
  rw [sec_comp, hcs] at hu
  have hmem : (sec g₂) ((sec p) (g : Γ((SCH).obj T, ⊤))) ∈ C.idl (X.map g₂.op θ) := by
    rw [C.idl_map]
    exact Ideal.mem_map_of_mem _ hpg
  obtain ⟨y₁, hy₁⟩ := C.lift_U (X.map g₂.op θ) (Ideal.eq_top_of_isUnit_mem _ hmem hu)
  have hsec : ∀ f, (sec y₁) f = (sec (g₁ ≫ y₀)) f := by
    intro f
    obtain ⟨N, t, ht⟩ := exists_val C hP hx hax hgens hhom g f
    obtain ⟨tθ, htθ⟩ := lift_exists C θ f (r := (sec p) (g : Γ((SCH).obj T, ⊤)) ^ expo C f)
      (Ideal.pow_mem_pow hpg _)
    have k := congrArg (sec g₂) (cmp_Y C hP hx hax hak hχ hχe p hθ hga ht le_rfl htθ)
    have l := lift_map C g₂ htθ
    rw [← hy₁, map_pow] at l
    have e₁ := lift_formula C y₁ l
    have e₂ := congrArg (sec g₁) (hy₀ f _ _ ht)
    rw [map_mul, hcs, hcs, map_pow, map_pow] at e₂
    simp only [map_mul, map_sub, map_pow, map_zero] at k
    set w := (sec g₂) ((sec p) (g : Γ((SCH).obj T, ⊤))) with hw
    have k' := (hu.pow (E₀ C f + E₀ C f)).mul_left_cancel (k.trans (mul_zero _).symm)
    rw [sec_comp g₁ y₀]
    apply ((hu.pow N).mul (hu.pow (expo C f))).mul_left_cancel
    rw [e₁] at k'
    rw [sub_eq_zero] at k'
    calc _ = w ^ N * (w ^ expo C f * (sec y₁) f) := by ring
      _ = w ^ expo C f * (sec g₂) ((sec p) t) := k'
      _ = w ^ expo C f * (w ^ N * (sec g₁) ((sec y₀) f)) := by rw [e₂]
      _ = _ := by ring
  have : y₁ = g₁ ≫ y₀ := eq_of_sec hsec
  rw [← hy₁, this, map_yoneda_app (φ := fU) g₁ y₀]

include hP hx hax hak hχ hχe hθ hgens hhom hy₀ in
/-- **Compatibility on `V`.** -/
theorem tau_theta (hX : IsAlgebraicSpace B S hS X) ⦃W : BigFppfOver B S hS⦄ (g₁ : W ⟶ UTo gens)
    (g₂ : W ⟶ Y) (hc : g₁ ≫ jo gens = g₂ ≫ p) :
    X.map g₁.op (fU.app (op _) y₀) = X.map g₂.op θ := by
  refine eq_of_unit hX g₁ fun {A} _ i g hu => ?_
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp]
  refine tau_theta_aff C hP hx hax hak hχ hχe p hθ hgens hhom y₀ hy₀ (i ≫ g₁) (i ≫ g₂) ?_ g ?_
  · rw [Category.assoc, Category.assoc, hc]
  · rwa [Category.assoc]

end AlgMag.ChartMain.DeligneQS
