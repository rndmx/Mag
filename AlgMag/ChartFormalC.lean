/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartMain
import AlgMag.ChartS5Spec

/-!
# §§3–4 of the chart-lemma proof: from a tower to `Spec C → X`, abstractly

`CTower`: a graded ring `C` with graded surjections `C → Γ(X_n)`, kernels `m^{n+1}`, `(C,m)` a complete
pair. For `C` the graded completion of `AlgMag.ChartMain.AffineTower`, see `ChartFormal2`.

* `CTower.lift`: a map to `T = Spec C` killing `ker(C → Γ(X_n))` factors through `X_n`.
* `CTower.exists_phi`: Theorem 4.1 gives `φ : T → X` from `c n : X_n → X`.
* `CTower.sn_phi`, `CTower.hMono`, `CTower.isIso_trunc`: properties of `φ`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.ChartAssembly

open ChartMain ChartS5

/-- A graded ring `C` with the graded surjections to the rings of a tower of affine objects. -/
structure CTower (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (M : Type u)
    [AddCommGroup M] [AddMonoid.FG M] [DecidableEq M] [IsAffine S]
    (C : Type u) [CommRing C] (𝒞 : M → AddSubgroup C) [GradedRing 𝒞] where
  /-- `Γ(S) → C` -/
  ρ : RT (siteTop (B := B) (S := S) (hS := hS)) →+* C
  hC : B.Contains (Spec (.of C))
  h0 : ∀ s, ρ s ∈ 𝒞 0
  /-- the ideal of the orbit -/
  m : Ideal C
  /-- `X_n` -/
  U : ℕ → BigFppfOver B S hS
  aff : ∀ n, IsAffine ((BigFppfOver.toScheme B S hS).obj (U n))
  /-- the action on `X_n` -/
  act : ∀ n, AAction (fppfO B S hS) M (yoneda.obj (U n))
  /-- `X_n → X_{n+1}` -/
  j : ∀ n, U n ⟶ U (n + 1)
  /-- `C → Γ(X_n)` -/
  ev : ∀ n, C →+* RT (U n)
  ev_surj : ∀ n, Function.Surjective (ev n)
  ev_ρ : ∀ n, (ev n).comp ρ = ((BigFppfOver.toScheme B S hS).map (toTop' (U n))).appTop.hom
  ev_mem : ∀ n d u, u ∈ 𝒞 d → ev n u ∈ homog (act n) d
  ev_j : ∀ n u, ((BigFppfOver.toScheme B S hS).map (j n)).appTop.hom (ev (n + 1) u) = ev n u
  ker_ev : ∀ n, RingHom.ker (ev n) = m ^ (n + 1)
  complete : ChartGraded.IsCompletePair 𝒞 m

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [AddMonoid.FG M] [DecidableEq M] [IsAffine S]
  {C : Type u} [CommRing C] {𝒞 : M → AddSubgroup C} [GradedRing 𝒞]

local notation "SCH" => BigFppfOver.toScheme B S hS

lemma cmapComp {V W Z : BigFppfOver B S hS} (f : V ⟶ W) (g : W ⟶ Z) (x) :
    ((BigFppfOver.toScheme B S hS).map (f ≫ g)).appTop.hom x =
      ((BigFppfOver.toScheme B S hS).map f).appTop.hom
        (((BigFppfOver.toScheme B S hS).map g).appTop.hom x) := by
  rw [Functor.map_comp, Scheme.Hom.comp_appTop]; rfl

lemma chom_appTop (V : BigFppfOver B S hS) (s : RT (siteTop (B := B) (S := S) (hS := hS))) :
    (V.hom.hom).appTop.hom s = ((BigFppfOver.toScheme B S hS).map (toTop' V)).appTop.hom s := by
  have e : (BigFppfOver.toScheme B S hS).map (toTop' V) ≫ 𝟙 S = V.hom.hom :=
    congrArg (fun z => z.hom) (Over.w (toTop' V))
  exact congrArg (fun z => z.appTop.hom s) (e.symm.trans (Category.comp_id _))

namespace CTower

variable (D : CTower B S hS M C 𝒞)

instance (n : ℕ) : IsAffine ((BigFppfOver.toScheme B S hS).obj (D.U n)) := D.aff n

/-- `T = Spec C`. -/
noncomputable abbrev Tb : BigFppfOver B S hS := rObj D.ρ D.hC

/-- `C ≃ Γ(T)`. -/
noncomputable abbrev sec : C ≃+* Γ((BigFppfOver.toScheme B S hS).obj D.Tb, ⊤) := rSec D.ρ D.hC

/-- The action on `T`. -/
noncomputable abbrev actTb : AAction (fppfO B S hS) M (yoneda.obj D.Tb) := rAct D.ρ D.hC 𝒞 D.h0

/-- The ideal `m`, on `T`. -/
noncomputable abbrev mTb : Ideal Γ((BigFppfOver.toScheme B S hS).obj D.Tb, ⊤) :=
  D.m.map D.sec.toRingHom

/-- `τ` kills `ker (C → Γ(X_n))`. -/
def Kills {W : BigFppfOver B S hS} (τ : W ⟶ D.Tb) (n : ℕ) : Prop :=
  ∀ u ∈ RingHom.ker (D.ev n), ((BigFppfOver.toScheme B S hS).map τ).appTop.hom (D.sec u) = 0

variable {D}

lemma Kills.comp {W W' : BigFppfOver B S hS} {τ : W ⟶ D.Tb} {n : ℕ} (h : D.Kills τ n) (g : W' ⟶ W) :
    D.Kills (g ≫ τ) n := fun u hu => by
  rw [cmapComp, h u hu, map_zero]

lemma ker_ev_succ_le (D : CTower B S hS M C 𝒞) (n : ℕ) : RingHom.ker (D.ev (n + 1)) ≤ RingHom.ker (D.ev n) :=
  fun u hu => by
    rw [RingHom.mem_ker] at hu ⊢
    rw [← D.ev_j, hu, map_zero]

lemma ker_ev_anti (D : CTower B S hS M C 𝒞) {n k : ℕ} (h : n ≤ k) :
    RingHom.ker (D.ev k) ≤ RingHom.ker (D.ev n) := by
  induction k, h using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih => exact (D.ker_ev_succ_le k).trans ih

lemma Kills.mono {W : BigFppfOver B S hS} {τ : W ⟶ D.Tb} {n k : ℕ} (h : D.Kills τ n) (hk : n ≤ k) :
    D.Kills τ k := fun u hu => h u (D.ker_ev_anti hk hu)

variable (D)

/-- `Γ(X_n) → Γ(W)`. -/
noncomputable def liftRing {W : BigFppfOver B S hS} (τ : W ⟶ D.Tb) (n : ℕ) (h : D.Kills τ n) :
    RT (D.U n) →+* Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) :=
  (D.ev n).liftOfSurjective (D.ev_surj n)
    ⟨((BigFppfOver.toScheme B S hS).map τ).appTop.hom.comp D.sec.toRingHom, fun u hu => h u hu⟩

lemma liftRing_ev {W : BigFppfOver B S hS} (τ : W ⟶ D.Tb) (n : ℕ) (h : D.Kills τ n) (u : C) :
    D.liftRing τ n h (D.ev n u) = ((BigFppfOver.toScheme B S hS).map τ).appTop.hom (D.sec u) :=
  RingHom.liftOfRightInverse_comp_apply _ _ _ _ u

lemma sec_structure {W : BigFppfOver B S hS} (τ : W ⟶ D.Tb)
    (s : RT (siteTop (B := B) (S := S) (hS := hS))) :
    ((BigFppfOver.toScheme B S hS).map τ).appTop.hom (D.sec (D.ρ s)) =
      ((BigFppfOver.toScheme B S hS).map (toTop' W)).appTop.hom s := by
  have e2 : D.sec (D.ρ s) =
      ((BigFppfOver.toScheme B S hS).map (spToT _ D.ρ D.hC)).appTop.hom s :=
    (spToT_appTop _ D.ρ D.hC s).symm
  have e3 : τ ≫ spToT _ D.ρ D.hC = toTop' W := Over.mkIdTerminal.hom_ext _ _
  rw [e2, ← e3, cmapComp]

lemma liftRing_structure {W : BigFppfOver B S hS} (τ : W ⟶ D.Tb) (n : ℕ) (h : D.Kills τ n)
    (s : RT (siteTop (B := B) (S := S) (hS := hS))) :
    D.liftRing τ n h (((BigFppfOver.toScheme B S hS).map (toTop' (D.U n))).appTop.hom s) =
      ((BigFppfOver.toScheme B S hS).map (toTop' W)).appTop.hom s := by
  rw [← D.ev_ρ, RingHom.comp_apply, liftRing_ev, sec_structure]

/-- `W → X_n`, for `τ : W → T` killing `ker (C → Γ(X_n))`. -/
noncomputable def lift {W : BigFppfOver B S hS} (τ : W ⟶ D.Tb) (n : ℕ) (h : D.Kills τ n) :
    W ⟶ D.U n :=
  haveI : IsAffine (B.obj hS).obj := ‹IsAffine S›
  siteHom (toAffine (D.liftRing τ n h)) (toAffine_comp _ _ _ (RingHom.ext fun s =>
    (congrArg (D.liftRing τ n h) (chom_appTop (D.U n) s)).trans
      ((D.liftRing_structure τ n h s).trans (chom_appTop _ s).symm)))

lemma lift_appTop {W : BigFppfOver B S hS} (τ : W ⟶ D.Tb) (n : ℕ) (h : D.Kills τ n) (u : C) :
    ((BigFppfOver.toScheme B S hS).map (D.lift τ n h)).appTop.hom (D.ev n u) =
      ((BigFppfOver.toScheme B S hS).map τ).appTop.hom (D.sec u) := by
  rw [← liftRing_ev D τ n h u]
  exact congrArg (fun z => z (D.ev n u)) (toAffine_appTop (D.liftRing τ n h))

variable {D}

lemma U_ext {W : BigFppfOver B S hS} {n : ℕ} {a b : W ⟶ D.U n}
    (h : ∀ u, ((BigFppfOver.toScheme B S hS).map a).appTop.hom (D.ev n u) =
      ((BigFppfOver.toScheme B S hS).map b).appTop.hom (D.ev n u)) : a = b :=
  siteExt (toAffine_ext (RingHom.ext fun y => by
    obtain ⟨u, rfl⟩ := D.ev_surj n y
    exact h u))

lemma Tb_ext {W : BigFppfOver B S hS} {a b : W ⟶ D.Tb}
    (h : ∀ u, ((BigFppfOver.toScheme B S hS).map a).appTop.hom (D.sec u) =
      ((BigFppfOver.toScheme B S hS).map b).appTop.hom (D.sec u)) : a = b :=
  siteExt (toAffine_ext (RingHom.ext fun y => by
    obtain ⟨u, rfl⟩ := D.sec.surjective y
    exact h u))

variable (D)

/-- `X_n → T`. -/
noncomputable def sn (n : ℕ) : D.U n ⟶ D.Tb :=
  spLift _ D.ρ D.hC (toTop' (D.U n)) (D.ev n) (D.ev_ρ n)

lemma sn_appTop (n : ℕ) (u : C) :
    ((BigFppfOver.toScheme B S hS).map (D.sn n)).appTop.hom (D.sec u) = D.ev n u :=
  spLift_appTop _ D.ρ D.hC (toTop' (D.U n)) (D.ev n) (D.ev_ρ n) u

lemma sn_kills (n : ℕ) : D.Kills (D.sn n) n := fun u hu => by
  rw [sn_appTop]; exact hu

lemma lift_sn {W : BigFppfOver B S hS} (τ : W ⟶ D.Tb) (n : ℕ) (h : D.Kills τ n) :
    D.lift τ n h ≫ D.sn n = τ :=
  Tb_ext fun u => by rw [cmapComp, sn_appTop, lift_appTop]

lemma lift_sn_self (n : ℕ) : D.lift (D.sn n) n (D.sn_kills n) = 𝟙 _ :=
  U_ext fun u => by
    rw [lift_appTop, sn_appTop]
    simp

lemma comp_lift {W W' : BigFppfOver B S hS} (g : W' ⟶ W) (τ : W ⟶ D.Tb) (n : ℕ) (h : D.Kills τ n) :
    g ≫ D.lift τ n h = D.lift (g ≫ τ) n (h.comp g) :=
  U_ext fun u => by rw [cmapComp, lift_appTop, lift_appTop, cmapComp]

lemma lift_j {W : BigFppfOver B S hS} (τ : W ⟶ D.Tb) (n : ℕ) (h : D.Kills τ n) :
    D.lift τ n h ≫ D.j n = D.lift τ (n + 1) (h.mono (Nat.le_succ n)) :=
  U_ext fun u => by rw [cmapComp, D.ev_j, lift_appTop, lift_appTop]

section Points

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (c : ∀ n, yoneda.obj (D.U n) ⟶ X)

/-- The point of `X` given by `τ : W → T`. -/
noncomputable def pt {W : BigFppfOver B S hS} (τ : W ⟶ D.Tb) (n : ℕ) (h : D.Kills τ n) : X.obj (op W) :=
  (c n).app (op W) (D.lift τ n h)

variable (hcj : ∀ n, yoneda.map (D.j n) ≫ c (n + 1) = c n)

include hcj in
lemma pt_succ {W : BigFppfOver B S hS} (τ : W ⟶ D.Tb) (n : ℕ) (h : D.Kills τ n) :
    D.pt c τ (n + 1) (h.mono (Nat.le_succ n)) = D.pt c τ n h := by
  unfold pt
  rw [← lift_j D τ n h, ← hcj n]
  rfl

include hcj in
lemma pt_le {W : BigFppfOver B S hS} (τ : W ⟶ D.Tb) {n k : ℕ} (hk : n ≤ k) (h : D.Kills τ n) :
    D.pt c τ k (h.mono hk) = D.pt c τ n h := by
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih => exact (pt_succ D c hcj τ k (h.mono hk)).trans ih

include hcj in
lemma pt_eq {W : BigFppfOver B S hS} (τ : W ⟶ D.Tb) {n k : ℕ} (h : D.Kills τ n) (h' : D.Kills τ k) :
    D.pt c τ n h = D.pt c τ k h' := by
  rcases le_total n k with hk | hk
  · exact (pt_le D c hcj τ hk h).symm
  · exact pt_le D c hcj τ hk h'

lemma map_pt {W W' : BigFppfOver B S hS} (g : W' ⟶ W) (τ : W ⟶ D.Tb) (n : ℕ) (h : D.Kills τ n) :
    X.map g.op (D.pt c τ n h) = D.pt c (g ≫ τ) n (h.comp g) := by
  unfold pt
  rw [← comp_lift D g τ n h]
  exact (NatTrans.naturality_apply (c n) g.op (D.lift τ n h)).symm

end Points

/-- `V(mⁿ) ⊂ T`, as an object. -/
noncomputable abbrev Vn (n : ℕ) : BigFppfOver B S hS :=
  Chart.immObj D.Tb (Chart.closedι ((BigFppfOver.toScheme B S hS).obj D.Tb) (D.mTb ^ n))

/-- `V(mⁿ) → T`. -/
noncomputable abbrev ιn (n : ℕ) : D.Vn n ⟶ D.Tb :=
  Chart.immι D.Tb (Chart.closedι ((BigFppfOver.toScheme B S hS).obj D.Tb) (D.mTb ^ n))

lemma sec_mem_pow {u : C} {n : ℕ} (hu : u ∈ D.m ^ n) : D.sec u ∈ D.mTb ^ n := by
  rw [mTb, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ hu

/-- `V(mⁿ⁺¹) → T` kills `ker(C → Γ(X_n))`. -/
lemma ι_kills (n : ℕ) : D.Kills (D.ιn (n + 1)) n := fun u hu => by
  rw [D.ker_ev n] at hu
  exact ChartMain.closedι_appTop_of_mem _ (D.sec_mem_pow hu)

lemma ι_kills' (n : ℕ) : D.Kills (D.ιn n) n :=
  fun u hu => by
    rw [D.ker_ev n] at hu
    exact ChartMain.closedι_appTop_of_mem _
      (D.sec_mem_pow (Ideal.pow_le_pow_right (Nat.le_succ n) hu))

section Effectivity

variable [IsAffine S]

theorem complete_Tb :
    letI := gradedRingOfAction D.actTb
    ChartGraded.IsCompletePair (homog D.actTb) D.mTb := by
  letI := gradedRingOfAction D.actTb
  exact D.complete.of_surjective D.sec.toRingHom D.sec.surjective
    (fun d a ha => (mem_homog_rAct D.ρ D.hC 𝒞 D.h0).2 ha)

/-- The action is seen on `C`. -/
lemma lift_smul {E W : BigFppfOver B S hS} (i : E ⟶ D.Tb) (n : ℕ) (h : D.Kills i n)
    (t t' : W ⟶ E) (g : Multiplicative M →* Γ((BigFppfOver.toScheme B S hS).obj W, ⊤))
    (ht : t' ≫ i = D.actTb.smul (F := yoneda.obj D.Tb) (U := op W) g (t ≫ i)) :
    t' ≫ D.lift i n h = (D.act n).smul (F := yoneda.obj (D.U n)) (U := op W) g (t ≫ D.lift i n h) := by
  have key : ((BigFppfOver.toScheme B S hS).map (t' ≫ D.lift i n h)).appTop.hom.comp (D.ev n) =
      ((BigFppfOver.toScheme B S hS).map
        ((D.act n).smul (F := yoneda.obj (D.U n)) (U := op W) g (t ≫ D.lift i n h))).appTop.hom.comp
          (D.ev n) := by
    refine ringHom_ext_homogeneous 𝒞 fun d u hu => ?_
    have h1 := appTop_smul_of_mem (D.act n) (t ≫ D.lift i n h) g (D.ev_mem n d u hu)
    have h2 := appTop_smul_of_mem D.actTb (t ≫ i) g
      ((mem_homog_rAct D.ρ D.hC 𝒞 D.h0).2 hu)
    change ((BigFppfOver.toScheme B S hS).map (t' ≫ D.lift i n h)).appTop.hom (D.ev n u) =
      ((BigFppfOver.toScheme B S hS).map
        (smulAt (D.act n) g (t ≫ D.lift i n h))).appTop.hom (D.ev n u)
    rw [h1, cmapComp, lift_appTop, ← cmapComp, ht, cmapComp t, lift_appTop, ← cmapComp]
    exact h2
  exact U_ext fun u => congrArg (fun z => z u) key

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (c : ∀ n, yoneda.obj (D.U n) ⟶ X)
  (hcj : ∀ n, yoneda.map (D.j n) ≫ c (n + 1) = c n)
  (actX : AAction (fppfO B S hS) M X) (hce : ∀ n, IsEquivariant (D.act n) actX (c n))

include hcj hce in
/-- **§4**: Theorem 4.1 gives `φ : T → X`. -/
theorem exists_phi (heff : ChartConclude.EquivariantEffectivity X actX) :
    ∃ φ : yoneda.obj D.Tb ⟶ X, IsEquivariant D.actTb actX φ ∧
      ∀ n, φ.app (op (D.Vn n)) (D.ιn n) = D.pt c (D.ιn n) n (D.ι_kills' n) := by
  obtain ⟨φ, h1, h2⟩ := heff D.Tb D.actTb D.mTb D.complete_Tb
    (fun n => D.pt c (D.ιn n) n (D.ι_kills' n))
    (fun n k t ht => by
      rw [map_pt]
      have e : t ≫ D.ιn k = D.ιn n := ht
      have hk : D.Kills (t ≫ D.ιn k) k := (D.ι_kills' k).comp t
      refine (rfl : _ = D.pt c (t ≫ D.ιn k) k hk).trans ?_
      simp only [e]
      exact pt_eq D c hcj _ _ _)
    (fun n W t g t' ht => by
      rw [map_pt, map_pt]
      unfold pt
      rw [← comp_lift D t _ n (D.ι_kills' n), ← comp_lift D t' _ n (D.ι_kills' n),
        D.lift_smul (D.ιn n) n (D.ι_kills' n) t t' g ht]
      exact hce n g _)
  exact ⟨φ, h1, h2⟩

end Effectivity

section Phi

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (c : ∀ n, yoneda.obj (D.U n) ⟶ X)
  (hcj : ∀ n, yoneda.map (D.j n) ≫ c (n + 1) = c n)
  {φ : yoneda.obj D.Tb ⟶ X}
  (hφ : ∀ n, φ.app (op (D.Vn n)) (D.ιn n) = D.pt c (D.ιn n) n (D.ι_kills' n))

lemma kills_pow {W : BigFppfOver B S hS} {τ : W ⟶ D.Tb} {n : ℕ} (h : D.Kills τ n) :
    ∀ x ∈ D.mTb ^ (n + 1), ((BigFppfOver.toScheme B S hS).map τ).appTop.hom x = 0 := by
  have hle : D.mTb ^ (n + 1) ≤ RingHom.ker ((BigFppfOver.toScheme B S hS).map τ).appTop.hom := by
    rw [mTb, ← Ideal.map_pow, Ideal.map_le_iff_le_comap]
    intro u hu
    rw [← D.ker_ev n] at hu
    exact h u hu
  exact fun x hx => hle hx

lemma yoneda_comp_app {W W' : BigFppfOver B S hS} {V : BigFppfOver B S hS} (ψ : yoneda.obj V ⟶ X)
    (g : W' ⟶ W) (τ : W ⟶ V) : ψ.app (op W') (g ≫ τ) = X.map g.op (ψ.app (op W) τ) :=
  NatTrans.naturality_apply ψ g.op τ

include hcj hφ in
/-- `φ` on a map to `T` through `X_n`. -/
theorem phi_app {W : BigFppfOver B S hS} (τ : W ⟶ D.Tb) (n : ℕ) (h : D.Kills τ n) :
    φ.app (op W) τ = D.pt c τ n h := by
  obtain ⟨r, hr⟩ := exists_factor_closed τ (D.mTb ^ (n + 1)) (D.kills_pow h)
  have hr' : r ≫ D.ιn (n + 1) = τ := hr
  subst hr'
  rw [yoneda_comp_app, hφ, map_pt]
  exact pt_eq D c hcj _ _ _

include hcj hφ in
/-- `φ` restricted to `X_n` is `c n`. -/
theorem sn_phi (n : ℕ) : yoneda.map (D.sn n) ≫ φ = c n := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  refine (D.phi_app c hcj hφ (D.sn n) n (D.sn_kills n)).trans ?_
  unfold pt
  rw [lift_sn_self]
  rfl

lemma kills_zero {W : BigFppfOver B S hS} {a : W ⟶ D.Tb}
    (ha : ∀ x ∈ D.mTb, ((BigFppfOver.toScheme B S hS).map a).appTop.hom x = 0) : D.Kills a 0 :=
  fun u hu => by
    rw [D.ker_ev 0, zero_add, pow_one] at hu
    exact ha _ (Ideal.mem_map_of_mem _ hu)

include hcj hφ in
/-- `hMono`: the maps to `T` killing `m` are detected by `φ`, when `X_0 → X` is mono. -/
theorem hMono (hm : Mono (c 0)) {W : BigFppfOver B S hS} (a b : W ⟶ D.Tb)
    (ha : ∀ x ∈ D.mTb, ((BigFppfOver.toScheme B S hS).map a).appTop.hom x = 0)
    (hb : ∀ x ∈ D.mTb, ((BigFppfOver.toScheme B S hS).map b).appTop.hom x = 0)
    (hab : φ.app (op W) a = φ.app (op W) b) : a = b := by
  rw [D.phi_app c hcj hφ a 0 (D.kills_zero ha), D.phi_app c hcj hφ b 0 (D.kills_zero hb)] at hab
  have hinj := (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 hm (op W))
  have := hinj hab
  rw [← D.lift_sn a 0 (D.kills_zero ha), ← D.lift_sn b 0 (D.kills_zero hb), this]

lemma mem_mTb_iff (x : Γ((BigFppfOver.toScheme B S hS).obj D.Tb, ⊤)) :
    x ∈ D.mTb ↔ ((BigFppfOver.toScheme B S hS).map (D.sn 0)).appTop.hom x = 0 := by
  refine ⟨fun h => D.kills_pow (D.sn_kills 0) x (by rwa [zero_add, pow_one]), fun h => ?_⟩
  obtain ⟨u, rfl⟩ := D.sec.surjective x
  rw [sn_appTop, ← RingHom.mem_ker, D.ker_ev 0, zero_add, pow_one] at h
  exact Ideal.mem_map_of_mem _ h

lemma closed_ιn (n : ℕ) : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map (D.ιn n)) :=
  inferInstanceAs (IsClosedImmersion
    (Chart.closedι ((BigFppfOver.toScheme B S hS).obj D.Tb) (D.mTb ^ n)))

lemma mono_ιn (n : ℕ) : Mono (D.ιn n) := by
  have := D.closed_ιn n
  have h : Mono ((BigFppfOver.toScheme B S hS).map (D.ιn n)) := inferInstance
  exact (BigFppfOver.toScheme B S hS).mono_of_mono_map h

/-- `V(m^{n+1}) ≃ X_n`. -/
theorem isIso_trunc (n : ℕ) : IsIso (D.lift (D.ιn (n + 1)) n (D.ι_kills n)) := by
  obtain ⟨r, hr⟩ := exists_factor_closed (D.sn n) (D.mTb ^ (n + 1)) (D.kills_pow (D.sn_kills n))
  have hr' : r ≫ D.ιn (n + 1) = D.sn n := hr
  have hmono : Mono (D.ιn (n + 1)) := D.mono_ιn (n + 1)
  refine ⟨r, ?_, ?_⟩
  · rw [← cancel_mono (D.ιn (n + 1)), Category.assoc, hr', lift_sn, Category.id_comp]
  · refine U_ext fun u => ?_
    rw [cmapComp, lift_appTop, ← cmapComp, hr', sn_appTop]
    simp

include hcj hφ in
/-- `V(m^{n+1}) → T → X` is `V(m^{n+1}) ≃ X_n → X`. -/
theorem trunc_phi (n : ℕ) : yoneda.map (D.ιn (n + 1)) ≫ φ =
    yoneda.map (D.lift (D.ιn (n + 1)) n (D.ι_kills n)) ≫ c n := by
  rw [← D.sn_phi c hcj hφ n, ← Category.assoc, ← Functor.map_comp, lift_sn]

end Phi

end CTower

end AlgMag.ChartAssembly
