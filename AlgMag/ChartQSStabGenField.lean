/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartQSStabGenAlg
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Ideal

/-!
# The generic stabilizer for quasi-separated `X`: the closure of `E_K`

`Ik` is the ideal of the closure of `E_K` in `D(M)_K`. It is closed under products of characters
(`hmul_Ik`), hence is the ideal of `D(M/Z)_K` (`exists_Z_field`).
-/

open TensorProduct AlgMag.ChartStratum

universe u

namespace AlgMag.ChartQSStabGen

section Tensor

variable {K : Type u} [Field K] {ι : Type u} [Finite ι] {A W : Type u} [AddCommGroup A] [Module K A]
  [AddCommGroup W] [Module K W] {Q : ι → Type u} [∀ i, AddCommGroup (Q i)] [∀ i, Module K (Q i)]

/-- Jointly injective maps stay jointly injective after tensoring over a field. -/
lemma tensor_joint_right (φ : ∀ i, A →ₗ[K] Q i) (hinj : ∀ a, (∀ i, φ i a = 0) → a = 0) (t : W ⊗[K] A)
    (h : ∀ i, TensorProduct.map LinearMap.id (φ i) t = 0) : t = 0 := by
  classical
  haveI := Fintype.ofFinite ι
  let Φ : A →ₗ[K] ∀ i, Q i := LinearMap.pi φ
  have hΦ : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero _).mpr fun a ha => hinj a fun i => ?_
    exact congrFun ha i
  have hl : Function.Injective (LinearMap.lTensor W Φ) :=
    Module.Flat.lTensor_preserves_injective_linearMap Φ hΦ
  refine (injective_iff_map_eq_zero _).mp hl t ?_
  refine (TensorProduct.piRight K K W Q).injective ?_
  rw [map_zero]
  funext i
  have e : ∀ s : W ⊗[K] A, TensorProduct.piRight K K W Q (LinearMap.lTensor W Φ s) i =
      TensorProduct.map LinearMap.id (φ i) s := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [Φ, TensorProduct.piRight_apply]
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  rw [e, h i]
  rfl

lemma tensor_joint_left (φ : ∀ i, A →ₗ[K] Q i) (hinj : ∀ a, (∀ i, φ i a = 0) → a = 0) (t : A ⊗[K] W)
    (h : ∀ i, TensorProduct.map (φ i) LinearMap.id t = 0) : t = 0 := by
  refine (TensorProduct.comm K A W).injective ?_
  rw [map_zero]
  refine tensor_joint_right φ hinj _ fun i => ?_
  have e : ∀ s : A ⊗[K] W, TensorProduct.map LinearMap.id (φ i) (TensorProduct.comm K A W s) =
      TensorProduct.comm K (Q i) W (TensorProduct.map (φ i) LinearMap.id s) := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [e, h i, map_zero]

lemma tensor_joint (φ : ∀ i, A →ₗ[K] Q i) (hinj : ∀ a, (∀ i, φ i a = 0) → a = 0) (t : A ⊗[K] A)
    (h : ∀ i j, TensorProduct.map (φ i) (φ j) t = 0) : t = 0 := by
  refine tensor_joint_left φ hinj t fun i => tensor_joint_right φ hinj _ fun j => ?_
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
  simpa using h i j

end Tensor

variable {R : Type u} [CommRing R] [IsDomain R] {M : Type u} [AddCommGroup M]
variable {ι : Type u} [Fintype ι] {f : ι → AddMonoidAlgebra R M}
  {G : ι → Finset (AddMonoidAlgebra R M)}

local notation "K" => FractionRing R

lemma ev_phi {A : Type u} [CommRing A] (ρ : K →+* A) (χ : Multiplicative M →* A)
    (x : AddMonoidAlgebra R M) :
    ev ρ χ (phi x) = ev (ρ.comp (algebraMap R K)) χ x := by
  have : (ev ρ χ).comp (phi (R := R) (M := M)) = ev (ρ.comp (algebraMap R K)) χ :=
    ringHom_ext' fun m r => by simp [phi, ev_single, AddMonoidAlgebra.mapRingHom_single]
  exact congrArg (fun k => k x) this

lemma lift_eq_ev {k A : Type u} [CommRing k] [CommRing A] [Algebra k A] (χ : Multiplicative M →* A)
    (x : AddMonoidAlgebra k M) :
    AddMonoidAlgebra.lift k A M χ x = ev (algebraMap k A) χ x := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single m r => rw [AddMonoidAlgebra.lift_single, ev_single, Algebra.smul_def]

variable (f G) in
/-- The ring of `E_K ∩ D(f i)`. -/
def QK (i : ι) : Type u :=
  Localization.Away (phi (f i)) ⧸
    Ideal.map (algebraMap (AddMonoidAlgebra K M) (Localization.Away (phi (f i))))
      (Ideal.span (phi '' (G i : Set (AddMonoidAlgebra R M))))

noncomputable instance (i : ι) : CommRing (QK f G i) := by unfold QK; infer_instance
noncomputable instance (i : ι) : Algebra K (QK f G i) := by unfold QK; infer_instance

variable (f G) in
/-- `K[M] → Γ(E_K ∩ D(f i))`. -/
noncomputable def qkA (i : ι) : AddMonoidAlgebra K M →ₐ[K] QK f G i :=
  (Ideal.Quotient.mkₐ K _).comp
    (IsScalarTower.toAlgHom K (AddMonoidAlgebra K M) (Localization.Away (phi (f i))))

lemma qkA_eq_zero (i : ι) (x : AddMonoidAlgebra K M) :
    qkA f G i x = 0 ↔ ∃ n : ℕ, phi (f i) ^ n * x ∈
      Ideal.span (phi '' (G i : Set (AddMonoidAlgebra R M))) := by
  have e : qkA f G i x = 0 ↔ algebraMap (AddMonoidAlgebra K M) (Localization.Away (phi (f i))) x ∈
      Ideal.map (algebraMap (AddMonoidAlgebra K M) (Localization.Away (phi (f i))))
        (Ideal.span (phi '' (G i : Set (AddMonoidAlgebra R M)))) :=
    Ideal.Quotient.eq_zero_iff_mem
  rw [e, IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers (phi (f i)))]
  constructor
  · rintro ⟨_, ⟨n, rfl⟩, h⟩; exact ⟨n, h⟩
  · rintro ⟨n, h⟩; exact ⟨_, ⟨n, rfl⟩, h⟩

lemma qkA_f_isUnit (i : ι) : IsUnit (qkA f G i (phi (f i))) := by
  have h : IsUnit (algebraMap (AddMonoidAlgebra K M) (Localization.Away (phi (f i))) (phi (f i))) :=
    IsLocalization.Away.algebraMap_isUnit _
  exact h.map (Ideal.Quotient.mk _)

lemma qkA_G (i : ι) {x : AddMonoidAlgebra R M} (hx : x ∈ G i) : qkA f G i (phi x) = 0 :=
  (qkA_eq_zero i _).2 ⟨0, by
    rw [pow_zero, one_mul]; exact Ideal.subset_span ⟨x, hx, rfl⟩⟩

variable (f G) in
/-- The ideal of the closure of `E_K` in `D(M)_K`. -/
noncomputable def Ik : Ideal (AddMonoidAlgebra K M) :=
  ⨅ i, RingHom.ker (qkA f G i)

lemma mem_Ik {x : AddMonoidAlgebra K M} : x ∈ Ik f G ↔ ∀ i, qkA f G i x = 0 := by
  simp [Ik, Ideal.mem_iInf, RingHom.mem_ker]

/-- A point of `E` kills the ideal of the closure. -/
lemma kills_of_fix {A : Type u} [CommRing A] (ρ : K →+* A) (χ : Multiplicative M →* A)
    (h : FixP f G (ρ.comp (algebraMap R K)) χ) {x : AddMonoidAlgebra K M} (hx : x ∈ Ik f G) :
    ev ρ χ x = 0 := by
  classical
  have hk : ∀ k, ∃ N : ℕ, ev ρ χ (phi (f k)) ^ N * ev ρ χ x = 0 := by
    intro k
    obtain ⟨n, hn⟩ := (qkA_eq_zero k x).1 (mem_Ik.1 hx k)
    have hspan : ∀ y ∈ Ideal.span (phi '' (G k : Set (AddMonoidAlgebra R M))),
        ∃ m : ℕ, ev ρ χ (phi (f k)) ^ m * ev ρ χ y = 0 := by
      intro y hy
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨z, hz, rfl⟩
        obtain ⟨m, hm⟩ := h.2 k z hz
        refine ⟨m, ?_⟩
        rwa [ev_phi, ev_phi]
      · exact ⟨0, by simp⟩
      · rintro a b - - ⟨m, hm⟩ ⟨m', hm'⟩
        refine ⟨m + m', ?_⟩
        rw [map_add, mul_add, pow_add, mul_comm (_ ^ m) (_ ^ m'), mul_assoc, hm, mul_zero,
          mul_comm (_ ^ m') (_ ^ m), mul_assoc, hm', mul_zero, add_zero]
      · rintro c a - ⟨m, hm⟩
        refine ⟨m, ?_⟩
        rw [smul_eq_mul, map_mul, mul_left_comm, hm, mul_zero]
    obtain ⟨m, hm⟩ := hspan _ hn
    refine ⟨m + n, ?_⟩
    rw [map_mul, map_pow] at hm
    rw [pow_add, mul_assoc]
    exact hm
  choose N hN using hk
  let N₀ : ℕ := Finset.univ.sup N
  have hN₀ : ∀ k, ev ρ χ (phi (f k)) ^ N₀ * ev ρ χ x = 0 := by
    intro k
    have hle : N k ≤ N₀ := Finset.le_sup (Finset.mem_univ k)
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    rw [hd, pow_add, mul_right_comm, hN k, zero_mul]
  have htop : Ideal.span ((fun y => y ^ N₀) '' Set.range fun k => ev ρ χ (phi (f k))) = ⊤ := by
    apply Ideal.span_pow_eq_top
    rw [← h.1]
    congr 1
    ext y
    simp [ev_phi]
  have hall : ∀ y ∈ Ideal.span ((fun y => y ^ N₀) '' Set.range fun k => ev ρ χ (phi (f k))),
      y * ev ρ χ x = 0 := by
    intro y hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      exact hN₀ k
    · simp
    · rintro a b - - ha hb
      rw [add_mul, ha, hb, add_zero]
    · rintro c a - ha
      rw [smul_eq_mul, mul_assoc, ha, mul_zero]
  simpa using hall 1 (htop ▸ Submodule.mem_top)

/-- `FixP` on a locally closed test ring, from one chart `f i`. -/
lemma fix_lc_of (hT : Tests f G) (a : Ideal (SS R M)) (b : SS R M) (χ : Multiplicative M →* SS R M)
    (i : ι) (c : SS R M) (hb : b = ev cS χ (f i) * c) (hG : ∀ x ∈ G i, ev cS χ x ∈ a) :
    FixP f G ((lcMap a b).comp cS) ((rm (lcMap a b)).comp χ) := by
  refine hT.hs a b χ i ?_ fun x hx => ?_
  · rw [← map_ev]
    have h0 := lcMap_b_isUnit a b
    have e : lcMap a b b = lcMap a b (ev cS χ (f i)) * lcMap a b c := by rw [← map_mul, ← hb]
    rw [e] at h0
    exact isUnit_of_mul_isUnit_left h0
  · rw [← map_ev]
    exact lcMap_eq_zero b (hG x hx)

/-- The product of two points of `E`, each in a chart. -/
lemma fix_pair_core (hT : Tests f G) {T : Type u} [CommRing T] (θ : SS R M →+* T)
    (i j : ι) (a : Ideal (SS R M)) (b c₁ c₂ : SS R M) (hb₁ : b = ev cS g₀ (f i) * c₁)
    (hb₂ : b = ev cS h₀ (f j) * c₂) (hG₁ : ∀ x ∈ G i, ev cS g₀ x ∈ a) (hG₂ : ∀ x ∈ G j, ev cS h₀ x ∈ a)
    (ha : ∀ x ∈ a, θ x = 0) (hb : IsUnit (θ b)) :
    FixP f G (θ.comp cS) ((rm θ).comp (g₀ * h₀)) :=
  fix_of_lc θ ha hb (hT.hmul a b g₀ h₀ (fix_lc_of hT a b g₀ i c₁ hb₁ hG₁) (fix_lc_of hT a b h₀ j c₂ hb₂ hG₂))

/-- The product of two points of `E`, each in a chart. -/
lemma fix_pair (hT : Tests f G) {T : Type u} [CommRing T] (ρ : R →+* T) (ul ur : Multiplicative M →* T)
    (i j : ι) (hul : IsUnit (ev ρ ul (f i))) (hur : IsUnit (ev ρ ur (f j)))
    (hGl : ∀ x ∈ G i, ev ρ ul x = 0) (hGr : ∀ x ∈ G j, ev ρ ur x = 0) :
    FixP f G ρ (ul * ur) := by
  classical
  have tc : (pairMap ρ ul ur).comp (cS (R := R) (M := M)) = ρ := pairMap_cS ρ ul ur
  have tg : (rm (pairMap ρ ul ur)).comp (g₀ (R := R) (M := M)) = ul := pairMap_g₀ ρ ul ur
  have th : (rm (pairMap ρ ul ur)).comp (h₀ (R := R) (M := M)) = ur := pairMap_h₀ ρ ul ur
  have θg : ∀ x, pairMap ρ ul ur (ev (cS (R := R) (M := M)) (g₀ (R := R) (M := M)) x) = ev ρ ul x := fun x => by
    rw [map_ev, tc]; exact congrArg (fun k => ev ρ k x) tg
  have θh : ∀ x, pairMap ρ ul ur (ev (cS (R := R) (M := M)) (h₀ (R := R) (M := M)) x) = ev ρ ur x := fun x => by
    rw [map_ev, tc]; exact congrArg (fun k => ev ρ k x) th
  have ha : ∀ x ∈ Ideal.span
      ((fun x => ev (cS (R := R) (M := M)) (g₀ (R := R) (M := M)) x) '' (G i : Set (AddMonoidAlgebra R M)) ∪ (fun x => ev (cS (R := R) (M := M)) (h₀ (R := R) (M := M)) x) '' (G j : Set (AddMonoidAlgebra R M))),
      pairMap ρ ul ur x = 0 := by
    have : Ideal.span
      ((fun x => ev (cS (R := R) (M := M)) (g₀ (R := R) (M := M)) x) '' (G i : Set (AddMonoidAlgebra R M)) ∪ (fun x => ev (cS (R := R) (M := M)) (h₀ (R := R) (M := M)) x) '' (G j : Set (AddMonoidAlgebra R M))) ≤
        RingHom.ker (pairMap ρ ul ur) := by
      refine Ideal.span_le.2 ?_
      rintro _ (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
      · change pairMap ρ ul ur (ev (cS (R := R) (M := M)) (g₀ (R := R) (M := M)) x) = 0
        rw [θg, hGl x hx]
      · change pairMap ρ ul ur (ev (cS (R := R) (M := M)) (h₀ (R := R) (M := M)) x) = 0
        rw [θh, hGr x hx]
    exact fun x hx => this hx
  have hb : IsUnit (pairMap ρ ul ur (ev (cS (R := R) (M := M)) (g₀ (R := R) (M := M)) (f i) * ev (cS (R := R) (M := M)) (h₀ (R := R) (M := M)) (f j))) := by
    rw [map_mul, θg, θh]
    exact hul.mul hur
  have e2 : (rm (pairMap ρ ul ur)).comp (g₀ * h₀) = ul * ur := by
    refine MonoidHom.ext fun m => ?_
    have e3 := congrArg (fun k : Multiplicative M →* T => k m) tg
    have e4 := congrArg (fun k : Multiplicative M →* T => k m) th
    simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, map_mul] at e3 e4 ⊢
    rw [e3, e4]
  have hG1 : ∀ x ∈ G i, ev (cS (R := R) (M := M)) (g₀ (R := R) (M := M)) x ∈ Ideal.span
      ((fun x => ev (cS (R := R) (M := M)) (g₀ (R := R) (M := M)) x) '' (G i : Set (AddMonoidAlgebra R M)) ∪ (fun x => ev (cS (R := R) (M := M)) (h₀ (R := R) (M := M)) x) '' (G j : Set (AddMonoidAlgebra R M))) := fun x hx =>
    Ideal.subset_span (Set.mem_union_left _ (Set.mem_image_of_mem _ (Finset.mem_coe.2 hx)))
  have hG2 : ∀ x ∈ G j, ev (cS (R := R) (M := M)) (h₀ (R := R) (M := M)) x ∈ Ideal.span
      ((fun x => ev (cS (R := R) (M := M)) (g₀ (R := R) (M := M)) x) '' (G i : Set (AddMonoidAlgebra R M)) ∪ (fun x => ev (cS (R := R) (M := M)) (h₀ (R := R) (M := M)) x) '' (G j : Set (AddMonoidAlgebra R M))) := fun x hx =>
    Ideal.subset_span (Set.mem_union_right _ (Set.mem_image_of_mem _ (Finset.mem_coe.2 hx)))
  have h3 : FixP f G ((pairMap ρ ul ur).comp cS) ((rm (pairMap ρ ul ur)).comp (g₀ * h₀)) := by
    generalize Ideal.span
      ((fun x => ev (cS (R := R) (M := M)) (g₀ (R := R) (M := M)) x) '' (G i : Set (AddMonoidAlgebra R M)) ∪ (fun x => ev (cS (R := R) (M := M)) (h₀ (R := R) (M := M)) x) '' (G j : Set (AddMonoidAlgebra R M))) = a at ha hG1 hG2
    obtain ⟨b, hbd⟩ : ∃ b, b = ev (cS (R := R) (M := M)) (g₀ (R := R) (M := M)) (f i) * ev (cS (R := R) (M := M)) (h₀ (R := R) (M := M)) (f j) := ⟨_, rfl⟩
    rw [← hbd] at hb
    generalize pairMap ρ ul ur = θ at ha hb
    exact fix_pair_core hT θ i j a b _ (ev (cS (R := R) (M := M)) (g₀ (R := R) (M := M)) (f i)) hbd (hbd.trans (mul_comm _ _)) hG1 hG2 ha hb
  rw [tc, e2] at h3
  exact h3

section Generic

variable {k : Type u} [Field k] {κ : Type u} [Finite κ] {Q : κ → Type u} [∀ i, CommRing (Q i)]
  [∀ i, Algebra k (Q i)]

/-- The product law on the closure, from the product law on the charts. -/
theorem hmul_generic (q : ∀ i, AddMonoidAlgebra k M →ₐ[k] Q i)
    (hfix : ∀ i j, ∀ x ∈ (⨅ i, RingHom.ker (q i) : Ideal (AddMonoidAlgebra k M)),
      ev (algebraMap k (Q i ⊗[k] Q j))
        ((rm (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := Q i) (B := Q j)).toRingHom).comp
            ((rm (q i).toRingHom).comp (AddMonoidAlgebra.of k M)) *
          (rm (Algebra.TensorProduct.includeRight (R := k) (A := Q i) (B := Q j)).toRingHom).comp
            ((rm (q j).toRingHom).comp (AddMonoidAlgebra.of k M))) x = 0)
    (A : Type u) [CommRing A] [Algebra k A] (g h : Multiplicative M →* A)
    (hg : ∀ x ∈ (⨅ i, RingHom.ker (q i) : Ideal (AddMonoidAlgebra k M)),
      AddMonoidAlgebra.lift k A M g x = 0)
    (hh : ∀ x ∈ (⨅ i, RingHom.ker (q i) : Ideal (AddMonoidAlgebra k M)),
      AddMonoidAlgebra.lift k A M h x = 0) :
    ∀ x ∈ (⨅ i, RingHom.ker (q i) : Ideal (AddMonoidAlgebra k M)),
      AddMonoidAlgebra.lift k A M (g * h) x = 0 := by
  classical
  intro x hx
  let I : Ideal (AddMonoidAlgebra k M) := ⨅ i, RingHom.ker (q i)
  let Ak := AddMonoidAlgebra k M ⧸ I
  let c : Multiplicative M →* Ak :=
    (rm (Ideal.Quotient.mkₐ k I).toRingHom).comp (AddMonoidAlgebra.of k M)
  let il : Ak →ₐ[k] Ak ⊗[k] Ak := Algebra.TensorProduct.includeLeft
  let ir : Ak →ₐ[k] Ak ⊗[k] Ak := Algebra.TensorProduct.includeRight
  let gl : Multiplicative M →* Ak ⊗[k] Ak := (rm il.toRingHom).comp c
  let gr : Multiplicative M →* Ak ⊗[k] Ak := (rm ir.toRingHom).comp c
  let D : Ak ⊗[k] Ak := AddMonoidAlgebra.lift k _ M (gl * gr) x
  have memI : ∀ y, y ∈ I ↔ ∀ i, q i y = 0 := fun y => by
    simp [I, Ideal.mem_iInf, RingHom.mem_ker]
  let qb : ∀ i, Ak →ₐ[k] Q i := fun i => Ideal.Quotient.liftₐ I (q i)
    (fun y hy => (memI y).1 hy i)
  have hD : D = 0 := by
    refine tensor_joint (fun i => (qb i).toLinearMap) ?_ D fun i j => ?_
    · intro y hy
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact Ideal.Quotient.eq_zero_iff_mem.2 ((memI y).2 fun i => hy i)
    · have e : ∀ z, TensorProduct.map (qb i).toLinearMap (qb j).toLinearMap
          (AddMonoidAlgebra.lift k _ M (gl * gr) z) =
          ev (algebraMap k (Q i ⊗[k] Q j))
            ((rm (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := Q i) (B := Q j)).toRingHom).comp
              ((rm (q i).toRingHom).comp (AddMonoidAlgebra.of k M)) *
            (rm (Algebra.TensorProduct.includeRight (R := k) (A := Q i) (B := Q j)).toRingHom).comp
              ((rm (q j).toRingHom).comp (AddMonoidAlgebra.of k M))) z := by
        intro z
        induction z using AddMonoidAlgebra.induction_linear with
        | zero => simp
        | add z w hz hw => simp only [map_add, hz, hw]
        | single m r =>
          rw [AddMonoidAlgebra.lift_single, ev_single, map_smul, Algebra.smul_def]
          congr 1
          change TensorProduct.map (qb i).toLinearMap (qb j).toLinearMap
            ((Ideal.Quotient.mk I (AddMonoidAlgebra.of k M (Multiplicative.ofAdd m)) ⊗ₜ[k] (1 : Ak)) *
              ((1 : Ak) ⊗ₜ[k] Ideal.Quotient.mk I (AddMonoidAlgebra.of k M (Multiplicative.ofAdd m)))) =
            ((q i (AddMonoidAlgebra.of k M (Multiplicative.ofAdd m)) ⊗ₜ[k] (1 : Q j)) *
              ((1 : Q i) ⊗ₜ[k] q j (AddMonoidAlgebra.of k M (Multiplicative.ofAdd m))))
          rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
            TensorProduct.map_tmul]
          simp only [mul_one, one_mul]
          rfl
      change TensorProduct.map (qb i).toLinearMap (qb j).toLinearMap
        (AddMonoidAlgebra.lift k _ M (gl * gr) x) = 0
      rw [e]
      exact hfix i j x hx
  let ĝ : Ak →ₐ[k] A := Ideal.Quotient.liftₐ I (AddMonoidAlgebra.lift k A M g) (fun y hy => hg y hy)
  let ĥ : Ak →ₐ[k] A := Ideal.Quotient.liftₐ I (AddMonoidAlgebra.lift k A M h) (fun y hy => hh y hy)
  let Ψ : Ak ⊗[k] Ak →ₐ[k] A := Algebra.TensorProduct.productMap ĝ ĥ
  have e : ∀ z, Ψ (AddMonoidAlgebra.lift k _ M (gl * gr) z) = AddMonoidAlgebra.lift k A M (g * h) z := by
    intro z
    induction z using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add z w hz hw => simp only [map_add, hz, hw]
    | single m r =>
      rw [AddMonoidAlgebra.lift_single, AddMonoidAlgebra.lift_single, map_smul]
      congr 1
      change Ψ ((Ideal.Quotient.mk I (AddMonoidAlgebra.of k M (Multiplicative.ofAdd m)) ⊗ₜ[k] (1 : Ak)) *
              ((1 : Ak) ⊗ₜ[k] Ideal.Quotient.mk I (AddMonoidAlgebra.of k M (Multiplicative.ofAdd m)))) = _
      rw [map_mul, Algebra.TensorProduct.productMap_apply_tmul, Algebra.TensorProduct.productMap_apply_tmul,
        map_one, map_one, mul_one, one_mul]
      have e1 : ĝ (Ideal.Quotient.mk I (AddMonoidAlgebra.of k M (Multiplicative.ofAdd m))) =
          g (Multiplicative.ofAdd m) := by
        change AddMonoidAlgebra.lift k A M g _ = _
        simp [AddMonoidAlgebra.of_apply, AddMonoidAlgebra.lift_single]
      have e2 : ĥ (Ideal.Quotient.mk I (AddMonoidAlgebra.of k M (Multiplicative.ofAdd m))) =
          h (Multiplicative.ofAdd m) := by
        change AddMonoidAlgebra.lift k A M h _ = _
        simp [AddMonoidAlgebra.of_apply, AddMonoidAlgebra.lift_single]
      rw [e1, e2]
      rfl
  rw [← e, show AddMonoidAlgebra.lift k _ M (gl * gr) x = D from rfl, hD, map_zero]

end Generic

/-- The universal character of `Γ(E_K ∩ D(f i))`. -/
noncomputable def uQ (f : ι → AddMonoidAlgebra R M) (G : ι → Finset (AddMonoidAlgebra R M)) (i : ι) :
    Multiplicative M →* QK f G i :=
  (rm (qkA f G i).toRingHom).comp (AddMonoidAlgebra.of K M)

lemma ev_uQ (i : ι) (y : AddMonoidAlgebra K M) :
    ev (algebraMap K (QK f G i)) (uQ f G i) y = qkA f G i y := by
  have : ev (algebraMap K (QK f G i)) (uQ f G i) = (qkA f G i).toRingHom :=
    ringHom_ext' fun m r => by
      rw [ev_single]
      have e : AddMonoidAlgebra.single m r = algebraMap K (AddMonoidAlgebra K M) r *
          AddMonoidAlgebra.of K M (Multiplicative.ofAdd m) := by
        simp [AddMonoidAlgebra.of_apply, AddMonoidAlgebra.single_mul_single,
          AddMonoidAlgebra.coe_algebraMap]
      rw [e, map_mul]
      congr 1
  exact congrArg (fun k => k y) this

lemma ev_uQ_map {T : Type u} [CommRing T] [Algebra K T] (i : ι) (il : QK f G i →ₐ[K] T)
    (x : AddMonoidAlgebra R M) :
    ev ((algebraMap K T).comp (algebraMap R K)) ((rm il.toRingHom).comp (uQ f G i)) x =
      il (qkA f G i (phi x)) := by
  have e := map_ev il.toRingHom (algebraMap K (QK f G i)) (uQ f G i) (phi x)
  rw [ev_uQ] at e
  have h : il.toRingHom.comp (algebraMap K (QK f G i)) = algebraMap K T := il.comp_algebraMap
  rw [h, ev_phi] at e
  exact e.symm

/-- **The closure of `E_K` is closed under products.** -/
theorem hmul_Ik (hT : Tests f G) (A : Type u) [CommRing A] [Algebra K A] (g h : Multiplicative M →* A)
    (hg : ∀ x ∈ Ik f G, AddMonoidAlgebra.lift K A M g x = 0)
    (hh : ∀ x ∈ Ik f G, AddMonoidAlgebra.lift K A M h x = 0) :
    ∀ x ∈ Ik f G, AddMonoidAlgebra.lift K A M (g * h) x = 0 := by
  refine hmul_generic (qkA f G) (fun i j x hx => ?_) A g h hg hh
  refine kills_of_fix (f := f) (G := G) _ _ ?_ hx
  have el := fun x => ev_uQ_map (f := f) (G := G) (T := QK f G i ⊗[K] QK f G j) i
    (Algebra.TensorProduct.includeLeft (R := K) (S := K) (A := QK f G i) (B := QK f G j)) x
  have er := fun x => ev_uQ_map (f := f) (G := G) (T := QK f G i ⊗[K] QK f G j) j
    (Algebra.TensorProduct.includeRight (R := K) (A := QK f G i) (B := QK f G j)) x
  refine fix_pair hT _ _ _ i j ?_ ?_ (fun x hx => ?_) (fun x hx => ?_)
  · exact (el _).symm ▸ (qkA_f_isUnit i).map _
  · exact (er _).symm ▸ (qkA_f_isUnit j).map _
  · exact (el x).trans (by rw [qkA_G i hx, map_zero])
  · exact (er x).trans (by rw [qkA_G j hx, map_zero])

/-- **The closure of `E_K` is `D(M/Z)_K`.** -/
theorem exists_Z_field [AddMonoid.FG M] (hT : Tests f G) :
    ∃ Z : AddSubgroup M, ∀ (A : Type u) [CommRing A] [Algebra K A] (h : Multiplicative M →* A),
      (∀ x ∈ Ik f G, AddMonoidAlgebra.lift K A M h x = 0) ↔
        ∀ z ∈ Z, h (Multiplicative.ofAdd z) = 1 := by
  have h1 : ∀ x ∈ Ik f G, AddMonoidAlgebra.lift K (FractionRing K) M 1 x = 0 := by
    intro x hx
    rw [lift_eq_ev]
    refine kills_of_fix (f := f) (G := G) _ _ ?_ hx
    have := hT.hone.map ((algebraMap K (FractionRing K)).comp (algebraMap R K))
    rw [RingHom.comp_id, MonoidHom.comp_one] at this
    exact this
  obtain ⟨s, hs, Z, hZ⟩ := exists_stab_subgroup (R := K) (M := M) (Ik f G) h1
    (fun A _ _ g h hg hh => hmul_Ik hT A g h hg hh)
  refine ⟨Z, fun A _ _ h => hZ A ?_ h⟩
  exact (isUnit_iff_ne_zero.2 hs).map _

end AlgMag.ChartQSStabGen
