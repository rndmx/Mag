/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartQSStabGenTrans

/-!
# The generic stabilizer for quasi-separated `X`: the ring statement

`exists_generic_ring`: a locally closed subgroup functor of `D(M)_R`, `R` a domain, is `D(M/Z)` over a
nonempty open of `Spec R`.
-/

open TensorProduct AlgMag.ChartStratum

universe u

namespace AlgMag.ChartQSStabGen

section Quot

variable {M : Type u} [AddCommGroup M] (Z : AddSubgroup M)

/-- `M → M/Z` on characters. -/
def qm : Multiplicative M →* Multiplicative (M ⧸ Z) :=
  AddMonoidHom.toMultiplicative (QuotientAddGroup.mk' Z)

/-- A character trivial on `Z` descends to `M/Z`. -/
noncomputable def descChar {A : Type u} [CommRing A] (χ : Multiplicative M →* A)
    (h : ∀ z ∈ Z, χ (Multiplicative.ofAdd z) = 1) : Multiplicative (M ⧸ Z) →* A :=
  let Λ : M →+ Additive A :=
    { toFun := fun m => Additive.ofMul (χ (Multiplicative.ofAdd m))
      map_zero' := by simp
      map_add' := fun a b => by simp [ofAdd_add] }
  let μ : M ⧸ Z →+ Additive A := QuotientAddGroup.lift Z Λ (fun z hz => by
    change Additive.ofMul (χ (Multiplicative.ofAdd z)) = 0
    rw [h z hz]; rfl)
  { toFun := fun x => Additive.toMul (μ (Multiplicative.toAdd x))
    map_one' := by simp
    map_mul' := fun a b => by simp }

lemma descChar_comp {A : Type u} [CommRing A] (χ : Multiplicative M →* A)
    (h : ∀ z ∈ Z, χ (Multiplicative.ofAdd z) = 1) : (descChar Z χ h).comp (qm Z) = χ := by
  refine MonoidHom.ext fun m => ?_
  rfl

lemma qm_trivial {A : Type u} [CommRing A] (χ : Multiplicative (M ⧸ Z) →* A) :
    ∀ z ∈ Z, (χ.comp (qm Z)) (Multiplicative.ofAdd z) = 1 := fun z hz => by
  have : qm Z (Multiplicative.ofAdd z) = 1 := by
    change Multiplicative.ofAdd (QuotientAddGroup.mk' Z z) = 1
    have e0 : QuotientAddGroup.mk' Z z = 0 := (QuotientAddGroup.eq_zero_iff z).2 hz
    rw [e0]
    rfl
  rw [MonoidHom.comp_apply, this, map_one]

variable (k : Type u) [CommRing k]

/-- `k[M] → k[M/Z]`. -/
noncomputable def mkN : AddMonoidAlgebra k M →+* AddMonoidAlgebra k (M ⧸ Z) :=
  ev (algebraMap k _) ((AddMonoidAlgebra.of k (M ⧸ Z)).comp (qm Z))

lemma mkN_single (m : M) (r : k) :
    mkN Z k (AddMonoidAlgebra.single m r) = AddMonoidAlgebra.single (QuotientAddGroup.mk' Z m) r := by
  simp only [mkN, ev_single]
  change AddMonoidAlgebra.single 0 r * AddMonoidAlgebra.single (QuotientAddGroup.mk' Z m) 1 = _
  rw [AddMonoidAlgebra.single_mul_single, zero_add, mul_one]

lemma ev_mkN {A : Type u} [CommRing A] (ρ : k →+* A) (χ : Multiplicative (M ⧸ Z) →* A)
    (x : AddMonoidAlgebra k M) : ev ρ χ (mkN Z k x) = ev ρ (χ.comp (qm Z)) x := by
  have : (ev ρ χ).comp (mkN Z k) = ev ρ (χ.comp (qm Z)) := ringHom_ext' fun m r => by
    rw [RingHom.comp_apply, mkN_single, ev_single, ev_single]
    rfl
  exact congrArg (fun e => e x) this

lemma mkN_surjective : Function.Surjective (mkN Z k) := by
  intro y
  induction y using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add a b ha hb =>
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    exact ⟨a' + b', map_add _ _ _⟩
  | single n r =>
    obtain ⟨m, rfl⟩ := QuotientAddGroup.mk'_surjective Z n
    exact ⟨_, mkN_single Z k m r⟩

end Quot

variable {R : Type u} [CommRing R] [IsDomain R] {M : Type u} [AddCommGroup M]
variable {ι : Type u} [Fintype ι] {f : ι → AddMonoidAlgebra R M}
  {G : ι → Finset (AddMonoidAlgebra R M)}

local notation "K" => FractionRing R

/-- `FixP` from one chart. -/
lemma fix_one_core (hT : Tests f G) {T : Type u} [CommRing T] (θ : SS R M →+* T) (i : ι)
    (a : Ideal (SS R M)) (b c : SS R M) (χ : Multiplicative M →* SS R M)
    (hb : b = ev cS χ (f i) * c) (hG : ∀ x ∈ G i, ev cS χ x ∈ a)
    (ha : ∀ x ∈ a, θ x = 0) (hbu : IsUnit (θ b)) :
    FixP f G (θ.comp cS) ((rm θ).comp χ) :=
  fix_of_lc θ ha hbu (fix_lc_of hT a b χ i c hb hG)

/-- `FixP` from one chart. -/
lemma fix_one (hT : Tests f G) {T : Type u} [CommRing T] (ρ : R →+* T) (u : Multiplicative M →* T)
    (i : ι) (hu : IsUnit (ev ρ u (f i))) (hG : ∀ x ∈ G i, ev ρ u x = 0) : FixP f G ρ u := by
  have tc : (pairMap ρ u u).comp (cS (R := R) (M := M)) = ρ := pairMap_cS ρ u u
  have tg : (rm (pairMap ρ u u)).comp (g₀ (R := R) (M := M)) = u := pairMap_g₀ ρ u u
  have θg : ∀ x, pairMap ρ u u (ev (cS (R := R) (M := M)) (g₀ (R := R) (M := M)) x) = ev ρ u x := fun x => by
    rw [map_ev, tc]; exact congrArg (fun k => ev ρ k x) tg
  have h3 := fix_one_core (f := f) (G := G) hT (pairMap ρ u u) i (RingHom.ker (pairMap ρ u u))
    (ev (cS (R := R) (M := M)) (g₀ (R := R) (M := M)) (f i)) 1 g₀ (mul_one _).symm
    (fun x hx => by rw [RingHom.mem_ker, θg, hG x hx]) (fun x hx => hx) (by rw [θg]; exact hu)
  rw [tc, tg] at h3
  exact h3

/-- Division in `E`, from charts. -/
lemma fix_div_core (hT : Tests f G) {T : Type u} [CommRing T] (θ : SS R M →+* T) (i j : ι)
    (a : Ideal (SS R M)) (b c₁ c₂ : SS R M) (χ₁ χ₂ : Multiplicative M →* SS R M)
    (hb₁ : b = ev cS χ₂ (f i) * c₁) (hb₂ : b = ev cS (χ₁ * χ₂) (f j) * c₂)
    (hG₁ : ∀ x ∈ G i, ev cS χ₂ x ∈ a) (hG₂ : ∀ x ∈ G j, ev cS (χ₁ * χ₂) x ∈ a)
    (ha : ∀ x ∈ a, θ x = 0) (hbu : IsUnit (θ b)) :
    FixP f G (θ.comp cS) ((rm θ).comp χ₁) :=
  fix_of_lc θ ha hbu (hT.hdiv a b χ₁ χ₂ (fix_lc_of hT a b χ₂ i c₁ hb₁ hG₁)
    (fix_lc_of hT a b (χ₁ * χ₂) j c₂ hb₂ hG₂))

/-- Division in `E`, from charts. -/
lemma fix_div (hT : Tests f G) {T : Type u} [CommRing T] (ρ : R →+* T) (χ₁ χ₂ : Multiplicative M →* T)
    (i j : ι) (hu₂ : IsUnit (ev ρ χ₂ (f i))) (hu₁₂ : IsUnit (ev ρ (χ₁ * χ₂) (f j)))
    (hG₂ : ∀ x ∈ G i, ev ρ χ₂ x = 0) (hG₁₂ : ∀ x ∈ G j, ev ρ (χ₁ * χ₂) x = 0) : FixP f G ρ χ₁ := by
  have tc : (pairMap ρ χ₁ χ₂).comp (cS (R := R) (M := M)) = ρ := pairMap_cS ρ χ₁ χ₂
  have tg : (rm (pairMap ρ χ₁ χ₂)).comp (g₀ (R := R) (M := M)) = χ₁ := pairMap_g₀ ρ χ₁ χ₂
  have th : (rm (pairMap ρ χ₁ χ₂)).comp (h₀ (R := R) (M := M)) = χ₂ := pairMap_h₀ ρ χ₁ χ₂
  have tgh : (rm (pairMap ρ χ₁ χ₂)).comp ((g₀ (R := R) (M := M)) * h₀) = χ₁ * χ₂ := by
    refine MonoidHom.ext fun m => ?_
    have e3 := congrArg (fun k : Multiplicative M →* T => k m) tg
    have e4 := congrArg (fun k : Multiplicative M →* T => k m) th
    simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, map_mul] at e3 e4 ⊢
    rw [e3, e4]
  have θh : ∀ x, pairMap ρ χ₁ χ₂ (ev (cS (R := R) (M := M)) (h₀ (R := R) (M := M)) x) = ev ρ χ₂ x := fun x => by
    rw [map_ev, tc]; exact congrArg (fun k => ev ρ k x) th
  have θgh : ∀ x, pairMap ρ χ₁ χ₂ (ev (cS (R := R) (M := M)) ((g₀ (R := R) (M := M)) * h₀) x) =
      ev ρ (χ₁ * χ₂) x := fun x => by
    rw [map_ev, tc]; exact congrArg (fun k => ev ρ k x) tgh
  have h3 := fix_div_core (f := f) (G := G) hT (pairMap ρ χ₁ χ₂) i j (RingHom.ker (pairMap ρ χ₁ χ₂))
    (ev (cS (R := R) (M := M)) (h₀ (R := R) (M := M)) (f i) *
      ev (cS (R := R) (M := M)) ((g₀ (R := R) (M := M)) * h₀) (f j)) _
    (ev (cS (R := R) (M := M)) (h₀ (R := R) (M := M)) (f i)) g₀ h₀ rfl (mul_comm _ _)
    (fun x hx => by rw [RingHom.mem_ker, θh, hG₂ x hx])
    (fun x hx => by rw [RingHom.mem_ker, θgh, hG₁₂ x hx]) (fun x hx => hx)
    (by rw [map_mul, θh, θgh]; exact hu₂.mul hu₁₂)
  rw [tc, tg] at h3
  exact h3

/-- A section vanishing locally on the `D(f k)` vanishes at a point of `E`. -/
lemma eq_zero_of_fix {A : Type u} [CommRing A] {ρ : R →+* A} {χ : Multiplicative M →* A}
    (h : FixP f G ρ χ) (e : A) (he : ∀ k, ∃ N : ℕ, ev ρ χ (f k) ^ N * e = 0) : e = 0 := by
  classical
  choose N hN using he
  let N₀ : ℕ := Finset.univ.sup N
  have hN₀ : ∀ k, ev ρ χ (f k) ^ N₀ * e = 0 := by
    intro k
    have hle : N k ≤ N₀ := Finset.le_sup (Finset.mem_univ k)
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    rw [hd, pow_add, mul_right_comm, hN k, zero_mul]
  have htop : Ideal.span ((fun y => y ^ N₀) '' Set.range fun k => ev ρ χ (f k)) = ⊤ :=
    Ideal.span_pow_eq_top _ h.1 _
  have hall : ∀ y ∈ Ideal.span ((fun y => y ^ N₀) '' Set.range fun k => ev ρ χ (f k)), y * e = 0 := by
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

/-- Elements of the ideal of a chart vanish locally at a point of `E`. -/
lemma pow_mul_span {A : Type u} [CommRing A] {ρ : R →+* A} {χ : Multiplicative M →* A}
    (h : FixP f G ρ χ) (k : ι) (y : AddMonoidAlgebra R M)
    (hy : y ∈ Ideal.span (G k : Set (AddMonoidAlgebra R M))) :
    ∃ m : ℕ, ev ρ χ (f k) ^ m * ev ρ χ y = 0 := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
  · intro z hz
    exact h.2 k z hz
  · exact ⟨0, by simp⟩
  · rintro a b - - ⟨m, hm⟩ ⟨m', hm'⟩
    refine ⟨m + m', ?_⟩
    rw [map_add, mul_add, pow_add, mul_comm (_ ^ m) (_ ^ m'), mul_assoc, hm, mul_zero,
      mul_comm (_ ^ m') (_ ^ m), mul_assoc, hm', mul_zero, add_zero]
  · rintro c a - ⟨m, hm⟩
    refine ⟨m, ?_⟩
    rw [smul_eq_mul, map_mul, mul_left_comm, hm, mul_zero]

/-- The closure is `D(M/Z)` in terms of `Z`. -/
def HZ (f : ι → AddMonoidAlgebra R M) (G : ι → Finset (AddMonoidAlgebra R M)) (Z : AddSubgroup M) : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra K A] (h : Multiplicative M →* A),
    (∀ x ∈ Ik f G, AddMonoidAlgebra.lift K A M h x = 0) ↔ ∀ z ∈ Z, h (Multiplicative.ofAdd z) = 1

lemma mem_Ik_iff {Z : AddSubgroup M} (hZ : HZ f G Z) (x : AddMonoidAlgebra K M) :
    x ∈ Ik f G ↔ mkN Z K x = 0 := by
  constructor
  · intro hx
    have h := (hZ (AddMonoidAlgebra K (M ⧸ Z)) ((AddMonoidAlgebra.of K (M ⧸ Z)).comp (qm Z))).2
      (qm_trivial Z _) x hx
    rw [lift_eq_ev] at h
    exact h
  · intro hx
    let A := AddMonoidAlgebra K M ⧸ Ik f G
    let c : Multiplicative M →* A :=
      (rm (Ideal.Quotient.mkₐ K (Ik f G)).toRingHom).comp (AddMonoidAlgebra.of K M)
    have hq : ∀ y, ev (algebraMap K A) c y = Ideal.Quotient.mk (Ik f G) y := fun y => by
      have : ev (algebraMap K A) c = Ideal.Quotient.mk (Ik f G) := ringHom_ext' fun m r => by
        rw [ev_single, single_eq_smul_of, Algebra.smul_def, map_mul]
        rfl
      exact congrArg (fun e => e y) this
    have hc : ∀ z ∈ Z, c (Multiplicative.ofAdd z) = 1 := (hZ A c).1 fun y hy => by
      rw [lift_eq_ev, hq]
      exact Ideal.Quotient.eq_zero_iff_mem.2 hy
    have e := ev_mkN Z K (algebraMap K A) (descChar Z c hc) x
    rw [hx, map_zero, descChar_comp, hq] at e
    exact Ideal.Quotient.eq_zero_iff_mem.1 e.symm

lemma ev_uQ_phi (i : ι) (x : AddMonoidAlgebra R M) :
    ev ((algebraMap K (QK f G i)).comp (algebraMap R K)) (uQ f G i) x = qkA f G i (phi x) := by
  rw [← ev_phi, ev_uQ]

/-- `E_K` has its generators in the closure, locally. -/
lemma mkN_G (hT : Tests f G) {Z : AddSubgroup M} (hZ : HZ f G Z) (i : ι) {x : AddMonoidAlgebra R M}
    (hx : x ∈ G i) : ∃ n : ℕ, mkN Z K (phi (f i)) ^ n * mkN Z K (phi x) = 0 := by
  classical
  have hk : ∀ k, ∃ n : ℕ, qkA f G k (phi (f i) ^ n * phi x) = 0 := by
    intro k
    have hF : FixP f G ((algebraMap K (QK f G k)).comp (algebraMap R K)) (uQ f G k) :=
      fix_one hT _ _ k (by rw [ev_uQ_phi]; exact qkA_f_isUnit k) fun y hy => by
        rw [ev_uQ_phi, qkA_G k hy]
    obtain ⟨n, hn⟩ := hF.2 i x hx
    refine ⟨n, ?_⟩
    rw [ev_uQ_phi, ev_uQ_phi] at hn
    rw [map_mul, map_pow, hn]
  choose n hn using hk
  refine ⟨Finset.univ.sup n, ?_⟩
  rw [← map_pow, ← map_mul, ← mem_Ik_iff hZ, mem_Ik]
  intro k
  have hle : n k ≤ Finset.univ.sup n := Finset.le_sup (Finset.mem_univ k)
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  rw [hd, pow_add, mul_right_comm, mul_comm, map_mul, hn k, mul_zero]

/-- The ideal of the complement of `E_K` in `D(M/Z)_K`. -/
noncomputable def JJ (f : ι → AddMonoidAlgebra R M) (Z : AddSubgroup M) :
    Ideal (AddMonoidAlgebra K (M ⧸ Z)) :=
  Ideal.span (Set.range fun i => mkN Z K (phi (f i)))

variable [AddMonoid.FG M]

/-- `E_K` is schematically dense in `D(M/Z)_K`: `J` holds a nonzerodivisor. -/
lemma exists_nzd {Z : AddSubgroup M} (hZ : HZ f G Z) :
    ∃ F ∈ JJ f Z, F ∈ nonZeroDivisors (AddMonoidAlgebra K (M ⧸ Z)) := by
  classical
  by_contra hne
  push Not at hne
  haveI : AddGroup.FG M := AddGroup.fg_iff_addMonoid_fg.mpr inferInstance
  haveI : AddMonoid.FG (M ⧸ Z) := AddGroup.fg_iff_addMonoid_fg.mp inferInstance
  haveI : IsNoetherianRing (AddMonoidAlgebra K (M ⧸ Z)) :=
    Algebra.FiniteType.isNoetherianRing K _
  have hd : Disjoint (JJ f Z : Set (AddMonoidAlgebra K (M ⧸ Z)))
      (nonZeroDivisors (AddMonoidAlgebra K (M ⧸ Z)) : Set (AddMonoidAlgebra K (M ⧸ Z))) :=
    Set.disjoint_left.2 fun F hF hF' => hne F hF hF'
  obtain ⟨-, y, hy, hy0⟩ := SetLike.lt_iff_le_and_exists.1
    (Ideal.bot_lt_annihilator_of_disjoint_nonZeroDivisors hd)
  have hy' : ∀ i, y * mkN Z K (phi (f i)) = 0 := fun i => by
    have := Module.mem_annihilator.1 hy ⟨_, Ideal.subset_span ⟨i, rfl⟩⟩
    exact congrArg Subtype.val this
  obtain ⟨ŷ, rfl⟩ := mkN_surjective Z K y
  refine hy0 ((mem_Ik_iff hZ ŷ).1 (mem_Ik.2 fun i => ?_))
  have h1 : ŷ * phi (f i) ∈ Ik f G := (mem_Ik_iff hZ _).2 (by rw [map_mul]; exact hy' i)
  have h2 := mem_Ik.1 h1 i
  rw [map_mul] at h2
  exact (qkA_f_isUnit i).mul_left_eq_zero.1 h2

/-- **The translate argument gives `J = ⊤`**: `E_K` is all of `D(M/Z)_K`. -/
theorem contra_field (hT : Tests f G) {Z : AddSubgroup M} (hZ : HZ f G Z) {L₀ : Type u} [Field L₀]
    [Algebra K L₀] (e : AddMonoidAlgebra K (M ⧸ Z) →ₐ[K] L₀)
    (he : ∀ k, e (mkN Z K (phi (f k))) = 0) : False := by
  classical
  obtain ⟨F, hFJ, hF⟩ := exists_nzd hZ
  let g : Multiplicative (M ⧸ Z) →* L₀ := (rm e.toRingHom).comp (AddMonoidAlgebra.of K (M ⧸ Z))
  obtain ⟨L', hL', ι', y, hy1, hy2⟩ := exists_translate g F hF
  letI := hL'
  let ρK : K →+* L' := ι'.comp (algebraMap K L₀)
  let g' : Multiplicative (M ⧸ Z) →* L' := (rm ι').comp g
  have pick : ∀ (χ : Multiplicative (M ⧸ Z) →* L'), ev ρK χ F ≠ 0 →
      ∃ i, ev ρK χ (mkN Z K (phi (f i))) ≠ 0 := by
    intro χ hχ
    by_contra hall
    push Not at hall
    have : JJ f Z ≤ RingHom.ker (ev ρK χ) := Ideal.span_le.2 (by
      rintro _ ⟨i, rfl⟩
      exact hall i)
    exact hχ (this hFJ)
  obtain ⟨i, hi⟩ := pick y hy1
  obtain ⟨j, hj⟩ := pick (g' * y) hy2
  let ρ : R →+* L' := ρK.comp (algebraMap R K)
  have val : ∀ (χ : Multiplicative (M ⧸ Z) →* L') (x : AddMonoidAlgebra R M),
      ev ρ (χ.comp (qm Z)) x = ev ρK χ (mkN Z K (phi x)) := fun χ x => by
    rw [ev_mkN, ev_phi]
  have vG : ∀ (χ : Multiplicative (M ⧸ Z) →* L') (k : ι), ev ρK χ (mkN Z K (phi (f k))) ≠ 0 →
      ∀ x ∈ G k, ev ρK χ (mkN Z K (phi x)) = 0 := by
    intro χ k hk x hx
    obtain ⟨n, hn⟩ := mkN_G hT hZ k hx
    have := congrArg (ev ρK χ) hn
    rw [map_mul, map_pow, map_zero] at this
    exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero _ hk)
  have hprod : (g'.comp (qm Z)) * (y.comp (qm Z)) = (g' * y).comp (qm Z) := by
    refine MonoidHom.ext fun m => ?_
    rfl
  have h3 : FixP f G ρ (g'.comp (qm Z)) := by
    refine fix_div hT ρ _ (y.comp (qm Z)) i j ?_ ?_ (fun x hx => ?_) (fun x hx => ?_)
    · rw [val]; exact isUnit_iff_ne_zero.2 hi
    · rw [hprod, val]; exact isUnit_iff_ne_zero.2 hj
    · rw [val]; exact vG y i hi x hx
    · rw [hprod, val]; exact vG _ j hj x hx
  have h0 : ∀ k, ev ρ (g'.comp (qm Z)) (f k) = 0 := by
    intro k
    rw [val]
    have : ev ρK g' = ι'.comp e.toRingHom := ringHom_ext' fun m r => by
      rw [ev_single, single_eq_smul_of, RingHom.comp_apply]
      change ι' _ * ι' (e (AddMonoidAlgebra.of K (M ⧸ Z) _)) = ι' (e _)
      rw [← map_mul, map_smul, Algebra.smul_def]
    rw [this, RingHom.comp_apply]
    change ι' (e _) = 0
    rw [he, map_zero]
  have h4 := h3.1
  have h5 : (Set.range fun k => ev ρ (g'.comp (qm Z)) (f k)) ⊆ {0} := by
    rintro _ ⟨k, rfl⟩
    exact h0 k
  have h6 : Ideal.span (Set.range fun k => ev ρ (g'.comp (qm Z)) (f k)) ≤ ⊥ :=
    Ideal.span_le.2 fun y hy => by
      have := h5 hy
      simpa using this
  rw [h4] at h6
  exact top_ne_bot (le_bot_iff.1 h6)

/-- `J = ⊤`. -/
theorem JJ_eq_top (hT : Tests f G) {Z : AddSubgroup M} (hZ : HZ f G Z) : JJ f Z = ⊤ := by
  classical
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  letI : Field (AddMonoidAlgebra K (M ⧸ Z) ⧸ m) := Ideal.Quotient.field m
  letI : Algebra K (AddMonoidAlgebra K (M ⧸ Z) ⧸ m) :=
    ((Ideal.Quotient.mk m).comp (algebraMap K (AddMonoidAlgebra K (M ⧸ Z)))).toAlgebra
  let e : AddMonoidAlgebra K (M ⧸ Z) →ₐ[K] (AddMonoidAlgebra K (M ⧸ Z) ⧸ m) :=
    { toRingHom := Ideal.Quotient.mk m
      commutes' := fun _ => rfl }
  exact contra_field hT hZ e fun k =>
    Ideal.Quotient.eq_zero_iff_mem.2 (hle (Ideal.subset_span ⟨k, rfl⟩))

omit [AddMonoid.FG M] [Fintype ι] in
/-- Characters trivial on `Z` kill what vanishes in `K[M/Z]`. -/
lemma ev_eq_zero_of_mkN {Z : AddSubgroup M} {A : Type u} [CommRing A] (ρ : R →+* A)
    (χ : Multiplicative M →* A) (hχ : ∀ z ∈ Z, χ (Multiplicative.ofAdd z) = 1)
    {x : AddMonoidAlgebra R M} (hx : mkN Z K (phi x) = 0) : ev ρ χ x = 0 := by
  have e : ∀ y : AddMonoidAlgebra R M, phi (mkN Z R y) = mkN Z K (phi y) := fun y => by
    have : (phi (R := R) (M := M ⧸ Z)).comp (mkN Z R) = (mkN Z K).comp (phi (R := R) (M := M)) :=
      ringHom_ext' fun m r => by
        simp [mkN_single, phi, AddMonoidAlgebra.mapRingHom_single]
    exact congrArg (fun k => k y) this
  have h0 : mkN Z R x = 0 := phi_injective (by rw [e, hx, map_zero])
  have h1 := ev_mkN Z R ρ (descChar Z χ hχ) x
  rw [h0, map_zero, descChar_comp] at h1
  exact h1.symm

omit [AddMonoid.FG M] [IsDomain R] [Fintype ι] in
lemma ev_smul {A : Type u} [CommRing A] (ρ : R →+* A) (χ : Multiplicative M →* A) (s : R)
    (w : AddMonoidAlgebra R M) : ev ρ χ (s • w) = ρ s * ev ρ χ w := by
  have e : s • w = AddMonoidAlgebra.single 0 s * w := by
    rw [Algebra.smul_def]; rfl
  rw [e, map_mul, ev_single]
  simp

/-- A common multiple over a finite index. -/
lemma exists_common {β : Type*} [Finite β] (P : β → R → Prop)
    (hP : ∀ b s t, P b s → P b (t * s)) (h : ∀ b, ∃ s : R, s ≠ 0 ∧ P b s) :
    ∃ s : R, s ≠ 0 ∧ ∀ b, P b s := by
  classical
  haveI := Fintype.ofFinite β
  choose σ hσ hPσ using h
  refine ⟨∏ b, σ b, Finset.prod_ne_zero_iff.2 fun b _ => hσ b, fun b => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ b)]
  exact hP b _ _ (hPσ b)

omit [AddMonoid.FG M] in
/-- The characters of `Z` lie in the closure, with a common denominator. -/
lemma exists_den (hT : Tests f G) {Z : AddSubgroup M} (hZ : HZ f G Z) (z : M) (hz : z ∈ Z) :
    ∃ s : R, s ≠ 0 ∧ ∀ k, ∃ n : ℕ,
      s • (f k ^ n * (AddMonoidAlgebra.single z 1 - 1)) ∈
        Ideal.span (G k : Set (AddMonoidAlgebra R M)) := by
  classical
  refine exists_common (fun k s => ∃ n : ℕ, s • (f k ^ n * (AddMonoidAlgebra.single z 1 - 1)) ∈
        Ideal.span (G k : Set (AddMonoidAlgebra R M))) ?_ fun k => ?_
  · rintro k s t ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [mul_smul]
    exact Submodule.smul_of_tower_mem _ t hn
  · have hmem : phi (AddMonoidAlgebra.single z (1 : R) - 1) ∈ Ik f G := by
      rw [mem_Ik_iff hZ, map_sub, map_sub, map_one, map_one]
      have e0 : QuotientAddGroup.mk' Z z = 0 := (QuotientAddGroup.eq_zero_iff z).2 hz
      simp only [phi, AddMonoidAlgebra.mapRingHom_single, map_one]
      rw [mkN_single, e0]
      exact sub_self _
    obtain ⟨n, hn⟩ := (qkA_eq_zero k _).1 (mem_Ik.1 hmem k)
    have hn' : phi (f k) ^ n * phi (AddMonoidAlgebra.single z (1 : R) - 1) ∈
        (Ideal.span (G k : Set (AddMonoidAlgebra R M))).map (phi (R := R) (M := M)) := by
      rw [Ideal.map_span]; exact hn
    obtain ⟨a, ha, w, hw, hwe⟩ := exists_mul_mem_of_mem_map _ hn'
    refine ⟨a, ha, n, ?_⟩
    have e : w = a • (f k ^ n * (AddMonoidAlgebra.single z 1 - 1)) := by
      refine phi_injective (hwe.trans ?_)
      have e' : ∀ (c : R) (y : AddMonoidAlgebra R M),
          phi (c • y) = algebraMap R (FractionRing R) c • phi y := by
        intro c y
        ext m
        simp [Algebra.smul_def]
      rw [e', map_mul, map_pow]
    rw [← e]
    exact hw

/-- **The ring statement.** A locally closed subgroup functor of `D(M)_R`, `R` a domain, is `D(M/Z)`
over a nonempty open of `Spec R`. -/
theorem exists_generic_ring (hT : Tests f G) :
    ∃ (s : R) (_ : s ≠ 0) (Z : AddSubgroup M), ∀ (A : Type u) [CommRing A] (ρ : R →+* A)
      (χ : Multiplicative M →* A), IsUnit (ρ s) →
        (FixP f G ρ χ ↔ ∀ z ∈ Z, χ (Multiplicative.ofAdd z) = 1) := by
  classical
  obtain ⟨Z, hZ⟩ := exists_Z_field (f := f) (G := G) hT
  have hZ' : HZ f G Z := hZ
  -- the unit ideal
  have htop := JJ_eq_top hT hZ'
  have h1 : (1 : AddMonoidAlgebra K (M ⧸ Z)) ∈ Ideal.span (Set.range fun i => mkN Z K (phi (f i))) := by
    change _ ∈ JJ f Z
    rw [htop]; trivial
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 h1
  choose ĉ hĉ using fun i => mkN_surjective Z K (c i)
  let w : AddMonoidAlgebra K M := ∑ i, ĉ i * phi (f i)
  have hw : w ∈ (Ideal.span (Set.range f)).map (phi (R := R) (M := M)) :=
    sum_mem fun i _ => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩))
  have hwN : mkN Z K w = 1 := by
    simp only [w, map_sum, map_mul, hĉ]
    exact hc
  obtain ⟨a, ha, x', hx', hxe⟩ := exists_mul_mem_of_mem_map _ hw
  have hY : mkN Z K (phi (AddMonoidAlgebra.single (0 : M) a - x')) = 0 := by
    rw [map_sub, map_sub, hxe]
    have e : algebraMap R K a • w = AddMonoidAlgebra.single 0 (algebraMap R K a) * w := by
      rw [Algebra.smul_def]; rfl
    rw [e, map_mul, hwN, mul_one]
    simp only [phi, AddMonoidAlgebra.mapRingHom_single]
    exact sub_self _
  -- the generators of `Z`
  haveI : AddGroup.FG M := AddGroup.fg_iff_addMonoid_fg.mpr inferInstance
  haveI : Module.Finite ℤ M := Module.Finite.iff_addGroup_fg.mpr inferInstance
  obtain ⟨T, hTs⟩ := (IsNoetherian.noetherian Z.toIntSubmodule : Z.toIntSubmodule.FG)
  have hTZ : ∀ z : T, (z : M) ∈ Z := fun z => by
    have : (z : M) ∈ Submodule.span ℤ (T : Set M) := Submodule.subset_span z.2
    rw [hTs] at this
    exact this
  obtain ⟨s₂, hs₂, hden⟩ := exists_common (β := T) (fun z s => ∀ k, ∃ n : ℕ,
      s • (f k ^ n * (AddMonoidAlgebra.single (z : M) 1 - 1)) ∈
        Ideal.span (G k : Set (AddMonoidAlgebra R M)))
    (fun z s t h k => by
      obtain ⟨n, hn⟩ := h k
      refine ⟨n, ?_⟩
      rw [mul_smul]
      exact Submodule.smul_of_tower_mem _ t hn)
    (fun z => exists_den hT hZ' z (hTZ z))
  refine ⟨a * s₂, mul_ne_zero ha hs₂, Z, fun A _ ρ χ hu => ?_⟩
  rw [map_mul] at hu
  have hua : IsUnit (ρ a) := isUnit_of_mul_isUnit_left hu
  have hus : IsUnit (ρ s₂) := isUnit_of_mul_isUnit_right hu
  constructor
  · intro hF
    -- the generators act trivially
    have hgen : ∀ z : T, χ (Multiplicative.ofAdd (z : M)) = 1 := by
      intro z
      refine sub_eq_zero.1 (eq_zero_of_fix hF _ fun k => ?_)
      obtain ⟨n, hn⟩ := hden z k
      obtain ⟨m, hm⟩ := pow_mul_span hF k _ hn
      refine ⟨m + n, ?_⟩
      rw [ev_smul, map_mul, map_pow, map_sub, map_one, ev_single, map_one, one_mul] at hm
      have hm' : ρ s₂ * (ev ρ χ (f k) ^ (m + n) * (χ (Multiplicative.ofAdd (z : M)) - 1)) = 0 := by
        rw [← hm, pow_add]; ring
      exact hus.mul_right_eq_zero.1 hm'
    let Z' : AddSubgroup M :=
      { carrier := {z | χ (Multiplicative.ofAdd z) = 1}
        add_mem' := fun {x y} hx hy => by
          change χ (Multiplicative.ofAdd (x + y)) = 1
          rw [ofAdd_add, map_mul, show χ _ = 1 from hx, show χ _ = 1 from hy, one_mul]
        zero_mem' := by
          change χ (Multiplicative.ofAdd 0) = 1
          rw [ofAdd_zero, map_one]
        neg_mem' := fun {x} hx => by
          change χ (Multiplicative.ofAdd (-x)) = 1
          have h : χ (Multiplicative.ofAdd x) * χ (Multiplicative.ofAdd (-x)) = 1 := by
            rw [← map_mul, ← ofAdd_add, add_neg_cancel, ofAdd_zero, map_one]
          rwa [show χ (Multiplicative.ofAdd x) = 1 from hx, one_mul] at h }
    have hle : Z.toIntSubmodule ≤ Z'.toIntSubmodule := by
      rw [← hTs]
      exact Submodule.span_le.2 fun z hz => hgen ⟨z, hz⟩
    exact fun z hz => hle hz
  · intro hχ
    refine ⟨?_, fun k x hx => ?_⟩
    · have h0 := ev_eq_zero_of_mkN ρ χ hχ hY
      rw [map_sub, ev_single, sub_eq_zero] at h0
      have h2 : ev ρ χ x' ∈ Ideal.map (ev ρ χ) (Ideal.span (Set.range f)) := Ideal.mem_map_of_mem _ hx'
      rw [Ideal.map_span, ← Set.range_comp] at h2
      have h3 : ρ a ∈ Ideal.span (Set.range fun k => ev ρ χ (f k)) := by
        have e : ρ a * χ (Multiplicative.ofAdd 0) = ρ a := by simp
        rw [← e, h0]
        exact h2
      exact Ideal.eq_top_of_isUnit_mem _ h3 hua
    · obtain ⟨n, hn⟩ := mkN_G hT hZ' k hx
      refine ⟨n, ?_⟩
      rw [← map_pow, ← map_mul]
      refine ev_eq_zero_of_mkN ρ χ hχ ?_
      rw [map_mul, map_mul, map_pow, map_pow]
      exact hn

end AlgMag.ChartQSStabGen
