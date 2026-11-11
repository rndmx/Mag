/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.AlgebraicGeometry.Cover.Directed
import AlgMag.GeneralBaseCore

/-!
# Fibre products of rings along a surjection give push-outs of schemes

Let `R' = A ×_B C` with `A → B` surjective. Then `Spec R'` is the push-out of
`Spec A ← Spec B → Spec C` in the category of **all** schemes, with no finiteness hypothesis on
`C → B`. This is what the proof of Proposition 2.19 needs from [Stacks, 0ET0] (see the module docstring
of `AlgMag.GeneralBasePushout`).

## Main results

* `AlgMag.GB.MilnorData`, `AlgMag.GB.MilnorData.away`: the hypothesis, and its localizations.
* `AlgMag.GB.IsLocalPO`, `AlgMag.GB.IsLocalPO.existsUnique`: a Zariski local form of the push-out
  property, and why it suffices.
* `AlgMag.GB.MilnorData.isLocalPO`: the affine case.
-/

suppress_compilation

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.GB

section Rings

variable {R' A C B : Type u} [CommRing R'] [CommRing A] [CommRing C] [CommRing B]

/-- `R' = A ×_B C`, with `A → B` surjective. -/
structure MilnorData (p : R' →+* A) (q : R' →+* C) (i : A →+* B) (j : C →+* B) : Prop where
  comm : ∀ z, i (p z) = j (q z)
  surj : Function.Surjective i
  inj : ∀ z, p z = 0 → q z = 0 → z = 0
  ex : ∀ x y, i x = j y → ∃ z, p z = x ∧ q z = y

variable {p : R' →+* A} {q : R' →+* C} {i : A →+* B} {j : C →+* B} (H : MilnorData p q i j)

/-- The localizations at `r : R'` of the four rings. -/
abbrev locA (p : R' →+* A) (r : R') := Localization.Away (p r)
/-- The localization of `B`. -/
abbrev locB (p : R' →+* A) (i : A →+* B) (r : R') := Localization.Away (i (p r))

/-- The localized map `R'_r → A_r`. -/
def pL (p : R' →+* A) (r : R') : Localization.Away r →+* locA p r :=
  Localization.awayLift ((algebraMap A (locA p r)).comp p) r
    (IsLocalization.Away.algebraMap_isUnit (p r))

/-- The localized map `R'_r → C_r`. -/
def qL (q : R' →+* C) (r : R') : Localization.Away r →+* locA q r := pL q r

/-- The localized map `A_r → B_r`. -/
def iL (p : R' →+* A) (i : A →+* B) (r : R') : locA p r →+* locB p i r :=
  Localization.awayLift ((algebraMap B (locB p i r)).comp i) (p r)
    (IsLocalization.Away.algebraMap_isUnit (i (p r)))

include H in
/-- The localized map `C_r → B_r`. -/
lemma isUnit_j (r : R') : IsUnit ((algebraMap B (locB p i r)).comp j (q r)) := by
  change IsUnit (algebraMap B (locB p i r) (j (q r)))
  rw [← H.comm]
  exact IsLocalization.Away.algebraMap_isUnit (i (p r))

/-- The localized map `C_r → B_r`. -/
def jL (r : R') : locA q r →+* locB p i r :=
  Localization.awayLift ((algebraMap B (locB p i r)).comp j) (q r) (isUnit_j H r)

@[simp] lemma pL_alg (r : R') (z : R') :
    pL p r (algebraMap R' _ z) = algebraMap A _ (p z) :=
  IsLocalization.Away.lift_eq r (IsLocalization.Away.algebraMap_isUnit (p r)) z

@[simp] lemma qL_alg (r : R') (z : R') :
    qL q r (algebraMap R' _ z) = algebraMap C _ (q z) :=
  IsLocalization.Away.lift_eq r (IsLocalization.Away.algebraMap_isUnit (q r)) z

@[simp] lemma iL_alg (r : R') (x : A) :
    iL p i r (algebraMap A _ x) = algebraMap B _ (i x) :=
  IsLocalization.Away.lift_eq (p r) (IsLocalization.Away.algebraMap_isUnit (i (p r))) x

@[simp] lemma jL_alg (r : R') (y : C) :
    jL H r (algebraMap C _ y) = algebraMap B _ (j y) :=
  IsLocalization.Away.lift_eq (q r) (isUnit_j H r) y

/-- **Fibre products commute with localization.** -/
theorem MilnorData.away (r : R') : MilnorData (pL p r) (qL q r) (iL p i r) (jL H r) where
  comm z := by
    have e : (iL p i r).comp (pL p r) = (jL H r).comp (qL q r) :=
      IsLocalization.ringHom_ext (Submonoid.powers r) (RingHom.ext fun z => by
        simp only [RingHom.comp_apply, pL_alg, iL_alg, qL_alg, jL_alg, H.comm])
    exact RingHom.congr_fun e z
  surj x := by
    obtain ⟨n, a, h⟩ := IsLocalization.Away.surj (i (p r)) x
    obtain ⟨b, rfl⟩ := H.surj a
    refine ⟨IsLocalization.Away.invSelf (p r) ^ n * algebraMap A _ b, ?_⟩
    have hu : IsUnit (algebraMap B (locB p i r) (i (p r))) :=
      IsLocalization.Away.algebraMap_isUnit _
    have e : iL p i r (IsLocalization.Away.invSelf (p r)) * algebraMap B (locB p i r) (i (p r)) = 1 := by
      rw [← iL_alg, ← map_mul, mul_comm]
      rw [IsLocalization.Away.mul_invSelf, map_one]
    rw [map_mul, map_pow, iL_alg, ← h]
    calc _ = (iL p i r (IsLocalization.Away.invSelf (p r)) ^ n *
          algebraMap B (locB p i r) (i (p r)) ^ n) * x := by
          ring
      _ = x := by rw [← mul_pow, e, one_pow, one_mul]
  inj z h1 h2 := by
    obtain ⟨n, a, h⟩ := IsLocalization.Away.surj r z
    have ha : pL p r (algebraMap R' _ a) = 0 := by rw [← h, map_mul, h1, zero_mul]
    have hb : qL q r (algebraMap R' _ a) = 0 := by rw [← h, map_mul, h2, zero_mul]
    rw [pL_alg] at ha
    rw [qL_alg] at hb
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (p r)) _ _).1 ha
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (q r)) _ _).1 hb
    have h0 : r ^ (m + k) * a = 0 := by
      refine H.inj _ ?_ ?_
      · simp only [map_mul, map_pow, pow_add]
        calc _ = (p r) ^ k * ((p r) ^ m * p a) := by ring
          _ = 0 := by simp only at hm; rw [hm, mul_zero]
      · simp only [map_mul, map_pow, pow_add]
        calc _ = (q r) ^ m * ((q r) ^ k * q a) := by ring
          _ = 0 := by simp only at hk; rw [hk, mul_zero]
    have h3 : algebraMap R' (Localization.Away r) a = 0 :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers r) _ _).2 ⟨⟨_, _, rfl⟩, h0⟩
    have hu : IsUnit (algebraMap R' (Localization.Away r) r ^ n) :=
      (IsLocalization.Away.algebraMap_isUnit r).pow n
    rw [h3] at h
    exact hu.mul_left_eq_zero.1 h
  ex x y hxy := by
    obtain ⟨n, a, h⟩ := IsLocalization.Away.surj (p r) x
    obtain ⟨n', b, h'⟩ := IsLocalization.Away.surj (q r) y
    have ha0 : x * algebraMap A (locA p r) ((p r) ^ (n + n')) =
        algebraMap A (locA p r) ((p r) ^ n' * a) := by
      rw [pow_add, map_mul, map_mul, ← h, map_pow, map_pow]; ring
    have hb0 : y * algebraMap C (locA q r) ((q r) ^ (n + n')) =
        algebraMap C (locA q r) ((q r) ^ n * b) := by
      rw [pow_add, map_mul, map_mul, ← h', map_pow, map_pow]; ring
    set N := n + n'
    set a₁ := (p r) ^ n' * a
    set b₁ := (q r) ^ n * b
    have hu : IsUnit (algebraMap B (locB p i r) ((i (p r)) ^ N)) := by
      rw [map_pow]
      exact (IsLocalization.Away.algebraMap_isUnit (i (p r))).pow N
    have hab : algebraMap B (locB p i r) (i a₁) = algebraMap B (locB p i r) (j b₁) := by
      have e1 := congrArg (iL p i r) ha0
      have e2 := congrArg (jL H r) hb0
      rw [map_mul, iL_alg, iL_alg, map_pow] at e1
      rw [map_mul, jL_alg, jL_alg, map_pow, ← H.comm] at e2
      rw [← e1, ← e2, hxy]
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers (i (p r))) _).1 hab
    simp only at hm
    obtain ⟨z₀, h1, h2⟩ := H.ex ((p r) ^ m * a₁) ((q r) ^ m * b₁) (by
      have e : i ((p r) ^ m * a₁) = (i (p r)) ^ m * i a₁ :=
        (map_mul i _ a₁).trans (congrArg (· * i a₁) (map_pow i _ _))
      have e' : j ((q r) ^ m * b₁) = (i (p r)) ^ m * j b₁ :=
        (map_mul j _ b₁).trans (congrArg (· * j b₁) ((map_pow j _ _).trans (by rw [H.comm r])))
      rw [e, e']
      exact hm)
    refine ⟨IsLocalization.Away.invSelf r ^ (N + m) * algebraMap R' _ z₀, ?_, ?_⟩
    · have hv : pL p r (IsLocalization.Away.invSelf r) * algebraMap A (locA p r) (p r) = 1 := by
        rw [← pL_alg, ← map_mul, mul_comm, IsLocalization.Away.mul_invSelf, map_one]
      rw [map_mul, map_pow, pL_alg, h1, map_mul, map_pow]
      calc _ = pL p r (IsLocalization.Away.invSelf r) ^ (N + m) *
            (algebraMap A (locA p r) (p r) ^ m * algebraMap A (locA p r) a₁) := rfl
        _ = pL p r (IsLocalization.Away.invSelf r) ^ (N + m) *
            (algebraMap A (locA p r) (p r) ^ m * (x * algebraMap A (locA p r) (p r) ^ N)) := by
            rw [← ha0, map_pow]
        _ = (pL p r (IsLocalization.Away.invSelf r) * algebraMap A (locA p r) (p r)) ^ (N + m) * x := by
            rw [mul_pow, pow_add (algebraMap A (locA p r) (p r))]; ring
        _ = x := by rw [hv, one_pow, one_mul]
    · have hv : qL q r (IsLocalization.Away.invSelf r) * algebraMap C (locA q r) (q r) = 1 := by
        rw [← qL_alg, ← map_mul, mul_comm, IsLocalization.Away.mul_invSelf, map_one]
      rw [map_mul, map_pow, qL_alg, h2, map_mul, map_pow]
      calc _ = qL q r (IsLocalization.Away.invSelf r) ^ (N + m) *
            (algebraMap C (locA q r) (q r) ^ m * algebraMap C (locA q r) b₁) := rfl
        _ = qL q r (IsLocalization.Away.invSelf r) ^ (N + m) *
            (algebraMap C (locA q r) (q r) ^ m * (y * algebraMap C (locA q r) (q r) ^ N)) := by
            rw [← hb0, map_pow]
        _ = (qL q r (IsLocalization.Away.invSelf r) * algebraMap C (locA q r) (q r)) ^ (N + m) * y := by
            rw [mul_pow, pow_add (algebraMap C (locA q r) (q r))]; ring
        _ = y := by rw [hv, one_pow, one_mul]

include H in
/-- **Joint surjectivity**: a prime of `R'` comes from `A` or from `C`. -/
theorem MilnorData.exists_prime (x : PrimeSpectrum R') :
    x ∈ Set.range (PrimeSpectrum.comap p) ∨ x ∈ Set.range (PrimeSpectrum.comap q) := by
  have hqs : Function.Surjective q := fun y => by
    obtain ⟨a, ha⟩ := H.surj (j y)
    obtain ⟨z, -, h⟩ := H.ex a y ha
    exact ⟨z, h⟩
  by_cases hk : RingHom.ker q ≤ x.asIdeal
  · right
    have hP : (x.asIdeal.map q).IsPrime := Ideal.map_isPrime_of_surjective hqs hk
    refine ⟨⟨_, hP⟩, PrimeSpectrum.ext ?_⟩
    change (x.asIdeal.map q).comap q = x.asIdeal
    rw [Ideal.comap_map_of_surjective q hqs]
    exact sup_eq_left.2 hk
  · left
    obtain ⟨z, hz, hzx⟩ := Set.not_subset.1 hk
    have hz0 : q z = 0 := hz
    let t : A → R' := fun a => (H.ex (a * p z) 0 (by
      rw [map_mul, H.comm, hz0, map_zero, mul_zero])).choose
    have ht : ∀ a, p (t a) = a * p z ∧ q (t a) = 0 := fun a => (H.ex (a * p z) 0 (by
      rw [map_mul, H.comm, hz0, map_zero, mul_zero])).choose_spec
    have uniq : ∀ w w', p w = p w' → q w = q w' → w = w' := fun w w' h1 h2 =>
      sub_eq_zero.1 (H.inj _ (by rw [map_sub, h1, sub_self]) (by rw [map_sub, h2, sub_self]))
    have tmul : ∀ a b, t a * t b = t (a * b) * z := fun a b =>
      uniq _ _ (by simp only [map_mul, (ht _).1]; ring) (by simp [(ht _).2])
    have tadd : ∀ a b, t (a + b) = t a + t b := fun a b =>
      uniq _ _ (by simp only [map_add, (ht _).1]; ring) (by simp [(ht _).2])
    have tp : ∀ y, t (p y) = y * z := fun y =>
      uniq _ _ (by simp only [map_mul, (ht _).1]) (by simp [(ht _).2, hz0])
    have hpr := x.2
    let Q : Ideal A :=
      { carrier := {a | t a ∈ x.asIdeal}
        add_mem' := fun {a b} ha hb => by
          simp only [Set.mem_ofPred_eq, tadd] at *
          exact add_mem ha hb
        zero_mem' := by
          have : t 0 = 0 := uniq _ _ (by simp [(ht _).1]) (by simp [(ht _).2])
          simp [this]
        smul_mem' := fun c a ha => by
          have h1 : t (c * a) * z ∈ x.asIdeal := by
            rw [← tmul]
            exact Ideal.mul_mem_left _ _ ha
          exact (hpr.mem_or_mem h1).resolve_right hzx }
    have hQ : Q.IsPrime :=
      { ne_top' := fun h => by
          have h1 : t 1 ∈ x.asIdeal := by
            have : (1 : A) ∈ Q := by rw [h]; trivial
            exact this
          have h2 : t 1 = z := uniq _ _ (by simp [(ht _).1]) (by simp [(ht _).2, hz0])
          exact hzx (h2 ▸ h1)
        mem_or_mem' := fun {a b} hab => by
          have h1 : t a * t b ∈ x.asIdeal := by
            rw [tmul]
            exact Ideal.mul_mem_right _ _ hab
          exact hpr.mem_or_mem h1 }
    refine ⟨⟨Q, hQ⟩, PrimeSpectrum.ext (Ideal.ext fun y => ?_)⟩
    change t (p y) ∈ x.asIdeal ↔ y ∈ x.asIdeal
    rw [tp]
    exact ⟨fun h => (hpr.mem_or_mem h).resolve_right hzx, fun h => Ideal.mul_mem_right _ _ h⟩

end Rings

section LocalPO

/-- A Zariski local form of the push-out property, for `a : A → P`, `c : C → P`. -/
structure IsLocalPO {A C P : Scheme.{u}} (a : A ⟶ P) (c : C ⟶ P) : Prop where
  /-- Uniqueness, over open subschemes of `P`. -/
  un : ∀ {T Y : Scheme.{u}} (G : T ⟶ P) [IsOpenImmersion G] (h₁ h₂ : T ⟶ Y),
    (∀ {W : Scheme.{u}} (u : W ⟶ A) (v : W ⟶ T), u ≫ a = v ≫ G → v ≫ h₁ = v ≫ h₂) →
    (∀ {W : Scheme.{u}} (u : W ⟶ C) (v : W ⟶ T), u ≫ c = v ≫ G → v ≫ h₁ = v ≫ h₂) → h₁ = h₂
  /-- Existence, locally on `P`. -/
  ex : ∀ {Y : Scheme.{u}} (f : A ⟶ Y) (g : C ⟶ Y),
    (∀ {W : Scheme.{u}} (u : W ⟶ A) (v : W ⟶ C), u ≫ a = v ≫ c → u ≫ f = v ≫ g) → ∀ x : P,
    ∃ (T : Scheme.{u}) (G : T ⟶ P) (_ : IsOpenImmersion G) (k : T ⟶ Y), x ∈ Set.range G ∧
      (∀ {W : Scheme.{u}} (u : W ⟶ A) (v : W ⟶ T), u ≫ a = v ≫ G → u ≫ f = v ≫ k) ∧
      (∀ {W : Scheme.{u}} (u : W ⟶ C) (v : W ⟶ T), u ≫ c = v ≫ G → u ≫ g = v ≫ k)

/-- The local form of the push-out property gives the universal property. -/
theorem IsLocalPO.existsUnique {A C P : Scheme.{u}} {a : A ⟶ P} {c : C ⟶ P} (H : IsLocalPO a c)
    {Y : Scheme.{u}} (f : A ⟶ Y) (g : C ⟶ Y)
    (hfg : ∀ {W : Scheme.{u}} (u : W ⟶ A) (v : W ⟶ C), u ≫ a = v ≫ c → u ≫ f = v ≫ g) :
    ∃! h : P ⟶ Y, a ≫ h = f ∧ c ≫ h = g := by
  have hx := fun x : P => H.ex f g hfg x
  choose T G hG k hmem hka hkc using hx
  let 𝒰 : P.OpenCover :=
    { I₀ := ULift.{u} P
      X := fun x => T x.down
      f := fun x => G x.down
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨fun x => ?_, fun x => hG x.down⟩
        obtain ⟨y, hy⟩ := hmem x
        exact ⟨⟨x⟩, y, hy⟩ }
  have hglue : ∀ x y : 𝒰.I₀, pullback.fst (𝒰.f x) (𝒰.f y) ≫ k x.down =
      pullback.snd (𝒰.f x) (𝒰.f y) ≫ k y.down := by
    intro x y
    have hoG : IsOpenImmersion (pullback.fst (𝒰.f x) (𝒰.f y) ≫ 𝒰.f x) := inferInstance
    refine H.un (pullback.fst (𝒰.f x) (𝒰.f y) ≫ 𝒰.f x) _ _ ?_ ?_
    · intro W u v huv
      have h1 := hka x.down u (v ≫ pullback.fst _ _) (by
        rw [huv, Category.assoc])
      have h2 := hka y.down u (v ≫ pullback.snd _ _) (huv.trans (by
        rw [Category.assoc]
        exact congrArg (v ≫ ·) pullback.condition))
      rw [← Category.assoc, ← Category.assoc, ← h1]
      exact h2
    · intro W u v huv
      have h1 := hkc x.down u (v ≫ pullback.fst _ _) (by
        rw [huv, Category.assoc])
      have h2 := hkc y.down u (v ≫ pullback.snd _ _) (huv.trans (by
        rw [Category.assoc]
        exact congrArg (v ≫ ·) pullback.condition))
      rw [← Category.assoc, ← Category.assoc, ← h1]
      exact h2
  let h : P ⟶ Y := 𝒰.glueMorphisms (fun x => k x.down) hglue
  have hh : ∀ x : 𝒰.I₀, 𝒰.f x ≫ h = k x.down := fun x => 𝒰.ι_glueMorphisms _ hglue x
  have ha : a ≫ h = f := by
    refine Scheme.Cover.hom_ext (𝒰.pullback₁ a) _ _ fun x => ?_
    have h1 := hka x.down (pullback.fst a (𝒰.f x)) (pullback.snd a (𝒰.f x)) pullback.condition
    change pullback.fst a (𝒰.f x) ≫ a ≫ h = pullback.fst a (𝒰.f x) ≫ f
    rw [h1, ← Category.assoc, pullback.condition, Category.assoc]
    exact congrArg (_ ≫ ·) (hh x)
  have hc : c ≫ h = g := by
    refine Scheme.Cover.hom_ext (𝒰.pullback₁ c) _ _ fun x => ?_
    have h1 := hkc x.down (pullback.fst c (𝒰.f x)) (pullback.snd c (𝒰.f x)) pullback.condition
    change pullback.fst c (𝒰.f x) ≫ c ≫ h = pullback.fst c (𝒰.f x) ≫ g
    rw [h1, ← Category.assoc, pullback.condition, Category.assoc]
    exact congrArg (_ ≫ ·) (hh x)
  refine ⟨h, ⟨ha, hc⟩, ?_⟩
  rintro h' ⟨e1, e2⟩
  refine H.un (𝟙 P) h' h (fun {W} u v huv => ?_) (fun {W} u v huv => ?_)
  · have hv : v = u ≫ a := by rw [huv, Category.comp_id]
    rw [hv, Category.assoc, Category.assoc, e1, ha]
  · have hv : v = u ≫ c := by rw [huv, Category.comp_id]
    rw [hv, Category.assoc, Category.assoc, e2, hc]

/-- The local form of the push-out property, and a cartesian square, give a push-out in schemes. -/
theorem IsLocalPO.isPushout {A B C P : Scheme.{u}} {a : A ⟶ P} {c : C ⟶ P} {bA : B ⟶ A}
    {bC : B ⟶ C} (H : IsLocalPO a c) (hpb : IsPullback bA bC a c) : IsPushout bA bC a c := by
  have ex : ∀ s : PushoutCocone bA bC, ∃! h : P ⟶ s.pt, a ≫ h = s.inl ∧ c ≫ h = s.inr := fun s =>
    H.existsUnique s.inl s.inr fun {W} u v huv => by
      have h1 : hpb.lift u v huv ≫ bA = u := hpb.lift_fst _ _ _
      have h2 : hpb.lift u v huv ≫ bC = v := hpb.lift_snd _ _ _
      calc u ≫ s.inl = (hpb.lift u v huv ≫ bA) ≫ s.inl := by rw [h1]
        _ = hpb.lift u v huv ≫ bC ≫ s.inr := by rw [Category.assoc, s.condition]
        _ = v ≫ s.inr := by rw [← Category.assoc, h2]
  refine ⟨⟨hpb.w⟩, ⟨PushoutCocone.IsColimit.mk _ (fun s => (ex s).choose)
    (fun s => (ex s).choose_spec.1.1) (fun s => (ex s).choose_spec.1.2) ?_⟩⟩
  intro s m h1 h2
  exact (ex s).choose_spec.2 m ⟨h1, h2⟩

/-- The local form of the push-out property can be checked on an open cover of `P`, whose preimages
in `A` and `C` are `A_i` and `C_i`. -/
theorem IsLocalPO.of_cover {A C P : Scheme.{u}} {a : A ⟶ P} {c : C ⟶ P} {I : Type u}
    {Ai Ci Pi : I → Scheme.{u}} (χA : ∀ i, Ai i ⟶ A) (χC : ∀ i, Ci i ⟶ C) (χP : ∀ i, Pi i ⟶ P)
    (ai : ∀ i, Ai i ⟶ Pi i) (ci : ∀ i, Ci i ⟶ Pi i) (hopen : ∀ i, IsOpenImmersion (χP i))
    (hcov : ∀ x : P, ∃ i, x ∈ Set.range (χP i))
    (hA : ∀ i, IsPullback (χA i) (ai i) a (χP i)) (hC : ∀ i, IsPullback (χC i) (ci i) c (χP i))
    (H : ∀ i, IsLocalPO (ai i) (ci i)) : IsLocalPO a c where
  un {T Y} G _ h₁ h₂ ha hc := by
    let 𝒰 : P.OpenCover :=
      { I₀ := I
        X := Pi
        f := χP
        mem₀ := by
          rw [Scheme.presieve₀_mem_precoverage_iff]
          refine ⟨fun x => ?_, hopen⟩
          obtain ⟨i, y, hy⟩ := hcov x
          exact ⟨i, y, hy⟩ }
    refine Scheme.Cover.hom_ext (𝒰.pullback₁ G) _ _ fun i => ?_
    change pullback.fst G (χP i) ≫ h₁ = pullback.fst G (χP i) ≫ h₂
    have hG' : IsOpenImmersion (pullback.snd G (χP i)) := inferInstance
    refine (H i).un (pullback.snd G (χP i)) _ _ ?_ ?_
    · intro W u v huv
      rw [← Category.assoc, ← Category.assoc]
      refine ha (u ≫ χA i) (v ≫ pullback.fst G (χP i)) ?_
      rw [Category.assoc, (hA i).w, ← Category.assoc, huv, Category.assoc, Category.assoc,
        pullback.condition]
    · intro W u v huv
      rw [← Category.assoc, ← Category.assoc]
      refine hc (u ≫ χC i) (v ≫ pullback.fst G (χP i)) ?_
      rw [Category.assoc, (hC i).w, ← Category.assoc, huv, Category.assoc, Category.assoc,
        pullback.condition]
  ex {Y} f g hfg x := by
    obtain ⟨i, x', hx'⟩ := hcov x
    obtain ⟨T, G, hG, k, hmem, hka, hkc⟩ := (H i).ex (χA i ≫ f) (χC i ≫ g) (fun {W} u v huv => by
      rw [← Category.assoc, ← Category.assoc]
      refine hfg _ _ ?_
      rw [Category.assoc, Category.assoc, (hA i).w, (hC i).w, ← Category.assoc, huv, Category.assoc]) x'
    have := hopen i
    refine ⟨T, G ≫ χP i, inferInstance, k, ?_, ?_, ?_⟩
    · obtain ⟨t, rfl⟩ := hmem
      refine ⟨t, ?_⟩
      rw [Scheme.Hom.comp_apply, hx']
    · intro W u v huv
      have huv' : u ≫ a = (v ≫ G) ≫ χP i := by rw [huv, Category.assoc]
      have h1 : (hA i).lift u (v ≫ G) huv' ≫ χA i = u := (hA i).lift_fst _ _ _
      have h2 : (hA i).lift u (v ≫ G) huv' ≫ ai i = v ≫ G := (hA i).lift_snd _ _ _
      have h3 := hka ((hA i).lift u (v ≫ G) huv') v h2
      rw [← h3, ← Category.assoc, h1]
    · intro W u v huv
      have huv' : u ≫ c = (v ≫ G) ≫ χP i := by rw [huv, Category.assoc]
      have h1 : (hC i).lift u (v ≫ G) huv' ≫ χC i = u := (hC i).lift_fst _ _ _
      have h2 : (hC i).lift u (v ≫ G) huv' ≫ ci i = v ≫ G := (hC i).lift_snd _ _ _
      have h3 := hkc ((hC i).lift u (v ≫ G) huv') v h2
      rw [← h3, ← Category.assoc, h1]

end LocalPO

section Affine

variable {R' A C B : Type u} [CommRing R'] [CommRing A] [CommRing C] [CommRing B]
variable {p : R' →+* A} {q : R' →+* C} {i : A →+* B} {j : C →+* B} (H : MilnorData p q i j)

/-- `Spec` of a ring morphism, for rings given as types. -/
abbrev sp {X Y : Type u} [CommRing X] [CommRing Y] (φ : X →+* Y) :
    Spec (CommRingCat.of Y) ⟶ Spec (CommRingCat.of X) := Spec.map (CommRingCat.ofHom φ)

lemma sp_comp {X Y Z : Type u} [CommRing X] [CommRing Y] [CommRing Z] (φ : X →+* Y) (ψ : Y →+* Z) :
    sp (ψ.comp φ) = sp ψ ≫ sp φ := by
  rw [sp, sp, sp, ← Spec.map_comp]
  rfl

lemma sp_apply {X Y : Type u} [CommRing X] [CommRing Y] (φ : X →+* Y) (y : PrimeSpectrum Y) :
    sp φ y = PrimeSpectrum.comap φ y := rfl

/-- The inclusion of a basic open. -/
abbrev spAway {X : Type u} [CommRing X] (r : X) : Spec (CommRingCat.of (Localization.Away r)) ⟶
    Spec (CommRingCat.of X) := sp (algebraMap X (Localization.Away r))

instance {X : Type u} [CommRing X] (r : X) : IsOpenImmersion (spAway r) :=
  IsOpenImmersion.of_isLocalization r

lemma range_spAway {X : Type u} [CommRing X] (r : X) :
    Set.range (spAway r) = (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum X)) :=
  PrimeSpectrum.localization_away_comap_range _ r

include H in
/-- Choice of `r`, first case. -/
lemma exists_r_of_C (OA : TopologicalSpace.Opens (PrimeSpectrum A))
    (OC : TopologicalSpace.Opens (PrimeSpectrum C))
    (hc : ∀ b : PrimeSpectrum B, PrimeSpectrum.comap i b ∈ OA ↔ PrimeSpectrum.comap j b ∈ OC)
    (z : PrimeSpectrum C) (hz : z ∈ OC) :
    ∃ r : R', z ∈ PrimeSpectrum.basicOpen (q r) ∧ PrimeSpectrum.basicOpen (p r) ≤ OA ∧
      PrimeSpectrum.basicOpen (q r) ≤ OC := by
  obtain ⟨_, ⟨γ, rfl⟩, hzγ, hγ⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    hz OC.isOpen
  obtain ⟨𝔞, h𝔞⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).1 OA.isOpen.isClosed_compl
  have hOA : ∀ y : PrimeSpectrum A, y ∉ OA ↔ (𝔞 : Set A) ⊆ y.asIdeal := fun y => by
    have := Set.ext_iff.1 h𝔞 y
    simpa [PrimeSpectrum.mem_zeroLocus] using this
  have hrad : j γ ∈ (𝔞.map i).radical := by
    rw [Ideal.radical_eq_sInf]
    refine Submodule.mem_sInf.2 fun J hJ => ?_
    obtain ⟨hle, hprime⟩ := hJ
    let b : PrimeSpectrum B := ⟨J, hprime⟩
    have h1 : PrimeSpectrum.comap i b ∉ OA := by
      rw [hOA]
      intro a ha
      exact hle (Ideal.mem_map_of_mem _ ha)
    have h2 : PrimeSpectrum.comap j b ∉ OC := fun h => h1 ((hc b).2 h)
    by_contra hγJ
    exact h2 (hγ (show γ ∉ (PrimeSpectrum.comap j b).asIdeal from hγJ))
  obtain ⟨n, hn⟩ := hrad
  have hn1 : (j γ) ^ (n + 1) ∈ 𝔞.map i := by
    rw [pow_succ]
    exact Ideal.mul_mem_right _ _ hn
  obtain ⟨α, hα, hαe⟩ := (Ideal.mem_map_iff_of_surjective i H.surj).1 hn1
  obtain ⟨r, h1, h2⟩ := H.ex α (γ ^ (n + 1)) (by rw [hαe, map_pow])
  have hD : PrimeSpectrum.basicOpen (q r) = PrimeSpectrum.basicOpen γ := by
    rw [h2]
    exact PrimeSpectrum.basicOpen_pow _ _ (Nat.succ_pos n)
  refine ⟨r, ?_, ?_, ?_⟩
  · rw [hD]; exact hzγ
  · intro y hy
    by_contra hyO
    have := (hOA y).1 hyO hα
    rw [h1] at hy
    exact hy this
  · rw [hD]; exact hγ

include H in
/-- Choice of `r`, second case. -/
lemma exists_r_of_A (OA : TopologicalSpace.Opens (PrimeSpectrum A)) (w : PrimeSpectrum A)
    (hw : w ∈ OA) (hk : ¬ RingHom.ker i ≤ w.asIdeal) :
    ∃ r : R', w ∈ PrimeSpectrum.basicOpen (p r) ∧ PrimeSpectrum.basicOpen (p r) ≤ OA ∧ q r = 0 := by
  obtain ⟨_, ⟨α, rfl⟩, hwα, hα⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    hw OA.isOpen
  obtain ⟨ι, hι, hιw⟩ := Set.not_subset.1 hk
  have hι0 : i ι = 0 := hι
  obtain ⟨r, h1, h2⟩ := H.ex (α * ι) 0 (by rw [map_mul, hι0, mul_zero, map_zero])
  refine ⟨r, ?_, ?_, h2⟩
  · rw [h1]
    change α * ι ∉ w.asIdeal
    exact fun h => (w.2.mem_or_mem h).elim hwα hιw
  · intro y hy
    rw [h1] at hy
    exact hα (show α ∉ y.asIdeal from fun h => hy (Ideal.mul_mem_right _ _ h))

/-- A ring morphism to `R'` from a pair of compatible ring morphisms. -/
def lift (H : MilnorData p q i j) {E : Type u} [CommRing E] (φ : E →+* A) (ψ : E →+* C)
    (h : ∀ e, i (φ e) = j (ψ e)) : E →+* R' where
  toFun e := (H.ex (φ e) (ψ e) (h e)).choose
  map_one' := by
    have s := (H.ex (φ 1) (ψ 1) (h 1)).choose_spec
    refine sub_eq_zero.1 (H.inj _ ?_ ?_)
    · rw [map_sub, s.1, map_one, map_one, sub_self]
    · rw [map_sub, s.2, map_one, map_one, sub_self]
  map_mul' a b := by
    have s := (H.ex (φ (a * b)) (ψ (a * b)) (h _)).choose_spec
    have sa := (H.ex (φ a) (ψ a) (h a)).choose_spec
    have sb := (H.ex (φ b) (ψ b) (h b)).choose_spec
    refine sub_eq_zero.1 (H.inj _ ?_ ?_)
    · rw [map_sub, s.1, map_mul, map_mul, sa.1, sb.1, sub_self]
    · rw [map_sub, s.2, map_mul, map_mul, sa.2, sb.2, sub_self]
  map_zero' := by
    have s := (H.ex (φ 0) (ψ 0) (h 0)).choose_spec
    refine H.inj _ ?_ ?_
    · rw [s.1, map_zero]
    · rw [s.2, map_zero]
  map_add' a b := by
    have s := (H.ex (φ (a + b)) (ψ (a + b)) (h _)).choose_spec
    have sa := (H.ex (φ a) (ψ a) (h a)).choose_spec
    have sb := (H.ex (φ b) (ψ b) (h b)).choose_spec
    refine sub_eq_zero.1 (H.inj _ ?_ ?_)
    · rw [map_sub, s.1, map_add, map_add, sa.1, sb.1, sub_self]
    · rw [map_sub, s.2, map_add, map_add, sa.2, sb.2, sub_self]

lemma p_lift {E : Type u} [CommRing E] (φ : E →+* A) (ψ : E →+* C) (h : ∀ e, i (φ e) = j (ψ e))
    (e : E) : p (lift H φ ψ h e) = φ e := (H.ex (φ e) (ψ e) (h e)).choose_spec.1

lemma q_lift {E : Type u} [CommRing E] (φ : E →+* A) (ψ : E →+* C) (h : ∀ e, i (φ e) = j (ψ e))
    (e : E) : q (lift H φ ψ h e) = ψ e := (H.ex (φ e) (ψ e) (h e)).choose_spec.2

/-- A morphism from `Spec D` landing in an affine open is `Spec` of a ring morphism. -/
lemma exists_ring_of_range {D : Type u} [CommRing D] {Y : Scheme.{u}} {W : Y.Opens}
    (hW : IsAffineOpen W) (k : Spec (CommRingCat.of D) ⟶ Y) (hk : Set.range k ⊆ W) :
    ∃ φ : Γ(Y, W) →+* D, sp φ ≫ hW.fromSpec = k := by
  have hr : Set.range k ⊆ Set.range hW.fromSpec := by rwa [hW.range_fromSpec]
  let l := IsOpenImmersion.lift hW.fromSpec k hr
  refine ⟨(Spec.preimage l).hom, ?_⟩
  have : sp (Spec.preimage l).hom = l := by
    change Spec.map (CommRingCat.ofHom (Spec.preimage l).hom) = l
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  rw [this]
  exact IsOpenImmersion.lift_fac _ _ _

lemma sp_injective {X Y : Type u} [CommRing X] [CommRing Y] {φ ψ : X →+* Y} (h : sp φ = sp ψ) :
    φ = ψ := by
  have := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom this

include H in
/-- Uniqueness on `Spec R'`, inside an affine open of the target. -/
lemma eq_of_range {Y : Scheme.{u}} {W : Y.Opens} (hW : IsAffineOpen W)
    (k₁ k₂ : Spec (CommRingCat.of R') ⟶ Y) (h₁ : Set.range k₁ ⊆ W) (h₂ : Set.range k₂ ⊆ W)
    (hp : sp p ≫ k₁ = sp p ≫ k₂) (hq : sp q ≫ k₁ = sp q ≫ k₂) : k₁ = k₂ := by
  obtain ⟨φ₁, rfl⟩ := exists_ring_of_range hW k₁ h₁
  obtain ⟨φ₂, rfl⟩ := exists_ring_of_range hW k₂ h₂
  have e : ∀ {D : Type u} [CommRing D] (t : R' →+* D),
      sp t ≫ sp φ₁ ≫ hW.fromSpec = sp t ≫ sp φ₂ ≫ hW.fromSpec → t.comp φ₁ = t.comp φ₂ := by
    intro D _ t ht
    apply sp_injective
    rw [sp_comp, sp_comp]
    rw [← cancel_mono hW.fromSpec, Category.assoc, Category.assoc]
    exact ht
  have ep := e p hp
  have eq := e q hq
  have : φ₁ = φ₂ := RingHom.ext fun x => sub_eq_zero.1 (H.inj _
    (by rw [map_sub, sub_eq_zero]; exact RingHom.congr_fun ep x)
    (by rw [map_sub, sub_eq_zero]; exact RingHom.congr_fun eq x))
  rw [this]

/-- The square `Spec A_r → Spec R'_r → Spec R' = Spec A_r → Spec A → Spec R'`. -/
lemma sp_pL_spAway (p : R' →+* A) (r : R') :
    sp (pL p r) ≫ spAway r = spAway (p r) ≫ sp p := by
  rw [← sp_comp, ← sp_comp]
  congr 1
  exact RingHom.ext fun z => pL_alg r z

lemma sp_iL_spAway (r : R') : sp (iL p i r) ≫ spAway (p r) = spAway (i (p r)) ≫ sp i := by
  rw [← sp_comp, ← sp_comp]
  congr 1
  exact RingHom.ext fun z => iL_alg r z

lemma sp_jL_spAway (r : R') : sp (jL H r) ≫ spAway (q r) = spAway (i (p r)) ≫ sp j := by
  rw [← sp_comp, ← sp_comp]
  congr 1
  exact RingHom.ext fun z => jL_alg H r z

include H in
lemma sp_comm : sp i ≫ sp p = sp j ≫ sp q := by
  rw [← sp_comp, ← sp_comp]
  congr 1
  exact RingHom.ext fun z => H.comm z

/-- A morphism to `Spec A` whose composite to `Spec R'` lands in `D(r)` lands in `Spec A_r`. -/
lemma exists_lift_spAway {W : Scheme.{u}} (p : R' →+* A) (r : R') (u : W ⟶ Spec (CommRingCat.of A))
    (v : W ⟶ Spec (CommRingCat.of (Localization.Away r))) (huv : u ≫ sp p = v ≫ spAway r) :
    ∃ ū : W ⟶ Spec (CommRingCat.of (Localization.Away (p r))),
      ū ≫ spAway (p r) = u ∧ ū ≫ sp (pL p r) = v := by
  have hr : Set.range u ⊆ Set.range (spAway (p r)) := by
    rw [range_spAway]
    rintro _ ⟨y, rfl⟩
    have h1 : sp p (u y) = spAway r (v y) := by
      have e := congrArg (fun k : W ⟶ _ => k y) huv
      simpa using e
    have h2 : sp p (u y) ∈ (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R')) := by
      rw [h1, ← range_spAway]
      exact ⟨_, rfl⟩
    exact h2
  let ū := IsOpenImmersion.lift (spAway (p r)) u hr
  have hū : ū ≫ spAway (p r) = u := IsOpenImmersion.lift_fac _ _ _
  refine ⟨ū, hū, ?_⟩
  rw [← cancel_mono (spAway r), Category.assoc, sp_pL_spAway, ← Category.assoc, hū, huv]

include H in
/-- **Uniqueness**, over an open subscheme of `Spec R'`. -/
theorem MilnorData.un {T Y : Scheme.{u}} (G : T ⟶ Spec (CommRingCat.of R')) [IsOpenImmersion G]
    (h₁ h₂ : T ⟶ Y)
    (ha : ∀ {W : Scheme.{u}} (u : W ⟶ Spec (CommRingCat.of A)) (v : W ⟶ T), u ≫ sp p = v ≫ G →
      v ≫ h₁ = v ≫ h₂)
    (hc : ∀ {W : Scheme.{u}} (u : W ⟶ Spec (CommRingCat.of C)) (v : W ⟶ T), u ≫ sp q = v ≫ G →
      v ≫ h₁ = v ≫ h₂) : h₁ = h₂ := by
  have hpt : ∀ y : T, h₁ y = h₂ y := by
    intro y
    rcases H.exists_prime (G y) with ⟨w, hw⟩ | ⟨z, hz⟩
    · obtain ⟨t, -, ht⟩ := Scheme.Pullback.exists_preimage_pullback (f := sp p) (g := G) w y hw
      have e := ha (pullback.fst (sp p) G) (pullback.snd (sp p) G) pullback.condition
      have e' := congrArg (fun k : pullback (sp p) G ⟶ Y => k t) e
      simpa [ht] using e'
    · obtain ⟨t, -, ht⟩ := Scheme.Pullback.exists_preimage_pullback (f := sp q) (g := G) z y hz
      have e := hc (pullback.fst (sp q) G) (pullback.snd (sp q) G) pullback.condition
      have e' := congrArg (fun k : pullback (sp q) G ⟶ Y => k t) e
      simpa [ht] using e'
  -- local data at a point
  have hloc : ∀ y : T, ∃ (r : R') (e : Spec (CommRingCat.of (Localization.Away r)) ⟶ T),
      e ≫ G = spAway r ∧ y ∈ Set.range e ∧ e ≫ h₁ = e ≫ h₂ := by
    intro y
    obtain ⟨W, hW, hyW, -⟩ : ∃ W : Y.Opens, IsAffineOpen W ∧ h₁ y ∈ W ∧ True := by
      obtain ⟨U, hU⟩ := Y.directedAffineCover.exists_eq (h₁ y)
      let U' : Y.affineOpens := U
      obtain ⟨z, hz⟩ := hU
      refine ⟨U'.1, U'.2, ?_, trivial⟩
      rw [← hz]
      exact z.2
    -- the open `G (h₁⁻¹ W)` of `Spec R'`
    have hO : IsOpen (G '' (h₁ ⁻¹' (W : Set Y))) :=
      G.isOpenEmbedding.isOpenMap _ (W.isOpen.preimage h₁.continuous)
    obtain ⟨_, ⟨r, rfl⟩, hr, hrO⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        (⟨y, hyW, rfl⟩ : G y ∈ G '' (h₁ ⁻¹' (W : Set Y))) hO
    have hr2 : Set.range (spAway r) ⊆ Set.range G := by
      rw [range_spAway]
      exact hrO.trans (Set.image_subset_range _ _)
    let e := IsOpenImmersion.lift G (spAway r) hr2
    have he : e ≫ G = spAway r := IsOpenImmersion.lift_fac _ _ _
    have hrange : ∀ x, e x ∈ h₁ ⁻¹' (W : Set Y) := by
      intro x
      have hx : spAway r x ∈ (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R')) := by
        rw [← range_spAway]
        exact ⟨_, rfl⟩
      obtain ⟨t, ht, hte⟩ := hrO hx
      have h3 : G (e x) = spAway r x := by
        rw [← he]
        simp
      have h4 : t = e x := G.isOpenEmbedding.injective (hte.trans h3.symm)
      exact h4 ▸ ht
    refine ⟨r, e, he, ?_, ?_⟩
    · have hyr : G y ∈ Set.range (spAway r) := by
        rw [range_spAway]
        exact hr
      obtain ⟨x, hx⟩ := hyr
      refine ⟨x, G.isOpenEmbedding.injective ?_⟩
      rw [← hx, ← he]
      simp
    · refine eq_of_range (H.away r) hW _ _ ?_ ?_ ?_ ?_
      · rintro _ ⟨x, rfl⟩
        simpa using hrange x
      · rintro _ ⟨x, rfl⟩
        have := hrange x
        rw [Set.mem_preimage, hpt] at this
        simpa using this
      · have := ha (spAway (p r)) (sp (pL p r) ≫ e) (by
          rw [Category.assoc, he, sp_pL_spAway])
        simpa using this
      · have := hc (spAway (q r)) (sp (qL q r) ≫ e) (by
          rw [Category.assoc, he]
          exact (sp_pL_spAway q r).symm)
        simpa using this
  choose r e heG hmem heq using hloc
  have hoe : ∀ y, IsOpenImmersion (e y) := fun y => by
    have : IsOpenImmersion (e y ≫ G) := by
      rw [heG]
      infer_instance
    exact IsOpenImmersion.of_comp _ G
  let 𝒰 : T.OpenCover :=
    { I₀ := ULift.{u} T
      X := fun y => Spec (CommRingCat.of (Localization.Away (r y.down)))
      f := fun y => e y.down
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨fun y => ?_, fun y => hoe y.down⟩
        obtain ⟨x, hx⟩ := hmem y
        exact ⟨⟨y⟩, x, hx⟩ }
  exact Scheme.Cover.hom_ext 𝒰 _ _ fun y => heq y.down

include H in
/-- The compatibility of a morphism out of `Spec A` and a morphism out of `Spec C` on `Spec B`,
in terms of open subsets. -/
lemma compat_opens {Y : Scheme.{u}} (f : Spec (CommRingCat.of A) ⟶ Y)
    (g : Spec (CommRingCat.of C) ⟶ Y) (hb : sp i ≫ f = sp j ≫ g) (W : Y.Opens)
    (b : PrimeSpectrum B) :
    PrimeSpectrum.comap i b ∈ (f ⁻¹ᵁ W) ↔ PrimeSpectrum.comap j b ∈ (g ⁻¹ᵁ W) := by
  have e : (sp i ≫ f) b = (sp j ≫ g) b := by rw [hb]
  have e' : f (sp i b) = g (sp j b) :=
    (Scheme.Hom.comp_apply (sp i) f b).symm.trans (e.trans (Scheme.Hom.comp_apply (sp j) g b))
  change f (sp i b) ∈ W ↔ g (sp j b) ∈ W
  rw [e']

include H in
/-- **Existence**, locally on `Spec R'`. -/
theorem MilnorData.ex_local {Y : Scheme.{u}} (f : Spec (CommRingCat.of A) ⟶ Y)
    (g : Spec (CommRingCat.of C) ⟶ Y)
    (hfg : ∀ {W : Scheme.{u}} (u : W ⟶ Spec (CommRingCat.of A)) (v : W ⟶ Spec (CommRingCat.of C)),
      u ≫ sp p = v ≫ sp q → u ≫ f = v ≫ g) (x : Spec (CommRingCat.of R')) :
    ∃ (r : R') (k : Spec (CommRingCat.of (Localization.Away r)) ⟶ Y),
      x ∈ Set.range (spAway r) ∧
      sp (pL p r) ≫ k = spAway (p r) ≫ f ∧ sp (qL q r) ≫ k = spAway (q r) ≫ g := by
  have hb : sp i ≫ f = sp j ≫ g := hfg (sp i) (sp j) (sp_comm H)
  have exW : ∀ y : Y, ∃ W : Y.Opens, IsAffineOpen W ∧ y ∈ W := by
    intro y
    obtain ⟨U, z, hz⟩ := Y.directedAffineCover.exists_eq y
    let U' : Y.affineOpens := U
    refine ⟨U'.1, U'.2, ?_⟩
    rw [← hz]
    exact z.2
  obtain ⟨W, hW, r, hx, hAW, hCW⟩ : ∃ W : Y.Opens, IsAffineOpen W ∧ ∃ r : R',
      x ∈ (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R')) ∧
      PrimeSpectrum.basicOpen (p r) ≤ f ⁻¹ᵁ W ∧ PrimeSpectrum.basicOpen (q r) ≤ g ⁻¹ᵁ W := by
    have caseC : ∀ z : PrimeSpectrum C, PrimeSpectrum.comap q z = x → ∃ W : Y.Opens,
        IsAffineOpen W ∧ ∃ r : R', x ∈ (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R')) ∧
        PrimeSpectrum.basicOpen (p r) ≤ f ⁻¹ᵁ W ∧ PrimeSpectrum.basicOpen (q r) ≤ g ⁻¹ᵁ W := by
      rintro z rfl
      obtain ⟨W, hW, hy⟩ := exW (g z)
      obtain ⟨r, h1, h2, h3⟩ := exists_r_of_C H (f ⁻¹ᵁ W) (g ⁻¹ᵁ W)
        (compat_opens H f g hb W) z hy
      exact ⟨W, hW, r, h1, h2, h3⟩
    rcases H.exists_prime x with ⟨w, hw⟩ | ⟨z, hz⟩
    · by_cases hk : RingHom.ker i ≤ w.asIdeal
      · have hP : (w.asIdeal.map i).IsPrime := Ideal.map_isPrime_of_surjective H.surj hk
        let b : PrimeSpectrum B := ⟨_, hP⟩
        have hbw : PrimeSpectrum.comap i b = w := by
          refine PrimeSpectrum.ext ?_
          change (w.asIdeal.map i).comap i = w.asIdeal
          rw [Ideal.comap_map_of_surjective i H.surj]
          exact sup_eq_left.2 hk
        refine caseC (PrimeSpectrum.comap j b) ?_
        rw [← hw, ← hbw]
        have e : (sp i ≫ sp p) b = (sp j ≫ sp q) b := by rw [sp_comm H]
        exact ((Scheme.Hom.comp_apply (sp i) (sp p) b).symm.trans
          (e.trans (Scheme.Hom.comp_apply (sp j) (sp q) b))).symm
      · obtain ⟨W, hW, hy⟩ := exW (f w)
        obtain ⟨r, h1, h2, h3⟩ := exists_r_of_A H (f ⁻¹ᵁ W) w hy hk
        refine ⟨W, hW, r, ?_, h2, ?_⟩
        · rw [← hw]
          exact h1
        · rw [h3]
          intro y hy'
          exact (hy' (zero_mem _)).elim
    · exact caseC z hz
  have rangeA : Set.range (spAway (p r) ≫ f) ⊆ W := by
    rintro _ ⟨y, rfl⟩
    have h1 : spAway (p r) y ∈ (PrimeSpectrum.basicOpen (p r) : Set (PrimeSpectrum A)) := by
      rw [← range_spAway]
      exact ⟨_, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hAW h1
  have rangeC : Set.range (spAway (q r) ≫ g) ⊆ W := by
    rintro _ ⟨y, rfl⟩
    have h1 : spAway (q r) y ∈ (PrimeSpectrum.basicOpen (q r) : Set (PrimeSpectrum C)) := by
      rw [← range_spAway]
      exact ⟨_, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hCW h1
  obtain ⟨φ, hφ⟩ := exists_ring_of_range hW _ rangeA
  obtain ⟨ψ, hψ⟩ := exists_ring_of_range hW _ rangeC
  have hcomp : (iL p i r).comp φ = (jL H r).comp ψ := by
    apply sp_injective
    rw [sp_comp, sp_comp, ← cancel_mono hW.fromSpec, Category.assoc, Category.assoc, hφ, hψ,
      ← Category.assoc, ← Category.assoc, sp_iL_spAway, sp_jL_spAway, Category.assoc, Category.assoc,
      hb]
  let θ := lift (H.away r) φ ψ fun e => RingHom.congr_fun hcomp e
  have hθp : (pL p r).comp θ = φ := RingHom.ext fun e => p_lift (H.away r) φ ψ _ e
  have hθq : (qL q r).comp θ = ψ := RingHom.ext fun e => q_lift (H.away r) φ ψ _ e
  refine ⟨r, sp θ ≫ hW.fromSpec, ?_, ?_, ?_⟩
  · rw [range_spAway]
    exact hx
  · rw [← Category.assoc, ← sp_comp, hθp, hφ]
  · rw [← Category.assoc, ← sp_comp, hθq, hψ]

include H in
/-- **The affine case of the push-out property** in the local form. -/
theorem MilnorData.isLocalPO : IsLocalPO (sp p) (sp q) where
  un G _ h₁ h₂ ha hc := H.un G h₁ h₂ ha hc
  ex f g hfg x := by
    obtain ⟨r, k, hx, h1, h2⟩ := H.ex_local f g hfg x
    refine ⟨_, spAway r, inferInstance, k, hx, ?_, ?_⟩
    · intro W u v huv
      obtain ⟨ū, h3, h4⟩ := exists_lift_spAway p r u v huv
      rw [← h3, ← h4, Category.assoc, Category.assoc, h1]
    · intro W u v huv
      obtain ⟨ū, h3, h4⟩ := exists_lift_spAway q r u v huv
      have h5 : ū ≫ sp (qL q r) = v := h4
      rw [← h3, ← h5, Category.assoc, Category.assoc, h2]

end Affine

end AlgMag.GB
