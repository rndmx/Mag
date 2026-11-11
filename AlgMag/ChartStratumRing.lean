/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Generic stabilizers of `D(M)`: the ring statement behind Lemma 4.2

The ring-theoretic input of Lemma 4.2 of the proof of the chart lemma.

An ideal `I` of `R[M]`, `R` a noetherian domain and `M` finitely generated, which defines a subgroup
functor of `D(M)_R` is generically the ideal of `D(M/Z)`:

* `AlgMag.ChartStratum.exists_stab_subgroup`: there are `s ≠ 0` in `R` and a subgroup `Z ≤ M` such
  that over `R_s` a character kills `I` exactly when it is trivial on `Z`.

Over the fraction field this is the classification of closed subgroups of `D(M)` (SGA3 VIII 3.2),
proved here from the linear independence of group-like elements.
-/

open TensorProduct

universe u

namespace AlgMag.ChartStratum

variable {M : Type u} [AddCommGroup M]

section Field

variable {K : Type u} [Field K] {A : Type u} [CommRing A] [Algebra K A]

/-- Group-like elements are linearly independent: a character `c` of `M` in `A` with a comultiplication
has no nontrivial relation among distinct values. -/
theorem relation_eq_zero (Δ : A →ₗ[K] A ⊗[K] A) (c : M → A)
    (hΔ : ∀ m, Δ (c m) = c m ⊗ₜ[K] c m) (hc : ∀ m, c m ≠ 0)
    (s : Finset A) (hs : ∀ x ∈ s, ∃ m, c m = x) (a : A → K)
    (h : ∑ x ∈ s, a x • x = 0) : ∀ x ∈ s, a x = 0 := by
  classical
  induction s using Finset.strongInduction generalizing a with
  | H s ih =>
    by_contra hne
    push Not at hne
    obtain ⟨x, hx, hax⟩ := hne
    obtain ⟨m, rfl⟩ := hs x hx
    -- the relation has a second term
    by_cases hsing : ∃ y ∈ s, y ≠ c m ∧ a y ≠ 0
    · obtain ⟨y, hy, hyx, hay⟩ := hsing
      -- a functional separating `c m` and `y`
      obtain ⟨φ, hφ⟩ : ∃ φ : A →ₗ[K] K, φ (c m) ≠ φ y := by
        by_contra hall
        push Not at hall
        have : c m - y = 0 := (Module.forall_dual_apply_eq_zero_iff K (c m - y)).mp fun φ => by
          rw [map_sub, hall φ, sub_self]
        exact hyx (sub_eq_zero.mp this).symm
      let ψ : A ⊗[K] A →ₗ[K] A :=
        (TensorProduct.rid K A).toLinearMap ∘ₗ LinearMap.lTensor A φ
      have hψ : ∀ x ∈ s, ψ (Δ x) = φ x • x := by
        intro x hx
        obtain ⟨n, rfl⟩ := hs x hx
        simp [ψ, hΔ]
      have h1 : ∑ x ∈ s, (a x * φ x) • x = 0 := by
        have := congrArg (fun z => ψ (Δ z)) h
        simp only [map_sum, map_smul, map_zero] at this
        rw [← this]
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [hψ x hx, smul_smul]
      have h2 : ∑ x ∈ s, (a x * (φ x - φ (c m))) • x = 0 := by
        have : ∑ x ∈ s, (a x * φ x) • x - φ (c m) • ∑ x ∈ s, a x • x
            = ∑ x ∈ s, (a x * (φ x - φ (c m))) • x := by
          rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [mul_sub, sub_smul, smul_smul, mul_comm (φ (c m))]
        rw [← this, h1, h, smul_zero, sub_zero]
      have hsub : s.erase (c m) ⊂ s := Finset.erase_ssubset hx
      have h3 : ∑ x ∈ s.erase (c m), (a x * (φ x - φ (c m))) • x = 0 := by
        rw [← Finset.add_sum_erase s _ hx] at h2
        simpa using h2
      have := ih _ hsub (fun x hx' => hs x (Finset.mem_of_mem_erase hx'))
        (fun x => a x * (φ x - φ (c m))) h3 y (Finset.mem_erase.mpr ⟨hyx, hy⟩)
      rcases mul_eq_zero.mp this with h0 | h0
      · exact hay h0
      · exact hφ (sub_eq_zero.mp h0).symm
    · push Not at hsing
      have : ∑ x ∈ s, a x • x = a (c m) • c m := by
        refine Finset.sum_eq_single_of_mem _ hx fun y hy hyx => ?_
        rw [hsing y hy hyx, zero_smul]
      rw [this] at h
      exact hc m ((smul_eq_zero.mp h).resolve_left hax)

end Field


section Generic

variable {R : Type u} [CommRing R] [IsDomain R]

/-- Scalars extended to the fraction field. -/
noncomputable abbrev phi : AddMonoidAlgebra R M →+* AddMonoidAlgebra (FractionRing R) M :=
  AddMonoidAlgebra.mapRingHom M (algebraMap R (FractionRing R))

lemma phi_coeff (f : AddMonoidAlgebra R M) (m : M) :
    (phi (M := M) f).coeff m = algebraMap R (FractionRing R) (f.coeff m) := by
  simp [phi, AddMonoidAlgebra.coeff_mapRingHom]

lemma phi_injective : Function.Injective (phi (R := R) (M := M)) := by
  intro f g h
  ext m
  have := congrArg (fun x : AddMonoidAlgebra (FractionRing R) M => x.coeff m) h
  simp only [phi_coeff] at this
  exact IsFractionRing.injective R (FractionRing R) this

lemma phi_add_smul (a b : R) (f g : AddMonoidAlgebra R M)
    (x y : AddMonoidAlgebra (FractionRing R) M)
    (hf : phi f = algebraMap R (FractionRing R) a • x)
    (hg : phi g = algebraMap R (FractionRing R) b • y) :
    phi (b • f + a • g) = algebraMap R (FractionRing R) (a * b) • (x + y) := by
  have e : ∀ (c : R) (w : AddMonoidAlgebra R M), phi (c • w) = algebraMap R (FractionRing R) c • phi w := by
    intro c w
    ext m
    simp [Algebra.smul_def]
  rw [map_add, e, e, hf, hg, smul_smul, smul_smul, smul_add, map_mul, mul_comm (algebraMap R _ b)]

lemma exists_clear (g : AddMonoidAlgebra (FractionRing R) M) :
    ∃ a : R, a ≠ 0 ∧ ∃ g' : AddMonoidAlgebra R M, phi g' = algebraMap R (FractionRing R) a • g := by
  induction g using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
  | add f g hf hg =>
    obtain ⟨a, ha, f', hf'⟩ := hf
    obtain ⟨b, hb, g', hg'⟩ := hg
    exact ⟨a * b, mul_ne_zero ha hb, _, phi_add_smul a b f' g' f g hf' hg'⟩
  | single m k =>
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := R) k
    have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
    refine ⟨y, hy0, AddMonoidAlgebra.single m x, ?_⟩
    have hy' : algebraMap R (FractionRing R) y ≠ 0 := by simpa using hy0
    simp only [phi, AddMonoidAlgebra.mapRingHom_single, AddMonoidAlgebra.smul_single, smul_eq_mul]
    rw [mul_div_cancel₀ _ hy']

lemma exists_mul_mem_of_mem_map (J : Ideal (AddMonoidAlgebra R M))
    {x : AddMonoidAlgebra (FractionRing R) M} (hx : x ∈ J.map (phi (R := R) (M := M))) :
    ∃ a : R, a ≠ 0 ∧ ∃ x' ∈ J, phi x' = algebraMap R (FractionRing R) a • x := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨1, one_ne_zero, y, hy, by simp⟩
  · exact ⟨1, one_ne_zero, 0, J.zero_mem, by simp⟩
  · rintro u v - - ⟨a, ha, u', hu, hu'⟩ ⟨b, hb, v', hv, hv'⟩
    exact ⟨a * b, mul_ne_zero ha hb, b • u' + a • v',
      J.add_mem (Submodule.smul_of_tower_mem _ b hu) (Submodule.smul_of_tower_mem _ a hv),
      phi_add_smul a b u' v' u v hu' hv'⟩
  · rintro g u - ⟨a, ha, u', hu, hu'⟩
    obtain ⟨b, hb, g', hg'⟩ := exists_clear g
    refine ⟨b * a, mul_ne_zero hb ha, g' * u', J.mul_mem_left _ hu, ?_⟩
    rw [map_mul, hg', hu', smul_eq_mul, smul_mul_smul_comm, map_mul]

/-- The product property of the characters killing `I`, over the fraction field. -/
lemma hmul_field (I : Ideal (AddMonoidAlgebra R M))
    (hmul : ∀ (A : Type u) [CommRing A] [Algebra R A] (g h : Multiplicative M →* A),
      (∀ f ∈ I, AddMonoidAlgebra.lift R A M g f = 0) →
      (∀ f ∈ I, AddMonoidAlgebra.lift R A M h f = 0) →
      ∀ f ∈ I, AddMonoidAlgebra.lift R A M (g * h) f = 0)
    (T : Type u) [CommRing T] [Algebra (FractionRing R) T] (g h : Multiplicative M →* T)
    (hg : ∀ f ∈ I.map (phi (R := R) (M := M)), AddMonoidAlgebra.lift (FractionRing R) T M g f = 0)
    (hh : ∀ f ∈ I.map (phi (R := R) (M := M)), AddMonoidAlgebra.lift (FractionRing R) T M h f = 0) :
    ∀ f ∈ I.map (phi (R := R) (M := M)), AddMonoidAlgebra.lift (FractionRing R) T M (g * h) f = 0 := by
  letI algT : Algebra R T := ((algebraMap (FractionRing R) T).comp
    (algebraMap R (FractionRing R))).toAlgebra
  haveI : IsScalarTower R (FractionRing R) T := ⟨fun a b x => by
    have e : ∀ y : T, a • y = (algebraMap R (FractionRing R) a) • y := fun y => by
      rw [Algebra.smul_def a y, Algebra.smul_def (algebraMap R (FractionRing R) a) y]
      rfl
    rw [e, smul_smul, Algebra.smul_def a b]⟩
  have down : ∀ u : Multiplicative M →* T,
      (∀ f ∈ I.map (phi (R := R) (M := M)), AddMonoidAlgebra.lift (FractionRing R) T M u f = 0) →
        ∀ f ∈ I, AddMonoidAlgebra.lift R T M u f = 0 := by
    intro u hu f hf
    rw [← AddMonoidAlgebra.lift_mapRingHom_algebraMap (S := FractionRing R)]
    exact hu _ (Ideal.mem_map_of_mem _ hf)
  have hR := hmul T g h (down g hg) (down h hh)
  have : I.map (phi (R := R) (M := M)) ≤
      RingHom.ker (AddMonoidAlgebra.lift (FractionRing R) T M (g * h)).toRingHom := by
    refine Ideal.map_le_iff_le_comap.mpr fun x hx => ?_
    change AddMonoidAlgebra.lift (FractionRing R) T M (g * h)
      (AddMonoidAlgebra.mapRingHom M (algebraMap R (FractionRing R)) x) = 0
    rw [AddMonoidAlgebra.lift_mapRingHom_algebraMap]
    exact hR x hx
  exact fun f hf => this hf

/-- **The generic stabilizer.** See the module docstring. The hypotheses say that the characters
killing `I` contain `1` and are closed under products. -/
theorem exists_stab_subgroup [IsNoetherianRing R] [AddMonoid.FG M]
    (I : Ideal (AddMonoidAlgebra R M))
    (h1 : ∀ f ∈ I, AddMonoidAlgebra.lift R (FractionRing R) M 1 f = 0)
    (hmul : ∀ (A : Type u) [CommRing A] [Algebra R A] (g h : Multiplicative M →* A),
      (∀ f ∈ I, AddMonoidAlgebra.lift R A M g f = 0) →
      (∀ f ∈ I, AddMonoidAlgebra.lift R A M h f = 0) →
      ∀ f ∈ I, AddMonoidAlgebra.lift R A M (g * h) f = 0) :
    ∃ (s : R) (_ : s ≠ 0) (Z : AddSubgroup M), ∀ (A : Type u) [CommRing A] [Algebra R A],
      IsUnit (algebraMap R A s) → ∀ h : Multiplicative M →* A,
        (∀ f ∈ I, AddMonoidAlgebra.lift R A M h f = 0) ↔
          ∀ z ∈ Z, h (Multiplicative.ofAdd z) = 1 := by
  classical
  let k := FractionRing R
  let Ik : Ideal (AddMonoidAlgebra k M) := I.map phi
  have hkill : ∀ (A : Type u) [CommRing A] [Algebra k A] [Algebra R A] [IsScalarTower R k A]
      (h : Multiplicative M →* A),
      (∀ f ∈ I, AddMonoidAlgebra.lift R A M h f = 0) →
        ∀ f ∈ Ik, AddMonoidAlgebra.lift k A M h f = 0 := by
    intro A _ _ _ _ h hI f hf
    have : Ik ≤ RingHom.ker (AddMonoidAlgebra.lift k A M h).toRingHom := by
      refine Ideal.map_le_iff_le_comap.mpr fun x hx => ?_
      change AddMonoidAlgebra.lift k A M h (AddMonoidAlgebra.mapRingHom M (algebraMap R k) x) = 0
      rw [AddMonoidAlgebra.lift_mapRingHom_algebraMap]
      exact hI x hx
    exact this hf
  have hkillR : ∀ (A : Type u) [CommRing A] [Algebra k A] [Algebra R A] [IsScalarTower R k A]
      (h : Multiplicative M →* A),
      (∀ f ∈ Ik, AddMonoidAlgebra.lift k A M h f = 0) →
        ∀ f ∈ I, AddMonoidAlgebra.lift R A M h f = 0 := by
    intro A _ _ _ _ h hI f hf
    rw [← AddMonoidAlgebra.lift_mapRingHom_algebraMap (S := k)]
    exact hI _ (Ideal.mem_map_of_mem _ hf)
  let A0 := AddMonoidAlgebra k M ⧸ Ik
  let q : AddMonoidAlgebra k M →ₐ[k] A0 := Ideal.Quotient.mkₐ k Ik
  let c : Multiplicative M →* A0 :=
    (q : AddMonoidAlgebra k M →* A0).comp (AddMonoidAlgebra.of k M)
  have hqlift : AddMonoidAlgebra.lift k A0 M c = q := by
    ext m
    simp [c, AddMonoidAlgebra.lift_single]
  have hq0 : ∀ f ∈ Ik, q f = 0 := fun f hf => Ideal.Quotient.eq_zero_iff_mem.mpr hf
  have hne : Nontrivial A0 := by
    refine Ideal.Quotient.nontrivial_iff.mpr fun htop => ?_
    have hK := hkill k (1 : Multiplicative M →* k) h1
    have := hK 1 (htop ▸ Submodule.mem_top)
    simp at this
  let T := A0 ⊗[k] A0
  let il : A0 →ₐ[k] T := Algebra.TensorProduct.includeLeft
  let ir : A0 →ₐ[k] T := Algebra.TensorProduct.includeRight
  let gl : Multiplicative M →* T := (il : A0 →* T).comp c
  let gr : Multiplicative M →* T := (ir : A0 →* T).comp c
  have hlift : ∀ i : A0 →ₐ[k] T, ∀ f ∈ Ik,
      AddMonoidAlgebra.lift k T M ((i : A0 →* T).comp c) f = 0 := by
    intro i f hf
    have : AddMonoidAlgebra.lift k T M ((i : A0 →* T).comp c) = i.comp q := by
      ext m
      simp [c, AddMonoidAlgebra.lift_single]
    rw [this, AlgHom.comp_apply, hq0 f hf, map_zero]
  have hD : ∀ f ∈ Ik, AddMonoidAlgebra.lift k T M (gl * gr) f = 0 :=
    hmul_field I hmul T gl gr (hlift il) (hlift ir)
  let Δa : A0 →ₐ[k] T := Ideal.Quotient.liftₐ Ik (AddMonoidAlgebra.lift k T M (gl * gr)) hD
  have hΔ : ∀ m : M, Δa (c (Multiplicative.ofAdd m)) =
      c (Multiplicative.ofAdd m) ⊗ₜ[k] c (Multiplicative.ofAdd m) := by
    intro m
    have : c (Multiplicative.ofAdd m) = q (AddMonoidAlgebra.single m 1) := by
      simp [c]
    rw [this]
    change AddMonoidAlgebra.lift k T M (gl * gr) (AddMonoidAlgebra.single m 1) = _
    rw [AddMonoidAlgebra.lift_single, one_smul, ← this]
    change (_ ⊗ₜ[k] (1 : A0)) * ((1 : A0) ⊗ₜ[k] _) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hc0 : ∀ m : M, c (Multiplicative.ofAdd m) ≠ 0 := by
    intro m h0
    have hu : c (Multiplicative.ofAdd m) * c (Multiplicative.ofAdd (-m)) = 1 := by
      rw [← map_mul, ← ofAdd_add, add_neg_cancel, ofAdd_zero, map_one]
    rw [h0, zero_mul] at hu
    exact zero_ne_one hu
  let Z : AddSubgroup M :=
    { carrier := {z | c (Multiplicative.ofAdd z) = 1}
      add_mem' := fun {a b} ha hb => by
        change c (Multiplicative.ofAdd (a + b)) = 1
        rw [ofAdd_add, map_mul, show c _ = 1 from ha, show c _ = 1 from hb, one_mul]
      zero_mem' := by
        change c (Multiplicative.ofAdd 0) = 1
        rw [ofAdd_zero, map_one]
      neg_mem' := fun {a} ha => by
        change c (Multiplicative.ofAdd (-a)) = 1
        have hu : c (Multiplicative.ofAdd a) * c (Multiplicative.ofAdd (-a)) = 1 := by
          rw [← map_mul, ← ofAdd_add, add_neg_cancel, ofAdd_zero, map_one]
        rwa [show c (Multiplicative.ofAdd a) = 1 from ha, one_mul] at hu }
  have hZmem : ∀ z, z ∈ Z ↔ c (Multiplicative.ofAdd z) = 1 := fun _ => Iff.rfl
  let J : Ideal (AddMonoidAlgebra R M) :=
    Ideal.span ((fun z : M => AddMonoidAlgebra.single z (1 : R) - 1) '' (Z : Set M))
  have hJk : ∀ z ∈ Z, (AddMonoidAlgebra.single z (1 : k) - 1) ∈ J.map phi := by
    intro z hz
    have : AddMonoidAlgebra.single z (1 : k) - 1 = phi (AddMonoidAlgebra.single z (1 : R) - 1) := by
      simp [phi, map_sub, AddMonoidAlgebra.mapRingHom_single]
    rw [this]
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨z, hz, rfl⟩)
  have hzI : ∀ z ∈ Z, (AddMonoidAlgebra.single z (1 : k) - 1) ∈ Ik := by
    intro z hz
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change q _ = 0
    rw [map_sub, map_one, sub_eq_zero]
    have : q (AddMonoidAlgebra.single z 1) = c (Multiplicative.ofAdd z) := by simp [c]
    rw [this]
    exact hz
  -- a section of `M → M/Z`
  let σ : M → M := fun m => Quotient.out (QuotientAddGroup.mk (s := Z) m)
  have hσ : ∀ m, -m + σ m ∈ Z := fun m =>
    QuotientAddGroup.eq.mp (Quotient.out_eq (QuotientAddGroup.mk (s := Z) m)).symm
  have hcσ : ∀ m, c (Multiplicative.ofAdd (σ m)) = c (Multiplicative.ofAdd m) := by
    intro m
    have h := (hZmem _).mp (hσ m)
    have e : Multiplicative.ofAdd (σ m) = Multiplicative.ofAdd m * Multiplicative.ofAdd (-m + σ m) := by
      rw [← ofAdd_add]
      congr 1
      abel
    rw [e, map_mul, h, mul_one]
  have hJI : J.map phi ≤ Ik := by
    refine Ideal.map_le_iff_le_comap.mpr ?_
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨z, hz, rfl⟩
    change phi _ ∈ Ik
    have : phi (AddMonoidAlgebra.single z (1 : R) - 1) = AddMonoidAlgebra.single z (1 : k) - 1 := by
      simp [phi, map_sub, AddMonoidAlgebra.mapRingHom_single]
    rw [this]
    exact hzI z hz
  have hdom : ∀ f : AddMonoidAlgebra k M, f - AddMonoidAlgebra.mapDomain σ f ∈ J.map phi := by
    intro f
    induction f using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add f g hf hg =>
      have := (J.map phi).add_mem hf hg
      rwa [show f - AddMonoidAlgebra.mapDomain σ f + (g - AddMonoidAlgebra.mapDomain σ g) =
        f + g - AddMonoidAlgebra.mapDomain σ (f + g) by
          rw [AddMonoidAlgebra.mapDomain_add]; abel] at this
    | single m a =>
      rw [AddMonoidAlgebra.mapDomain_single]
      have e : AddMonoidAlgebra.single m a - AddMonoidAlgebra.single (σ m) a =
          (-AddMonoidAlgebra.single m a) * (AddMonoidAlgebra.single (-m + σ m) (1 : k) - 1) := by
        rw [neg_mul, mul_sub, mul_one, AddMonoidAlgebra.single_mul_single, mul_one]
        rw [show m + (-m + σ m) = σ m by abel]
        abel
      rw [e]
      exact (J.map phi).mul_mem_left _ (hJk _ (hσ m))
  have hIJ : Ik ≤ J.map phi := by
    intro f hf
    set g := AddMonoidAlgebra.mapDomain σ f with hg
    have hgI : g ∈ Ik := by
      have := Ik.sub_mem hf (hJI (hdom f))
      rwa [sub_sub_cancel] at this
    have hg0 : g = 0 := by
      let c' : M → A0 := fun m => c (Multiplicative.ofAdd m)
      let S := g.coeff.support
      have hS : ∀ x ∈ S, ∃ m, x = σ m := by
        intro x hx
        have := Finsupp.mapDomain_support (f := σ) (s := f.coeff) (by simpa [S, hg] using hx)
        obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp this
        exact ⟨m, rfl⟩
      have hinj : Set.InjOn c' S := by
        intro x hx y hy hxy
        obtain ⟨m, rfl⟩ := hS x hx
        obtain ⟨n, rfl⟩ := hS y hy
        have hmn : c' m = c' n := by simpa [c', hcσ] using hxy
        have hz : -m + n ∈ Z := by
          rw [hZmem, ofAdd_add, map_mul]
          have hu : c (Multiplicative.ofAdd (-m)) * c' m = 1 := by
            simp only [c']
            rw [← map_mul, ← ofAdd_add, neg_add_cancel, ofAdd_zero, map_one]
          rw [show c (Multiplicative.ofAdd n) = c' m from hmn.symm, hu]
        exact congrArg Quotient.out (QuotientAddGroup.eq.mpr hz)
      have hsum : ∑ y ∈ S.image c', g.coeff (Function.invFunOn c' S y) • y = 0 := by
        rw [Finset.sum_image hinj]
        have h0 : q g = 0 := hq0 g hgI
        rw [← hqlift, AddMonoidAlgebra.lift_apply] at h0
        rw [← h0]
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [hinj.leftInvOn_invFunOn hx]
      have := relation_eq_zero (K := k) (A := A0) (M := M) Δa.toLinearMap c' hΔ hc0 (S.image c')
        (fun x hx => by
          obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
          exact ⟨y, rfl⟩) _ hsum
      ext x
      by_contra hx
      have hxS : x ∈ S := Finsupp.mem_support_iff.mpr hx
      have h2 := this (c' x) (Finset.mem_image_of_mem _ hxS)
      rw [hinj.leftInvOn_invFunOn hxS] at h2
      exact hx h2
    have h3 : f - g ∈ J.map phi := hdom f
    rwa [hg0, sub_zero] at h3
  haveI : Algebra.FiniteType R (AddMonoidAlgebra R M) := AddMonoidAlgebra.finiteType_of_fg R M
  haveI : IsNoetherianRing (AddMonoidAlgebra R M) := Algebra.FiniteType.isNoetherianRing R _
  obtain ⟨F, hF⟩ := (IsNoetherian.noetherian I : I.FG)
  haveI : Module.Finite ℤ M := Module.Finite.iff_addGroup_fg.mpr (AddGroup.fg_iff_addMonoid_fg.mpr inferInstance)
  obtain ⟨Tg, hTg⟩ := (IsNoetherian.noetherian Z.toIntSubmodule : Z.toIntSubmodule.FG)
  have hphi : ∀ (a : R) (w : AddMonoidAlgebra R M),
      phi (a • w) = algebraMap R (FractionRing R) a • phi w := by
    intro a w
    ext m
    simp [Algebra.smul_def]
  have hF1 : ∀ f ∈ F, ∃ a : R, a ≠ 0 ∧ a • f ∈ J := by
    intro f hf
    have hfI : f ∈ I := hF ▸ Ideal.subset_span hf
    obtain ⟨a, ha, x, hx, hxe⟩ := exists_mul_mem_of_mem_map J (hIJ (Ideal.mem_map_of_mem phi hfI))
    refine ⟨a, ha, ?_⟩
    rwa [show a • f = x from phi_injective (by rw [hphi, hxe])]
  have hT1 : ∀ z ∈ Tg, ∃ a : R, a ≠ 0 ∧ a • (AddMonoidAlgebra.single z (1 : R) - 1) ∈ I := by
    intro z hz
    have hzZ : z ∈ Z := by
      have : z ∈ Z.toIntSubmodule := hTg ▸ Submodule.subset_span hz
      exact this
    obtain ⟨a, ha, x, hx, hxe⟩ := exists_mul_mem_of_mem_map I (hzI z hzZ)
    refine ⟨a, ha, ?_⟩
    have e : phi (AddMonoidAlgebra.single z (1 : R) - 1) = AddMonoidAlgebra.single z (1 : k) - 1 := by
      simp [phi, map_sub, AddMonoidAlgebra.mapRingHom_single]
    rwa [show a • (AddMonoidAlgebra.single z (1 : R) - 1) = x from
      phi_injective (by rw [hphi, hxe, e])]
  have common : ∀ {ι : Type u} (L : Ideal (AddMonoidAlgebra R M)) (G : Finset ι)
      (v : ι → AddMonoidAlgebra R M), (∀ i ∈ G, ∃ a : R, a ≠ 0 ∧ a • v i ∈ L) →
      ∃ s : R, s ≠ 0 ∧ ∀ i ∈ G, s • v i ∈ L := by
    intro ι L G v
    induction G using Finset.induction_on with
    | empty => exact fun _ => ⟨1, one_ne_zero, by simp⟩
    | insert i G _ ih =>
      intro h
      obtain ⟨s, hs, hsG⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
      obtain ⟨a, ha, hai⟩ := h i (Finset.mem_insert_self _ _)
      refine ⟨a * s, mul_ne_zero ha hs, fun j hj => ?_⟩
      rcases Finset.mem_insert.mp hj with rfl | hj
      · rw [mul_comm, mul_smul]
        exact Submodule.smul_of_tower_mem _ s hai
      · rw [mul_smul]
        exact Submodule.smul_of_tower_mem _ a (hsG j hj)
  obtain ⟨s1, hs1, h1F⟩ := common J F id hF1
  obtain ⟨s2, hs2, h2T⟩ := common I Tg (fun z => AddMonoidAlgebra.single z (1 : R) - 1) hT1
  refine ⟨s1 * s2, mul_ne_zero hs1 hs2, Z, fun A _ _ hu h => ⟨fun hk z hz => ?_, fun hz => ?_⟩⟩
  · let H : AddSubgroup M :=
      { carrier := {m | h (Multiplicative.ofAdd m) = 1}
        add_mem' := fun {a b} ha hb => by
          change h (Multiplicative.ofAdd (a + b)) = 1
          rw [ofAdd_add, map_mul, show h _ = 1 from ha, show h _ = 1 from hb, one_mul]
        zero_mem' := by
          change h (Multiplicative.ofAdd 0) = 1
          rw [ofAdd_zero, map_one]
        neg_mem' := fun {a} ha => by
          change h (Multiplicative.ofAdd (-a)) = 1
          have e : h (Multiplicative.ofAdd a) * h (Multiplicative.ofAdd (-a)) = 1 := by
            rw [← map_mul, ← ofAdd_add, add_neg_cancel, ofAdd_zero, map_one]
          rwa [show h (Multiplicative.ofAdd a) = 1 from ha, one_mul] at e }
    have hsp : Submodule.span ℤ (Tg : Set M) ≤ H.toIntSubmodule := by
      refine Submodule.span_le.mpr fun x hx => ?_
      have h0 := hk _ (h2T x hx)
      rw [map_smul, map_sub, map_one, AddMonoidAlgebra.lift_single, one_smul, Algebra.smul_def] at h0
      have hu2 : IsUnit (algebraMap R A s2) :=
        isUnit_of_mul_isUnit_right (by rwa [← map_mul])
      have := (hu2.mul_right_eq_zero).mp h0
      exact sub_eq_zero.mp this
    exact hsp (hTg ▸ hz : z ∈ Submodule.span ℤ (Tg : Set M))
  · have hJ : J ≤ RingHom.ker (AddMonoidAlgebra.lift R A M h).toRingHom := by
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨z, hz', rfl⟩
      change AddMonoidAlgebra.lift R A M h _ = 0
      rw [map_sub, map_one, AddMonoidAlgebra.lift_single, one_smul, hz z hz', sub_self]
    have hI' : I ≤ RingHom.ker (AddMonoidAlgebra.lift R A M h).toRingHom := by
      rw [← hF]
      refine Ideal.span_le.mpr fun f hf => ?_
      have h0 : AddMonoidAlgebra.lift R A M h (s1 • f) = 0 := hJ (h1F f hf)
      rw [map_smul, Algebra.smul_def] at h0
      have hu1 : IsUnit (algebraMap R A s1) :=
        isUnit_of_mul_isUnit_left (by rwa [← map_mul])
      exact (hu1.mul_right_eq_zero).mp h0
    exact fun f hf => hI' hf

end Generic

end AlgMag.ChartStratum

#print axioms AlgMag.ChartStratum.exists_stab_subgroup
