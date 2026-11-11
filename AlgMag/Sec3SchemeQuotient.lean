/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.GroupTheory.Torsion
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.PullbackCarrier
import AlgMag.Sec3Intersections
import AlgMag.Sec12Topology
import AlgMag.AppendixA

/-!
# Proposition 3.32 (ii), Fact 3.34, Proposition 15.1 for schemes, with no atlas

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026) 126–201, §3 and §15. Schemes, proof repaired.

`X` is a scheme over an arbitrary `S`, `M` a finitely generated abelian group, `N`, `L` arbitrary magnets.
The printed structure is kept: a point of `(X^N)^L` is an equivariant `F : 𝔸(N)_T × 𝔸(L)_T → X`
(`AlgMag.iterEquivBi`), the map back is `f ↦ F = f ∘ m` with `m` the multiplication
(`AlgMag.iterOfInf`), and the claim is that it is bijective. Only the printed step *free action, fpqc
quotient* is replaced: the antidiagonal action is not free in general.

Let `A = R[N × L]`, graded by `(n, l) ↦ n - l`, with `A₀ = R[N ∩ L]`, and `m : Spec A → Spec A₀`.

1. **Reynolds.** A homogeneous ideal `I` with `I₀ ⊆ q`, maximal such, is the closed orbit over `q`
   (`AlgMag.SQ.exists_maximal_homIdeal`); adding a homogeneous element leaves `q`
   (`AlgMag.SQ.exists_inv_of_homog`).
2. **Saturated neighbourhood.** For `V` affine around the image of a point of the closed orbit, `F⁻¹(V)`
   contains `m⁻¹(D(h))`, `h ∉ q` (`AlgMag.SQ.exists_loc_of_torsionFree`, `AlgMag.SQ.exists_loc_of_tors`).
3. **Descent on `D(h)`.** `O(V) → A_h` lands in degree `0` (`AlgMag.SQ.exists_local`); glue
   (`AlgMag.SQ.exists_desc_of_loc`).
4. **Uniqueness.** `A₀ → A` is split (`AlgMag.SQ.IsSplit`, `AlgMag.SQ.uniq_of_isSplit`).

Step 2 needs care when `N^gp + L^gp` has torsion: then `F⁻¹(V)` need not be a union of `D(a)`, `a`
homogeneous, for the whole grading (`D(ℤ/p)` in characteristic `p` is not reduced). So the descent runs
in two stages (`AlgMag.SQ.exists_desc`): first the torsion-free quotient of the grading, by steps 1 to 3;
then the torsion part, where `A' → A₀` is integral hence closed, and two points of a fibre lie in one
orbit (`AlgMag.SQ.exists_twist`, characters extended by divisibility of `K^×`).

## Main results

* `AlgMag.SQ.exists_desc`, `AlgMag.SQ.desc_unique`: the descent, for `Spec R[P] → Spec R[ker δ]`.
* `AlgMag.existsUnique_toBi_affine`: Proposition 3.32 (ii), `T` affine.
* `AlgMag.prop332_scheme`: **Proposition 3.32 (ii)**, `T` arbitrary.
* `AlgMag.attractorImage_inf_of_eq_scheme`, `AlgMag.fact334_finite_scheme`: **Fact 3.34** for finite
  families, `X` a separated scheme.
* `AlgMag.prop151_scheme`: **Proposition 15.1**, `X` a separated scheme.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgMag.SQ

/-- A grading of `A` by `Γ`, as a coaction `A → A[Γ]`. -/
structure Coact (A Γ : Type u) [CommRing A] [AddCommGroup Γ] where
  /-- The coaction. -/
  σ : A →+* AddMonoidAlgebra A Γ
  sum_eq : ∀ y, ((σ y).coeff.sum fun _ a => a) = y
  hom : ∀ y d, σ ((σ y).coeff d) = AddMonoidAlgebra.single d ((σ y).coeff d)

variable {A Γ : Type u} [CommRing A] [AddCommGroup Γ] (c : Coact A Γ)

/-- The homogeneous component of degree `d`. -/
noncomputable def Coact.comp (d : Γ) (y : A) : A := (c.σ y).coeff d

/-- Homogeneous of degree `d`. -/
def Coact.IsHom (d : Γ) (y : A) : Prop := c.σ y = AddMonoidAlgebra.single d y

lemma Coact.comp_isHom (d : Γ) (y : A) : c.IsHom d (c.comp d y) := c.hom y d

lemma Coact.comp_add (d : Γ) (y z : A) : c.comp d (y + z) = c.comp d y + c.comp d z := by
  simp [Coact.comp]

lemma Coact.comp_self_of_isHom {d : Γ} {y : A} (h : c.IsHom d y) : c.comp d y = y := by
  have h' : c.σ y = AddMonoidAlgebra.single d y := h
  simp [Coact.comp, h']

lemma Coact.comp_mul_of_isHom {d : Γ} {a : A} (h : c.IsHom d a) (b : A) (e : Γ) :
    c.comp e (a * b) = a * c.comp (e - d) b := by
  have : c.σ (a * b) = AddMonoidAlgebra.single d a * c.σ b := by
    have h' : c.σ a = AddMonoidAlgebra.single d a := h
    rw [map_mul, h']
  rw [Coact.comp, this]
  have := AddMonoidAlgebra.coeff_single_mul_add (c.σ b) a d (e - d)
  rw [add_sub_cancel] at this
  exact this

/-- A prime (or any ideal) containing all components contains `y`. -/
lemma Coact.mem_of_comp_mem (I : Ideal A) (y : A) (h : ∀ d, c.comp d y ∈ I) : y ∈ I := by
  rw [← c.sum_eq y]
  exact Ideal.sum_mem _ fun d _ => h d

/-- Induction: all elements are sums of homogeneous elements. -/
lemma Coact.induction {p : A → Prop} (h0 : p 0) (hadd : ∀ a b, p a → p b → p (a + b))
    (hh : ∀ d a, c.IsHom d a → p a) (y : A) : p y := by
  rw [← c.sum_eq y]
  exact Finset.sum_induction _ p hadd h0 fun d _ => hh d _ (c.comp_isHom d y)

/-- The ring of invariants is described by a ring map `ι`. -/
structure Coact.IsInv {A₀ : Type u} [CommRing A₀] (ι : A₀ →+* A) : Prop where
  inj : Function.Injective ι
  range : ∀ y, c.IsHom 0 y ↔ y ∈ ι.range

variable {c} {A₀ : Type u} [CommRing A₀] {ι : A₀ →+* A}

lemma Coact.IsInv.comp_ι (hι : c.IsInv ι) (a : A₀) (b : A) (e : Γ) :
    c.comp e (ι a * b) = ι a * c.comp e b := by
  have := c.comp_mul_of_isHom ((hι.range (ι a)).2 ⟨a, rfl⟩) b e
  simpa using this

/-- The Reynolds operator. -/
noncomputable def Coact.IsInv.r (hι : c.IsInv ι) (y : A) : A₀ :=
  ((hι.range _).1 (c.comp_isHom 0 y)).choose

lemma Coact.IsInv.ι_r (hι : c.IsInv ι) (y : A) : ι (hι.r y) = c.comp 0 y :=
  ((hι.range _).1 (c.comp_isHom 0 y)).choose_spec

lemma Coact.IsInv.r_add (hι : c.IsInv ι) (y z : A) : hι.r (y + z) = hι.r y + hι.r z :=
  hι.inj (by simp [hι.ι_r, c.comp_add])

lemma Coact.IsInv.r_mul (hι : c.IsInv ι) (a : A₀) (y : A) : hι.r (ι a * y) = a * hι.r y :=
  hι.inj (by simp [hι.ι_r, hι.comp_ι])

lemma Coact.IsInv.r_one (hι : c.IsInv ι) : hι.r 1 = 1 :=
  hι.inj (by
    have h1 : c.IsHom 0 (1 : A) := (hι.range 1).2 ⟨1, map_one ι⟩
    rw [hι.ι_r, c.comp_self_of_isHom h1, map_one])

/-- Step (4): `R[N ∩ L] → R[N × L]` is split. -/
structure IsSplit (ι : A₀ →+* A) (r : A → A₀) : Prop where
  add : ∀ y z, r (y + z) = r y + r z
  mul : ∀ a y, r (ι a * y) = a * r y
  one : r 1 = 1

lemma Coact.IsInv.isSplit (hι : c.IsInv ι) : IsSplit ι hι.r := ⟨hι.r_add, hι.r_mul, hι.r_one⟩

lemma IsSplit.injective {r : A → A₀} (h : IsSplit ι r) : Function.Injective ι := by
  intro a b e
  have key : ∀ x, r (ι x) = x := fun x => by
    have := h.mul x 1
    rwa [mul_one, h.one, mul_one] at this
  rw [← key a, e, key b]

/-- Lying over for a split map. -/
lemma IsSplit.exists_prime {r : A → A₀} (hs : IsSplit ι r) (q : PrimeSpectrum A₀) :
    ∃ p : PrimeSpectrum A, PrimeSpectrum.comap ι p = q := by
  have hmem : ∀ y ∈ Ideal.map ι q.asIdeal, ∀ b, r (b * y) ∈ q.asIdeal := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      intro b
      rw [mul_comm, hs.mul]
      exact Ideal.mul_mem_right _ _ ha
    | zero =>
      intro b
      have h0 : r 0 = 0 := by simpa using hs.add 0 0
      rw [mul_zero, h0]; exact Ideal.zero_mem _
    | add x z _ _ hx hz =>
      intro b
      rw [mul_add, hs.add]; exact Ideal.add_mem _ (hx b) (hz b)
    | smul c x _ hx =>
      intro b
      rw [smul_eq_mul, ← mul_assoc]; exact hx _
  have hdisj : Disjoint ((Ideal.map ι q.asIdeal : Ideal A) : Set A)
      (q.asIdeal.primeCompl.map ι : Submonoid A) := by
    rw [Set.disjoint_left]
    rintro _ h1 ⟨s, hs', rfl⟩
    have := hmem _ h1 1
    rw [one_mul] at this
    have h2 := hs.mul s 1
    rw [mul_one, hs.one, mul_one] at h2
    rw [h2] at this
    exact hs' this
  obtain ⟨p, hp, hle, hd⟩ := Ideal.exists_le_prime_disjoint _ _ hdisj
  refine ⟨⟨p, hp⟩, PrimeSpectrum.ext (le_antisymm ?_ ?_)⟩
  · intro a ha
    by_contra hna
    exact Set.disjoint_left.1 hd ha ⟨a, hna, rfl⟩
  · exact Ideal.map_le_iff_le_comap.1 hle

/-! ### Step (1): Reynolds, and the closed orbit -/

/-- A homogeneous ideal. -/
def Coact.IsHomIdeal (c : Coact A Γ) (I : Ideal A) : Prop := ∀ y ∈ I, ∀ d, c.comp d y ∈ I

/-- The closed orbit of a fibre: a maximal homogeneous ideal with invariants in `q`. -/
lemma exists_maximal_homIdeal (c : Coact A Γ) (hι : Function.Injective ι) (q : Ideal A₀) :
    ∃ I : Ideal A, c.IsHomIdeal I ∧ (∀ a, ι a ∈ I → a ∈ q) ∧
      ∀ J, c.IsHomIdeal J → I < J → ∃ a, ι a ∈ J ∧ a ∉ q := by
  let s : Set (Ideal A) := {I | c.IsHomIdeal I ∧ ∀ a, ι a ∈ I → a ∈ q}
  have h0 : (⊥ : Ideal A) ∈ s := by
    refine ⟨fun y hy d => ?_, fun a ha => ?_⟩
    · rw [Ideal.mem_bot] at hy ⊢
      simp [hy, Coact.comp]
    · rw [Ideal.mem_bot] at ha
      rw [hι (ha.trans (map_zero ι).symm)]
      exact q.zero_mem
  obtain ⟨I, -, hI⟩ := zorn_le_nonempty₀ s (fun C hC hch y hy => by
    have hne : C.Nonempty := ⟨y, hy⟩
    have hdir : DirectedOn (· ≤ ·) C := hch.directedOn
    refine ⟨sSup C, ⟨fun z hz d => ?_, fun a ha => ?_⟩, fun z hz => le_sSup hz⟩
    · obtain ⟨K, hK, hzK⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 hz
      exact (Submodule.mem_sSup_of_directed hne hdir).2 ⟨K, hK, (hC hK).1 z hzK d⟩
    · obtain ⟨K, hK, hzK⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 ha
      exact (hC hK).2 a hzK) ⊥ h0
  refine ⟨I, hI.prop.1, hI.prop.2, fun J hJ hlt => ?_⟩
  by_contra hcon
  push Not at hcon
  exact absurd (hI.le_of_ge ⟨hJ, hcon⟩ hlt.le) (not_le_of_gt hlt)

/-- The element `h` of step (2). -/
lemma exists_inv_of_homog (hι : c.IsInv ι) {q : Ideal A₀} {I : Ideal A} (hI : c.IsHomIdeal I)
    (hIq : ∀ a, ι a ∈ I → a ∈ q)
    (hmax : ∀ J, c.IsHomIdeal J → I < J → ∃ a, ι a ∈ J ∧ a ∉ q) {d : Γ} {a : A}
    (ha : c.IsHom d a) (haI : a ∉ I) :
    ∃ h : A₀, h ∉ q ∧ ∃ b, ι h = a * b := by
  have hJ : c.IsHomIdeal (I ⊔ Ideal.span {a}) := by
    intro y hy e
    obtain ⟨i, hi, z, hz, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    rw [c.comp_add, mul_comm b a, c.comp_mul_of_isHom ha]
    exact Ideal.add_mem _ (Ideal.mem_sup_left (hI i hi e))
      (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self a)))
  have hlt : I < I ⊔ Ideal.span {a} :=
    lt_of_le_of_ne le_sup_left fun e => haI (e ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self a))
  obtain ⟨x, hx, hxq⟩ := hmax _ hJ hlt
  obtain ⟨i, hi, z, hz, hiz⟩ := Submodule.mem_sup.1 hx
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  refine ⟨x - hι.r i, fun hmem => hxq ?_, c.comp (0 - d) b, ?_⟩
  · have hri : hι.r i ∈ q := hIq _ (by rw [hι.ι_r]; exact hI i hi 0)
    simpa using q.add_mem hmem hri
  · have h1 : c.comp 0 (ι x) = ι x :=
      c.comp_self_of_isHom ((hι.range _).2 ⟨x, rfl⟩)
    rw [map_sub, hι.ι_r, ← h1, ← hiz, c.comp_add, mul_comm b a, c.comp_mul_of_isHom ha]
    ring

/-! ### Stage A: torsion-free grading -/

/-- The point of the orbit of `p`. -/
noncomputable def orbitHom (c : Coact A Γ) (p : Ideal A) :
    A →+* AddMonoidAlgebra (A ⧸ p) Γ :=
  (AddMonoidAlgebra.mapRingHom Γ (Ideal.Quotient.mk p)).comp c.σ

/-- A stable open is a union of `D(a)`, `a` homogeneous, for a torsion-free grading. The orbit of `p`
has a generic point, whose image in `X` is that of `p`. -/
lemma comp_mem_of_stable [UniqueSums Γ] (c : Coact A Γ) (U : Set (PrimeSpectrum A))
    (hU : ∀ (p : PrimeSpectrum A) [IsDomain (AddMonoidAlgebra (A ⧸ p.asIdeal) Γ)], p ∉ U →
      PrimeSpectrum.comap (orbitHom c p.asIdeal)
        ⟨⊥, Ideal.isPrime_bot⟩ ∉ U) {a₀ : A} (ha : ∀ p : PrimeSpectrum A, a₀ ∉ p.asIdeal → p ∈ U)
    (d : Γ) (p : PrimeSpectrum A) (hp : p ∉ U) : c.comp d a₀ ∈ p.asIdeal := by
  haveI : IsDomain (AddMonoidAlgebra (A ⧸ p.asIdeal) Γ) := inferInstance
  have h1 := hU p hp
  have h2 : a₀ ∈ (PrimeSpectrum.comap (orbitHom c p.asIdeal) ⟨⊥, Ideal.isPrime_bot⟩).asIdeal := by
    by_contra hn
    exact h1 (ha _ hn)
  have h3 : orbitHom c p.asIdeal a₀ = 0 := by
    simpa using h2
  have h4 := congrArg (fun z => z.coeff d) h3
  have h5 : Ideal.Quotient.mk p.asIdeal (c.comp d a₀) = 0 := by
    simpa [orbitHom, Coact.comp] using h4
  exact Ideal.Quotient.eq_zero_iff_mem.1 h5

/-! ### Stage B: torsion grading -/

/-- All degrees of nonzero homogeneous elements are torsion. -/
def Coact.IsTors (c : Coact A Γ) : Prop :=
  ∀ d a, c.IsHom d a → a ≠ 0 → ∃ n : ℕ, 0 < n ∧ n • d = 0

lemma Coact.IsHom.pow {d : Γ} {a : A} (h : c.IsHom d a) (n : ℕ) : c.IsHom (n • d) (a ^ n) := by
  have h' : c.σ a = AddMonoidAlgebra.single d a := h
  change c.σ (a ^ n) = _
  rw [map_pow, h', AddMonoidAlgebra.single_pow]

lemma Coact.IsHom.mul {d e : Γ} {a b : A} (h : c.IsHom d a) (h₂ : c.IsHom e b) :
    c.IsHom (d + e) (a * b) := by
  have h' : c.σ a = AddMonoidAlgebra.single d a := h
  have h₂' : c.σ b = AddMonoidAlgebra.single e b := h₂
  change c.σ (a * b) = _
  rw [map_mul, h', h₂', AddMonoidAlgebra.single_mul_single]

lemma isIntegral_of_isTors (hι : c.IsInv ι) (ht : c.IsTors) : ι.IsIntegral := by
  refine c.induction (p := fun y => ι.IsIntegralElem y) ?_ ?_ ?_
  · simpa using ι.isIntegralElem_map (x := 0)
  · exact fun a b ha hb => RingHom.IsIntegralElem.add ι ha hb
  · intro d a ha
    by_cases h0 : a = 0
    · rw [h0]; simpa using ι.isIntegralElem_map (x := 0)
    obtain ⟨n, hn, hd⟩ := ht d a ha h0
    have h1 := ha.pow n
    rw [hd] at h1
    obtain ⟨b, hb⟩ := (hι.range _).1 h1
    refine ⟨Polynomial.X ^ n - Polynomial.C b, Polynomial.monic_X_pow_sub_C b hn.ne', ?_⟩
    simp [hb]

/-- The evaluation `A[Γ] → K` of `φ` and a point `g` of `D(Γ)`. -/
noncomputable def twist {K : Type u} [CommRing K] (φ : A →+* K) (g : Multiplicative Γ →* K) :
    AddMonoidAlgebra A Γ →+* K :=
  AddMonoidAlgebra.liftNCRingHom φ g fun _ _ => Commute.all _ _

lemma twist_single {K : Type u} [CommRing K] (φ : A →+* K) (g : Multiplicative Γ →* K) (d : Γ)
    (a : A) : twist φ g (AddMonoidAlgebra.single d a) = φ a * g (Multiplicative.ofAdd d) := by
  simp [twist, AddMonoidAlgebra.liftNCRingHom, AddMonoidAlgebra.liftNC_single]

section Trans

variable {K : Type u} [Field K] [IsAlgClosed K] {φ φ' : A →+* K}

lemma ratio_eq (hι : c.IsInv ι) (ht : c.IsTors) (hφ : φ.comp ι = φ'.comp ι) {d : Γ} {a b : A}
    (ha : c.IsHom d a) (hb : c.IsHom d b) (ha0 : φ a ≠ 0) (hb0 : φ b ≠ 0) :
    φ' a * φ b = φ a * φ' b := by
  have hb' : b ≠ 0 := fun e => hb0 (by rw [e, map_zero])
  obtain ⟨n, hn, hd⟩ := ht d b hb hb'
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 : c.IsHom 0 (a * b ^ m) := by
    have := ha.mul (hb.pow m)
    rwa [show d + m • d = (m + 1) • d by rw [add_smul, one_smul, add_comm], hd] at this
  have h2 : c.IsHom 0 (b ^ (m + 1)) := by
    have := hb.pow (m + 1)
    rwa [hd] at this
  have hinv : ∀ y, c.IsHom 0 y → φ y = φ' y := by
    intro y hy
    obtain ⟨x, rfl⟩ := (hι.range y).1 hy
    exact congrArg (fun k => k x) hφ
  have e1 := hinv _ h1
  have e2 := hinv _ h2
  simp only [map_mul, map_pow] at e1 e2
  have hbm : φ b ^ m ≠ 0 := pow_ne_zero _ hb0
  apply mul_left_cancel₀ hbm
  calc φ b ^ m * (φ' a * φ b) = φ' a * φ b ^ (m + 1) := by ring
    _ = φ' a * φ' b ^ (m + 1) := by rw [e2]
    _ = (φ' a * φ' b ^ m) * φ' b := by ring
    _ = (φ a * φ b ^ m) * φ' b := by rw [e1]
    _ = φ b ^ m * (φ a * φ' b) := by ring

lemma map_eq_zero_of_inv (hι : c.IsInv ι) (ht : c.IsTors) (hφ : φ.comp ι = φ'.comp ι) {d : Γ} {a : A}
    (ha : c.IsHom d a) (ha0 : φ a = 0) : φ' a = 0 := by
  by_cases h0 : a = 0
  · rw [h0, map_zero]
  obtain ⟨n, hn, hd⟩ := ht d a ha h0
  have h1 := ha.pow n
  rw [hd] at h1
  obtain ⟨x, hx⟩ := (hι.range _).1 h1
  have := congrArg (fun k => k x) hφ
  simp only [RingHom.comp_apply, hx, map_pow, ha0, zero_pow hn.ne'] at this
  exact pow_eq_zero_iff hn.ne' |>.1 this.symm

/-- Step (2) for the torsion part: two points of `A` over the same point of `A₀` are in one orbit. -/
theorem exists_twist (hι : c.IsInv ι) (ht : c.IsTors) (hφ : φ.comp ι = φ'.comp ι) :
    ∃ g : Multiplicative Γ →* K, φ' = (twist φ g).comp c.σ := by
  classical
  have hinv0 : ∀ y, c.IsHom 0 y → φ y = φ' y := by
    intro y hy
    obtain ⟨x, rfl⟩ := (hι.range y).1 hy
    exact congrArg (fun k => k x) hφ
  have h1 : c.IsHom 0 (1 : A) := (hι.range 1).2 ⟨1, map_one ι⟩
  -- the support of `φ`
  let H : AddSubgroup Γ :=
    { carrier := {d | ∃ a, c.IsHom d a ∧ φ a ≠ 0}
      zero_mem' := ⟨1, h1, by simp⟩
      add_mem' := by
        rintro d e ⟨a, ha, ha0⟩ ⟨b, hb, hb0⟩
        exact ⟨a * b, ha.mul hb, by simp [ha0, hb0]⟩
      neg_mem' := by
        rintro d ⟨a, ha, ha0⟩
        have ha' : a ≠ 0 := fun e => ha0 (by rw [e, map_zero])
        obtain ⟨n, hn, hd⟩ := ht d a ha ha'
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        refine ⟨a ^ m, ?_, by rw [map_pow]; exact pow_ne_zero _ ha0⟩
        have := ha.pow m
        rwa [show m • d = -d from eq_neg_of_add_eq_zero_left (by
          rw [← hd, add_smul, one_smul])] at this }
  have hne' : ∀ {d a}, c.IsHom d a → φ a ≠ 0 → φ' a ≠ 0 := by
    intro d a ha ha0
    have ha' : a ≠ 0 := fun e => ha0 (by rw [e, map_zero])
    obtain ⟨n, hn, hd⟩ := ht d a ha ha'
    have h2 := ha.pow n
    rw [hd] at h2
    have := hinv0 _ h2
    simp only [map_pow] at this
    intro h
    rw [h, zero_pow hn.ne'] at this
    exact pow_ne_zero n ha0 this
  let w : H → A := fun d => d.2.choose
  have hw : ∀ d : H, c.IsHom d (w d) := fun d => d.2.choose_spec.1
  have hw0 : ∀ d : H, φ (w d) ≠ 0 := fun d => d.2.choose_spec.2
  let χ₀ : H → Kˣ := fun d => Units.mk0 (φ' (w d) / φ (w d)) (div_ne_zero (hne' (hw d) (hw0 d)) (hw0 d))
  have hχ₀ : ∀ (d : H) {a}, c.IsHom d a → φ a ≠ 0 → (χ₀ d : K) * φ a = φ' a := by
    intro d a ha ha0
    change φ' (w d) / φ (w d) * φ a = φ' a
    rw [div_mul_eq_mul_div, div_eq_iff (hw0 d), ratio_eq hι ht hφ (hw d) ha (hw0 d) ha0]
    ring
  let χ : H →+ Additive Kˣ := AddMonoidHom.mk' (fun d => Additive.ofMul (χ₀ d)) (by
    intro d e
    apply Additive.toMul.injective
    apply Units.ext
    have h3 := hχ₀ (d + e) ((hw d).mul (hw e)) (by simp [hw0])
    have h4 := hχ₀ d (hw d) (hw0 d)
    have h5 := hχ₀ e (hw e) (hw0 e)
    have hnz : φ (w d) * φ (w e) ≠ 0 := mul_ne_zero (hw0 d) (hw0 e)
    apply mul_right_cancel₀ hnz
    simp only [map_mul] at h3
    change (χ₀ (d + e) : K) * _ = (χ₀ d : K) * (χ₀ e : K) * _
    rw [h3, ← h4, ← h5]
    ring)
  -- extend to `Γ`
  haveI : DivisibleBy (Additive Kˣ) ℕ :=
    { div := fun x n => if hn : n = 0 then 0 else Additive.ofMul
        (Units.mk0 (Classical.choose (IsAlgClosed.exists_pow_nat_eq ((Additive.toMul x : Kˣ) : K)
          (Nat.pos_of_ne_zero hn))) (by
            intro h0
            have := Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq
              ((Additive.toMul x : Kˣ) : K) (Nat.pos_of_ne_zero hn))
            rw [h0, zero_pow hn] at this
            exact (Additive.toMul x).ne_zero this.symm))
      div_zero := fun _ => by simp
      div_cancel := fun {n} x hn => by
        apply Additive.toMul.injective
        apply Units.ext
        have := Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq
          ((Additive.toMul x : Kˣ) : K) (Nat.pos_of_ne_zero hn))
        simpa [hn] using this }
  haveI : DivisibleBy (Additive Kˣ) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  haveI : Injective (AddCommGrpCat.of (Additive Kˣ)) := AddCommGrpCat.injective_of_divisible _
  let inc : AddCommGrpCat.of H ⟶ AddCommGrpCat.of Γ := AddCommGrpCat.ofHom H.subtype
  haveI : Mono inc := (AddCommGrpCat.mono_iff_injective _).2 Subtype.val_injective
  let g₀ := Injective.factorThru (AddCommGrpCat.ofHom χ) inc
  have hg₀ : inc ≫ g₀ = AddCommGrpCat.ofHom χ := Injective.comp_factorThru _ _
  let g : Multiplicative Γ →* K :=
    (Units.coeHom K).comp (AddMonoidHom.toMultiplicativeLeft g₀.hom)
  refine ⟨g, ?_⟩
  ext y
  refine c.induction (p := fun y => φ' y = (twist φ g).comp c.σ y) ?_ ?_ ?_ y
  · simp
  · intro a b ha hb
    simp only [map_add, ha, hb]
  · intro d a ha
    have ha' : c.σ a = AddMonoidAlgebra.single d a := ha
    simp only [RingHom.comp_apply, ha', twist_single]
    by_cases h0 : φ a = 0
    · rw [h0, zero_mul]
      exact map_eq_zero_of_inv hι ht hφ ha h0
    · have hgd : g (Multiplicative.ofAdd d) = (χ₀ ⟨d, a, ha, h0⟩ : K) := by
        have := congrArg (fun k => k.hom (⟨d, a, ha, h0⟩ : H)) hg₀
        change g₀.hom d = Additive.ofMul (χ₀ ⟨d, a, ha, h0⟩) at this
        change ((Additive.toMul (g₀.hom d) : Kˣ) : K) = _
        rw [this]; rfl
      rw [hgd, mul_comm]
      exact (hχ₀ ⟨d, a, ha, h0⟩ ha h0).symm

end Trans

/-- `Spec` of a ring map. -/
noncomputable abbrev sp {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    Spec (.of B) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom f)

lemma sp_comp {A B D : Type u} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D) :
    sp (g.comp f) = sp g ≫ sp f := by
  rw [sp, sp, sp, ← Spec.map_comp]; rfl

lemma sp_inj {A B : Type u} [CommRing A] [CommRing B] {f g : A →+* B} (h : sp f = sp g) : f = g := by
  have := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom this

lemma sp_apply {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (x : PrimeSpectrum B) :
    sp f x = PrimeSpectrum.comap f x := rfl

variable {X : Scheme.{u}}

/-- A morphism from `Spec B` landing in an affine open is given by a ring map. -/
lemma exists_factor {B : Type u} [CommRing B] (G : Spec (.of B) ⟶ X) {V : X.Opens}
    (hV : IsAffineOpen V) (h : ∀ x, G x ∈ V) :
    ∃ e : Γ(X, V) →+* B, G = sp e ≫ hV.fromSpec := by
  have hr : Set.range G ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    exact h x
  let l := IsOpenImmersion.lift hV.fromSpec G hr
  refine ⟨(Spec.preimage l).hom, ?_⟩
  have : sp (Spec.preimage l).hom = l := by
    change Spec.map (CommRingCat.ofHom (Spec.preimage l).hom) = l
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  rw [this]
  exact (IsOpenImmersion.lift_fac _ _ _).symm

lemma factor_inj {B : Type u} [CommRing B] {V : X.Opens} (hV : IsAffineOpen V) {e e' : Γ(X, V) →+* B}
    (h : sp e ≫ hV.fromSpec = sp e' ≫ hV.fromSpec) : e = e' :=
  sp_inj ((cancel_mono _).1 h)

section Loc

variable {A A₀ : Type u} [CommRing A] [CommRing A₀] (ι : A₀ →+* A)

lemma ιLoc_aux (h : A₀) : IsUnit (((algebraMap A (Localization.Away (ι h))).comp ι) h) :=
  IsLocalization.Away.algebraMap_isUnit (ι h)

/-- `(A₀)_h → A_{ι h}`. -/
noncomputable def ιLoc (h : A₀) : Localization.Away h →+* Localization.Away (ι h) :=
  IsLocalization.Away.lift h (ιLoc_aux ι h)

lemma ιLoc_comp (h : A₀) : (ιLoc ι h).comp (algebraMap A₀ (Localization.Away h)) =
    (algebraMap A (Localization.Away (ι h))).comp ι := by
  refine RingHom.ext fun x => ?_
  rw [RingHom.comp_apply, ιLoc, IsLocalization.Away.lift_eq (S := Localization.Away h) h (ιLoc_aux ι h) x]

lemma sp_ιLoc (h : A₀) : sp (ιLoc ι h) ≫ sp (algebraMap A₀ (Localization.Away h)) =
    sp (algebraMap A (Localization.Away (ι h))) ≫ sp ι := by
  rw [← sp_comp, ← sp_comp, ιLoc_comp]

lemma ιLoc_injective (hι : Function.Injective ι) (h : A₀) : Function.Injective (ιLoc ι h) := by
  refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
  obtain ⟨n, a, hza⟩ := IsLocalization.Away.surj h z
  have e : ∀ x, ιLoc ι h (algebraMap A₀ _ x) = algebraMap A (Localization.Away (ι h)) (ι x) :=
    fun x => congrArg (fun k => k x) (ιLoc_comp ι h)
  have h1 : algebraMap A (Localization.Away (ι h)) (ι a) = 0 := by
    rw [← e, ← hza, map_mul, hz, zero_mul]
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (ι h)) _ _).1 h1
  have h2 : h ^ k * a = 0 := hι (by simpa [map_mul, map_pow] using hk)
  have hu : IsUnit (algebraMap A₀ (Localization.Away h) h) := IsLocalization.Away.algebraMap_isUnit h
  have h3 : algebraMap A₀ (Localization.Away h) a = 0 := by
    have := congrArg (algebraMap A₀ (Localization.Away h)) h2
    rw [map_mul, map_pow, map_zero] at this
    exact (hu.pow k).mul_right_eq_zero.1 this
  rw [h3] at hza
  exact (hu.pow n).mul_left_eq_zero.1 hza

variable {ι}

/-- Basic opens are a basis. -/
lemma exists_basic {W : Set (PrimeSpectrum A₀)} (hW : IsOpen W) {q : PrimeSpectrum A₀} (hq : q ∈ W) :
    ∃ h : A₀, h ∉ q.asIdeal ∧ ∀ q' : PrimeSpectrum A₀, h ∉ q'.asIdeal → q' ∈ W := by
  obtain ⟨_, ⟨h, rfl⟩, hqh, hle⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hq hW
  exact ⟨h, hqh, fun q' hq' => hle hq'⟩

lemma exists_away_pt {h : A₀} {q : PrimeSpectrum A₀} (hq : h ∉ q.asIdeal) :
    ∃ x, sp (algebraMap A₀ (Localization.Away h)) x = q := by
  have : q ∈ Set.range (PrimeSpectrum.comap (algebraMap A₀ (Localization.Away h))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away h) h]
    exact hq
  exact this

lemma away_pt_not_mem {h : A₀} (x : PrimeSpectrum (Localization.Away h)) :
    h ∉ (PrimeSpectrum.comap (algebraMap A₀ (Localization.Away h)) x).asIdeal := by
  have : PrimeSpectrum.comap (algebraMap A₀ (Localization.Away h)) x ∈
      (PrimeSpectrum.basicOpen h : Set _) := by
    rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away h) h]
    exact ⟨x, rfl⟩
  exact this

/-- **Step (4), uniqueness**, on an open of `Spec A₀`: two morphisms which agree on the part over
`Spec A` are equal, because `A₀ → A` is split. -/
theorem uniq_of_isSplit {r : A → A₀} (hs : IsSplit ι r) {Z : Scheme.{u}} (k : Z ⟶ Spec (.of A₀))
    [IsOpenImmersion k] {g g' : Z ⟶ X}
    (H : ∀ (Y : Scheme.{u}) (u : Y ⟶ Spec (.of A)) (v : Y ⟶ Z), v ≫ k = u ≫ sp ι → v ≫ g = v ≫ g') :
    g = g' := by
  have hinj := hs.injective
  -- the local chart
  have chart : ∀ h : A₀, (∀ q' : PrimeSpectrum A₀, h ∉ q'.asIdeal → q' ∈ Set.range k) →
      ∃ l : Spec (.of (Localization.Away h)) ⟶ Z, l ≫ k = sp (algebraMap A₀ _) := by
    intro h hh
    refine ⟨IsOpenImmersion.lift k (sp (algebraMap A₀ _)) ?_, IsOpenImmersion.lift_fac _ _ _⟩
    rintro _ ⟨x, rfl⟩
    exact hh _ (away_pt_not_mem x)
  have hH : ∀ (h : A₀) (l : Spec (.of (Localization.Away h)) ⟶ Z),
      l ≫ k = sp (algebraMap A₀ _) → sp (ιLoc ι h) ≫ l ≫ g = sp (ιLoc ι h) ≫ l ≫ g' := by
    intro h l hl
    have := H _ (sp (algebraMap A (Localization.Away (ι h)))) (sp (ιLoc ι h) ≫ l) (by
      rw [Category.assoc, hl, sp_ιLoc])
    simpa using this
  refine Scheme.hom_ext_of_forall _ _ fun z => ?_
  obtain ⟨p, hp⟩ := hs.exists_prime (k z)
  -- first `g z = g' z`
  have hzz : g z = g' z := by
    have hRo : IsOpen (Set.range k) := k.isOpenEmbedding.isOpen_range
    obtain ⟨h, hzh, hh⟩ := exists_basic hRo (q := k z) ⟨z, rfl⟩
    obtain ⟨l, hl⟩ := chart h hh
    have hph : ι h ∉ p.asIdeal := fun hm => hzh (by rw [← hp]; exact hm)
    obtain ⟨x, hx⟩ := exists_away_pt (A₀ := A) (h := ι h) (q := p) hph
    have e := hH h l hl
    have hv : l (sp (ιLoc ι h) x) = z := by
      apply k.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hl, ← Scheme.Hom.comp_apply, sp_ιLoc, Scheme.Hom.comp_apply, hx]
      exact hp
    have := congrArg (fun m => m x) e
    simp only [Scheme.Hom.comp_apply, hv] at this
    exact this
  obtain ⟨V, hV, hzV⟩ : ∃ V : X.Opens, IsAffineOpen V ∧ g z ∈ V := by
    obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (g z)) isOpen_univ
    exact ⟨V, hV, hx⟩
  let Z' : Z.Opens := g ⁻¹ᵁ V ⊓ g' ⁻¹ᵁ V
  have hW : IsOpen (k '' (Z' : Set Z)) := k.isOpenEmbedding.isOpenMap _ Z'.2
  obtain ⟨h, hzh, hh⟩ := exists_basic hW (q := k z) ⟨z, ⟨hzV, (show g' z ∈ V by rw [← hzz]; exact hzV)⟩, rfl⟩
  obtain ⟨l, hl⟩ := chart h (fun q' hq' => by
    obtain ⟨y, -, rfl⟩ := hh q' hq'
    exact ⟨y, rfl⟩)
  have hlZ : ∀ x, l x ∈ Z' := by
    intro x
    obtain ⟨y, hy, hye⟩ := hh _ (away_pt_not_mem x)
    have : l x = y := by
      apply k.isOpenEmbedding.injective
      rw [hye, ← Scheme.Hom.comp_apply, hl]
      rfl
    rw [this]
    exact hy
  obtain ⟨e, he⟩ := exists_factor (l ≫ g) hV (fun x => by
    rw [Scheme.Hom.comp_apply]; exact (hlZ x).1)
  obtain ⟨e', he'⟩ := exists_factor (l ≫ g') hV (fun x => by
    rw [Scheme.Hom.comp_apply]; exact (hlZ x).2)
  have hee : e = e' := by
    have e1 := hH h l hl
    rw [he, he', ← Category.assoc, ← Category.assoc, ← sp_comp, ← sp_comp] at e1
    have e2 := factor_inj hV e1
    ext s
    exact ιLoc_injective ι hinj h (congrArg (fun m => m s) e2)
  have hll : l ≫ g = l ≫ g' := by rw [he, he', hee]
  have : IsOpenImmersion l := by
    have : IsOpenImmersion (l ≫ k) := by rw [hl]; infer_instance
    exact IsOpenImmersion.of_comp l k
  obtain ⟨xz, hxz⟩ := exists_away_pt (h := h) (q := k z) hzh
  have hlz : l xz = z := by
    apply k.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hl, hxz]
  refine ⟨l.opensRange, ⟨xz, hlz⟩, ?_⟩
  rw [← cancel_epi l.isoOpensRange.hom]
  simp [hll]

end Loc

variable {X : Scheme.{u}} {A A₀ Γ : Type u} [CommRing A] [CommRing A₀] [AddCommGroup Γ]
  {c : Coact A Γ} {ι : A₀ →+* A}

/-- `a ↦ a ⊗ 1`. -/
noncomputable abbrev cC (A Γ : Type u) [CommRing A] [AddCommGroup Γ] : A →+* AddMonoidAlgebra A Γ :=
  AddMonoidAlgebra.singleZeroRingHom

/-- `F : Spec A → X` is invariant under `D(Γ)`. -/
def IsInvariantF (c : Coact A Γ) (F : Spec (.of A) ⟶ X) : Prop :=
  sp c.σ ≫ F = sp (cC A Γ) ≫ F

lemma IsInvariantF.test {F : Spec (.of A) ⟶ X} (hF : IsInvariantF c F) {D : Type u} [CommRing D]
    (τ : AddMonoidAlgebra A Γ →+* D) : sp (τ.comp c.σ) ≫ F = sp (τ.comp (cC A Γ)) ≫ F := by
  have hF' : sp c.σ ≫ F = sp (cC A Γ) ≫ F := hF
  rw [sp_comp, sp_comp, Category.assoc, Category.assoc, hF']

/-- Step (3): `O(V) → O(m⁻¹W)` lands in degree `0`, so `F` descends on `W = D(h)`. -/
theorem exists_local (hι : c.IsInv ι) {F : Spec (.of A) ⟶ X} (hF : IsInvariantF c F) (h : A₀)
    {V : X.Opens} (hV : IsAffineOpen V) (hc : ∀ p : PrimeSpectrum A, ι h ∉ p.asIdeal → F p ∈ V) :
    ∃ f : Spec (.of (Localization.Away h)) ⟶ X, ∀ (Y : Scheme.{u}) (u : Y ⟶ Spec (.of A))
      (v : Y ⟶ Spec (.of (Localization.Away h))),
      v ≫ sp (algebraMap A₀ _) = u ≫ sp ι → v ≫ f = u ≫ F := by
  let B := Localization.Away (ι h)
  let loc : A →+* B := algebraMap A B
  obtain ⟨e, he⟩ := exists_factor (sp loc ≫ F) hV (fun x => by
    rw [Scheme.Hom.comp_apply]
    exact hc _ (away_pt_not_mem x))
  let m : AddMonoidAlgebra A Γ →+* AddMonoidAlgebra B Γ := AddMonoidAlgebra.mapRingHom Γ loc
  have hC : ∀ a : A, m (cC A Γ a) = cC B Γ (loc a) := fun a => by
    simp [m, cC]
  have hhι : c.σ (ι h) = cC A Γ (ι h) := (hι.range _).2 ⟨h, rfl⟩
  have hu0 : IsUnit (loc (ι h)) := IsLocalization.Away.algebraMap_isUnit (ι h)
  have hu : IsUnit ((m.comp c.σ) (ι h)) := by
    rw [RingHom.comp_apply, hhι, hC]
    exact hu0.map _
  let θ₁ : B →+* AddMonoidAlgebra B Γ := IsLocalization.Away.lift (ι h) hu
  let θ₂ : B →+* AddMonoidAlgebra B Γ := cC B Γ
  have hθ₁ : ∀ a, θ₁ (loc a) = m (c.σ a) := fun a =>
    IsLocalization.Away.lift_eq (S := B) (ι h) hu a
  have hc₁ : θ₁.comp loc = m.comp c.σ := RingHom.ext hθ₁
  have hc₂ : θ₂.comp loc = m.comp (cC A Γ) := RingHom.ext fun a => (hC a).symm
  have heq : θ₁.comp e = θ₂.comp e := by
    apply factor_inj hV
    rw [sp_comp, sp_comp, Category.assoc, Category.assoc, ← he, ← Category.assoc, ← Category.assoc,
      ← sp_comp, ← sp_comp, hc₁, hc₂]
    exact hF.test m
  have hrange : ∀ s, e s ∈ (ιLoc ι h).range := by
    intro s
    have hx : θ₁ (e s) = θ₂ (e s) := congrArg (fun k => k s) heq
    obtain ⟨n, y, hy⟩ := IsLocalization.Away.surj (ι h) (e s)
    have h1 : m (c.σ y) = cC B Γ (loc y) := by
      have e1 : θ₁ (loc (ι h)) = θ₂ (loc (ι h)) := by rw [hθ₁, hhι, hC]
      rw [← hθ₁]
      change θ₁ (algebraMap A B y) = _
      rw [← hy, map_mul, map_pow, hx]
      change θ₂ (e s) * θ₁ (loc (ι h)) ^ n = _
      rw [e1, ← map_pow, ← map_mul]
    have h2 : ∀ d, d ≠ 0 → loc (c.comp d y) = 0 := by
      intro d hd
      have := congrArg (fun z => z.coeff d) h1
      simpa [m, Coact.comp, cC, Finsupp.single_eq_of_ne hd] using this
    have h3 : loc y = loc (c.comp 0 y) := by
      have e1 := congrArg loc (c.sum_eq y)
      rw [← e1, Finsupp.sum, map_sum]
      classical
      by_cases h0 : (c.σ y).coeff 0 = 0
      · have : c.comp 0 y = 0 := h0
        rw [this, map_zero]
        exact Finset.sum_eq_zero fun d hd => h2 d fun e0 => (Finsupp.mem_support_iff.1 hd) (e0 ▸ h0)
      · exact Finset.sum_eq_single_of_mem 0 (Finsupp.mem_support_iff.2 h0)
          fun d _ hd => h2 d hd
    have hu₀ : IsUnit (algebraMap A₀ (Localization.Away h) h) :=
      IsLocalization.Away.algebraMap_isUnit h
    obtain ⟨w, hw⟩ := hu₀.exists_left_inv
    refine ⟨algebraMap A₀ _ (hι.r y) * w ^ n, ?_⟩
    have ec : ∀ x, ιLoc ι h (algebraMap A₀ _ x) = loc (ι x) :=
      fun x => congrArg (fun k => k x) (ιLoc_comp ι h)
    have hw' : ιLoc ι h w * loc (ι h) = 1 := by
      rw [← ec, ← map_mul, hw, map_one]
    rw [map_mul, ec, hι.ι_r, ← h3, map_pow]
    change loc y * _ = _
    have hy' : loc y = e s * loc (ι h) ^ n := hy.symm
    rw [hy', mul_assoc, ← mul_pow, mul_comm (loc (ι h)), hw', one_pow, mul_one]
  have hbij : Function.Bijective (ιLoc ι h).rangeRestrict :=
    ⟨fun a b hab => ιLoc_injective ι hι.inj h (congrArg Subtype.val hab),
      (ιLoc ι h).rangeRestrict_surjective⟩
  let E := RingEquiv.ofBijective _ hbij
  let e₀ : Γ(X, V) →+* Localization.Away h :=
    E.symm.toRingHom.comp (e.codRestrict (ιLoc ι h).range hrange)
  have he₀ : (ιLoc ι h).comp e₀ = e := by
    refine RingHom.ext fun s => ?_
    have := E.apply_symm_apply ⟨e s, hrange s⟩
    exact congrArg Subtype.val this
  refine ⟨sp e₀ ≫ hV.fromSpec, fun Y u v huv => ?_⟩
  have hr : Set.range u ⊆ Set.range (sp loc) := by
    rintro _ ⟨y, rfl⟩
    have hq : ι h ∉ (u y).asIdeal := by
      have e1 : (u ≫ sp ι) y = (v ≫ sp (algebraMap A₀ _)) y := by rw [huv]
      intro hm
      have : h ∈ ((v ≫ sp (algebraMap A₀ (Localization.Away h))) y).asIdeal := by
        rw [← e1]; exact hm
      rw [Scheme.Hom.comp_apply] at this
      exact away_pt_not_mem _ this
    exact exists_away_pt (A₀ := A) hq
  let w := IsOpenImmersion.lift (sp loc) u hr
  have hw : w ≫ sp loc = u := IsOpenImmersion.lift_fac _ _ _
  have hv : v = w ≫ sp (ιLoc ι h) := by
    rw [← cancel_mono (sp (algebraMap A₀ (Localization.Away h))), huv, Category.assoc, sp_ιLoc,
      ← Category.assoc, hw]
  have hsp : sp (ιLoc ι h) ≫ sp e₀ = sp e := by rw [← sp_comp, he₀]
  rw [hv, Category.assoc, ← Category.assoc (sp (ιLoc ι h)), hsp, ← he, ← Category.assoc, hw]

/-- The cover of `Spec A₀` by principal opens. -/
noncomputable def awayCover {R J : Type u} [CommRing R] (h : J → R)
    (hc : ∀ q : PrimeSpectrum R, ∃ j, h j ∉ q.asIdeal) : (Spec (.of R)).OpenCover :=
  Scheme.Cover.mkOfCovers J (fun j => Spec (.of (Localization.Away (h j))))
    (fun j => sp (algebraMap R _))
    (fun q => by
      obtain ⟨j, hj⟩ := hc q
      obtain ⟨x, hx⟩ := exists_away_pt hj
      exact ⟨j, x, hx⟩)
    (fun j => inferInstanceAs (IsOpenImmersion _))

/-- **Gluing** of step (3). -/
theorem exists_desc_of_loc (hι : c.IsInv ι) {F : Spec (.of A) ⟶ X} (hF : IsInvariantF c F)
    (hloc : ∀ q : PrimeSpectrum A₀, ∃ h : A₀, h ∉ q.asIdeal ∧ ∃ V : X.Opens, IsAffineOpen V ∧
      ∀ p : PrimeSpectrum A, ι h ∉ p.asIdeal → F p ∈ V) :
    ∃ f : Spec (.of A₀) ⟶ X, sp ι ≫ f = F := by
  choose h hh V hV hc using hloc
  choose fh hfh using fun q => exists_local hι hF (h q) (hV q) (hc q)
  let 𝒰 := awayCover h fun q => ⟨q, hh q⟩
  let fh' : ∀ x : 𝒰.I₀, 𝒰.X x ⟶ X := fun x => fh x
  have hcompat : ∀ x y : 𝒰.I₀, pullback.fst (𝒰.f x) (𝒰.f y) ≫ fh' x = pullback.snd _ _ ≫ fh' y := by
    intro x y
    refine uniq_of_isSplit hι.isSplit (pullback.fst (𝒰.f x) (𝒰.f y) ≫ 𝒰.f x) fun Y u v huv => ?_
    have e1 : (v ≫ pullback.fst (𝒰.f x) (𝒰.f y)) ≫ fh' x = u ≫ F :=
      hfh x Y u (v ≫ pullback.fst (𝒰.f x) (𝒰.f y)) ((Category.assoc _ _ _).trans huv)
    have hcond : pullback.snd (𝒰.f x) (𝒰.f y) ≫ 𝒰.f y = pullback.fst _ _ ≫ 𝒰.f x :=
      pullback.condition.symm
    have e2 : (v ≫ pullback.snd (𝒰.f x) (𝒰.f y)) ≫ fh' y = u ≫ F :=
      hfh y Y u (v ≫ pullback.snd (𝒰.f x) (𝒰.f y))
        ((Category.assoc _ _ _).trans ((congrArg (v ≫ ·) hcond).trans huv))
    rw [Category.assoc] at e1 e2
    exact e1.trans e2.symm
  refine ⟨𝒰.glueMorphisms fh' hcompat, ?_⟩
  let 𝒱 := awayCover (fun q => ι (h q)) fun p =>
    ⟨PrimeSpectrum.comap ι p, hh (PrimeSpectrum.comap ι p)⟩
  refine 𝒱.hom_ext _ _ fun q => ?_
  have e1 := hfh q _ (sp (algebraMap A (Localization.Away (ι (h q))))) (sp (ιLoc ι (h q))) (sp_ιLoc ι _)
  have e2 : 𝒰.f q ≫ 𝒰.glueMorphisms fh' hcompat = fh' q := Scheme.Cover.ι_glueMorphisms 𝒰 fh' hcompat q
  have e3 : 𝒱.f q ≫ sp ι = sp (ιLoc ι (h q)) ≫ 𝒰.f q := (sp_ιLoc ι (h q)).symm
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ 𝒰.glueMorphisms fh' hcompat) e3).trans
    ((Category.assoc _ _ _).trans ((congrArg (sp (ιLoc ι (h q)) ≫ ·) e2).trans e1)))

/-! ### Stage A -/

lemma comap_cC_bot (p : PrimeSpectrum A) [IsDomain (AddMonoidAlgebra (A ⧸ p.asIdeal) Γ)] :
    PrimeSpectrum.comap (((AddMonoidAlgebra.mapRingHom Γ (Ideal.Quotient.mk p.asIdeal)).comp (cC A Γ)))
      ⟨⊥, Ideal.isPrime_bot⟩ = p := by
  refine PrimeSpectrum.ext (Ideal.ext fun a => ?_)
  change (AddMonoidAlgebra.mapRingHom Γ (Ideal.Quotient.mk p.asIdeal)) (cC A Γ a) ∈ (⊥ : Ideal _) ↔ _
  rw [Ideal.mem_bot, ← Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro h
    have := congrArg (fun z => z.coeff 0) h
    simpa [cC] using this
  · intro h
    simp [cC, h]

/-- **Steps (1), (2)** for a torsion-free grading. -/
theorem exists_loc_of_torsionFree [UniqueSums Γ] (hι : c.IsInv ι) {F : Spec (.of A) ⟶ X}
    (hF : IsInvariantF c F) (q : PrimeSpectrum A₀) :
    ∃ h : A₀, h ∉ q.asIdeal ∧ ∃ V : X.Opens, IsAffineOpen V ∧
      ∀ p : PrimeSpectrum A, ι h ∉ p.asIdeal → F p ∈ V := by
  obtain ⟨I, hI, hIq, hmax⟩ := exists_maximal_homIdeal c hι.inj q.asIdeal
  have hIne : I ≠ ⊤ := fun e => q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hIq 1 (by rw [map_one, e]; trivial)))
  obtain ⟨o, ho, hIo⟩ := I.exists_le_maximal hIne
  let oP : PrimeSpectrum A := ⟨o, ho.isPrime⟩
  obtain ⟨V, hV, hoV⟩ : ∃ V : X.Opens, IsAffineOpen V ∧ F oP ∈ V := by
    obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (F oP)) isOpen_univ
    exact ⟨V, hV, hx⟩
  let U : Set (PrimeSpectrum A) := {p | F p ∈ V}
  have hUo : IsOpen U := (F ⁻¹ᵁ V).2
  obtain ⟨a₀, ha₀, hsub⟩ := exists_basic hUo (q := oP) hoV
  have hstable : ∀ (p : PrimeSpectrum A) [IsDomain (AddMonoidAlgebra (A ⧸ p.asIdeal) Γ)], p ∉ U →
      PrimeSpectrum.comap (orbitHom c p.asIdeal) ⟨⊥, Ideal.isPrime_bot⟩ ∉ U := by
    intro p _ hp hm
    apply hp
    have e := hF.test (AddMonoidAlgebra.mapRingHom Γ (Ideal.Quotient.mk p.asIdeal))
    have e2 := congrArg (fun m => m (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (AddMonoidAlgebra (A ⧸ p.asIdeal) Γ))) e
    simp only [Scheme.Hom.comp_apply] at e2
    have e3 : F p = F (PrimeSpectrum.comap (orbitHom c p.asIdeal) ⟨⊥, Ideal.isPrime_bot⟩) := by
      refine Eq.trans ?_ e2.symm
      exact congrArg F (comap_cC_bot p).symm
    change F p ∈ V
    rw [e3]
    exact hm
  have hcomp := fun d p hp => comp_mem_of_stable c U hstable (a₀ := a₀) hsub d p hp
  obtain ⟨d, hd⟩ : ∃ d, c.comp d a₀ ∉ o := by
    by_contra hcon
    push Not at hcon
    exact ha₀ (c.mem_of_comp_mem o a₀ hcon)
  obtain ⟨h, hhq, b, hb⟩ := exists_inv_of_homog hι hI hIq hmax (c.comp_isHom d a₀)
    (fun hmem => hd (hIo hmem))
  refine ⟨h, hhq, V, hV, fun p hp => ?_⟩
  by_contra hn
  exact hp (by rw [hb]; exact Ideal.mul_mem_right _ _ (hcomp d p hn))

/-- **Descent, torsion-free grading.** -/
theorem exists_desc_of_torsionFree [UniqueSums Γ] (hι : c.IsInv ι) {F : Spec (.of A) ⟶ X}
    (hF : IsInvariantF c F) : ∃ f : Spec (.of A₀) ⟶ X, sp ι ≫ f = F :=
  exists_desc_of_loc hι hF (exists_loc_of_torsionFree hι hF)

/-! ### Stage B -/

/-- Two points over the same point of `Spec A₀` have the same image in `X`. -/
theorem map_eq_of_comap_eq (hι : c.IsInv ι) (ht : c.IsTors) {F : Spec (.of A) ⟶ X}
    (hF : IsInvariantF c F) {p p' : PrimeSpectrum A}
    (hpp : PrimeSpectrum.comap ι p = PrimeSpectrum.comap ι p') : F p = F p' := by
  obtain ⟨z, hz, hz'⟩ := Scheme.Pullback.exists_preimage_pullback (f := sp ι) (g := sp ι) p p' hpp
  let Z := pullback (sp ι) (sp ι)
  let κ := Z.residueField z
  let K := AlgebraicClosure κ
  let t : Spec (.of K) ⟶ Z := sp (algebraMap κ K) ≫ Z.fromSpecResidueField z
  let φ : A →+* K := (Spec.preimage (t ≫ pullback.fst _ _)).hom
  let φ' : A →+* K := (Spec.preimage (t ≫ pullback.snd _ _)).hom
  have hφ : sp φ = t ≫ pullback.fst _ _ := by
    change Spec.map (CommRingCat.ofHom (Spec.preimage _).hom) = _
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hφ' : sp φ' = t ≫ pullback.snd _ _ := by
    change Spec.map (CommRingCat.ofHom (Spec.preimage _).hom) = _
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hcomp : φ.comp ι = φ'.comp ι := by
    apply sp_inj
    rw [sp_comp, sp_comp, hφ, hφ']
    exact (Category.assoc _ _ _).trans ((congrArg (t ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)
  obtain ⟨g, hg⟩ := exists_twist hι ht hcomp
  have htest := hF.test (twist φ g)
  have h1 : (twist φ g).comp (cC A Γ) = φ := by
    refine RingHom.ext fun a => ?_
    change twist φ g (AddMonoidAlgebra.single 0 a) = _
    rw [twist_single]
    simp
  rw [← hg, h1] at htest
  let pt : Spec (.of K) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
  have hpt : t pt = z := by
    have : t pt ∈ Set.range (Z.fromSpecResidueField z) := ⟨_, rfl⟩
    rw [Scheme.range_fromSpecResidueField] at this
    exact this
  have e1 : sp φ pt = p := by
    rw [hφ, Scheme.Hom.comp_apply, hpt]; exact hz
  have e2 : sp φ' pt = p' := by
    rw [hφ', Scheme.Hom.comp_apply, hpt]; exact hz'
  have := congrArg (fun m => m pt) htest
  simp only [Scheme.Hom.comp_apply, e1, e2] at this
  exact this.symm

/-- **Steps (1), (2)** for a torsion grading. -/
theorem exists_loc_of_tors (hι : c.IsInv ι) (ht : c.IsTors) {F : Spec (.of A) ⟶ X}
    (hF : IsInvariantF c F) (q : PrimeSpectrum A₀) :
    ∃ h : A₀, h ∉ q.asIdeal ∧ ∃ V : X.Opens, IsAffineOpen V ∧
      ∀ p : PrimeSpectrum A, ι h ∉ p.asIdeal → F p ∈ V := by
  obtain ⟨p₁, hp₁⟩ := hι.isSplit.exists_prime q
  obtain ⟨V, hV, hoV⟩ : ∃ V : X.Opens, IsAffineOpen V ∧ F p₁ ∈ V := by
    obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (F p₁)) isOpen_univ
    exact ⟨V, hV, hx⟩
  let C : Set (PrimeSpectrum A) := {p | F p ∉ V}
  have hC : IsClosed C := by
    rw [← isOpen_compl_iff]
    have hO : IsOpen {p : PrimeSpectrum A | F p ∈ V} := (F ⁻¹ᵁ V).2
    have : Cᶜ = {p : PrimeSpectrum A | F p ∈ V} := by
      ext p
      simp [C]
    rw [this]
    exact hO
  have hcl := PrimeSpectrum.isClosedMap_comap_of_isIntegral ι (isIntegral_of_isTors hι ht) C hC
  have hq : q ∈ (PrimeSpectrum.comap ι '' C)ᶜ := by
    rintro ⟨p, hp, hpq⟩
    apply hp
    have : F p = F p₁ := map_eq_of_comap_eq hι ht hF (hpq.trans hp₁.symm)
    change F p ∈ V
    rw [this]
    exact hoV
  obtain ⟨h, hh, hsub⟩ := exists_basic hcl.isOpen_compl hq
  refine ⟨h, hh, V, hV, fun p hp => ?_⟩
  by_contra hn
  exact hsub (PrimeSpectrum.comap ι p) hp ⟨p, hn, rfl⟩

/-- **Descent, torsion grading.** -/
theorem exists_desc_of_tors (hι : c.IsInv ι) (ht : c.IsTors) {F : Spec (.of A) ⟶ X}
    (hF : IsInvariantF c F) : ∃ f : Spec (.of A₀) ⟶ X, sp ι ≫ f = F :=
  exists_desc_of_loc hι hF (exists_loc_of_tors hι ht hF)

section Mon

variable {R P Γ : Type u} [CommRing R] [AddCommMonoid P] [AddCommGroup Γ] (δ : P →+ Γ)

/-- `x^p ↦ x^p ⊗ e^{δ p}`. -/
noncomputable def monσ : AddMonoidAlgebra R P →+* AddMonoidAlgebra (AddMonoidAlgebra R P) Γ :=
  AddMonoidAlgebra.liftNCRingHom
    ((AddMonoidAlgebra.singleZeroRingHom).comp AddMonoidAlgebra.singleZeroRingHom)
    { toFun := fun m => AddMonoidAlgebra.single (δ (Multiplicative.toAdd m))
        (AddMonoidAlgebra.single (Multiplicative.toAdd m) 1)
      map_one' := by simp [AddMonoidAlgebra.one_def]
      map_mul' := fun a b => by simp [AddMonoidAlgebra.single_mul_single] }
    fun _ _ => Commute.all _ _

lemma monσ_single (p : P) (r : R) :
    monσ δ (AddMonoidAlgebra.single p r) =
      AddMonoidAlgebra.single (δ p) (AddMonoidAlgebra.single p r) := by
  simp [monσ, AddMonoidAlgebra.liftNCRingHom, AddMonoidAlgebra.liftNC_single,
    AddMonoidAlgebra.single_mul_single]

lemma monσ_coeff (y : AddMonoidAlgebra R P) (d : Γ) (p : P) [Decidable (δ p = d)] :
    ((monσ δ y).coeff d).coeff p = if δ p = d then y.coeff p else 0 := by
  classical
  induction y using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ha, hb]
    split_ifs <;> simp
  | single m c =>
    rw [monσ_single]
    by_cases hm : δ m = d
    · subst hm
      by_cases hp : δ p = δ m
      · simp [hp]
      · have : m ≠ p := fun e => hp (e ▸ rfl)
        simp [hp, Finsupp.single_apply, this]
    · by_cases hp : δ p = d
      · have : m ≠ p := fun e => hm (e ▸ hp)
        simp [hm, hp, Finsupp.single_apply, this]
      · simp [hp, Finsupp.single_apply, hm]

/-- The grading of `R[P]` by `δ : P → Γ`. -/
noncomputable def monCoact : Coact (AddMonoidAlgebra R P) Γ where
  σ := monσ δ
  sum_eq y := by
    classical
    induction y using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb =>
      rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.sum_add_index' (by simp) (by simp), ha, hb]
    | single m c =>
      rw [monσ_single]
      simp
  hom y d := by
    classical
    induction y using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb =>
      simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ha, hb,
        AddMonoidAlgebra.single_add]
    | single m c =>
      rw [monσ_single]
      by_cases hm : δ m = d
      · subst hm
        simp [monσ_single]
      · simp [Finsupp.single_apply, hm]

variable {P₀ : Type u} [AddCommMonoid P₀] (j : P₀ →+ P)

/-- `R[P₀] → R[P]`. -/
noncomputable abbrev monι (R : Type u) [CommRing R] : AddMonoidAlgebra R P₀ →+* AddMonoidAlgebra R P :=
  AddMonoidAlgebra.mapDomainRingHom R j

variable {δ j}

lemma monι_single (k : P₀) (r : R) :
    monι j R (AddMonoidAlgebra.single k r) = AddMonoidAlgebra.single (j k) r := by
  simp

/-- `R[P₀]` is the ring of invariants, for `P₀ = ker δ`. -/
theorem monCoact_isInv (hj : Function.Injective j) (hk : ∀ p, δ p = 0 ↔ p ∈ Set.range j) :
    (monCoact (R := R) δ).IsInv (monι j R) where
  inj := AddMonoidAlgebra.mapDomain_injective hj
  range y := by
    classical
    constructor
    · intro h
      have h' : monσ δ y = AddMonoidAlgebra.single 0 y := h
      have hs : ∀ p ∈ y.coeff.support, p ∈ Set.range j := by
        intro p hp
        rw [← hk]
        by_contra hne
        have := monσ_coeff δ y (δ p) p
        rw [h', if_pos rfl] at this
        rw [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne hne] at this
        exact (Finsupp.mem_support_iff.1 hp) (by simpa using this.symm)
      have hsum : y = ∑ p ∈ y.coeff.support, AddMonoidAlgebra.single p (y.coeff p) := by
        ext p
        simp [AddMonoidAlgebra.coeff_sum, Finsupp.single_apply]
      rw [hsum]
      refine Subring.sum_mem _ fun p hp => ?_
      obtain ⟨k, rfl⟩ := hs p hp
      exact ⟨AddMonoidAlgebra.single k (y.coeff (j k)), monι_single _ _⟩
    · rintro ⟨x, rfl⟩
      induction x using AddMonoidAlgebra.induction_linear with
      | zero =>
        change monσ δ _ = _
        simp
      | add a b ha hb =>
        have ha' : monσ δ _ = _ := ha
        have hb' : monσ δ _ = _ := hb
        change monσ δ _ = _
        rw [RingHom.map_add, map_add, ha', hb', AddMonoidAlgebra.single_add]
      | single k r =>
        change monσ δ _ = _
        have h0 : δ (j k) = 0 := (hk _).2 ⟨k, rfl⟩
        rw [monι_single, monσ_single, h0]

/-- Nonzero homogeneous elements have degree in the image of `δ`. -/
lemma monCoact_deg {d : Γ} {a : AddMonoidAlgebra R P} (h : (monCoact δ).IsHom d a) (h0 : a ≠ 0) :
    ∃ p, δ p = d := by
  classical
  have h' : monσ δ a = AddMonoidAlgebra.single d a := h
  obtain ⟨p, hp⟩ : ∃ p, a.coeff p ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact h0 (AddMonoidAlgebra.ext (Finsupp.ext hcon))
  refine ⟨p, ?_⟩
  by_contra hne
  have := monσ_coeff δ a d p
  rw [h', if_neg hne] at this
  simp at this
  exact hp this

end Mon

/-! ### Base change of split maps -/

section Split

variable {A A₀ Γ : Type u} [CommRing A] [CommRing A₀] [AddCommGroup Γ] {ι : A₀ →+* A} {r : A → A₀}

/-- `r[Γ]`. -/
noncomputable def IsSplit.rΓ (hs : IsSplit ι r) (y : AddMonoidAlgebra A Γ) : AddMonoidAlgebra A₀ Γ :=
  AddMonoidAlgebra.ofCoeff (Finsupp.mapRange r (by simpa using hs.add 0 0) y.coeff)

lemma IsSplit.rΓ_single (hs : IsSplit ι r) (d : Γ) (a : A) :
    hs.rΓ (AddMonoidAlgebra.single d a) = AddMonoidAlgebra.single d (r a) := by
  ext
  simp [IsSplit.rΓ, Finsupp.mapRange_single]

lemma IsSplit.rΓ_zero (hs : IsSplit ι r) : hs.rΓ (0 : AddMonoidAlgebra A Γ) = 0 := by
  ext d
  simp [IsSplit.rΓ]

lemma IsSplit.rΓ_add (hs : IsSplit ι r) (x y : AddMonoidAlgebra A Γ) :
    hs.rΓ (x + y) = hs.rΓ x + hs.rΓ y := by
  ext d
  simp [IsSplit.rΓ, hs.add]

/-- `A₀[Γ] → A[Γ]` is split. -/
theorem IsSplit.mapRing (hs : IsSplit ι r) :
    IsSplit (AddMonoidAlgebra.mapRingHom Γ ι) hs.rΓ where
  add := hs.rΓ_add
  mul a y := by
    induction a using AddMonoidAlgebra.induction_linear with
    | zero => simp [hs.rΓ_zero]
    | add a b ha hb => rw [map_add, add_mul, add_mul, hs.rΓ_add, ha, hb]
    | single d a =>
      induction y using AddMonoidAlgebra.induction_linear with
      | zero => simp [hs.rΓ_zero]
      | add x y hx hy => rw [mul_add, hs.rΓ_add, hx, hy, hs.rΓ_add, mul_add]
      | single e b =>
        simp [AddMonoidAlgebra.single_mul_single, hs.rΓ_single, hs.mul]
  one := by
    rw [AddMonoidAlgebra.one_def, hs.rΓ_single, hs.one]
    rfl

end Split

/-- **Step (4)**: uniqueness of the descent. -/
theorem desc_unique {X : Scheme.{u}} {A A₀ : Type u} [CommRing A] [CommRing A₀] {ι : A₀ →+* A}
    {r : A → A₀} (hs : IsSplit ι r) {g g' : Spec (.of A₀) ⟶ X} (h : sp ι ≫ g = sp ι ≫ g') : g = g' := by
  refine uniq_of_isSplit hs (𝟙 _) fun Y u v huv => ?_
  rw [Category.comp_id] at huv
  rw [huv, Category.assoc, Category.assoc, h]

section TwoStage

variable {X : Scheme.{u}} {R P P₀ Γ : Type u} [CommRing R] [AddCommMonoid P] [AddCommMonoid P₀]
  [AddCommGroup Γ] [AddMonoid.FG Γ]

/-- **The descent**: `F : Spec R[P] → X` invariant under `D(Γ)` factors through `Spec R[ker δ]`. First
through the invariants of the torsion-free quotient of `Γ` (the Reynolds argument), then through
those of the torsion part (`R[P'] → R[ker δ]` is integral, and fibres are orbits). -/
theorem exists_desc (δ : P →+ Γ) {j : P₀ →+ P} (hj : Function.Injective j)
    (hk : ∀ p, δ p = 0 ↔ p ∈ Set.range j) {F : Spec (.of (AddMonoidAlgebra R P)) ⟶ X}
    (hF : IsInvariantF (monCoact δ) F) :
    ∃ f : Spec (.of (AddMonoidAlgebra R P₀)) ⟶ X, sp (monι j R) ≫ f = F := by
  classical
  let T := AddCommGroup.torsion Γ
  let π : Γ →+ Γ ⧸ T := QuotientAddGroup.mk' T
  let δ' : P →+ Γ ⧸ T := π.comp δ
  let P' : AddSubmonoid P := AddMonoidHom.mker δ'
  have : AddMonoid.FG (Γ ⧸ T) := AddMonoid.fg_of_surjective π (QuotientAddGroup.mk'_surjective T)
  have hιA : (monCoact (R := R) δ').IsInv (monι P'.subtype R) :=
    monCoact_isInv Subtype.val_injective fun p =>
      ⟨fun h => ⟨⟨p, h⟩, rfl⟩, by rintro ⟨q, rfl⟩; exact q.2⟩
  have hF' : IsInvariantF (monCoact (R := R) δ') F := by
    have e := hF.test (AddMonoidAlgebra.mapDomainRingHom (AddMonoidAlgebra R P) π)
    have e1 : (AddMonoidAlgebra.mapDomainRingHom (AddMonoidAlgebra R P) π).comp (monCoact δ).σ =
        (monCoact (R := R) δ').σ := by
      refine RingHom.ext fun y => ?_
      induction y using AddMonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [map_add, ha, hb]
      | single m c =>
        change AddMonoidAlgebra.mapDomainRingHom _ π (monσ δ _) = monσ δ' _
        rw [monσ_single, monσ_single]
        simp [δ']
    have e2 : (AddMonoidAlgebra.mapDomainRingHom (AddMonoidAlgebra R P) π).comp
        (cC (AddMonoidAlgebra R P) Γ) = cC _ _ := by
      refine RingHom.ext fun a => ?_
      simp [cC]
    rw [e1, e2] at e
    exact e
  obtain ⟨f', hf'⟩ := exists_desc_of_torsionFree hιA hF'
  let δ₁ : P' →+ Γ := δ.comp P'.subtype
  let j₁ : P₀ →+ P' := AddMonoidHom.codRestrict j P' (fun k => by
    have : δ (j k) = 0 := (hk _).2 ⟨k, rfl⟩
    change π (δ (j k)) = 0
    rw [this, map_zero])
  have hιB : (monCoact (R := R) δ₁).IsInv (monι j₁ R) :=
    monCoact_isInv (fun a b e => hj (congrArg Subtype.val e)) fun p => by
      constructor
      · intro h
        obtain ⟨k, hk'⟩ := (hk _).1 h
        exact ⟨k, Subtype.ext hk'⟩
      · rintro ⟨k, rfl⟩
        exact (hk _).2 ⟨k, rfl⟩
  have ht : (monCoact (R := R) δ₁).IsTors := by
    intro d a ha h0
    obtain ⟨p, rfl⟩ := monCoact_deg ha h0
    have hp : π (δ₁ p) = 0 := p.2
    have htor : δ₁ p ∈ T := (QuotientAddGroup.eq_zero_iff _).1 hp
    obtain ⟨n, hn, hd⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 htor
    exact ⟨n, hn, hd⟩
  have hF₁ : IsInvariantF (monCoact (R := R) δ₁) f' := by
    let ιΓ := AddMonoidAlgebra.mapRingHom Γ (monι P'.subtype R)
    have hs : IsSplit ιΓ hιA.isSplit.rΓ := hιA.isSplit.mapRing
    refine desc_unique hs ?_
    have e1 : ιΓ.comp (monCoact (R := R) δ₁).σ = (monCoact (R := R) δ).σ.comp (monι P'.subtype R) := by
      refine RingHom.ext fun y => ?_
      induction y using AddMonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [map_add, ha, hb]
      | single m c =>
        change ιΓ (monσ δ₁ _) = monσ δ _
        rw [monι_single, monσ_single, monσ_single]
        simp [ιΓ, monι_single]
        rfl
    have e2 : ιΓ.comp (cC _ Γ) = (cC _ Γ).comp (monι P'.subtype R) := by
      refine RingHom.ext fun y => ?_
      simp [ιΓ, cC]
    change sp ιΓ ≫ sp _ ≫ f' = sp ιΓ ≫ sp _ ≫ f'
    rw [← Category.assoc, ← Category.assoc, ← sp_comp, ← sp_comp, e1, e2, sp_comp, sp_comp,
      Category.assoc, Category.assoc, hf']
    exact hF
  obtain ⟨f, hf⟩ := exists_desc_of_tors hιB ht hF₁
  refine ⟨f, ?_⟩
  have e : monι j R = (monι P'.subtype R).comp (monι j₁ R) := by
    rw [monι, monι, monι, ← AddMonoidAlgebra.mapDomainRingHom_comp]
    rfl
  rw [e, sp_comp, Category.assoc, hf, hf']

end TwoStage

end AlgMag.SQ

open Opposite

namespace AlgMag

open SQ

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

section Spec

variable {P P' : Type u} [AddCommMonoid P] [Countable P] [AddCommMonoid P'] [Countable P']

lemma monι_comp_algebraMap (g : P' →+ P) (R : Type u) [CommRing R] :
    (monι g R).comp (algebraMap R _) = algebraMap R (AddMonoidAlgebra R P) := by
  refine RingHom.ext fun r => ?_
  change monι g R (AddMonoidAlgebra.single 0 r) = AddMonoidAlgebra.single 0 r
  rw [monι_single, map_zero]

variable (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]

lemma sp_specPrS {R' : Type u} [CommRing R'] (ψ : gRing P T →+* R') :
    sp ψ ≫ specPrS P T = sp (ψ.comp (algebraMap _ _)) ≫ ((SCH).obj T).isoSpec.inv := by
  rw [sp_comp, Category.assoc]
  rfl

/-- `𝔸(P)_T → 𝔸(P')_T`, along `g : P' → P`. -/
noncomputable def specAlong (g : P' →+ P) : specObj P T ⟶ specObj P' T :=
  overHom (sp (monι g _)) (by
    change sp (monι g _) ≫ specPrS P' T ≫ T.hom.hom = specPrS P T ≫ T.hom.hom
    rw [← Category.assoc, sp_specPrS, monι_comp_algebraMap]
    rfl)

lemma map_specAlong (g : P' →+ P) : (SCH).map (specAlong T g) = sp (monι g _) := rfl

lemma specAlong_pr (g : P' →+ P) : specAlong T g ≫ specPr P' T = specPr P T :=
  toScheme_map_injective (by
    rw [Functor.map_comp]
    change sp (monι g _) ≫ specPrS P' T = specPrS P T
    rw [sp_specPrS, monι_comp_algebraMap]
    rfl)

lemma specPt_apply (p : Multiplicative P) :
    specPt P T p = (Scheme.ΓSpecIso (.of (gRing P T))).inv.hom
      (AddMonoidAlgebra.single (Multiplicative.toAdd p) 1) := rfl

lemma appTop_sp_inv {A A' : Type u} [CommRing A] [CommRing A'] (ψ : A →+* A') (y : A) :
    (sp ψ).appTop.hom ((Scheme.ΓSpecIso (.of A)).inv.hom y) =
      (Scheme.ΓSpecIso (.of A')).inv.hom (ψ y) :=
  congrArg (fun k => k.hom y) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ)).symm

lemma res_specAlong (g : P' →+ P) :
    APt.res (specAlong T g).op (specPt P' T) = APt.along g (specPt P T) := by
  refine MonoidHom.ext fun p => ?_
  refine (appTop_sp_inv (monι g _) _).trans ?_
  rw [monι_single]
  rfl

variable {T}

lemma specLift_comp {T' T'' : BigFppfOver B S hS} (s : T'' ⟶ T') (t : T' ⟶ T)
    (a : APt (fppfO B S hS) P (op T')) :
    specLift (s ≫ t) (APt.res s.op a) = s ≫ specLift t a := by
  refine (specLift_uniq _ _ _ ?_ ?_).symm
  · rw [Category.assoc, specLift_pr]
  · rw [op_comp, APt.res_comp, res_specLift]

lemma specLift_along (g : P' →+ P) {T' : BigFppfOver B S hS} (t : T' ⟶ T)
    (c : APt (fppfO B S hS) P (op T')) :
    specLift t (APt.along g c) = specLift t c ≫ specAlong T g := by
  refine (specLift_uniq _ _ _ ?_ ?_).symm
  · rw [Category.assoc, specAlong_pr, specLift_pr]
  · rw [op_comp, APt.res_comp, res_specAlong]
    refine MonoidHom.ext fun p => ?_
    have := res_specLift t c
    exact congrArg (fun a => a (AddMonoidHom.toMultiplicative g p)) this

/-- On `Spec R'` over `T`, the classifying morphism of `ψ ∘ x^•` is `Spec ψ`. -/
lemma map_specLift_spPt {R' : Type u} [CommRing R'] {ρ : RT T →+* R'}
    {hC : B.Contains (Spec (.of R'))} (ψ : gRing P T →+* R') (hψ : ψ.comp (algebraMap _ _) = ρ) :
    (SCH).map (specLift (spToT T ρ hC) (spPt (T := T) (ρ := ρ) (hC := hC)
      (ψ.toMonoidHom.comp (AddMonoidAlgebra.of _ P)))) = sp ψ := by
  subst hψ
  let s : spObj T (ψ.comp (algebraMap _ _)) hC ⟶ specObj P T :=
    overHom (sp ψ) (by
      change sp ψ ≫ specPrS P T ≫ T.hom.hom = sp (ψ.comp (algebraMap _ _)) ≫ _ ≫ T.hom.hom
      rw [← Category.assoc, sp_specPrS, Category.assoc])
  have := specLift_uniq (spToT T (ψ.comp (algebraMap _ _)) hC) (spPt (T := T)
    (ρ := ψ.comp (algebraMap _ _)) (hC := hC) (ψ.toMonoidHom.comp (AddMonoidAlgebra.of _ P))) s
    (toScheme_map_injective (by
      rw [Functor.map_comp]
      change sp ψ ≫ specPrS P T = _
      rw [sp_specPrS]
      rfl))
    (MonoidHom.ext fun p => appTop_sp_inv ψ _)
  rw [← this]
  rfl

end Spec

section Bi0

variable {M : Type u} [AddCommGroup M] {N L : AddSubmonoid M}

/-- `(n, l) ↦ n - l`: the grading of the statement. -/
def dlt (N L : AddSubmonoid M) : ↥(N.prod L) →+ M :=
  (AddMonoidHom.fst M M - AddMonoidHom.snd M M).comp (N.prod L).subtype

lemma hKinf (N L : AddSubmonoid M) : ∀ k ∈ N ⊓ L, (k, k) ∈ N.prod L :=
  fun _ hk => ⟨(AddSubmonoid.mem_inf.mp hk).1, (AddSubmonoid.mem_inf.mp hk).2⟩

/-- `N ∩ L → N × L`, dual to the multiplication `𝔸(N) × 𝔸(L) → 𝔸(N ∩ L)`. -/
abbrev jD (N L : AddSubmonoid M) : ↥(N ⊓ L) →+ ↥(N.prod L) := iDiag (hKinf N L)

lemma jD_inj : Function.Injective (jD N L) := fun a b h =>
  Subtype.ext (congrArg (fun p => p.1.1) h)

lemma dlt_eq_zero (p : ↥(N.prod L)) : dlt N L p = 0 ↔ p ∈ Set.range (jD N L) := by
  constructor
  · intro h
    have e : p.1.1 = p.1.2 := sub_eq_zero.1 h
    exact ⟨⟨p.1.1, p.2.1, e ▸ p.2.2⟩, Subtype.ext (Prod.ext rfl e)⟩
  · rintro ⟨k, rfl⟩
    exact sub_self _

end Bi0

section Bi

variable {M : Type u} [AddCommGroup M] [AddMonoid.FG M] [Countable M]
variable {U : BigFppfOver B S hS} {aX : AAction (fppfO B S hS) M (yoneda.obj U)}
  {N L : AddSubmonoid M} {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]

/-- The morphism `F : 𝔸(N)_T × 𝔸(L)_T → X` of the statement. -/
noncomputable def biX (φ : AttractorPt (biAct aX) (N.prod L) T) : specObj ↥(N.prod L) T ⟶ U :=
  φ.app (specPr _ T) (specPt _ T)

lemma app_eq_biX (φ : AttractorPt (biAct aX) (N.prod L) T) {T' : BigFppfOver B S hS} (t : T' ⟶ T)
    (c : APt (fppfO B S hS) ↥(N.prod L) (op T')) : φ.app t c = specLift t c ≫ biX φ :=
  φ.app_eq_of_universal (specUniversal (N.prod L) T) t c

/-- `F` is invariant under `D(N^gp + L^gp)`, through `D(M)`. -/
theorem isInvariant_biX (φ : AttractorPt (biAct aX) (N.prod L) T) :
    IsInvariantF (monCoact (R := Γ((SCH).obj T, ⊤)) (dlt N L)) ((SCH).map (biX φ)) := by
  let A := gRing ↥(N.prod L) T
  let ρ : RT T →+* AddMonoidAlgebra A M := (cC A M).comp (algebraMap _ _)
  have hC : B.Contains (Spec (.of (AddMonoidAlgebra A M))) := contains_M (contains_spec _ T)
  let t := spToT T ρ hC
  let σ : A →+* AddMonoidAlgebra A M := (monCoact (R := Γ((SCH).obj T, ⊤)) (dlt N L)).σ
  have hσ : σ.comp (algebraMap _ _) = ρ := by
    refine RingHom.ext fun r => ?_
    change monσ _ (AddMonoidAlgebra.single 0 r) = _
    rw [monσ_single, map_zero]
    rfl
  let a₁ := spPt (T := T) (ρ := ρ) (hC := hC) (σ.toMonoidHom.comp (AddMonoidAlgebra.of _ _))
  let a₂ := spPt (T := T) (ρ := ρ) (hC := hC) ((cC A M).toMonoidHom.comp (AddMonoidAlgebra.of _ _))
  let E : Multiplicative M →* AddMonoidAlgebra A M := AddMonoidAlgebra.of _ _
  let e := spPt (T := T) (ρ := ρ) (hC := hC) E
  let h : APt (fppfO B S hS) (M × M) (op (spObj T ρ hC)) :=
    e.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst M M - AddMonoidHom.snd M M))
  have ha : a₁ = APt.toMagnet (N.prod L) h * a₂ := by
    refine MonoidHom.ext fun p => ?_
    change spSec T ρ hC (σ (AddMonoidAlgebra.single (Multiplicative.toAdd p) 1)) =
      spSec T ρ hC _ * spSec T ρ hC _
    rw [← map_mul]
    congr 1
    change monσ _ _ = _
    rw [monσ_single]
    simp [E, cC, AddMonoidAlgebra.single_mul_single]
    rfl
  have hdiag : h.comp (AddMonoidHom.toMultiplicative (diagHom M)) = 1 := by
    refine MonoidHom.ext fun m => ?_
    have h0 : ((AddMonoidHom.fst M M - AddMonoidHom.snd M M) (diagHom M (Multiplicative.toAdd m))) = 0 :=
      sub_self _
    change e (Multiplicative.ofAdd ((AddMonoidHom.fst M M - AddMonoidHom.snd M M)
      (diagHom M (Multiplicative.toAdd m)))) = 1
    rw [h0]
    exact map_one e
  have heq : φ.app t a₁ = φ.app t a₂ := by
    rw [ha]
    refine (φ.equivariant t h a₂).trans ?_
    change aX.smul (h.comp (AddMonoidHom.toMultiplicative (diagHom M))) _ = _
    rw [hdiag]
    exact aX.one_smul _
  rw [app_eq_biX, app_eq_biX] at heq
  have h1 := congrArg (fun k => (SCH).map k) heq
  simp only [Functor.map_comp] at h1
  rw [map_specLift_spPt σ hσ, map_specLift_spPt (cC A M) rfl] at h1
  exact h1

end Bi

section Bi

variable {M : Type u} [AddCommGroup M] [AddMonoid.FG M] [Countable M]
variable {U : BigFppfOver B S hS} {aX : AAction (fppfO B S hS) M (yoneda.obj U)}
  {N L : AddSubmonoid M} {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]

/-- **The descent**, on the universal point: `F = f ∘ m` for a morphism `f : 𝔸(N ∩ L)_T → X` over `S`. -/
theorem exists_x₀ (φ : AttractorPt (biAct aX) (N.prod L) T) :
    ∃ x₀ : specObj ↥(N ⊓ L) T ⟶ U, specAlong T (jD N L) ≫ x₀ = biX φ := by
  let R := Γ((SCH).obj T, ⊤)
  have hι := monCoact_isInv (R := R) (δ := dlt N L) jD_inj dlt_eq_zero
  obtain ⟨f, hf⟩ := exists_desc (R := R) (dlt N L) jD_inj dlt_eq_zero (isInvariant_biX φ)
  refine ⟨overHom f ?_, toScheme_map_injective ?_⟩
  · refine desc_unique hι.isSplit ?_
    have e1 : sp (monι (jD N L) R) ≫ specPrS ↥(N ⊓ L) T = specPrS ↥(N.prod L) T := by
      rw [sp_specPrS, monι_comp_algebraMap]
      rfl
    have e2 : (SCH).map (biX φ) ≫ U.hom.hom = specPrS ↥(N.prod L) T ≫ T.hom.hom := site_w (biX φ)
    change sp (monι (jD N L) R) ≫ f ≫ U.hom.hom = sp (monι (jD N L) R) ≫ specPrS ↥(N ⊓ L) T ≫ T.hom.hom
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ U.hom.hom) hf).trans (e2.trans
      ((congrArg (· ≫ T.hom.hom) e1).symm.trans (Category.assoc _ _ _))))
  · rw [Functor.map_comp]
    exact hf

lemma lift_x₀ {φ : AttractorPt (biAct aX) (N.prod L) T} {x₀ : specObj ↥(N ⊓ L) T ⟶ U}
    (hx : specAlong T (jD N L) ≫ x₀ = biX φ) {T' : BigFppfOver B S hS} (t : T' ⟶ T)
    (c : APt (fppfO B S hS) ↥(N.prod L) (op T')) :
    specLift t (APt.along (jD N L) c) ≫ x₀ = φ.app t c := by
  rw [specLift_along, Category.assoc, hx, app_eq_biX]

/-- Equivariance of `f`: it suffices to check it on the universal point of `𝔸(N ∩ L) × 𝔸(M)`, and
there after pulling back to `𝔸(N) × 𝔸(L) × 𝔸(M)`, by step (4). -/
theorem equivariant_x₀ {φ : AttractorPt (biAct aX) (N.prod L) T} {x₀ : specObj ↥(N ⊓ L) T ⟶ U}
    (hx : specAlong T (jD N L) ≫ x₀ = biX φ) {T' : BigFppfOver B S hS} (t : T' ⟶ T)
    (h : APt (fppfO B S hS) M (op T')) (a : APt (fppfO B S hS) ↥(N ⊓ L) (op T')) :
    specLift t (APt.toMagnet (N ⊓ L) h * a) ≫ x₀ = aX.smul h (specLift t a ≫ x₀) := by
  let R := Γ((SCH).obj T, ⊤)
  let P₂ := ↥(N ⊓ L) × M
  let Pm := ↥(N.prod L) × M
  let Q := specObj P₂ T
  let tQ : Q ⟶ T := specPr P₂ T
  let aU : APt (fppfO B S hS) ↥(N ⊓ L) (op Q) := APt.along (AddMonoidHom.inl _ _) (specPt P₂ T)
  let hU : APt (fppfO B S hS) M (op Q) := APt.along (AddMonoidHom.inr _ _) (specPt P₂ T)
  let jh : P₂ →+ Pm := (jD N L).prodMap (AddMonoidHom.id M)
  let δh : Pm →+ M := (dlt N L).comp (AddMonoidHom.fst _ _)
  have hι : (monCoact (R := R) δh).IsInv (monι jh R) := monCoact_isInv
    (Function.Injective.prodMap jD_inj Function.injective_id) (fun p => by
      constructor
      · intro hp
        obtain ⟨k, hk⟩ := (dlt_eq_zero p.1).1 hp
        exact ⟨(k, p.2), Prod.ext hk rfl⟩
      · rintro ⟨k, rfl⟩
        exact (dlt_eq_zero _).2 ⟨k.1, rfl⟩)
  let π : specObj Pm T ⟶ Q := specAlong T jh
  let tm : specObj Pm T ⟶ T := specPr Pm T
  let ch : APt (fppfO B S hS) ↥(N.prod L) (op (specObj Pm T)) :=
    APt.along (AddMonoidHom.inl _ _) (specPt Pm T)
  let eh : APt (fppfO B S hS) M (op (specObj Pm T)) :=
    APt.along (AddMonoidHom.inr _ _) (specPt Pm T)
  have hπt : π ≫ tQ = tm := specAlong_pr T jh
  have hra : APt.res π.op aU = APt.along (jD N L) ch := by
    have e := res_specAlong T jh
    refine MonoidHom.ext fun p => ?_
    exact congrArg (fun z => z (AddMonoidHom.toMultiplicative (AddMonoidHom.inl _ _) p)) e
  have hrh : APt.res π.op hU = eh := by
    have e := res_specAlong T jh
    refine MonoidHom.ext fun p => ?_
    exact congrArg (fun z => z (AddMonoidHom.toMultiplicative (AddMonoidHom.inr _ _) p)) e
  have hmag : APt.along (jD N L) (APt.toMagnet (N.prod L)
      (eh.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst M M))) * ch) =
      APt.toMagnet (N ⊓ L) eh * APt.along (jD N L) ch := MonoidHom.ext fun p => rfl
  have hφsm : φ.app tm (APt.toMagnet (N.prod L)
      (eh.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst M M))) * ch) =
      aX.smul eh (φ.app tm ch) := by
    refine (φ.equivariant tm _ ch).trans ?_
    change aX.smul ((eh.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst M M))).comp
      (AddMonoidHom.toMultiplicative (diagHom M))) _ = _
    rfl
  -- the universal equation
  have huniv : specLift tQ (APt.toMagnet (N ⊓ L) hU * aU) ≫ x₀ = aX.smul hU (specLift tQ aU ≫ x₀) := by
    apply toScheme_map_injective
    refine desc_unique hι.isSplit ?_
    have e0 : ∀ w : Q ⟶ U, sp (monι jh R) ≫ (SCH).map w = (SCH).map (π ≫ w) := fun w => by
      rw [Functor.map_comp]
      rfl
    rw [e0, e0]
    congr 1
    have e1 : π ≫ specLift tQ (APt.toMagnet (N ⊓ L) hU * aU) =
        specLift tm (APt.along (jD N L) (APt.toMagnet (N.prod L)
          (eh.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst M M))) * ch)) := by
      rw [← specLift_comp, hπt, hmag, APt.res_mul, hra, ← APt.toMagnet_res, hrh]
    have e2 : π ≫ specLift tQ aU = specLift tm (APt.along (jD N L) ch) := by
      rw [← specLift_comp, hπt, hra]
    have e3 : (yoneda.obj U).map π.op (aX.smul hU (specLift tQ aU ≫ x₀)) =
        aX.smul (APt.res π.op hU) ((yoneda.obj U).map π.op (specLift tQ aU ≫ x₀)) :=
      aX.map_smul π.op hU _
    change _ = (yoneda.obj U).map π.op (aX.smul hU (specLift tQ aU ≫ x₀))
    rw [e3, hrh]
    change _ = aX.smul eh (π ≫ specLift tQ aU ≫ x₀)
    have eL : π ≫ specLift tQ (APt.toMagnet (N ⊓ L) hU * aU) ≫ x₀ = aX.smul eh (φ.app tm ch) := by
      rw [← Category.assoc, e1, lift_x₀ hx, hφsm]
    have eR : π ≫ specLift tQ aU ≫ x₀ = φ.app tm ch := by
      rw [← Category.assoc, e2, lift_x₀ hx]
    rw [eL, eR]
  -- pull back along the classifying morphism
  let pt : APt (fppfO B S hS) P₂ (op T') :=
    APt.along (AddMonoidHom.fst _ _) a * APt.along (AddMonoidHom.snd _ _) h
  let ξ : T' ⟶ Q := specLift t pt
  have hξt : ξ ≫ tQ = t := specLift_pr t pt
  have hξa : APt.res ξ.op aU = a := by
    refine MonoidHom.ext fun p => ?_
    have e := res_specLift t pt
    refine (congrArg (fun z => z (AddMonoidHom.toMultiplicative (AddMonoidHom.inl _ _) p)) e).trans ?_
    change a p * h (Multiplicative.ofAdd 0) = a p
    have : h (Multiplicative.ofAdd (0 : M)) = 1 := map_one h
    rw [this, mul_one]
  have hξh : APt.res ξ.op hU = h := by
    refine MonoidHom.ext fun p => ?_
    have e := res_specLift t pt
    refine (congrArg (fun z => z (AddMonoidHom.toMultiplicative (AddMonoidHom.inr _ _) p)) e).trans ?_
    change a (Multiplicative.ofAdd 0) * h p = h p
    have : a (Multiplicative.ofAdd (0 : ↥(N ⊓ L))) = 1 := map_one a
    rw [this, one_mul]
  have e1 := congrArg (fun w => ξ ≫ w) huniv
  have e3 : (yoneda.obj U).map ξ.op (aX.smul hU (specLift tQ aU ≫ x₀)) =
      aX.smul (APt.res ξ.op hU) ((yoneda.obj U).map ξ.op (specLift tQ aU ≫ x₀)) :=
    aX.map_smul ξ.op hU _
  have e4 : ξ ≫ specLift tQ (APt.toMagnet (N ⊓ L) hU * aU) = specLift t (APt.toMagnet (N ⊓ L) h * a) := by
    rw [← specLift_comp, hξt, APt.res_mul, hξa, ← APt.toMagnet_res, hξh]
  have e5 : ξ ≫ specLift tQ aU = specLift t a := by
    rw [← specLift_comp, hξt, hξa]
  simp only at e1
  rw [← Category.assoc, e4] at e1
  refine e1.trans ?_
  refine Eq.trans e3 ?_
  rw [hξh]
  change aX.smul h (ξ ≫ specLift tQ aU ≫ x₀) = _
  rw [← Category.assoc, e5]

/-- The point of `X^{N ∩ L}` given by `f`. -/
noncomputable def chiOf {φ : AttractorPt (biAct aX) (N.prod L) T} {x₀ : specObj ↥(N ⊓ L) T ⟶ U}
    (hx : specAlong T (jD N L) ≫ x₀ = biX φ) : AttractorPt aX (N ⊓ L) T where
  app t a := specLift t a ≫ x₀
  naturality s t a := by
    rw [specLift_comp, Category.assoc]
    rfl
  equivariant t h a := equivariant_x₀ hx t h a

/-- **Proposition 3.32 (ii)** for `T` affine: existence and uniqueness of `f` with `F = f ∘ m`.
Schemes, proof repaired. -/
theorem existsUnique_toBi_affine (φ : AttractorPt (biAct aX) (N.prod L) T) :
    ∃! χ : AttractorPt aX (N ⊓ L) T, χ.toBi (hKinf N L) = φ := by
  obtain ⟨x₀, hx⟩ := exists_x₀ φ
  refine ⟨chiOf hx, ?_, fun χ hχ => ?_⟩
  · refine AttractorPt.ext ?_
    funext T' t c
    exact lift_x₀ hx t c
  · refine AttractorPt.ext ?_
    funext T' t a
    have e1 : ∀ {T' : BigFppfOver B S hS} (t : T' ⟶ T) (a : APt (fppfO B S hS) ↥(N ⊓ L) (op T')),
        χ.app t a = specLift t a ≫ χ.app (specPr _ T) (specPt _ T) :=
      fun t a => χ.app_eq_of_universal (specUniversal (N ⊓ L) T) t a
    have e2 : χ.app (specPr _ T) (specPt _ T) = x₀ := by
      apply toScheme_map_injective
      refine desc_unique (monCoact_isInv (R := Γ((SCH).obj T, ⊤)) (δ := dlt N L) jD_inj
        dlt_eq_zero).isSplit ?_
      have e0 : ∀ w : specObj ↥(N ⊓ L) T ⟶ U, sp (monι (jD N L) Γ((SCH).obj T, ⊤)) ≫ (SCH).map w =
          (SCH).map (specAlong T (jD N L) ≫ w) := fun w => by
        rw [Functor.map_comp]
        rfl
      rw [e0, e0, hx]
      congr 1
      have e3 : specAlong T (jD N L) ≫ χ.app (specPr _ T) (specPt _ T) = biX φ := by
        have e4 := e1 (specPr _ T) (APt.along (jD N L) (specPt ↥(N.prod L) T))
        rw [specLift_along] at e4
        have e5 : specLift (specPr ↥(N.prod L) T) (specPt ↥(N.prod L) T) = 𝟙 _ :=
          (specLift_uniq _ _ _ (Category.id_comp _) (by simp)).symm
        rw [e5, Category.id_comp] at e4
        rw [← e4, ← hχ]
        rfl
      exact e3
    exact (e1 t a).trans (congrArg (specLift t a ≫ ·) e2)

end Bi

section Glue

variable {M : Type u} [AddCommGroup M] [AddMonoid.FG M]
variable {U : BigFppfOver B S hS} {aX : AAction (fppfO B S hS) M (yoneda.obj U)}
  {N L : AddSubmonoid M}

lemma baseChange_comp' {M' : Type*} [AddCommMonoid M'] {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {act : AAction (fppfO B S hS) M' F} {K : AddSubmonoid M'} {T Y W : BigFppfOver B S hS}
    (a : W ⟶ Y) (b : Y ⟶ T) (φ : AttractorPt act K T) :
    AttractorPt.baseChange (a ≫ b) φ = AttractorPt.baseChange a (AttractorPt.baseChange b φ) := by
  refine AttractorPt.ext ?_
  funext T' t c
  change φ.app (t ≫ a ≫ b) c = φ.app ((t ≫ a) ≫ b) c
  rw [Category.assoc]

lemma toBi_baseChange {T Y : BigFppfOver B S hS} (s : Y ⟶ T) (χ : AttractorPt aX (N ⊓ L) T) :
    (AttractorPt.baseChange s χ).toBi (hKinf N L) =
      AttractorPt.baseChange s (χ.toBi (hKinf N L)) := rfl

/-- **Step (4), uniqueness**, for an arbitrary `T`. Schemes, proof repaired. -/
theorem toBi_injective (T : BigFppfOver B S hS) :
    Function.Injective fun χ : AttractorPt aX (N ⊓ L) T => χ.toBi (hKinf N L) := by
  have : AddGroup.FG M := AddGroup.fg_iff_addMonoid_fg.mpr inferInstance
  have : Countable M := countable_of_fg M
  intro χ χ' h
  obtain ⟨I, V, π, hV, hcov⟩ := exists_affine_cover T
  have hsh := isSheaf_attractor aX (N ⊓ L) _ (BigFppfOver.isSheaf_of_type_yoneda_obj U)
  refine (hsh _ hcov).isSeparatedFor.ext ?_
  rintro Y g ⟨W, a, b, ⟨i⟩, rfl⟩
  have := hV i
  have e : AttractorPt.baseChange (π i) χ = AttractorPt.baseChange (π i) χ' :=
    (existsUnique_toBi_affine (AttractorPt.baseChange (π i) (χ.toBi (hKinf N L)))).unique
      (toBi_baseChange _ _) ((toBi_baseChange _ _).trans (congrArg _ h.symm))
  change AttractorPt.baseChange (a ≫ π i) χ = AttractorPt.baseChange (a ≫ π i) χ'
  rw [baseChange_comp', baseChange_comp', e]

/-- **Proposition 3.32 (ii)**, the descent for an arbitrary `T`, glued from affine `T`. Schemes, proof
repaired. -/
theorem exists_toBi {T : BigFppfOver B S hS} (φ : AttractorPt (biAct aX) (N.prod L) T) :
    ∃ χ : AttractorPt aX (N ⊓ L) T, χ.toBi (hKinf N L) = φ := by
  have : AddGroup.FG M := AddGroup.fg_iff_addMonoid_fg.mpr inferInstance
  have : Countable M := countable_of_fg M
  obtain ⟨I, V, π, hV, hcov⟩ := exists_affine_cover T
  have hsh := isSheaf_attractor aX (N ⊓ L) _ (BigFppfOver.isSheaf_of_type_yoneda_obj U)
  have hshB := isSheaf_attractor (biAct aX) (N.prod L) _ (BigFppfOver.isSheaf_of_type_yoneda_obj U)
  have key : ∀ {Y : BigFppfOver B S hS} (g : Y ⟶ T), (Sieve.ofArrows V π) g →
      ∃ χ : AttractorPt aX (N ⊓ L) Y, χ.toBi (hKinf N L) = AttractorPt.baseChange g φ := by
    rintro Y g ⟨W, a, b, ⟨i⟩, rfl⟩
    have := hV i
    obtain ⟨χ, hχ, -⟩ := existsUnique_toBi_affine (AttractorPt.baseChange (π i) φ)
    refine ⟨AttractorPt.baseChange a χ, ?_⟩
    rw [toBi_baseChange, hχ, baseChange_comp']
  choose x hx using @key
  have hcomp : Presieve.FamilyOfElements.Compatible (P := attractor aX (N ⊓ L))
      (R := (Sieve.ofArrows V π).arrows) (fun _ g hg => x g hg) := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ comm
    apply toBi_injective Z
    change (AttractorPt.baseChange g₁ (x f₁ h₁)).toBi _ = (AttractorPt.baseChange g₂ (x f₂ h₂)).toBi _
    rw [toBi_baseChange, toBi_baseChange, hx, hx, ← baseChange_comp', ← baseChange_comp', comm]
  have hamal := (hsh _ hcov).isAmalgamation hcomp
  let t : AttractorPt aX (N ⊓ L) T := (hsh _ hcov).amalgamate _ hcomp
  refine ⟨t, (hshB _ hcov).isSeparatedFor.ext ?_⟩
  intro Y g hg
  have e : AttractorPt.baseChange g t = x g hg := hamal g hg
  exact (toBi_baseChange g t).symm.trans
    ((congrArg (fun χ => AttractorPt.toBi (hKinf N L) χ) e).trans (hx g hg))

/-- **Proposition 3.32 (ii)**: `(X^N)^L = X^{N ∩ L}`, `F = f ∘ m` and `f ↦ F` is bijective. `X` is a
scheme over an arbitrary `S`, with no atlas; `M` is a finitely generated abelian group. Schemes, proof
repaired: the printed step *free action, fpqc quotient* is replaced by the descent `AlgMag.SQ.exists_desc`
along the Reynolds operator. -/
theorem prop332_scheme (T : BigFppfOver B S hS) :
    Function.Bijective (iterOfInf : AttractorPt aX (N ⊓ L) T → IterPt aX N L T) := by
  constructor
  · intro χ χ' h
    exact toBi_injective T ((iterEquivBi T).symm.injective h)
  · intro Ψ
    obtain ⟨χ, hχ⟩ := exists_toBi Ψ.toBi
    refine ⟨χ, ?_⟩
    apply (iterEquivBi T).injective
    rw [iterOfInf, Equiv.apply_symm_apply]
    exact hχ

/-- `X^N = X^L` implies `X^{N ∩ L} = X^N`, `X` a separated scheme. The case of two magnets of
**Fact 3.34**. Schemes, proof repaired. -/
theorem attractorImage_inf_of_eq_scheme (hsep : IsSeparatedOver (yoneda.obj U))
    (h : attractorImage aX N = attractorImage aX L) :
    attractorImage aX (N ⊓ L) = attractorImage aX N := by
  refine le_antisymm (attractorImage_monotone aX inf_le_left) ?_
  intro T x hx
  rw [h] at hx
  obtain ⟨ψ, rfl⟩ := hx
  obtain ⟨Ψ, hΨ⟩ := exists_iter_of_image_eq (isAlgebraicSpace_yoneda B S hS U) hsep h ψ
  obtain ⟨χ, hχ⟩ := exists_toBi Ψ.toBi
  refine ⟨χ, ?_⟩
  have e := AttractorPt.toPoint_toBi (hKinf N L) χ
  rw [hχ, IterPt.toPoint_toBi, hΨ] at e
  exact e.symm

/-- **Fact 3.34** for a finite family, `X` a separated scheme over an arbitrary `S`, no atlas. Schemes,
proof repaired. -/
theorem fact334_finite_scheme (hsep : IsSeparatedOver (yoneda.obj U)) {s : Set (AddSubmonoid M)}
    (hfin : s.Finite) (y) (hne : s.Nonempty) (hy : ∀ N ∈ s, attractorImage aX N = y) :
    attractorImage aX (sInf s) = y := by
  induction s, hfin using Set.Finite.induction_on with
  | empty => exact absurd hne Set.not_nonempty_empty
  | @insert N s' _ _ ih =>
    rw [sInf_insert]
    rcases s'.eq_empty_or_nonempty with rfl | hs'
    · simpa using hy N (Set.mem_insert _ _)
    · have e := ih hs' fun K hK => hy K (Set.mem_insert_of_mem _ hK)
      rw [attractorImage_inf_of_eq_scheme hsep ((hy N (Set.mem_insert _ _)).trans e.symm)]
      exact hy N (Set.mem_insert _ _)

/-- **Proposition 15.1**, `X` a separated scheme over an arbitrary `S`, no atlas. Schemes, proof
repaired. -/
theorem prop151_scheme (hsep : IsSeparatedOver (yoneda.obj U)) (N : AddSubmonoid M) :
    IsPure (attractorImage aX) N ↔ ∀ L, L < N → attractorImage aX L < attractorImage aX N := by
  constructor
  · intro h L hL
    exact IsPure.attractorImage_lt aX h hL
  · intro h L e
    by_contra hNL
    have hlt : N ⊓ L < N := lt_of_le_of_ne inf_le_left fun e' => hNL (inf_eq_left.mp e')
    have := h _ hlt
    rw [attractorImage_inf_of_eq_scheme hsep e] at this
    exact lt_irrefl _ this

end Glue

end AlgMag

#print axioms AlgMag.SQ.exists_desc
#print axioms AlgMag.SQ.desc_unique
#print axioms AlgMag.existsUnique_toBi_affine
#print axioms AlgMag.prop332_scheme
#print axioms AlgMag.attractorImage_inf_of_eq_scheme
#print axioms AlgMag.fact334_finite_scheme
#print axioms AlgMag.prop151_scheme
