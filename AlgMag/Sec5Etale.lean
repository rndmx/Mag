/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec3Rest
import AlgMag.Cutoff
import StacksFrontier.AlgebraicGeometry.Spaces.Representability
import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeLocal
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Order.WellFoundedSet
import Mathlib.Data.Finsupp.Order
import Mathlib.GroupTheory.Finiteness
import Mathlib.Data.Pi.Interval
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Base change of affine étale morphisms along faces: the formal steps

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026) 126–201, §5.

Let `S` be a scheme, `X` an algebraic space with an action of `D(M)_S`, `M` an abelian group, `N` a
magnet, `Q` a face of `N`, and `U → X` étale equivariant, `U` an `S`-affine scheme.

The paper takes `M` finitely generated. The proofs use only `#M < B.cutoff` (the hypothesis
`[Fact (Cardinal.mk M < B.cutoff)]`), which puts `Spec R[M]` in the site; it holds for `M` finitely
generated or countable (`fact_cutoff_of_fg`, `fact_cutoff_of_countable`). Lemmas that use no negation
are stated for commutative monoids.

* `AlgMag.faceComparison`: the natural map `U^N → X^N ×_{X^Q} U^Q`.
* `AlgMag.isFaceCartesian_of_fg`: **Proposition 5.1 (i)**, for `X` separated (an assumption that the
  paper does not state in (i)).
* `AlgMag.isFaceCartesian_of_separated`: **Proposition 5.1 (ii)**, for `X` limit preserving.
* `AlgMag.IsFaceCartesian.of_face`: the reduction to the face `N^×` of the paper. It is not used: the
  direct proof treats all faces, without passing to `M/N^×`.

The proof differs from the paper's at one place. For a face `Q` of a finitely generated `N`, the
powers of the ideal of `𝔸(Q)_T` in `𝔸(N)_T` have trivial intersection (`exists_not_mem_faceL`), so
the lifts on `V(I^k)` give a map to `R[N]` directly (`exists_limit_hom`), and that this map lies over
`X` is `eq_of_forall_restrict_eq`.
-/

open CategoryTheory Opposite

universe v u

namespace AlgMag

section Formal

variable {C : Type*} [Category.{v} C] {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}} {M : Type*} [AddCommMonoid M]
variable {U X : Cᵒᵖ ⥤ Type u} {aU : AAction 𝒪 M U} {aX : AAction 𝒪 M X}

lemma IsFace.trans' {E Q N : AddSubmonoid M} (hE : IsFace E Q) (hQ : IsFace Q N) : IsFace E N :=
  ⟨hE.le.trans hQ.le, fun hx hy h => by
    have h' := hQ.mem_of_add_mem hx hy (hE.le h)
    exact hE.mem_of_add_mem h'.1 h'.2 h⟩

lemma APt.faceExt_trans {E Q N : AddSubmonoid M} (hE : IsFace E Q) (hQ : IsFace Q N) {V : Cᵒᵖ}
    (a : APt 𝒪 E V) :
    APt.faceExt (hE.trans' hQ) a = APt.faceExt hQ (APt.faceExt hE a) := by
  refine MonoidHom.ext fun n => ?_
  by_cases hnQ : ((Multiplicative.toAdd n : N) : M) ∈ Q
  · rw [APt.faceExt_pos hQ _ hnQ]
    by_cases hnE : ((Multiplicative.toAdd n : N) : M) ∈ E
    · rw [APt.faceExt_pos _ _ hnE]
      exact (APt.faceExt_pos hE a (n := Multiplicative.ofAdd ⟨_, hnQ⟩) hnE).symm
    · rw [APt.faceExt_neg _ _ hnE]
      exact (APt.faceExt_neg hE a (n := Multiplicative.ofAdd ⟨_, hnQ⟩) hnE).symm
  · rw [APt.faceExt_neg hQ _ hnQ, APt.faceExt_neg _ _ (fun h => hnQ (hE.le h))]

lemma AttractorPt.ofFace_trans {E Q N : AddSubmonoid M} (hE : IsFace E Q) (hQ : IsFace Q N) {T : C}
    (φ : AttractorPt aU N T) :
    AttractorPt.ofFace (hE.trans' hQ) φ = AttractorPt.ofFace hE (AttractorPt.ofFace hQ φ) := by
  refine AttractorPt.ext ?_
  funext T' t a
  change φ.app t (APt.faceExt _ a) = φ.app t (APt.faceExt hQ (APt.faceExt hE a))
  rw [APt.faceExt_trans]

lemma AttractorPt.push_ofFace (f : EquivariantHom aU aX) {Q N : AddSubmonoid M} (hQ : IsFace Q N)
    {T : C} (φ : AttractorPt aU N T) :
    AttractorPt.push f (AttractorPt.ofFace hQ φ) = AttractorPt.ofFace hQ (AttractorPt.push f φ) :=
  rfl

/-- The natural map of **Proposition 5.1**, `U^N(T) → X^N(T) ×_{X^Q(T)} U^Q(T)`. -/
noncomputable def faceComparison (f : EquivariantHom aU aX) {Q N : AddSubmonoid M} (hQ : IsFace Q N)
    (T : C) (φ : AttractorPt aU N T) :
    {p : AttractorPt aX N T × AttractorPt aU Q T //
      AttractorPt.ofFace hQ p.1 = AttractorPt.push f p.2} :=
  ⟨(AttractorPt.push f φ, AttractorPt.ofFace hQ φ), rfl⟩

/-- The conclusion of **Proposition 5.1** for the face `Q` of `N`: the natural map is bijective on
points. -/
def IsFaceCartesian (f : EquivariantHom aU aX) {Q N : AddSubmonoid M} (hQ : IsFace Q N) : Prop :=
  ∀ T : C, Function.Bijective (faceComparison f hQ T)

/-- The reduction in the proof of **Proposition 5.1 (i)**: if `E` is a face of `Q` and `Q` a face of
`N`, and the natural maps for `(N, E)` and `(Q, E)` are bijective, so is the one for `(N, Q)`. In the
paper `E = N^×`. -/
theorem IsFaceCartesian.of_face (f : EquivariantHom aU aX) {E Q N : AddSubmonoid M}
    (hE : IsFace E Q) (hQ : IsFace Q N) (hNE : IsFaceCartesian f (hE.trans' hQ))
    (hQE : IsFaceCartesian f hE) : IsFaceCartesian f hQ := by
  intro T
  constructor
  · intro φ ψ h
    have h1 : AttractorPt.push f φ = AttractorPt.push f ψ := congrArg (fun p => p.1.1) h
    have h2 : AttractorPt.ofFace hQ φ = AttractorPt.ofFace hQ ψ := congrArg (fun p => p.1.2) h
    refine (hNE T).1 (Subtype.ext (Prod.ext h1 ?_))
    change AttractorPt.ofFace (hE.trans' hQ) φ = AttractorPt.ofFace (hE.trans' hQ) ψ
    rw [AttractorPt.ofFace_trans hE hQ, AttractorPt.ofFace_trans hE hQ, h2]
  · rintro ⟨⟨x, w⟩, hxw⟩
    change AttractorPt.ofFace hQ x = AttractorPt.push f w at hxw
    obtain ⟨u, hu⟩ := (hNE T).2 ⟨(x, AttractorPt.ofFace hE w), by
      change AttractorPt.ofFace (hE.trans' hQ) x = AttractorPt.push f (AttractorPt.ofFace hE w)
      rw [AttractorPt.ofFace_trans hE hQ, hxw]
      rfl⟩
    have hu1 : AttractorPt.push f u = x := congrArg (fun p => p.1.1) hu
    have hu2 : AttractorPt.ofFace (hE.trans' hQ) u = AttractorPt.ofFace hE w :=
      congrArg (fun p => p.1.2) hu
    refine ⟨u, Subtype.ext (Prod.ext hu1 ?_)⟩
    refine (hQE T).1 (Subtype.ext (Prod.ext ?_ ?_))
    · change AttractorPt.push f (AttractorPt.ofFace hQ u) = AttractorPt.push f w
      rw [AttractorPt.push_ofFace, hu1, hxw]
    · change AttractorPt.ofFace hE (AttractorPt.ofFace hQ u) = AttractorPt.ofFace hE w
      rw [← AttractorPt.ofFace_trans hE hQ, hu2]

end Formal

section Sharp

variable {M : Type*} [AddCommGroup M]

/-- Part of the proof of **Proposition 5.1 (i)**. Let `N` be a sharp submonoid of a group generated
by a finite set `g`. Then an element `m` is a sum of `k` nonzero elements of `N` only for bounded
`k`. This is the reason why the map to the completion lands in `𝒪_T[N]`. -/
theorem exists_not_sum_of_sharp {N : AddSubmonoid M} (hsharp : ∀ x ∈ N, ∀ y ∈ N, x + y = 0 → x = 0)
    (hfg : N.FG) (m : M) :
    ∃ k : ℕ, ∀ l : List M, (∀ x ∈ l, x ∈ N ∧ x ≠ 0) → l.sum = m → l.length < k := by
  classical
  obtain ⟨g, hg⟩ := hfg
  let ι := {x // x ∈ g ∧ x ≠ (0 : M)}
  have : Fintype ι := Fintype.subtype (g.filter (· ≠ 0)) (by simp)
  let rep : (ι → ℕ) → M := fun a => ∑ i, a i • (i.1 : M)
  have hgN : ∀ i : ι, (i.1 : M) ∈ N := fun i => hg ▸ AddSubmonoid.subset_closure i.2.1
  have hsmul : ∀ (n : ℕ) (i : ι), n • (i.1 : M) ∈ N := fun n i => N.nsmul_mem (hgN i) n
  have hrepN : ∀ a, rep a ∈ N := fun a => N.sum_mem fun i _ => hsmul _ i
  -- representations with zero value vanish
  have hzero : ∀ c : ι → ℕ, rep c = 0 → c = 0 := by
    intro c hc
    funext i
    by_contra hci
    have hsplit : rep c = c i • (i.1 : M) + ∑ j ∈ Finset.univ.erase i, c j • (j.1 : M) :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
    have h1 := hsharp _ (hsmul (c i) i) _ (N.sum_mem fun j _ => hsmul _ j) (hsplit ▸ hc)
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hci
    rw [hn, Nat.succ_eq_add_one, add_nsmul, one_nsmul] at h1
    have h2 := hsharp _ (hgN i) _ (hsmul n i) (by rw [add_comm]; exact h1)
    exact i.2.2 h2
  have hadd : ∀ a b, rep (a + b) = rep a + rep b := fun a b => by
    simp [rep, add_nsmul, Finset.sum_add_distrib]
  have hA : {a | rep a = m}.Finite := by
    have hanti : IsAntichain (· ≤ ·) {a | rep a = m} := by
      intro a ha b hb hne hle
      apply hne
      have hb' : b = a + (b - a) := by
        funext i; simp [Nat.add_sub_cancel' (hle i)]
      have h0 : rep (b - a) = 0 := by
        have : rep a + rep (b - a) = rep a + 0 := by
          have ha' : rep a = m := ha
          have hb'' : rep b = m := hb
          rw [← hadd, ← hb', add_zero, ha', hb'']
        exact add_left_cancel this
      rw [hb', hzero _ h0, add_zero]
    exact hanti.finite_of_partiallyWellOrderedOn
      (Set.partiallyWellOrderedOn_of_wellQuasiOrdered wellQuasiOrdered_le _)
  obtain ⟨K, hK⟩ := (hA.image fun a => ∑ i, a i).bddAbove
  refine ⟨K + 1, fun l hl hs => ?_⟩
  have hrep : ∀ x ∈ N, ∃ a, rep a = x := by
    intro x hx
    rw [← hg] at hx
    induction hx using AddSubmonoid.closure_induction with
    | mem x hx =>
      by_cases h0 : x = 0
      · exact ⟨0, by simp [rep, h0]⟩
      · exact ⟨Pi.single ⟨x, hx, h0⟩ 1, by
          simp only [rep, Pi.single_apply, ite_smul, one_smul, zero_smul]
          rw [Finset.sum_ite_eq' Finset.univ _ (fun j : ι => (j.1 : M))]
          simp⟩
    | zero => exact ⟨0, by simp [rep]⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, hadd a b⟩
  have hlist : ∀ l : List M, (∀ x ∈ l, x ∈ N ∧ x ≠ 0) →
      ∃ a, rep a = l.sum ∧ l.length ≤ ∑ i, a i := by
    intro l
    induction l with
    | nil => exact fun _ => ⟨0, by simp [rep], by simp⟩
    | cons x t ih =>
      intro h
      obtain ⟨a, ha, hlen⟩ := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
      obtain ⟨hxN, hx0⟩ := h x List.mem_cons_self
      obtain ⟨b, hb⟩ := hrep x hxN
      have hb0 : 1 ≤ ∑ i, b i := by
        by_contra hlt
        have : ∑ i, b i = 0 := by omega
        have hb' : b = 0 := by
          funext i
          exact (Finset.sum_eq_zero_iff.1 this) i (Finset.mem_univ i)
        exact hx0 (by rw [← hb, hb']; simp [rep])
      refine ⟨b + a, by rw [hadd, ha, hb, List.sum_cons], ?_⟩
      simp only [Pi.add_apply, Finset.sum_add_distrib, List.length_cons]
      omega
  obtain ⟨a, ha, hlen⟩ := hlist l hl
  have := hK (Set.mem_image_of_mem _ (ha.trans hs : rep a = m))
  omega

end Sharp

end AlgMag



namespace AlgMag

open scoped Classical

/-! ### The filtration of `R[N]` attached to a face -/

section Filtration

variable {M : Type*} [AddCommGroup M] (Q N : AddSubmonoid M)

/-- `L k`: the elements of `N` that are sums of `k` elements of `N \ Q` and of an element of `N`.
The monomials in `L k` span the `k`-th power of the ideal of `𝔸(Q)_T` in `𝔸(N)_T` (the `I^k` of the
proof of **Proposition 5.1 (i)**). -/
def faceL : ℕ → Set N
  | 0 => Set.univ
  | k + 1 => {n | ∃ p m : N, (p : M) ∉ Q ∧ m ∈ faceL k ∧ n = p + m}

variable {Q N}

lemma faceL_add {k : ℕ} {n : N} (hn : n ∈ faceL Q N k) (r : N) : n + r ∈ faceL Q N k := by
  induction k generalizing n with
  | zero => exact Set.mem_univ _
  | succ k ih =>
    obtain ⟨p, m, hp, hm, rfl⟩ := hn
    exact ⟨p, m + r, hp, ih hm, add_assoc _ _ _⟩

lemma faceL_succ_subset {k : ℕ} {n : N} (hn : n ∈ faceL Q N (k + 1)) : n ∈ faceL Q N k := by
  induction k generalizing n with
  | zero => exact Set.mem_univ _
  | succ k ih =>
    obtain ⟨p, m, hp, hm, rfl⟩ := hn
    exact ⟨p, m, hp, ih hm, rfl⟩

lemma faceL_anti {k l : ℕ} (h : l ≤ k) {n : N} (hn : n ∈ faceL Q N k) : n ∈ faceL Q N l := by
  induction h with
  | refl => exact hn
  | step _ ih => exact ih (faceL_succ_subset hn)

lemma faceL_add_mem {k l : ℕ} {n m : N} (hn : n ∈ faceL Q N k) (hm : m ∈ faceL Q N l) :
    n + m ∈ faceL Q N (k + l) := by
  induction k generalizing n with
  | zero =>
    rw [Nat.zero_add, add_comm]
    exact faceL_add hm n
  | succ k ih =>
    obtain ⟨p, m', hp, hm', rfl⟩ := hn
    rw [Nat.succ_add]
    exact ⟨p, m' + m, hp, ih hm', add_assoc _ _ _⟩

lemma faceL_one_iff {n : N} (hQ : IsFace Q N) : n ∈ faceL Q N 1 ↔ (n : M) ∉ Q := by
  constructor
  · rintro ⟨p, m, hp, -, rfl⟩ h
    exact hp (hQ.mem_of_add_mem p.2 m.2 h).1
  · intro h
    exact ⟨n, 0, h, Set.mem_univ _, (add_zero _).symm⟩

/-- For a face `Q` of a finitely generated `N`, each element lies in finitely many `L k`: the
powers of `I` have trivial intersection (proof of **Proposition 5.1 (i)**). This holds for every
face, so no passage to `M/N^×` is required. -/
theorem exists_not_mem_faceL (hQ : IsFace Q N) (hN : N.FG) (n : N) :
    ∃ k, n ∉ faceL Q N k := by
  let Z : AddSubgroup M := AddSubgroup.closure (Q : Set M)
  have hZ : ∀ x ∈ Z, ∃ a ∈ Q, ∃ b ∈ Q, x = a - b := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx => exact ⟨x, hx, 0, Q.zero_mem, by simp⟩
    | zero => exact ⟨0, Q.zero_mem, 0, Q.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      obtain ⟨c, hc, d, hd, rfl⟩ := hy
      exact ⟨a + c, Q.add_mem ha hc, b + d, Q.add_mem hb hd, by abel⟩
    | neg x _ hx =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      exact ⟨b, hb, a, ha, by abel⟩
  let π : M →+ M ⧸ Z := QuotientAddGroup.mk' Z
  have hπ : ∀ x ∈ N, π x = 0 → x ∈ Q := by
    intro x hx h0
    obtain ⟨a, ha, b, hb, e⟩ := hZ x ((QuotientAddGroup.eq_zero_iff x).1 h0)
    have e' : x + b = a := by rw [e]; abel
    exact (hQ.mem_of_add_mem hx (hQ.le hb) (e' ▸ ha)).1
  let N' : AddSubmonoid (M ⧸ Z) := N.map π
  have hsharp : ∀ x ∈ N', ∀ y ∈ N', x + y = 0 → x = 0 := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
    have h : x + y ∈ Q := hπ _ (N.add_mem hx hy) (by rw [map_add]; exact hxy)
    have hxQ := (hQ.mem_of_add_mem hx hy h).1
    exact (QuotientAddGroup.eq_zero_iff x).2 (AddSubgroup.subset_closure hxQ)
  obtain ⟨K, hK⟩ := exists_not_sum_of_sharp hsharp (hN.map π) (π n)
  refine ⟨K, fun hn => ?_⟩
  have key : ∀ (k : ℕ) (m : N), m ∈ faceL Q N k →
      ∃ l : List (M ⧸ Z), (∀ x ∈ l, x ∈ N' ∧ x ≠ 0) ∧ l.sum = π m ∧ k ≤ l.length := by
    intro k
    induction k with
    | zero =>
      intro m _
      by_cases h : π m = 0
      · exact ⟨[], by simp, by simp [h], by simp⟩
      · exact ⟨[π m], by simpa using ⟨⟨m, m.2, rfl⟩, h⟩, by simp, by simp⟩
    | succ k ih =>
      rintro _ ⟨p, m, hp, hm, rfl⟩
      obtain ⟨l, hl, hs, hlen⟩ := ih m hm
      refine ⟨π p :: l, ?_, ?_, by simpa using hlen⟩
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact ⟨⟨p, p.2, rfl⟩, fun h => hp (hπ _ p.2 h)⟩
        · exact hl x hx
      · simp [hs]
  obtain ⟨l, hl, hs, hlen⟩ := key K n hn
  have := hK l hl hs
  omega

end Filtration

section Ring

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] {Q N : AddSubmonoid M}

lemma exists_coeff_ne_of_coeff_mul_ne {P : Type*} [AddMonoid P] {A : Type*} [Semiring A]
    {x y : AddMonoidAlgebra A P} {n : P} (h : (x * y).coeff n ≠ 0) :
    ∃ a b, x.coeff a ≠ 0 ∧ y.coeff b ≠ 0 ∧ a + b = n := by
  by_contra hne
  apply h
  rw [AddMonoidAlgebra.coeff_mul]
  refine Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => ?_
  beta_reduce
  rw [ite_eq_right_iff]
  exact fun e => absurd e fun e => hne ⟨a, b, Finsupp.mem_support_iff.1 ha, Finsupp.mem_support_iff.1 hb, e⟩

variable (R Q N) in
/-- The ideal `I^k` of `R[N]`: the elements supported on `L k`. -/
def faceJ (k : ℕ) : Ideal (AddMonoidAlgebra R N) where
  carrier := {x | ∀ n, x.coeff n ≠ 0 → n ∈ faceL Q N k}
  add_mem' {x y} hx hy n h := by
    by_cases hxn : x.coeff n = 0
    · refine hy n fun hyn => h ?_
      simp [hxn, hyn]
    · exact hx n hxn
  zero_mem' n h := absurd rfl h
  smul_mem' c x hx n h := by
    obtain ⟨a, b, -, hb, rfl⟩ := exists_coeff_ne_of_coeff_mul_ne h
    rw [add_comm]
    exact faceL_add (hx b hb) a

lemma mem_faceJ {k : ℕ} {x : AddMonoidAlgebra R N} :
    x ∈ faceJ R Q N k ↔ ∀ n, x.coeff n ≠ 0 → n ∈ faceL Q N k := Iff.rfl

lemma faceJ_anti {k l : ℕ} (h : l ≤ k) : faceJ R Q N k ≤ faceJ R Q N l :=
  fun _ hx n hn => faceL_anti h (hx n hn)

lemma faceJ_mul (k l : ℕ) : faceJ R Q N k * faceJ R Q N l ≤ faceJ R Q N (k + l) := by
  refine Ideal.mul_le.2 fun x hx y hy n h => ?_
  obtain ⟨a, b, ha, hb, rfl⟩ := exists_coeff_ne_of_coeff_mul_ne h
  exact faceL_add_mem (hx a ha) (hy b hb)

lemma faceJ_one_pow (k : ℕ) : faceJ R Q N 1 ^ k ≤ faceJ R Q N k := by
  induction k with
  | zero => rw [pow_zero]; exact fun _ _ n _ => Set.mem_univ n
  | succ k ih =>
    rw [pow_succ]
    exact (Ideal.mul_mono_left ih).trans (faceJ_mul k 1)

lemma faceJ_inter (hL : ∀ n : N, ∃ k, n ∉ faceL Q N k) (x : AddMonoidAlgebra R N)
    (h : ∀ k, x ∈ faceJ R Q N k) : x = 0 := by
  refine AddMonoidAlgebra.coeff_injective (Finsupp.ext fun n => ?_)
  by_contra hn
  obtain ⟨k, hk⟩ := hL n
  exact hk (h k n hn)

/-- The ring `R[N]/I^k`. -/
abbrev faceS (R : Type*) [CommRing R] (Q N : AddSubmonoid M) (k : ℕ) : Type _ :=
  AddMonoidAlgebra R N ⧸ faceJ R Q N k

/-- The transition map `R[N]/I^k → R[N]/I^l`. -/
noncomputable def faceTr {k l : ℕ} (h : l ≤ k) : faceS R Q N k →+* faceS R Q N l :=
  Ideal.Quotient.factor (faceJ_anti h)

@[simp] lemma faceTr_mk {k l : ℕ} (h : l ≤ k) (x : AddMonoidAlgebra R N) :
    faceTr h (Ideal.Quotient.mk (faceJ R Q N k) x) = Ideal.Quotient.mk _ x := rfl

lemma faceTr_surjective {k l : ℕ} (h : l ≤ k) : Function.Surjective (faceTr (R := R) (Q := Q) (N := N) h) :=
  Ideal.Quotient.factor_surjective _

/-- `R[N]/I^k → R[N]/I^l` is a nilpotent thickening when `l = 1`. -/
lemma faceTr_ker_nilpotent (k : ℕ) (hk : 1 ≤ k) :
    IsNilpotent (RingHom.ker (faceTr (R := R) (Q := Q) (N := N) hk)) := by
  refine ⟨k, ?_⟩
  rw [Ideal.zero_eq_bot, eq_bot_iff]
  have hker : RingHom.ker (faceTr (R := R) (Q := Q) (N := N) hk) ≤
      (faceJ R Q N 1).map (Ideal.Quotient.mk (faceJ R Q N k)) := by
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.mem_map_of_mem _ (Ideal.Quotient.eq_zero_iff_mem.1 hx)
  refine (Ideal.pow_right_mono hker k).trans ?_
  rw [← Ideal.map_pow]
  refine Ideal.map_le_iff_le_comap.2 fun x hx => ?_
  exact Ideal.Quotient.eq_zero_iff_mem.2 (faceJ_one_pow k hx)

end Ring

section RingMonoid

variable {R : Type*} [CommRing R] {M : Type*} [AddCommMonoid M] {N : AddSubmonoid M}

variable (R M) in
/-- The ideal of `A[M]` of the elements with coefficients in an ideal. -/
def coeffIdeal {A : Type*} [CommRing A] (I : Ideal A) : Ideal (AddMonoidAlgebra A M) where
  carrier := {x | ∀ m, x.coeff m ∈ I}
  add_mem' {x y} hx hy m := by
    simpa using I.add_mem (hx m) (hy m)
  zero_mem' m := by simp
  smul_mem' c x hx m := by
    change (c * x).coeff m ∈ I
    rw [AddMonoidAlgebra.coeff_mul]
    exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => by
      beta_reduce
      split_ifs
      · exact I.mul_mem_left _ (hx b)
      · exact I.zero_mem

lemma coeffIdeal_mul {A : Type*} [CommRing A] (I K : Ideal A) :
    coeffIdeal M I * coeffIdeal M K ≤ coeffIdeal M (I * K) := by
  refine Ideal.mul_le.2 fun x hx y hy m => ?_
  rw [AddMonoidAlgebra.coeff_mul]
  exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => by
    beta_reduce
    split_ifs
    · exact Ideal.mul_mem_mul (hx a) (hy b)
    · exact Ideal.zero_mem _

/-- If `π` has nilpotent kernel, so has `π[M]`. Used for `D(M) × V(I^k)` in the proof of the
equivariance of the lifts in **Proposition 5.1 (i)**. -/
lemma mapRingHom_ker_nilpotent {A A' : Type*} [CommRing A] [CommRing A'] (π : A →+* A')
    (h : IsNilpotent (RingHom.ker π)) :
    IsNilpotent (RingHom.ker (AddMonoidAlgebra.mapRingHom M π)) := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n + 1, ?_⟩
  have hn' : ∀ x, x ∈ RingHom.ker π ^ n → x = 0 := fun x hx => by
    rw [hn] at hx
    simpa using hx
  have hker : RingHom.ker (AddMonoidAlgebra.mapRingHom M π) ≤ coeffIdeal M (RingHom.ker π) := by
    intro x hx m
    have := congrArg (fun z => z.coeff m) (RingHom.mem_ker.1 hx)
    exact RingHom.mem_ker.2 (by simpa using this)
  have hp : ∀ j : ℕ, coeffIdeal M (RingHom.ker π) ^ (j + 1) ≤
      coeffIdeal M (RingHom.ker π ^ (j + 1)) := by
    intro j
    induction j with
    | zero => rw [zero_add, pow_one, pow_one]
    | succ j ih =>
      rw [pow_succ, pow_succ (RingHom.ker π)]
      exact (Ideal.mul_mono_left ih).trans (coeffIdeal_mul _ _)
  have hfin : RingHom.ker (AddMonoidAlgebra.mapRingHom M π) ^ (n + 1) ≤ ⊥ := by
    refine (Ideal.pow_right_mono hker _).trans ((hp n).trans fun x hx => ?_)
    have : x = 0 := by
      refine AddMonoidAlgebra.coeff_injective (Finsupp.ext fun m => ?_)
      exact hn' _ (Ideal.pow_le_pow_right (Nat.le_succ n) (hx m))
    simp [this]
  exact le_bot_iff.1 hfin

lemma mapRingHom_surjective' {A A' : Type*} [CommRing A] [CommRing A'] (π : A →+* A')
    (h : Function.Surjective π) : Function.Surjective (AddMonoidAlgebra.mapRingHom M π) := by
  intro y
  induction y using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add p q hp hq =>
    obtain ⟨p₁, rfl⟩ := hp
    obtain ⟨q₁, rfl⟩ := hq
    exact ⟨p₁ + q₁, map_add _ _ _⟩
  | single n r =>
    obtain ⟨s, rfl⟩ := h r
    exact ⟨AddMonoidAlgebra.single n s, AddMonoidAlgebra.mapRingHom_single _ _ _⟩

variable (R N) in
/-- The coaction `R[N] → R[N][M]`, `eₙ ↦ eₙ ⊗ eₙ`, dual to the action of `D(M)` on `𝔸(N)`. -/
noncomputable def faceCoact : AddMonoidAlgebra R N →+* AddMonoidAlgebra (AddMonoidAlgebra R N) M :=
  AddMonoidAlgebra.liftNCRingHom
    ((AddMonoidAlgebra.singleZeroRingHom).comp (AddMonoidAlgebra.singleZeroRingHom))
    { toFun := fun n => AddMonoidAlgebra.single ((Multiplicative.toAdd n : N) : M)
        (AddMonoidAlgebra.single (Multiplicative.toAdd n) 1)
      map_one' := rfl
      map_mul' := fun x y => by
        rw [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.single_mul_single, one_mul]
        rfl }
    (fun _ _ => Commute.all _ _)

lemma faceCoact_single (a : N) (r : R) : faceCoact R N (AddMonoidAlgebra.single a r) =
    AddMonoidAlgebra.single (a : M) (AddMonoidAlgebra.single a r) := by
  have e : AddMonoidAlgebra.single a r =
      AddMonoidAlgebra.single (0 : N) r * AddMonoidAlgebra.single a (1 : R) := by
    rw [AddMonoidAlgebra.single_mul_single]; simp
  rw [e, map_mul]
  simp [faceCoact, AddMonoidAlgebra.single_mul_single]

lemma faceCoact_coeff (x : AddMonoidAlgebra R N) (n : N) :
    (faceCoact R N x).coeff (n : M) = AddMonoidAlgebra.single n (x.coeff n) := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq, AddMonoidAlgebra.single_add]
  | single a r =>
    rw [faceCoact_single]
    by_cases h : a = n
    · subst h; simp
    · have h' : (a : M) ≠ n := fun e => h (Subtype.ext e)
      simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, h, h']

end RingMonoid

section Ring

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] {Q N : AddSubmonoid M}

/-- The passage from `𝒪_T[[N]]` to `𝒪_T[N]` of the proof of **Proposition 5.1 (i)**. A compatible
family of ring maps `φₖ : A → R[N]/I^k`, equivariant for a coaction `γ : A → A[M]`, comes from a
ring map `A → R[N]`: the coaction bounds the support of the image of each element. -/
theorem exists_limit_hom (hL : ∀ n : N, ∃ k, n ∉ faceL Q N k) {A : Type*} [CommRing A]
    (γ : A →+* AddMonoidAlgebra A M) (φ : ∀ k, A →+* faceS R Q N k)
    (hcompat : ∀ {k l} (h : l ≤ k), (faceTr h).comp (φ k) = φ l)
    (hco : ∀ k, 1 ≤ k → ∀ (a : A) (y : AddMonoidAlgebra R N), Ideal.Quotient.mk _ y = φ k a →
      AddMonoidAlgebra.mapRingHom M (Ideal.Quotient.mk (faceJ R Q N k)) (faceCoact R N y) =
        AddMonoidAlgebra.mapRingHom M (φ k) (γ a)) :
    ∃ Φ : A →+* AddMonoidAlgebra R N, ∀ k a, Ideal.Quotient.mk (faceJ R Q N k) (Φ a) = φ k a := by
  -- support bound
  have hsupp : ∀ (k : ℕ), 1 ≤ k → ∀ (a : A) (y : AddMonoidAlgebra R N),
      Ideal.Quotient.mk _ y = φ k a → ∀ n : N, (n : M) ∉ (γ a).coeff.support → n ∉ faceL Q N k → y.coeff n = 0 := by
    intro k hk a y hy n hnF hnL
    have h1 := congrArg (fun z => z.coeff (n : M)) (hco k hk a y hy)
    have h2 : (γ a).coeff (n : M) = 0 := by simpa using hnF
    simp only [AddMonoidAlgebra.coeff_mapRingHom, faceCoact_coeff, h2, map_zero] at h1
    by_contra hne
    have hmem : AddMonoidAlgebra.single n (y.coeff n) ∈ faceJ R Q N k :=
      Ideal.Quotient.eq_zero_iff_mem.1 h1
    exact hnL (hmem n (by simpa using hne))
  have hex : ∀ a : A, ∃ s : AddMonoidAlgebra R N,
      ∀ k, Ideal.Quotient.mk (faceJ R Q N k) s = φ k a := by
    intro a
    -- the finitely many relevant elements of `N`
    let F : Finset N := ((γ a).coeff.support.preimage (fun n : N => (n : M))
      (fun _ _ _ _ e => Subtype.ext e))
    choose kb hkb using hL
    let K := max 1 (F.sup kb)
    have hK1 : 1 ≤ K := le_max_left _ _
    have hKF : ∀ n ∈ F, n ∉ faceL Q N K := fun n hn hmem =>
      hkb n (faceL_anti ((Finset.le_sup (f := kb) hn).trans (le_max_right _ _)) hmem)
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (φ K a)
    let s : AddMonoidAlgebra R N := ∑ n ∈ F, AddMonoidAlgebra.single n (y.coeff n)
    have hs : ∀ n, s.coeff n = if n ∈ F then y.coeff n else 0 := by
      intro n
      simp only [s, AddMonoidAlgebra.coeff_sum, Finsupp.coe_finsetSum, Finset.sum_apply,
        AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
      rw [Finset.sum_ite_eq' F n]
    have hmemF : ∀ n : N, n ∈ F ↔ (n : M) ∈ (γ a).coeff.support := fun n => Finset.mem_preimage
    have hKs : Ideal.Quotient.mk (faceJ R Q N K) s = φ K a := by
      rw [← hy]
      refine (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2 fun n hn => ?_
      by_contra hnL
      apply hn
      have hsy : (s - y).coeff n = s.coeff n - y.coeff n := by simp
      rw [hsy, hs]
      split_ifs with hF
      · simp
      · rw [hsupp K hK1 a y hy n (by rwa [hmemF] at hF) hnL]; simp
    refine ⟨s, fun k => ?_⟩
    rcases le_total k K with hkK | hKk
    · rw [← hcompat hkK]
      change _ = faceTr hkK (φ K a)
      rw [← hKs]
      rfl
    · obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (φ k a)
      rw [← hz]
      refine (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2 fun n hn => ?_
      by_contra hnL
      apply hn
      have hzK : Ideal.Quotient.mk (faceJ R Q N K) z = φ K a := by
        rw [← hcompat hKk]
        change _ = faceTr hKk (φ k a)
        rw [← hz]
        rfl
      have hdiff : s - z ∈ faceJ R Q N K :=
        (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).1 (hKs.trans hzK.symm)
      have hsz : (s - z).coeff n = s.coeff n - z.coeff n := by simp
      rw [hsz]
      by_cases hF : n ∈ F
      · by_contra hne
        exact hKF n hF (hdiff n (by rw [hsz]; exact hne))
      · have h1 : s.coeff n = 0 := by rw [hs, if_neg hF]
        have h2 := hsupp k (hK1.trans hKk) a z hz n (by rwa [hmemF] at hF) hnL
        rw [h1, h2]; simp
  choose s hs using hex
  have hinj : ∀ x y : AddMonoidAlgebra R N,
      (∀ k, Ideal.Quotient.mk (faceJ R Q N k) x = Ideal.Quotient.mk (faceJ R Q N k) y) → x = y := by
    intro x y h
    exact sub_eq_zero.1 (faceJ_inter hL _ fun k =>
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).1 (h k))
  exact ⟨{ toFun := s
           map_one' := hinj _ _ fun k => by simp [hs]
           map_mul' := fun a b => hinj _ _ fun k => by simp [hs]
           map_zero' := hinj _ _ fun k => by simp [hs]
           map_add' := fun a b => hinj _ _ fun k => by simp [hs] }, fun k a => hs a k⟩

lemma mapMk_coact_eq_zero {k : ℕ} {x : AddMonoidAlgebra R N} (hx : x ∈ faceJ R Q N k) :
    AddMonoidAlgebra.mapRingHom M (Ideal.Quotient.mk (faceJ R Q N k)) (faceCoact R N x) = 0 := by
  have hx' : x = ∑ n ∈ x.coeff.support, AddMonoidAlgebra.single n (x.coeff n) := by
    refine AddMonoidAlgebra.coeff_injective (Finsupp.ext fun n => ?_)
    simp only [AddMonoidAlgebra.coeff_sum, Finsupp.coe_finsetSum, Finset.sum_apply,
      AddMonoidAlgebra.coeff_single]
    simp [Finsupp.single_apply]
  rw [hx', map_sum, map_sum]
  refine Finset.sum_eq_zero fun n hn => ?_
  rw [faceCoact_single, AddMonoidAlgebra.mapRingHom_single,
    Ideal.Quotient.eq_zero_iff_mem.2 ?_, AddMonoidAlgebra.single_zero]
  intro m hm
  have : m = n := by
    by_contra h
    simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Ne.symm h] at hm
  rw [this]
  exact hx n (Finsupp.mem_support_iff.1 hn)

/-- The coaction on `R[N]/I^k`: `I^k` is a graded ideal. -/
noncomputable def coactS (k : ℕ) : faceS R Q N k →+* AddMonoidAlgebra (faceS R Q N k) M :=
  Ideal.Quotient.lift _ ((AddMonoidAlgebra.mapRingHom M (Ideal.Quotient.mk (faceJ R Q N k))).comp
    (faceCoact R N)) fun _ hx => mapMk_coact_eq_zero hx

@[simp] lemma coactS_mk (k : ℕ) (x : AddMonoidAlgebra R N) :
    coactS (Q := Q) k (Ideal.Quotient.mk _ x) =
      AddMonoidAlgebra.mapRingHom M (Ideal.Quotient.mk (faceJ R Q N k)) (faceCoact R N x) := rfl

lemma faceCoact_inter (hL : ∀ n : N, ∃ k, n ∉ faceL Q N k) (x : AddMonoidAlgebra (AddMonoidAlgebra R N) M)
    (h : ∀ k, 1 ≤ k → AddMonoidAlgebra.mapRingHom M (Ideal.Quotient.mk (faceJ R Q N k)) x = 0) :
    x = 0 := by
  refine AddMonoidAlgebra.coeff_injective (Finsupp.ext fun m => ?_)
  refine faceJ_inter (Q := Q) hL _ fun k => ?_
  have : x.coeff m ∈ faceJ R Q N (k + 1) := by
    have := congrArg (fun z => z.coeff m) (h (k + 1) (Nat.le_add_left _ _))
    exact Ideal.Quotient.eq_zero_iff_mem.1 (by simpa using this)
  exact faceJ_anti (Nat.le_succ k) this

end Ring

end AlgMag

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry


namespace AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "Sch" => BigFppfOver.toScheme B S hS

attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

section Generic

/-- Size: an object of the site gives `Spec Γ`. -/
lemma contains_RT (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] :
    B.Contains (Spec (.of (RT T))) :=
  (Scheme.size_congr ((Sch).obj T).isoSpec).symm.trans_lt T.left.property

/-- Size: Tag 000R (9)(b). -/
lemma contains_ft (A R' : Type u) [CommRing A] [CommRing R'] [Algebra A R']
    [Algebra.FiniteType A R'] (h : B.Contains (Spec (.of A))) : B.Contains (Spec (.of R')) :=
  Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit A R' h

variable {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
variable {R' R₀ : Type u} [CommRing R'] [CommRing R₀] {ρ : RT T →+* R'} {ρ₀ : RT T →+* R₀}
  {hC : B.Contains (Spec (.of R'))} {hC₀ : B.Contains (Spec (.of R₀))}

lemma spMap_id : spMap T (hC := hC) (hC' := hC) (RingHom.id R') (RingHom.id_comp ρ) = 𝟙 _ := by
  refine site_hom_ext ?_
  change Spec.map (CommRingCat.ofHom (RingHom.id R')) = 𝟙 _
  exact Spec.map_id _

/-- Value of a point of an attractor on `Spec R'`, and base change. -/
lemma app_sp {M : Type u} [AddCommMonoid M] {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {act : AAction (fppfO B S hS) M F} {P : AddSubmonoid M} (φ : AttractorPt act P T)
    (π : R' →+* R₀) (hπ : π.comp ρ = ρ₀) (ν : Multiplicative P →* R') :
    F.map (spMap T (hC := hC) (hC' := hC₀) π hπ).op (φ.app (spToT T ρ hC) (spPt ν)) =
      φ.app (spToT T ρ₀ hC₀) (spPt (π.toMonoidHom.comp ν)) := by
  have h := φ.naturality (spMap T (hC := hC) (hC' := hC₀) π hπ) (spToT T ρ hC) (spPt ν)
  rw [spMap_toT, spPt_res] at h
  exact h.symm

variable {U : BigFppfOver B S hS} [IsAffineHom U.hom.hom]
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Infinitesimal lifting along `Spec R' → Spec R₀`. -/
theorem sp_lift (hX : IsSeparatedOver X) {f : yoneda.obj U ⟶ X}
    (hf : (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (Sch)).presheaf f)
    (π : R' →+* R₀) (hπ : π.comp ρ = ρ₀) (hs : Function.Surjective π)
    (hn : IsNilpotent (RingHom.ker π))
    (τ : X.obj (op (spObj T ρ hC))) (v₀ : spObj T ρ₀ hC₀ ⟶ U)
    (hv₀ : f.app (op (spObj T ρ₀ hC₀)) v₀ = X.map (spMap T (hC := hC) (hC' := hC₀) π hπ).op τ) :
    ∃! v : spObj T ρ hC ⟶ U, spMap T (hC := hC) (hC' := hC₀) π hπ ≫ v = v₀ ∧
      f.app (op (spObj T ρ hC)) v = τ := by
  refine existsUnique_etale_lift hX hf _ ?_ ?_ τ v₀ hv₀
  · intro y
    obtain ⟨z, rfl⟩ := (spSec_bijective T ρ₀ hC₀).2 y
    obtain ⟨r, rfl⟩ := hs z
    exact ⟨spSec T ρ hC r, spMap_appTop T π hπ r⟩
  · obtain ⟨n, hn⟩ := hn
    refine ⟨n, ?_⟩
    have hle : RingHom.ker ((Sch).map (spMap T (hC := hC) (hC' := hC₀) π hπ)).appTop.hom ≤
        (RingHom.ker π).map (spSec T ρ hC) := by
      intro x hx
      obtain ⟨y, rfl⟩ := (spSec_bijective T ρ hC).2 x
      have h0 : spSec T ρ₀ hC₀ (π y) = 0 := (spMap_appTop T π hπ y).symm.trans hx
      have : π y = 0 := (spSec_bijective T ρ₀ hC₀).1 (h0.trans (map_zero _).symm)
      exact Ideal.mem_map_of_mem _ this
    refine le_bot_iff.1 ((Ideal.pow_right_mono hle n).trans ?_)
    rw [← Ideal.map_pow, hn]
    simp

end Generic

section Gamma

variable {M : Type u} [AddCommMonoid M] [Fact (Cardinal.mk M < B.cutoff)]
variable {T U : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  [IsAffineHom U.hom.hom]
variable {R' : Type u} [CommRing R']

/-- The structure map `R → R[M]`. -/
noncomputable def jr (R' : Type u) [CommRing R'] (M : Type u) [AddCommMonoid M] :
    RH R' (AddMonoidAlgebra R' M) :=
  AddMonoidAlgebra.singleZeroRingHom

/-- The universal point `M → R[M]`. -/
noncomputable def eM (R' : Type u) [CommRing R'] (M : Type u) [AddCommMonoid M] :
    Multiplicative M →* AddMonoidAlgebra R' M where
  toFun n := AddMonoidAlgebra.single (Multiplicative.toAdd n) 1
  map_one' := rfl
  map_mul' x y := by
    rw [AddMonoidAlgebra.single_mul_single, one_mul]; rfl

/-- `π[M]`. -/
noncomputable def mapR {A C : Type u} [CommRing A] [CommRing C] (π : A →+* C) (M : Type u)
    [AddCommMonoid M] : RH (AddMonoidAlgebra A M) (AddMonoidAlgebra C M) :=
  AddMonoidAlgebra.mapRingHom M π

lemma mapR_jr {A C : Type u} [CommRing A] [CommRing C] (π : A →+* C) :
    (mapR π M).comp (jr A M) = (jr C M).comp π := by
  refine RingHom.ext fun x => ?_
  change AddMonoidAlgebra.mapRingHom M π (AddMonoidAlgebra.single 0 x) = AddMonoidAlgebra.single 0 (π x)
  exact AddMonoidAlgebra.mapRingHom_single _ _ _

lemma mapR_eM {A C : Type u} [CommRing A] [CommRing C] (π : A →+* C) :
    (mapR π M).toMonoidHom.comp (eM A M) = eM C M := by
  refine MonoidHom.ext fun n => ?_
  refine (AddMonoidAlgebra.mapRingHom_single _ _ _).trans ?_
  rw [map_one]
  rfl

lemma contains_M {R' : Type u} [CommRing R'] (h : B.Contains (Spec (.of R'))) :
    B.Contains (Spec (.of (AddMonoidAlgebra R' M))) :=
  contains_addMonoidAlgebra Fact.out h

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

lemma spMap_congr {R₁ R₂ : Type u} [CommRing R₁] [CommRing R₂] {ρ₁ : RT T →+* R₁} {ρ₂ : RT T →+* R₂}
    {h₁ : B.Contains (Spec (.of R₁))} {h₂ : B.Contains (Spec (.of R₂))} {π π' : R₁ →+* R₂}
    (hπ : π.comp ρ₁ = ρ₂) (hπ' : π'.comp ρ₁ = ρ₂) (e : π = π') :
    spMap T (hC := h₁) (hC' := h₂) π hπ = spMap T (hC := h₁) (hC' := h₂) π' hπ' := by
  subst e; rfl

/-- The coaction `γ : A → A[M]` on the algebra of `U_T` defined by the action, in the form used in
the proof of **Proposition 5.1 (i)**: the action of the universal point of `D(M)` on a point of `U`
given by `ψ : A → R'` corresponds to `ψ[M] ∘ γ`. -/
theorem exists_gamma (T U : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsAffineHom U.hom.hom] (aU : AAction (fppfO B S hS) M (yoneda.obj U)) :
    ∃ (γ : RH (chartA T U) (AddMonoidAlgebra (chartA T U) M))
      (hγ : γ.comp (chartα T U) = (jr _ M).comp (chartα T U)),
      ∀ {R' : Type u} [CommRing R'] {ρ : RT T →+* R'} (hC : B.Contains (Spec (.of R')))
        (ψ : chartA T U →+* R') (hψ : ψ.comp (chartα T U) = ρ),
        aU.smul (U := op (spObj T ((jr R' M).comp ρ) (contains_M hC))) (spPt (eM R' M))
          (spMap T (hC := hC) (hC' := contains_M hC) (jr R' M) rfl ≫ ptOf ψ hψ) =
        ptOf (hC := contains_M hC) ((mapR ψ M).comp γ) (by
          rw [RingHom.comp_assoc, hγ, ← RingHom.comp_assoc, mapR_jr, RingHom.comp_assoc, hψ]) := by
  have hA : B.Contains (Spec (.of (chartA T U))) := contains_RT (chartObj T U)
  let vA : spObj T (chartα T U) hA ⟶ U := ptOf (RingHom.id _) (RingHom.id_comp _)
  let VA := aU.smul (U := op (spObj T ((jr _ M).comp (chartα T U)) (contains_M hA)))
    (spPt (eM _ M)) (spMap T (hC := hA) (hC' := contains_M hA) (jr _ M) rfl ≫ vA)
  obtain ⟨γ, hγ, hγV⟩ := exists_ptOf (T := T) (U := U) (hC := contains_M hA) VA
  refine ⟨γ, hγ, ?_⟩
  intro R' _ ρ hC ψ hψ
  have hπ : (mapR ψ M).comp ((jr _ M).comp (chartα T U)) = (jr R' M).comp ρ := by
    rw [← RingHom.comp_assoc, mapR_jr, RingHom.comp_assoc, hψ]
  rw [← spMap_comp_ptOf (hC := contains_M hA) (mapR ψ M) hπ γ hγ, hγV]
  have hsm := aU.map_smul (spMap T (hC := contains_M hA) (hC' := contains_M hC) (mapR ψ M) hπ).op
    (spPt (eM _ M)) (spMap T (hC := hA) (hC' := contains_M hA) (jr _ M) rfl ≫ vA)
  refine Eq.trans ?_ hsm.symm
  rw [spPt_res, mapR_eM]
  congr 1
  change _ = spMap T (hC := contains_M hA) (hC' := contains_M hC) (mapR ψ M) hπ ≫
    spMap T (hC := hA) (hC' := contains_M hA) (jr _ M) rfl ≫ vA
  rw [← Category.assoc, spMap_comp]
  have e : (jr R' M).comp ψ = (mapR ψ M).comp (jr _ M) := (mapR_jr ψ).symm
  rw [← spMap_congr (h₁ := hA) (h₂ := contains_M hC) (by rw [RingHom.comp_assoc, hψ]) _ e]
  rw [← spMap_comp T (hC := hA) (hC' := hC) (hC'' := contains_M hC) ψ hψ (jr R' M) rfl, Category.assoc]
  congr 1
  rw [spMap_comp_ptOf (hC := hA) (hC' := hC) ψ hψ (RingHom.id _) (RingHom.id_comp _)]
  rfl

/-- Equivariance of the value of a point of `X^P` on `Spec R'`, for a coaction `c` on `R'`. -/
lemma app_coact {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {act : AAction (fppfO B S hS) M F}
    {P : AddSubmonoid M} (φ : AttractorPt act P T) {ρ : RT T →+* R'}
    (hC : B.Contains (Spec (.of R'))) (ν : Multiplicative P →* R')
    (c : R' →+* AddMonoidAlgebra R' M) (hν : ∀ p : Multiplicative P, c (ν p) =
      AddMonoidAlgebra.single ((Multiplicative.toAdd p : P) : M) (ν p)) :
    φ.app (spToT T ((jr R' M).comp ρ) (contains_M hC)) (spPt (c.toMonoidHom.comp ν)) =
      act.smul (spPt (eM R' M)) (φ.app (spToT T ((jr R' M).comp ρ) (contains_M hC))
        (spPt ((jr R' M).toMonoidHom.comp ν))) := by
  rw [← φ.equivariant]
  congr 1
  refine MonoidHom.ext fun p => ?_
  have key : c (ν p) = eM R' M (Multiplicative.ofAdd ((Multiplicative.toAdd p : P) : M)) *
      jr R' M (ν p) := by
    rw [hν]
    change _ = AddMonoidAlgebra.single _ 1 * AddMonoidAlgebra.single 0 (ν p)
    rw [AddMonoidAlgebra.single_mul_single, one_mul, add_zero]
    rfl
  exact (congrArg (spSec T ((jr R' M).comp ρ) (contains_M hC)) key).trans (map_mul _ _ _)

end Gamma

end AlgMag

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry


namespace AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "Sch" => BigFppfOver.toScheme B S hS

attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

attribute [local irreducible] spObj

section CoreMonoid

variable {M : Type u} [AddCommMonoid M] [Fact (Cardinal.mk M < B.cutoff)]
variable {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] {N : AddSubmonoid M}

/-- The coaction `R[N] → R[N][M]`. -/
noncomputable def cN (T : BigFppfOver B S hS) (N : AddSubmonoid M) :
    RH (AddMonoidAlgebra (RT T) N) (AddMonoidAlgebra (AddMonoidAlgebra (RT T) N) M) :=
  faceCoact _ N

lemma cN_ρN : (cN T N).comp (ρN T N) = (jr _ M).comp (ρN T N) := by
  refine RingHom.ext fun r => ?_
  refine (faceCoact_single (0 : N) r).trans ?_
  rfl

/-- The ring map `R[N][M] → Γ(T')` of a pair of points of `𝔸(N)` and of `𝔸(M)`. -/
noncomputable def pairRing {T' : BigFppfOver B S hS} (t : T' ⟶ T)
    (h : APt (fppfO B S hS) M (op T')) (a : APt (fppfO B S hS) N (op T')) :
    RH (AddMonoidAlgebra (AddMonoidAlgebra (RT T) N) M) Γ((Sch).obj T', ⊤) :=
  AddMonoidAlgebra.liftNCRingHom (pointRing t a)
    (show Multiplicative M →* Γ((Sch).obj T', ⊤) from h) (fun _ _ => Commute.all _ _)

lemma pairRing_single {T' : BigFppfOver B S hS} (t : T' ⟶ T)
    (h : APt (fppfO B S hS) M (op T')) (a : APt (fppfO B S hS) N (op T')) (r) (m : M) :
    pairRing t h a (AddMonoidAlgebra.single m r) = pointRing t a r *
      (show Multiplicative M →* Γ((Sch).obj T', ⊤) from h) (Multiplicative.ofAdd m) :=
  lift_single' _ _ _ _ _

lemma pairRing_comp {T' : BigFppfOver B S hS} (t : T' ⟶ T)
    (h : APt (fppfO B S hS) M (op T')) (a : APt (fppfO B S hS) N (op T')) :
    (pairRing t h a).comp ((jr _ M).comp (ρN T N)) = ((Sch).map t).appTop.hom := by
  refine RingHom.ext fun x => ?_
  have e : pairRing t h a (AddMonoidAlgebra.single 0 (AddMonoidAlgebra.single 0 x)) =
      ((Sch).map t).appTop.hom x := by
    rw [pairRing_single, ofAdd_zero, map_one, mul_one]
    exact congrArg (fun k : _ →+* _ => k x) (pointRing_comp t a)
  exact e

omit [Fact (Cardinal.mk M < B.cutoff)] [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] in
lemma monN_faceCoact (R : Type*) [CommRing R] (n : Multiplicative N) :
    faceCoact R N (monN R N n) = AddMonoidAlgebra.single ((Multiplicative.toAdd n : N) : M) (monN R N n) :=
  faceCoact_single _ _

end CoreMonoid

section Core

variable {M : Type u} [AddCommGroup M] [Fact (Cardinal.mk M < B.cutoff)]
variable {T U : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  [IsAffineHom U.hom.hom]
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
variable {aU : AAction (fppfO B S hS) M (yoneda.obj U)} {aX : AAction (fppfO B S hS) M X}
variable {Q N : AddSubmonoid M}

/-- `R[N] → R[N]/I^k`. -/
noncomputable def mkS (T : BigFppfOver B S hS) (Q N : AddSubmonoid M) (k : ℕ) :
    RH (AddMonoidAlgebra (RT T) N) (faceS (RT T) Q N k) :=
  Ideal.Quotient.mk _

/-- `R → R[N]/I^k`. -/
noncomputable def ρS (T : BigFppfOver B S hS) (Q N : AddSubmonoid M) (k : ℕ) :
    RH (RT T) (faceS (RT T) Q N k) :=
  (mkS T Q N k).comp (ρN T N)

/-- `R[N]/I^k → R[N]/I^l`. -/
noncomputable def trS (T : BigFppfOver B S hS) {Q N : AddSubmonoid M} {k l : ℕ} (h : l ≤ k) :
    RH (faceS (RT T) Q N k) (faceS (RT T) Q N l) :=
  faceTr h

/-- The coaction on `R[N]/I^k`. -/
noncomputable def cS (T : BigFppfOver B S hS) (Q N : AddSubmonoid M) (k : ℕ) :
    RH (faceS (RT T) Q N k) (AddMonoidAlgebra (faceS (RT T) Q N k) M) :=
  coactS k

lemma trS_ρS {k l : ℕ} (h : l ≤ k) : (trS T (Q := Q) (N := N) h).comp (ρS T Q N k) = ρS T Q N l := rfl

/-- The monoid map `N → R[N]/I^k`. -/
noncomputable def νS (T : BigFppfOver B S hS) (Q N : AddSubmonoid M) (k : ℕ) :
    Multiplicative N →* faceS (RT T) Q N k :=
  (mkS T Q N k).toMonoidHom.comp (monN _ N)

/-- The monoid map `Q → R[N]/I`, for `Q` a face of `N`. -/
noncomputable def νQ (T : BigFppfOver B S hS) (hQ : IsFace Q N) :
    Multiplicative Q →* faceS (RT T) Q N 1 :=
  (νS T Q N 1).comp (AddMonoidHom.toMultiplicative (AddSubmonoid.inclusion hQ.le))

lemma νS_one_eq_zero (n : Multiplicative N) (hQ : IsFace Q N)
    (h : ((Multiplicative.toAdd n : N) : M) ∉ Q) : νS T Q N 1 n = 0 := by
  refine Ideal.Quotient.eq_zero_iff_mem.2 fun m hm => ?_
  have e : m = Multiplicative.toAdd n := by
    by_contra hne
    exact hm (by simp [monN, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Ne.symm hne])
  rw [e]
  exact (faceL_one_iff hQ).2 h

lemma faceExt_νQ (hQ : IsFace Q N) (hC : B.Contains (Spec (.of (faceS (RT T) Q N 1)))) :
    APt.faceExt hQ (spPt (T := T) (ρ := ρS T Q N 1) (hC := hC) (νQ T hQ)) = spPt (νS T Q N 1) := by
  refine MonoidHom.ext fun n => ?_
  by_cases h : ((Multiplicative.toAdd n : N) : M) ∈ Q
  · rw [APt.faceExt_pos hQ _ h]
    rfl
  · rw [APt.faceExt_neg hQ _ h, spPt_apply, νS_one_eq_zero n hQ h, map_zero]
    rfl

lemma contains_N (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (hN : N.FG) : B.Contains (Spec (.of (AddMonoidAlgebra (RT T) N))) :=
  haveI : AddMonoid.FG N := (AddMonoid.fg_iff_addSubmonoid_fg N).2 hN
  haveI := AddMonoidAlgebra.finiteType_of_fg (RT T) N
  contains_ft (RT T) _ (contains_RT T)

lemma contains_S (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (Q : AddSubmonoid M) (hN : N.FG) (k : ℕ) : B.Contains (Spec (.of (faceS (RT T) Q N k))) :=
  haveI : Algebra.FiniteType (AddMonoidAlgebra (RT T) N) (faceS (RT T) Q N k) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ (AddMonoidAlgebra (RT T) N) _)
      Ideal.Quotient.mk_surjective
  contains_ft _ _ (contains_N T hN)

variable (f : EquivariantHom aU aX) (hX : IsSeparatedOver X)
  (hf : (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf f.hom)
  (hQ : IsFace Q N) (hN : N.FG)

include hX hf in
/-- The lifts `fₖ : V(I^k) → U_T` of the proof of **Proposition 5.1 (i)**. -/
theorem exists_lift_S (x : AttractorPt aX N T) (w : AttractorPt aU Q T)
    (hxw : AttractorPt.ofFace hQ x = AttractorPt.push f w) (k : ℕ) (hk : 1 ≤ k) :
    ∃! v : spObj T (ρS T Q N k) (contains_S T Q hN k) ⟶ U,
      spMap T (hC := contains_S T Q hN k) (hC' := contains_S T Q hN 1) (trS T hk) (trS_ρS hk) ≫ v =
        w.app (spToT T (ρS T Q N 1) (contains_S T Q hN 1)) (spPt (νQ T hQ)) ∧
      f.hom.app (op (spObj T (ρS T Q N k) (contains_S T Q hN k))) v = x.app (spToT T (ρS T Q N k) (contains_S T Q hN k)) (spPt (νS T Q N k)) := by
  refine sp_lift hX hf (trS T hk) (trS_ρS hk) (faceTr_surjective hk) (faceTr_ker_nilpotent k hk)
    _ _ ?_
  rw [app_sp]
  have h1 := congrArg (fun χ : AttractorPt aX Q T =>
    χ.app (spToT T (ρS T Q N 1) (contains_S T Q hN 1)) (spPt (νQ T hQ))) hxw
  change x.app _ (APt.faceExt hQ _) = f.hom.app _ _ at h1
  rw [faceExt_νQ] at h1
  exact h1.symm

/-- The coaction on `R[N]/I^k`, as a map over `R`. -/
lemma cS_ρS (k : ℕ) : (cS T Q N k).comp (ρS T Q N k) = (jr _ M).comp (ρS T Q N k) := by
  refine RingHom.ext fun r => ?_
  change coactS (R := RT T) (Q := Q) (N := N) k (Ideal.Quotient.mk _ (AddMonoidAlgebra.single 0 r)) =
    AddMonoidAlgebra.single 0 _
  rw [coactS_mk, faceCoact_single, AddMonoidAlgebra.mapRingHom_single]
  rfl

lemma cS_νS (k : ℕ) (p : Multiplicative N) :
    cS T Q N k (νS T Q N k p) =
      AddMonoidAlgebra.single ((Multiplicative.toAdd p : N) : M) (νS T Q N k p) := by
  change coactS (R := RT T) (Q := Q) (N := N) k (Ideal.Quotient.mk _ (monN _ N p)) = _
  rw [coactS_mk, monN_faceCoact, AddMonoidAlgebra.mapRingHom_single]
  rfl

lemma cS_νQ (hQ : IsFace Q N) (p : Multiplicative Q) :
    cS T Q N 1 (νQ T hQ p) =
      AddMonoidAlgebra.single ((Multiplicative.toAdd p : Q) : M) (νQ T hQ p) :=
  cS_νS 1 _

lemma mapR_tr_cS {k l : ℕ} (h : l ≤ k) :
    (mapR (trS T (Q := Q) (N := N) h) M).comp (cS T Q N k) = (cS T Q N l).comp (trS T h) := by
  refine RingHom.ext fun x => ?_
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction y using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq =>
    simp only [map_add, hp, hq]
  | single n r =>
    change mapR _ M (coactS (R := RT T) (Q := Q) (N := N) k (Ideal.Quotient.mk _ _)) =
      coactS (R := RT T) (Q := Q) (N := N) l (Ideal.Quotient.mk _ _)
    rw [coactS_mk, coactS_mk, faceCoact_single, AddMonoidAlgebra.mapRingHom_single,
      AddMonoidAlgebra.mapRingHom_single]
    exact AddMonoidAlgebra.mapRingHom_single _ _ _

include hX hf in
/-- The equivariance of the lifts in the proof of **Proposition 5.1 (i)**: the two maps
`D(M) × V(I^k) → U` are lifts of the same map, hence equal. In rings, `φₖ` is `M`-graded. -/
theorem lift_S_equivariant (x : AttractorPt aX N T) (w : AttractorPt aU Q T)
    (hxw : AttractorPt.ofFace hQ x = AttractorPt.push f w) (k : ℕ) (hk : 1 ≤ k)
    (γ : RH (chartA T U) (AddMonoidAlgebra (chartA T U) M))
    (hγ : γ.comp (chartα T U) = (jr _ M).comp (chartα T U))
    (hγa : ∀ {R' : Type u} [CommRing R'] {ρ : RT T →+* R'} (hC : B.Contains (Spec (.of R')))
        (ψ : chartA T U →+* R') (hψ : ψ.comp (chartα T U) = ρ),
        aU.smul (U := op (spObj T ((jr R' M).comp ρ) (contains_M hC))) (spPt (eM R' M))
          (spMap T (hC := hC) (hC' := contains_M hC) (jr R' M) rfl ≫ ptOf ψ hψ) =
        ptOf (hC := contains_M hC) ((mapR ψ M).comp γ) (by
          rw [RingHom.comp_assoc, hγ, ← RingHom.comp_assoc, mapR_jr, RingHom.comp_assoc, hψ]))
    (ψ : RH (chartA T U) (faceS (RT T) Q N k)) (hψ : ψ.comp (chartα T U) = ρS T Q N k)
    (hψ₁ : spMap T (hC := contains_S T Q hN k) (hC' := contains_S T Q hN 1) (trS T hk) (trS_ρS hk) ≫
        ptOf ψ hψ = w.app (spToT T (ρS T Q N 1) (contains_S T Q hN 1)) (spPt (νQ T hQ)))
    (hψ₂ : f.hom.app (op (spObj T (ρS T Q N k) (contains_S T Q hN k))) (ptOf (hC := contains_S T Q hN k) ψ hψ) =
      x.app (spToT T (ρS T Q N k) (contains_S T Q hN k)) (spPt (νS T Q N k))) :
    (cS T Q N k).comp ψ = (mapR ψ M).comp γ := by
  have hCk := contains_S T Q hN k
  have hC1 := contains_S T Q hN 1
  have hCkM := contains_M (M := M) hCk
  have hC1M := contains_M (M := M) hC1
  let ρk : RT T →+* AddMonoidAlgebra (faceS (RT T) Q N k) M := (jr _ M).comp (ρS T Q N k)
  let ρ1 : RT T →+* AddMonoidAlgebra (faceS (RT T) Q N 1) M := (jr _ M).comp (ρS T Q N 1)
  have hthick : (mapR (trS T (Q := Q) (N := N) hk) M).comp ρk = ρ1 := by
    change ((mapR _ M).comp (jr _ M)).comp _ = _
    rw [mapR_jr, RingHom.comp_assoc]
    rfl
  let τ : X.obj (op (spObj T ρk hCkM)) := x.app (spToT T ρk hCkM)
    (spPt ((cS T Q N k).toMonoidHom.comp (νS T Q N k)))
  have hc : (cS T Q N k).comp (ρS T Q N k) = ρk := cS_ρS k
  have hc₁ : (cS T Q N 1).comp (ρS T Q N 1) = ρ1 := cS_ρS 1
  -- first lift
  let V₁ : spObj T ρk hCkM ⟶ U := spMap T (hC := hCk) (hC' := hCkM) (cS T Q N k) hc ≫ ptOf ψ hψ
  let V₂ : spObj T ρk hCkM ⟶ U := aU.smul (U := op (spObj T ρk hCkM)) (spPt (eM _ M))
    (spMap T (hC := hCk) (hC' := hCkM) (jr _ M) rfl ≫ ptOf ψ hψ)
  have hV₁ : V₁ = ptOf (hC := hCkM) ((cS T Q N k).comp ψ) (by
      rw [RingHom.comp_assoc, hψ, hc]) := spMap_comp_ptOf _ hc ψ hψ
  have hV₂ : V₂ = ptOf (hC := hCkM) ((mapR ψ M).comp γ) (by
      rw [RingHom.comp_assoc, hγ, ← RingHom.comp_assoc, mapR_jr, RingHom.comp_assoc, hψ]) :=
    hγa hCk ψ hψ
  have hnat : ∀ {V V' : BigFppfOver B S hS} (r : V' ⟶ V) (v : V ⟶ U),
      f.hom.app (op V') (r ≫ v) = X.map r.op (f.hom.app (op V) v) := fun r v =>
    hom_naturality_apply f.hom r.op v
  have hτ₁ : f.hom.app (op (spObj T ρk hCkM)) V₁ = τ :=
    (hnat _ _).trans ((congrArg _ hψ₂).trans (app_sp x _ hc _))
  have hτ₂ : f.hom.app (op (spObj T ρk hCkM)) V₂ = τ := by
    refine (f.map_smul _ _).trans ?_
    refine Eq.trans (congrArg _ ((hnat _ _).trans ((congrArg _ hψ₂).trans (app_sp x _ rfl _)))) ?_
    exact (app_coact (ρ := ρS T Q N k) x hCk (νS T Q N k) (cS T Q N k) (cS_νS k)).symm
  -- their restrictions to `V(I)`
  let wb := w.app (spToT T (ρS T Q N 1) hC1) (spPt (νQ T hQ))
  let v₀ : spObj T ρ1 hC1M ⟶ U :=
    spMap T (hC := hC1) (hC' := hC1M) (cS T Q N 1) hc₁ ≫ wb
  have hr₁ : spMap T (hC := hCkM) (hC' := hC1M) (mapR (trS T hk) M) hthick ≫ V₁ = v₀ := by
    change _ ≫ spMap T _ hc ≫ ptOf ψ hψ = _
    rw [← Category.assoc, spMap_comp T]
    rw [spMap_congr (h₁ := hCk) (h₂ := hC1M) (π' := (cS T Q N 1).comp (trS T hk)) _ (by
      rw [RingHom.comp_assoc, trS_ρS, hc₁]) (mapR_tr_cS hk)]
    rw [← spMap_comp T (hC := hCk) (hC' := hC1) (hC'' := hC1M) (trS T hk) (trS_ρS hk) (cS T Q N 1) hc₁,
      Category.assoc, hψ₁]
  have hr₂ : spMap T (hC := hCkM) (hC' := hC1M) (mapR (trS T hk) M) hthick ≫ V₂ = v₀ := by
    have hsm := aU.map_smul (spMap T (hC := hCkM) (hC' := hC1M) (mapR (trS T hk) M) hthick).op
      (spPt (eM _ M)) (spMap T (hC := hCk) (hC' := hCkM) (jr _ M) rfl ≫ ptOf ψ hψ)
    refine Eq.trans hsm ?_
    rw [spPt_res, mapR_eM]
    have e₁ : (yoneda.obj U).map (spMap T (hC := hCkM) (hC' := hC1M) (mapR (trS T hk) M) hthick).op
        (spMap T (hC := hCk) (hC' := hCkM) (jr _ M) rfl ≫ ptOf ψ hψ) =
        spMap T (hC := hC1) (hC' := hC1M) (jr _ M) rfl ≫ wb := by
      change spMap T _ hthick ≫ spMap T _ rfl ≫ ptOf ψ hψ = _
      rw [← Category.assoc, spMap_comp T]
      rw [spMap_congr (h₁ := hCk) (h₂ := hC1M) (π' := (jr _ M).comp (trS T hk)) _ (by
        rw [RingHom.comp_assoc, trS_ρS]) (mapR_jr _)]
      rw [← spMap_comp T (hC := hCk) (hC' := hC1) (hC'' := hC1M) (trS T hk) (trS_ρS hk) (jr _ M) rfl,
        Category.assoc, hψ₁]
    rw [e₁]
    have e₂ := app_coact (ρ := ρS T Q N 1) w hC1 (νQ T hQ) (cS T Q N 1) (cS_νQ hQ)
    have e₃ := app_sp (hC := hC1) (hC₀ := hC1M) (ρ := ρS T Q N 1) w (cS T Q N 1) hc₁ (νQ T hQ)
    have e₄ := app_sp (hC := hC1) (hC₀ := hC1M) (ρ := ρS T Q N 1) w (jr _ M) rfl (νQ T hQ)
    refine Eq.trans ?_ e₃.symm |>.trans ?_
    · exact (congrArg _ e₄).trans e₂.symm
    · rfl
  -- uniqueness of the lift
  have hτ₀ : f.hom.app (op (spObj T ρ1 hC1M)) v₀ = X.map (spMap T (hC := hCkM) (hC' := hC1M)
      (mapR (trS T hk) M) hthick).op τ := by
    rw [← hτ₁]
    exact (congrArg _ hr₁.symm).trans (hnat _ _)
  obtain ⟨v, -, hu⟩ := sp_lift hX hf (hC := hCkM) (hC₀ := hC1M) (mapR (trS T hk) M) hthick
    (mapRingHom_surjective' _ (faceTr_surjective hk))
    (mapRingHom_ker_nilpotent _ (faceTr_ker_nilpotent k hk)) τ v₀ hτ₀
  have heq : V₁ = V₂ := (hu V₁ ⟨hr₁, hτ₁⟩).trans (hu V₂ ⟨hr₂, hτ₂⟩).symm
  rw [hV₁, hV₂] at heq
  exact ptOf_injective _ _ heq

end Core

end AlgMag

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry


namespace AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "Sch" => BigFppfOver.toScheme B S hS

attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

attribute [local irreducible] spObj

section Core

variable {M : Type u} [AddCommGroup M] [Fact (Cardinal.mk M < B.cutoff)]
variable {T U : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  [IsAffineHom U.hom.hom]
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
variable {aU : AAction (fppfO B S hS) M (yoneda.obj U)} {aX : AAction (fppfO B S hS) M X}
variable {Q N : AddSubmonoid M}

lemma ptOf_congr {R' : Type u} [CommRing R'] {ρ : RT T →+* R'} {hC : B.Contains (Spec (.of R'))}
    {ψ ψ' : chartA T U →+* R'} (hψ : ψ.comp (chartα T U) = ρ) (hψ' : ψ'.comp (chartα T U) = ρ)
    (e : ψ = ψ') : ptOf (hC := hC) ψ hψ = ptOf (hC := hC) ψ' hψ' := by
  subst e; rfl

lemma mapR_comp {A C D : Type u} [CommRing A] [CommRing C] [CommRing D] (π : A →+* C) (π' : C →+* D) :
    mapR (π'.comp π) M = (mapR π' M).comp (mapR π M) := by
  refine RingHom.ext fun x => ?_
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single n r =>
    change AddMonoidAlgebra.mapRingHom M _ _ =
      AddMonoidAlgebra.mapRingHom M _ (AddMonoidAlgebra.mapRingHom M _ _)
    simp [AddMonoidAlgebra.mapRingHom_single]

lemma subsingleton_faceS0 : Subsingleton (faceS (RT T) Q N 0) :=
  Ideal.Quotient.subsingleton_iff.2 (Ideal.eq_top_iff_one _ |>.2 fun _ _ => Set.mem_univ _)

lemma eq_sum_single {R P : Type*} [Semiring R] [AddMonoid P] (x : AddMonoidAlgebra R P) :
    x = ∑ n ∈ x.coeff.support, AddMonoidAlgebra.single n (x.coeff n) := by
  classical
  refine AddMonoidAlgebra.coeff_injective (Finsupp.ext fun n => ?_)
  simp only [AddMonoidAlgebra.coeff_sum, Finsupp.coe_finsetSum, Finset.sum_apply,
    AddMonoidAlgebra.coeff_single]
  simp [Finsupp.single_apply]

variable (f : EquivariantHom aU aX) (hX : IsSeparatedOver X)
  (hf : (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf f.hom)
  (hQ : IsFace Q N) (hN : N.FG)

lemma mk_ρN (k : ℕ) : (mkS T Q N k).comp (ρN T N) = ρS T Q N k := rfl

lemma app_sp_mk (φ : AttractorPt aU N T) (k : ℕ) :
    spMap T (hC := contains_N T hN) (hC' := contains_S T Q hN k) (mkS T Q N k) (mk_ρN k) ≫
        φ.app (spToT T (ρN T N) (contains_N T hN)) (spPt (monN _ N)) =
      φ.app (spToT T (ρS T Q N k) (contains_S T Q hN k)) (spPt (νS T Q N k)) :=
  app_sp φ (mkS T Q N k) (mk_ρN k) (monN _ N)

lemma app_sp_face (φ : AttractorPt aU N T) (k : ℕ) (hk : 1 ≤ k) :
    spMap T (hC := contains_S T Q hN k) (hC' := contains_S T Q hN 1) (trS T hk) (trS_ρS hk) ≫
        φ.app (spToT T (ρS T Q N k) (contains_S T Q hN k)) (spPt (νS T Q N k)) =
      (AttractorPt.ofFace hQ φ).app (spToT T (ρS T Q N 1) (contains_S T Q hN 1))
        (spPt (νQ T hQ)) := by
  refine (app_sp φ (trS T hk) (trS_ρS hk) (νS T Q N k)).trans ?_
  change φ.app _ _ = φ.app _ (APt.faceExt hQ _)
  rw [faceExt_νQ]
  rfl

include hX hf hN in
/-- Injectivity in **Proposition 5.1 (i)**: uniqueness of the filling. -/
theorem faceComparison_injective_affine :
    Function.Injective (faceComparison f hQ T) := by
  intro φ φ' h
  have h1 : AttractorPt.push f φ = AttractorPt.push f φ' := congrArg (fun p => p.1.1) h
  have h2 : AttractorPt.ofFace hQ φ = AttractorPt.ofFace hQ φ' := congrArg (fun p => p.1.2) h
  have hL := exists_not_mem_faceL hQ hN
  have hCN := contains_N (N := N) T hN
  let Uni := spUniversal T N hCN
  suffices key : φ.app Uni.π Uni.u = φ'.app Uni.π Uni.u by
    refine AttractorPt.ext ?_
    funext T' t a
    rw [φ.app_eq_of_universal Uni, φ'.app_eq_of_universal Uni, key]
  obtain ⟨Φ, hΦ, eΦ⟩ := exists_ptOf (T := T) (U := U) (hC := hCN)
    (φ.app (spToT T (ρN T N) hCN) (spPt (monN _ N)))
  obtain ⟨Φ', hΦ', eΦ'⟩ := exists_ptOf (T := T) (U := U) (hC := hCN)
    (φ'.app (spToT T (ρN T N) hCN) (spPt (monN _ N)))
  have hk : ∀ k, 1 ≤ k → (mkS T Q N k).comp Φ = (mkS T Q N k).comp Φ' := by
    intro k hk
    obtain ⟨v, -, hu⟩ := exists_lift_S f hX hf hQ hN (T := T) (AttractorPt.push f φ)
      (AttractorPt.ofFace hQ φ) rfl k hk
    have e₁ := hu (φ.app (spToT T (ρS T Q N k) (contains_S T Q hN k)) (spPt (νS T Q N k)))
      ⟨app_sp_face hQ hN φ k hk, rfl⟩
    have e₂ := hu (φ'.app (spToT T (ρS T Q N k) (contains_S T Q hN k)) (spPt (νS T Q N k)))
      ⟨(app_sp_face hQ hN φ' k hk).trans (by rw [h2]),
        by
          change AttractorPt.app (AttractorPt.push f φ') _ _ = _
          rw [h1]⟩
    have e₃ := e₁.trans e₂.symm
    rw [← app_sp_mk hN φ, ← app_sp_mk hN φ', ← eΦ, ← eΦ', spMap_comp_ptOf, spMap_comp_ptOf] at e₃
    exact ptOf_injective _ _ e₃
  have hΦΦ : Φ = Φ' := by
    refine RingHom.ext fun a => sub_eq_zero.1 (faceJ_inter (Q := Q) hL _ fun k => ?_)
    refine faceJ_anti (Nat.le_succ k) ?_
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).1
      (congrArg (fun g : _ →+* _ => g a) (hk (k + 1) (Nat.le_add_left _ _)))
  subst hΦΦ
  exact eΦ.symm.trans eΦ'

/-- `R[N] → R[N]/I^k` is compatible with the coactions. -/
lemma mapMk_cN (k : ℕ) (y : AddMonoidAlgebra (RT T) N) :
    mapR (mkS T Q N k) M (cN T N y) = cS T Q N k (mkS T Q N k y) := rfl

include hX hf in
/-- Surjectivity in **Proposition 5.1 (i)**: the filling exists, is equivariant, lies over `X`, and
restricts to the given point. For `T` affine and `X` separated. -/
theorem faceComparison_surjective_affine (hN : N.FG) :
    Function.Surjective (faceComparison f hQ T) := by
  rintro ⟨⟨x, w⟩, hxw⟩
  change AttractorPt.ofFace hQ x = AttractorPt.push f w at hxw
  have hL := exists_not_mem_faceL hQ hN
  have hCN := contains_N (N := N) T hN
  have hCNM := contains_M (M := M) hCN
  have hCS := contains_S (N := N) T Q hN
  obtain ⟨γ, hγ, hγa⟩ := exists_gamma (M := M) T U aU
  have hnat : ∀ {V V' : BigFppfOver B S hS} (r : V' ⟶ V) (v : V ⟶ U),
      f.hom.app (op V') (r ≫ v) = X.map r.op (f.hom.app (op V) v) := fun r v =>
    hom_naturality_apply f.hom r.op v
  let wb := w.app (spToT T (ρS T Q N 1) (hCS 1)) (spPt (νQ T hQ))
  -- the lifts, as ring maps
  have hlift : ∀ k, ∃ (ψ : RH (chartA T U) (faceS (RT T) Q N k))
      (hψ : ψ.comp (chartα T U) = ρS T Q N k), ∀ hk : 1 ≤ k,
      spMap T (hC := hCS k) (hC' := hCS 1) (trS T hk) (trS_ρS hk) ≫ ptOf ψ hψ = wb ∧
      f.hom.app (op (spObj T (ρS T Q N k) (hCS k))) (ptOf (hC := hCS k) ψ hψ) =
        x.app (spToT T (ρS T Q N k) (hCS k)) (spPt (νS T Q N k)) := by
    have hk1 : ∀ k (hk : 1 ≤ k), ∃ (ψ : RH (chartA T U) (faceS (RT T) Q N k))
      (hψ : ψ.comp (chartα T U) = ρS T Q N k),
      spMap T (hC := hCS k) (hC' := hCS 1) (trS T hk) (trS_ρS hk) ≫ ptOf ψ hψ = wb ∧
      f.hom.app (op (spObj T (ρS T Q N k) (hCS k))) (ptOf (hC := hCS k) ψ hψ) =
        x.app (spToT T (ρS T Q N k) (hCS k)) (spPt (νS T Q N k)) := by
      intro k hk
      obtain ⟨v, ⟨hv₁, hv₂⟩, -⟩ := exists_lift_S f hX hf hQ hN x w hxw k hk
      obtain ⟨ψ, hψ, rfl⟩ := exists_ptOf (T := T) (U := U) v
      exact ⟨ψ, hψ, hv₁, hv₂⟩
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · obtain ⟨ψ, hψ, -⟩ := hk1 1 le_rfl
      exact ⟨(trS T (Nat.zero_le 1)).comp ψ, by rw [RingHom.comp_assoc, hψ, trS_ρS], fun h => absurd h (by simp)⟩
    · obtain ⟨ψ, hψ, h⟩ := hk1 k hk
      exact ⟨ψ, hψ, fun _ => h⟩
  choose ψ hψ hψp using hlift
  -- compatibility
  have hcompat : ∀ {k l} (h : l ≤ k), (faceTr h).comp (ψ k) = ψ l := by
    intro k l h
    rcases Nat.eq_zero_or_pos l with rfl | hl
    · haveI : Subsingleton (faceS (RT T) Q N 0) := subsingleton_faceS0
      exact RingHom.ext fun _ => Subsingleton.elim _ _
    · have hk : 1 ≤ k := Nat.le_trans hl h
      obtain ⟨v, -, hu⟩ := exists_lift_S f hX hf hQ hN x w hxw l hl
      have e₁ := hu _ (hψp l hl)
      have e₂ := hu (spMap T (hC := hCS k) (hC' := hCS l) (trS T h) (trS_ρS h) ≫ ptOf (ψ k) (hψ k))
        ⟨by
          rw [← Category.assoc, spMap_comp T]
          rw [spMap_congr (h₁ := hCS k) (h₂ := hCS 1) (π' := trS T hk) _ (trS_ρS hk) (by
            refine RingHom.ext fun y => ?_
            obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
            rfl)]
          exact (hψp k hk).1,
         (hnat _ _).trans ((congrArg _ (hψp k hk).2).trans (app_sp x _ _ _))⟩
      rw [spMap_comp_ptOf] at e₂
      exact ptOf_injective _ _ (e₂.trans e₁.symm)
  -- passage to the limit
  have hequi : ∀ k, 1 ≤ k → (cS T Q N k).comp (ψ k) = (mapR (ψ k) M).comp γ := fun k hk =>
    lift_S_equivariant f hX hf hQ hN x w hxw k hk γ hγ hγa (ψ k) (hψ k) (hψp k hk).1 (hψp k hk).2
  obtain ⟨Φ, hΦ⟩ := exists_limit_hom (R := RT T) hL γ ψ hcompat (by
    intro k hk a y hy
    have := congrArg (fun g : _ →+* _ => g a) (hequi k hk)
    change cS T Q N k (ψ k a) = mapR (ψ k) M (γ a) at this
    rw [← hy] at this
    exact this)
  have hinjS : ∀ y y' : AddMonoidAlgebra (RT T) N,
      (∀ k, 1 ≤ k → mkS T Q N k y = mkS T Q N k y') → y = y' := by
    intro y y' h
    refine sub_eq_zero.1 (faceJ_inter (Q := Q) hL _ fun k => faceJ_anti (Nat.le_succ k) ?_)
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).1 (h (k + 1) (Nat.le_add_left _ _))
  have hΦα : Φ.comp (chartα T U) = ρN T N := by
    refine RingHom.ext fun r => hinjS _ _ fun k _ => ?_
    refine (hΦ k _).trans ?_
    exact congrArg (fun g : _ →+* _ => g r) (hψ k)
  let u₀ : spObj T (ρN T N) hCN ⟶ U := ptOf Φ hΦα
  have hk_u : ∀ k, spMap T (hC := hCN) (hC' := hCS k) (mkS T Q N k) (mk_ρN k) ≫ u₀ = ptOf (ψ k) (hψ k) := by
    intro k
    refine (spMap_comp_ptOf (mkS T Q N k) (mk_ρN k) Φ hΦα).trans (ptOf_congr _ _ ?_)
    exact RingHom.ext fun a => hΦ k a
  -- equivariance of `u₀`
  have hgm : ∀ a, cN T N (Φ a) = mapR Φ M (γ a) := by
    intro a
    refine sub_eq_zero.1 (faceCoact_inter (Q := Q) hL _ fun k hk => ?_)
    rw [map_sub, sub_eq_zero]
    refine (mapMk_cN k (Φ a)).trans ?_
    have e₁ : mkS T Q N k (Φ a) = ψ k a := hΦ k a
    rw [e₁]
    have e₂ := congrArg (fun g : _ →+* _ => g a) (hequi k hk)
    refine e₂.trans ?_
    have e₃ : ψ k = (mkS T Q N k).comp Φ := RingHom.ext fun a => (hΦ k a).symm
    change mapR (ψ k) M (γ a) = mapR (mkS T Q N k) M (mapR Φ M (γ a))
    rw [e₃, mapR_comp]
    rfl
  have hkey : spMap T (hC := hCN) (hC' := hCNM) (cN T N) cN_ρN ≫ u₀ =
      aU.smul (U := op (spObj T ((jr _ M).comp (ρN T N)) hCNM)) (spPt (eM _ M))
        (spMap T (hC := hCN) (hC' := hCNM) (jr _ M) rfl ≫ u₀) := by
    refine (spMap_comp_ptOf _ _ Φ hΦα).trans (Eq.trans (ptOf_congr _ ?_ ?_) (hγa hCN Φ hΦα).symm)
    · rw [RingHom.comp_assoc, hγ, ← RingHom.comp_assoc, mapR_jr, RingHom.comp_assoc, hΦα]
    · exact RingHom.ext hgm
  let Uni := spUniversal T N hCN
  have hequiv : ∀ {T' : BigFppfOver B S hS} (t : T' ⟶ T) (h : APt (fppfO B S hS) M (op T'))
      (a : APt (fppfO B S hS) N (op T')),
      (yoneda.obj U).map (Uni.lift t (APt.toMagnet N h * a)).op u₀ =
        aU.smul h ((yoneda.obj U).map (Uni.lift t a).op u₀) := by
    intro T' t h a
    let r : T' ⟶ spObj T ((jr _ M).comp (ρN T N)) hCNM :=
      spLift T _ hCNM t (pairRing t h a) (pairRing_comp t h a)
    have hrπ : r ≫ spToT T _ hCNM = t := spLift_toT T _ hCNM t _ _
    have hra : ∀ x', ((Sch).map r).appTop.hom (spSec T _ hCNM x') = pairRing t h a x' :=
      fun x' => spLift_appTop T _ hCNM t _ _ x'
    have l₁ : r ≫ spMap T (hC := hCN) (hC' := hCNM) (jr _ M) rfl = spUniLift T N hCN t a := by
      refine Uni.uniq t a _ ?_ ?_
      · change (r ≫ spMap T _ rfl) ≫ spToT T (ρN T N) hCN = t
        rw [Category.assoc, spMap_toT, hrπ]
      · change APt.res (r ≫ spMap T _ rfl).op (spPt (monN _ N)) = a
        rw [op_comp, APt.res_comp, spPt_res]
        refine MonoidHom.ext fun n => ?_
        rw [res_spPt_apply, hra]
        change pairRing t h a (AddMonoidAlgebra.single 0 (monN _ N n)) = _
        rw [pairRing_single, ofAdd_zero, map_one, mul_one]
        change pointRing t a (AddMonoidAlgebra.single _ 1) = _
        rw [pointRing_single, map_one, one_mul]
        rfl
    have l₂ : r ≫ spMap T (hC := hCN) (hC' := hCNM) (cN T N) cN_ρN =
        spUniLift T N hCN t (APt.toMagnet N h * a) := by
      refine Uni.uniq t _ _ ?_ ?_
      · change (r ≫ spMap T _ _) ≫ spToT T (ρN T N) hCN = t
        rw [Category.assoc, spMap_toT, hrπ]
      · change APt.res (r ≫ spMap T _ _).op (spPt (monN _ N)) = _
        rw [op_comp, APt.res_comp, spPt_res]
        refine MonoidHom.ext fun n => ?_
        rw [res_spPt_apply, hra]
        have : (cN T N).toMonoidHom.comp (monN _ N) n = AddMonoidAlgebra.single
            ((Multiplicative.toAdd n : N) : M) (monN _ N n) := monN_faceCoact _ n
        rw [this, pairRing_single]
        change pointRing t a (AddMonoidAlgebra.single _ 1) * _ = _
        rw [pointRing_single, map_one, one_mul, mul_comm]
        rfl
    have hres : APt.res r.op (spPt (T := T) (ρ := (jr _ M).comp (ρN T N)) (hC := hCNM) (eM _ M)) = h := by
      refine MonoidHom.ext fun m => ?_
      rw [res_spPt_apply, hra]
      change pairRing t h a (AddMonoidAlgebra.single _ 1) = _
      rw [pairRing_single, map_one, one_mul]
      rfl
    have hsm := aU.map_smul r.op (spPt (eM _ M)) (spMap T (hC := hCN) (hC' := hCNM) (jr _ M) rfl ≫ u₀)
    rw [hres] at hsm
    change spUniLift T N hCN t (APt.toMagnet N h * a) ≫ u₀ = aU.smul h (spUniLift T N hCN t a ≫ u₀)
    rw [← l₁, ← l₂, Category.assoc, Category.assoc, hkey]
    exact hsm
  let uPt : AttractorPt aU N T := (attractorPtEquivOfUniversal Uni).symm ⟨u₀, hequiv⟩
  have hu_app : ∀ {T' : BigFppfOver B S hS} (t : T' ⟶ T) (a : APt (fppfO B S hS) N (op T')),
      uPt.app t a = (yoneda.obj U).map (Uni.lift t a).op u₀ := fun _ _ => rfl
  refine ⟨uPt, Subtype.ext (Prod.ext ?_ ?_)⟩
  · -- `u` lies over `x`
    change AttractorPt.push f uPt = x
    have huni : f.hom.app (op (spObj T (ρN T N) hCN)) u₀ =
        x.app (spToT T (ρN T N) hCN) (spPt (monN _ N)) := by
      refine eq_of_forall_restrict_eq hX (Zk := fun k : {k // 1 ≤ k} =>
        spObj T (ρS T Q N k.1) (hCS k.1))
        (fun k => spMap T (hC := hCN) (hC' := hCS k.1) (mkS T Q N k.1) (mk_ρN k.1)) ?_ ?_
      · intro y hy
        obtain ⟨z, hzy⟩ := (spSec_bijective T (ρN T N) hCN).2 y
        have hz : z = 0 := by
          refine hinjS _ _ fun k hk => ?_
          have h1 : ((Sch).map (spMap T (hC := hCN) (hC' := hCS k) (mkS T Q N k) (mk_ρN k))).appTop.hom
              y = 0 := hy (⟨k, hk⟩ : {k // 1 ≤ k})
          have h2 := spMap_appTop T (hC := hCN) (hC' := hCS k) (mkS T Q N k) (mk_ρN k) z
          have h0 : spSec T (ρS T Q N k) (hCS k) (mkS T Q N k z) = 0 := by
            rw [← h2, hzy]
            exact h1
          rw [map_zero]
          exact (spSec_bijective T (ρS T Q N k) (hCS k)).1 (h0.trans (map_zero _).symm)
        rw [← hzy, hz, map_zero]
      · intro k
        refine (hnat _ _).symm.trans ?_
        rw [hk_u]
        exact ((hψp k.1 k.2).2).trans (app_sp x _ rfl _).symm
    refine AttractorPt.ext ?_
    funext T' t a
    have e₁ := x.app_eq_of_universal Uni t a
    change f.hom.app _ ((yoneda.obj U).map (Uni.lift t a).op u₀) = _
    rw [e₁]
    refine (hom_naturality_apply f.hom (Uni.lift t a).op u₀).trans ?_
    exact congrArg _ huni
  · -- `u` restricts to `w`
    change AttractorPt.ofFace hQ uPt = w
    refine AttractorPt.ext ?_
    funext T' t a
    change uPt.app t (APt.faceExt hQ a) = w.app t a
    have hkill : ∀ y ∈ faceJ (RT T) Q N 1, pointRing t (APt.faceExt hQ a) y = 0 := by
      intro y hy
      rw [eq_sum_single y, map_sum]
      refine Finset.sum_eq_zero fun n hn => ?_
      rw [pointRing_single]
      have hnQ : (n : M) ∉ Q := (faceL_one_iff hQ).1 (hy n (Finsupp.mem_support_iff.1 hn))
      exact mul_eq_zero_of_right _ (APt.faceExt_neg hQ a hnQ)
    let ψa : RH (faceS (RT T) Q N 1) Γ((Sch).obj T', ⊤) :=
      Ideal.Quotient.lift _ (pointRing t (APt.faceExt hQ a)) hkill
    have hψa : ψa.comp (ρS T Q N 1) = ((Sch).map t).appTop.hom :=
      pointRing_comp t (APt.faceExt hQ a)
    let l : T' ⟶ spObj T (ρS T Q N 1) (hCS 1) := spLift T _ (hCS 1) t ψa hψa
    have hlπ : l ≫ spToT T _ (hCS 1) = t := spLift_toT T _ (hCS 1) t _ _
    have hla : ∀ y, ((Sch).map l).appTop.hom (spSec T _ (hCS 1) y) = ψa y :=
      fun y => spLift_appTop T _ (hCS 1) t _ _ y
    have hli : l ≫ spMap T (hC := hCN) (hC' := hCS 1) (mkS T Q N 1) (mk_ρN 1) =
        spUniLift T N hCN t (APt.faceExt hQ a) := by
      refine Uni.uniq t _ _ ?_ ?_
      · change (l ≫ spMap T _ _) ≫ spToT T (ρN T N) hCN = t
        rw [Category.assoc, spMap_toT, hlπ]
      · change APt.res (l ≫ spMap T _ _).op (spPt (monN _ N)) = _
        rw [op_comp, APt.res_comp, spPt_res]
        refine MonoidHom.ext fun n => ?_
        rw [res_spPt_apply, hla]
        change pointRing t _ (AddMonoidAlgebra.single _ 1) = _
        rw [pointRing_single, map_one, one_mul]
        rfl
    have hres : APt.res l.op (spPt (T := T) (ρ := ρS T Q N 1) (hC := hCS 1) (νQ T hQ)) = a := by
      refine MonoidHom.ext fun q => ?_
      rw [res_spPt_apply, hla]
      change pointRing t _ (AddMonoidAlgebra.single _ 1) = _
      rw [pointRing_single, map_one, one_mul]
      exact APt.faceExt_pos hQ a (n := Multiplicative.ofAdd _) (Multiplicative.toAdd q).2
    have h₁ : ptOf (ψ 1) (hψ 1) = wb := by
      have := (hψp 1 le_rfl).1
      have e : spMap T (hC := hCS 1) (hC' := hCS 1) (trS T (le_refl 1)) (trS_ρS _) = 𝟙 _ := by
        rw [← spMap_id (T := T) (ρ := ρS T Q N 1) (hC := hCS 1)]
        refine spMap_congr _ _ (RingHom.ext fun y => ?_)
        obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
        rfl
      rw [e, Category.id_comp] at this
      exact this
    have hw := w.naturality l (spToT T (ρS T Q N 1) (hCS 1)) (spPt (νQ T hQ))
    rw [hlπ, hres] at hw
    refine Eq.trans ?_ hw.symm
    change spUniLift T N hCN t (APt.faceExt hQ a) ≫ u₀ = l ≫ wb
    rw [← hli, Category.assoc, hk_u, h₁]

include hX hf in
/-- **Proposition 5.1**, for `T` affine, `N` finitely generated and `X` separated: for every face `Q`
of `N`, the natural map `U^N(T) → X^N(T) ×_{X^Q(T)} U^Q(T)` is bijective. -/
theorem faceComparison_bijective_affine (hN : N.FG) :
    Function.Bijective (faceComparison f hQ T) :=
  ⟨faceComparison_injective_affine f hX hf hQ hN, faceComparison_surjective_affine f hX hf hQ hN⟩

end Core

end AlgMag

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry


namespace AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "Sch" => BigFppfOver.toScheme B S hS

/-- Every object of the site is covered by affine opens. -/
theorem exists_affine_cover (T : BigFppfOver B S hS) :
    ∃ (I : Type u) (V : I → BigFppfOver B S hS) (π : ∀ i, V i ⟶ T),
      (∀ i, IsAffine ((Sch).obj (V i))) ∧ Sieve.ofArrows V π ∈ BigFppfOver.topology B S hS T := by
  let I := ((Sch).obj T).affineOpens
  have hC : ∀ i : I, B.Contains (i.1 : Scheme.{u}) := fun i =>
    Scheme.size_lt_of_isOpenImmersion i.1.ι T.left.property
  let V : I → BigFppfOver B S hS := fun i => siteObject B S hS (hC i) (i.1.ι ≫ T.hom.hom)
  let π : ∀ i, V i ⟶ T := fun i => siteHom i.1.ι rfl
  refine ⟨I, V, π, fun i => i.2, ?_⟩
  refine BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS π
    (fun i => inferInstanceAs (IsOpenImmersion i.1.ι)) fun x => ?_
  obtain ⟨W, hW, hxW⟩ : ∃ W : ((Sch).obj T).Opens, IsAffineOpen W ∧ x ∈ W := by
    obtain ⟨_, ⟨W, hW, rfl⟩, hx, -⟩ := ((Sch).obj T).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ x) isOpen_univ
    exact ⟨W, hW, hx⟩
  refine ⟨⟨W, hW⟩, ?_⟩
  exact ⟨⟨x, hxW⟩, rfl⟩

section Global

variable {M : Type u} [AddCommGroup M] [Fact (Cardinal.mk M < B.cutoff)]
variable {U : BigFppfOver B S hS} [IsAffineHom U.hom.hom]
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
variable {aU : AAction (fppfO B S hS) M (yoneda.obj U)} {aX : AAction (fppfO B S hS) M X}
variable {Q N : AddSubmonoid M}

lemma push_baseChange (f : EquivariantHom aU aX) {T T' : BigFppfOver B S hS} (s : T' ⟶ T)
    (φ : AttractorPt aU N T) :
    AttractorPt.push f (AttractorPt.baseChange s φ) = AttractorPt.baseChange s (AttractorPt.push f φ) :=
  rfl

lemma ofFace_baseChange {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {act : AAction (fppfO B S hS) M F}
    (hQ : IsFace Q N) {T T' : BigFppfOver B S hS} (s : T' ⟶ T) (φ : AttractorPt act N T) :
    AttractorPt.ofFace hQ (AttractorPt.baseChange s φ) =
      AttractorPt.baseChange s (AttractorPt.ofFace hQ φ) :=
  rfl

/-- Passage from affine `T` to arbitrary `T` in **Proposition 5.1**: the attractors are Zariski
sheaves, and the natural map is bijective as soon as this holds on affine objects. -/
theorem faceComparison_bijective_of_affine (hXs : Presieve.IsSheaf (BigFppfOver.topology B S hS) X)
    (f : EquivariantHom aU aX) (hQ : IsFace Q N)
    (haff : ∀ (T : BigFppfOver B S hS) [IsAffine ((Sch).obj T)],
      Function.Bijective (faceComparison f hQ T)) (T : BigFppfOver B S hS) :
    Function.Bijective (faceComparison f hQ T) := by
  have hUs : Presieve.IsSheaf (BigFppfOver.topology B S hS) (yoneda.obj U) :=
    BigFppfOver.isSheaf_of_type_yoneda_obj U
  have shUN := isSheaf_attractor aU N _ hUs
  have shUQ := isSheaf_attractor aU Q _ hUs
  have shXN := isSheaf_attractor aX N _ hXs
  -- injectivity everywhere
  have hinj : ∀ T : BigFppfOver B S hS, Function.Injective (faceComparison f hQ T) := by
    intro T φ ψ h
    have h1 : AttractorPt.push f φ = AttractorPt.push f ψ := congrArg (fun p => p.1.1) h
    have h2 : AttractorPt.ofFace hQ φ = AttractorPt.ofFace hQ ψ := congrArg (fun p => p.1.2) h
    obtain ⟨I, V, π, hV, hS'⟩ := exists_affine_cover T
    have hsep := shUN _ hS'
    refine hsep.isSeparatedFor.ext fun W g hg => ?_
    obtain ⟨_, a, b, ⟨i⟩, rfl⟩ := hg
    have : IsAffine ((Sch).obj (V i)) := hV i
    have e : AttractorPt.baseChange (π i) φ = AttractorPt.baseChange (π i) ψ :=
      (haff (V i)).1 (Subtype.ext (Prod.ext (congrArg (AttractorPt.baseChange (π i)) h1)
        (congrArg (AttractorPt.baseChange (π i)) h2)))
    exact congrArg (AttractorPt.baseChange a) e
  refine ⟨hinj T, ?_⟩
  rintro ⟨⟨x, w⟩, hxw⟩
  change AttractorPt.ofFace hQ x = AttractorPt.push f w at hxw
  obtain ⟨I, V, π, hV, hS'⟩ := exists_affine_cover T
  have hloc : ∀ i, ∃ u : AttractorPt aU N (V i), AttractorPt.push f u = AttractorPt.baseChange (π i) x ∧
      AttractorPt.ofFace hQ u = AttractorPt.baseChange (π i) w := by
    intro i
    have : IsAffine ((Sch).obj (V i)) := hV i
    obtain ⟨u, hu⟩ := (haff (V i)).2 ⟨(AttractorPt.baseChange (π i) x, AttractorPt.baseChange (π i) w),
      congrArg (AttractorPt.baseChange (π i)) hxw⟩
    exact ⟨u, congrArg (fun p => p.1.1) hu, congrArg (fun p => p.1.2) hu⟩
  choose u hu₁ hu₂ using hloc
  have hsh : (Presieve.ofArrows V π).IsSheafFor (attractor aU N) := by
    rw [Presieve.isSheafFor_iff_generate]
    exact shUN _ hS'
  obtain ⟨t, ht, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).1 hsh u (by
    intro i j Z gi gj hij
    apply hinj Z
    refine Subtype.ext (Prod.ext ?_ ?_)
    · change AttractorPt.push f (AttractorPt.baseChange gi (u i)) =
        AttractorPt.push f (AttractorPt.baseChange gj (u j))
      rw [push_baseChange, push_baseChange, hu₁, hu₁]
      change AttractorPt.baseChange (gi ≫ π i) x = AttractorPt.baseChange (gj ≫ π j) x
      rw [hij]
    · change AttractorPt.ofFace hQ (AttractorPt.baseChange gi (u i)) =
        AttractorPt.ofFace hQ (AttractorPt.baseChange gj (u j))
      rw [ofFace_baseChange, ofFace_baseChange, hu₂, hu₂]
      change AttractorPt.baseChange (gi ≫ π i) w = AttractorPt.baseChange (gj ≫ π j) w
      rw [hij])
  refine ⟨t, Subtype.ext (Prod.ext ?_ ?_)⟩
  · refine (shXN _ hS').isSeparatedFor.ext fun W g hg => ?_
    obtain ⟨_, a, b, ⟨i⟩, rfl⟩ := hg
    have e : AttractorPt.baseChange (π i) (AttractorPt.push f t) = AttractorPt.baseChange (π i) x :=
      (push_baseChange f (π i) t).symm.trans ((congrArg (AttractorPt.push f) (ht i)).trans (hu₁ i))
    exact congrArg (AttractorPt.baseChange a) e
  · refine (shUQ _ hS').isSeparatedFor.ext fun W g hg => ?_
    obtain ⟨_, a, b, ⟨i⟩, rfl⟩ := hg
    have e : AttractorPt.baseChange (π i) (AttractorPt.ofFace hQ t) = AttractorPt.baseChange (π i) w :=
      (ofFace_baseChange hQ (π i) t).symm.trans ((congrArg (AttractorPt.ofFace hQ) (ht i)).trans (hu₂ i))
    exact congrArg (AttractorPt.baseChange a) e

/-- `U → X` étale in the sense of Tag 03FR, for `U` a scheme: its base changes are étale. -/
lemma presheaf_etale_of_isEtale {f : yoneda.obj U ⟶ X} (hf : Space.IsEtale B S hS f) :
    (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (Sch)).presheaf f := by
  have h := hf U (𝟙 _) (by
    refine ⟨MorphismProperty.id_mem _ _, fun a b g fst snd h => ?_⟩
    have h₁ : IsIso (yoneda.map snd) := h.isIso_snd_of_isIso
    have h₂ : IsIso snd := isIso_of_reflects_iso snd yoneda
    change AlgebraicGeometry.Etale ((Sch).map snd)
    infer_instance)
  simpa using h

/-- **Proposition 5.1 (i)**, general `S`, with the added assumption that `X` is separated (the proof in
the paper does not check that the filling lies over `X`). `Q` is any face of
the finitely generated magnet `N`, `U` is an `S`-affine scheme and `U → X` is étale and equivariant
for `D(M)`, `M` an abelian group with `#M` below the cutoff of the site. -/
theorem isFaceCartesian_of_fg (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    (f : EquivariantHom aU aX) (hf : Space.IsEtale B S hS f.hom) (hQ : IsFace Q N) (hN : N.FG) :
    IsFaceCartesian f hQ :=
  faceComparison_bijective_of_affine ((isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf) f hQ
    (fun _ _ => faceComparison_bijective_affine f hsep (presheaf_etale_of_isEtale hf) hQ hN)

end Global

end AlgMag


open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry


namespace AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "Sch" => BigFppfOver.toScheme B S hS

attribute [local irreducible] spObj

attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

section Magnets

variable {M : Type u} [AddCommMonoid M] [Fact (Cardinal.mk M < B.cutoff)]
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {aX : AAction (fppfO B S hS) M X}

/-- `R[L] → R[N]` for `L ≤ N`. -/
noncomputable def inclR (T : BigFppfOver B S hS) {L N : AddSubmonoid M} (h : L ≤ N) :
    RH (AddMonoidAlgebra (RT T) L) (AddMonoidAlgebra (RT T) N) :=
  AddMonoidAlgebra.mapDomainRingHom _ (AddSubmonoid.inclusion h)

omit [Fact (Cardinal.mk M < B.cutoff)] in
lemma incl_injective (T : BigFppfOver B S hS) {L N : AddSubmonoid M} (h : L ≤ N) :
    Function.Injective (inclR T h) :=
  AddMonoidAlgebra.mapDomain_injective (AddSubmonoid.inclusion_injective h)

omit [Fact (Cardinal.mk M < B.cutoff)] in
lemma incl_ρN {T : BigFppfOver B S hS} {L N : AddSubmonoid M} (h : L ≤ N) :
    (inclR T h).comp (ρN T L) = ρN T N := by
  refine RingHom.ext fun r => ?_
  simp [inclR, ρN]

omit [Fact (Cardinal.mk M < B.cutoff)] in
lemma incl_mon {T : BigFppfOver B S hS} {L N : AddSubmonoid M} (h : L ≤ N) :
    (inclR T h).toMonoidHom.comp (monN _ L) =
      (monN _ N).comp (AddMonoidHom.toMultiplicative (AddSubmonoid.inclusion h)) := by
  refine MonoidHom.ext fun p => ?_
  simp [inclR, monN]

/-- `𝔸(N)_T` lies in the site, for all magnets `N`, when `#M` is below the cutoff. -/
lemma contains_any (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (N : AddSubmonoid M) : B.Contains (Spec (.of (AddMonoidAlgebra (RT T) N))) := by
  have hM : B.Contains (Spec (.of (AddMonoidAlgebra (RT T) M))) := contains_M (contains_RT T)
  refine Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hM ?_
  exact (Cardinal.mk_le_of_injective
    (AddMonoidAlgebra.mapDomain_injective (R := RT T) N.subtype_injective)).trans (le_max_right _ _)

/-- The value of a point of `X^N` at the universal point restricts to `X^L` along `L ≤ N`. -/
lemma ofLE_universal {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {act : AAction (fppfO B S hS) M F}
    {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    {L N : AddSubmonoid M} (h : L ≤ N) (φ : AttractorPt act L T) :
    (AttractorPt.ofLE h φ).app (spToT T (ρN T N) (contains_any T N)) (spPt (monN _ N)) =
      F.map (spMap T (hC := contains_any T L) (hC' := contains_any T N) (inclR T h) (incl_ρN h)).op
        (φ.app (spToT T (ρN T L) (contains_any T L)) (spPt (monN _ L))) := by
  rw [app_sp φ (inclR T h) (incl_ρN h) (monN _ L), incl_mon]
  rfl

/-- Restriction along an injective ring map is injective on points: `Spec R'' → Spec R'` is
schematically dominant, and the target is separated. -/
def HasDensePullback (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∀ (T : BigFppfOver B S hS) [IsAffine ((Sch).obj T)] {R' R'' : Type u} [CommRing R'] [CommRing R'']
    {ρ : RT T →+* R'} {ρ' : RT T →+* R''} {hC : B.Contains (Spec (.of R'))}
    {hC' : B.Contains (Spec (.of R''))} (π : R' →+* R'') (hπ : π.comp ρ = ρ'),
    Function.Injective π →
    Function.Injective (F.map (spMap T (hC := hC) (hC' := hC') π hπ).op)

lemma hasDensePullback_of_separated (hsep : IsSeparatedOver X) : HasDensePullback X := by
  intro T _ R' R'' _ _ ρ ρ' hC hC' π hπ hinj x y hxy
  refine eq_of_forall_restrict_eq hsep (ι := Unit)
    (fun _ => spMap T (hC := hC) (hC' := hC') π hπ) ?_ fun _ => hxy
  intro y' hy
  obtain ⟨z, hzy⟩ := (spSec_bijective T ρ hC).2 y'
  have h1 := hy ()
  have h2 := spMap_appTop T (hC := hC) (hC' := hC') π hπ z
  have h0 : spSec T ρ' hC' (π z) = 0 := by
    rw [← h2, hzy]
    exact h1
  have hz : z = 0 := hinj (by
    rw [map_zero]
    exact (spSec_bijective T ρ' hC').1 (h0.trans (map_zero _).symm))
  rw [← hzy, hz, map_zero]

lemma hasDensePullback_yoneda (U : BigFppfOver B S hS) [IsAffineHom U.hom.hom] :
    HasDensePullback (yoneda.obj U) := by
  intro T _ R' R'' _ _ ρ ρ' hC hC' π hπ hinj v v' hvv
  obtain ⟨ψ, hψ, rfl⟩ := exists_ptOf (T := T) (U := U) v
  obtain ⟨ψ', hψ', rfl⟩ := exists_ptOf (T := T) (U := U) v'
  have h : spMap T (hC := hC) (hC' := hC') π hπ ≫ ptOf ψ hψ =
      spMap T (hC := hC) (hC' := hC') π hπ ≫ ptOf ψ' hψ' := hvv
  rw [spMap_comp_ptOf, spMap_comp_ptOf] at h
  have e := ptOf_injective _ _ h
  have : ψ = ψ' := RingHom.ext fun a => hinj (congrArg (fun g : _ →+* _ => g a) e)
  subst this
  rfl

/-- **Proposition 3.29**, general form: if restriction along injective ring maps is injective on the
points of the sheaf `F`, then `F^L → F^N` is a monomorphism for `L ⊆ N`. -/
theorem ofLE_injective_of_dense {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {act : AAction (fppfO B S hS) M F} (hF : Presieve.IsSheaf (BigFppfOver.topology B S hS) F)
    (hd : HasDensePullback F) {L N : AddSubmonoid M} (h : L ≤ N) (T : BigFppfOver B S hS) :
    Function.Injective (AttractorPt.ofLE (act := act) (T := T) h) := by
  have shL := isSheaf_attractor act L _ hF
  intro φ ψ hφψ
  obtain ⟨I, V, π, hV, hS'⟩ := exists_affine_cover T
  refine (shL _ hS').isSeparatedFor.ext fun W g hg => ?_
  obtain ⟨_, a, b, ⟨i⟩, rfl⟩ := hg
  have main : AttractorPt.baseChange (π i) φ = AttractorPt.baseChange (π i) ψ := by
    have : IsAffine ((Sch).obj (V i)) := hV i
    set φ' := AttractorPt.baseChange (π i) φ with hφ'
    set ψ' := AttractorPt.baseChange (π i) ψ with hψ'
    have hφψ' : AttractorPt.ofLE h φ' = AttractorPt.ofLE h ψ' :=
      congrArg (AttractorPt.baseChange (π i)) hφψ
    let Uni := spUniversal (V i) L (contains_any (V i) L)
    suffices key : φ'.app Uni.π Uni.u = ψ'.app Uni.π Uni.u by
      refine AttractorPt.ext ?_
      funext T' t a'
      rw [φ'.app_eq_of_universal Uni, ψ'.app_eq_of_universal Uni, key]
    refine hd (V i) (hC := contains_any (V i) L) (hC' := contains_any (V i) N) (inclR (V i) h)
      (incl_ρN h) (incl_injective _ h) ?_
    refine (ofLE_universal h φ').symm.trans (Eq.trans ?_ (ofLE_universal h ψ'))
    rw [hφψ']
  exact congrArg (AttractorPt.baseChange a) main

/-- **Proposition 3.29**: if `X` is a separated algebraic space and
`L ⊆ N`, then `X^L → X^N` is a monomorphism. -/
theorem ofLE_injective (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    {L N : AddSubmonoid M} (h : L ≤ N) (T : BigFppfOver B S hS) :
    Function.Injective (AttractorPt.ofLE (act := aX) (T := T) h) :=
  ofLE_injective_of_dense ((isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf)
    (hasDensePullback_of_separated hsep) h T

/-- **Corollary 3.30**: if `X` is separated, `X^N → X` is a monomorphism. -/
theorem attractor_toPoint_injective_sep (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    (N : AddSubmonoid M) (T : BigFppfOver B S hS) :
    Function.Injective (AttractorPt.toPoint (act := aX) (N := N) (T := T)) := by
  intro φ ψ h
  apply ofLE_injective hX hsep (le_top : N ≤ ⊤) T
  exact (attractorTopEquiv aX T).injective h

/-! ### Equivariance from the universal point; Proposition 3.37 -/

section Key

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {act : AAction (fppfO B S hS) M F}
variable {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]

/-- The equivariance of a point on `𝔸(L)_T`, on the universal points of `𝔸(L)` and of `D(M)`. -/
def IsKey (L : AddSubmonoid M) (x₀ : F.obj (op (spObj T (ρN T L) (contains_any T L)))) : Prop :=
  F.map (spMap T (hC := contains_any T L) (hC' := contains_M (contains_any T L))
    (cN T L) cN_ρN).op x₀ =
  act.smul (spPt (eM _ M)) (F.map (spMap T (hC := contains_any T L)
    (hC' := contains_M (contains_any T L)) (jr _ M) rfl).op x₀)

/-- A point of `F` on `𝔸(L)_T` which is equivariant for the universal point of `D(M)` is a point of
`F^L`. -/
theorem exists_attractorPt_of_key (L : AddSubmonoid M)
    (x₀ : F.obj (op (spObj T (ρN T L) (contains_any T L)))) (hk : IsKey (act := act) L x₀) :
    ∃ φ : AttractorPt act L T,
      φ.app (spToT T (ρN T L) (contains_any T L)) (spPt (monN _ L)) = x₀ := by
  have hCN := contains_any T L
  have hCNM := contains_M (M := M) hCN
  let Uni := spUniversal T L hCN
  have hequiv : ∀ {T' : BigFppfOver B S hS} (t : T' ⟶ T) (h : APt (fppfO B S hS) M (op T'))
      (a : APt (fppfO B S hS) L (op T')),
      F.map (Uni.lift t (APt.toMagnet L h * a)).op x₀ = act.smul h (F.map (Uni.lift t a).op x₀) := by
    intro T' t h a
    let r : T' ⟶ spObj T ((jr _ M).comp (ρN T L)) hCNM :=
      spLift T _ hCNM t (pairRing t h a) (pairRing_comp t h a)
    have hrπ : r ≫ spToT T _ hCNM = t := spLift_toT T _ hCNM t _ _
    have hra : ∀ x', ((Sch).map r).appTop.hom (spSec T _ hCNM x') = pairRing t h a x' :=
      fun x' => spLift_appTop T _ hCNM t _ _ x'
    have l₁ : r ≫ spMap T (hC := hCN) (hC' := hCNM) (jr _ M) rfl = spUniLift T L hCN t a := by
      refine Uni.uniq t a _ ?_ ?_
      · change (r ≫ spMap T _ rfl) ≫ spToT T (ρN T L) hCN = t
        rw [Category.assoc, spMap_toT, hrπ]
      · change APt.res (r ≫ spMap T _ rfl).op (spPt (monN _ L)) = a
        rw [op_comp, APt.res_comp, spPt_res]
        refine MonoidHom.ext fun n => ?_
        rw [res_spPt_apply, hra]
        change pairRing t h a (AddMonoidAlgebra.single 0 (monN _ L n)) = _
        rw [pairRing_single, ofAdd_zero, map_one, mul_one]
        change pointRing t a (AddMonoidAlgebra.single _ 1) = _
        rw [pointRing_single, map_one, one_mul]
        rfl
    have l₂ : r ≫ spMap T (hC := hCN) (hC' := hCNM) (cN T L) cN_ρN =
        spUniLift T L hCN t (APt.toMagnet L h * a) := by
      refine Uni.uniq t _ _ ?_ ?_
      · change (r ≫ spMap T _ _) ≫ spToT T (ρN T L) hCN = t
        rw [Category.assoc, spMap_toT, hrπ]
      · change APt.res (r ≫ spMap T _ _).op (spPt (monN _ L)) = _
        rw [op_comp, APt.res_comp, spPt_res]
        refine MonoidHom.ext fun n => ?_
        rw [res_spPt_apply, hra]
        have : (cN T L).toMonoidHom.comp (monN _ L) n = AddMonoidAlgebra.single
            ((Multiplicative.toAdd n : L) : M) (monN _ L n) := monN_faceCoact _ n
        rw [this, pairRing_single]
        change pointRing t a (AddMonoidAlgebra.single _ 1) * _ = _
        rw [pointRing_single, map_one, one_mul, mul_comm]
        rfl
    have hres : APt.res r.op (spPt (T := T) (ρ := (jr _ M).comp (ρN T L)) (hC := hCNM) (eM _ M)) = h := by
      refine MonoidHom.ext fun m => ?_
      rw [res_spPt_apply, hra]
      change pairRing t h a (AddMonoidAlgebra.single _ 1) = _
      rw [pairRing_single, map_one, one_mul]
      rfl
    have hsm := act.map_smul r.op (spPt (eM _ M))
      (F.map (spMap T (hC := hCN) (hC' := hCNM) (jr _ M) rfl).op x₀)
    rw [hres] at hsm
    change F.map (spUniLift T L hCN t (APt.toMagnet L h * a)).op x₀ =
      act.smul h (F.map (spUniLift T L hCN t a).op x₀)
    rw [← l₁, ← l₂, op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply]
    have hkk : F.map (spMap T (hC := hCN) (hC' := hCNM) (cN T L) cN_ρN).op x₀ = _ := hk
    rw [hkk]
    exact hsm
  refine ⟨(attractorPtEquivOfUniversal Uni).symm ⟨x₀, hequiv⟩, ?_⟩
  change F.map (Uni.lift Uni.π Uni.u).op x₀ = x₀
  rw [Uni.lift_self]
  simp
  rfl

/-- Conversely, the value of a point of `F^L` at the universal point is equivariant. -/
theorem isKey_app (L : AddSubmonoid M) (φ : AttractorPt act L T) :
    IsKey (act := act) L (φ.app (spToT T (ρN T L) (contains_any T L)) (spPt (monN _ L))) := by
  unfold IsKey
  rw [app_sp φ (cN T L) cN_ρN (monN _ L), app_sp φ (jr _ M) rfl (monN _ L)]
  exact app_coact (ρ := ρN T L) φ (contains_any T L) (monN _ L) (cN T L)
    (fun p => monN_faceCoact _ p)

lemma mapR_injective {A C : Type u} [CommRing A] [CommRing C] (π : A →+* C)
    (h : Function.Injective π) : Function.Injective (mapR π M) := by
  intro x y e
  refine AddMonoidAlgebra.coeff_injective (Finsupp.ext fun m => h ?_)
  have := congrArg (fun z => z.coeff m) e
  simpa [mapR] using this

lemma mapR_incl_cN {L N : AddSubmonoid M} (h : L ≤ N) :
    (mapR (inclR T h) M).comp (cN T L) = (cN T N).comp (inclR T h) := by
  refine RingHom.ext fun x => ?_
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single n r =>
    change mapR (inclR T h) M (faceCoact _ L (AddMonoidAlgebra.single n r)) =
      faceCoact _ N (inclR T h (AddMonoidAlgebra.single n r))
    have e : inclR T h (AddMonoidAlgebra.single n r) =
        AddMonoidAlgebra.single (AddSubmonoid.inclusion h n) r := by simp [inclR]
    rw [e, faceCoact_single, faceCoact_single]
    refine (AddMonoidAlgebra.mapRingHom_single _ _ _).trans ?_
    rw [e]
    rfl

/-- If the image of a point of `𝔸(L)` in `𝔸(N)` is equivariant, so is the point, when restriction
along injective ring maps is injective on `F`. -/
theorem isKey_descend (hd : HasDensePullback F) {L N : AddSubmonoid M} (h : L ≤ N)
    (x₀ : F.obj (op (spObj T (ρN T L) (contains_any T L))))
    (hk : IsKey (act := act) N (F.map (spMap T (hC := contains_any T L) (hC' := contains_any T N)
      (inclR T h) (incl_ρN h)).op x₀)) :
    IsKey (act := act) L x₀ := by
  have hCL := contains_any T L
  have hCN := contains_any T N
  have hCLM := contains_M (M := M) hCL
  have hCNM := contains_M (M := M) hCN
  have hM : (mapR (inclR T h) M).comp ((jr _ M).comp (ρN T L)) = (jr _ M).comp (ρN T N) := by
    rw [← RingHom.comp_assoc, mapR_jr, RingHom.comp_assoc, incl_ρN]
  let S₀ := spMap T (hC := hCLM) (hC' := hCNM) (mapR (inclR T h) M) hM
  refine hd T (hC := hCLM) (hC' := hCNM) (mapR (inclR T h) M) hM (mapR_injective _ (incl_injective _ h)) ?_
  have hsm := act.map_smul S₀.op (spPt (eM _ M))
    (F.map (spMap T (hC := hCL) (hC' := hCLM) (jr _ M) rfl).op x₀)
  refine Eq.trans ?_ hsm.symm
  rw [spPt_res, mapR_eM]
  have hk' := hk
  unfold IsKey at hk'
  have comm : ∀ (π₁ : _ →+* _) (h₁) (π₂ : _ →+* _) (h₂) (e : (mapR (inclR T h) M).comp π₁ = π₂.comp (inclR T h)),
      F.map S₀.op (F.map (spMap T (hC := hCL) (hC' := hCLM) π₁ h₁).op x₀) =
        F.map (spMap T (hC := hCN) (hC' := hCNM) π₂ h₂).op
          (F.map (spMap T (hC := hCL) (hC' := hCN) (inclR T h) (incl_ρN h)).op x₀) := by
    intro π₁ h₁ π₂ h₂ e
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, spMap_comp T, spMap_comp T]
    congr 3
    exact congrArg Quiver.Hom.op (spMap_congr (T := T) _ _ e)
  rw [comm (cN T L) cN_ρN (cN T N) cN_ρN (mapR_incl_cN h),
    comm (jr _ M) rfl (jr _ M) rfl (mapR_jr _)]
  exact hk'

end Key

/-- The form of "`X` locally of finite presentation" used in **Proposition 3.37**: `X` commutes with
filtered unions of rings (Tag 049J gives this for an algebraic space locally of finite presentation
over `S`; that implication is not formalized). Only the surjectivity is required, since the injectivity
holds for separated `X`. -/
def IsLimitPreserving (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∀ (T : BigFppfOver B S hS) [IsAffine ((Sch).obj T)] {R' : Type u} [CommRing R'] {ρ : RT T →+* R'}
    {hC : B.Contains (Spec (.of R'))} {ι : Type u} (Ri : ι → Type u) [∀ i, CommRing (Ri i)]
    (ρi : ∀ i, RT T →+* Ri i) (hCi : ∀ i, B.Contains (Spec (.of (Ri i))))
    (gi : ∀ i, Ri i →+* R') (hg : ∀ i, (gi i).comp (ρi i) = ρ),
    (∀ i, Function.Injective (gi i)) →
    (∀ s : Finset R', ∃ i, ∀ x ∈ s, x ∈ (gi i).range) →
    ∀ x : X.obj (op (spObj T ρ hC)), ∃ (i : ι) (xi : X.obj (op (spObj T (ρi i) (hCi i)))),
      X.map (spMap T (hC := hCi i) (hC' := hC) (gi i) (hg i)).op xi = x

omit [Fact (Cardinal.mk M < B.cutoff)] in
lemma mem_range_incl {T : BigFppfOver B S hS} {L N : AddSubmonoid M} (h : L ≤ N)
    (x : AddMonoidAlgebra (RT T) N) (hx : ∀ n : N, x.coeff n ≠ 0 → (n : M) ∈ L) :
    x ∈ (inclR T h).range := by
  rw [eq_sum_single x]
  refine Subring.sum_mem _ fun n hn => ?_
  refine ⟨AddMonoidAlgebra.single ⟨n, hx n (Finsupp.mem_support_iff.1 hn)⟩ (x.coeff n), ?_⟩
  simp [inclR]
  rfl

/-- Finitely many elements of `R[N]` lie in `R[P]` for `P` finitely generated, containing a given
finitely generated `P₀ ≤ N`. -/
lemma exists_fg_range {T : BigFppfOver B S hS} {P₀ N : AddSubmonoid M} (h₀ : P₀ ≤ N) (hP₀ : P₀.FG)
    (s : Finset (AddMonoidAlgebra (RT T) N)) :
    ∃ P : AddSubmonoid M, ∃ (hP : P ≤ N), P₀ ≤ P ∧ P.FG ∧ ∀ x ∈ s, x ∈ (inclR T hP).range := by
  classical
  let G : Finset M := (s.biUnion fun x => x.coeff.support).image (fun n : N => (n : M))
  let P : AddSubmonoid M := P₀ ⊔ AddSubmonoid.closure (G : Set M)
  have hG : ∀ g ∈ G, g ∈ N := by
    intro g hg
    obtain ⟨n, -, rfl⟩ := Finset.mem_image.1 hg
    exact n.2
  have hP : P ≤ N := sup_le h₀ ((AddSubmonoid.closure_le).2 hG)
  refine ⟨P, hP, le_sup_left, hP₀.sup ⟨G, rfl⟩, fun x hx => mem_range_incl hP x fun n hn => ?_⟩
  refine (le_sup_right : _ ≤ P) (AddSubmonoid.subset_closure ?_)
  exact Finset.mem_image.2 ⟨n, Finset.mem_biUnion.2 ⟨x, hx, Finsupp.mem_support_iff.2 hn⟩, rfl⟩

/-- **Proposition 3.37**, for `T` affine: if `X` is separated and limit
preserving, a point of `X^N(T)` comes from `X^P(T)` for some finitely generated `P ≤ N` (and from a
unique one, by `ofLE_injective`). The statement in the paper for arbitrary `T` is false when `T` is not
quasi-compact. -/
theorem exists_ofLE_eq (hsep : IsSeparatedOver X) (hlim : IsLimitPreserving X) {N P₀ : AddSubmonoid M}
    (h₀ : P₀ ≤ N) (hP₀ : P₀.FG) {T : BigFppfOver B S hS} [IsAffine ((Sch).obj T)]
    (φ : AttractorPt aX N T) :
    ∃ (P : AddSubmonoid M) (hP : P ≤ N) (φ' : AttractorPt aX P T), P₀ ≤ P ∧ P.FG ∧
      AttractorPt.ofLE hP φ' = φ := by
  let ι := {P : AddSubmonoid M // P ≤ N ∧ P₀ ≤ P ∧ P.FG}
  obtain ⟨⟨P, hP, hP₁, hPf⟩, x', hx'⟩ := hlim T (ρ := ρN T N) (hC := contains_any T N) (ι := ι)
    (fun i => AddMonoidAlgebra (RT T) i.1) (fun i => ρN T i.1) (fun i => contains_any T i.1)
    (fun i => inclR T i.2.1) (fun i => incl_ρN i.2.1) (fun i => incl_injective T i.2.1)
    (fun s => by
      obtain ⟨P, hP, h₁, hf, h⟩ := exists_fg_range h₀ hP₀ s
      exact ⟨⟨P, hP, h₁, hf⟩, h⟩)
    (φ.app (spToT T (ρN T N) (contains_any T N)) (spPt (monN _ N)))
  have hk : IsKey (act := aX) P x' := isKey_descend (hasDensePullback_of_separated hsep) hP x' (by
    change IsKey N (X.map (spMap T (inclR T hP) (incl_ρN hP)).op x')
    have e : X.map (spMap T (hC := contains_any T P) (hC' := contains_any T N) (inclR T hP)
      (incl_ρN hP)).op x' = _ := hx'
    rw [e]
    exact isKey_app N φ)
  obtain ⟨φ', hφ'⟩ := exists_attractorPt_of_key P x' hk
  refine ⟨P, hP, φ', hP₁, hPf, ?_⟩
  let Uni := spUniversal T N (contains_any T N)
  have key : (AttractorPt.ofLE hP φ').app Uni.π Uni.u = φ.app Uni.π Uni.u := by
    refine (ofLE_universal hP φ').trans ?_
    rw [hφ']
    exact hx'
  refine AttractorPt.ext ?_
  funext T' t a'
  rw [AttractorPt.app_eq_of_universal Uni, φ.app_eq_of_universal Uni, key]

end Magnets

end AlgMag


open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry


namespace AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "Sch" => BigFppfOver.toScheme B S hS

attribute [local irreducible] spObj

attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

section Descent

variable {M : Type u} [AddCommGroup M] [Fact (Cardinal.mk M < B.cutoff)]
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {aX : AAction (fppfO B S hS) M X}
variable {U : BigFppfOver B S hS} [IsAffineHom U.hom.hom] {aU : AAction (fppfO B S hS) M (yoneda.obj U)}
variable {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]

/-- Global functions on `Spec R'` as a morphism in `CommRingCat`. -/
noncomputable def spSecHom {R' : Type u} [CommRing R'] (ρ : RT T →+* R')
    (hC : B.Contains (Spec (.of R'))) : CommRingCat.of R' ⟶ Γ((Sch).obj (spObj T ρ hC), ⊤) :=
  CommRingCat.ofHom (spSec T ρ hC)

unseal spObj in
/-- Descent of a section of an étale `E → Spec R₁` along a filtered union: the part of the proof of
**Proposition 5.1 (ii)** which shows that `U`, being étale over `X`, is limit preserving relative to
`X`. Since `Γ(E)` is of finite type over `R₁`, its image in `R'` lies in one of the subrings. -/
theorem etale_descend {f : yoneda.obj U ⟶ X} (hsep : IsSeparatedOver X)
    (hf : (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f)
    {R₁ R' : Type u} [CommRing R₁] [CommRing R'] {ρ₁ : RT T →+* R₁} {ρ : RT T →+* R'}
    {hC₁ : B.Contains (Spec (.of R₁))} {hC : B.Contains (Spec (.of R'))}
    (τ : X.obj (op (spObj T ρ₁ hC₁))) (g : R₁ →+* R') (hg : g.comp ρ₁ = ρ)
    (v : spObj T ρ hC ⟶ U)
    (hv : f.app (op (spObj T ρ hC)) v = X.map (spMap T (hC := hC₁) (hC' := hC) g hg).op τ)
    {ι : Type*} (Ri : ι → Type u) [∀ i, CommRing (Ri i)]
    (ρi : ∀ i, RT T →+* Ri i) (hCi : ∀ i, B.Contains (Spec (.of (Ri i))))
    (gi : ∀ i, Ri i →+* R') (hgi : ∀ i, (gi i).comp (ρi i) = ρ) (hi : ∀ i, R₁ →+* Ri i)
    (hiρ : ∀ i, (hi i).comp ρ₁ = ρi i) (hc : ∀ i, (gi i).comp (hi i) = g)
    (hinj : ∀ i, Function.Injective (gi i))
    (hcov : ∀ s : Finset R', ∃ i, ∀ x ∈ s, x ∈ (gi i).range) :
    ∃ (i : ι) (w : spObj T (ρi i) (hCi i) ⟶ U),
      spMap T (hC := hCi i) (hC' := hC) (gi i) (hgi i) ≫ w = v ∧
      f.app (op _) w = X.map (spMap T (hC := hC₁) (hC' := hCi i) (hi i) (hiρ i)).op τ := by
  classical
  let Z' := spObj T ρ₁ hC₁
  obtain ⟨E, e₁, e₂, hEa, hring, h₀, huniq, hex⟩ := exists_etale_chart hsep hf τ
  have hfnat : ∀ {V V' : BigFppfOver B S hS} (r : V' ⟶ V) (v : V ⟶ U),
      f.app (op V') (r ≫ v) = X.map r.op (f.app (op V) v) := fun r v =>
    hom_naturality_apply f r.op v
  obtain ⟨l, hl₁, hl₂⟩ := hex (spMap T (hC := hC₁) (hC' := hC) g hg) v hv
  -- the ring map `Γ(E) → R'`
  let e' := RingEquiv.ofBijective (spSec T ρ hC) (spSec_bijective T ρ hC)
  let ψ : Γ((Sch).obj E, ⊤) →+* R' := e'.symm.toRingHom.comp ((Sch).map l).appTop.hom
  have hψ : ∀ y, spSec T ρ hC (ψ y) = ((Sch).map l).appTop.hom y := fun y => e'.apply_symm_apply _
  have hψα : ∀ r, ψ (((Sch).map e₁).appTop.hom (spSec T ρ₁ hC₁ r)) = g r := by
    intro r
    apply (spSec_bijective T ρ hC).1
    rw [hψ, ← spMap_appTop T (hC := hC₁) (hC' := hC) g hg r, ← hl₁, Functor.map_comp,
      Scheme.Hom.comp_appTop]
    rfl
  -- finite generation
  obtain ⟨s', hs'⟩ : ∃ s' : Finset Γ((Sch).obj E, ⊤), ∀ y, ψ y ∈ Subring.closure
      ((ψ '' (s' : Set _)) ∪ Set.range g) := by
    have := hring
    algebraize [((Sch).map e₁).appTop.hom]
    obtain ⟨s', hs'⟩ := (inferInstance : Algebra.FiniteType Γ((Sch).obj Z', ⊤) Γ((Sch).obj E, ⊤)).out
    refine ⟨s', fun y => ?_⟩
    have hy : y ∈ Algebra.adjoin Γ((Sch).obj Z', ⊤) (s' : Set Γ((Sch).obj E, ⊤)) := by
      rw [hs']; trivial
    induction hy using Algebra.adjoin_induction with
    | mem y hy => exact Subring.subset_closure (Or.inl ⟨y, hy, rfl⟩)
    | algebraMap r =>
      obtain ⟨r', rfl⟩ := (spSec_bijective T ρ₁ hC₁).2 r
      refine Subring.subset_closure (Or.inr ⟨r', ?_⟩)
      exact (hψα r').symm
    | add x y _ _ hx hy => rw [map_add]; exact Subring.add_mem _ hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact Subring.mul_mem _ hx hy
  obtain ⟨i, hi'⟩ := hcov (s'.image ψ)
  have hrange : ∀ y, ψ y ∈ (gi i).range := by
    intro y
    refine (Subring.closure_le.2 ?_) (hs' y)
    rintro _ (⟨y', hy', rfl⟩ | ⟨r, rfl⟩)
    · exact hi' _ (Finset.mem_image_of_mem _ hy')
    · exact ⟨hi i r, congrArg (fun k : _ →+* _ => k r) (hc i)⟩
  let eᵢ := RingEquiv.ofBijective (gi i).rangeRestrict
    ⟨fun a b e => hinj i (congrArg Subtype.val e), (gi i).rangeRestrict_surjective⟩
  let ψᵢ : Γ((Sch).obj E, ⊤) →+* Ri i := eᵢ.symm.toRingHom.comp (ψ.codRestrict (gi i).range hrange)
  have hψᵢ : ∀ y, gi i (ψᵢ y) = ψ y := fun y =>
    congrArg Subtype.val (eᵢ.apply_symm_apply (ψ.codRestrict (gi i).range hrange y))
  let L : (Sch).obj (spObj T (ρi i) (hCi i)) ⟶ (Sch).obj E :=
    homOfGlobal (CommRingCat.ofHom ψᵢ ≫ spSecHom (ρi i) (hCi i))
  have hL : ∀ y, L.appTop.hom y = spSec T (ρi i) (hCi i) (ψᵢ y) := fun y =>
    congrArg (fun k => k.hom y) (homOfGlobal_appTop (CommRingCat.ofHom ψᵢ ≫ spSecHom (ρi i) (hCi i)))
  have hL₁ : L ≫ (Sch).map e₁ = (Sch).map (spMap T (hC := hC₁) (hC' := hCi i) (hi i) (hiρ i)) := by
    refine ext_of_isAffine ?_
    ext x
    obtain ⟨r, rfl⟩ := (spSec_bijective T ρ₁ hC₁).2 x
    refine Eq.trans ?_ (spMap_appTop T (hi i) (hiρ i) r).symm
    rw [Scheme.Hom.comp_appTop]
    change L.appTop.hom (((Sch).map e₁).appTop.hom (spSec T ρ₁ hC₁ r)) = _
    rw [hL]
    refine congrArg _ (hinj i ?_)
    rw [hψᵢ, hψα]
    exact (congrArg (fun k : _ →+* _ => k r) (hc i)).symm
  let li : spObj T (ρi i) (hCi i) ⟶ E := siteHom L (by
    rw [← site_w e₁, ← Category.assoc, hL₁, site_w])
  have hli₁ : li ≫ e₁ = spMap T (hC := hC₁) (hC' := hCi i) (hi i) (hiρ i) := site_hom_ext (by
    rw [Functor.map_comp, siteHom_map, hL₁])
  have hli₂ : spMap T (hC := hCi i) (hC' := hC) (gi i) (hgi i) ≫ li = l := by
    refine site_hom_ext (ext_of_isAffine ?_)
    ext y
    rw [Functor.map_comp, Scheme.Hom.comp_appTop]
    exact (congrArg (((Sch).map (spMap T (hC := hCi i) (hC' := hC) (gi i) (hgi i))).appTop.hom) (hL y)).trans
      ((spMap_appTop T (gi i) (hgi i) _).trans ((congrArg _ (hψᵢ y)).trans (hψ y)))
  refine ⟨i, li ≫ e₂, ?_, ?_⟩
  · rw [← Category.assoc, hli₂, hl₂]
  · refine (hfnat li e₂).trans ?_
    rw [h₀, ← Functor.map_comp_apply, ← op_comp, hli₁]

end Descent

section PartII

variable {M : Type u} [AddCommMonoid M] [Fact (Cardinal.mk M < B.cutoff)]
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {aX : AAction (fppfO B S hS) M X}
variable {U : BigFppfOver B S hS} [IsAffineHom U.hom.hom] {aU : AAction (fppfO B S hS) M (yoneda.obj U)}

omit [Fact (Cardinal.mk M < B.cutoff)] in
lemma isFace_inf {Q N P : AddSubmonoid M} (hQ : IsFace Q N) (hP : P ≤ N) : IsFace (Q ⊓ P) P :=
  ⟨inf_le_right, fun {_ _} hx hy h =>
    have h' := hQ.mem_of_add_mem (hP hx) (hP hy) h.1
    ⟨⟨h'.1, hx⟩, ⟨h'.2, hy⟩⟩⟩

omit [Fact (Cardinal.mk M < B.cutoff)] in
/-- Faces and inclusions of magnets commute. -/
lemma ofFace_ofLE {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {act : AAction (fppfO B S hS) M F}
    {Q N P : AddSubmonoid M} (hQ : IsFace Q N) (hP : P ≤ N) {T : BigFppfOver B S hS}
    (φ : AttractorPt act P T) :
    AttractorPt.ofFace hQ (AttractorPt.ofLE hP φ) =
      AttractorPt.ofLE (inf_le_left : Q ⊓ P ≤ Q) (AttractorPt.ofFace (isFace_inf hQ hP) φ) := by
  refine AttractorPt.ext ?_
  funext T' t a
  change φ.app t (APt.restrict hP (APt.faceExt hQ a)) =
    φ.app t (APt.faceExt (isFace_inf hQ hP) (APt.restrict inf_le_left a))
  congr 1
  refine MonoidHom.ext fun n => ?_
  by_cases h : ((Multiplicative.toAdd n : P) : M) ∈ Q
  · have h' : ((Multiplicative.toAdd n : P) : M) ∈ Q ⊓ P := ⟨h, (Multiplicative.toAdd n).2⟩
    rw [APt.faceExt_pos (isFace_inf hQ hP) _ h']
    exact APt.faceExt_pos hQ a (n := AddMonoidHom.toMultiplicative (AddSubmonoid.inclusion hP) n) h
  · have h' : ((Multiplicative.toAdd n : P) : M) ∉ Q ⊓ P := fun e => h e.1
    rw [APt.faceExt_neg (isFace_inf hQ hP) _ h']
    exact APt.faceExt_neg hQ a (n := AddMonoidHom.toMultiplicative (AddSubmonoid.inclusion hP) n) h

omit [Fact (Cardinal.mk M < B.cutoff)] in
lemma push_ofLE (f : EquivariantHom aU aX) {L N : AddSubmonoid M} (h : L ≤ N)
    {T : BigFppfOver B S hS} (φ : AttractorPt aU L T) :
    AttractorPt.push f (AttractorPt.ofLE h φ) = AttractorPt.ofLE h (AttractorPt.push f φ) := rfl

omit [Fact (Cardinal.mk M < B.cutoff)] in
lemma ofLE_ofLE {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {act : AAction (fppfO B S hS) M F}
    {K L N : AddSubmonoid M} (h₁ : K ≤ L) (h₂ : L ≤ N) {T : BigFppfOver B S hS}
    (φ : AttractorPt act K T) :
    AttractorPt.ofLE h₂ (AttractorPt.ofLE h₁ φ) = AttractorPt.ofLE (h₁.trans h₂) φ := rfl

omit [Fact (Cardinal.mk M < B.cutoff)] in
lemma incl_comp {T : BigFppfOver B S hS} {K L N : AddSubmonoid M} (h₁ : K ≤ L) (h₂ : L ≤ N) :
    (inclR T h₂).comp (inclR T h₁) = inclR T (h₁.trans h₂) := by
  refine RingHom.ext fun x => ?_
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single n r =>
    simp [inclR]
    rfl

omit [Fact (Cardinal.mk M < B.cutoff)] in
/-- A face of a finitely generated monoid is finitely generated. -/
lemma IsFace.fg {Q P : AddSubmonoid M} (hQ : IsFace Q P) (hP : P.FG) : Q.FG := by
  classical
  obtain ⟨G, rfl⟩ := hP
  refine ⟨G.filter (· ∈ Q), le_antisymm ((AddSubmonoid.closure_le).2 fun x hx => ?_) fun x hx => ?_⟩
  · exact (Finset.mem_filter.1 hx).2
  · have hxP := hQ.le hx
    revert hx
    induction hxP using AddSubmonoid.closure_induction with
    | mem x hx =>
      intro h
      exact AddSubmonoid.subset_closure (Finset.mem_filter.2 ⟨hx, h⟩)
    | zero => exact fun _ => AddSubmonoid.zero_mem _
    | add x y hx hy ihx ihy =>
      intro h
      have := hQ.mem_of_add_mem hx hy h
      exact AddSubmonoid.add_mem _ (ihx this.1) (ihy this.2)

/-- A point of `F^N` whose value at the universal point comes from `R[P]` comes from `F^P`. -/
theorem exists_ofLE_of_pull {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {act : AAction (fppfO B S hS) M F}
    (hd : HasDensePullback F) {P N : AddSubmonoid M} (hP : P ≤ N)
    {T : BigFppfOver B S hS} [IsAffine ((Sch).obj T)] (φ : AttractorPt act N T)
    (x' : F.obj (op (spObj T (ρN T P) (contains_any T P))))
    (hx' : F.map (spMap T (hC := contains_any T P) (hC' := contains_any T N) (inclR T hP)
      (incl_ρN hP)).op x' = φ.app (spToT T (ρN T N) (contains_any T N)) (spPt (monN _ N))) :
    ∃ φ' : AttractorPt act P T, AttractorPt.ofLE hP φ' = φ := by
  have hk : IsKey (act := act) P x' := isKey_descend hd hP x' (by rw [hx']; exact isKey_app N φ)
  obtain ⟨φ', hφ'⟩ := exists_attractorPt_of_key P x' hk
  refine ⟨φ', ?_⟩
  let Uni := spUniversal T N (contains_any T N)
  have key : (AttractorPt.ofLE hP φ').app Uni.π Uni.u = φ.app Uni.π Uni.u := by
    refine (ofLE_universal hP φ').trans ?_
    rw [hφ']
    exact hx'
  refine AttractorPt.ext ?_
  funext T' t a'
  rw [AttractorPt.app_eq_of_universal Uni, φ.app_eq_of_universal Uni, key]

end PartII

section PartIIGroup

variable {M : Type u} [AddCommGroup M] [Fact (Cardinal.mk M < B.cutoff)]
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {aX : AAction (fppfO B S hS) M X}
variable {U : BigFppfOver B S hS} [IsAffineHom U.hom.hom] {aU : AAction (fppfO B S hS) M (yoneda.obj U)}

/-- Descent of a point of `U^N`: given `x' ∈ X^{P₀}` with image `f(u)`, the point `u` comes from a
finitely generated `P ≥ P₀`. Part of the proof of **Proposition 5.1 (ii)**. -/
theorem exists_descend_U (hsep : IsSeparatedOver X)
    (f : EquivariantHom aU aX) (hf : Space.IsEtale B S hS f.hom) {N P₀ : AddSubmonoid M}
    (h₀ : P₀ ≤ N) (hP₀ : P₀.FG) {T : BigFppfOver B S hS} [IsAffine ((Sch).obj T)]
    (u : AttractorPt aU N T) (x' : AttractorPt aX P₀ T)
    (hu : AttractorPt.push f u = AttractorPt.ofLE h₀ x') :
    ∃ (P : AddSubmonoid M) (hP : P ≤ N) (_ : P₀ ≤ P) (u' : AttractorPt aU P T), P.FG ∧
      AttractorPt.ofLE hP u' = u := by
  have hhf := presheaf_etale_of_isEtale hf
  let ι := {P : AddSubmonoid M // P ≤ N ∧ P₀ ≤ P ∧ P.FG}
  have hv : f.hom.app (op (spObj T (ρN T N) (contains_any T N)))
      (u.app (spToT T (ρN T N) (contains_any T N)) (spPt (monN _ N))) =
      X.map (spMap T (hC := contains_any T P₀) (hC' := contains_any T N) (inclR T h₀) (incl_ρN h₀)).op
        (x'.app (spToT T (ρN T P₀) (contains_any T P₀)) (spPt (monN _ P₀))) := by
    refine Eq.trans ?_ (ofLE_universal h₀ x')
    rw [← hu]
    rfl
  obtain ⟨⟨P, hP, hP₁, hPf⟩, w, hw, -⟩ := etale_descend hsep hhf (ρ₁ := ρN T P₀) (hC₁ := contains_any T P₀)
    (ρ := ρN T N) (hC := contains_any T N)
    (x'.app (spToT T (ρN T P₀) (contains_any T P₀)) (spPt (monN _ P₀)))
    (inclR T h₀) (incl_ρN h₀) _ hv (ι := ι)
    (fun i => AddMonoidAlgebra (RT T) i.1) (fun i => ρN T i.1) (fun i => contains_any T i.1)
    (fun i => inclR T i.2.1) (fun i => incl_ρN i.2.1) (fun i => inclR T i.2.2.1)
    (fun i => incl_ρN i.2.2.1)
    (fun i => incl_comp _ _)
    (fun i => incl_injective T i.2.1)
    (fun s => by
      obtain ⟨P, hP, h₁, hf, h⟩ := exists_fg_range h₀ hP₀ s
      exact ⟨⟨P, hP, h₁, hf⟩, h⟩)
  obtain ⟨u', hu'⟩ := exists_ofLE_of_pull (hasDensePullback_yoneda U) hP u w hw
  exact ⟨P, hP, hP₁, u', hPf, hu'⟩

include aU in
/-- **Proposition 5.1 (ii)**, for `T` affine. -/
theorem faceComparison_bijective_of_separated_affine (hX : IsAlgebraicSpace B S hS X)
    (hsep : IsSeparatedOver X) (hlim : IsLimitPreserving X) (f : EquivariantHom aU aX)
    (hf : Space.IsEtale B S hS f.hom) {Q N : AddSubmonoid M} (hQ : IsFace Q N)
    (T : BigFppfOver B S hS) [IsAffine ((Sch).obj T)] :
    Function.Bijective (faceComparison f hQ T) := by
  have hUs : Presieve.IsSheaf (BigFppfOver.topology B S hS) (yoneda.obj U) :=
    BigFppfOver.isSheaf_of_type_yoneda_obj U
  have hbot : (⊥ : AddSubmonoid M).FG := ⟨∅, by simp⟩
  constructor
  · intro u₁ u₂ h
    have h1 : AttractorPt.push f u₁ = AttractorPt.push f u₂ := congrArg (fun p => p.1.1) h
    have h2 : AttractorPt.ofFace hQ u₁ = AttractorPt.ofFace hQ u₂ := congrArg (fun p => p.1.2) h
    obtain ⟨P₀, hP₀, x₀, -, hf₀, hx₀⟩ := exists_ofLE_eq hsep hlim (bot_le : ⊥ ≤ N) hbot
      (AttractorPt.push f u₁)
    obtain ⟨P₁, hP₁, hle, u₁', hf₁, hu₁⟩ := exists_descend_U hsep f hf hP₀ hf₀ u₁ x₀ hx₀.symm
    obtain ⟨P₂, hP₂, hle₂, u₂', hf₂, hu₂⟩ := exists_descend_U hsep f hf hP₁ hf₁ u₂
      (AttractorPt.ofLE hle x₀) (by rw [← h1, ← hx₀]; rfl)
    let u₁'' := AttractorPt.ofLE hle₂ u₁'
    have e₁ : AttractorPt.ofLE hP₂ u₁'' = u₁ := hu₁
    have hpush : AttractorPt.push f u₁'' = AttractorPt.push f u₂' := by
      apply ofLE_injective hX hsep hP₂ T
      rw [← push_ofLE, ← push_ofLE, e₁, hu₂, h1]
    have hface : AttractorPt.ofFace (isFace_inf hQ hP₂) u₁'' =
        AttractorPt.ofFace (isFace_inf hQ hP₂) u₂' := by
      apply ofLE_injective_of_dense hUs (hasDensePullback_yoneda U) (inf_le_left : Q ⊓ P₂ ≤ Q) T
      rw [← ofFace_ofLE hQ hP₂, ← ofFace_ofLE hQ hP₂, e₁, hu₂, h2]
    have heq : u₁'' = u₂' := (isFaceCartesian_of_fg hX hsep f hf (isFace_inf hQ hP₂) hf₂ T).1
      (Subtype.ext (Prod.ext hpush hface))
    rw [← e₁, heq, hu₂]
  · rintro ⟨⟨x, w⟩, hxw⟩
    change AttractorPt.ofFace hQ x = AttractorPt.push f w at hxw
    obtain ⟨P₀, hP₀, x₀, -, hf₀, hx₀⟩ := exists_ofLE_eq hsep hlim (bot_le : ⊥ ≤ N) hbot x
    have hF₀ : (Q ⊓ P₀).FG := IsFace.fg (isFace_inf hQ hP₀) hf₀
    obtain ⟨P', hP'Q, hP'₀, w', hfw, hw'⟩ := exists_descend_U hsep f hf (inf_le_left : Q ⊓ P₀ ≤ Q) hF₀ w
      (AttractorPt.ofFace (isFace_inf hQ hP₀) x₀) (by
        rw [← hxw, ← hx₀, ofFace_ofLE])
    let P : AddSubmonoid M := P₀ ⊔ P'
    have hPN : P ≤ N := sup_le hP₀ (hP'Q.trans hQ.le)
    have hPf : P.FG := hf₀.sup hfw
    have hP'P : P' ≤ Q ⊓ P := le_inf hP'Q le_sup_right
    let w'' : AttractorPt aU (Q ⊓ P) T := AttractorPt.ofLE hP'P w'
    have ew : AttractorPt.ofLE (inf_le_left : Q ⊓ P ≤ Q) w'' = w := hw'
    let x₁ : AttractorPt aX P T := AttractorPt.ofLE le_sup_left x₀
    have ex : AttractorPt.ofLE hPN x₁ = x := hx₀
    have hcomp : AttractorPt.ofFace (isFace_inf hQ hPN) x₁ = AttractorPt.push f w'' := by
      apply ofLE_injective hX hsep (inf_le_left : Q ⊓ P ≤ Q) T
      rw [← ofFace_ofLE hQ hPN, ← push_ofLE, ex, ew, hxw]
    obtain ⟨u', hu'⟩ := (isFaceCartesian_of_fg hX hsep f hf (isFace_inf hQ hPN) hPf T).2
      ⟨(x₁, w''), hcomp⟩
    have hu₁ : AttractorPt.push f u' = x₁ := congrArg (fun p => p.1.1) hu'
    have hu₂ : AttractorPt.ofFace (isFace_inf hQ hPN) u' = w'' := congrArg (fun p => p.1.2) hu'
    refine ⟨AttractorPt.ofLE hPN u', Subtype.ext (Prod.ext ?_ ?_)⟩
    · change AttractorPt.push f (AttractorPt.ofLE hPN u') = x
      rw [push_ofLE, hu₁, ex]
    · change AttractorPt.ofFace hQ (AttractorPt.ofLE hPN u') = w
      rw [ofFace_ofLE, hu₂, ew]

/-- **Proposition 5.1 (ii)**, general `S`: `X` separated and "locally of finite presentation" in the form
`IsLimitPreserving`, `N` an arbitrary magnet, `Q` a face of `N`. -/
theorem isFaceCartesian_of_separated (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    (hlim : IsLimitPreserving X) (f : EquivariantHom aU aX) (hf : Space.IsEtale B S hS f.hom)
    {Q N : AddSubmonoid M} (hQ : IsFace Q N) : IsFaceCartesian f hQ :=
  faceComparison_bijective_of_affine ((isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf) f hQ
    (fun T _ => faceComparison_bijective_of_separated_affine hX hsep hlim f hf hQ T)

end PartIIGroup

end AlgMag


#print axioms AlgMag.IsFaceCartesian.of_face
#print axioms AlgMag.exists_not_sum_of_sharp
#print axioms AlgMag.isFaceCartesian_of_fg
#print axioms AlgMag.isFaceCartesian_of_separated
#print axioms AlgMag.ofLE_injective
#print axioms AlgMag.attractor_toPoint_injective_sep
#print axioms AlgMag.exists_ofLE_eq
