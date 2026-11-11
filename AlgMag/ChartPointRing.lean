/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartPoint

/-!
# Ring theory for Lemma 1.1 (chart-lemma proof, §1)

* `AlgMag.ChartPoint.stable_ideal_top_or_nil`: "`G` is transitive on `O`": for `O = Spec k[N]` with
  `D(M)` acting, a closed subset of `O` stable under the action is empty or everything.
* `AlgMag.ChartPoint.surjective_of_epi_of_local`: a local epimorphism from an artinian local ring is
  surjective (the Nakayama step of the proof of Lemma 1.1).
-/

open CategoryTheory TensorProduct

universe u

namespace AlgMag.ChartPoint

open ChartMain

section Stable

variable {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M] (N : AddSubgroup M)

/-- The coaction `A[N] → A[N][M]`, `z ↦ z ⊗ z`. -/
noncomputable def coact (A : Type u) [CommRing A] : AddMonoidAlgebra A N →+*
    AddMonoidAlgebra (AddMonoidAlgebra A N) M :=
  evalAt (ρ0 N A) (c0 N A * resChar N (AddMonoidAlgebra.of (AddMonoidAlgebra A N) M))

lemma coact_coeff (p : AddMonoidAlgebra A N) (z : N) :
    (coact N A p).coeff (z : M) =
      AddMonoidAlgebra.single z (p.coeff z) := by
  classical
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq =>
    rw [map_add]
    simp [hp, hq, AddMonoidAlgebra.single_add]
  | single w b =>
    have e : coact N A (AddMonoidAlgebra.single w b) =
        AddMonoidAlgebra.single (w : M) (AddMonoidAlgebra.single w b) := by
      rw [coact, evalAt_single]
      change AddMonoidAlgebra.single 0 (AddMonoidAlgebra.single 0 b) *
        (AddMonoidAlgebra.single 0 (AddMonoidAlgebra.single w 1) *
          AddMonoidAlgebra.single (w : M) 1) = _
      simp [AddMonoidAlgebra.single_mul_single]
    rw [e]
    by_cases h : w = z
    · subst h; simp
    · have h' : (w : M) ≠ z := fun e => h (Subtype.ext e)
      simp [h, h', AddMonoidAlgebra.coeff_single]

/-- A coefficient of an element of `I·R[M]` lies in `I`. -/
lemma coeff_mem_of_mem_map {R : Type u} [CommRing R] (I : Ideal R) {f : AddMonoidAlgebra R M}
    (hf : f ∈ I.map (AddMonoidAlgebra.singleZeroRingHom : R →+* AddMonoidAlgebra R M)) (m : M) :
    f.coeff m ∈ I := by
  classical
  refine Submodule.span_induction (p := fun f _ => ∀ m : M, f.coeff m ∈ I) ?_ ?_ ?_ ?_ hf m
  · rintro _ ⟨r, hr, rfl⟩ m
    change (AddMonoidAlgebra.single 0 r : AddMonoidAlgebra R M).coeff m ∈ I
    rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs
    · exact hr
    · exact I.zero_mem
  · intro m; simp
  · intro a b _ _ ha hb m
    have : (a + b).coeff m = a.coeff m + b.coeff m := by simp
    rw [this]; exact I.add_mem (ha m) (hb m)
  · intro a x _ hx m
    change (a * x).coeff m ∈ I
    induction a using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add p q hp hq =>
      rw [add_mul]
      have : (p * x + q * x).coeff m = (p * x).coeff m + (q * x).coeff m := by simp
      rw [this]; exact I.add_mem hp hq
    | single w b =>
      rw [AddMonoidAlgebra.coeff_single_mul_apply]
      exact I.mul_mem_left _ (hx _)

/-- **§1, "`G` is transitive on `O`"**: homogeneous elements of `k[N]` are units or zero, so a
closed subset of `O = Spec k[N]` stable under `D(M)` is empty or everything. The stability, in one
direction, says that a prime of `k[N][M]` above `I` under `pr` is above `I` under the coaction. -/
theorem stable_ideal_top_or_nil {k : Type u} [Field k] (I : Ideal (AddMonoidAlgebra k N))
    (h : ∀ Q : Ideal (AddMonoidAlgebra (AddMonoidAlgebra k N) M), Q.IsPrime →
      I.map AddMonoidAlgebra.singleZeroRingHom ≤ Q → I.map (coact N k) ≤ Q) :
    I = ⊤ ∨ ∀ g ∈ I, IsNilpotent g := by
  classical
  by_cases htop : I = ⊤
  · exact Or.inl htop
  refine Or.inr fun g hg => ?_
  have h1 : coact N k g ∈ (I.map (AddMonoidAlgebra.singleZeroRingHom :
      AddMonoidAlgebra k N →+* AddMonoidAlgebra (AddMonoidAlgebra k N) M)).radical := by
    rw [Ideal.radical_eq_sInf]
    refine (Submodule.mem_sInf).2 ?_
    rintro Q ⟨hQ, hp⟩
    exact h Q hp hQ (Ideal.mem_map_of_mem _ hg)
  obtain ⟨e, he⟩ := h1
  refine ⟨e, ?_⟩
  rw [← map_pow] at he
  ext z
  by_contra hne
  have hne' : (g ^ e).coeff z ≠ 0 := hne
  have hm := coeff_mem_of_mem_map I he (z : M)
  rw [coact_coeff] at hm
  apply htop
  refine Ideal.eq_top_of_isUnit_mem _ hm ?_
  refine IsUnit.of_mul_eq_one (AddMonoidAlgebra.single (-z) ((g ^ e).coeff z)⁻¹) ?_
  rw [AddMonoidAlgebra.single_mul_single, add_neg_cancel, mul_inv_cancel₀ hne']
  rfl

end Stable

section Epi

/-- **Lemma 1.1, Nakayama step**: `A` local with nilpotent maximal ideal (e.g. artinian), `B` a
nonzero `A`-algebra such that `κ(A) → B/m_A B` is surjective. Then `A → B` is surjective. -/
theorem surjective_of_residue_surjective {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A]
    (f : A →+* B) (hnil : IsNilpotent (IsLocalRing.maximalIdeal A))
    (h : ∀ b : B, ∃ a : A, b - f a ∈ (IsLocalRing.maximalIdeal A).map f) :
    Function.Surjective f := by
  let m := (IsLocalRing.maximalIdeal A).map f
  let R : Subring B := f.range
  obtain ⟨n, hn⟩ := hnil
  have hm : m ^ n = ⊥ := by
    change (IsLocalRing.maximalIdeal A).map f ^ n = ⊥
    rw [← Ideal.map_pow, hn]
    exact Ideal.map_bot
  -- `B = f(A) + m^i` for all `i`
  have key : ∀ i : ℕ, ∀ b : B, ∃ a : A, b - f a ∈ m ^ i := by
    intro i
    induction i with
    | zero => exact fun b => ⟨0, by simp⟩
    | succ i ih =>
      intro b
      obtain ⟨a, ha⟩ := ih b
      -- every element of `m^i` is, modulo `m^(i+1)`, in `f(m^i)`
      have step : ∀ y ∈ m ^ i, ∃ a' : A, y - f a' ∈ m ^ (i + 1) := by
        intro y hy
        have hmap : m ^ i = (IsLocalRing.maximalIdeal A ^ i).map f := by
          change _ ^ i = _; rw [Ideal.map_pow]
        rw [hmap] at hy
        refine Submodule.span_induction (p := fun y _ => ∃ a' : A, y - f a' ∈ m ^ (i + 1))
          ?_ ?_ ?_ ?_ hy
        · rintro _ ⟨r, -, rfl⟩
          exact ⟨r, by simp⟩
        · exact ⟨0, by simp⟩
        · rintro x y _ _ ⟨a1, h1⟩ ⟨a2, h2⟩
          refine ⟨a1 + a2, ?_⟩
          have : x + y - f (a1 + a2) = (x - f a1) + (y - f a2) := by rw [map_add]; ring
          rw [this]; exact Ideal.add_mem _ h1 h2
        · rintro c y hy ⟨a1, h1⟩
          obtain ⟨c0, hc0⟩ := h c
          refine ⟨c0 * a1, ?_⟩
          have hy' : y ∈ m ^ i := by rw [hmap]; exact hy
          have : c • y - f (c0 * a1) = (c - f c0) * y + f c0 * (y - f a1) := by
            rw [map_mul, smul_eq_mul]; ring
          rw [this]
          refine Ideal.add_mem _ ?_ (Ideal.mul_mem_left _ _ h1)
          rw [pow_succ']
          exact Ideal.mul_mem_mul hc0 hy'
      obtain ⟨a', ha'⟩ := step _ ha
      refine ⟨a + a', ?_⟩
      have : b - f (a + a') = (b - f a) - f a' := by rw [map_add]; ring
      rw [this]; exact ha'
  intro b
  obtain ⟨a, ha⟩ := key n b
  rw [hm, Ideal.mem_bot, sub_eq_zero] at ha
  exact ⟨a, ha.symm⟩

end Epi

end AlgMag.ChartPoint

#print axioms AlgMag.ChartPoint.stable_ideal_top_or_nil
#print axioms AlgMag.ChartPoint.surjective_of_residue_surjective
