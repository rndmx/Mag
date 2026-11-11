/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartS5Graded

/-!
# Equivariant Artin approximation: spreading `(f, r)` and the `S`-structure, on rings

Part of the proof of **Theorem 6.8 (ii)** (= Theorem A.2 (ii)) of Algebraic Magnetism (Mayeux,
Semigroup Forum 113 (2026)), through the specialization to `D(M)` of Alper–Hall–Rydh, Corollary 10.2.


For `Q → C` onto with kernel `(f)`, the data `f, r` and the map `Γ(S) → C` are defined over
`Q_R = P ⊗_{P₀} R` for `R ⊆ P̂₀` a finite type `P₀`-subalgebra (the functor `F` of the approximation step).
-/

open DirectSum TensorProduct

universe u

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

namespace AlgMag.ChartS5

open ChartAlg

variable {C M : Type u} [CommRing C] [AddCommGroup M] [DecidableEq M] {ι : Type u} [Finite ι]
  {𝒞 : M → AddSubgroup C} [GradedRing 𝒞] {m : Ideal C} {w : ι → M} {x : ι → C}
  (hx : ∀ i, x i ∈ 𝒞 (w i)) (hC : CompletePair 𝒞 m)

noncomputable instance (priority := 2000) fastAlgRs {w : ι → M} {Rh : Type u} [CommRing Rh]
    [Algebra (P0 w ℤ) Rh] (s : Finset Rh) : Algebra (P0 w ℤ) (Rs w s) := Subalgebra.algebra _

/-- `Q_{R_s} → C`. -/
noncomputable def varpi (s : Finset (P0hat w x m)) : QR w (Rs w s) →+* C :=
  (Qmap hx hC).comp (QRmap w (RsI w s) : QR w (Rs w s) →+* QR w (P0hat w x m))

lemma varpi_LE {s t : Finset (P0hat w x m)} (h : s ⊆ t) (q : QR w (Rs w s)) :
    varpi hx hC t (QRmap w (RsLE w h) q) = varpi hx hC s q :=
  congrArg (Qmap hx hC) (QRmap_RsI_RsLE w h q)

lemma varpi_mem {s : Finset (P0hat w x m)} {d : M} {q : QR w (Rs w s)} (hq : q ∈ qGrade w (Rs w s) d) :
    varpi hx hC s q ∈ 𝒞 d := by
  have h1 : qProj d (QRmap w (RsI w s) q) = QRmap w (RsI w s) q := QRmap_mem w (RsI w s) hq
  have h2 := Qmap_qProj hx hC d (QRmap w (RsI w s) q)
  rw [h1] at h2
  have e : varpi hx hC s q = Qmap hx hC (QRmap w (RsI w s) q) := rfl
  rw [e, h2]
  exact SetLike.coe_mem _

variable {s₁ : ℕ} (F : Fin s₁ → Qring w x m)
  (hF : Ideal.span (Set.range F) = RingHom.ker (Qmap hx hC))

include hF in
/-- Kernel elements land in the span of `F`, at a further level. -/
theorem exists_mem_span {s : Finset (P0hat w x m)} (F₀ : Fin s₁ → QR w (Rs w s))
    (hF₀ : ∀ ℓ, QRmap w (RsI w s) (F₀ ℓ) = F ℓ) (q : QR w (Rs w s)) (hq : varpi hx hC s q = 0) :
    ∃ (t : Finset (P0hat w x m)) (h : s ⊆ t),
      QRmap w (RsLE w h) q ∈ Ideal.span (Set.range fun ℓ => QRmap w (RsLE w h) (F₀ ℓ)) := by
  classical
  have h1 : (QRmap w (RsI w s) q : Qring w x m) ∈ Ideal.span (Set.range F) := by
    rw [hF]; exact hq
  obtain ⟨a, ha⟩ := (Ideal.mem_span_range_iff_exists_fun).1 h1
  obtain ⟨t, hst, a', ha'⟩ := exists_QR_lift_family w s a
  let d : QR w (Rs w t) := QRmap w (RsLE w hst) q -
    ∑ ℓ, a' ℓ * QRmap w (RsLE w hst) (F₀ ℓ)
  have hd : QRmap w (RsI w t) d = 0 := by
    simp only [d, map_sub, map_sum, map_mul, QRmap_RsI_RsLE, ha', hF₀]
    rw [ha, sub_self]
  obtain ⟨t', ht', hk⟩ := exists_QR_kill w d hd
  refine ⟨t', hst.trans ht', ?_⟩
  have e : ∀ y : QR w (Rs w s), QRmap w (RsLE w (hst.trans ht')) y =
      QRmap w (RsLE w ht') (QRmap w (RsLE w hst) y) := fun y => (QRmap_RsLE_RsLE w hst ht' y).symm
  have h2 : QRmap w (RsLE w ht') (QRmap w (RsLE w hst) q) =
      ∑ ℓ, QRmap w (RsLE w ht') (a' ℓ) * QRmap w (RsLE w ht') (QRmap w (RsLE w hst) (F₀ ℓ)) := by
    have := hk
    simp only [d, map_sub, map_sum, map_mul, sub_eq_zero] at this
    exact this
  rw [e, h2]
  refine Ideal.sum_mem _ fun ℓ _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨ℓ, ?_⟩)
  exact e _

/-- **The functor `F`**: `f` (homogeneous) and `r` (syzygies) are defined over a finite type subalgebra. -/
theorem exists_spread {t₁ : ℕ} (r : Fin t₁ → Fin s₁ → Qring w x m)
    (hs : ∀ j, ∑ ℓ, r j ℓ * F ℓ = 0) (deg : Fin s₁ → M) (hd : ∀ ℓ, qProj (deg ℓ) (F ℓ) = F ℓ) :
    ∃ (s : Finset (P0hat w x m)) (F₀ : Fin s₁ → QR w (Rs w s)) (r₀ : Fin t₁ → Fin s₁ → QR w (Rs w s)),
      (∀ ℓ, QRmap w (RsI w s) (F₀ ℓ) = F ℓ) ∧ (∀ j ℓ, QRmap w (RsI w s) (r₀ j ℓ) = r j ℓ) ∧
      (∀ j, ∑ ℓ, r₀ j ℓ * F₀ ℓ = 0) ∧ ∀ ℓ, F₀ ℓ ∈ qGrade w (Rs w s) (deg ℓ) := by
  classical
  obtain ⟨t, -, q, hq⟩ := exists_QR_lift_family w (∅ : Finset (P0hat w x m))
    (Sum.elim F (fun p : Fin t₁ × Fin s₁ => r p.1 p.2))
  let F' : Fin s₁ → QR w (Rs w t) := fun ℓ => qProjR w _ (deg ℓ) (q (Sum.inl ℓ))
  let r' : Fin t₁ → Fin s₁ → QR w (Rs w t) := fun j ℓ => q (Sum.inr (j, ℓ))
  have hF' : ∀ ℓ, QRmap w (RsI w t) (F' ℓ) = F ℓ := fun ℓ => by
    simp only [F']
    rw [QRmap_qProjR, hq (Sum.inl ℓ)]
    exact hd ℓ
  have hr' : ∀ j ℓ, QRmap w (RsI w t) (r' j ℓ) = r j ℓ := fun j ℓ => hq (Sum.inr (j, ℓ))
  have hz : ∀ j, ∃ (t' : Finset (P0hat w x m)) (h : t ⊆ t'),
      QRmap w (RsLE w h) (∑ ℓ, r' j ℓ * F' ℓ) = 0 := fun j =>
    exists_QR_kill w _ (by simp only [map_sum, map_mul, hF', hr']; exact hs j)
  choose T hT hk using hz
  let U : Finset (P0hat w x m) := t ∪ Finset.univ.biUnion T
  have htU : t ⊆ U := Finset.subset_union_left
  have hTU : ∀ j, T j ⊆ U := fun j =>
    (Finset.subset_biUnion_of_mem T (Finset.mem_univ j)).trans Finset.subset_union_right
  refine ⟨U, fun ℓ => QRmap w (RsLE w htU) (F' ℓ), fun j ℓ => QRmap w (RsLE w htU) (r' j ℓ),
    fun ℓ => by rw [QRmap_RsI_RsLE, hF'], fun j ℓ => by rw [QRmap_RsI_RsLE, hr'], fun j => ?_,
    fun ℓ => QRmap_mem w _ (qProjR_mem w _ _)⟩
  have := congrArg (QRmap w (RsLE w (hTU j))) (hk j)
  rw [map_zero, QRmap_RsLE_RsLE, map_sum] at this
  simpa only [map_mul] using this

include hF in
/-- **The `S`-structure over a finite level.** `A₀ = Γ(S)` is of finite type over `ℤ`, and
`κ : A₀ → C` lands in degree `0`. Then `κ` lifts to degree `0` of `Q_{R_t}/(F₀)`. -/
theorem exists_structure [IsNoetherianRing (MvPolynomial ι ℤ)] {A₀ : Type u} [CommRing A₀] [Algebra.FiniteType ℤ A₀]
    (κ : A₀ →+* C) (hκ : ∀ a, κ a ∈ 𝒞 0)
    (hsurj : Function.Surjective (Qmap hx hC)) {s : Finset (P0hat w x m)}
    (F₀ : Fin s₁ → QR w (Rs w s)) (hF₀ : ∀ ℓ, QRmap w (RsI w s) (F₀ ℓ) = F ℓ) :
    ∃ (t : Finset (P0hat w x m)) (h : s ⊆ t)
      (ρ : A₀ →+* QR w (Rs w t) ⧸ Ideal.span (Set.range fun ℓ => QRmap w (RsLE w h) (F₀ ℓ))),
      (∀ a, ∃ q ∈ qGrade w (Rs w t) 0, Ideal.Quotient.mk _ q = ρ a ∧ varpi hx hC t q = κ a) := by
  classical
  obtain ⟨n, π, hπ⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := ℤ) (S := A₀)).1 inferInstance
  have hker : (RingHom.ker π).FG := IsNoetherian.noetherian _
  obtain ⟨G, hG⟩ := hker
  choose Y hY using fun i : Fin n => hsurj (κ (π (MvPolynomial.X i)))
  obtain ⟨t₀, ht₀, c, hc⟩ := exists_QR_lift_family w s Y
  let c₀ : Fin n → QR w (Rs w t₀) := fun i => qProjR w _ 0 (c i)
  have hc₀ : ∀ i, varpi hx hC t₀ (c₀ i) = κ (π (MvPolynomial.X i)) := fun i => by
    change Qmap hx hC (QRmap w (RsI w t₀) (qProjR w _ 0 (c i))) = _
    rw [QRmap_qProjR, hc]
    have h2 := Qmap_qProj hx hC 0 (Y i)
    rw [hY] at h2
    refine h2.trans ?_
    exact DirectSum.decompose_of_mem_same 𝒞 (hκ _)
  have hc₀m : ∀ i, c₀ i ∈ qGrade w (Rs w t₀) 0 := fun i => qProjR_mem w _ _
  let Λ₀ : MvPolynomial (Fin n) ℤ →+* QR w (Rs w t₀) :=
    (MvPolynomial.aeval c₀ : MvPolynomial (Fin n) ℤ →ₐ[ℤ] QR w (Rs w t₀)).toRingHom
  have hΛ₀ : ∀ p, varpi hx hC t₀ (Λ₀ p) = κ (π p) := fun p => by
    have : (varpi hx hC t₀).comp Λ₀ = κ.comp (π : MvPolynomial (Fin n) ℤ →+* A₀) := by
      apply MvPolynomial.ringHom_ext
      · intro r; simp
      · intro i; simpa [Λ₀] using hc₀ i
    exact congrArg (fun z => z p) this
  have hF₁ : ∀ ℓ, QRmap w (RsI w t₀) (QRmap w (RsLE w ht₀) (F₀ ℓ)) = F ℓ := fun ℓ => by
    rw [QRmap_RsI_RsLE, hF₀]
  have hmem := fun g : G => exists_mem_span hx hC F hF _ hF₁ (Λ₀ g) (by
    rw [hΛ₀]
    have : (g : MvPolynomial (Fin n) ℤ) ∈ RingHom.ker π := by
      rw [← hG]; exact Ideal.subset_span g.2
    rw [RingHom.mem_ker.1 this, map_zero])
  choose T hT hk using hmem
  let U : Finset (P0hat w x m) := t₀ ∪ Finset.univ.biUnion T
  have htU : t₀ ⊆ U := Finset.subset_union_left
  have hTU : ∀ g, T g ⊆ U := fun g =>
    (Finset.subset_biUnion_of_mem T (Finset.mem_univ g)).trans Finset.subset_union_right
  have hsU : s ⊆ U := ht₀.trans htU
  let I := Ideal.span (Set.range fun ℓ => QRmap w (RsLE w hsU) (F₀ ℓ))
  let Λ : MvPolynomial (Fin n) ℤ →+* QR w (Rs w U) ⧸ I :=
    (Ideal.Quotient.mk I).comp ((QRmap w (RsLE w htU) : _ →ₐ[_] _).toRingHom.comp Λ₀)
  have hΛk : ∀ p ∈ RingHom.ker (π : MvPolynomial (Fin n) ℤ →+* A₀), Λ p = 0 := by
    have hG' : Ideal.span (G : Set (MvPolynomial (Fin n) ℤ)) ≤ RingHom.ker Λ := by
      refine Ideal.span_le.2 fun g hg => ?_
      refine Ideal.Quotient.eq_zero_iff_mem.2 ?_
      have h1 := hk ⟨g, hg⟩
      have hle : (Ideal.span (Set.range fun ℓ => QRmap w (RsLE w (hT ⟨g, hg⟩))
          (QRmap w (RsLE w ht₀) (F₀ ℓ)))).map
          ((QRmap w (RsLE w (hTU ⟨g, hg⟩)) : _ →ₐ[_] _).toRingHom) ≤ I := by
        rw [Ideal.map_le_iff_le_comap, Ideal.span_le]
        rintro _ ⟨ℓ, rfl⟩
        refine Ideal.subset_span ⟨ℓ, ?_⟩
        have e1 := QRmap_RsLE_RsLE w (hT ⟨g, hg⟩) (hTU ⟨g, hg⟩) (QRmap w (RsLE w ht₀) (F₀ ℓ))
        have e2 := QRmap_RsLE_RsLE w ht₀ ((hT ⟨g, hg⟩).trans (hTU ⟨g, hg⟩)) (F₀ ℓ)
        exact e2.symm.trans e1.symm
      have h2 := hle (Ideal.mem_map_of_mem _ h1)
      have e : (QRmap w (RsLE w (hTU ⟨g, hg⟩)) : _ →ₐ[_] _).toRingHom
          (QRmap w (RsLE w (hT ⟨g, hg⟩)) (Λ₀ g)) = QRmap w (RsLE w htU) (Λ₀ g) :=
        QRmap_RsLE_RsLE w _ _ _
      rw [e] at h2
      exact h2
    intro p hp
    have hp' : p ∈ Ideal.span (G : Set (MvPolynomial (Fin n) ℤ)) := by rw [hG]; exact hp
    exact hG' hp'
  have hπ' : Function.Surjective (π : MvPolynomial (Fin n) ℤ →+* A₀) := hπ
  let ρ : A₀ →+* QR w (Rs w U) ⧸ I :=
    RingHom.liftOfSurjective (π : MvPolynomial (Fin n) ℤ →+* A₀) hπ' ⟨Λ, hΛk⟩
  have hρ : ∀ p, ρ (π p) = Λ p := fun p =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ p
  have hdeg : ∀ p, Λ₀ p ∈ qGrade w (Rs w t₀) 0 := fun p => by
    induction p using MvPolynomial.induction_on with
    | C r =>
      have : Λ₀ (MvPolynomial.C r) = (r : ℤ) • (1 : QR w (Rs w t₀)) :=
        (MvPolynomial.aeval_C _ _).trans (Algebra.algebraMap_eq_smul_one r)
      rw [this]
      exact zsmul_mem SetLike.GradedOne.one_mem r
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      have e : Λ₀ (MvPolynomial.X i) = c₀ i := by simp [Λ₀]
      rw [e]
      simpa using SetLike.GradedMul.mul_mem hp (hc₀m i)
  refine ⟨U, hsU, ρ, fun a => ?_⟩
  obtain ⟨p, rfl⟩ := hπ' a
  exact ⟨QRmap w (RsLE w htU) (Λ₀ p), QRmap_mem w _ (hdeg p), (hρ p).symm,
    (varpi_LE hx hC htU _).trans (hΛ₀ p)⟩

end AlgMag.ChartS5
