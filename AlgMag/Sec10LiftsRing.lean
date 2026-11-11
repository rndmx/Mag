/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.GeneralBaseMilnor

/-!
# Integration over `D(M)` on a first order thickening: ring side

Mayeux, *Algebraic Magnetism*, proof of Corollary 10.3, schemes only. The vanishing of `H¹(D(M), -)`
(Proposition 9.13) amounts to integration, that is, taking the coefficient at `0`. For a square zero
surjection `φ : D → D₀`, the coefficient at `0` is a ring map on the subring `avgRing φ` of those
`w ∈ D[M]` constant modulo `ker φ`. That subring is a Milnor square, hence a push-out of schemes.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgMag.Lifts

open AlgMag.GB

section Monoid

variable {M : Type u} [AddCommMonoid M] {D D₀ : Type u} [CommRing D] [CommRing D₀]

/-- The constants `D → D[M]`. -/
noncomputable abbrev cst (D : Type u) [CommRing D] (M : Type u) [AddCommMonoid M] :
    D →+* AddMonoidAlgebra D M := AddMonoidAlgebra.singleZeroRingHom

/-- `D ×_{D₀[M]} ...`: pairs `(x, w)` with `x ∈ D₀`, `w ∈ D[M]`, `w ≡ x` modulo `ker φ`. -/
noncomputable def avgRing (φ : D →+* D₀) : Subring (D₀ × AddMonoidAlgebra D M) :=
  RingHom.eqLocus ((cst D₀ M).comp (RingHom.fst _ _))
    ((AddMonoidAlgebra.mapRingHom M φ).comp (RingHom.snd _ _))

/-- Projection to `D₀`. -/
noncomputable def avgFst (φ : D →+* D₀) : avgRing (M := M) φ →+* D₀ :=
  (RingHom.fst _ _).comp (avgRing φ).subtype

/-- Projection to `D[M]`. -/
noncomputable def avgSnd (φ : D →+* D₀) : avgRing (M := M) φ →+* AddMonoidAlgebra D M :=
  (RingHom.snd _ _).comp (avgRing φ).subtype

lemma avg_prop (φ : D →+* D₀) (p : avgRing (M := M) φ) :
    AddMonoidAlgebra.mapRingHom M φ (avgSnd φ p) = cst D₀ M (avgFst φ p) := p.2.symm

/-- The Milnor square of `avgRing`. -/
theorem milnor_avg (φ : D →+* D₀) (hs : Function.Surjective φ) :
    MilnorData (avgSnd (M := M) φ) (avgFst φ) (AddMonoidAlgebra.mapRingHom M φ) (cst D₀ M) where
  comm := avg_prop φ
  surj := by
    intro y
    induction y using AddMonoidAlgebra.induction_linear with
    | zero => exact ⟨0, map_zero _⟩
    | add p q hp hq =>
      obtain ⟨p₁, rfl⟩ := hp
      obtain ⟨q₁, rfl⟩ := hq
      exact ⟨p₁ + q₁, map_add _ _ _⟩
    | single n r =>
      obtain ⟨s, rfl⟩ := hs r
      exact ⟨AddMonoidAlgebra.single n s, AddMonoidAlgebra.mapRingHom_single _ _ _⟩
  inj z h₁ h₂ := Subtype.ext (Prod.ext h₂ h₁)
  ex x y h := ⟨⟨(y, x), h.symm⟩, rfl, rfl⟩

lemma coeff_of_avg (φ : D →+* D₀) (p : avgRing (M := M) φ) {k : M} (hk : k ≠ 0) :
    φ ((avgSnd φ p).coeff k) = 0 := by
  classical
  have := congrArg (fun z => z.coeff k) (avg_prop φ p)
  simp only [AddMonoidAlgebra.coeff_mapRingHom] at this
  rw [this]
  change (Finsupp.single (0 : M) _) k = 0
  rw [Finsupp.single_apply, if_neg (Ne.symm hk)]

lemma coeff_zero_of_avg (φ : D →+* D₀) (p : avgRing (M := M) φ) :
    φ ((avgSnd φ p).coeff 0) = avgFst φ p := by
  classical
  have := congrArg (fun z => z.coeff (0 : M)) (avg_prop φ p)
  simp only [AddMonoidAlgebra.coeff_mapRingHom] at this
  rw [this]
  change (Finsupp.single (0 : M) _) 0 = _
  rw [Finsupp.single_eq_same]

/-- The section `D → avgRing φ`. -/
noncomputable def avgCst (φ : D →+* D₀) : D →+* avgRing (M := M) φ :=
  RingHom.codRestrict (((φ.prod (cst D M)) : D →+* D₀ × AddMonoidAlgebra D M)) (avgRing φ) (fun d => by
    change cst D₀ M (φ d) = AddMonoidAlgebra.mapRingHom M φ (cst D M d)
    simp [cst, AddMonoidAlgebra.singleZeroRingHom])

lemma avgSnd_cst (φ : D →+* D₀) : (avgSnd (M := M) φ).comp (avgCst φ) = cst D M := rfl
lemma avgFst_cst (φ : D →+* D₀) : (avgFst (M := M) φ).comp (avgCst φ) = φ := rfl

/-- `q` is surjective. -/
lemma avgFst_surjective (φ : D →+* D₀) (hs : Function.Surjective φ) :
    Function.Surjective (avgFst (M := M) φ) := fun x => by
  obtain ⟨d, rfl⟩ := hs x
  exact ⟨avgCst φ d, rfl⟩

/-- The two level ring: square zero passes to `D[M]`. -/
lemma map_sq_zero (φ : D →+* D₀) (hq : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0)
    (x y : AddMonoidAlgebra D M) (hx : AddMonoidAlgebra.mapRingHom M φ x = 0)
    (hy : AddMonoidAlgebra.mapRingHom M φ y = 0) : x * y = 0 := by
  have hcx : ∀ a, φ (x.coeff a) = 0 := fun a => by
    have := congrArg (fun z => z.coeff a) hx
    simpa using this
  have hcy : ∀ a, φ (y.coeff a) = 0 := fun a => by
    have := congrArg (fun z => z.coeff a) hy
    simpa using this
  rw [AddMonoidAlgebra.mul_def]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun c _ => ?_
  change AddMonoidAlgebra.single _ (x.coeff a * y.coeff c) = 0
  rw [hq _ _ (hcx a) (hcy c), AddMonoidAlgebra.single_zero]

lemma map_surjective (φ : D →+* D₀) (hs : Function.Surjective φ) :
    Function.Surjective (AddMonoidAlgebra.mapRingHom M φ) :=
  (milnor_avg φ hs).surj

/-- `μ : D[M] → D[M][M]`, `a e^m ↦ a e₂^m e₁^m`: the multiplication of `D(M)` in the variable. -/
noncomputable def diag (D : Type u) [CommRing D] (M : Type u) [AddCommMonoid M] :
    AddMonoidAlgebra D M →+* AddMonoidAlgebra (AddMonoidAlgebra D M) M :=
  AddMonoidAlgebra.liftNCRingHom ((cst _ M).comp (cst D M))
    { toFun := fun m => AddMonoidAlgebra.single (Multiplicative.toAdd m)
        (AddMonoidAlgebra.single (Multiplicative.toAdd m) 1)
      map_one' := rfl
      map_mul' := fun x y => by simp [AddMonoidAlgebra.single_mul_single] }
    (fun _ _ => Commute.all _ _)

lemma diag_single (m : M) (a : D) : diag D M (AddMonoidAlgebra.single m a) =
    AddMonoidAlgebra.single m (AddMonoidAlgebra.single m a) := by
  simp [diag, cst, AddMonoidAlgebra.liftNCRingHom, AddMonoidAlgebra.singleZeroRingHom,
    AddMonoidAlgebra.single_mul_single]

end Monoid

section Group

variable {M : Type u} [AddCommGroup M] {D D₀ : Type u} [CommRing D] [CommRing D₀]

/-- Coefficient at `0` of a product, when the terms off `0` multiply to zero. -/
lemma coeff_zero_mul (x y : AddMonoidAlgebra D M)
    (h : ∀ a, a ≠ 0 → x.coeff a * y.coeff (-a) = 0) :
    (x * y).coeff 0 = x.coeff 0 * y.coeff 0 := by
  classical
  have key : ∀ x y : AddMonoidAlgebra D M, (x * y).coeff 0 = x.coeff.sum fun a r => r * y.coeff (-a) := by
    intro x y
    induction x using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add p q hp hq =>
      rw [add_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq, AddMonoidAlgebra.coeff_add,
        Finsupp.sum_add_index' (by simp) (by simp [add_mul])]
    | single a r =>
      rw [AddMonoidAlgebra.coeff_single_mul_eq_mul_coeff (m₂ := -a)
        (H := fun m' _ => by rw [eq_neg_iff_add_eq_zero, add_comm]),
        AddMonoidAlgebra.coeff_single, Finsupp.sum_single_index (by simp)]
  rw [key, Finsupp.sum]
  by_cases h0 : x.coeff 0 = 0
  · rw [h0, zero_mul]
    refine Finset.sum_eq_zero fun a ha => ?_
    refine h a ?_
    rintro rfl
    exact (Finsupp.mem_support_iff.1 ha) h0
  · rw [Finset.sum_eq_single 0, neg_zero]
    · intro b _ hb
      exact h b hb
    · intro hc
      exact absurd (Finsupp.notMem_support_iff.1 hc) h0

/-- Integration: the coefficient at `0`, a ring map on `avgRing φ` when `ker φ` has square zero. -/
noncomputable def avgInt (φ : D →+* D₀) (hq : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0) :
    avgRing (M := M) φ →+* D where
  toFun p := (avgSnd φ p).coeff 0
  map_one' := by simp [map_one, AddMonoidAlgebra.one_def]
  map_zero' := by simp
  map_add' p q := by simp
  map_mul' p q := by
    rw [map_mul]
    refine coeff_zero_mul _ _ fun a ha => hq _ _ ?_ ?_
    · exact coeff_of_avg φ p ha
    · exact coeff_of_avg φ q (neg_ne_zero.2 ha)

lemma avgInt_cst (φ : D →+* D₀) (hq : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0) :
    (avgInt (M := M) φ hq).comp (avgCst φ) = RingHom.id D := by
  ext d
  change (AddMonoidAlgebra.single (0 : M) d).coeff 0 = d
  simp

lemma φ_avgInt (φ : D →+* D₀) (hq : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0) :
    φ.comp (avgInt (M := M) φ hq) = avgFst φ := by
  ext p
  exact coeff_zero_of_avg φ p

end Group

end AlgMag.Lifts
