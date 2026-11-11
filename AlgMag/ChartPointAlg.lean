/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartActionGrading
import Mathlib.RingTheory.Coalgebra.GroupLike
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Algebra of the chart-lemma proof, §1: closed subgroups of `D(M)` over a field

* `AlgMag.ChartPoint.eval_eq_zero_of_trivial_on`: Hopf ideals of `K[M]`, `K` a field: a closed
  subgroup `V(J)` of `D(M)_K` is `D(M/Z₀)` with `Z₀ = {z | e_z - 1 ∈ J}` (SGA3 VIII 3.2).
* `AlgMag.ChartPoint.exists_inv_of_homogeneous`: homogeneous elements outside `I_O` are units
  modulo `I_O`, for `A/I_O = K[Z₀]`.
-/

open CategoryTheory TensorProduct

universe u

namespace AlgMag.ChartPoint

open ChartMain

section Hopf

variable {K M : Type u} [Field K] [AddCommGroup M] (J : Ideal (AddMonoidAlgebra K M))

/-- `e_z - 1 ∈ J`: the subgroup `Z₀` attached to an ideal of `K[M]`. -/
def stabSubgroup : AddSubgroup M where
  carrier := {z | AddMonoidAlgebra.single z (1 : K) - 1 ∈ J}
  zero_mem' := by
    change AddMonoidAlgebra.single (0 : M) (1 : K) - 1 ∈ J
    rw [← AddMonoidAlgebra.one_def, sub_self]
    exact J.zero_mem
  add_mem' := by
    intro a b ha hb
    change AddMonoidAlgebra.single a (1 : K) - 1 ∈ J at ha
    change AddMonoidAlgebra.single b (1 : K) - 1 ∈ J at hb
    change AddMonoidAlgebra.single (a + b) (1 : K) - 1 ∈ J
    have e : AddMonoidAlgebra.single (a + b) (1 : K) - 1 =
        AddMonoidAlgebra.single a (1 : K) * (AddMonoidAlgebra.single b (1 : K) - 1) +
          (AddMonoidAlgebra.single a (1 : K) - 1) := by
      rw [mul_sub, AddMonoidAlgebra.single_mul_single, mul_one, mul_one]
      ring
    rw [e]
    exact J.add_mem (J.mul_mem_left _ hb) ha
  neg_mem' := by
    intro a ha
    change AddMonoidAlgebra.single a (1 : K) - 1 ∈ J at ha
    change AddMonoidAlgebra.single (-a) (1 : K) - 1 ∈ J
    have e : AddMonoidAlgebra.single (-a) (1 : K) - 1 =
        - (AddMonoidAlgebra.single (-a) (1 : K) * (AddMonoidAlgebra.single a (1 : K) - 1)) := by
      rw [mul_sub, AddMonoidAlgebra.single_mul_single, mul_one, mul_one, neg_add_cancel,
        ← AddMonoidAlgebra.one_def]
      ring
    rw [e]
    exact J.neg_mem (J.mul_mem_left _ ha)

/-- The image of `e_m` in `K[M]/J`. -/
noncomputable def bq : Multiplicative M →* (AddMonoidAlgebra K M ⧸ J) :=
  (Ideal.Quotient.mk J).toMonoidHom.comp (AddMonoidAlgebra.of K M)

lemma bq_ofAdd (m : M) : bq J (Multiplicative.ofAdd m) =
    Ideal.Quotient.mk J (AddMonoidAlgebra.single m 1) := rfl

/-- `evalAt` is `K`-linear when the coefficient map is the structure map. -/
lemma evalAt_algebraMap_smul {R : Type*} [CommRing R] [Algebra K R] (h : Multiplicative M →* R)
    (r : K) (f : AddMonoidAlgebra K M) :
    evalAt (algebraMap K R) h (r • f) = r • evalAt (algebraMap K R) h f := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [smul_add, map_add, hp, hq]
  | single m c =>
    rw [AddMonoidAlgebra.smul_single, evalAt_single, evalAt_single, smul_eq_mul, map_mul,
      Algebra.smul_def, mul_assoc]

/-- The `K`-linear map `K[M]/J → R` of a point of `V(J)`. -/
noncomputable def quotLin {R : Type*} [CommRing R] [Algebra K R] (h : Multiplicative M →* R)
    (hJ : ∀ f ∈ J, evalAt (algebraMap K R) h f = 0) : (AddMonoidAlgebra K M ⧸ J) →ₗ[K] R where
  toFun := Ideal.Quotient.lift J (evalAt (algebraMap K R) h) hJ
  map_add' := map_add _
  map_smul' r x := by
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.lift J _ hJ (Ideal.Quotient.mk J (r • f)) = _
    simp only [Ideal.Quotient.lift_mk, RingHom.id_apply]
    exact evalAt_algebraMap_smul h r f

lemma quotLin_bq {R : Type*} [CommRing R] [Algebra K R] (h : Multiplicative M →* R)
    (hJ : ∀ f ∈ J, evalAt (algebraMap K R) h f = 0) (m : M) :
    quotLin J h hJ (bq J (Multiplicative.ofAdd m)) = h (Multiplicative.ofAdd m) := by
  change evalAt (algebraMap K R) h (AddMonoidAlgebra.single m 1) = _
  rw [evalAt_single, map_one, one_mul]

lemma mk_single (m : M) (c : K) : Ideal.Quotient.mk J (AddMonoidAlgebra.single m c) =
    c • bq J (Multiplicative.ofAdd m) := by
  have es : AddMonoidAlgebra.single m c = c • AddMonoidAlgebra.single m (1 : K) := by
    rw [AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one]
  rw [es]
  rfl

lemma linearMap_ext_bq {N : Type*} [AddCommGroup N] [Module K N]
    {f g : (AddMonoidAlgebra K M ⧸ J) →ₗ[K] N}
    (h : ∀ m : M, f (bq J (Multiplicative.ofAdd m)) = g (bq J (Multiplicative.ofAdd m))) :
    f = g := by
  ext x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single m c =>
    rw [mk_single, map_smul, map_smul, h]

/-- The two universal points of `V(J) × V(J)`, multiplied. -/
noncomputable def diagPt : Multiplicative M →*
    ((AddMonoidAlgebra K M ⧸ J) ⊗[K] (AddMonoidAlgebra K M ⧸ J)) where
  toFun m := bq J m ⊗ₜ[K] bq J m
  map_one' := by rw [map_one]; rfl
  map_mul' a b := by rw [map_mul, Algebra.TensorProduct.tmul_mul_tmul]

variable {J}

/-- The factorization of a character through `M/Z`. -/
noncomputable def factorChar {R : Type*} [CommMonoid R] (Z : AddSubgroup M)
    (h : Multiplicative M →* R) (hZ : ∀ z ∈ Z, h (Multiplicative.ofAdd z) = 1) :
    Multiplicative (M ⧸ Z) →* R :=
  AddMonoidHom.toMultiplicativeLeft (QuotientAddGroup.lift Z (MonoidHom.toAdditiveRight h)
    (fun z hz => congrArg Additive.ofMul (hZ z hz)))

lemma factorChar_mk {R : Type*} [CommMonoid R] (Z : AddSubgroup M)
    (h : Multiplicative M →* R) (hZ : ∀ z ∈ Z, h (Multiplicative.ofAdd z) = 1) (m : M) :
    factorChar Z h hZ (Multiplicative.ofAdd (QuotientAddGroup.mk m)) = h (Multiplicative.ofAdd m) :=
  rfl

/-- **Hopf ideals of `K[M]`** (SGA3 VIII 3.2). If `V(J)` contains the unit and is stable under
products, then `V(J)` is `D(M/Z₀)`: any point trivial on `Z₀` kills `J`. -/
theorem eval_eq_zero_of_trivial_on
    (hone : ∀ f ∈ J, evalAt (algebraMap K K) (1 : Multiplicative M →* K) f = 0)
    (hmul : ∀ f ∈ J, evalAt (algebraMap K _) (diagPt J) f = 0)
    {R : Type*} [CommRing R] (ρ : K →+* R) (h : Multiplicative M →* R)
    (hZ : ∀ z, AddMonoidAlgebra.single z (1 : K) - 1 ∈ J → h (Multiplicative.ofAdd z) = 1)
    {f : AddMonoidAlgebra K M} (hf : f ∈ J) : evalAt ρ h f = 0 := by
  classical
  let B := AddMonoidAlgebra K M ⧸ J
  have hΔ : ∀ m : M, quotLin J (diagPt J) hmul (bq J (Multiplicative.ofAdd m)) =
      bq J (Multiplicative.ofAdd m) ⊗ₜ[K] bq J (Multiplicative.ofAdd m) :=
    fun m => quotLin_bq J (diagPt J) hmul m
  have hε : ∀ m : M, quotLin J 1 hone (bq J (Multiplicative.ofAdd m)) = 1 :=
    fun m => quotLin_bq J 1 hone m
  let cs : Coalgebra K B :=
    { comul := quotLin J (diagPt J) hmul
      counit := quotLin J 1 hone
      coassoc := by
        refine linearMap_ext_bq J fun m => ?_
        simp only [LinearMap.comp_apply, hΔ, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
        rfl
      rTensor_counit_comp_comul := by
        refine linearMap_ext_bq J fun m => ?_
        simp only [LinearMap.comp_apply, hΔ, LinearMap.rTensor_tmul, hε]
        rfl
      lTensor_counit_comp_comul := by
        refine linearMap_ext_bq J fun m => ?_
        simp only [LinearMap.comp_apply, hΔ, LinearMap.lTensor_tmul, hε, LinearMap.flip_apply]
        rfl }
  have hgl : ∀ m : M, IsGroupLikeElem K (bq J (Multiplicative.ofAdd m)) := fun m =>
    ⟨hε m, hΔ m⟩
  let Z := stabSubgroup J
  have hbZ : ∀ a b : M, bq J (Multiplicative.ofAdd a) = bq J (Multiplicative.ofAdd b) →
      -a + b ∈ Z := by
    intro a b hab
    change AddMonoidAlgebra.single (-a + b) (1 : K) - 1 ∈ J
    rw [bq_ofAdd, bq_ofAdd, Ideal.Quotient.eq] at hab
    have e : AddMonoidAlgebra.single (-a + b) (1 : K) - 1 =
        - (AddMonoidAlgebra.single (-a) (1 : K) *
          (AddMonoidAlgebra.single a (1 : K) - AddMonoidAlgebra.single b 1)) := by
      simp only [mul_sub, AddMonoidAlgebra.single_mul_single, mul_one, neg_add_cancel]
      rw [← AddMonoidAlgebra.one_def]
      ring
    rw [e]
    exact J.neg_mem (J.mul_mem_left _ hab)
  have hZb : ∀ a b : M, -a + b ∈ Z →
      bq J (Multiplicative.ofAdd a) = bq J (Multiplicative.ofAdd b) := by
    intro a b hab
    change AddMonoidAlgebra.single (-a + b) (1 : K) - 1 ∈ J at hab
    rw [bq_ofAdd, bq_ofAdd, eq_comm, Ideal.Quotient.eq]
    have e : AddMonoidAlgebra.single b (1 : K) - AddMonoidAlgebra.single a 1 =
        AddMonoidAlgebra.single a (1 : K) * (AddMonoidAlgebra.single (-a + b) (1 : K) - 1) := by
      rw [mul_sub, AddMonoidAlgebra.single_mul_single, mul_one, mul_one, add_neg_cancel_left]
    rw [e]
    exact J.mul_mem_left _ hab
  -- the family indexed by `M ⧸ Z`
  let bb : M ⧸ Z → B := fun c => bq J (Multiplicative.ofAdd c.out)
  have hbb : ∀ m : M, bb (QuotientAddGroup.mk m) = bq J (Multiplicative.ofAdd m) := fun m =>
    hZb _ _ (QuotientAddGroup.eq.1 (Quotient.out_eq' (QuotientAddGroup.mk m : M ⧸ Z)))
  have hinj : Function.Injective bb := by
    intro c d hcd
    have := hbZ _ _ hcd
    rw [← Quotient.out_eq' c, ← Quotient.out_eq' d]
    exact QuotientAddGroup.eq.2 this
  have hli : LinearIndependent K bb := by
    have h0 : LinearIndepOn K id {a : B | IsGroupLikeElem K a} := linearIndepOn_isGroupLikeElem
    have h1 : LinearIndependent K (fun a : {a : B | IsGroupLikeElem K a} => (a : B)) := h0
    exact h1.comp (fun c => ⟨bb c, hgl _⟩) (fun c d e => hinj (congrArg Subtype.val e))
  -- `f` has zero sums over the classes
  let l : (M ⧸ Z) →₀ K := f.coeff.mapDomain QuotientAddGroup.mk
  have hl : Finsupp.linearCombination K bb l = Ideal.Quotient.mk J f := by
    have : ∀ p : AddMonoidAlgebra K M,
        Finsupp.linearCombination K bb (p.coeff.mapDomain QuotientAddGroup.mk) =
          Ideal.Quotient.mk J p := by
      intro p
      induction p using AddMonoidAlgebra.induction_linear with
      | zero => simp
      | add p q hp hq =>
        rw [AddMonoidAlgebra.coeff_add, Finsupp.mapDomain_add, map_add, hp, hq, map_add]
      | single m c =>
        simp only [AddMonoidAlgebra.coeff_single, Finsupp.mapDomain_single,
          Finsupp.linearCombination_single, hbb]
        exact (mk_single J m c).symm
    exact this f
  have hl0 : l = 0 := by
    apply (linearIndependent_iff.1 hli) l
    rw [hl]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hf
  -- `h` factors through `M ⧸ Z`
  let h' := factorChar Z h (fun z hz => hZ z hz)
  have hev : ∀ p : AddMonoidAlgebra K M,
      evalAt ρ h p = (p.coeff.mapDomain QuotientAddGroup.mk).sum
        (fun c r => ρ r * h' (Multiplicative.ofAdd c)) := by
    intro p
    induction p using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add p q hp hq =>
      rw [map_add, hp, hq, AddMonoidAlgebra.coeff_add, Finsupp.mapDomain_add,
        Finsupp.sum_add_index'] <;> simp [add_mul]
    | single m c =>
      rw [evalAt_single]
      simp only [AddMonoidAlgebra.coeff_single, Finsupp.mapDomain_single]
      rw [Finsupp.sum_single_index (by simp)]
      rfl
  rw [hev f]
  change l.sum _ = 0
  rw [hl0, Finsupp.sum_zero_index]

end Hopf

section Units

variable {K Z₀ A M : Type*} [Field K] [AddCommGroup Z₀] [CommRing A] (𝒜 : M → AddSubgroup A)

/-- **§1, the input `hOf` of `AlgMag.ChartConclude`**: suppose `ψ : A → K[Z₀]` is surjective with
kernel `I_O`, with `Z₀` a subgroup of `M` via `i`, and that `ψ` sends degree `d` to the
span of `e_z`, `i z = d`. Then homogeneous elements outside `I_O` are units modulo `I_O`. -/
theorem exists_inv_of_homogeneous (i : Z₀ → M) (hi : Function.Injective i)
    (ψ : A →+* AddMonoidAlgebra K Z₀) (hψ : Function.Surjective ψ)
    (hdeg : ∀ d, ∀ a ∈ 𝒜 d, ∀ z, (ψ a).coeff z ≠ 0 → i z = d) {IO : Ideal A}
    (hIO : IO = RingHom.ker ψ) {d : M} {c : A} (hc : c ∈ 𝒜 d) (hcO : c ∉ IO) :
    ∃ c', c * c' - 1 ∈ IO := by
  classical
  subst hIO
  have hne : ψ c ≠ 0 := hcO
  obtain ⟨z, hz⟩ : ∃ z, (ψ c).coeff z ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hne
    ext z
    simpa using hall z
  have hsingle : ψ c = AddMonoidAlgebra.single z ((ψ c).coeff z) := by
    ext y
    by_cases hy : y = z
    · subst hy; simp
    · rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, ite_eq_right_iff.2 (fun e => absurd e (Ne.symm hy))]
      by_contra hne'
      exact hy (hi ((hdeg d c hc y hne').trans (hdeg d c hc z hz).symm))
  obtain ⟨c', hc'⟩ := hψ (AddMonoidAlgebra.single (-z) ((ψ c).coeff z)⁻¹)
  refine ⟨c', ?_⟩
  have key : ψ c * AddMonoidAlgebra.single (-z) ((ψ c).coeff z)⁻¹ = 1 := by
    have : AddMonoidAlgebra.single z ((ψ c).coeff z) *
        AddMonoidAlgebra.single (-z) ((ψ c).coeff z)⁻¹ = 1 := by
      rw [AddMonoidAlgebra.single_mul_single, add_neg_cancel, mul_inv_cancel₀ hz,
        ← AddMonoidAlgebra.one_def]
    rwa [← hsingle] at this
  rw [RingHom.mem_ker, map_sub, map_mul, hc', key, map_one, sub_self]

end Units

end AlgMag.ChartPoint

#print axioms AlgMag.ChartPoint.eval_eq_zero_of_trivial_on
#print axioms AlgMag.ChartPoint.exists_inv_of_homogeneous
