/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import TauCeti.Algebra.AlgebraicGroup.Representation.Faithful.Basic
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Weight
import TauCeti.Algebra.AlgebraicGroup.Derived.Character
import TauCeti.Algebra.AlgebraicGroup.Derived.Basic
import TauCeti.Algebra.AlgebraicGroup.Torus.Maximal
import TauCeti.Algebra.AlgebraicGroup.Torus.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Basic
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Submodule
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Matrix
import TauCeti.Algebra.Coalgebra.Subcomodule.Induced
import TauCeti.Algebra.Coalgebra.Comodule.MonoidAlgebra.Basic

/-!
# `T ∩ [C, C]` is finite for a central maximal torus `T`

Determinant argument.  Let `Q` be a Hopf algebra of finite type over `k = k̄`, `T` a maximal torus
with `T` central (every `A`-point of `Q` commutes with every `A`-point of `T`).

1. A faithful finite comodule `M` (Tau Ceti `exists_isFaithful`).
2. `M` is the direct sum of the `T`-weight spaces `M_x` (`DiagonalizableGroup.isInternal_weightSpace`).
3. **(new)** Each `M_x` is a `Q`-subcomodule: `weightSubcomodule`.  The centrality of `T` is
   used in the functional form `CentralFun`: the contractions of the coaction of `Q` commute with
   those coming from `T`.
4. The determinant of `M_x` is a group-like element, hence `det - 1 ∈ [Q, Q]`
   (`GroupLike.sub_one_mem_derivedDefiningIdeal`); it restricts to `x ^ dim M_x` on `T`.
5. So a point `t ∈ T ∩ [Q, Q]` has `χ_x(t) ^ dim M_x = 1`; finitely many values, and faithfulness
   gives finitely many points.
-/

open WithConv TauCeti TauCeti.HopfAlgebra TauCeti.Comodule
open scoped TensorProduct

namespace AlgMag.Reductive.CentralTorusFinite

universe u

/-! ### Split tori (copy of `NoTorusUnipotent.exists_split_of_torus`, which is not imported) -/

theorem exists_split_of_torus {k H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
    [Algebra.FiniteType k H] [IsAlgClosed k] (S : HopfIdeal k H)
    (hS : torusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) S)) :
    ∃ (r : ℕ) (φ : H →ₐc[k] MonoidAlgebra k (SplitTorus.characterGroup (ULift.{u} (Fin r)))),
      Function.Surjective φ ∧
        RingHom.ker (φ : H →ₐ[k] MonoidAlgebra k (SplitTorus.characterGroup (ULift.{u} (Fin r))))
          = S.toIdeal := by
  obtain ⟨r, ⟨i⟩⟩ := (splitTorusCommHopfAlgProperty_iff k _).1
    (torusCommHopfAlgProperty.split k _ hS)
  let G0 := SplitTorus.characterGroup (ULift.{u} (Fin r))
  let m : H →ₐc[k] (H ⧸ S.toIdeal) :=
    (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of k H) S).hom
  let ψ : (H ⧸ S.toIdeal) →ₐc[k] MonoidAlgebra k G0 := i.inv.hom.hom
  let ψ' : MonoidAlgebra k G0 →ₐc[k] (H ⧸ S.toIdeal) := i.hom.hom.hom
  have h1 : ∀ x, ψ' (ψ x) = x := fun x ↦ by
    exact congrArg (fun f ↦ f.hom.hom x) i.inv_hom_id
  have h2 : ∀ x, ψ (ψ' x) = x := fun x ↦ by
    exact congrArg (fun f ↦ f.hom.hom x) i.hom_inv_id
  have hm : ∀ x, m x = Ideal.Quotient.mk _ x := fun _ ↦ rfl
  refine ⟨r, ψ.comp m, fun y ↦ ?_, ?_⟩
  · obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (ψ' y)
    exact ⟨x, by simp [hm, hx, h2]⟩
  · ext x
    rw [RingHom.mem_ker]
    change ψ (m x) = 0 ↔ _
    constructor
    · intro hx
      have : m x = 0 := by rw [← h1 (m x), hx, map_zero]
      rw [hm] at this
      exact Ideal.Quotient.eq_zero_iff_mem.mp this
    · intro hx
      rw [hm, Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

/-! ### Factoring a point through a surjection -/

theorem exists_factor {k Q B : Type*} [Field k] [CommRing Q] [Algebra k Q] [CommRing B]
    [Algebra k B] (π : Q →ₐ[k] B) (hπ : Function.Surjective π) (s : Q →ₐ[k] k)
    (h : RingHom.ker π ≤ RingHom.ker s) : ∃ f : B →ₐ[k] k, f.comp π = s := by
  let eS := Ideal.quotientKerAlgEquivOfSurjective hπ
  refine ⟨(Ideal.Quotient.liftₐ (RingHom.ker π) s (fun y hy ↦ RingHom.mem_ker.mp (h hy))).comp
    eS.symm.toAlgHom, AlgHom.ext fun y ↦ ?_⟩
  have : eS.symm (π y) = Ideal.Quotient.mk _ y := by
    rw [AlgEquiv.symm_apply_eq]
    exact (Ideal.quotientKerAlgEquivOfSurjective_mk hπ y).symm
  rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, this]
  rfl

/-! ### Centrality of a torus, in tensor and in functional form -/

section Central

variable {k Q X : Type u} [Field k] [CommRing Q] [HopfAlgebra k Q] [CommMonoid X]

/-- Evaluating `g * t` and `t * g` at `Q`-tensors (`g = x ↦ x ⊗ 1`, `t = y ↦ 1 ⊗ π y`). -/
theorem central_tensor (π : Q →ₐc[k] MonoidAlgebra k X)
    (h : ∀ (A : Type u) [CommRing A] [Algebra k A] (g t : WithConv (Q →ₐ[k] A)),
      RingHom.ker (π : Q →ₐ[k] MonoidAlgebra k X) ≤ RingHom.ker (ofConv t) → g * t = t * g)
    (q : Q) :
    TensorProduct.map LinearMap.id (π : Q →ₗc[k] MonoidAlgebra k X).toLinearMap
        (Coalgebra.comul (R := k) q) =
      TensorProduct.comm k _ _
        (TensorProduct.map (π : Q →ₗc[k] MonoidAlgebra k X).toLinearMap LinearMap.id
          (Coalgebra.comul (R := k) q)) := by
  let A := Q ⊗[k] MonoidAlgebra k X
  let g : WithConv (Q →ₐ[k] A) := toConv Algebra.TensorProduct.includeLeft
  let t : WithConv (Q →ₐ[k] A) :=
    toConv ((Algebra.TensorProduct.includeRight : MonoidAlgebra k X →ₐ[k] A).comp
      (π : Q →ₐ[k] MonoidAlgebra k X))
  have ht : RingHom.ker (π : Q →ₐ[k] MonoidAlgebra k X) ≤ RingHom.ker (ofConv t) := by
    intro x hx
    rw [RingHom.mem_ker] at hx ⊢
    change Algebra.TensorProduct.includeRight (π x) = 0
    rw [show π x = 0 from hx, map_zero]
  have key := congrArg (fun f : WithConv (Q →ₐ[k] A) ↦ f.ofConv q) (h A g t ht)
  simp only [AlgHom.convMul_apply, g, t] at key
  have e1 : ∀ z : Q ⊗[k] Q,
      Algebra.TensorProduct.lift
        (Algebra.TensorProduct.includeLeft : Q →ₐ[k] A)
        ((Algebra.TensorProduct.includeRight : MonoidAlgebra k X →ₐ[k] A).comp
          (π : Q →ₐ[k] MonoidAlgebra k X)) (fun _ _ ↦ .all ..) z =
      TensorProduct.map LinearMap.id (π : Q →ₗc[k] MonoidAlgebra k X).toLinearMap z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  have e2 : ∀ z : Q ⊗[k] Q,
      Algebra.TensorProduct.lift
        ((Algebra.TensorProduct.includeRight : MonoidAlgebra k X →ₐ[k] A).comp
          (π : Q →ₐ[k] MonoidAlgebra k X))
        (Algebra.TensorProduct.includeLeft : Q →ₐ[k] A) (fun _ _ ↦ .all ..) z =
      TensorProduct.comm k _ _
        (TensorProduct.map (π : Q →ₗc[k] MonoidAlgebra k X).toLinearMap LinearMap.id z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
  rw [e1, e2] at key
  exact key

variable {V : Type*} [AddCommMonoid V] [Module k V]

/-- Functional form of the centrality of a quotient `π : Q → k[X]`: the contractions of the
coaction by a functional of `Q` and by a functional pulled back along `π` commute. -/
def CentralFun (π : Q →ₗc[k] MonoidAlgebra k X) : Prop :=
  ∀ (ψ : Module.Dual k Q) (c : Module.Dual k (MonoidAlgebra k X)),
    (c ∘ₗ π.toLinearMap) ∘ₗ LinearMap.tensorComponent ψ ∘ₗ Coalgebra.comul =
      ψ ∘ₗ LinearMap.tensorComponent (c ∘ₗ π.toLinearMap) ∘ₗ Coalgebra.comul

theorem centralFun_of_tensor (π : Q →ₐc[k] MonoidAlgebra k X)
    (hc : ∀ q : Q,
      TensorProduct.map LinearMap.id (π : Q →ₗc[k] MonoidAlgebra k X).toLinearMap
          (Coalgebra.comul (R := k) q) =
        TensorProduct.comm k _ _
          (TensorProduct.map (π : Q →ₗc[k] MonoidAlgebra k X).toLinearMap LinearMap.id
            (Coalgebra.comul (R := k) q))) :
    CentralFun (π : Q →ₗc[k] MonoidAlgebra k X) := by
  intro ψ c
  let Φ : Q ⊗[k] MonoidAlgebra k X →ₗ[k] k :=
    LinearMap.mul' k k ∘ₗ TensorProduct.map ψ c
  have h1 : ∀ z : Q ⊗[k] Q,
      ψ (LinearMap.tensorComponent (c ∘ₗ (π : Q →ₗc[k] MonoidAlgebra k X).toLinearMap) z) =
        Φ (TensorProduct.map LinearMap.id (π : Q →ₗc[k] MonoidAlgebra k X).toLinearMap z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Φ, mul_comm]
    | add a b ha hb => rw [map_add, map_add, map_add, map_add, ha, hb]
  have h2 : ∀ z : Q ⊗[k] Q,
      (c ∘ₗ (π : Q →ₗc[k] MonoidAlgebra k X).toLinearMap)
          (LinearMap.tensorComponent ψ z) =
        Φ (TensorProduct.comm k _ _
          (TensorProduct.map (π : Q →ₗc[k] MonoidAlgebra k X).toLinearMap LinearMap.id z)) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Φ]
    | add a b ha hb => rw [map_add, map_add, map_add, map_add, map_add, ha, hb]
  ext q
  have h := h2 (Coalgebra.comul q)
  rw [← hc q, ← h1] at h
  exact h

end Central

/-! ### Weight spaces of a central torus are subcomodules -/

section WeightSub

variable {k Q X : Type u} [Field k] [CommRing Q] [HopfAlgebra k Q] [CommMonoid X]
variable {M : Type u} [AddCommGroup M] [Module k M] [Comodule k Q M]

omit [CommMonoid X] in
theorem tensorComponent_map_coact (π : Q →ₗc[k] MonoidAlgebra k X)
    (c : Module.Dual k (MonoidAlgebra k X)) (v : M) :
    LinearMap.tensorComponent c
        (TensorProduct.map LinearMap.id π.toLinearMap (Comodule.coact (R := k) (C := Q) v)) =
      Comodule.coactComponent (R := k) (C := Q) (c ∘ₗ π.toLinearMap) v := by
  rw [LinearMap.tensorComponent_map, Comodule.coactComponent_apply]
  rfl

omit [CommMonoid X] in
/-- Weight vectors, in terms of contractions of the coaction. -/
theorem mem_weightSpace_iff_coactComponent (π : Q →ₗc[k] MonoidAlgebra k X) (x : X) (v : M) :
    v ∈ DiagonalizableGroup.weightSpace M π x ↔
      ∀ c : Module.Dual k (MonoidAlgebra k X),
        Comodule.coactComponent (R := k) (C := Q) (c ∘ₗ π.toLinearMap) v =
          c (MonoidAlgebra.single x 1) • v := by
  rw [DiagonalizableGroup.mem_weightSpace]
  constructor
  · intro h c
    rw [← tensorComponent_map_coact, h, LinearMap.tensorComponent_tmul]
  · intro h
    apply TensorProduct.tensor_eq_of_forall_tensorComponent_eq
    intro c
    rw [tensorComponent_map_coact, h c, LinearMap.tensorComponent_tmul]

omit [CommMonoid X] in
/-- For a central `π`, the weight spaces are stable under all contractions of the coaction. -/
theorem coactComponent_mem_weightSpace {π : Q →ₗc[k] MonoidAlgebra k X} (hπ : CentralFun π)
    {x : X} (f : Module.Dual k Q) {v : M} (hv : v ∈ DiagonalizableGroup.weightSpace M π x) :
    Comodule.coactComponent (R := k) (C := Q) f v ∈ DiagonalizableGroup.weightSpace M π x := by
  rw [mem_weightSpace_iff_coactComponent] at hv ⊢
  intro c
  rw [Comodule.coactComponent_coactComponent, hπ f c, ← Comodule.coactComponent_coactComponent,
    hv c, map_smul]

/-- The weight subcomodule of a central `π`. -/
noncomputable def weightSubcomodule {π : Q →ₗc[k] MonoidAlgebra k X} (hπ : CentralFun π) (x : X) :
    Subcomodule k Q M where
  carrier := DiagonalizableGroup.weightSpace M π x
  coact_mem' _ hm := Submodule.coact_mem_range_of_forall_coactComponent_mem _
    (fun f _ h ↦ coactComponent_mem_weightSpace hπ f h) hm

theorem coe_coactComponent_subcomodule (N : Subcomodule k Q M) (φ : Module.Dual k Q) (w : N) :
    ((Comodule.coactComponent (R := k) (C := Q) φ w : N) : M) =
      Comodule.coactComponent (R := k) (C := Q) φ (w : M) := by
  rw [Comodule.coactComponent_apply, Comodule.coactComponent_apply,
    ← Subcomodule.subtype_rTensor_coact, LinearMap.rTensor_def, LinearMap.tensorComponent_map,
    LinearMap.comp_id]
  rfl

omit [CommMonoid X] in
/-- Every vector of the weight subcomodule is a weight vector of it. -/
theorem mem_weightSpace_weightSubcomodule {π : Q →ₗc[k] MonoidAlgebra k X} (hπ : CentralFun π)
    (x : X) (w : weightSubcomodule (M := M) hπ x) :
    w ∈ DiagonalizableGroup.weightSpace (weightSubcomodule (M := M) hπ x) π x := by
  rw [mem_weightSpace_iff_coactComponent]
  intro c
  apply Subtype.ext
  rw [coe_coactComponent_subcomodule]
  exact (mem_weightSpace_iff_coactComponent π x (w : M)).mp w.2 c

end WeightSub

/-! ### Finiteness of `T ∩ [Q, Q]` -/

section Finite

variable {k Q : Type u} [Field k] [IsAlgClosed k] [CommRing Q] [HopfAlgebra k Q]
  [Algebra.FiniteType k Q]

/-- **(b)**: for a central torus `T` of `Q`, the points of `T ∩ [Q, Q]` form a finite set. -/
theorem finite_torus_inter_derived_of_central {T : HopfIdeal k Q}
    (hT : torusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k Q) T))
    (hcent : ∀ (A : Type u) [CommRing A] [Algebra k A] (g t : WithConv (Q →ₐ[k] A)),
      T.toIdeal ≤ RingHom.ker (ofConv t) → g * t = t * g) :
    {t : WithConv (Q →ₐ[k] k) | T.toIdeal ≤ RingHom.ker t.ofConv ∧
      (TauCeti.CommHopfAlgCat.derivedDefiningIdeal (R := k) Q).toIdeal ≤
        RingHom.ker t.ofConv}.Finite := by
  obtain ⟨r, πT, hπT, hkT⟩ := exists_split_of_torus T hT
  let X := SplitTorus.characterGroup (ULift.{u} (Fin r))
  let π0 : Q →ₐ[k] MonoidAlgebra k X := (πT : Q →ₐ[k] MonoidAlgebra k X)
  let πc : Q →ₗc[k] MonoidAlgebra k X := (πT : Q →ₗc[k] MonoidAlgebra k X)
  have hCF : CentralFun πc := centralFun_of_tensor πT (central_tensor πT
    (fun A _ _ g t h ↦ hcent A g t (hkT ▸ h)))
  obtain ⟨M0, hM⟩ := Comodule.exists_isFaithful (k := k) (H := Q)
  let M : Type u := M0
  let _ : AddCommGroup M := Module.addCommMonoidToAddCommGroup k
  let F : Set X := {x | DiagonalizableGroup.weightSpace M πc x ≠ ⊥}
  have hF : F.Finite := DiagonalizableGroup.finite_setOf_weightSpace_ne_bot M πc
  have : Finite F := hF.to_subtype
  -- determinants of the weight subcomodules
  let N : X → Subcomodule k Q M := fun x ↦ weightSubcomodule hCF x
  let d : X → ℕ := fun x ↦ Module.finrank k (N x)
  let c : X → Q := fun x ↦
    (Comodule.coefficientMatrix (C := Q) (Module.finBasis k (N x))).det
  have hcg : ∀ x, IsGroupLikeElem k (c x) := fun x ↦
    Comodule.isGroupLikeElem_det_coefficientMatrix _
  have hcπ : ∀ x, π0 (c x) = MonoidAlgebra.single (x ^ d x) 1 := fun x ↦ by
    have h := DiagonalizableGroup.map_det_coefficientMatrix_of_forall_mem_weightSpace πT
      (mem_weightSpace_weightSubcomodule hCF x) (Module.finBasis k (N x))
    rw [Fintype.card_fin] at h
    exact h
  have hdpos : ∀ x ∈ F, 0 < d x := by
    intro x hx
    apply Nat.pos_of_ne_zero
    intro h0
    apply hx
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hs : Subsingleton (N x) := Module.finrank_zero_iff.mp h0
    have := congrArg Subtype.val (hs.elim (⟨v, hv⟩ : N x) 0)
    exact this
  -- lifts of the characters
  choose f hf0 using fun x : X ↦ hπT (MonoidAlgebra.single x (1 : k))
  have hf : ∀ x, π0 (f x) = MonoidAlgebra.single x 1 := hf0
  set S := {t : WithConv (Q →ₐ[k] k) | T.toIdeal ≤ RingHom.ker t.ofConv ∧
      (TauCeti.CommHopfAlgCat.derivedDefiningIdeal (R := k) Q).toIdeal ≤ RingHom.ker t.ofConv}
  have hfac : ∀ t ∈ S, ∃ tb : MonoidAlgebra k X →ₐ[k] k, tb.comp π0 = t.ofConv := by
    rintro t ⟨htT, -⟩
    exact exists_factor π0 hπT t.ofConv (by
      change RingHom.ker π0 ≤ _
      rw [show RingHom.ker π0 = T.toIdeal from hkT]
      exact htT)
  let Φ : WithConv (Q →ₐ[k] k) → (F → k) := fun t x ↦ t.ofConv (f x)
  have hroot : ∀ t ∈ S, ∀ x : F, Φ t x ^ d x = 1 := by
    intro t ht x
    obtain ⟨tb, htb⟩ := hfac t ht
    have hc1 : t.ofConv (c x) = 1 := by
      have hmem := ht.2 (HopfIdeal.mem_toIdeal.mpr (GroupLike.sub_one_mem_derivedDefiningIdeal
        ⟨c x, hcg x⟩))
      rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at hmem
      exact hmem
    change t.ofConv (f x) ^ d x = 1
    rw [← htb, AlgHom.comp_apply, hf x, ← map_pow, MonoidAlgebra.single_pow, one_pow, ← hcπ x,
      ← AlgHom.comp_apply, htb, hc1]
  have hinj : Set.InjOn Φ S := by
    intro t ht t' ht' htt'
    obtain ⟨tb, htb⟩ := hfac t ht
    obtain ⟨tb', htb'⟩ := hfac t' ht'
    have hval : ∀ x ∈ F, tb (MonoidAlgebra.single x 1) = tb' (MonoidAlgebra.single x 1) := by
      intro x hx
      have h := congrFun htt' ⟨x, hx⟩
      change t.ofConv (f x) = t'.ofConv (f x) at h
      rw [← htb, ← htb', AlgHom.comp_apply, AlgHom.comp_apply, hf x] at h
      exact h
    apply Comodule.pointsAction_injective_of_isFaithful (K := k) hM
    apply LinearEquiv.toLinearMap_injective
    rw [Comodule.pointsAction_toLinearMap, Comodule.pointsAction_toLinearMap, ← htb, ← htb']
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, ha, hb]
    | tmul a v =>
      have hv : v ∈ ⨆ x, DiagonalizableGroup.weightSpace M πc x := by
        let _ : DecidableEq X := Classical.decEq _
        rw [(DiagonalizableGroup.isInternal_weightSpace M πc).submodule_iSup_eq_top]
        exact Submodule.mem_top
      induction hv using Submodule.iSup_induction' with
      | mem x v hv =>
        rw [DiagonalizableGroup.endOfPoint_tmul_of_mem_weightSpace M πT tb a hv,
          DiagonalizableGroup.endOfPoint_tmul_of_mem_weightSpace M πT tb' a hv]
        by_cases hx : x ∈ F
        · rw [hval x hx]
        · have : v = 0 := by
            have h0 : DiagonalizableGroup.weightSpace M πc x = ⊥ := not_not.mp hx
            rw [h0] at hv
            exact (Submodule.mem_bot k).mp hv
          simp [this]
      | zero => simp
      | add v w _ _ hv hw => rw [TensorProduct.tmul_add, map_add, map_add, hv, hw]
  have himg : (Φ '' S).Finite := by
    classical
    refine (Set.Finite.pi (t := fun x : F ↦ ((Polynomial.nthRoots (d x) (1 : k)).toFinset : Set k))
      fun x ↦ Finset.finite_toSet _).subset ?_
    rintro _ ⟨t, ht, rfl⟩ x -
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    exact (Polynomial.mem_nthRoots (hdpos x x.2)).mpr (hroot t ht x)
  exact himg.of_finite_image hinj

/-- **`hfin`** in the form used by `NoTorusUnipotent.cSolvable_of_centralTorus`. -/
theorem hfin {T : HopfIdeal k Q} (hT : HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k Q) T)
    (hcent : ∀ (A : Type u) [CommRing A] [Algebra k A] (g t : WithConv (Q →ₐ[k] A)),
      T.toIdeal ≤ RingHom.ker (ofConv t) → g * t = t * g) :
    {t : WithConv (Q →ₐ[k] k) | T.toIdeal ≤ RingHom.ker t.ofConv ∧
      (TauCeti.CommHopfAlgCat.derivedDefiningIdeal (R := k) Q).toIdeal ≤
        RingHom.ker t.ofConv}.Finite :=
  finite_torus_inter_derived_of_central hT.1 hcent

end Finite

#print axioms hfin

end AlgMag.Reductive.CentralTorusFinite
