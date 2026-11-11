/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.TorusConjDyn
import AlgMag.Reductive.TorusImage
import TauCeti.Algebra.AlgebraicGroup.Torus.AlgebraicallyClosed
import TauCeti.Algebra.Bialgebra.MonoidAlgebra.GroupLike

/-!
# `limit_mem_torus'`: the Levi limit of a torus point lies in `T`

Notes: `equivalence-reductive/lean-torusimage.md`.

Proof. Split `S` and `T` (`k = k̄`): `π_S : H ↠ k[X]`, `π_T : H ↠ k[Y]`. With `L` the Levi
retraction (`leviRetractionBialgHom`), the Hopf maps `a = ι₁ ∘ π_S ∘ L` and `b = ι₂ ∘ π_T` into
`k[X × Y]` commute (`DynHyp.hcent`: `L` lands in the Levi, which centralizes `T`), so
`ψ = a * b` is a Hopf map (`commMul`), i.e. `lim(S) · T` is a closed subgroup, and its ideal
`ker ψ` is a torus (`torus_quotient_ker`, the image of the torus `D(X × Y)`). It contains `T`
(project to `k[Y]`), so equals `T` by maximality; evaluating `ψ` at the point `(s̄, 1)` gives
`s ∘ L = lim(s)`, which therefore kills `T`.
-/

open TensorProduct Magnetism TauCeti TauCeti.Cocharacter WithConv

namespace AlgMag.Reductive

universe u

section Helpers

variable {k : Type u} [Field k]

/-- `mapDomain` of the trivial homomorphism is `algebraMap ∘ ε`. -/
lemma mapDomainBialgHom_one_eq {M N : Type u} [CommMonoid M] [CommMonoid N] :
    ((MonoidAlgebra.mapDomainBialgHom k (1 : M →* N) : MonoidAlgebra k M →ₐc[k] _) :
        MonoidAlgebra k M →ₐ[k] MonoidAlgebra k N) =
      (Algebra.ofId k _).comp (Bialgebra.counitAlgHom k (MonoidAlgebra k M)) := by
  refine MonoidAlgebra.algHom_ext (fun m ↦ ?_) (Subsingleton.elim _ _)
  simp

end Helpers

section Dyn

variable {k : Type u} [Field k] {H : Type u} [CommRing H] [HopfAlgebra k H] [DecidableEq H]
variable [Algebra.FiniteType k H] [Algebra.Smooth k H]
variable (l : H →ₐc[k] LaurentPolynomial k)

omit [DecidableEq H] [Algebra.Smooth k H] in
/-- **Tori over `k = k̄` are split**, with the explicit character group `ℤ^r`
(the proof of `TuStep.exists_split_of_isMaximalTorus`, with the group made explicit). -/
theorem exists_split_explicit [IsAlgClosed k] (S : HopfIdeal k H)
    (hS : HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) S) :
    ∃ (r : ℕ) (φ : H →ₐc[k] MonoidAlgebra k (SplitTorus.characterGroup (ULift.{u} (Fin r)))),
      Function.Surjective φ ∧
        RingHom.ker (φ : H →ₐ[k] MonoidAlgebra k (SplitTorus.characterGroup (ULift.{u} (Fin r))))
          = S.toIdeal := by
  obtain ⟨r, ⟨i⟩⟩ := (splitTorusCommHopfAlgProperty_iff k _).1
    (torusCommHopfAlgProperty.split k _ hS.1)
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

omit [DecidableEq H] [Algebra.FiniteType k H] [Algebra.Smooth k H] in
/-- Every point composed with the Levi retraction kills the Levi ideal. -/
lemma leviDefiningHopfIdeal_le_ker_comp (hP : parabolicDefiningHopfIdeal l = ⊥) (A : Type u)
    [CommRing A] [Algebra k A] (q : WithConv (H →ₐ[k] A)) :
    (leviDefiningHopfIdeal l).toIdeal ≤ RingHom.ker (q.ofConv.comp (leviRetraction l hP)) := by
  intro x hx
  have hq := limit_mem_levi (A := A) (l := l) ⟨q, mem_parabolic_of_eq_bot l hP q⟩
  rw [limit_eq_comp_leviRetraction l hP,
    ← quotientPointsSubgroup_leviDefiningHopfIdeal l (CommAlgCat.of k A)] at hq
  exact (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mp hq x
    (HopfIdeal.mem_toIdeal.mp hx)

/-- **(T1b) geometric core**, same statement as `TorusConjDyn.limit_mem_torus`. -/
theorem limit_mem_torus' [IsAlgClosed k] {T : HopfIdeal k H} (h : DynHyp l T)
    (S : HopfIdeal k H) (hS : HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) S)
    (s : WithConv (H →ₐ[k] k)) (hs : S.toIdeal ≤ RingHom.ker s.ofConv) (hsP : s ∈ parabolic k l) :
    T.toIdeal ≤ RingHom.ker (limit k l ⟨s, hsP⟩).ofConv := by
  classical
  obtain ⟨r, πS, hπS, hkS⟩ := exists_split_explicit S hS
  obtain ⟨r', πT, hπT, hkT⟩ := exists_split_explicit T h.hT
  let X := SplitTorus.characterGroup (ULift.{u} (Fin r))
  let Y := SplitTorus.characterGroup (ULift.{u} (Fin r'))
  let C := MonoidAlgebra k (X × Y)
  let ι1 : MonoidAlgebra k X →ₐc[k] C := MonoidAlgebra.mapDomainBialgHom k (MonoidHom.inl X Y)
  let ι2 : MonoidAlgebra k Y →ₐc[k] C := MonoidAlgebra.mapDomainBialgHom k (MonoidHom.inr X Y)
  let p1 : C →ₐc[k] MonoidAlgebra k X := MonoidAlgebra.mapDomainBialgHom k (MonoidHom.fst X Y)
  let p2 : C →ₐc[k] MonoidAlgebra k Y := MonoidAlgebra.mapDomainBialgHom k (MonoidHom.snd X Y)
  let Lb := leviRetractionBialgHom l h.hP
  let a : H →ₐc[k] C := (ι1.comp πS).comp Lb
  let b : H →ₐc[k] C := ι2.comp πT
  have hab : Commute
      (toConv ((Algebra.TensorProduct.includeRight : C →ₐ[k] C ⊗[k] C).comp (a : H →ₐ[k] C)))
      (toConv ((Algebra.TensorProduct.includeLeft : C →ₐ[k] C ⊗[k] C).comp (b : H →ₐ[k] C))) := by
    refine h.hcent (C ⊗[k] C) _ _ ?_ ?_
    · exact leviDefiningHopfIdeal_le_ker_comp l h.hP (C ⊗[k] C)
        (toConv ((Algebra.TensorProduct.includeRight : C →ₐ[k] C ⊗[k] C).comp
          ((ι1.comp πS : H →ₐc[k] C) : H →ₐ[k] C)))
    · intro x hx
      rw [← hkT] at hx
      have hx' : πT x = 0 := hx
      simp [b, hx']
  let ψ := commMul a b hab
  have hconv : ∀ (D : Type u) [CommRing D] [Algebra k D] (φ : C →ₐ[k] D),
      toConv (φ.comp (ψ : H →ₐ[k] C)) =
        toConv (φ.comp (a : H →ₐ[k] C)) * toConv (φ.comp (b : H →ₐ[k] C)) := fun D _ _ φ ↦ by
    rw [coe_commMul, AlgHom.comp_convMul_distrib, toConv_ofConv, ofConv_toConv, ofConv_toConv]
  -- the closed subgroup `lim(S) · T` is a torus
  have htor := torus_quotient_ker (H := H) (C := C)
    (TauCeti.MonoidAlgebra.groupLikeSetSpan_eq_top (R := k) (X × Y)) ψ
  -- it contains `T`: project to `k[Y]`
  have hp2a : toConv ((p2 : C →ₐ[k] MonoidAlgebra k Y).comp (a : H →ₐ[k] C)) = 1 := by
    have e : (p2 : C →ₐ[k] MonoidAlgebra k Y).comp (a : H →ₐ[k] C) =
        ((MonoidAlgebra.mapDomainBialgHom k (1 : X →* Y) : MonoidAlgebra k X →ₐc[k] _) :
          MonoidAlgebra k X →ₐ[k] _).comp ((πS.comp Lb : H →ₐc[k] _) : H →ₐ[k] _) := by
      refine AlgHom.ext fun x ↦ ?_
      change p2 (ι1 (πS (Lb x))) = MonoidAlgebra.mapDomainBialgHom k (1 : X →* Y) (πS (Lb x))
      rw [MonoidAlgebra.mapDomainBialgHom_mapDomainBialgHom, MonoidHom.snd_comp_inl]
    rw [e, mapDomainBialgHom_one_eq, AlgHom.comp_assoc, counitAlgHom_comp_bialgHom',
      AlgHom.convOne_def]
  have hp2b : (p2 : C →ₐ[k] MonoidAlgebra k Y).comp (b : H →ₐ[k] C) = (πT : H →ₐ[k] _) := by
    refine AlgHom.ext fun x ↦ ?_
    change p2 (ι2 (πT x)) = πT x
    rw [MonoidAlgebra.mapDomainBialgHom_mapDomainBialgHom, MonoidHom.snd_comp_inr,
      MonoidAlgebra.mapDomainBialgHom_id]
    rfl
  have hKT : HopfIdeal.ker ψ ≤ T := by
    intro x hx
    rw [HopfIdeal.mem_ker] at hx
    have e := congrArg (fun f : WithConv (H →ₐ[k] MonoidAlgebra k Y) ↦ f.ofConv x)
      (hconv _ (p2 : C →ₐ[k] MonoidAlgebra k Y))
    simp only [hp2a, hp2b, one_mul, ofConv_toConv, AlgHom.comp_apply] at e
    rw [← HopfIdeal.mem_toIdeal, ← hkT, RingHom.mem_ker]
    change πT x = 0
    refine e.symm.trans ?_
    change (p2 : C →ₐ[k] MonoidAlgebra k Y) (ψ x) = 0
    rw [hx, map_zero]
  have hTK : T ≤ HopfIdeal.ker ψ := h.hT.2 htor hKT
  -- evaluate at the point `(s̄, 1)`
  have hπS' : Function.Surjective (πS : H →ₐ[k] MonoidAlgebra k X) := hπS
  let eS := Ideal.quotientKerAlgEquivOfSurjective hπS'
  let sbar : MonoidAlgebra k X →ₐ[k] k :=
    (Ideal.Quotient.liftₐ (RingHom.ker (πS : H →ₐ[k] MonoidAlgebra k X)) s.ofConv
      (fun y hy ↦ RingHom.mem_ker.mp (hs (hkS ▸ hy)))).comp eS.symm.toAlgHom
  have hsbar : ∀ y, sbar (πS y) = s.ofConv y := fun y ↦ by
    have : eS.symm (πS y) = Ideal.Quotient.mk _ y := by
      rw [AlgEquiv.symm_apply_eq]
      exact (Ideal.quotientKerAlgEquivOfSurjective_mk hπS' y).symm
    dsimp only [sbar]
    rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, this]
    rfl
  let z : C →ₐ[k] k := sbar.comp (p1 : C →ₐ[k] MonoidAlgebra k X)
  have hza : toConv (z.comp (a : H →ₐ[k] C)) = toConv (s.ofConv.comp (leviRetraction l h.hP)) := by
    refine WithConv.ext (AlgHom.ext fun x ↦ ?_)
    change sbar (p1 (ι1 (πS (Lb x)))) = s.ofConv (leviRetraction l h.hP x)
    rw [MonoidAlgebra.mapDomainBialgHom_mapDomainBialgHom, MonoidHom.fst_comp_inl,
      MonoidAlgebra.mapDomainBialgHom_id]
    exact hsbar _
  have hzb : toConv (z.comp (b : H →ₐ[k] C)) = 1 := by
    have e : z.comp (b : H →ₐ[k] C) = sbar.comp
        (((MonoidAlgebra.mapDomainBialgHom k (1 : Y →* X) : MonoidAlgebra k Y →ₐc[k] _) :
          MonoidAlgebra k Y →ₐ[k] _).comp (πT : H →ₐ[k] _)) := by
      refine AlgHom.ext fun x ↦ ?_
      change sbar (p1 (ι2 (πT x))) = sbar (MonoidAlgebra.mapDomainBialgHom k (1 : Y →* X) (πT x))
      rw [MonoidAlgebra.mapDomainBialgHom_mapDomainBialgHom, MonoidHom.fst_comp_inr]
    rw [e, mapDomainBialgHom_one_eq, ← AlgHom.comp_assoc, ← AlgHom.comp_assoc,
      show sbar.comp (Algebra.ofId k (MonoidAlgebra k X)) = Algebra.ofId k k from
        Subsingleton.elim _ _, AlgHom.comp_assoc, counitAlgHom_comp_bialgHom', AlgHom.convOne_def]
  intro x hx
  have hxK : ψ x = 0 := (HopfIdeal.mem_ker ψ).mp (hTK (HopfIdeal.mem_toIdeal.mp hx))
  rw [RingHom.mem_ker, limit_eq_comp_leviRetraction l h.hP, ofConv_toConv]
  have e := congrArg (fun f : WithConv (H →ₐ[k] k) ↦ f.ofConv x) (hconv k z)
  simp only [hza, hzb, mul_one, ofConv_toConv, AlgHom.comp_apply] at e
  change s.ofConv (leviRetraction l h.hP x) = 0
  refine e.symm.trans ?_
  change z (ψ x) = 0
  rw [hxK, map_zero]

end Dyn

end AlgMag.Reductive
