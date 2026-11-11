/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import TauCeti.Algebra.Coalgebra.Subcoalgebra.GroupLike
import Mathlib.RingTheory.Flat.Basic
import TauCeti.Algebra.AlgebraicGroup.Torus.Characterization
import TauCeti.Algebra.AlgebraicGroup.Torus.Maximal
import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Kernel
import TauCeti.Algebra.AlgebraicGroup.Dynamic.Representability
import TauCeti.Algebra.AlgebraicGroup.Dynamic.Levi.Representability

/-!
# Images of tori (infrastructure for `limit_mem_torus`)

Notes: `equivalence-reductive/lean-torusimage.md`.

1. `groupLikeSetSpan_eq_top_of_injective`: a coalgebra injecting into a coalgebra spanned by
   group-like elements is itself spanned by group-like elements (over a field).
-/

open TensorProduct TauCeti WithConv

namespace AlgMag.Reductive

universe u v w

section GroupLike

variable {k : Type u} [Field k] {Q : Type v} {C : Type w}
  [AddCommGroup Q] [Module k Q] [Coalgebra k Q] [AddCommGroup C] [Module k C] [Coalgebra k C]

/-- The coefficient-extraction map `c ↦ (b.coord g ⊗ id)(Δ c)` on a group-like basis is
`c ↦ b.coord g c • g`. -/
lemma lid_map_coord_comul (hC : Subcoalgebra.groupLikeSetSpan (R := k) (C := C) Set.univ = ⊤)
    (g : GroupLike k C) (c : C) :
    TensorProduct.lid k C (TensorProduct.map ((Subcoalgebra.groupLikeBasis hC).coord g)
      LinearMap.id (Coalgebra.comul (R := k) c)) =
      (Subcoalgebra.groupLikeBasis hC).coord g c • (g : C) := by
  classical
  set b := Subcoalgebra.groupLikeBasis hC
  have : ((TensorProduct.lid k C).toLinearMap ∘ₗ TensorProduct.map (b.coord g) LinearMap.id ∘ₗ
      Coalgebra.comul (R := k) (A := C)) = (LinearMap.smulRight (b.coord g) (g : C)) := by
    refine b.ext fun g' ↦ ?_
    have hb := Subcoalgebra.groupLikeBasis_apply hC g'
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearMap.smulRight_apply]
    rw [hb, g'.isGroupLikeElem_val.comul_eq_tmul_self, TensorProduct.map_tmul,
      TensorProduct.lid_tmul, LinearMap.id_apply, ← hb, Module.Basis.coord_apply,
      Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs with h
    · subst h; simp [hb]
    · simp
  exact congrArg (fun φ : C →ₗ[k] C ↦ φ c) this

/-- **(1) Group-like spanning passes to subcoalgebras.** Over a field, a coalgebra `Q` with an
injective coalgebra map into a coalgebra spanned by its group-like elements is spanned by its own
group-like elements. -/
theorem groupLikeSetSpan_eq_top_of_injective (f : Q →ₗc[k] C) (hf : Function.Injective f)
    (hC : Subcoalgebra.groupLikeSetSpan (R := k) (C := C) Set.univ = ⊤) :
    Subcoalgebra.groupLikeSetSpan (R := k) (C := Q) Set.univ = ⊤ := by
  set b := Subcoalgebra.groupLikeBasis hC
  rw [Subcoalgebra.groupLikeSetSpan_eq_top_iff_span_eq_top]
  have hff : Function.Injective (TensorProduct.map (f : Q →ₗ[k] C) (f : Q →ₗ[k] C)) :=
    TensorProduct.map_injective_of_flat_flat _ _ hf hf
  -- every basis vector in the support of `f q` is the image of a group-like of `Q`
  have key : ∀ (q : Q) (g : GroupLike k C), b.coord g (f q) ≠ 0 →
      (g : C) ∈ Set.range (fun y : GroupLike k Q ↦ f y.val) := by
    intro q g hg
    set Φ' : Q →ₗ[k] Q := (TensorProduct.lid k Q).toLinearMap ∘ₗ
      TensorProduct.map (b.coord g ∘ₗ (f : Q →ₗ[k] C)) LinearMap.id ∘ₗ Coalgebra.comul
    have hΦ : b.coord g (f q) • (g : C) = f (Φ' q) := by
      rw [← lid_map_coord_comul hC g (f q), ← CoalgHomClass.map_comp_comul_apply]
      simp only [Φ', LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
      induction Coalgebra.comul (R := k) q using TensorProduct.induction_on with
      | zero => simp
      | tmul a a' => simp; rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    set c := b.coord g (f q)
    set y := c⁻¹ • Φ' q
    have hy : f y = g := by
      simp only [y, map_smul, ← hΦ, smul_smul, inv_mul_cancel₀ hg, one_smul]
    have hgl : IsGroupLikeElem k y := by
      refine ⟨?_, hff ?_⟩
      · rw [← CoalgHomClass.counit_comp_apply f y, hy]
        exact g.isGroupLikeElem_val.counit_eq_one
      · change TensorProduct.map (f : Q →ₗ[k] C) (f : Q →ₗ[k] C) (Coalgebra.comul y) = _
        rw [CoalgHomClass.map_comp_comul_apply, TensorProduct.map_tmul]
        change Coalgebra.comul (f y) = f y ⊗ₜ f y
        rw [hy]
        exact g.isGroupLikeElem_val.comul_eq_tmul_self
    exact ⟨⟨y, hgl⟩, hy⟩
  refine top_unique fun q _ ↦ ?_
  have hq : f q ∈ Submodule.map (f : Q →ₗ[k] C)
      (Submodule.span k (Set.range (GroupLike.val (R := k) (A := Q)))) := by
    rw [Submodule.map_span]
    refine Submodule.span_mono ?_ (b.mem_span_repr_support (f q))
    rintro _ ⟨g, hg, rfl⟩
    rw [Finset.mem_coe, Finsupp.mem_support_iff, ← Module.Basis.coord_apply] at hg
    obtain ⟨y, hy⟩ := key q g hg
    exact ⟨y.val, ⟨y, rfl⟩, (hy.trans (Subcoalgebra.groupLikeBasis_apply hC g).symm :)⟩
  obtain ⟨q', hq', hqq⟩ := hq
  rwa [hf hqq] at hq'

end GroupLike

section Image

variable {k : Type u} [Field k] {H : Type u} [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] {C : Type u} [CommRing C] [HopfAlgebra k C]

/-- **(2) The image of a torus is a torus** (in the form used downstream): over `k = k̄`, the
kernel of a Hopf map `f : H → C` into a domain spanned by group-like elements (e.g. the group
algebra of a finitely generated free abelian group, a split torus) cuts out a torus. -/
theorem torus_quotient_ker [IsAlgClosed k] [IsDomain C]
    (hC : Subcoalgebra.groupLikeSetSpan (R := k) (C := C) Set.univ = ⊤) (f : H →ₐc[k] C) :
    torusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient
        ⟨_root_.CommHopfAlgCat.of k H, (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
        (HopfIdeal.ker f : HopfIdeal k H)) := by
  set g : H ⧸ (HopfIdeal.ker f : HopfIdeal k H).toIdeal →ₐc[k] C :=
    Bialgebra.Quotient.liftBialgHom (HopfIdeal.ker f : HopfIdeal k H).toIdeal f
      (by rw [HopfIdeal.ker_toIdeal]; exact le_rfl)
  have hg : Function.Injective g := by
    refine (injective_iff_map_eq_zero g).2 fun q hq ↦ ?_
    obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [Ideal.Quotient.eq_zero_iff_mem, HopfIdeal.mem_toIdeal, HopfIdeal.mem_ker]
    simpa [g] using hq
  have : IsDomain (H ⧸ (HopfIdeal.ker f : HopfIdeal k H).toIdeal) :=
    Function.Injective.isDomain (g : H ⧸ _ →+* C) hg
  have : ConnectedSpace (PrimeSpectrum (H ⧸ (HopfIdeal.ker f : HopfIdeal k H).toIdeal)) :=
    connectedSpace_iff_univ.mpr (IrreducibleSpace.isIrreducible_univ _).isConnected
  exact torusCommHopfAlgProperty.of_groupLikeSetSpan_eq_top _
    (groupLikeSetSpan_eq_top_of_injective (g : _ →ₗc[k] C) hg hC)

end Image

section CommMul

variable {k : Type u} [Field k] {H C : Type u} [CommRing H] [Bialgebra k H] [CommRing C]
  [Bialgebra k C]

/-- The convolution of the two tensor-factor embeddings is the tensor map composed with `Δ`. -/
lemma convMul_include (φ ψ : H →ₐ[k] C) :
    toConv ((Algebra.TensorProduct.includeLeft : C →ₐ[k] C ⊗[k] C).comp φ) *
      toConv ((Algebra.TensorProduct.includeRight : C →ₐ[k] C ⊗[k] C).comp ψ) =
      toConv ((Algebra.TensorProduct.map φ ψ).comp (Bialgebra.comulAlgHom k H)) := by
  rw [AlgHom.convMul_def]
  congr 1
  rw [← AlgHom.comp_assoc]
  congr 1
  refine Algebra.TensorProduct.ext' fun a b ↦ ?_
  simp

/-- A coalgebra map intertwines the comultiplications, as algebra maps. -/
lemma comulAlgHom_comp_bialgHom (a : H →ₐc[k] C) :
    (Bialgebra.comulAlgHom k C).comp (a : H →ₐ[k] C) =
      (Algebra.TensorProduct.map (a : H →ₐ[k] C) a).comp (Bialgebra.comulAlgHom k H) := by
  ext x
  simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, BialgHom.coe_toAlgHom]
  exact (CoalgHomClass.map_comp_comul_apply a x).symm

lemma counitAlgHom_comp_bialgHom' (a : H →ₐc[k] C) :
    (Bialgebra.counitAlgHom k C).comp (a : H →ₐ[k] C) = Bialgebra.counitAlgHom k H := by
  ext x
  simp

/-- **(4) Product of two commuting homomorphisms.** If `a, b : H → C` are Hopf maps whose points
commute (in the universal form: `a` on the right factor commutes with `b` on the left factor of
`C ⊗ C`), the pointwise product `a * b` is again a Hopf map. Geometrically: the multiplication
`D₁ × D₂ → G` of two commuting closed subgroups is a homomorphism; its image is the product. -/
noncomputable def commMul (a b : H →ₐc[k] C)
    (hab : Commute (toConv ((Algebra.TensorProduct.includeRight : C →ₐ[k] C ⊗[k] C).comp
      (a : H →ₐ[k] C))) (toConv ((Algebra.TensorProduct.includeLeft : C →ₐ[k] C ⊗[k] C).comp
      (b : H →ₐ[k] C)))) : H →ₐc[k] C :=
  BialgHom.ofAlgHom (toConv (a : H →ₐ[k] C) * toConv (b : H →ₐ[k] C)).ofConv
    (by
      rw [AlgHom.comp_convMul_distrib, ofConv_toConv, ofConv_toConv,
        counitAlgHom_comp_bialgHom', counitAlgHom_comp_bialgHom']
      have h1 : toConv (Bialgebra.counitAlgHom k H) = (1 : WithConv (H →ₐ[k] k)) := by
        ext x; simp
      rw [h1, one_mul, AlgHom.convOne_def, ofConv_toConv]
      ext x; simp)
    (by
      apply toConv_injective
      have hdist : ∀ φ : C →ₐ[k] C ⊗[k] C, toConv (φ.comp
          (toConv (a : H →ₐ[k] C) * toConv (b : H →ₐ[k] C)).ofConv) =
          toConv (φ.comp (a : H →ₐ[k] C)) * toConv (φ.comp (b : H →ₐ[k] C)) := fun φ ↦ by
        rw [AlgHom.comp_convMul_distrib, toConv_ofConv, ofConv_toConv, ofConv_toConv]
      rw [← convMul_include, hdist, hdist, hdist, comulAlgHom_comp_bialgHom a,
        comulAlgHom_comp_bialgHom b, ← convMul_include, ← convMul_include]
      simp only [mul_assoc]
      congr 1
      rw [← mul_assoc, ← mul_assoc, ← hab.eq])

@[simp]
lemma coe_commMul (a b : H →ₐc[k] C) (hab) :
    ((commMul a b hab : H →ₐc[k] C) : H →ₐ[k] C) =
      (toConv (a : H →ₐ[k] C) * toConv (b : H →ₐ[k] C)).ofConv := rfl

end CommMul

section Levi

open TauCeti.Cocharacter

variable {k : Type u} [Field k] {H : Type u} [CommRing H] [HopfAlgebra k H]
variable (l : H →ₐc[k] LaurentPolynomial k)

/-- If `P(λ) = G`, every point lies in the dynamic parabolic. -/
lemma mem_parabolic_of_eq_bot (hP : parabolicDefiningHopfIdeal l = ⊥) {A : Type u} [CommRing A]
    [Algebra k A] (g : WithConv (H →ₐ[k] A)) : g ∈ parabolic A l := by
  refine (negativeCoefficientIdeal_le_ker_iff l g).mp ?_
  have : negativeCoefficientIdeal l = (parabolicDefiningHopfIdeal l).toIdeal :=
    (parabolicDefiningHopfIdeal_toIdeal l).symm
  rw [this, hP]
  intro x hx
  have : x = 0 := by simpa using hx
  simp [this]

/-- **The Levi retraction** `G = P(λ) → Z(λ) ⊆ G` on coordinate rings: the limit of the generic
point, `h ↦ (conjugation h).coeff 0`. -/
noncomputable def leviRetraction (hP : parabolicDefiningHopfIdeal l = ⊥) : H →ₐ[k] H :=
  (limit H l ⟨toConv (AlgHom.id k H), mem_parabolic_of_eq_bot l hP _⟩).ofConv

/-- The limit of any point is that point composed with the Levi retraction. -/
theorem limit_eq_comp_leviRetraction (hP : parabolicDefiningHopfIdeal l = ⊥) {A : Type u}
    [CommRing A] [Algebra k A] (g : parabolic A l) :
    limit A l g = toConv (g.1.ofConv.comp (leviRetraction l hP)) := by
  ext h
  rw [ofConv_toConv, AlgHom.comp_apply, limit_apply_eq_coeff_conjugate, coeff_conjugate,
    leviRetraction, limit_apply_eq_coeff_conjugate]
  rfl

/-- **(3) The Levi retraction is a Hopf map.** -/
noncomputable def leviRetractionBialgHom (hP : parabolicDefiningHopfIdeal l = ⊥) : H →ₐc[k] H :=
  BialgHom.ofAlgHom (leviRetraction l hP)
    (by
      have h1 := limit_eq_comp_leviRetraction l hP (1 : parabolic k l)
      rw [map_one] at h1
      ext x
      have h2 := congrArg (fun p : WithConv (H →ₐ[k] k) ↦ p.ofConv x) h1
      simp only [AlgHom.convOne_def, ofConv_toConv, AlgHom.comp_apply, OneMemClass.coe_one] at h2
      simpa using h2.symm)
    (by
      let pL : parabolic (H ⊗[k] H) l :=
        ⟨toConv Algebra.TensorProduct.includeLeft, mem_parabolic_of_eq_bot l hP _⟩
      let pR : parabolic (H ⊗[k] H) l :=
        ⟨toConv Algebra.TensorProduct.includeRight, mem_parabolic_of_eq_bot l hP _⟩
      have h1 := limit_eq_comp_leviRetraction l hP (pL * pR)
      rw [map_mul, limit_eq_comp_leviRetraction l hP, limit_eq_comp_leviRetraction l hP] at h1
      have hΔ : (pL * pR).1 = toConv (Bialgebra.comulAlgHom k H) := by
        have := convMul_include (k := k) (AlgHom.id k H) (AlgHom.id k H)
        simp only [AlgHom.comp_id, Algebra.TensorProduct.map_id, AlgHom.id_comp] at this
        exact this
      rw [hΔ] at h1
      have h3 := convMul_include (k := k) (leviRetraction l hP) (leviRetraction l hP)
      exact congrArg ofConv (h3.symm.trans h1))

@[simp]
lemma coe_leviRetractionBialgHom (hP : parabolicDefiningHopfIdeal l = ⊥) :
    ((leviRetractionBialgHom l hP : H →ₐc[k] H) : H →ₐ[k] H) = leviRetraction l hP := rfl

end Levi

end AlgMag.Reductive
