/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
-/
import AlgMag.Faces.Spaces
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# `p_{N,F}` is an affine space fibration

From `face_sym_ring` / `FaceChart`: over an affine chart, `B = O(X^N) ≅ Sym_{B₀}(P)` with
`P = I/I²` finite projective over `B₀ = O(X^F)`. Then there are `f_j ∈ B₀` with
`(f_j) = B₀` such that `P_{f_j}` is free of rank `r_j` and `B_{f_j} ≅ (B₀)_{f_j}[x_1, …, x_{r_j}]`
as `(B₀)_{f_j}`-algebras: Zariski-locally on `X^F`, `X^N ≅ X^F ×_S 𝔸^r_S`.

* `symBaseChange`: `S ⊗_R Sym_R P ≅ Sym_S(S ⊗_R P)`.
* `exists_cover_mvPolynomial_of_sym`: the ring statement.
* `faceChart_affineSpace`, `bb_face_affineSpace`: the chart statement.
-/

universe u v w

open TensorProduct

namespace AlgMag.Faces

section SymBaseChange

variable (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
  (P : Type w) [AddCommGroup P] [Module R P]

/-- The map `S ⊗_R Sym_R P → Sym_S(S ⊗_R P)`. -/
noncomputable def symBCto : S ⊗[R] SymmetricAlgebra R P →ₐ[S] SymmetricAlgebra S (S ⊗[R] P) :=
  Algebra.TensorProduct.lift (Algebra.ofId S _)
    (SymmetricAlgebra.lift
      (((SymmetricAlgebra.ι S (S ⊗[R] P)).restrictScalars R) ∘ₗ TensorProduct.mk R S P 1))
    (fun _ _ => Commute.all _ _)

/-- The map `Sym_S(S ⊗_R P) → S ⊗_R Sym_R P`. -/
noncomputable def symBCfrom : SymmetricAlgebra S (S ⊗[R] P) →ₐ[S] S ⊗[R] SymmetricAlgebra R P :=
  SymmetricAlgebra.lift (LinearMap.baseChange S (SymmetricAlgebra.ι R P))

/-- **Base change of the symmetric algebra.** `S ⊗_R Sym_R P ≅ Sym_S(S ⊗_R P)`. -/
noncomputable def symBaseChange :
    S ⊗[R] SymmetricAlgebra R P ≃ₐ[S] SymmetricAlgebra S (S ⊗[R] P) :=
  AlgEquiv.ofAlgHom (symBCto R S P) (symBCfrom R S P)
    (SymmetricAlgebra.algHom_ext (TensorProduct.AlgebraTensorModule.ext fun s p => by
      simp only [symBCto, symBCfrom, LinearMap.coe_comp, Function.comp_apply]
      simp [Algebra.TensorProduct.lift_tmul]
      rw [← Algebra.smul_def, ← LinearMap.map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]))
    (Algebra.TensorProduct.ext (Subsingleton.elim _ _)
      (SymmetricAlgebra.algHom_ext (LinearMap.ext fun p => by
        simp [symBCto, symBCfrom, Algebra.TensorProduct.lift_tmul])))

end SymBaseChange

section Ring

variable {R : Type u} [CommRing R] {B : Type u} [CommRing B] [Algebra R B]
  {P : Type u} [AddCommGroup P] [Module R P]

attribute [local instance] Module.finitePresentation_of_projective Module.free_of_flat_of_isLocalRing

/-- A finite projective module is free of finite rank on a cover by basic opens. -/
theorem exists_cover_free [Module.Finite R P] [Module.Projective R P] :
    ∃ s : Finset R, Ideal.span (s : Set R) = ⊤ ∧ ∀ f ∈ s,
      Module.Free (Localization.Away f) (LocalizedModule.Away f P) ∧
      Module.Finite (Localization.Away f) (LocalizedModule.Away f P) := by
  have hx : ∀ x : PrimeSpectrum R, ∃ r, r ∈ x.asIdeal.primeCompl ∧
      Module.Free (Localization (.powers r)) (LocalizedModule.Away r P) := fun x => by
    obtain ⟨r, hr, hr', -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
      x.asIdeal.primeCompl (LocalizedModule.mkLinearMap x.asIdeal.primeCompl P)
      (Localization.AtPrime x.asIdeal)
    exact ⟨r, hr, hr'⟩
  choose r hr hfree using hx
  have htop : Ideal.span (Set.range r) = ⊤ := by
    by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    exact hr ⟨m, hm.isPrime⟩ (hle (Ideal.subset_span ⟨_, rfl⟩))
  obtain ⟨s, hs, hspan⟩ := (Ideal.span_eq_top_iff_finite _).1 htop
  refine ⟨s, hspan, fun f hf => ?_⟩
  obtain ⟨x, rfl⟩ := hs hf
  exact ⟨hfree x, Module.Finite.of_isLocalizedModule (.powers (r x))
    (LocalizedModule.mkLinearMap (.powers (r x)) P)⟩

omit [Module R P] in
/-- `R_f`-algebra maps out of `R_f`-algebras are determined as ring maps commuting with `R`. -/
theorem locAway_algEquiv {f : R} {C D : Type u} [CommRing C] [CommRing D]
    [Algebra (Localization.Away f) C] [Algebra (Localization.Away f) D] (e : C ≃+* D)
    (he : ∀ x : R, e (algebraMap (Localization.Away f) C (algebraMap R _ x)) =
      algebraMap (Localization.Away f) D (algebraMap R _ x)) :
    Nonempty (C ≃ₐ[Localization.Away f] D) := by
  refine ⟨AlgEquiv.ofRingEquiv (f := e) fun y => ?_⟩
  have := IsLocalization.ringHom_ext (Submonoid.powers f)
    (j := (e : C →+* D).comp (algebraMap (Localization.Away f) C))
    (k := algebraMap (Localization.Away f) D) (RingHom.ext he)
  exact DFunLike.congr_fun this y

/-- **Affine space fibration, ring form.** `B ≅ Sym_R(P)` with `P` finite projective. There is
a finite family `f_j` generating the unit ideal (a cover of `Spec R` by the `D(f_j)`) such that
`P_{f_j}` is free of rank `r_j` and `B_{f_j} ≅ R_{f_j}[x_1, …, x_{r_j}]` as `R_{f_j}`-algebras. -/
theorem exists_cover_mvPolynomial_of_sym [Module.Finite R P] [Module.Projective R P]
    (e : SymmetricAlgebra R P ≃ₐ[R] B) :
    ∃ s : Finset R, Ideal.span (s : Set R) = ⊤ ∧ ∀ f ∈ s, ∃ r : ℕ,
      Nonempty (Module.Basis (Fin r) (Localization.Away f) (LocalizedModule.Away f P)) ∧
      Nonempty (Localization (Algebra.algebraMapSubmonoid B (.powers f)) ≃ₐ[Localization.Away f]
        MvPolynomial (Fin r) (Localization.Away f)) := by
  obtain ⟨s, hs, h⟩ := exists_cover_free (R := R) (P := P)
  refine ⟨s, hs, fun f hf => ?_⟩
  obtain ⟨hfr, hfin⟩ := h f hf
  set Rf := Localization.Away f
  obtain ⟨r, ⟨bL⟩⟩ : ∃ r : ℕ, Nonempty (Module.Basis (Fin r) Rf (LocalizedModule.Away f P)) := by
    rcases subsingleton_or_nontrivial Rf with hR | hR
    · have : Subsingleton (LocalizedModule.Away f P) := Module.subsingleton Rf _
      exact ⟨0, ⟨Module.Basis.empty _⟩⟩
    · exact ⟨_, ⟨Module.finBasis Rf (LocalizedModule.Away f P)⟩⟩
  refine ⟨r, ⟨bL⟩, ?_⟩
  -- basis of `R_f ⊗ P`
  let eP : Rf ⊗[R] P ≃ₗ[Rf] LocalizedModule.Away f P :=
    (LocalizedModule.isBaseChange (.powers f) P).equiv
  let b := bL.map eP.symm
  -- `R_f ⊗ B ≃ₐ[R_f] R_f[x]`
  let E : Rf ⊗[R] B ≃ₐ[Rf] MvPolynomial (Fin _) Rf :=
    (Algebra.TensorProduct.congr AlgEquiv.refl e.symm).trans
      ((symBaseChange R Rf P).trans (SymmetricAlgebra.equivMvPolynomial b))
  -- `B_f ≃ₐ[B] R_f ⊗ B`
  let L : Localization (Algebra.algebraMapSubmonoid B (.powers f)) ≃ₐ[B] B ⊗[R] Rf :=
    (Localization.tensorLeftAlgEquiv (.powers f) B).symm
  let Lc : Localization (Algebra.algebraMapSubmonoid B (.powers f)) ≃+* Rf ⊗[R] B :=
    L.toRingEquiv.trans (Algebra.TensorProduct.comm R B Rf).toRingEquiv
  refine locAway_algEquiv (Lc.trans E.toRingEquiv) fun x => ?_
  have h1 : algebraMap Rf (Localization (Algebra.algebraMapSubmonoid B (.powers f)))
      (algebraMap R Rf x) = algebraMap B _ (algebraMap R B x) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have h2 : Lc (algebraMap B _ (algebraMap R B x)) = algebraMap R (Rf ⊗[R] B) x := by
    simp only [Lc, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes, L]
    simp [Algebra.TensorProduct.algebraMap_apply]
    rw [Algebra.algebraMap_eq_smul_one (A := B), Algebra.algebraMap_eq_smul_one (A := Rf),
      TensorProduct.smul_tmul]
  rw [h1, RingEquiv.trans_apply, h2]
  simp only [AlgEquiv.coe_ringEquiv]
  rw [IsScalarTower.algebraMap_apply R Rf (Rf ⊗[R] B), AlgEquiv.commutes,
    ← IsScalarTower.algebraMap_apply]

end Ring

section Chart

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Magnetism
open AlgMag.GB AlgMag.Sec12Printed

variable {S : Scheme.{u}} {M : Type u} [AddCommGroup M]
variable {X : Over S} [IsAffineHom X.hom] (act : AAction (overO S) M (yoneda.obj X))
variable (N : AddSubmonoid M) {F : AddSubmonoid M} (hF : IsFace F N)

attribute [local instance] gradedAlgebraOf

/-- `p_{N,F}` over the affine open `V` of `S` is an affine space fibration: the zero section
`ρ : B₀ = O(X^F|_V) → B = O(X^N|_V)` gives the cartesian chart square for `p_{N,F}`, and there are
`f_j ∈ B₀` generating the unit ideal with `(I/I²)_{f_j}` free of rank `r_j` and
`B_{f_j} ≅ (B₀)_{f_j}[x_1, …, x_{r_j}]` as `(B₀)_{f_j}`-algebras. So over `D(f_j) ⊆ X^F|_V`,
`X^N ≅ D(f_j) ×_S 𝔸^{r_j}_S`. -/
def AffineSpaceChart {V : S.Opens} (hV : IsAffineOpen V) : Prop :=
  ∃ ρ : Qalg act F hV →ₐ[Γ(S, V)] Qalg act N hV,
    IsPullback (iotaZ act N ⟨V, hV⟩).left (PhiMap hV ρ).left (faceZF act N hF).left
      (iotaZ act F ⟨V, hV⟩).left ∧
    (letI := ρ.toRingHom.toAlgebra
     ∃ π : Qalg act N hV →ₐ[Qalg act F hV] Qalg act F hV,
      (∀ x, π (ρ x) = x) ∧
      ∃ s : Finset (Qalg act F hV), Ideal.span (s : Set (Qalg act F hV)) = ⊤ ∧ ∀ f ∈ s, ∃ r : ℕ,
        Nonempty (Module.Basis (Fin r) (Localization.Away f) (LocalizedModule.Away f (Conormal π))) ∧
        Nonempty (Localization (Algebra.algebraMapSubmonoid (Qalg act N hV) (.powers f)) ≃ₐ[Localization.Away f]
          MvPolynomial (Fin r) (Localization.Away f)))

/-- `FaceChart` (Theorem A (ii)) implies `AffineSpaceChart`. -/
theorem affineSpaceChart_of_faceChart {V : S.Opens} (hV : IsAffineOpen V)
    (h : FaceChart act N hF hV) : AffineSpaceChart act N hF hV := by
  obtain ⟨ρ, hpb, π, hπ, -, hfin, hproj, ⟨e⟩⟩ := h
  let := ρ.toRingHom.toAlgebra
  obtain ⟨s, hs, hf⟩ := exists_cover_mvPolynomial_of_sym e
  exact ⟨ρ, hpb, π, hπ, s, hs, hf⟩

/-- **Corollary of Theorem A (ii).** `X` affine and smooth over `S`, `N` finitely generated or `M`
finitely generated, `F` a face of `N`: `p_{N,F}` is an affine space fibration over every affine
open of `S`. -/
theorem affineSpaceChart_printed [Smooth X.hom] {V : S.Opens} (hV : IsAffineOpen V)
    (h : N.FG ∨ AddGroup.FG M) : AffineSpaceChart act N hF hV :=
  affineSpaceChart_of_faceChart act N hF hV (faceChart_printed act N hF hV h)

end Chart

section Thm

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Magnetism
open AlgMag.GB AlgMag.Sec12Spaces AlgMag.Sec12Printed AlgMag.Sec12SpacesThm

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {M : Type u} [AddCommGroup M] [AddGroup.FG M]
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {actX : AAction (fppfO B S hS) M X}
  {A : Type u} {U : A → BigFppfOver B S hS}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- **`p_{N,F} : X^N → X^F` is an affine space fibration.** `X → S` smooth with a Zariski locally
linearizable action, `F` a face of `N`. Every point of `X^F` lies in a chart `(U_a)^F`, open in
`X^F`, with `(U_a)^N = X^N ×_{X^F} (U_a)^F`, and over each affine open of `S` the map
`(U_a)^N → (U_a)^F` is, Zariski-locally on `(U_a)^F`, the projection `X^F ×_S 𝔸^r_S → X^F`. -/
theorem bb_face_affineSpace (L : ZariskiLocallyLinearizable actX A U)
    (hsm : Space.IsSmooth B S hS (terminal.from X)) {N F : AddSubmonoid M} (hF : IsFace F N)
    {T : BigFppfOver B S hS} (y : (attP actX F).obj (op T)) (t : (SCH).obj T) :
    ∃ a : A, haveI : IsAffineHom (structMap (U a)) := L.isAffineHom a
      ∃ he : Space.IsOpenImmersion B S hS
          (repAttractorMap (jHom L a) F (repCh (L.act a) F) (attPRep actX F)),
        Space.IsOpenImmersion B S hS
          (repAttractorMap (jHom L a) N (repCh (L.act a) N) (attPRep actX N)) ∧
        t ∈ rangeOf he y ∧
        IsPullback (repAttractorMap (jHom L a) N (repCh (L.act a) N) (attPRep actX N))
          (yoneda.map (faceSF (L.act a) hF)) (repFace (attPRep actX N) (attPRep actX F) hF)
          (repAttractorMap (jHom L a) F (repCh (L.act a) F) (attPRep actX F)) ∧
        (SCH).map (faceSF (L.act a) hF) = (faceZF (chA (L.act a)) N hF).left ∧
        ∀ (V : S.Opens) (hV : IsAffineOpen V), AffineSpaceChart (chA (L.act a)) N hF hV := by
  obtain ⟨a, he, h1, h2, h3, h4, h5⟩ := bb_face_attP L hsm hF y t
  haveI : IsAffineHom (structMap (U a)) := L.isAffineHom a
  exact ⟨a, he, h1, h2, h3, h4, fun V hV =>
    affineSpaceChart_of_faceChart (chA (L.act a)) N hF hV (h5 V hV)⟩

end Thm

end AlgMag.Faces
