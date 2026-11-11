/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import StacksFrontier.RingTheory.Smoothing.ApproximationGRingEtale
import StacksFrontier.RingTheory.GRing.EssFiniteType

/-!
# Artin approximation for the chart theorem (chart-lemma proof, §5)

Artin 1969, Cor 2.2, in the functor form used in §5 of the note: a limit preserving functor on
`A`-algebras, an element over the completion of `A` at a prime `𝔭`, and an approximation of it
over an étale neighbourhood `(A', 𝔭')` of `(A, 𝔭)` with trivial residue extension.

The polynomial form is the library's Stacks 0CAR,
`StacksDraft.ArtinApproximation.artinApproximationGRing`, which rests on Stacks 07QZ and on
Popescu's theorem (Stacks 07GC, `Stacks.Smoothing.indSmooth_of_isRegularRingMap`). This file only
passes from polynomial systems to functors.

## Main results

* `AlgMag.ChartArtin.artinApprox`: the functor form, at a prime whose local ring is a G-ring.
* `AlgMag.ChartArtin.artinApprox_of_finiteType_int`: the case of a finite type `ℤ`-algebra, which
  is the case used in §5.
-/

open CategoryTheory IsLocalRing StacksDraft.ArtinApproximation

universe v u

namespace AlgMag.ChartArtin

variable {A : Type u} [CommRing A]

/-- An `A`-algebra `g : A → B`, as an object of the category of `A`-algebras. -/
abbrev algObj {B : Type u} [CommRing B] (g : A →+* B) : Under (CommRingCat.of A) :=
  Under.mk (CommRingCat.ofHom g)

/-- A map of `A`-algebras, as a morphism of the category of `A`-algebras. -/
abbrev algHom {B C : Type u} [CommRing B] [CommRing C] (g : A →+* B) (g' : A →+* C)
    (h : B →+* C) (e : h.comp g = g') : algObj g ⟶ algObj g' :=
  Under.homMk (CommRingCat.ofHom h) (by
    ext x
    exact RingHom.congr_fun e x)

/-- The form of "`F` is limit preserving" used in §5: every element of `F` over an `A`-algebra
comes from a finitely presented `A`-algebra. This is what commutation with filtered colimits gives
for a functor on `A`-algebras, every `A`-algebra being a filtered colimit of finitely presented
ones. -/
def IsLimitPreserving (F : Under (CommRingCat.of A) ⥤ Type v) : Prop :=
  ∀ (B : Type u) [CommRing B] (g : A →+* B) (ξ : F.obj (algObj g)),
    ∃ (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra A B₀) (_ : Algebra.FinitePresentation A B₀)
      (h : B₀ →+* B) (e : h.comp (algebraMap A B₀) = g) (ξ₀ : F.obj (algObj (algebraMap A B₀))),
      F.map (algHom _ g h e) ξ₀ = ξ

/-- The map `A' → (A'_{𝔭'})^∧ / 𝔪^N`. -/
noncomputable abbrev truncation {A' : Type u} [CommRing A'] (q : Ideal A') [q.IsPrime] (N : ℕ) :
    A' →+* Completion q ⧸ completionIdeal q N :=
  (Ideal.Quotient.mk (completionIdeal q N)).comp (toCompletion q)

/-- The map `(A_𝔭)^∧ → (A'_{𝔭'})^∧ / 𝔪^N`. -/
noncomputable abbrev completionTruncation {A' : Type u} [CommRing A'] (p : Ideal A') [p.IsPrime]
    {A'' : Type u} [CommRing A''] (q : Ideal A'') [q.IsPrime] (g : A' →+* A'')
    (hq : p = q.comap g) (N : ℕ) : Completion p →+* Completion q ⧸ completionIdeal q N :=
  (Ideal.Quotient.mk (completionIdeal q N)).comp (completionComparison p q g hq)

/-- **Artin approximation** (Artin 1969, Cor 2.2; the chart-lemma proof, §5).

Let `A` be a Noetherian ring, `𝔭` a prime with `A_𝔭` a G-ring, `F` a limit preserving functor on
`A`-algebras, `ξ ∈ F((A_𝔭)^∧)` and `N` an integer. There are an étale `A → A'`, a prime `𝔭'` over
`𝔭` with `κ(𝔭) = κ(𝔭')` and `ξ' ∈ F(A')` such that `ξ` and `ξ'` have the same image in
`F((A'_{𝔭'})^∧ / 𝔪^N)`.

The comparison `(A_𝔭)^∧ → (A'_{𝔭'})^∧` is bijective
(`AlgebraicGeometry.bijective_completionComparison`, Stacks), so this is the congruence
`ξ' ≡ ξ` of the note. -/
theorem artinApprox [IsNoetherianRing A] (p : Ideal A) [p.IsPrime]
    (hG : IsGRing (Localization.AtPrime p)) (F : Under (CommRingCat.of A) ⥤ Type v)
    (hF : IsLimitPreserving F) (ξ : F.obj (algObj (toCompletion p))) (N : ℕ) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Algebra.Etale A A')
      (q : Ideal A') (_ : q.IsPrime) (hq : p = q.comap (algebraMap A A'))
      (_ : Function.Bijective (Ideal.ResidueField.map p q (algebraMap A A') hq))
      (ξ' : F.obj (algObj (algebraMap A A')))
      (e : (completionTruncation p q (algebraMap A A') hq N).comp (toCompletion p) =
        (truncation q N).comp (algebraMap A A')),
      F.map (algHom _ _ (completionTruncation p q (algebraMap A A') hq N) e) ξ =
        F.map (algHom _ _ (truncation q N) rfl) ξ' := by
  classical
  obtain ⟨B₀, _, _, hfp, h, e₀, ξ₀, rfl⟩ := hF _ (toCompletion p) ξ
  -- A presentation of `B₀`, that is, a polynomial system.
  obtain ⟨n, φ, hφ, hker⟩ := Algebra.FinitePresentation.out (R := A) (A := B₀) |> fun ⟨n, φ, hφ, hk⟩ =>
    (⟨n, φ, hφ, hk⟩ : ∃ (n : ℕ) (φ : MvPolynomial (Fin n) A →ₐ[A] B₀),
      Function.Surjective φ ∧ (RingHom.ker φ.toRingHom).FG)
  obtain ⟨m, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hker
  have hfker : ∀ j, φ (f j) = 0 := fun j => by
    have : f j ∈ RingHom.ker φ.toRingHom := by
      rw [← hf]
      exact Submodule.subset_span ⟨j, rfl⟩
    exact this
  -- The solution in the completion.
  let a : Fin n → Completion p := fun i => h (φ (MvPolynomial.X i))
  have hcomp : ∀ P : MvPolynomial (Fin n) A,
      MvPolynomial.eval₂ (toCompletion p) a P = h (φ P) := fun P => by
    have : (MvPolynomial.eval₂Hom (toCompletion p) a) =
        h.comp φ.toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, RingHom.comp_apply]
        rw [show φ.toRingHom (MvPolynomial.C r) = algebraMap A B₀ r from
          (φ.commutes r)]
        exact (RingHom.congr_fun e₀ r).symm
      · intro i
        simp [a]
    exact RingHom.congr_fun this P
  obtain ⟨s⟩ := artinApproximationGRing.{u} A p ‹_› hG n m f N a fun j => by
    rw [hcomp, hfker, map_zero]
  -- The solution in the étale extension defines `B₀ → A'`.
  let ψ : MvPolynomial (Fin n) A →+* s.carrier :=
    MvPolynomial.eval₂Hom (algebraMap A s.carrier) s.sol
  have hψ : RingHom.ker φ.toRingHom ≤ RingHom.ker ψ := by
    rw [← hf, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact s.eval_sol j
  let θ : B₀ →+* s.carrier := RingHom.liftOfSurjective φ.toRingHom hφ ⟨ψ, fun x hx => hψ hx⟩
  have hθ : ∀ P, θ (φ P) = ψ P := fun P =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ P
  have hθA : θ.comp (algebraMap A B₀) = algebraMap A s.carrier := by
    ext r
    have := hθ (MvPolynomial.C r)
    rw [show φ (MvPolynomial.C r) = algebraMap A B₀ r from φ.commutes r] at this
    simpa [ψ] using this
  -- The two maps `B₀ → (A'_{𝔭'})^∧ / 𝔪^N` agree.
  have hmaps : (completionTruncation p s.prime (algebraMap A s.carrier) s.comap_prime N).comp h =
      (truncation s.prime N).comp θ := by
    apply RingHom.ext
    intro b
    obtain ⟨P, rfl⟩ := hφ b
    change _ = (truncation s.prime N) (θ (φ P))
    rw [hθ]
    have : ((completionTruncation p s.prime (algebraMap A s.carrier) s.comap_prime N).comp
          (h.comp φ.toRingHom)) = (truncation s.prime N).comp ψ := by
      apply MvPolynomial.ringHom_ext
      · intro r
        have h1 : φ.toRingHom (MvPolynomial.C r) = algebraMap A B₀ r := φ.commutes r
        simp only [RingHom.comp_apply, h1]
        rw [show h (algebraMap A B₀ r) = toCompletion p r from RingHom.congr_fun e₀ r]
        simp only [ψ, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, completionTruncation,
          truncation, RingHom.comp_apply]
        exact congrArg (Ideal.Quotient.mk (completionIdeal s.prime N))
          (completionComparison_toCompletion p s.prime _ s.comap_prime r)
      · intro i
        simp only [ψ, RingHom.comp_apply, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X,
          completionTruncation, truncation]
        exact Ideal.Quotient.eq.mpr (s.approx i)
    exact RingHom.congr_fun this P
  have ecomm : (completionTruncation p s.prime (algebraMap A s.carrier) s.comap_prime N).comp
      (toCompletion p) = (truncation s.prime N).comp (algebraMap A s.carrier) := by
    rw [← e₀, ← RingHom.comp_assoc, hmaps, RingHom.comp_assoc, hθA]
  refine ⟨s.carrier, inferInstance, inferInstance, inferInstance, s.prime, inferInstance,
    s.comap_prime, s.residueField_bijective, F.map (algHom _ _ θ hθA) ξ₀, ecomm, ?_⟩
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply]
  exact congrArg (fun z => F.map z ξ₀) (Under.UnderMorphism.ext (CommRingCat.hom_ext hmaps))

/-- A local ring of a finite type `ℤ`-algebra is a G-ring (Stacks 07PX, 07PV). -/
theorem isGRing_localization_of_finiteType_int [Algebra.FiniteType ℤ A] (p : Ideal A)
    [p.IsPrime] : IsGRing (Localization.AtPrime p) := by
  have : Algebra.EssFiniteType ℤ (Localization.AtPrime p) :=
    Algebra.EssFiniteType.comp ℤ A (Localization.AtPrime p)
  exact isGRing_of_essFiniteType (R := ℤ) isGRing_basic_examples.{0, 0}.2.2.1

/-- **Artin approximation over a finite type `ℤ`-algebra**: `artinApprox` without the G-ring
hypothesis, in the case used in §5 of the chart-lemma proof (there `A = P₀`). -/
theorem artinApprox_of_finiteType_int [Algebra.FiniteType ℤ A] (p : Ideal A) [p.IsPrime]
    (F : Under (CommRingCat.of A) ⥤ Type v) (hF : IsLimitPreserving F)
    (ξ : F.obj (algObj (toCompletion p))) (N : ℕ) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Algebra.Etale A A')
      (q : Ideal A') (_ : q.IsPrime) (hq : p = q.comap (algebraMap A A'))
      (_ : Function.Bijective (Ideal.ResidueField.map p q (algebraMap A A') hq))
      (ξ' : F.obj (algObj (algebraMap A A')))
      (e : (completionTruncation p q (algebraMap A A') hq N).comp (toCompletion p) =
        (truncation q N).comp (algebraMap A A')),
      F.map (algHom _ _ (completionTruncation p q (algebraMap A A') hq N) e) ξ =
        F.map (algHom _ _ (truncation q N) rfl) ξ' :=
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  artinApprox p (isGRing_localization_of_finiteType_int p) F hF ξ N

end AlgMag.ChartArtin
