/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.FinalMiscThm124Printed
import AlgMag.FixesThm124

/-!
# Theorem 12.4 of *Algebraic Magnetism*, global statement through the printed route

`thm124_attP_printed` is `thm124_attP` with the chart statement obtained as printed: Cor 11.2, then the content of
Tags 067U, 063M, 062Z, with no use of Cor 11.10. The finiteness of `I/I²` comes from `A₀ ⊗_B Ω_{B/R}`.
-/

suppress_compilation

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Magnetism
open scoped Classical TensorProduct

attribute [local instance] AlgMag.GB.gradedAlgebraOf

universe u

namespace AlgMag.Sec12SpacesThm

open AlgMag.GB AlgMag.Sec12Spaces AlgMag.Sec12Printed

/-- `I/I²` is finite: it is a quotient of `A₀ ⊗_B Ω_{B/R}` (Tag 031I). -/
theorem finite_conormal_of_smooth {R A₀ B : Type u} [CommRing R] [CommRing A₀] [CommRing B] [Algebra A₀ B]
    (π : B →ₐ[A₀] A₀) [Algebra R B] [Algebra R A₀] [Algebra.Smooth R B]
    [Algebra.FormallySmooth R A₀] (φ : B →ₐ[R] A₀) (hφ : ∀ b, φ b = π b) :
    Module.Finite A₀ (Conormal π) := by
  letI : Algebra B A₀ := π.toRingHom.toAlgebra
  have hmap : ∀ b, algebraMap B A₀ b = π b := fun _ => rfl
  haveI : IsScalarTower R B A₀ := IsScalarTower.of_algebraMap_eq fun r => by
    rw [hmap, ← hφ]; exact (φ.commutes r).symm
  have surj : Function.Surjective (algebraMap B A₀) := fun a =>
    ⟨algebraMap A₀ B a, by rw [hmap]; exact π.commutes a⟩
  obtain ⟨l, hl⟩ := (Algebra.FormallySmooth.iff_split_injection (R := R) surj).1 inferInstance
  have hsm : ∀ (a : A₀) (y : A₀ ⊗[B] Ω[B⁄R]), algebraMap A₀ B a • y = a • y := by
    intro a y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [smul_add, hx, hy]
    | tmul x w =>
      rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, Algebra.smul_def, hmap]
      congr 1
      exact congrArg (· * x) (π.commutes a)
  let s : A₀ ⊗[B] Ω[B⁄R] →ₗ[A₀] Conormal π :=
    { toFun := fun y => l y
      map_add' := fun x y => map_add _ _ _
      map_smul' := fun a y => by
        rw [RingHom.id_apply, ← hsm]
        refine (map_smul l _ y).trans ?_
        exact algebraMap_smul B a (l y) }
  have hs : Function.Surjective s := fun x =>
    ⟨KaehlerDifferential.kerCotangentToTensor R B A₀ x, LinearMap.congr_fun hl x⟩
  haveI : Module.Finite A₀ (A₀ ⊗[B] Ω[B⁄R]) := Module.Finite.base_change B A₀ (Ω[B⁄R])
  exact Module.Finite.of_surjective s hs

variable {S : Scheme.{u}} {M : Type u} [AddCommGroup M] {X : Over S} [IsAffineHom X.hom]
  (act : AAction (overO S) M (yoneda.obj X))

/-- `SymOver`, by the printed route. -/
theorem symOver_printed [Smooth X.hom] (N : AddSubmonoid M) {F : AddSubgroup M}
    (hF : IsFace F.toAddSubmonoid N) {V : S.Opens} (hV : IsAffineOpen V) (h : N.FG ∨ AddGroup.FG M) :
    SymOver act N hF hV := by
  have hrest := printed_affine_067U act N hF hV h
  letI := (rho0 act N hF hV).toRingHom.toAlgebra
  have s₁ := smooth_Qalg act ⟨V, hV⟩ N
  have s₀ := smooth_Qalg act ⟨V, hV⟩ F.toAddSubmonoid
  exact ⟨finite_conormal_of_smooth (R := Γ(S, V)) _
    (piR (gZ act hV (F := F)) (Yq F N) (hI₁' act N hF hV) (hI₀' act hV)) (fun _ => rfl), hrest⟩

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

variable {M : Type u} [AddCommGroup M] [AddGroup.FG M]
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {actX : AAction (fppfO B S hS) M X}
  {A : Type u} {U : A → BigFppfOver B S hS}

/-- **Theorem 12.4**, printed route, face form, with `e`, `e'` the maps induced by the chart `U_a → X`. -/
theorem thm124_induced_face_printed (L : ZariskiLocallyLinearizable actX A U)
    (hsm : Space.IsSmooth B S hS (terminal.from X)) {N : AddSubmonoid M} {F : AddSubgroup M}
    (hF : IsFace F.toAddSubmonoid N) {Zx Zf : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (rx : RepresentsAttractor actX N Zx) (rf : RepresentsAttractor actX F.toAddSubmonoid Zf)
    {T : BigFppfOver B S hS} (y : Zf.obj (op T)) (t : (SCH).obj T) :
    ∃ a : A, haveI : IsAffineHom (structMap (U a)) := L.isAffineHom a
      ∃ he : Space.IsOpenImmersion B S hS
          (repAttractorMap (jHom L a) F.toAddSubmonoid (repCh (L.act a) F.toAddSubmonoid) rf),
        Space.IsOpenImmersion B S hS (repAttractorMap (jHom L a) N (repCh (L.act a) N) rx) ∧
        t ∈ rangeOf he y ∧
        IsPullback (repAttractorMap (jHom L a) N (repCh (L.act a) N) rx)
          (yoneda.map (faceS (L.act a) hF)) (repFace rx rf hF)
          (repAttractorMap (jHom L a) F.toAddSubmonoid (repCh (L.act a) F.toAddSubmonoid) rf) ∧
        (SCH).map (faceS (L.act a) hF) = (faceZ (chA (L.act a)) N hF).left ∧
        ∀ (V : S.Opens) (hV : IsAffineOpen V),
          IsPullback (iotaZ (chA (L.act a)) N ⟨V, hV⟩).left
            (PhiMap hV (rho0 (chA (L.act a)) N hF hV)).left (faceZ (chA (L.act a)) N hF).left
            (iotaZ (chA (L.act a)) F.toAddSubmonoid ⟨V, hV⟩).left ∧
          SymOver (chA (L.act a)) N hF hV := by
  have hC := countable_of_fg83 (M := M)
  have : ∀ a, IsAffineHom (structMap (U a)) := L.isAffineHom
  obtain ⟨a, he, ht⟩ := exists_chart_cover L rf (fun a => repCh (L.act a) F.toAddSubmonoid) y t
  have hO : Space.IsOpenImmersion B S hS (L.j a) := L.isOpen a
  have hp := isPullback_repFace_open (jHom L a) hO hF (repCh (L.act a) N) rx
    (repCh (L.act a) F.toAddSubmonoid) rf
  rw [repFace_eq] at hp
  have hs : Smooth (chO (B := B) (S := S) (hS := hS) (U₀ := U a)).hom := smooth_chart L hsm a
  exact ⟨a, he, (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hp.flip he,
    ht, hp, rfl, fun V hV => ⟨isPullback_chart_square (chA (L.act a)) hF ⟨V, hV⟩,
      symOver_printed (chA (L.act a)) N hF hV (Or.inr inferInstance)⟩⟩

/-- **Theorem 12.4**, printed route: `X → S` smooth with a Zariski locally linearizable action of `D(M)_S`, for any
magnet `N`. The morphism `X^N → X^{N^×}` of the attractor functors is, around every point of a scheme `T`
over `X^{N^×}`, the base change along the open immersion `(U_a)^{N^×} → X^{N^×}` induced by the chart
`U_a → X` of the morphism of schemes `(U_a)^N → (U_a)^{N^×}`. Over every affine open `V` of `S` the latter
is the base change of `Spec B → Spec B₀`, with `B = Sym_{B₀}(P)`, `P` finite projective over `B₀`. -/
theorem thm124_attP_printed (L : ZariskiLocallyLinearizable actX A U)
    (hsm : Space.IsSmooth B S hS (terminal.from X)) (N : AddSubmonoid M)
    {T : BigFppfOver B S hS} (y : (attP actX (unitsOf N).toAddSubmonoid).obj (op T))
    (t : (SCH).obj T) :
    ∃ a : A, haveI : IsAffineHom (structMap (U a)) := L.isAffineHom a
      ∃ he : Space.IsOpenImmersion B S hS
          (repAttractorMap (jHom L a) (unitsOf N).toAddSubmonoid
            (repCh (L.act a) (unitsOf N).toAddSubmonoid) (attPRep actX (unitsOf N).toAddSubmonoid)),
        Space.IsOpenImmersion B S hS
          (repAttractorMap (jHom L a) N (repCh (L.act a) N) (attPRep actX N)) ∧
        t ∈ rangeOf he y ∧
        IsPullback (repAttractorMap (jHom L a) N (repCh (L.act a) N) (attPRep actX N))
          (yoneda.map (faceS (L.act a) (isFace_unitsOf N)))
          (repFace (attPRep actX N) (attPRep actX (unitsOf N).toAddSubmonoid) (isFace_unitsOf N))
          (repAttractorMap (jHom L a) (unitsOf N).toAddSubmonoid
            (repCh (L.act a) (unitsOf N).toAddSubmonoid) (attPRep actX (unitsOf N).toAddSubmonoid)) ∧
        (SCH).map (faceS (L.act a) (isFace_unitsOf N)) =
          (faceZ (chA (L.act a)) N (isFace_unitsOf N)).left ∧
        ∀ (V : S.Opens) (hV : IsAffineOpen V),
          IsPullback (iotaZ (chA (L.act a)) N ⟨V, hV⟩).left
            (PhiMap hV (rho0 (chA (L.act a)) N (isFace_unitsOf N) hV)).left
            (faceZ (chA (L.act a)) N (isFace_unitsOf N)).left
            (iotaZ (chA (L.act a)) (unitsOf N).toAddSubmonoid ⟨V, hV⟩).left ∧
          SymOver (chA (L.act a)) N (isFace_unitsOf N) hV :=
  thm124_induced_face_printed L hsm (isFace_unitsOf N) (attPRep actX N)
    (attPRep actX (unitsOf N).toAddSubmonoid) y t

#print axioms thm124_attP_printed

end AlgMag.Sec12SpacesThm
