/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartAtlas
import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
import StacksFrontier.AlgebraicGeometry.Spaces.Separated

/-!
# The chart lemma, as a statement, and Theorem 6.8 from it

**Conditional file.** `AlgMag.ChartLemmaStatement` and `AlgMag.ClosedPointsDetectCovers` are
*statements, not theorems*: nothing here proves them.

A closed point is given as `x : Spec k → X`, a closed immersion from the spectrum of a field. Then
`k` is the residue field; a chart point `u : Spec k → U` over `x` says `κ(u) = κ(x)`.

* `AlgMag.exists_chartFamily`: the chart lemma plus the covering property gives a finite family.
* `AlgMag.thm68_ii_of_chart`: **Theorem 6.8** for `D(M/Z)` with irreducible fibres (case (ii)),
  `S` affine and `X` of finite type over `S`, conditionally on the two statements above.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {M : Type u} [AddCommGroup M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- A closed point of `X`: a closed immersion from an object of the site which is the spectrum of a
field. -/
structure ChartPoint (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) where
  /-- The object `Spec k` of the site. -/
  P : BigFppfOver B S hS
  /-- The field. -/
  k : Type u
  [field : Field k]
  /-- `P` is `Spec k`. -/
  iso : (SCH).obj P ≅ Spec (.of k)
  /-- The point. -/
  x : yoneda.obj P ⟶ X
  isClosed : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) (SCH))) x

/-- An affine equivariant étale chart at `x`, preserving the residue field (`u` is defined over
the same `Spec k`) and the stabilizer. -/
structure IsChartAt (actX : AAction (fppfO B S hS) M X) (p : ChartPoint X)
    (U : BigFppfOver B S hS) (actU : AAction (fppfO B S hS) M (yoneda.obj U))
    (f : yoneda.obj U ⟶ X) (u : p.P ⟶ U) : Prop where
  affine : IsAffine ((SCH).obj U)
  equivariant : IsEquivariant actU actX f
  etale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) f
  lies_over : yoneda.map u ≫ f = p.x
  stabilizer : ∀ {T : BigFppfOver B S hS} (t : T ⟶ p.P) (h : APt (fppfO B S hS) M (op T)),
    actX.smul h (f.app (op T) (t ≫ u)) = f.app (op T) (t ≫ u) →
    actU.smul h (t ≫ u) = t ≫ u

/-- **The chart lemma**, as a statement: `M` f.g. abelian, `S` affine of finite type over `ℤ`, `X`
separated of finite type over `S` with `D(M)`-action, `x` a closed point. NOT PROVED here. -/
def ChartLemmaStatement (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (M : Type u)
    [AddCommGroup M] : Prop :=
  IsAffine S → LocallyOfFiniteType (terminal.from S) →
  ∀ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS X)
    (_ : Space.IsSeparatedOver B S hS X)
    (_ : Space.IsFiniteType B S hS (terminal.from X))
    (actX : AAction (fppfO B S hS) M X) (p : ChartPoint X),
    ∃ (U : BigFppfOver B S hS) (actU : AAction (fppfO B S hS) M (yoneda.obj U))
      (f : yoneda.obj U ⟶ X) (u : p.P ⟶ U), IsChartAt actX p U actU f u

/-- Closed points detect étale covers, with a finite subcover: for `X` of finite type over a
Jacobson base, a family of étale maps through which all closed points factor has a finite jointly
surjective subfamily. NOT PROVED here: the library has no closed points of algebraic spaces and no
Jacobson property for them. -/
def ClosedPointsDetectCovers (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∀ (ι : Type (u + 1)) (U : ι → BigFppfOver B S hS) (f : ∀ i, yoneda.obj (U i) ⟶ X)
    (e : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) (f i)),
    (∀ p : ChartPoint X, ∃ (i : ι) (u : p.P ⟶ U i), yoneda.map u ≫ f i = p.x) →
    ∃ (n : ℕ) (c : Fin n → ι), ∀ (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X)
      (t : (SCH).obj T), ∃ a, t ∈ Set.range ((SCH).map ((e (c a)).rep.snd x))

/-- Chart lemma + covering property: a finite family of charts. -/
theorem exists_chartFamily [IsAffine S] (hSft : LocallyOfFiniteType (terminal.from S)) (hX : IsAlgebraicSpace B S hS X)
    (hsep : Space.IsSeparatedOver B S hS X)
    (hft : Space.IsFiniteType B S hS (terminal.from X))
    (actX : AAction (fppfO B S hS) M X) (hchart : ChartLemmaStatement B S hS M)
    (hcov : ClosedPointsDetectCovers X) :
    ∃ (n : ℕ) (U : ULift.{u} (Fin n) → BigFppfOver B S hS),
      Nonempty (EtaleChartFamily actX (ULift.{u} (Fin n)) U) := by
  have hc := fun p : ChartPoint X => hchart inferInstance hSft X hX hsep hft actX p
  choose U actU f u h using hc
  obtain ⟨n, c, hcv⟩ := hcov (ChartPoint X) U f (fun p => (h p).etale)
    (fun p => ⟨p, u p, (h p).lies_over⟩)
  refine ⟨n, fun a => U (c a.down), ⟨{
    act := fun a => actU (c a.down)
    f := fun a => f (c a.down)
    equivariant := fun a => (h _).equivariant
    etale := fun a => (h _).etale
    isAffineHom := fun a => ?_
    covers := fun T x t => ?_ }⟩⟩
  · have := (h (c a.down)).affine
    exact isAffineHom_of_isAffine _
  · obtain ⟨a, ha⟩ := hcv T x t
    exact ⟨⟨a⟩, ha⟩

/-- **Theorem 6.8, case (ii), `S` affine, `X` of finite type over `S`**, conditional on
`ChartLemmaStatement` and `ClosedPointsDetectCovers`. The atlas is `S`-affine. -/
theorem thm68_ii_of_chart [IsAffine S] [HasFiniteCoproducts (BigFppfOver B S hS)]
    (hSft : LocallyOfFiniteType (terminal.from S)) (hX : IsAlgebraicSpace B S hS X)
    (hsep : Space.IsSeparatedOver B S hS X)
    (hft : Space.IsFiniteType B S hS (terminal.from X))
    (actX : AAction (fppfO B S hS) M X) (hchart : ChartLemmaStatement B S hS M)
    (hcov : ClosedPointsDetectCovers X) {Z : AddSubgroup M}
    (hM : B.Contains (Spec (ZMon (M ⧸ Z)))) (hirr : IrreducibleFibres (M ⧸ Z) S) :
    ∃ (V : BigFppfOver B S hS) (actV : AAction (fppfO B S hS) M (yoneda.obj V))
      (v : yoneda.obj V ⟶ X), IsZFPRAtlas actV actX v Z ∧ IsSAffineAtlas actV actX v := by
  obtain ⟨n, U, ⟨L⟩⟩ := exists_chartFamily hSft hX hsep hft actX hchart hcov
  have : Finite (ULift.{u} (Fin n)) := inferInstance
  have : HasColimit (Discrete.functor U) := inferInstance
  let V := ∐ U
  let j : ∀ a, U a ⟶ V := Sigma.ι U
  have hV : IsColimit (Cofan.mk V j) :=
    (coproductIsCoproduct U).ofIsoColimit (Cocone.ext (Iso.refl _) (by
      rintro ⟨a⟩; simp [j]))
  obtain ⟨v, hv⟩ := isZFPRAtlas_of_family_irreducible hX L hV hM hirr
  exact ⟨V, _, v, hv, hv.atlas, ULift.{u} (Fin n), inferInstance, _,
    coprod_decomposition L.act hV L.isAffineHom⟩

end AlgMag

#print axioms AlgMag.exists_chartFamily
#print axioms AlgMag.thm68_ii_of_chart
