/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartPointRing
import AlgMag.ChartTower
import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# End of §1 of the chart-lemma proof: from the orbit to `OrbitInput`

* `AlgMag.ChartPoint.isField_of_chartPoint`: `Γ(P)` is a field for a `ChartPoint`.
* `AlgMag.ChartPoint.isSeparatedOver_of_space`: `Space.IsSeparatedOver → AlgMag.IsSeparatedOver`.
* `AlgMag.ChartPoint.orbitInput_of_closed`: a closed orbit is an `OrbitInput`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.ChartPoint

open ChartMain

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- `Γ(P)` is a field, for a closed point `P = Spec k`. -/
lemma isField_of_chartPoint (p : AlgMag.ChartPoint X) : IsField (RT p.P) := by
  letI := p.field
  let e1 : Γ((SCH).obj p.P, ⊤) ≃+* Γ(Spec (.of p.k), ⊤) :=
    (Scheme.Γ.mapIso p.iso.symm.op).commRingCatIsoToRingEquiv
  let e2 : Γ(Spec (.of p.k), ⊤) ≃+* p.k := (Scheme.ΓSpecIso (.of p.k)).commRingCatIsoToRingEquiv
  exact MulEquiv.isField (Field.toIsField p.k) (e1.trans e2).toMulEquiv

/-- `Γ(P)`-affineness of a closed point `P = Spec k`. -/
lemma isAffine_of_chartPoint (p : AlgMag.ChartPoint X) : IsAffine ((SCH).obj p.P) :=
  .of_isIso p.iso.hom

/-- The conversion between the two forms of "separated over `S`". -/
lemma isSeparatedOver_of_space (h : Space.IsSeparatedOver B S hS X) : AlgMag.IsSeparatedOver X :=
  (Space.isSeparatedOver_iff_isSeparated_of_isTerminal B S hS
    (Limits.IsTerminal.isTerminalObj yoneda _ Over.mkIdTerminal) (toBase X)).1 h

/-- **§1 → §2**: an equivariant closed orbit is an `OrbitInput`. -/
noncomputable def orbitInput_of_closed [AddMonoid.FG M] {P : BigFppfOver B S hS}
    [IsAffine ((SCH).obj P)] (actX : AAction (fppfO B S hS) M X) (N : AddSubgroup M)
    [AddMonoid.FG N] (o : yoneda.obj (Ob P N) ⟶ X) (hc : ClosedP o)
    (he : IsEquivariant (oAct N) actX o) : OrbitInput actX where
  O := Ob P N
  aff := inferInstance
  actO := oAct N
  j := o
  closed := hc
  equivariant := he

end AlgMag.ChartPoint

#print axioms AlgMag.ChartPoint.isField_of_chartPoint
#print axioms AlgMag.ChartPoint.isSeparatedOver_of_space
#print axioms AlgMag.ChartPoint.orbitInput_of_closed
