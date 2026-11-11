/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartPointReduce
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# Assembly of §1 of the chart-lemma proof

* `AlgMag.ChartPoint.finite_of_chartPoint`: the residue field of a closed point is finite.
* `AlgMag.ChartPoint.Lemma11Statement`: **Lemma 1.1, as a statement. NOT PROVED here.**
* `AlgMag.ChartPoint.exists_orbitInput_of_lemma11`: §1 conditionally on it: the reduction to `X ×_S Z'`,
  the orbit, and the `OrbitInput`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.ChartPoint

open ChartMain

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- `ℤ` is a Jacobson ring (Stacks 00G4). -/
lemma isJacobsonRing_int' : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases h : P = ⊥
  · subst h
    refine le_antisymm ?_ Ideal.le_jacobson
    intro n hn
    by_contra hn0
    have hn0' : n ≠ 0 := fun e => hn0 (by simp [e])
    obtain ⟨q, hq, hqp⟩ := Nat.exists_infinite_primes (n.natAbs + 1)
    have hirr : Irreducible (q : ℤ) := Nat.prime_iff_prime_int.1 hqp |>.irreducible
    have hmax : (Ideal.span {(q : ℤ)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hirr
    have hmem : n ∈ Ideal.span {(q : ℤ)} :=
      (Submodule.mem_sInf.1 hn) _ ⟨bot_le, hmax⟩
    rw [Ideal.mem_span_singleton] at hmem
    have := Nat.le_of_dvd (Int.natAbs_pos.2 hn0') (Int.natCast_dvd.1 hmem)
    omega
  · have : P.IsMaximal := hP.isMaximal h
    exact Ideal.jacobson_eq_self_of_isMaximal

/-- A field which is a quotient of a ring of finite type over `ℤ` is finite (the ring being given
over `ULift ℤ`). -/
lemma finite_quot_of_ft {R : Type u} [CommRing R] (φ : ULift.{u} ℤ →+* R) (hφ : φ.FiniteType)
    (m : Ideal R) [m.IsMaximal] : Finite (R ⧸ m) := by
  letI := Ideal.Quotient.field m
  have hft : (algebraMap ℤ (R ⧸ m)).FiniteType := by
    have h1 : (Ideal.Quotient.mk m).FiniteType :=
      RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective
    have h2 : ((ULift.ringEquiv.symm : ℤ ≃+* ULift.{u} ℤ) : ℤ →+* ULift.{u} ℤ).FiniteType :=
      RingHom.FiniteType.of_surjective _ ULift.ringEquiv.symm.surjective
    have := (h1.comp hφ).comp h2
    convert this using 1
    exact Subsingleton.elim _ _
  have : Algebra.FiniteType ℤ (R ⧸ m) := (RingHom.finiteType_algebraMap).1 hft
  have := isJacobsonRing_int'
  have : Module.Finite ℤ (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℤ (R ⧸ m)
  have hint : Algebra.IsIntegral ℤ (R ⧸ m) := Algebra.IsIntegral.of_finite ℤ (R ⧸ m)
  have hninj : ¬ Function.Injective (algebraMap ℤ (R ⧸ m)) := fun h =>
    Int.not_isField (isField_of_isIntegral_of_isField h (Field.toIsField (R ⧸ m)))
  obtain ⟨q, hq⟩ := CharP.exists (R ⧸ m)
  have hq0 : q ≠ 0 := by
    rintro rfl
    have := CharP.charP_to_charZero (R ⧸ m)
    exact hninj (algebraMap ℤ (R ⧸ m)).injective_int
  refine Module.finite_of_fg_torsion (R ⧸ m) fun x => ?_
  refine ⟨⟨(q : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hq0)⟩, ?_⟩
  change (q : ℤ) • x = 0
  rw [zsmul_eq_mul, Int.cast_natCast, CharP.cast_eq_zero, zero_mul]

/-- **§1**: `κ(x)` is a finite field: `S` of finite type over `ℤ`, `X` of finite type over `S`.
Uses `finite_of_finite_type_of_isJacobsonRing`. -/
theorem finite_of_chartPoint (hSft : LocallyOfFiniteType (terminal.from S))
    (hX : IsAlgebraicSpace B S hS X) (hft : Space.IsFiniteType B S hS (terminal.from X))
    (p : AlgMag.ChartPoint X) : Finite (RT p.P) := by
  obtain ⟨U, φ, hs, he⟩ := hX.exists_atlas
  have hK := isField_of_chartPoint p
  -- `U → S` is locally of finite type
  let T1 : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))
  let hT : IsTerminal T1 := Over.mkIdTerminal
  let hY : IsTerminal (yoneda.obj T1) := Limits.IsTerminal.isTerminalObj yoneda T1 hT
  let b : yoneda.obj T1 ≅ ⊤_ _ := hY.uniqueUpToIso terminalIsTerminal
  have hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (SCH)).presheaf b.hom := Space.presheaf_etale_of_iso B S hS b
  have hl : LocallyOfFiniteType ((SCH).map (hT.from U)) :=
    hft.1 U T1 φ b.hom (hT.from U) he hb (Subsingleton.elim _ _ |>.trans rfl)
  -- `Y = P ×_X U`
  have sq := hs.rep.isPullback p.x
  let Y := hs.rep.pullback p.x
  let toP : Y ⟶ p.P := hs.rep.snd p.x
  obtain ⟨toU, htoU⟩ := yoneda.map_surjective (hs.rep.fst p.x)
  have sq' : IsPullback (yoneda.map toP) (yoneda.map toU) p.x φ := by
    rw [htoU]; exact sq.flip
  have hcl : IsClosedImmersion ((SCH).map toU) := p.isClosed.property _ _ _ sq'
  have hsu : Surjective ((SCH).map toP) := hs.property_snd p.x
  have hP : IsAffine ((SCH).obj p.P) := isAffine_of_chartPoint p
  letI : Field (RT p.P) := hK.toField
  letI := p.field
  let y0 : (SCH).obj p.P := p.iso.inv (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum p.k)
  obtain ⟨y, -⟩ := ((SCH).map toP).surjective y0
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
  haveI := hl
  haveI hSft' : LocallyOfFiniteType (terminal.from ((SCH).obj T1)) := hSft
  let e := terminalIsoIsTerminal specULiftZIsTerminal.{u}
  let g : (SCH).obj Y ⟶ Spec (.of (ULift.{u} ℤ)) :=
    (SCH).map toU ≫ (SCH).map (hT.from U) ≫ terminal.from ((SCH).obj T1) ≫ e.hom
  have hg : LocallyOfFiniteType g := inferInstance
  have hft1 := g.finiteType_appLE (U := ⊤) (V := W) (isAffineOpen_top _) hW le_top
  let R : Type u := Γ((SCH).obj Y, W)
  haveI : Nonempty W := ⟨⟨y, hyW⟩⟩
  haveI : Nontrivial R := Scheme.component_nontrivial _ W
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  let φ0 : ULift.{u} ℤ →+* R :=
    (g.appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (.of (ULift.{u} ℤ))).inv.hom
  have hφ0 : φ0.FiniteType := hft1.comp (RingHom.FiniteType.of_surjective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (ULift.{u} ℤ))).inv).2)
  haveI : Finite (R ⧸ m) := finite_quot_of_ft φ0 hφ0 m
  letI := Ideal.Quotient.field m
  let ψ : RT p.P →+* R ⧸ m :=
    (Ideal.Quotient.mk m).comp (((SCH).obj Y).presheaf.map (homOfLE le_top).op).hom |>.comp
      ((SCH).map toP).appTop.hom
  exact Finite.of_injective ψ ψ.injective

/-- **Lemma 1.1, as a statement. NOT PROVED here.** `O = Spec k[N] → X` equivariant and injective on
points, `X` separated: after replacing `X` by a stable open containing the orbit, it is a closed
immersion. -/
def Lemma11Statement (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (M : Type u)
    [AddCommGroup M] [AddMonoid.FG M] : Prop :=
  ∀ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS X)
    (_ : Space.IsSeparatedOver B S hS X) (actX : AAction (fppfO B S hS) M X)
    (P : BigFppfOver B S hS) (_ : IsAffine ((BigFppfOver.toScheme B S hS).obj P)) (_ : IsField (RT P))
    (N : AddSubgroup M) [AddMonoid.FG N] (o : yoneda.obj (Ob P N) ⟶ X),
    IsEquivariant (oAct N) actX o →
    (∀ {T : BigFppfOver B S hS} (a b : T ⟶ Ob P N), o.app (op T) a = o.app (op T) b → a = b) →
    ∃ (X' : Subfunctor X) (hle : Subfunctor.range o ≤ X'),
      Space.IsOpenSubspace B S hS X' ∧
      (∀ {T : (BigFppfOver B S hS)ᵒᵖ} (h : APt (fppfO B S hS) M T) (x : X'.toFunctor.obj T),
        ∃ y, X'.ι.app T y = actX.smul h (X'.ι.app T x)) ∧
      ClosedP (Subfunctor.lift o hle)

/-- **§1, conditional on `Lemma11Statement`.** For a closed point `p` of `X`, `S` affine of finite
type over `ℤ`, `X` separated of finite type over `S`: there is `Z'` étale over `S` and a stable open
`X'' ⊆ X ×_S Z'` with an `OrbitInput`. -/
theorem exists_orbitInput_of_lemma11 [IsAffine S] [AddMonoid.FG M]
    (h11 : Lemma11Statement B S hS M) (hSft : LocallyOfFiniteType (terminal.from S))
    (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X)
    (hft : Space.IsFiniteType B S hS (terminal.from X))
    (actX : AAction (fppfO B S hS) M X) (p : AlgMag.ChartPoint X) :
    ∃ (Zp : BigFppfOver B S hS) (ιz : p.P ⟶ Zp) (X'' : Subfunctor (XP X Zp))
      (hst : ∀ {T : (BigFppfOver B S hS)ᵒᵖ} (h : APt (fppfO B S hS) M T)
        (x : X''.toFunctor.obj T),
        ∃ y, X''.ι.app T y = (actProd Zp actX).smul h (X''.ι.app T x))
      (D : OrbitInput (actOfMono (actProd Zp actX) X''.ι hst)),
      Etale ((SCH).map (toTop Zp)) ∧ Mono ιz ∧ Space.IsOpenSubspace B S hS X'' ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH)))
        (FunctorToTypes.prod.fst (F := X) (G := yoneda.obj Zp)) := by
  have hK := isField_of_chartPoint p
  have hP := isAffine_of_chartPoint p
  obtain ⟨Zp, ιz, hZa, hιm, hZe⟩ := exists_Zp (P := p.P) hK
    (finite_of_chartPoint hSft hX hft p)
  obtain ⟨hA, hE, hSp⟩ := xp_props (X := X) hX hsep hZe
  let x' : yoneda.obj p.P ⟶ XP X Zp := FunctorToTypes.prod.lift p.x (yoneda.map ιz)
  obtain ⟨Z₀, hfg, o, -, hoe, hoi⟩ := exists_orbit_mono hK hA (isSeparatedOver_of_space hSp)
    (actProd Zp actX) x' (Zp := Zp) FunctorToTypes.prod.snd (fun _ _ => rfl) ιz rfl
  obtain ⟨X'', hle, hop, hst, hcl⟩ := h11 _ hA hSp (actProd Zp actX) p.P hP hK Z₀ o hoe hoi
  refine ⟨Zp, ιz, X'', hst, orbitInput_of_closed _ Z₀ (Subfunctor.lift o hle) hcl ?_, hZe, hιm,
    hop, hE⟩
  intro T h a
  have hinj : Function.Injective (X''.ι.app T) :=
    (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 inferInstance T)
  apply hinj
  rw [actOfMono_spec]
  exact hoe h a

end AlgMag.ChartPoint

#print axioms AlgMag.ChartPoint.finite_of_chartPoint
#print axioms AlgMag.ChartPoint.exists_orbitInput_of_lemma11
