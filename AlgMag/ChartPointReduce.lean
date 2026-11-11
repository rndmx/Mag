/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartPointFinal
import AlgMag.ChartStatement
import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms

/-!
# The rational point reduction (chart-lemma proof, §1)

`k` a finite field, `S` affine. `Z' = Spec Γ(S)[t]/(t^q - t)[1/(q t^{q-1} - 1)]` is étale over `S`,
and `Spec k → Z'` is a monomorphism for `t ↦` a generator of `kˣ`. On `X' = X ×_S Z'` the point `x`
becomes `k`-rational in the sense that `X' → Z'` is invariant and `Spec k → Z'` is a monomorphism,
the hypothesis of `AlgMag.ChartPoint.exists_orbit_mono`.

The note takes `f` lifting a minimal polynomial; `t^q - t` is a shorter choice with the same
properties at `x`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Polynomial

universe u

namespace AlgMag.ChartPoint

open ChartMain

section Ring

/-- The standard étale pair `(t^q - t, derivative)`. -/
noncomputable def finPair (A : Type*) [CommRing A] (q : ℕ) (hq : 2 ≤ q) : StandardEtalePair A where
  f := (Polynomial.X : A[X]) ^ q - Polynomial.X
  monic_f := by
    apply monic_X_pow_sub
    exact lt_of_le_of_lt degree_X_le (by exact_mod_cast (by omega : 1 < q))
  g := derivative ((Polynomial.X : A[X]) ^ q - Polynomial.X)
  cond := ⟨1, 0, 1, by simp⟩

lemma exists_field_generator (k : Type*) [Field k] [Finite k] :
    ∃ α : k, ∀ y : k, y = 0 ∨ ∃ n : ℕ, y = α ^ n := by
  have : Finite kˣ := inferInstance
  obtain ⟨a, ha⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := kˣ)
  have hgen : ∀ u : kˣ, u ∈ Submonoid.powers a := by
    intro u
    have hmem : u ∈ Subgroup.zpowers a := by
      have hc : Nat.card (Subgroup.zpowers a) = Nat.card kˣ := by
        rw [Nat.card_zpowers, ha]
      rw [Subgroup.eq_top_of_card_eq _ hc]
      trivial
    rw [mem_powers_iff_mem_zpowers]
    exact hmem
  refine ⟨a, fun y => ?_⟩
  by_cases hy : y = 0
  · exact Or.inl hy
  · refine Or.inr ?_
    obtain ⟨n, hn⟩ := hgen (Units.mk0 y hy)
    refine ⟨n, ?_⟩
    have := congrArg (Units.val) hn
    simpa using this.symm

/-- The surjection `P.Ring → k`. -/
theorem exists_finPair_lift (A : Type*) [CommRing A] (k : Type*) [Field k] [Finite k] [Algebra A k]
    (q : ℕ) (hq : 2 ≤ q) (hqk : q = Nat.card k) :
    ∃ ψ : (finPair A q hq).Ring →ₐ[A] k, Function.Surjective ψ := by
  obtain ⟨α, hα⟩ := exists_field_generator k
  have := Fintype.ofFinite k
  have hcard : q = Fintype.card k := by rw [hqk, Nat.card_eq_fintype_card]
  obtain ⟨p, hp⟩ := CharP.exists k
  have hc0 : ((q : ℕ) : k) = 0 := by
    rw [hcard]; exact FiniteField.cast_card_eq_zero k
  have hm : (finPair A q hq).HasMap α := by
    refine ⟨?_, ?_⟩
    · change aeval α ((Polynomial.X : A[X]) ^ q - Polynomial.X) = 0
      simp [hcard, FiniteField.pow_card]
    · change IsUnit (aeval α (derivative ((Polynomial.X : A[X]) ^ q - Polynomial.X)))
      have : aeval α (derivative ((Polynomial.X : A[X]) ^ q - Polynomial.X)) = -1 := by
        simp [derivative_X_pow, hc0]
      rw [this]
      exact isUnit_one.neg
  refine ⟨(finPair A q hq).lift α hm, fun y => ?_⟩
  rcases hα y with rfl | ⟨n, rfl⟩
  · exact ⟨0, map_zero _⟩
  · exact ⟨(finPair A q hq).X ^ n, by rw [map_pow, StandardEtalePair.lift_X]⟩

end Ring

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- `T → S/S`. -/
noncomputable abbrev toTop (T : BigFppfOver B S hS) : T ⟶ siteTop (B := B) (S := S) (hS := hS) :=
  Over.mkIdTerminal.from T

section Zp

instance instAffineTop [IsAffine S] : IsAffine ((SCH).obj (siteTop (B := B) (S := S) (hS := hS))) :=
  inferInstanceAs (IsAffine S)

/-- **§1, rational point reduction, base**: for `P = Spec k`, `k` finite, there is `Z'` étale over
`S` with a monomorphism `P → Z'`. -/
theorem exists_Zp [IsAffine S] {P : BigFppfOver B S hS} [IsAffine ((SCH).obj P)]
    (hK : IsField (RT P)) (hfin : Finite (RT P)) :
    ∃ (Zp : BigFppfOver B S hS) (ιz : P ⟶ Zp), IsAffine ((SCH).obj Zp) ∧ Mono ιz ∧
      Etale ((SCH).map (toTop Zp)) := by
  letI : Field (RT P) := hK.toField
  let A := RT (siteTop (B := B) (S := S) (hS := hS))
  letI alg : Algebra A (RT P) := ((SCH).map (toTop P)).appTop.hom.toAlgebra
  have h2 : 2 ≤ Nat.card (RT P) := Finite.one_lt_card
  obtain ⟨ψ, hψ⟩ := exists_finPair_lift A (RT P) _ h2 rfl
  let R := (finPair A _ h2).Ring
  have hC : B.Contains (Spec (.of R)) :=
    contains_ft A R (contains_RT (siteTop (B := B) (S := S) (hS := hS)))
  let Zp : BigFppfOver B S hS := spObj siteTop (algebraMap A R) hC
  have hcomp : (ψ : R →+* RT P).comp (algebraMap A R) = ((SCH).map (toTop P)).appTop.hom :=
    ψ.comp_algebraMap
  let ι : P ⟶ Zp := spLift siteTop (algebraMap A R) hC (toTop P) ψ hcomp
  refine ⟨Zp, ι, inferInstance, ⟨?_⟩, ?_⟩
  · intro T a b hab
    refine site_hom_ext (toAffine_ext (RingHom.ext fun y => ?_))
    obtain ⟨r, rfl⟩ := hψ y
    have e := spLift_appTop siteTop (algebraMap A R) hC (toTop P) (ψ : R →+* RT P) hcomp r
    have hab' := congrArg (fun l => ((SCH).map l).appTop.hom (spSec siteTop (algebraMap A R) hC r)) hab
    simp only [Functor.map_comp, Scheme.Hom.comp_appTop] at hab'
    change ((SCH).map a).appTop.hom (ψ r) = ((SCH).map b).appTop.hom (ψ r)
    rw [← show ((SCH).map ι).appTop.hom (spSec siteTop (algebraMap A R) hC r) = ψ r from e]
    exact hab'
  · have ht : toTop Zp = spToT siteTop (algebraMap A R) hC := Over.mkIdTerminal.hom_ext _ _
    rw [ht]
    change Etale (Spec.map (CommRingCat.ofHom (algebraMap A R)) ≫
      ((SCH).obj (siteTop (B := B) (S := S) (hS := hS))).isoSpec.inv)
    have : Etale (Spec.map (CommRingCat.ofHom (algebraMap A R))) := by
      rw [HasRingHomProperty.Spec_iff (P := @Etale)]
      exact (RingHom.etale_algebraMap (R := A) (S := R)).2 inferInstance
    infer_instance

end Zp

section Prod

variable (Zp : BigFppfOver B S hS)

variable (X) in
/-- `X' = X ×_S Z'`. -/
noncomputable abbrev XP : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  FunctorToTypes.prod X (yoneda.obj Zp)

/-- The action on `X ×_S Z'`, through the first factor. -/
def actProd (actX : AAction (fppfO B S hS) M X) : AAction (fppfO B S hS) M (XP X Zp) where
  smul h x := (actX.smul h x.1, x.2)
  one_smul x := Prod.ext (actX.one_smul _) rfl
  mul_smul g h x := Prod.ext (actX.mul_smul g h _) rfl
  map_smul f h x := Prod.ext (actX.map_smul f h _) rfl

lemma actProd_fst (actX : AAction (fppfO B S hS) M X) :
    IsEquivariant (actProd Zp actX) actX (FunctorToTypes.prod.fst (F := X) (G := yoneda.obj Zp)) :=
  fun _ _ => rfl

/-- `X ×_S Z'` is the fibre product. -/
theorem isPullback_XP : IsPullback (FunctorToTypes.prod.snd (F := X) (G := yoneda.obj Zp))
    (FunctorToTypes.prod.fst (F := X) (G := yoneda.obj Zp)) (yoneda.map (toTop Zp)) (toBase X) := by
  refine ⟨⟨?_⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => FunctorToTypes.prod.lift s.snd s.fst) (fun s => rfl) (fun s => rfl) ?_⟩⟩
  · ext T x
    exact Over.mkIdTerminal.hom_ext _ _
  · intro s m h₁ h₂
    ext T x
    · exact congrArg (fun z => z.app T x) h₂
    · exact congrArg (fun z => z.app T x) h₁

variable {Zp}

/-- `X ×_S Z'` is an algebraic space, étale over `X`, separated over `S`. -/
theorem xp_props [IsAffine S] [IsAffine ((SCH).obj Zp)] (hX : IsAlgebraicSpace B S hS X)
    (hsep : Space.IsSeparatedOver B S hS X) (he : Etale ((SCH).map (toTop Zp))) :
    IsAlgebraicSpace B S hS (XP X Zp) ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH)))
        (FunctorToTypes.prod.fst (F := X) (G := yoneda.obj Zp)) ∧
      Space.IsSeparatedOver B S hS (XP X Zp) := by
  have sq := isPullback_XP (X := X) Zp
  have hterm : IsTerminal (yoneda.obj (siteTop (B := B) (S := S) (hS := hS))) :=
    Limits.IsTerminal.isTerminalObj yoneda _ Over.mkIdTerminal
  refine ⟨?_, ?_, ?_⟩
  · exact Space.isAlgebraicSpace_of_iso B S hS sq.isoPullback.symm
      (isAlgebraicSpace_pullback B S hS _ _ (isAlgebraicSpace_yoneda B S hS _) hX
        (isAlgebraicSpace_yoneda B S hS _))
  · have h1 : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) (yoneda.map (toTop Zp)) :=
      Space.presheaf_yoneda_map_of_inverseImage B S hS inferInstance _ he
    have : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))).IsStableUnderBaseChange :=
      MorphismProperty.relative_isStableUnderBaseChange _
    exact MorphismProperty.of_isPullback sq h1
  · have hbase : Space.IsSeparated B S hS (toBase X) :=
      (Space.isSeparatedOver_iff_isSeparated_of_isTerminal B S hS hterm (toBase X)).1 hsep
    have hsnd : Space.IsSeparated B S hS
        (FunctorToTypes.prod.snd (F := X) (G := yoneda.obj Zp)) :=
      by
        have h0 := Space.isSeparated_pullback B S hS (toBase X) (yoneda.map (toTop Zp)) hbase
        have e : Arrow.mk (FunctorToTypes.prod.snd (F := X) (G := yoneda.obj Zp)) ≅
            Arrow.mk (pullback.snd (toBase X) (yoneda.map (toTop Zp))) :=
          Arrow.isoMk sq.flip.isoPullback (Iso.refl _) (by simp)
        exact (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.diagonal
          (MorphismProperty.presheaf (MorphismProperty.inverseImage
            (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) (SCH)))) e).2 h0
    have hsY : Space.IsSeparatedOver B S hS (yoneda.obj Zp) := by
      refine (Space.isSeparatedOver_iff_isSeparated_of_isTerminal B S hS hterm
        (yoneda.map (toTop Zp))).2 ((Space.isSeparated_yoneda_map_iff B S hS _).2 ?_)
      have := isAffineHom_of_isAffine ((SCH).map (toTop Zp))
      infer_instance
    exact Space.isSeparatedOver_of_isSeparated B S hS hsY hsnd

/-- **§1, "compose the final chart with the étale equivariant map to `X`"**: a chart of `X ×_S Z'`
at a point above `x` is a chart of `X` at `x`. -/
theorem isChartAt_of_XP (actX : AAction (fppfO B S hS) M X) (p : AlgMag.ChartPoint X)
    (hprod : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH)))
        (FunctorToTypes.prod.fst (F := X) (G := yoneda.obj Zp)))
    {U : BigFppfOver B S hS} (actU : AAction (fppfO B S hS) M (yoneda.obj U))
    (f : yoneda.obj U ⟶ XP X Zp) (u : p.P ⟶ U) (haff : IsAffine ((SCH).obj U))
    (heq : IsEquivariant actU (actProd Zp actX) f)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) f)
    (hover : yoneda.map u ≫ f ≫ FunctorToTypes.prod.fst = p.x)
    (hstab : ∀ {T : BigFppfOver B S hS} (t : T ⟶ p.P) (h : APt (fppfO B S hS) M (op T)),
      (actProd Zp actX).smul h (f.app (op T) (t ≫ u)) = f.app (op T) (t ≫ u) →
        actU.smul h (t ≫ u) = t ≫ u) :
    IsChartAt actX p U actU (f ≫ FunctorToTypes.prod.fst) u where
  affine := haff
  equivariant := fun {T} h x => by
    change (f.app T (actU.smul h x)).1 = _
    rw [heq]
    rfl
  etale := by
    have : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (SCH)).IsStableUnderComposition := ⟨fun f g hf hg => by
      change Etale _
      rw [Functor.map_comp]
      have : Etale ((SCH).map f) := hf
      have : Etale ((SCH).map g) := hg
      infer_instance⟩
    exact MorphismProperty.comp_mem _ _ _ he hprod
  lies_over := hover
  stabilizer := fun {T} t h hfix => hstab t h (Prod.ext hfix rfl)

end Prod

end AlgMag.ChartPoint

#print axioms AlgMag.ChartPoint.exists_Zp
#print axioms AlgMag.ChartPoint.xp_props
#print axioms AlgMag.ChartPoint.isChartAt_of_XP
