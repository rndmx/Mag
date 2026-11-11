/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartPointOrbitInput
import AlgMag.ChartQSStratPoint
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# The point and the orbit, for quasi-separated `X`

Part of the proof of **Theorem 6.8 (ii)** (= Theorem A.2 (ii)) of Algebraic Magnetism (Mayeux,
Semigroup Forum 113 (2026)), through the specialization to `D(M)` of Alper–Hall–Rydh, Corollary 10.2.
This file gives the reduction to a closed point and its orbit.

`exists_orbitInput_qs` is `exists_orbitInput` with `X` quasi-separated. The stabilizer of the closed
point is `exists_stabilizer_closedPoint`; `Lemma11QS` is the named hypothesis that the
orbit map is a closed immersion after shrinking `X` to a stable open; it includes `o` locally of finite presentation (`orbit_lfp`).
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.ChartPoint

open ChartMain AlgMag.ChartQSStrat

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

variable (B S hS) in
/-- **Named hypothesis, orbit lemma** for quasi-separated `X`: `lemma11` and `orbit_lfp` with
`toBase X` quasi-separated in place of `X` separated. -/
def Lemma11QS [IsAffine S] : Prop :=
  ∀ {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {M : Type u} [AddCommGroup M] [AddMonoid.FG M]
    {P : BigFppfOver B S hS} [IsAffine ((SCH).obj P)] {N : AddSubgroup M} [AddMonoid.FG N],
    IsAlgebraicSpace B S hS X → Space.IsQuasiSeparated B S hS (toBase X) → IsField (RT P) →
    ∀ (actX : AAction (fppfO B S hS) M X) (o : yoneda.obj (Ob P N) ⟶ X),
    IsEquivariant (oAct N) actX o →
    (∀ {T : BigFppfOver B S hS} (a b : T ⟶ Ob P N), o.app (op T) a = o.app (op T) b → a = b) →
    LocallyOfFiniteType (toZ (Ob P N)) →
    (∀ (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) φ → LocallyOfFiniteType (toZ U)) →
    ∃ (X' : Subfunctor X) (hle : Subfunctor.range o ≤ X'),
      Space.IsOpenSubspace B S hS X' ∧
      (∀ {T : (BigFppfOver B S hS)ᵒᵖ} (h : APt (fppfO B S hS) M T) (x : X'.toFunctor.obj T),
        ∃ y, X'.ι.app T y = actX.smul h (X'.ι.app T x)) ∧
      ClosedP (Subfunctor.lift o hle)

/-- The diagonal of `Y → G` is a base change of the diagonal of `X → G'`, for a monomorphism
`Y → X` over `G → G'`. -/
theorem diagPb {C : Type*} [Category C] [HasPullbacks C]
    {Y X G G' : C} (ι : Y ⟶ X) [Mono ι] (r : Y ⟶ G) (e : X ⟶ G') (a : G ⟶ G') (h : r ≫ a = ι ≫ e) :
    IsPullback ι (pullback.diagonal r) (pullback.diagonal e)
      (pullback.lift (pullback.fst r r ≫ ι) (pullback.snd r r ≫ ι)
        (by simp only [Category.assoc, ← h]; rw [← Category.assoc, pullback.condition,
          Category.assoc]) : pullback r r ⟶ pullback e e) := by
  set k : pullback r r ⟶ pullback e e := pullback.lift (pullback.fst r r ≫ ι) (pullback.snd r r ≫ ι)
    (by simp only [Category.assoc, ← h]; rw [← Category.assoc, pullback.condition,
      Category.assoc]) with hk
  have k1 : k ≫ pullback.fst e e = pullback.fst r r ≫ ι := pullback.lift_fst _ _ _
  have k2 : k ≫ pullback.snd e e = pullback.snd r r ≫ ι := pullback.lift_snd _ _ _
  have w : ι ≫ pullback.diagonal e = pullback.diagonal r ≫ k := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id, k1]
      rw [← Category.assoc, pullback.diagonal_fst, Category.id_comp]
    · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id, k2]
      rw [← Category.assoc, pullback.diagonal_snd, Category.id_comp]
  refine IsPullback.of_isLimit' ⟨w⟩ ?_
  have eqs : ∀ c : PullbackCone (pullback.diagonal e) k,
      c.fst = c.snd ≫ pullback.fst r r ≫ ι ∧ c.fst = c.snd ≫ pullback.snd r r ≫ ι := by
    intro c
    have q := c.condition
    constructor
    · have e1 := congrArg (· ≫ pullback.fst e e) q
      simpa only [Category.assoc, pullback.diagonal_fst, Category.comp_id, k1] using e1
    · have e1 := congrArg (· ≫ pullback.snd e e) q
      simpa only [Category.assoc, pullback.diagonal_snd, Category.comp_id, k2] using e1
  have same : ∀ c : PullbackCone (pullback.diagonal e) k,
      c.snd ≫ pullback.fst r r = c.snd ≫ pullback.snd r r := fun c => by
    rw [← cancel_mono ι, Category.assoc, Category.assoc, ← (eqs c).1, ← (eqs c).2]
  refine PullbackCone.IsLimit.mk _ (fun c => c.snd ≫ pullback.fst r r) ?_ ?_ ?_
  · intro c
    rw [Category.assoc, ← (eqs c).1]
  · intro c
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
    · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, same c]
  · intro c m h1 h2
    rw [← h2, Category.assoc, pullback.diagonal_fst, Category.comp_id]

section Reduce
variable [IsAffine S] {Zp : BigFppfOver B S hS}

/-- The first two clauses of `xp_props`. -/
theorem xp_props_qs [IsAffine ((SCH).obj Zp)] (hX : IsAlgebraicSpace B S hS X) (he : Etale ((SCH).map (toTop Zp))) :
    IsAlgebraicSpace B S hS (XP X Zp) ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH)))
        (FunctorToTypes.prod.fst (F := X) (G := yoneda.obj Zp)) := by
  have sq := isPullback_XP (X := X) Zp
  refine ⟨?_, ?_⟩
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

/-- `X ×_S Z'` is quasi-separated if `X` is. -/
theorem isQuasiSeparated_toBase_XP [IsAffine ((SCH).obj Zp)] (hA : IsAlgebraicSpace B S hS (XP X Zp))
    (hX : IsAlgebraicSpace B S hS X) (hqs : Space.IsQuasiSeparated B S hS (terminal.from X)) :
    Space.IsQuasiSeparated B S hS (toBase (XP X Zp)) := by
  have sq := (isPullback_XP (X := X) Zp).flip
  have hterm : IsTerminal (yoneda.obj (siteTop (B := B) (S := S) (hS := hS))) :=
    Limits.IsTerminal.isTerminalObj yoneda _ Over.mkIdTerminal
  have hTop := isAlgebraicSpace_yoneda B S hS (siteTop (B := B) (S := S) (hS := hS))
  have hZ := isAlgebraicSpace_yoneda B S hS Zp
  have hbase : Space.IsQuasiSeparated B S hS (toBase X) :=
    Space.isQuasiCompact_of_isPullback B S hS
      (diagPb (𝟙 X) (toBase X) (terminal.from X) (terminal.from _) (terminal.hom_ext _ _)) hqs
  let cP : AlgebraicSpaces B S hS := ⟨_, hA⟩
  let cX : AlgebraicSpaces B S hS := ⟨_, hX⟩
  let cZ : AlgebraicSpaces B S hS := ⟨_, hZ⟩
  let cT : AlgebraicSpaces B S hS := ⟨_, hTop⟩
  let a : cP ⟶ cX := ObjectProperty.homMk FunctorToTypes.prod.fst
  let b : cP ⟶ cZ := ObjectProperty.homMk FunctorToTypes.prod.snd
  let v : cX ⟶ cT := ObjectProperty.homMk (toBase X)
  let w : cZ ⟶ cT := ObjectProperty.homMk (yoneda.map (toTop Zp))
  have sq' : IsPullback a b v w :=
    IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ sq.w) sq
  have hsnd : Space.IsQuasiSeparated B S hS (FunctorToTypes.prod.snd (F := X) (G := yoneda.obj Zp)) :=
    (Space.isQuasiSeparated_isStableUnderBaseChange B S hS).of_isPullback sq' hbase
  have hsY : Space.IsQuasiSeparated B S hS (yoneda.map (toTop Zp)) := by
    refine Space.isQuasiSeparated_of_isSeparated B S hS ((Space.isSeparated_yoneda_map_iff B S hS _).2 ?_)
    have := isAffineHom_of_isAffine ((SCH).map (toTop Zp))
    infer_instance
  have e : toBase (XP X Zp) = FunctorToTypes.prod.snd ≫ yoneda.map (toTop Zp) := hterm.hom_ext _ _
  rw [e]
  exact Space.isQuasiSeparated_comp B S hS hA hZ _ _ hsnd hsY

end Reduce

variable [IsAffine S] {M : Type u} [AddCommGroup M] [AddMonoid.FG M]

/-- **The point and the orbit.** For a closed point `p` of `X`, `S` affine of finite
type over `ℤ`, `X` quasi-separated of finite type over `S`: there is `Z'` étale over `S` and a stable open
`X'' ⊆ X ×_S Z'` with an `OrbitInput` whose orbit contains the lift of `p`. -/
theorem exists_orbitInput_qs (hL11 : Lemma11QS B S hS) (hSft : LocallyOfFiniteType (terminal.from S))
    (hX : IsAlgebraicSpace B S hS X) (hqs : Space.IsQuasiSeparated B S hS (terminal.from X))
    (hft : Space.IsFiniteType B S hS (terminal.from X))
    (actX : AAction (fppfO B S hS) M X) (p : AlgMag.ChartPoint X) :
    ∃ (Zp : BigFppfOver B S hS) (ιz : p.P ⟶ Zp) (X'' : Subfunctor (XP X Zp))
      (hst : ∀ {T : (BigFppfOver B S hS)ᵒᵖ} (h : APt (fppfO B S hS) M T)
        (x : X''.toFunctor.obj T),
        ∃ y, X''.ι.app T y = (actProd Zp actX).smul h (X''.ι.app T x))
      (D : OrbitInput (actOfMono (actProd Zp actX) X''.ι hst)) (u : p.P ⟶ D.O),
      Etale ((SCH).map (toTop Zp)) ∧ Mono ιz ∧ Space.IsOpenSubspace B S hS X'' ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH)))
        (FunctorToTypes.prod.fst (F := X) (G := yoneda.obj Zp)) ∧
      yoneda.map u ≫ D.j ≫ X''.ι = FunctorToTypes.prod.lift p.x (yoneda.map ιz) := by
  have hK := isField_of_chartPoint p
  haveI hP := isAffine_of_chartPoint p
  have hfin := finite_of_chartPoint hSft hX hft p
  obtain ⟨Zp, ιz, hZa, hιm, hZe⟩ := exists_Zp (P := p.P) hK hfin
  haveI := hZa
  haveI := hιm
  obtain ⟨hA, hE⟩ := xp_props_qs (X := X) hX hZe
  have hs' := isQuasiSeparated_toBase_XP (X := X) hA hX hqs (Zp := Zp)
  let x' : yoneda.obj p.P ⟶ XP X Zp := FunctorToTypes.prod.lift p.x (yoneda.map ιz)
  let act' := actProd Zp actX
  obtain ⟨Z₀, hZ₀⟩ := exists_stabilizer_closedPoint hK actX p.x p.isClosed
  have hZ : ∀ {T : BigFppfOver B S hS} (t : T ⟶ p.P) (h : Multiplicative M →* Γ((SCH).obj T, ⊤)),
      act'.smul (U := op T) h (x'.app (op T) t) = x'.app (op T) t ↔
        ∀ z ∈ Z₀, h (Multiplicative.ofAdd z) = 1 := by
    intro T t h
    rw [← hZ₀ t h]
    constructor
    · intro e
      exact congrArg Prod.fst e
    · intro e
      exact Prod.ext e rfl
  haveI hfg : AddMonoid.FG Z₀ := fg_addSubgroup Z₀
  obtain ⟨o, ho⟩ := exists_orbit (N := Z₀) hK hA hZ
  have hoe : IsEquivariant (oAct Z₀) act' o := orbit_equivariant hK hA ho
  have hoi : ∀ {T : BigFppfOver B S hS} (a b : T ⟶ Ob p.P Z₀),
      o.app (op T) a = o.app (op T) b → a = b := fun a b hab =>
    orbit_injective hK hA hZ ho FunctorToTypes.prod.snd (fun _ _ => rfl) ιz rfl a b hab
  -- finiteness
  have hSft' : LocallyOfFiniteType (terminal.from ((SCH).obj (siteTop (B := B) (S := S) (hS := hS)))) :=
    hSft
  have hPZ : LocallyOfFiniteType (toZ p.P) := by
    refine (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).2 ?_
    classical
    haveI : Fintype (RT p.P) := @Fintype.ofFinite _ hfin
    letI := (toZ p.P).appTop.hom.toAlgebra
    refine (⟨⟨Finset.univ, ?_⟩⟩ : Algebra.FiniteType Γ(Spec (.of (ULift.{u} ℤ)), ⊤) (RT p.P))
    rw [eq_top_iff]
    intro x _
    exact Algebra.subset_adjoin (by simp)
  have hO : LocallyOfFiniteType (toZ (Ob p.P Z₀)) := by
    have e : toZ (Ob p.P Z₀) = (SCH).map (Oπ p.P Z₀) ≫ toZ p.P := (comp_toZ _).symm
    rw [e]
    have : LocallyOfFiniteType ((SCH).map (Oπ p.P Z₀)) := by
      change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom _) ≫ ((SCH).obj p.P).isoSpec.inv)
      have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
          (AddMonoidAlgebra.singleZeroRingHom : RT p.P →+* RN p.P Z₀))) := by
        rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
        change (algebraMap (RT p.P) (RN p.P Z₀)).FiniteType
        exact (RingHom.finiteType_algebraMap).2 (AddMonoidAlgebra.finiteType_of_fg _ _)
      infer_instance
    infer_instance
  have hUlft : ∀ (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ XP X Zp),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) φ → LocallyOfFiniteType (toZ U) := by
    intro U φ hφ
    have hcomp : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (SCH)).IsStableUnderComposition := ⟨fun f g hf hg => by
      change Etale _
      rw [Functor.map_comp]
      have : Etale ((SCH).map f) := hf
      have : Etale ((SCH).map g) := hg
      infer_instance⟩
    have hφX := MorphismProperty.comp_mem _ _ _ hφ hE
    let T1 : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))
    let hT : IsTerminal T1 := Over.mkIdTerminal
    let hY : IsTerminal (yoneda.obj T1) := Limits.IsTerminal.isTerminalObj yoneda T1 hT
    let bb : yoneda.obj T1 ≅ ⊤_ _ := hY.uniqueUpToIso terminalIsTerminal
    have hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (SCH)).presheaf bb.hom := Space.presheaf_etale_of_iso B S hS bb
    have hl : LocallyOfFiniteType ((SCH).map (hT.from U)) :=
      hft.1 U T1 _ bb.hom (hT.from U) hφX hb (Subsingleton.elim _ _ |>.trans rfl)
    change LocallyOfFiniteType ((SCH).map (toTop U) ≫ _ ≫ _)
    have : LocallyOfFiniteType ((SCH).map (toTop U)) := hl
    infer_instance
  obtain ⟨X'', hle, hop, hst, hcl⟩ := hL11 hA hs' hK act' o hoe hoi hO hUlft
  -- the lift of `p` is in the orbit
  obtain ⟨σ, hσ1, hσ2⟩ := exists_gk_lift (T := p.P) (M := M) (𝟙 p.P) 1
  let u : p.P ⟶ Ob p.P Z₀ := σ ≫ qN Z₀
  have hu : o.app (op p.P) u = x'.app (op p.P) (𝟙 p.P) := by
    have e1 : o.app (op p.P) (σ ≫ qN Z₀) = (orbMap act' x').app (op p.P) σ :=
      congrArg (fun k => k.app (op p.P) σ) ho
    rw [e1, orbMap_app, hσ1, hσ2]
    exact act'.one_smul (U := op p.P) _
  refine ⟨Zp, ιz, X'', hst, orbitInput_of_closed _ Z₀ (Subfunctor.lift o hle) hcl ?_, u, hZe, hιm,
    hop, hE, ?_⟩
  · intro T h a
    have hinj : Function.Injective (X''.ι.app T) := fun _ _ h => Subtype.ext h
    apply hinj
    rw [actOfMono_spec]
    exact hoe h a
  · apply yonedaEquiv.injective
    change o.app (op p.P) (𝟙 p.P ≫ u) = x'.app (op p.P) (𝟙 p.P)
    rw [Category.id_comp, hu]

end AlgMag.ChartPoint

#print axioms AlgMag.ChartPoint.exists_orbitInput_qs
