/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartPointLemma11
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# §1 of the chart-lemma proof, unconditional

* `orbit_lfp`: the orbit map is locally of finite presentation, for `S` of finite type over `ℤ`.
* `exists_orbitInput`: the reduction to `X ×_S Z'`, the stable open, the `OrbitInput`, and the clause
  that the orbit contains the lift of `p`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.ChartPoint

open ChartMain

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- The structure morphism to `Spec ℤ`. -/
noncomputable def toZ (V : BigFppfOver B S hS) : (SCH).obj V ⟶ Spec (.of (ULift.{u} ℤ)) :=
  (SCH).map (toTop V) ≫ terminal.from ((SCH).obj (siteTop (B := B) (S := S) (hS := hS))) ≫
    (terminalIsoIsTerminal specULiftZIsTerminal.{u}).hom

lemma comp_toZ {V V' : BigFppfOver B S hS} (r : V' ⟶ V) : (SCH).map r ≫ toZ V = toZ V' := by
  simp only [toZ, ← Category.assoc, ← Functor.map_comp]
  congr 3
  exact Over.mkIdTerminal.hom_ext _ _

instance : IsNoetherianRing (ULift.{u} ℤ) :=
  isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm

variable {M : Type u} [AddCommGroup M] [AddMonoid.FG M] {P : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj P)] {N : AddSubgroup M} [AddMonoid.FG N]

variable [IsAffine S] {o : yoneda.obj (Ob P N) ⟶ X}

set_option backward.isDefEq.respectTransparency.types false in
/-- Mathlib's "fpqc descent implies fppf descent", for `LocallyOfFinitePresentation`. -/
lemma lfp_descends : MorphismProperty.DescendsAlong (@LocallyOfFinitePresentation.{u})
    (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) := by
  haveI : IsZariskiLocalAtTarget (@LocallyOfFinitePresentation.{u}) :=
    @HasRingHomProperty.instIsZariskiLocalAtTarget _ _ inferInstance
  apply IsZariskiLocalAtTarget.descendsAlong
  rintro R X Y f g ⟨⟨h₁, h₂⟩, h₃⟩ H
  obtain ⟨V : X.Opens, hV, e⟩ := f.isOpenMap.exists_opens_image_eq_of_prespectralSpace
    f.continuous (by simp) isOpen_univ isCompact_univ
  refine MorphismProperty.of_isPullback_of_descendsAlong (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (.paste_vert (.of_hasPullback V.ι _) (.of_hasPullback f g)) ⟨⟨?_, inferInstance⟩,
      (quasiCompact_iff_compactSpace _).mpr (isCompact_iff_compactSpace.mp hV)⟩ ?_
  · exact ⟨fun x ↦ have ⟨y, hyV, e⟩ := e.ge (Set.mem_univ x); ⟨⟨y, hyV⟩, e⟩⟩
  · exact IsZariskiLocalAtTarget.of_isPullback (.flip <| .of_hasPullback _ _) H

/-- The orbit map is locally of finite presentation: all charts are of finite type over `ℤ`, and
this descends along an étale cover of the test scheme. -/
theorem orbit_lfp (hX : IsAlgebraicSpace B S hS X) (hsep : AlgMag.IsSeparatedOver X)
    (hO : LocallyOfFiniteType (toZ (Ob P N)))
    (hU : ∀ (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) φ → LocallyOfFiniteType (toZ U)) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u}) (SCH))) o := by
  have : HasPullbacks (BigFppfOver B S hS) := hasPullbacks_bigFppfOver B S hS
  have : PreservesLimitsOfShape WalkingCospan (SCH) :=
    preservesPullbacks_bigFppfOverToScheme B S hS
  obtain ⟨U, φ, hs, he⟩ := hX.exists_atlas
  have hLU := hU U φ he
  haveI : IsLocallyNoetherian ((SCH).obj U) := LocallyOfFiniteType.isLocallyNoetherian (toZ U)
  -- the chart
  obtain ⟨E, pE, wE, -, sqE⟩ := exists_pull hsep o φ
  have hpE : Etale ((SCH).map pE) := he.property _ _ _ sqE.flip
  have hwE : LocallyOfFinitePresentation ((SCH).map wE) := by
    rw [LocallyOfFinitePresentation.iff_locallyOfFiniteType]
    have h1 : LocallyOfFiniteType ((SCH).map wE ≫ toZ U) := by
      rw [comp_toZ, ← comp_toZ pE]
      infer_instance
    exact locallyOfFiniteType_of_comp _ (toZ U)
  haveI : MorphismProperty.RespectsIso (@LocallyOfFinitePresentation.{u}) :=
    MorphismProperty.respectsIso_of_isStableUnderComposition
      (fun _ _ f (_ : IsIso f) => inferInstance)
  haveI : IsZariskiLocalAtTarget (@LocallyOfFinitePresentation.{u}) :=
    @HasRingHomProperty.instIsZariskiLocalAtTarget _ _ inferInstance
  haveI : (MorphismProperty.inverseImage (@LocallyOfFinitePresentation.{u} :
      MorphismProperty Scheme.{u}) (SCH)).RespectsIso :=
    MorphismProperty.RespectsIso.of_respects_arrow_iso _ fun f g e hf =>
      (MorphismProperty.arrow_mk_iso_iff (@LocallyOfFinitePresentation.{u})
        ((SCH).mapArrow.mapIso e)).1 hf
  refine MorphismProperty.relative.of_exists fun T g => ?_
  obtain ⟨W, p, w, -, sq⟩ := exists_pull hsep o g
  refine ⟨W, yoneda.map p, w, sq, ?_⟩
  let T1 := he.rep.pullback g
  let sn : T1 ⟶ T := he.rep.snd g
  have sq1 : IsPullback (he.rep.fst g) (yoneda.map sn) φ g := he.rep.isPullback g
  obtain ⟨toU, htoU⟩ := yoneda.map_surjective (he.rep.fst g)
  have sq1' : IsPullback (yoneda.map toU) (yoneda.map sn) φ g := by rw [htoU]; exact sq1
  have hsnE : Etale ((SCH).map sn) := he.property _ _ _ sq1'
  have hsnS : Surjective ((SCH).map sn) := hs.property _ _ _ sq1'
  let W1 := pullback w sn
  let a : W1 ⟶ W := pullback.fst w sn
  let b : W1 ⟶ T1 := pullback.snd w sn
  have hA : IsPullback a b w sn := IsPullback.of_hasPullback _ _
  have h0 : o.app (op W1) (a ≫ p) = φ.app (op W1) (b ≫ toU) := by
    rw [hom_nat, pb_comm sq, ← hom_nat, hA.w, hom_nat, ← pb_comm sq1', ← hom_nat]
  obtain ⟨k, hk1, hk2⟩ := pb_lift sqE _ _ h0
  have hsqY : IsPullback (yoneda.map k) (yoneda.map b) (yoneda.map wE) (yoneda.map toU) := by
    refine pb_mk hk2 ?_ ?_
    · intro V x y hxy
      have hxy' : x ≫ wE = y ≫ toU := hxy
      have e6 : o.app (op V) (x ≫ pE) = g.app (op V) (y ≫ sn) := by
        rw [hom_nat, pb_comm sqE, ← hom_nat, hxy', hom_nat, pb_comm sq1', ← hom_nat]
      obtain ⟨l0, hl1, hl2⟩ := pb_lift sq _ _ e6
      refine ⟨hA.lift l0 y hl2, pb_ext sqE ?_ ?_, hA.lift_snd _ _ _⟩
      · rw [Category.assoc, hk1, ← Category.assoc, hA.lift_fst, hl1]
      · rw [Category.assoc, hk2, ← Category.assoc, hA.lift_snd, hxy']
    · intro V l l' h1 h2
      have h1' : l ≫ k = l' ≫ k := h1
      have h2' : l ≫ b = l' ≫ b := h2
      refine hA.hom_ext (pb_ext sq ?_ ?_) h2'
      · rw [Category.assoc, Category.assoc, ← hk1, ← Category.assoc, ← Category.assoc, h1']
      · rw [Category.assoc, Category.assoc, hA.w, ← Category.assoc, ← Category.assoc, h2']
  have hsqS : IsPullback k b wE toU :=
    IsPullback.of_map yoneda hk2 (by simpa using hsqY)
  have hb : LocallyOfFinitePresentation ((SCH).map b) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) (hsqS.map (SCH)) hwE
  have hAS := (hA.map (SCH)).flip
  haveI := lfp_descends.{u}
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @LocallyOfFinitePresentation) (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)
    hAS ⟨⟨hsnS, inferInstance⟩, inferInstance⟩ hb

/-- **§1 of the chart-lemma proof.** For a closed point `p` of `X`, `S` affine of finite
type over `ℤ`, `X` separated of finite type over `S`: there is `Z'` étale over `S` and a stable open
`X'' ⊆ X ×_S Z'` with an `OrbitInput` whose orbit contains the lift of `p`. -/
theorem exists_orbitInput (hSft : LocallyOfFiniteType (terminal.from S))
    (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X)
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
  obtain ⟨hA, hE, hSp⟩ := xp_props (X := X) hX hsep hZe
  have hs' := isSeparatedOver_of_space hSp
  let x' : yoneda.obj p.P ⟶ XP X Zp := FunctorToTypes.prod.lift p.x (yoneda.map ιz)
  let act' := actProd Zp actX
  obtain ⟨Z₀, hZ⟩ := exists_stabilizer hK hs' act' x'
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
  have hlfp := orbit_lfp (o := o) hA hs' hO hUlft
  obtain ⟨X'', hle, hop, hst, hcl⟩ := lemma11 hA hs' hK act' hoe hoi hlfp
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

#print axioms AlgMag.ChartPoint.exists_orbitInput
