/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartEffectiveFinal
import StacksFrontier.AlgebraicGeometry.Spaces.MorphismAlgebraizationLocallyFiniteType
import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraizationMorphismSmallerBase
import StacksFrontier.AlgebraicGeometry.Artin.ContractionSituationSmallerBase
import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeTfae
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitQuasiFinitePart
import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms

/-!
# `NoetherianAlgebraization` from Stacks 0GHK, and Theorem 4.1 of the chart-lemma proof

* `AlgMag.ChartMain.noetherianAlgebraization_of_lft`: `X` separated and locally of finite type over
  `S` has `NoetherianAlgebraization`. `X` is re-based to `Spec Γ(W)` by Stacks 04SG and
  `ChartSplit.existsUnique_section_of_algebraization` is applied with Stacks 0GHK.
* `AlgMag.ChartMain.thm41_exists`: Theorem 4.1, existence, from Lemmas 4.2 and 4.3.

The imported Stacks modules are outside the sparse build.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Space

universe u

namespace AlgMag.ChartMain

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

section Rebase

variable {R : Type u} [CommRing R] {hR : B.Contains (Spec (.of R))} {g : B.obj hR ⟶ B.obj hS}
  (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- `X ×_S V` over `V = (Spec R → S)`. -/
noncomputable abbrev rbX (g : B.obj hR ⟶ B.obj hS) :
    Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Over.mk (pullback.fst (terminal.from (yoneda.obj (Over.mk g))) (terminal.from X))

/-- The map from an object over `Spec R` to `V`. -/
noncomputable def rbToV (T : BigFppfOver B (Spec (.of R)) hR) :
    (Over.map g).obj T ⟶ (Over.mk g : BigFppfOver B S hS) :=
  Over.homMk T.hom rfl

/-- The morphism to `X ×_S V` attached to a section of `X`. -/
noncomputable def rbLift (T : BigFppfOver B (Spec (.of R)) hR)
    (x : X.obj (op ((Over.map g).obj T))) :
    yoneda.obj ((Over.map g).obj T) ⟶ (rbX X g).left :=
  pullback.lift (yoneda.map (rbToV T)) (yonedaEquiv.symm x) (terminal.hom_ext _ _)

lemma rbLift_fst (T : BigFppfOver B (Spec (.of R)) hR) (x : X.obj (op ((Over.map g).obj T))) :
    rbLift X T x ≫ (rbX X g).hom = yoneda.map (rbToV T) :=
  pullback.lift_fst _ _ _

lemma rbLift_snd (T : BigFppfOver B (Spec (.of R)) hR) (x : X.obj (op ((Over.map g).obj T))) :
    rbLift X T x ≫ pullback.snd (terminal.from (yoneda.obj (Over.mk g))) (terminal.from X) =
      yonedaEquiv.symm x :=
  pullback.lift_snd _ _ _

/-- A section of `X` over `T → Spec R → S` gives a section of `X_V` over `T`. -/
noncomputable def rbPhi (T : BigFppfOver B (Spec (.of R)) hR) (x : X.obj (op ((Over.map g).obj T))) :
    (overSpecInverse B hS hR g (rbX X g)).obj (op T) :=
  ⟨yonedaEquiv (rbLift X T x), by
    have h := congrArg yonedaEquiv (rbLift_fst X T x)
    rw [yonedaEquiv_comp] at h
    refine h.trans (Over.OverMorphism.ext (Category.id_comp _))⟩

/-- The section of `X` under a section of `X_V`. -/
noncomputable def rbPsi (T : BigFppfOver B (Spec (.of R)) hR)
    (y : (overSpecInverse B hS hR g (rbX X g)).obj (op T)) : X.obj (op ((Over.map g).obj T)) :=
  (pullback.snd (terminal.from (yoneda.obj (Over.mk g))) (terminal.from X)).app _ y.1

lemma rbPsi_rbPhi (T : BigFppfOver B (Spec (.of R)) hR) (x : X.obj (op ((Over.map g).obj T))) :
    rbPsi X T (rbPhi X T x) = x := by
  have h := congrArg yonedaEquiv (rbLift_snd X T x)
  rw [yonedaEquiv_comp, Equiv.apply_symm_apply] at h
  exact h

lemma rbPsi_map {T T' : BigFppfOver B (Spec (.of R)) hR} (f : T' ⟶ T)
    (y : (overSpecInverse B hS hR g (rbX X g)).obj (op T)) :
    rbPsi X T' ((overSpecInverse B hS hR g (rbX X g)).map f.op y) =
      X.map ((Over.map g).map f).op (rbPsi X T y) :=
  NatTrans.naturality_apply
    (pullback.snd (terminal.from (yoneda.obj (Over.mk g))) (terminal.from X))
    ((Over.map g).map f).op y.1

lemma rbPhi_map {T T' : BigFppfOver B (Spec (.of R)) hR} (f : T' ⟶ T)
    (x : X.obj (op ((Over.map g).obj T))) :
    (overSpecInverse B hS hR g (rbX X g)).map f.op (rbPhi X T x) =
      rbPhi X T' (X.map ((Over.map g).map f).op x) := by
  apply Subtype.ext
  have e : yoneda.map ((Over.map g).map f) ≫ rbLift X T x =
      rbLift X T' (X.map ((Over.map g).map f).op x) := by
    apply pullback.hom_ext
    · refine ((Category.assoc _ _ _).trans (congrArg _ (rbLift_fst X T x))).trans ?_
      refine Eq.trans ?_ (rbLift_fst X T' _).symm
      rw [← yoneda.map_comp]
      exact congrArg _ (Over.OverMorphism.ext (by simp [rbToV]))
    · refine ((Category.assoc _ _ _).trans (congrArg _ (rbLift_snd X T x))).trans ?_
      refine Eq.trans ?_ (rbLift_snd X T' _).symm
      apply yonedaEquiv.injective
      rw [← yonedaEquiv_naturality, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have h := yonedaEquiv_naturality (rbLift X T x) ((Over.map g).map f)
  exact h.trans (congrArg yonedaEquiv e)

end Rebase

section Alg

variable (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- `Y → Spec A` is separated and locally of finite type, and `Y` is an algebraic space. -/
lemma rb_props {R : Type u} [CommRing R] {hR : B.Contains (Spec (.of R))} (g : B.obj hR ⟶ B.obj hS)
    (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X)
    (hlft : IsLocallyOfFiniteType B S hS (terminal.from X)) :
    IsAlgebraicSpace B _ hR (overSpecInverse B hS hR g (rbX X g)) ∧
    IsSeparated B _ hR (toYonedaId B (Spec (.of R)) hR (overSpecInverse B hS hR g (rbX X g))) ∧
    IsLocallyOfFiniteType B _ hR
      (toYonedaId B (Spec (.of R)) hR (overSpecInverse B hS hR g (rbX X g))) := by
  have hT : IsAlgebraicSpace B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :=
    isAlgebraicSpace_of_iso B S hS
      ((((Over.mkIdTerminal (X := B.obj hS)).isTerminalObj yoneda _).uniqueUpToIso
        terminalIsTerminal).symm) (isAlgebraicSpace_yoneda B S hS _)
  have hXa : IsAlgebraicSpace B S hS (rbX X g).left :=
    isAlgebraicSpace_pullback B S hS _ _ (isAlgebraicSpace_yoneda B S hS _) hX hT
  have hYa := isAlgebraicSpace_overSpecInverse B (hS := hS) (hR := hR) (g := g) (rbX X g) hXa
  refine ⟨hYa, isSeparated_toYonedaId_overSpecInverse B (rbX X g) hXa
    (isSeparated_pullbackFst B S hS _ (isSeparated_of_isSeparatedOver B S hS hsep _)), ?_⟩
  have hl := isLocallyOfFiniteType_terminal_from_smallerBaseInverse B (Spec (.of R)) S hR hS g
    (rbX X g) (isLocallyOfFiniteType_pullback_fst B S hS hX hT hlft _ _)
  let e := ((Over.mkIdTerminal (X := B.obj hR)).isTerminalObj yoneda _).uniqueUpToIso
    terminalIsTerminal
  have h3 : toYonedaId B (Spec (.of R)) hR (overSpecInverse B hS hR g (rbX X g)) =
      terminal.from _ ≫ e.inv :=
    ((Over.mkIdTerminal (X := B.obj hR)).isTerminalObj yoneda _).hom_ext _ _
  rw [h3]
  have hT' : IsAlgebraicSpace B _ hR (⊤_ ((BigFppfOver B (Spec (.of R)) hR)ᵒᵖ ⥤ Type u)) :=
    isAlgebraicSpace_of_iso B _ hR e.symm (isAlgebraicSpace_yoneda B _ hR _)
  exact isLocallyOfFiniteType_comp B _ hR hYa hT' (isAlgebraicSpace_yoneda B _ hR _) _ _ hl
    (isLocallyOfFiniteType_of_isClosedImmersion B _ hR _
      (MorphismProperty.of_isIso (closedImmersionPresheafProperty B _ hR) e.inv))

set_option maxHeartbeats 4000000 in
/-- **Stacks 0GHK, section form on `X`.** `X` separated and locally of finite type over `S` has
`NoetherianAlgebraization`: re-base to `Spec Γ(W)` by Stacks 04SG, and apply
`ChartSplit.existsUnique_section_of_algebraization`. -/
theorem noetherianAlgebraization_of_lft (hX : IsAlgebraicSpace B S hS X)
    (hsep : Space.IsSeparatedOver B S hS X)
    (hlft : IsLocallyOfFiniteType B S hS (terminal.from X)) : NoetherianAlgebraization X := by
  intro W _ _ I _ x hx
  have hR : B.Contains (Spec (.of (RT W))) := contains_RT W
  let g : B.obj hR ⟶ B.obj hS := ObjectProperty.homMk (((SCH).obj W).isoSpec.inv ≫ W.hom.hom)
  have hSn : ∀ n, B.Contains (adicThickening Γ((SCH).obj W, ⊤) I n) := fun n =>
    have : AlgebraicGeometry.IsClosedImmersion (adicThickeningι Γ((SCH).obj W, ⊤) I n) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    Space.contains_of_isImmersion B hR (adicThickeningι Γ((SCH).obj W, ⊤) I n)
  let base := baseObject Γ((SCH).obj W, ⊤) B hR
  let toW : (Over.map g).obj base ⟶ W := siteHom ((SCH).obj W).isoSpec.inv
    ((Category.id_comp _).symm)
  let frW : W ⟶ (Over.map g).obj base := siteHom ((SCH).obj W).isoSpec.hom (by
    change ((SCH).obj W).isoSpec.hom ≫ 𝟙 _ ≫ ((SCH).obj W).isoSpec.inv ≫ W.hom.hom = W.hom.hom
    simp)
  have hfr : frW ≫ toW = 𝟙 W := siteExt (by
    change ((SCH).obj W).isoSpec.hom ≫ ((SCH).obj W).isoSpec.inv = 𝟙 _
    simp)
  let th := adicThickeningObject Γ((SCH).obj W, ⊤) I B hR hSn
  let tm := adicThickeningMap Γ((SCH).obj W, ⊤) I B hR hSn
  let eN : ∀ n, (Over.map g).obj (th n) ⟶
      Chart.immObj W (Chart.closedι ((SCH).obj W) (I ^ (n + 1))) := fun n =>
    siteHom (𝟙 _) (by
      change 𝟙 _ ≫ (Chart.closedι ((SCH).obj W) (I ^ (n + 1))) ≫ W.hom.hom =
        adicThickeningι _ I n ≫ ((SCH).obj W).isoSpec.inv ≫ W.hom.hom
      simp [Chart.closedι, adicThickeningι])
  let fN : ∀ n, Chart.immObj W (Chart.closedι ((SCH).obj W) (I ^ (n + 1))) ⟶
      (Over.map g).obj (th n) := fun n =>
    siteHom (𝟙 _) (by
      change 𝟙 _ ≫ adicThickeningι _ I n ≫ ((SCH).obj W).isoSpec.inv ≫ W.hom.hom =
        (Chart.closedι ((SCH).obj W) (I ^ (n + 1))) ≫ W.hom.hom
      simp [Chart.closedι, adicThickeningι])
  have hfe : ∀ n, fN n ≫ eN n = 𝟙 _ := fun n => siteExt (by
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    simp)
  have he : ∀ n, eN n ≫ Chart.immι W _ = (Over.map g).map (tm n) ≫ toW := fun n => siteExt (by
    change 𝟙 _ ≫ Chart.closedι ((SCH).obj W) (I ^ (n + 1)) =
      adicThickeningι _ I n ≫ ((SCH).obj W).isoSpec.inv
    simp [Chart.closedι, adicThickeningι])
  have hf : ∀ n, Chart.immι W _ ≫ frW = fN n ≫ (Over.map g).map (tm n) := fun n => siteExt (by
    change Chart.closedι ((SCH).obj W) (I ^ (n + 1)) ≫ ((SCH).obj W).isoSpec.hom =
      𝟙 _ ≫ adicThickeningι _ I n
    simp [Chart.closedι, adicThickeningι])
  obtain ⟨hYa, hsY, hlY⟩ := rb_props (hR := hR) X g hX hsep hlft
  let y : ∀ n, yoneda.obj (th n) ⟶ overSpecInverse B hS hR g (rbX X g) := fun n =>
    yonedaEquiv.symm (rbPhi X (th n) (X.map (eN n).op (x (n + 1))))
  have hterm := (Over.mkIdTerminal (X := B.obj hR)).isTerminalObj yoneda _
  have hyc : ∀ n, yoneda.map (adicThickeningSuccMap _ I B hR hSn n) ≫ y (n + 1) = y n := by
    intro n
    apply yonedaEquiv.injective
    simp only [y]
    rw [← yonedaEquiv_naturality, Equiv.apply_symm_apply, Equiv.apply_symm_apply, rbPhi_map]
    congr 1
    obtain ⟨t, ht⟩ := exists_factor_closed (Chart.immι W (Chart.closedι ((SCH).obj W) (I ^ (n + 1))))
      (I ^ (n + 1 + 1)) (fun c hc => closedι_appTop_of_mem _
        (Ideal.pow_le_pow_right (Nat.le_succ _) hc))
    rw [← hx (n + 1) (n + 1 + 1) t ht, ← Functor.map_comp_apply, ← Functor.map_comp_apply,
      ← op_comp, ← op_comp]
    have := mono_immι (T := W) (I ^ (n + 1 + 1))
    have hc : (Over.map g).map (adicThickeningSuccMap _ I B hR hSn n) ≫ eN (n + 1) = eN n ≫ t := by
      refine (cancel_mono (Chart.immι W _)).1 ?_
      rw [Category.assoc, he, Category.assoc, ht, he, ← Category.assoc, ← Functor.map_comp]
      exact congrArg (· ≫ toW) (congrArg _ (adicThickeningSuccMap_adicThickeningMap _ I B hR hSn n))
    exact congrArg (fun k => X.map k.op (x (n + 1 + 1))) hc
  obtain ⟨s, ⟨-, hs2⟩, huniq⟩ := ChartSplit.existsUnique_section_of_algebraization
    (fun g' hg hgc => existsUnique_adicFibreMap_eq_of_isLocallyOfFiniteType
      (isAlgebraicSpace_yoneda B _ hR base) hYa (𝟙 _) (toYonedaId B _ hR _)
      (isProper_of_isIso B _ hR (𝟙 _)) hsY hlY g' hg hgc) y
    (fun n => hterm.hom_ext _ _) hyc
  let P := rbPsi X base (yonedaEquiv s)
  have hP : ∀ n, X.map ((Over.map g).map (tm n)).op P = X.map (eN n).op (x (n + 1)) := by
    intro n
    rw [← rbPsi_map]
    have h := congrArg yonedaEquiv (hs2 n)
    rw [← yonedaEquiv_naturality, Equiv.apply_symm_apply] at h
    exact (congrArg (rbPsi X (th n)) h).trans (rbPsi_rbPhi X _ _)
  have htr : ∀ n, X.map (Chart.immι W (Chart.closedι ((SCH).obj W) (I ^ n))).op
      (X.map frW.op P) = x n := by
    have hsucc : ∀ n, X.map (Chart.immι W (Chart.closedι ((SCH).obj W) (I ^ (n + 1)))).op
        (X.map frW.op P) = x (n + 1) := by
      intro n
      rw [← Functor.map_comp_apply, ← op_comp, hf, op_comp, Functor.map_comp_apply, hP,
        ← Functor.map_comp_apply, ← op_comp, hfe, CategoryTheory.op_id,
        Functor.map_id_apply]
    rintro (_ | n)
    · obtain ⟨t, ht⟩ := exists_factor_closed (Chart.immι W (Chart.closedι ((SCH).obj W) (I ^ 0)))
        (I ^ (0 + 1)) (fun c hc => closedι_appTop_of_mem _ (by simp))
      rw [← hx 0 (0 + 1) t ht, ← hsucc 0, ← ht]
      simp only [op_comp, Functor.map_comp_apply]
    · exact hsucc n
  refine ⟨X.map frW.op P, htr, fun z hz => ?_⟩
  have hsz : yonedaEquiv.symm (rbPhi X base (X.map toW.op z)) = s := by
    refine huniq _ ⟨hterm.hom_ext _ _, fun n => ?_⟩
    apply yonedaEquiv.injective
    simp only [y]
    rw [← yonedaEquiv_naturality, Equiv.apply_symm_apply, Equiv.apply_symm_apply, rbPhi_map]
    congr 1
    rw [← hz (n + 1), ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, he]
  have hPz : X.map toW.op z = P := by
    have := congrArg (rbPsi X base) (congrArg yonedaEquiv hsz)
    rwa [Equiv.apply_symm_apply, rbPsi_rbPhi] at this
  change z = _
  rw [← hPz, ← Functor.map_comp_apply, ← op_comp, hfr, CategoryTheory.op_id,
    Functor.map_id_apply]

end Alg

/-- **Theorem 4.1, existence**, from Lemma 4.2 (`AffineStratum`) and the setup with Lemma 4.3
(`StrataOver`): for `X` separated and locally of finite type over `S`, with `|X|` noetherian. -/
theorem thm41_exists {M : Type u} [AddCommGroup M] [AddMonoid.FG M] [DecidableEq M]
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {actX : AAction (fppfO B S hS) M X}
    (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X)
    (hlft : IsLocallyOfFiniteType B S hS (terminal.from X))
    [letI := Space.pointTopology B S hS X; TopologicalSpace.NoetherianSpace (points B S hS X)]
    (h42 : ∀ C : ClosedStable actX, AffineStratum C.Z C.actZ)
    (h43 : ∀ C : ClosedStable actX, StrataOver C) : Effective actX := by
  have hT : IsAlgebraicSpace B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :=
    isAlgebraicSpace_of_iso B S hS
      ((((Over.mkIdTerminal (X := B.obj hS)).isTerminalObj yoneda _).uniqueUpToIso
        terminalIsTerminal).symm) (isAlgebraicSpace_yoneda B S hS _)
  refine effective_of_noetherian hX (fun C => ?_) h42 h43 (ClosedStable.self actX hX)
  have hs := isSeparatedOver_of_isSeparated B S hS hsep
    (isSeparated_of_isClosedImmersion B S hS C.i C.closed)
  refine ⟨hs, noetherianAlgebraization_of_lft C.Z C.alg hs ?_⟩
  have hl := isLocallyOfFiniteType_comp B S hS C.alg hX hT C.i (terminal.from X)
    (isLocallyOfFiniteType_of_isClosedImmersion B S hS C.i C.closed) hlft
  rwa [terminal.comp_from] at hl

end AlgMag.ChartMain

#print axioms AlgMag.ChartMain.noetherianAlgebraization_of_lft
#print axioms AlgMag.ChartMain.thm41_exists
