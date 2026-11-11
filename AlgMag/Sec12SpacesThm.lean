/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec12Spaces
import AlgMag.Sec12PrintedThm
import AlgMag.Sec8Theorem83
import AlgMag.Sec7Linearizable
import StacksFrontier.AlgebraicGeometry.Spaces.Smooth

/-!
# Theorem 12.4 for algebraic spaces

Mayeux, *Algebraic Magnetism*, Theorem 12.4: `X → S` smooth with a Zariski locally linearizable action
(Definition 7.2); then `X^N → X^{N^×}` is an affine space fibration.

`X` is a presheaf on the big fppf site, with `X^N`, `X^{N^×}` represented by presheaves `Zx`, `Zf`. Each
stable `S`-affine open `U a` of `X` gives the chart `U_a^F → X^F`, an open immersion, with
`U_a^N = X^N ×_{X^F} U_a^F` (printed reduction "to the case where `X` is affine over `S`"). The charts
cover `X^F`, and over an affine open of `S` the map `U_a^N → U_a^F` is `Spec Sym_{B₀}(P) → Spec B₀`
(`AlgMag.Sec12Printed.printed_affine`).

Beyond the printed statement: `M` is finitely generated, as for the bridge `exists_over_att` of §8. Then
`N` is arbitrary.
-/

suppress_compilation

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Magnetism

open scoped Classical

attribute [local instance] AlgMag.GB.gradedAlgebraOf

universe u

namespace AlgMag.Sec12SpacesThm

open AlgMag.GB AlgMag.Sec12Spaces AlgMag.Sec12Printed

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

variable {M : Type u} [AddCommGroup M] [AddGroup.FG M]

section Chart

variable {U₀ : BigFppfOver B S hS} (act : AAction (fppfO B S hS) M (yoneda.obj U₀))

/-- The whole of `U₀`, as a stable open. -/
lemma stableTop : IsStableOpen act (⊤ : ((SCH).obj U₀).Opens) := fun _ _ _ _ _ => trivial

/-- The trivial decomposition of an `S`-affine `U₀`. -/
lemma decTop (hA : IsAffineHom (structMap U₀)) :
    IsAffineDecomposition (A := PUnit.{u + 1}) act (fun _ => (⊤ : ((SCH).obj U₀).Opens)) where
  disjoint := fun a b h => (h (Subsingleton.elim a b)).elim
  iSup_eq_top := iSup_const
  stable := fun _ => stableTop act
  isAffineHom := fun _ => by
    have := hA
    have : IsIso (⊤ : ((SCH).obj U₀).Opens).ι := inferInstanceAs (IsIso ((SCH).obj U₀).topIso.hom)
    infer_instance

/-- The chart `U₀`, as a scheme over `S` with its action on all schemes over `S`. -/
abbrev chO : Over S := openOver (⊤ : ((SCH).obj U₀).Opens)

/-- The action on the chart, on all schemes over `S`. -/
abbrev chA : AAction (overO S) M (yoneda.obj (chO (B := B) (S := S) (hS := hS) (U₀ := U₀))) :=
  overAct (hM_of hS M) (stableTop act)

/-- A point of `(U₀)^N` on all schemes gives a point on the site, with the explicit formula. -/
def siteAtt {N : AddSubmonoid M} {T : BigFppfOver B S hS}
    (φo : AttractorPt (chA act) N (ov T)) : AttractorPt act N T where
  app {T'} s a := siteOf (φo.app (ovHom s) (castPt a)) ≫ openJ ⊤
  naturality {T' T''} r s a := by
    have hovc : ovHom (r ≫ s) = ovHom r ≫ ovHom s := Over.OverMorphism.ext ((SCH).map_comp r s)
    have hn : φo.app (ovHom (r ≫ s)) (castPt (APt.res r.op a)) =
        ovHom r ≫ φo.app (ovHom s) (castPt a) := by
      rw [hovc]
      exact φo.naturality (ovHom r) (ovHom s) (castPt a)
    refine (congrArg (fun q => siteOf q ≫ openJ ⊤) hn).trans ?_
    change siteOf _ ≫ openJ ⊤ = r ≫ siteOf _ ≫ openJ ⊤
    rw [siteOf_comp, Category.assoc]
  equivariant {T'} s h a := by
    have he : φo.app (ovHom s) (castPt (APt.toMagnet N h * a)) =
        overSmul (hM_of hS M) (stableTop act) (T := ov T') (castPt h) (φo.app (ovHom s) (castPt a)) :=
      φo.equivariant (ovHom s) (castPt h) (castPt a)
    refine (congrArg (fun q => siteOf q ≫ openJ ⊤) he).trans ?_
    exact overSmul_siteOf (stableTop act) _ h

lemma toPoint_siteAtt {N : AddSubmonoid M} {T : BigFppfOver B S hS}
    (φo : AttractorPt (chA act) N (ov T)) :
    (siteAtt act φo).toPoint = siteOf φo.toPoint ≫ openJ ⊤ := by
  have hov1 : ovHom (𝟙 T) = 𝟙 (ov T) := Over.OverMorphism.ext ((SCH).map_id T)
  change siteOf (φo.app (ovHom (𝟙 T)) (castPt 1)) ≫ openJ ⊤ = siteOf (φo.app (𝟙 (ov T)) 1) ≫ openJ ⊤
  rw [hov1]
  rfl

variable [hA : IsAffineHom (structMap U₀)]

instance instAffCh : IsAffineHom (chO (B := B) (S := S) (hS := hS) (U₀ := U₀)).hom := by
  change IsAffineHom ((⊤ : ((SCH).obj U₀).Opens).ι ≫ structMap U₀)
  have : IsIso (⊤ : ((SCH).obj U₀).Opens).ι := inferInstanceAs (IsIso ((SCH).obj U₀).topIso.hom)
  infer_instance

lemma contains_Z (N : AddSubmonoid M) : B.Contains (Zatt (chA act) N).left :=
  Scheme.size_lt_of_isClosedImmersion (iAtt (chA act) N).left (openObj (⊤ : ((SCH).obj U₀).Opens)).left.2

/-- `(U₀)^N`, as an object of the site. -/
def siteZ (N : AddSubmonoid M) : BigFppfOver B S hS :=
  siteObject B S hS (contains_Z act N) (Zatt (chA act) N).hom

/-- A morphism to `siteZ`, over `S`. -/
def ovZ {N : AddSubmonoid M} {T : BigFppfOver B S hS} (w : T ⟶ siteZ act N) :
    ov T ⟶ Zatt (chA act) N :=
  Over.homMk ((SCH).map w) (congrArg B.inclusion.map (Over.w w))

/-- A morphism to `Zatt`, on the site. -/
def ofOv {N : AddSubmonoid M} {T : BigFppfOver B S hS} (m : ov T ⟶ Zatt (chA act) N) :
    T ⟶ siteZ act N :=
  Over.homMk (ObjectProperty.homMk m.left) (by
    apply B.inclusion.map_injective
    exact Over.w m)

lemma ovZ_ofOv {N : AddSubmonoid M} {T : BigFppfOver B S hS} (m : ov T ⟶ Zatt (chA act) N) :
    ovZ act (ofOv act m) = m := Over.OverMorphism.ext rfl

lemma ovZ_injective {N : AddSubmonoid M} {T : BigFppfOver B S hS} {w w' : T ⟶ siteZ act N}
    (h : ovZ act w = ovZ act w') : w = w' :=
  (SCH).map_injective (congrArg (fun k => k.left) h)

lemma ovZ_comp {N : AddSubmonoid M} {T T' : BigFppfOver B S hS} (s : T' ⟶ T) (w : T ⟶ siteZ act N) :
    ovZ act (s ≫ w) = ovHom s ≫ ovZ act w :=
  Over.OverMorphism.ext ((SCH).map_comp s w)

/-- The map from `T`-points of `siteZ` to points of the attractor. -/
def fwd {N : AddSubmonoid M} {T : BigFppfOver B S hS} (w : T ⟶ siteZ act N) : AttractorPt act N T :=
  siteAtt act (attEquiv (chA act) N (ov T) (ovZ act w))

lemma toPoint_fwd {N : AddSubmonoid M} {T : BigFppfOver B S hS} (w : T ⟶ siteZ act N) :
    (fwd act w).toPoint = siteOf (ovZ act w ≫ iAtt (chA act) N) ≫ openJ ⊤ := by
  rw [fwd, toPoint_siteAtt, toPoint_attEquiv]

lemma fwd_bijective (N : AddSubmonoid M) (T : BigFppfOver B S hS) :
    Function.Bijective (fwd act (N := N) (T := T)) := by
  have hmJ := mono_openJ (V := (⊤ : ((SCH).obj U₀).Opens))
  refine ⟨fun w w' h => ovZ_injective act (iAtt_cancel (chA act) N ?_), fun φ => ?_⟩
  · have e := congrArg AttractorPt.toPoint h
    rw [toPoint_fwd, toPoint_fwd] at e
    have e₂ := (cancel_mono (openJ (⊤ : ((SCH).obj U₀).Opens))).1 e
    refine Over.OverMorphism.ext ?_
    exact congrArg (fun k => (SCH).map k) e₂
  · obtain ⟨t, ht⟩ := exists_lift_open (V := (⊤ : ((SCH).obj U₀).Opens)) φ.toPoint fun _ => trivial
    obtain ⟨φo, hφo⟩ := exists_over_att (decTop act hA) PUnit.unit φ t ht
    let m := (attEquiv (chA act) N (ov T)).symm φo
    refine ⟨ofOv act m, toPoint_injective_U (decTop act hA) ?_⟩
    rw [toPoint_fwd, ovZ_ofOv, ← toPoint_attEquiv, Equiv.apply_symm_apply, hφo, ← ht]
    congr 1

/-- **`(U₀)^N` on the site** is represented by `siteZ`, the scheme of Theorem 3.20. -/
def repCh (N : AddSubmonoid M) : RepresentsAttractor act N (yoneda.obj (siteZ act N)) where
  equiv T := Equiv.ofBijective _ (fwd_bijective act N T)
  naturality {T T'} s w := by
    refine toPoint_injective_U (decTop act hA) ?_
    change (fwd act (s ≫ w)).toPoint = (AttractorPt.baseChange s (fwd act w)).toPoint
    rw [AttractorPt.toPoint_baseChange, toPoint_fwd, toPoint_fwd, ovZ_comp, Category.assoc]
    change _ = s ≫ siteOf (ovZ act w ≫ iAtt (chA act) N) ≫ openJ ⊤
    rw [siteOf_comp, Category.assoc]

variable {N : AddSubmonoid M} {F : AddSubgroup M} (hF : IsFace F.toAddSubmonoid N)

/-- `X^N → X^F` on the site: the morphism of schemes `faceZ`. -/
def faceS : siteZ act N ⟶ siteZ act F.toAddSubmonoid :=
  Over.homMk (ObjectProperty.homMk (faceZ (chA act) N hF).left) (by
    apply B.inclusion.map_injective
    exact Over.w (faceZ (chA act) N hF))

lemma map_faceS : (SCH).map (faceS act hF) = (faceZ (chA act) N hF).left := rfl

lemma siteAtt_ofFace {T : BigFppfOver B S hS} (φo : AttractorPt (chA act) N (ov T)) :
    siteAtt act (AttractorPt.ofFace hF φo) = AttractorPt.ofFace hF (siteAtt act φo) := by
  refine AttractorPt.ext ?_
  funext T' s a
  rfl

/-- `yoneda (faceS)` is the morphism `r : (U₀)^N → (U₀)^F`. -/
lemma repFace_eq : repFace (repCh act N) (repCh act F.toAddSubmonoid) hF = yoneda.map (faceS act hF) := by
  ext T w
  apply ((repCh act F.toAddSubmonoid).equiv (unop T)).injective
  change _ = fwd act (w ≫ faceS act hF)
  refine ((repCh act F.toAddSubmonoid).equiv (unop T)).apply_symm_apply _ |>.trans ?_
  have e : ovZ act (w ≫ faceS act hF) = ovZ act w ≫ faceZ (chA act) N hF :=
    Over.OverMorphism.ext rfl
  rw [fwd, e, faceZ_spec, siteAtt_ofFace]
  rfl

end Chart

section Cover

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {actX : AAction (fppfO B S hS) M X}
  {A : Type u} {U : A → BigFppfOver B S hS}

lemma vertex_self {F : AddSubgroup M} {T : BigFppfOver B S hS}
    (φ : AttractorPt actX F.toAddSubmonoid T) : vertex (isFace_self F) φ = φ.toPoint := by
  change φ.app (𝟙 T) (APt.faceExt (isFace_self F) 1) = φ.app (𝟙 T) 1
  congr 1
  exact MonoidHom.ext fun n => APt.faceExt_pos _ 1 (Multiplicative.toAdd n).2

/-- The equivariant inclusion of a chart. -/
def jHom (L : ZariskiLocallyLinearizable actX A U) (a : A) : EquivariantHom (L.act a) actX where
  hom := L.j a
  map_smul := fun h x => L.equivariant a h x

/-- A chart of a smooth `X` is smooth over `S`. -/
lemma smooth_chart (L : ZariskiLocallyLinearizable actX A U)
    (hsm : Space.IsSmooth B S hS (terminal.from X)) (a : A) :
    Smooth (chO (B := B) (S := S) (hS := hS) (U₀ := U a)).hom := by
  have hO : Space.IsOpenImmersion B S hS (L.j a) := L.isOpen a
  have ha : (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (SCH)).presheaf (L.j a) :=
    MorphismProperty.relative_monotone (fun _ _ f (hf : IsOpenImmersion _) =>
      (inferInstance : Etale ((SCH).map f))) _ hO
  let t : IsTerminal (yoneda.obj (siteTop (B := B) (S := S) (hS := hS))) :=
    IsTerminal.isTerminalObj yoneda _ Over.mkIdTerminal
  let e : yoneda.obj (siteTop (B := B) (S := S) (hS := hS)) ≅ ⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    t.uniqueUpToIso terminalIsTerminal
  have hi : IsIso (terminal.from (yoneda.obj (siteTop (B := B) (S := S) (hS := hS)))) := by
    rw [terminal.hom_ext (terminal.from _) e.hom]
    infer_instance
  have hb : (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (SCH)).presheaf (terminal.from (yoneda.obj (siteTop (B := B) (S := S) (hS := hS)))) := by
    refine ⟨Functor.relativelyRepresentable.of_isIso _ _, fun c d g fst snd hp => ?_⟩
    have h1 : IsIso (yoneda.map snd) := hp.flip.isIso_fst_of_isIso
    have h2 : IsIso snd := isIso_of_reflects_iso snd yoneda
    exact (inferInstance : Etale ((SCH).map snd))
  have h := hsm (U a) siteTop (L.j a) (terminal.from _) (Over.mkIdTerminal.from _) ha hb
    (terminal.hom_ext _ _)
  have h' : Smooth ((SCH).map (Over.mkIdTerminal.from (U a) : U a ⟶ siteTop)) := h
  have e : (SCH).map (Over.mkIdTerminal.from (U a) : U a ⟶ siteTop) = structMap (U a) := by
    have e' : (SCH).map (Over.mkIdTerminal.from (U a) : U a ⟶ siteTop) ≫ 𝟙 _ = structMap (U a) :=
      congrArg B.inclusion.map (Over.w (Over.mkIdTerminal.from (U a) : U a ⟶ siteTop))
    rwa [Category.comp_id] at e'
  rw [e] at h'
  change Smooth ((⊤ : ((SCH).obj (U a)).Opens).ι ≫ structMap (U a))
  have : IsIso (⊤ : ((SCH).obj (U a)).Opens).ι := inferInstanceAs (IsIso ((SCH).obj (U a)).topIso.hom)
  infer_instance

variable [Countable M]

/-- The charts `(U_a)^F → X^F` cover `X^F`. -/
theorem exists_chart_cover (L : ZariskiLocallyLinearizable actX A U) {F : AddSubgroup M}
    {Zf : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (rf : RepresentsAttractor actX F.toAddSubmonoid Zf)
    {ZF : A → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (rF : ∀ a, RepresentsAttractor (L.act a) F.toAddSubmonoid (ZF a))
    {T : BigFppfOver B S hS} (y : Zf.obj (op T)) (t : (SCH).obj T) :
    ∃ (a : A) (he : Space.IsOpenImmersion B S hS (repAttractorMap (jHom L a) F.toAddSubmonoid (rF a) rf)),
      t ∈ rangeOf he y := by
  let φ := rf.equiv T y
  obtain ⟨a, ha⟩ := L.covers T (yonedaEquiv.symm φ.toPoint) t
  have hO : Space.IsOpenImmersion B S hS (L.j a) := L.isOpen a
  have he := isOpenImmersion_repAttractorMap (jHom L a) hO F.toAddSubmonoid (rF a) rf
  refine ⟨a, he, ?_⟩
  set x := yonedaEquiv.symm φ.toPoint with hx
  let q := (L.isOpen a).rep.snd x
  have hw := ((L.isOpen a).rep.isPullback x).w
  have hx' : (jHom L a).hom.app _ (yonedaEquiv ((L.isOpen a).rep.fst x)) =
      vertex (isFace_self F) (φ.baseChange q) := by
    rw [vertex_baseChange, vertex_self]
    have e' := congrArg yonedaEquiv hw
    rw [yonedaEquiv_comp, yonedaEquiv_comp] at e'
    refine e'.trans ?_
    simp [hx, yonedaEquiv]
    rfl
  obtain ⟨ψ, ⟨h₁, -⟩, -⟩ := existsUnique_attractorPt (jHom L a) hO (isFace_self F) (φ.baseChange q) _ hx'
  refine range_sub_of_mem he q y (((rF a).equiv _).symm ψ) ?_ ha
  change (rf.equiv _).symm ((((rF a).equiv _) (((rF a).equiv _).symm ψ)).push (jHom L a)) = Zf.map q.op y
  rw [Equiv.apply_symm_apply, h₁, Equiv.symm_apply_eq, rf.naturality]

end Cover

section Thm

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {actX : AAction (fppfO B S hS) M X}
  {A : Type u} {U : A → BigFppfOver B S hS}

/-- The conclusion of Theorem 12.4 over an affine open `V` of `S`, for `X` `S`-affine: with
`B₀ = O(X^F|_V) → B = O(X^N|_V)`, `P = ker/ker²` is finite projective and `B = Sym_{B₀}(P)`. -/
def SymOver {W : Over S} [IsAffineHom W.hom] (act : AAction (overO S) M (yoneda.obj W)) (N : AddSubmonoid M)
    {F : AddSubgroup M} (hF : IsFace F.toAddSubmonoid N) {V : S.Opens} (hV : IsAffineOpen V) : Prop :=
  letI := (rho0 act N hF hV).toRingHom.toAlgebra
  Module.Finite (Qalg act F.toAddSubmonoid hV)
      (Conormal (piB (gZ act hV (F := F)) (Yq F N) (hI₁' act N hF hV) (hI₀' act hV) (sharp_Yq N hF))) ∧
    Module.Projective (Qalg act F.toAddSubmonoid hV)
      (Conormal (piB (gZ act hV (F := F)) (Yq F N) (hI₁' act N hF hV) (hI₀' act hV) (sharp_Yq N hF))) ∧
    Nonempty (SymmetricAlgebra (Qalg act F.toAddSubmonoid hV)
      (Conormal (piB (gZ act hV (F := F)) (Yq F N) (hI₁' act N hF hV) (hI₀' act hV) (sharp_Yq N hF))) ≃ₐ[Qalg act F.toAddSubmonoid hV]
      Qalg act N hV)

/-- **Theorem 12.4** for algebraic spaces. `X → S` is smooth with a Zariski locally linearizable action,
`M` finitely generated, `N` arbitrary, `F` a subgroup face of `N` (the statement of the paper is
`F = N^×`: see `thm124_spaces`), `Zx`, `Zf` represent `X^N`, `X^F`. For every point `t` of a scheme `T`
over `Zf`, there is a chart `a` such that:

* `e : (U_a)^F → Zf` is an open immersion with `t` in the preimage of its image;
* `(U_a)^N = Zx ×_{Zf} (U_a)^F`, the map `(U_a)^N → (U_a)^F` being the morphism of schemes `faceZ`;
* over every affine open `V` of `S`, `faceZ` is the base change of `Spec B → Spec B₀`, with
  `B = Sym_{B₀}(P)`, `P` finite projective over `B₀`. -/
theorem thm124_spaces_face (L : ZariskiLocallyLinearizable actX A U)
    (hsm : Space.IsSmooth B S hS (terminal.from X)) {N : AddSubmonoid M} {F : AddSubgroup M}
    (hF : IsFace F.toAddSubmonoid N) {Zx Zf : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (rx : RepresentsAttractor actX N Zx) (rf : RepresentsAttractor actX F.toAddSubmonoid Zf)
    {T : BigFppfOver B S hS} (y : Zf.obj (op T)) (t : (SCH).obj T) :
    ∃ a : A, haveI : IsAffineHom (structMap (U a)) := L.isAffineHom a
      ∃ (e : yoneda.obj (siteZ (L.act a) F.toAddSubmonoid) ⟶ Zf)
        (e' : yoneda.obj (siteZ (L.act a) N) ⟶ Zx)
        (he : Space.IsOpenImmersion B S hS e),
        Space.IsOpenImmersion B S hS e' ∧ t ∈ rangeOf he y ∧
        IsPullback e' (yoneda.map (faceS (L.act a) hF)) (repFace rx rf hF) e ∧
        (BigFppfOver.toScheme B S hS).map (faceS (L.act a) hF) = (faceZ (chA (L.act a)) N hF).left ∧
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
  refine ⟨a, _, _, he, (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hp.flip he,
    ht, hp, rfl, fun V hV => ⟨isPullback_chart_square (chA (L.act a)) hF ⟨V, hV⟩,
      printed_affine (chA (L.act a)) N hF hV (Or.inr inferInstance)⟩⟩

/-- **Theorem 12.4** for algebraic spaces, `F = N^×`. -/
theorem thm124_spaces (L : ZariskiLocallyLinearizable actX A U)
    (hsm : Space.IsSmooth B S hS (terminal.from X)) (N : AddSubmonoid M)
    {Zx Zf : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (rx : RepresentsAttractor actX N Zx) (rf : RepresentsAttractor actX (unitsOf N).toAddSubmonoid Zf)
    {T : BigFppfOver B S hS} (y : Zf.obj (op T)) (t : (SCH).obj T) :
    ∃ a : A, haveI : IsAffineHom (structMap (U a)) := L.isAffineHom a
      ∃ (e : yoneda.obj (siteZ (L.act a) (unitsOf N).toAddSubmonoid) ⟶ Zf)
        (e' : yoneda.obj (siteZ (L.act a) N) ⟶ Zx)
        (he : Space.IsOpenImmersion B S hS e),
        Space.IsOpenImmersion B S hS e' ∧ t ∈ rangeOf he y ∧
        IsPullback e' (yoneda.map (faceS (L.act a) (isFace_unitsOf N))) (repFace rx rf (isFace_unitsOf N)) e ∧
        (BigFppfOver.toScheme B S hS).map (faceS (L.act a) (isFace_unitsOf N)) =
          (faceZ (chA (L.act a)) N (isFace_unitsOf N)).left ∧
        ∀ (V : S.Opens) (hV : IsAffineOpen V),
          IsPullback (iotaZ (chA (L.act a)) N ⟨V, hV⟩).left
            (PhiMap hV (rho0 (chA (L.act a)) N (isFace_unitsOf N) hV)).left
            (faceZ (chA (L.act a)) N (isFace_unitsOf N)).left
            (iotaZ (chA (L.act a)) (unitsOf N).toAddSubmonoid ⟨V, hV⟩).left ∧
          SymOver (chA (L.act a)) N (isFace_unitsOf N) hV :=
  thm124_spaces_face L hsm (isFace_unitsOf N) rx rf y t

end Thm

#print axioms thm124_spaces
#print axioms thm124_spaces_face

end AlgMag.Sec12SpacesThm
