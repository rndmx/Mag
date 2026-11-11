/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec11SpacesCor
import AlgMag.Sec16Lie
import StacksFrontier.AlgebraicGeometry.Spaces.SmoothMorphismProperty

/-!
# Proposition 16.15 (ii) for algebraic spaces

The printed proof: by Corollary 11.10, `G^{[α⟩} → S` and `G^{[α⟩} → G^0` are smooth, and
`G^{[α⟩}_{e_S} = G^{[α⟩} ×_{G^0} e_S`. `G`, `G^{[α⟩}`, `G^{[α⟩^×}`, `G^{[α⟩}_{e_S}` are algebraic spaces
here. Their representability by algebraic spaces is a hypothesis (it is Theorem 8.3, which needs an
atlas). The site cutoff is `SM B M`, as in `AlgMag.Sec11SpacesCor`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.Leftover

open AlgMag.GB AlgMag.SpacesLift AlgMag.Sec11Spaces

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [SM B M]

/-- The fibre of `X^N → X^F` over a section `σ` of `X^F` is smooth over `S`, if `X → S` is smooth. -/
theorem isSmooth_fibre_spaces {N F : AddSubmonoid M} (hF : IsFace F N)
    {X Zx Zy K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hZx : IsAlgebraicSpace B S hS Zx)
    (hZy : IsAlgebraicSpace B S hS Zy) (hK : IsAlgebraicSpace B S hS K)
    (act : AAction (fppfO B S hS) M X) (hsm : Space.IsSmooth B S hS (terminal.from X))
    (rx : RepresentsAttractor act N Zx) (rf : RepresentsAttractor act F Zy)
    (σ : ∀ T, AttractorPt act F T) (hσ : ∀ {T T'} (s : T' ⟶ T), (σ T).baseChange s = σ T')
    (eK : ∀ T, K.obj (op T) ≃ {x : AttractorPt act N T // AttractorPt.ofFace hF x = σ T})
    (nK : ∀ {T T'} (s : T' ⟶ T) (w : K.obj (op T)),
      (eK T' (K.map s.op w)).1 = (eK T w).1.baseChange s) :
    Space.IsSmooth B S hS (terminal.from K) := by
  have ofb : ∀ {T T'} (s : T' ⟶ T) (x : AttractorPt act N T),
      AttractorPt.ofFace hF (x.baseChange s) = (AttractorPt.ofFace hF x).baseChange s :=
    fun _ _ => rfl
  let z : Zx ⟶ Zy :=
    { app := fun U => TypeCat.ofHom fun w =>
        (rf.equiv (unop U)).symm (AttractorPt.ofFace hF (rx.equiv (unop U) w))
      naturality := fun U V s => by
        ext w
        apply (rf.equiv (unop V)).injective
        change rf.equiv _ ((rf.equiv _).symm _) = rf.equiv _ (Zy.map s.unop.op _)
        rw [Equiv.apply_symm_apply, rf.naturality]
        refine Eq.trans ?_ (congrArg _ ((rf.equiv _).apply_symm_apply _).symm)
        exact congrArg _ (rx.naturality s.unop w) }
  have hz : ∀ T w, rf.equiv T (z.app (op T) w) = AttractorPt.ofFace hF (rx.equiv T w) :=
    fun T w => (rf.equiv T).apply_symm_apply _
  let u : ⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) ⟶ Zy :=
    { app := fun U => TypeCat.ofHom fun _ => (rf.equiv (unop U)).symm (σ (unop U))
      naturality := fun U V s => by
        ext w
        apply (rf.equiv (unop V)).injective
        change rf.equiv _ ((rf.equiv _).symm _) = rf.equiv _ (Zy.map s.unop.op _)
        rw [Equiv.apply_symm_apply, rf.naturality]
        refine Eq.trans ?_ (congrArg _ ((rf.equiv _).apply_symm_apply _).symm)
        exact (hσ _).symm }
  let j : K ⟶ Zx :=
    { app := fun U => TypeCat.ofHom fun w => (rx.equiv (unop U)).symm (eK (unop U) w).1
      naturality := fun U V s => by
        ext w
        apply (rx.equiv (unop V)).injective
        change rx.equiv _ ((rx.equiv _).symm _) = rx.equiv _ (Zx.map s.unop.op _)
        rw [Equiv.apply_symm_apply, rx.naturality]
        refine Eq.trans ?_ (congrArg _ ((rx.equiv _).apply_symm_apply _).symm)
        exact nK s.unop w }
  have hj : ∀ U w, rx.equiv (unop U) (j.app U w) = (eK (unop U) w).1 :=
    fun U w => (rx.equiv (unop U)).apply_symm_apply _
  have hcomm : j ≫ z = terminal.from K ≫ u := by
    ext U w
    apply (rf.equiv (unop U)).injective
    change rf.equiv _ (z.app U (j.app U w)) = rf.equiv _ ((rf.equiv _).symm _)
    rw [Equiv.apply_symm_apply]
    exact (hz (unop U) _).trans ((congrArg _ (hj U w)).trans (eK (unop U) w).2)
  have hpb : IsPullback j (terminal.from K) z u := by
    refine IsPullback.of_isLimit (c := PullbackCone.mk j (terminal.from K) hcomm) ?_
    have mem : ∀ (s : PullbackCone z u) (U) (p : s.pt.obj U),
        AttractorPt.ofFace hF (rx.equiv (unop U) (s.fst.app U p)) = σ (unop U) := by
      intro s U p
      have h1 := congrArg (fun k => (rf.equiv (unop U)) (k.app U p)) s.condition
      exact (hz (unop U) _).symm.trans (h1.trans ((rf.equiv (unop U)).apply_symm_apply _))
    let lift : ∀ s : PullbackCone z u, s.pt ⟶ K := fun s =>
      { app := fun U => TypeCat.ofHom fun p => (eK (unop U)).symm ⟨rx.equiv (unop U) (s.fst.app U p), mem s U p⟩
        naturality := fun U V f => by
          ext p
          apply (eK (unop V)).injective
          apply Subtype.ext
          change (eK _ ((eK _).symm _)).1 = (eK _ (K.map f.unop.op ((eK _).symm _))).1
          rw [nK, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
          have h1 := congrArg (fun k => k p) (s.fst.naturality f)
          change rx.equiv _ (s.fst.app V (s.pt.map f p)) = _
          rw [show s.fst.app V (s.pt.map f p) = Zx.map f (s.fst.app U p) from h1]
          exact rx.naturality f.unop _ }
    refine PullbackCone.IsLimit.mk hcomm lift ?_ ?_ ?_
    · intro s
      ext U p
      apply (rx.equiv (unop U)).injective
      refine (hj U _).trans ?_
      change (eK _ ((eK _).symm _)).1 = _
      rw [Equiv.apply_symm_apply]
      rfl
    · intro s
      exact terminal.hom_ext _ _
    · intro s m h1 h2
      ext U p
      apply (eK (unop U)).injective
      apply Subtype.ext
      change _ = (eK _ ((eK _).symm _)).1
      rw [Equiv.apply_symm_apply]
      refine (hj U _).symm.trans ?_
      exact congrArg (fun k => rx.equiv (unop U) (k.app U p)) h1
  have hzs := isSmooth_repFace_spaces N hF hX hZx hZy act hsm rx rf z hz
  let P : MorphismProperty (AlgebraicSpaces B S hS) := fun _ _ f => Space.IsSmooth B S hS f.hom
  haveI : P.IsStableUnderBaseChange := Space.isSmooth_isStableUnderBaseChange B S hS
  let A : ∀ F, IsAlgebraicSpace B S hS F → AlgebraicSpaces B S hS := fun F h => ⟨F, h⟩
  let top := isAlgebraicSpace_top B S hS
  have hpb' : IsPullback (ObjectProperty.homMk j : A K hK ⟶ A Zx hZx)
      (ObjectProperty.homMk (terminal.from K) : A K hK ⟶ A _ top)
      (ObjectProperty.homMk z : A Zx hZx ⟶ A Zy hZy) (ObjectProperty.homMk u : A _ top ⟶ A Zy hZy) :=
    IsPullback.of_map (ObjectProperty.ι _) (by ext1; exact hcomm) hpb
  exact MorphismProperty.of_isPullback (P := P) hpb' hzs

/-- `X^N → S` is smooth, if `X → S` is. -/
theorem isSmooth_rep_spaces (N : AddSubmonoid M) {X Zx : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hZx : IsAlgebraicSpace B S hS Zx)
    (act : AAction (fppfO B S hS) M X) (hsm : Space.IsSmooth B S hS (terminal.from X))
    (rx : RepresentsAttractor act N Zx) : Space.IsSmooth B S hS (terminal.from Zx) := by
  let eqT : EquivariantHom act (topAct (B := B) (S := S) (hS := hS) (M := M)) :=
    { hom := terminal.from X
      map_smul := fun _ _ => top_eq _ _ }
  refine isSmooth_repMap_spaces N hX (isAlgebraicSpace_top B S hS) hZx
    (isAlgebraicSpace_top B S hS) eqT hsm rx (repTop N) _ fun T w => ?_
  refine AttractorPt.ext ?_
  funext T₁ t a
  exact top_eq _ _

/-- **Proposition 16.15 (ii)** for algebraic spaces. Let `G → S` be a smooth group algebraic space with
an action of `D(M)` by group morphisms, and `G^{[α⟩}`, `G^{[α⟩^×}`, `G^{[α⟩}_{e_S}` algebraic spaces
`Y`, `Y0`, `K`. Then `Y` and `K` are smooth over `S`. -/
theorem prop1615_ii_spaces [DecidableEq M]
    (G : GrpFunctor.{u} (BigFppfOver B S hS)) (hG : IsAlgebraicSpace B S hS G.F)
    (act : AAction (fppfO B S hS) M G.F) (ha : ActsByMonoidEnd act) (α : M)
    (hsm : Space.IsSmooth B S hS (terminal.from G.F))
    {Y Y0 K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (hY0 : IsAlgebraicSpace B S hS Y0)
    (hKs : IsAlgebraicSpace B S hS K)
    (rY : RepresentsAttractor act (AddSubmonoid.closure {α}) Y)
    (rY0 : RepresentsAttractor act (unitsFace (AddSubmonoid.closure {α})) Y0)
    (eK : ∀ T, K.obj (op T) ≃ (rootKernel act ha α).F.obj (op T))
    (hK : ∀ {T T'} (s : T' ⟶ T) (w : K.obj (op T)),
      eK T' (K.map s.op w) = (rootKernel act ha α).F.map s.op (eK T w)) :
    Space.IsSmooth B S hS (terminal.from Y) ∧ Space.IsSmooth B S hS (terminal.from K) := by
  refine ⟨isSmooth_rep_spaces _ hG hY act hsm rY, ?_⟩
  let G' := attrGrp G act ha (unitsFace (AddSubmonoid.closure {α}))
  refine isSmooth_fibre_spaces (unitsIsFace (AddSubmonoid.closure {α})) hG hY hY0 hKs act hsm rY rY0
    (fun T => (1 : G'.F.obj (op T))) (fun {T T'} s => GrpFunctor.map_one G' s.op)
    (fun T => (eK T).trans
      { toFun := fun x => ⟨x.1.1, x.2⟩
        invFun := fun x => ⟨(x.1, PUnit.unit), x.2⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }) ?_
  intro T T' s w
  exact congrArg (fun x => x.1.1) (hK s w)

end AlgMag.Leftover

#print axioms AlgMag.Leftover.prop1615_ii_spaces
