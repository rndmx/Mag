/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SecLeftover1615Spaces
import AlgMag.FinalCorAtlas

/-!
# Proposition 16.15 (ii) without representability hypotheses

`G → S` a smooth group algebraic space, separated, locally of finite presentation and quasi-compact,
`S` separated, `M` a finitely generated abelian group, with the site conditions of Theorem 8.3
(`thm83_free`, atlas from Theorem 6.8) and the cutoff `SM B M` of Corollary 11.2. Then `G^{[α⟩}` and
`G^{[α⟩^×}` are representable by algebraic spaces (Theorem 8.3), `G^{[α⟩}_{e_S}` is an algebraic space
(fibre product), and `G^{[α⟩}`, `G^{[α⟩}_{e_S}` are smooth over `S`. Smoothness of `G^{[α⟩}` over `S`
is Corollary 11.2 with target `S`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.Leftover

open AlgMag.GB AlgMag.SpacesLift AlgMag.Sec11Spaces AlgMag.Final

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [SM B M]

/-- The fibre `K` of `X^N → X^F` over a section `σ` is an algebraic space, smooth over `S`, if `X → S`
is smooth and `X^N`, `X^F` are algebraic spaces. -/
theorem isAlgebraicSpace_isSmooth_fibre {N F : AddSubmonoid M} (hF : IsFace F N)
    {X Zx Zy K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hZx : IsAlgebraicSpace B S hS Zx)
    (hZy : IsAlgebraicSpace B S hS Zy)
    (act : AAction (fppfO B S hS) M X) (hsm : Space.IsSmooth B S hS (terminal.from X))
    (rx : RepresentsAttractor act N Zx) (rf : RepresentsAttractor act F Zy)
    (σ : ∀ T, AttractorPt act F T) (hσ : ∀ {T T'} (s : T' ⟶ T), (σ T).baseChange s = σ T')
    (eK : ∀ T, K.obj (op T) ≃ {x : AttractorPt act N T // AttractorPt.ofFace hF x = σ T})
    (nK : ∀ {T T'} (s : T' ⟶ T) (w : K.obj (op T)),
      (eK T' (K.map s.op w)).1 = (eK T w).1.baseChange s) :
    IsAlgebraicSpace B S hS K ∧ Space.IsSmooth B S hS (terminal.from K) := by
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
      { app := fun U => TypeCat.ofHom fun p =>
          (eK (unop U)).symm ⟨rx.equiv (unop U) (s.fst.app U p), mem s U p⟩
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
  have hK : IsAlgebraicSpace B S hS K :=
    isAlgebraicSpace_of_iso B S hS hpb.isoPullback
      (isAlgebraicSpace_pullback B S hS z u hZx (isAlgebraicSpace_top B S hS) hZy)
  exact ⟨hK, isSmooth_fibre_spaces hF hX hZx hZy hK act hsm rx rf σ hσ eK nK⟩

/-- **Proposition 16.15 (ii)**, no representability assumed. Let `M` be a finitely generated abelian
group, `S` separated, `G → S` a smooth group algebraic space, separated, locally of finite presentation
and quasi-compact, with an action of `D(M)` by group morphisms. Then `G^{[α⟩}` is represented by an
algebraic space `Y`, smooth over `S`, and `G^{[α⟩}_{e_S}` is an algebraic space, smooth over `S`. -/
theorem prop1615_ii_free [DecidableEq M] [AddGroup.FG M] [S.IsSeparated]
    (hZ : B.Contains (⊤_ Scheme.{u})) (hM : B.Contains (Spec (ZMon M)))
    (G : GrpFunctor.{u} (BigFppfOver B S hS)) (hG : IsAlgebraicSpace B S hS G.F)
    (hsep : Space.IsSeparatedOver B S hS G.F)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from G.F))
    (hq : Space.IsQuasiCompactSpace B S hS G.F)
    (act : AAction (fppfO B S hS) M G.F) (ha : ActsByMonoidEnd act) (α : M)
    (hsm : Space.IsSmooth B S hS (terminal.from G.F)) :
    (∃ Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u,
      Nonempty (RepresentsAttractor act (AddSubmonoid.closure {α}) Y) ∧
      IsAlgebraicSpace B S hS Y ∧ Space.IsSmooth B S hS (terminal.from Y)) ∧
    (∃ (K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (eK : ∀ T, K.obj (op T) ≃ (rootKernel act ha α).F.obj (op T)),
      (∀ {T T'} (s : T' ⟶ T) (w : K.obj (op T)),
        eK T' (K.map s.op w) = (rootKernel act ha α).F.map s.op (eK T w)) ∧
      IsAlgebraicSpace B S hS K ∧ Space.IsSmooth B S hS (terminal.from K)) := by
  obtain ⟨r, -⟩ := thm83_free hZ hM hG hsep hfp hq act (AddSubmonoid.closure {α})
  obtain ⟨r0, -⟩ := thm83_free hZ hM hG hsep hfp hq act (unitsFace (AddSubmonoid.closure {α}))
  refine ⟨⟨r.P, ⟨r.rP⟩, r.algP, isSmooth_rep_spaces _ hG r.algP act hsm r.rP⟩, ?_⟩
  let hF := unitsIsFace (AddSubmonoid.closure {α})
  let G' := attrGrp G act ha (unitsFace (AddSubmonoid.closure {α}))
  let σ : ∀ T, AttractorPt act (unitsFace (AddSubmonoid.closure {α})) T :=
    fun T => (1 : G'.F.obj (op T))
  have hσ : ∀ {T T'} (s : T' ⟶ T), (σ T).baseChange s = σ T' :=
    fun {T T'} s => GrpFunctor.map_one G' s.op
  let K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
    { obj := fun U => {w : r.P.obj U // AttractorPt.ofFace hF (r.rP.equiv (unop U) w) = σ (unop U)}
      map := fun {U V} s => TypeCat.ofHom fun w => ⟨r.P.map s w.1, by
        rw [show r.P.map s = r.P.map s.unop.op from rfl, r.rP.naturality]
        exact (congrArg (fun x => x.baseChange s.unop) w.2).trans (hσ s.unop)⟩
      map_id := fun U => by
        ext w
        change r.P.map (𝟙 U) w.1 = w.1
        simp
      map_comp := fun f g => by
        ext w
        change r.P.map (f ≫ g) w.1 = r.P.map g (r.P.map f w.1)
        simp }
  let eS : ∀ T, K.obj (op T) ≃ {x : AttractorPt act (AddSubmonoid.closure {α}) T //
      AttractorPt.ofFace hF x = σ T} := fun T => (r.rP.equiv T).subtypeEquiv fun _ => Iff.rfl
  let E : ∀ T, (rootKernel act ha α).F.obj (op T) ≃ {x : AttractorPt act (AddSubmonoid.closure {α}) T //
      AttractorPt.ofFace hF x = σ T} := fun T =>
    { toFun := fun x => ⟨x.1.1, x.2⟩
      invFun := fun x => ⟨(x.1, PUnit.unit), x.2⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  have nK : ∀ {T T'} (s : T' ⟶ T) (w : K.obj (op T)),
      (eS T' (K.map s.op w)).1 = (eS T w).1.baseChange s := fun s w => r.rP.naturality s w.1
  obtain ⟨hK, hKs⟩ := isAlgebraicSpace_isSmooth_fibre hF hG r.algP r0.algP act hsm r.rP r0.rP σ hσ
    eS nK
  refine ⟨K, fun T => (eS T).trans (E T).symm, fun {T T'} s w => ?_, hK, hKs⟩
  apply (E T').injective
  apply Subtype.ext
  exact nK s w

end AlgMag.Leftover

#print axioms AlgMag.Leftover.prop1615_ii_free
