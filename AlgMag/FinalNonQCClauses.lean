/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.FinalNonQCGeneral
import AlgMag.Sec14Strong
import AlgMag.Sec14Remaining

/-!
# Remaining clauses of Theorem 8.3 and Proposition 14.4, `S` arbitrary, no atlas

`X` separated, locally of finite presentation, not necessarily quasi-compact, `S` not necessarily separated.

* `thm83_v_general`, `thm83_vi_general`, `thm83_vii_general`: clauses (v), (vi), (vii) of **Theorem 8.3**.
* `prop144_rep_general`, `prop144_closed_general`, `prop144_scheme_general`: the last assertions of **Proposition 14.4**.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe v u

namespace AlgMag.Final

open AlgMag.ChartAssembly LimThm LimOrbit CategoryTheory.OverShriek

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [AddGroup.FG M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **Theorem 8.3 (vii)** on a representing space: `X` a scheme gives `X^N` a scheme. Printed proof: closed in `X`, then affine over it. -/
theorem scheme_of_repr {act : AAction (fppfO B S hS) M X} {N : AddSubmonoid M} (r : Thm83Repr act N)
    {T₀ : BigFppfOver B S hS} (e : X ≅ yoneda.obj T₀) :
    ∃ W : BigFppfOver B S hS, Nonempty (r.P ≅ yoneda.obj W) := by
  let R₁ := r.closed_i.rep
  have hp₁ := R₁.isPullback e.inv
  have hiso₁ : IsIso (R₁.fst e.inv) := hp₁.isIso_fst_of_isIso
  let R₂ := r.affine_c.rep
  have hp₂ := R₂.isPullback (R₁.fst e.inv)
  have hiso₂ : IsIso (R₂.fst (R₁.fst e.inv)) := hp₂.isIso_fst_of_isIso
  exact ⟨_, ⟨(asIso (R₂.fst (R₁.fst e.inv))).symm⟩⟩

/-- Two presheaves representing the same attractor are isomorphic. -/
noncomputable def repIso {act : AAction (fppfO B S hS) M X} {N : AddSubmonoid M}
    {P P' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (r : RepresentsAttractor act N P)
    (r' : RepresentsAttractor act N P') : P ≅ P' :=
  NatIso.ofComponents (fun T => ((r.equiv T.unop).trans (r'.equiv T.unop).symm).toIso) (by
    intro T T' s
    ext z
    refine (r'.equiv T'.unop).injective ?_
    have h1 := r.naturality s.unop z
    have h2 := r'.naturality s.unop ((r'.equiv T.unop).symm (r.equiv T.unop z))
    simp only [Equiv.apply_symm_apply] at h2
    simpa using h1.trans h2.symm)

section Thm83

variable (hM : B.Contains (Spec (ZMon M))) (hX : IsAlgebraicSpace B S hS X)
  (hsep : Space.IsSeparatedOver B S hS X)
  (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
  (act : AAction (fppfO B S hS) M X) (N : AddSubmonoid M)

include hZ hM hX hsep hfp

/-- **Theorem 8.3 (v)**, relative form: `X → S` quasi-compact gives `X^N → S` quasi-compact. -/
theorem thm83_v_general :
    ∃ r : Thm83Repr act N, Space.IsQuasiCompact B S hS (terminal.from X) →
      Space.IsQuasiCompact B S hS (terminal.from r.P) := by
  obtain ⟨r⟩ := thm83_repr_general hZ hM hX hsep hfp act N
  exact ⟨r, fun hq => isQuasiCompact_terminal_of_presheaf (P := @AlgebraicGeometry.IsAffineHom)
    (fun g _ => inferInstance) inferInstance r.affine_c
    (isQuasiCompact_terminal_of_presheaf (P := @IsClosedImmersion)
      (fun g _ => inferInstance) inferInstance r.closed_i hq)⟩

/-- **Theorem 8.3 (vi)**: `X → S` of finite presentation gives `X^N → S` of finite presentation. -/
theorem thm83_vi_general (hf : Space.IsFinitePresentation B S hS (terminal.from X)) :
    ∃ r : Thm83Repr act N, Space.IsFinitePresentation B S hS (terminal.from r.P) := by
  obtain ⟨r⟩ := thm83_repr_general hZ hM hX hsep hfp act N
  exact ⟨r, thm83_vi hX (isSeparatedOver_iff_space.1 hsep) hf r⟩

/-- **Theorem 8.3 (vii)**: `X` a scheme gives `X^N` a scheme. -/
theorem thm83_vii_general {T₀ : BigFppfOver B S hS} (e : X ≅ yoneda.obj T₀) :
    ∃ W : BigFppfOver B S hS, Nonempty (RepresentsAttractor act N (yoneda.obj W)) := by
  obtain ⟨r⟩ := thm83_repr_general hZ hM hX hsep hfp act N
  obtain ⟨W, ⟨f⟩⟩ := scheme_of_repr r e
  exact ⟨W, ⟨fun T => ((f.app (op T)).toEquiv.symm).trans (r.rP.equiv T), fun s z => by
    refine (congrArg (r.rP.equiv _) ?_).trans (r.rP.naturality s _)
    exact NatTrans.naturality_apply f.inv s.op z⟩⟩

end Thm83

section Prop144

variable {P : ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) → Prop}
  {Xi : (BigAffineFppf B S hS)ᵒᵖ ⥤ Type u} {p : IndPresentation.{u, v, u} P Xi}
  (hM : B.Contains (Spec (ZMon M)))
  (a : IndAction M p)
  (hX : ∀ i, IsAlgebraicSpace B S hS (p.obj i))
  (hsep : ∀ i, Space.IsSeparatedOver B S hS (p.obj i))
  (hfp : ∀ i, Space.IsLocallyOfFinitePresentation B S hS (terminal.from (p.obj i)))

include hZ hM hX hsep hfp

/-- **Proposition 14.4**: `X^N → X` is representable by algebraic spaces, terms separated, locally of finite presentation, `S` arbitrary, no atlas. -/
theorem prop144_rep_general (N : AddSubmonoid M) :
    haveI : Countable M := countable_of_fg83
    IndAttractorMapHasPropNat a N (fun {Z' _} _ => IsAlgebraicSpace B S hS Z') :=
  haveI : Countable M := countable_of_fg83
  indAttractorMap_rep_nat a N (fun i => attPRep (a.act i) N) (fun i => attToX (a.act i) N)
    (fun _ _ _ => rfl) (fun i => attP_alg hZ hM (hX i) (hsep i) (hfp i) (a.act i) N) hX

/-- **Proposition 14.4**, last assertion: for a subgroup `Z`, `X^Z → X` is representable by a closed immersion, terms separated, locally of
finite presentation, `S` arbitrary, no atlas. -/
theorem prop144_closed_general (K : AddSubgroup M) :
    haveI : Countable M := countable_of_fg83
    IndAttractorMapHasPropNat a K.toAddSubmonoid (fun f => IsClosedImm f) := by
  haveI : Countable M := countable_of_fg83
  intro T y
  obtain ⟨i, x, rfl⟩ := p.surj T y
  obtain ⟨r⟩ := thm83_repr_general hZ hM (hX i) (hsep i) (hfp i) (a.act i) K.toAddSubmonoid
  have key : ∀ (K' : AddSubgroup M), K' = K → ∀ (rY : RepresentsAttractor (a.act i) K'.toAddSubmonoid r.Y),
      (∀ (T : BigFppfOver B S hS) (y : r.Y.obj (op T)), r.i.app (op T) y = (rY.equiv T y).toPoint) →
      ∃ r' : RepresentsAttractor (a.act i) K.toAddSubmonoid r.Y,
        ∀ (T : BigFppfOver B S hS) (y : r.Y.obj (op T)), r.i.app (op T) y = (r'.equiv T y).toPoint := by
    rintro _ rfl rY h
    exact ⟨rY, h⟩
  obtain ⟨r', hj⟩ := key _ (by ext m; simp [unitsSub]) r.rY r.i_eq
  refine ⟨fibreProduct r.i (yonedaEquiv.symm x), fibreSnd _ _, ?_,
    fun T' t => indAttractorFibreEquiv a K.toAddSubmonoid r' r.i hj x T' t,
    fun s t z hz => indAttractorFibreEquiv_nat a K.toAddSubmonoid r' r.i hj x s t z hz⟩
  exact (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
    (isPullback_fibreProduct _ _) r.closed_i

/-- **Proposition 14.4**, resp. ind-schemes: terms schemes, separated, locally of finite presentation, `S` arbitrary, no atlas. -/
theorem prop144_scheme_general (N : AddSubmonoid M)
    (hS' : ∀ i, ∃ U : BigFppfOver B S hS, Nonempty (p.obj i ≅ yoneda.obj U)) :
    haveI : Countable M := countable_of_fg83
    IsIndScheme.{u, v} (attractor a.toAction N) ∧
      IndAttractorMapHasPropNat a N
        (fun {Z' _} _ => ∃ U : BigFppfOver B S hS, Nonempty (Z' ≅ yoneda.obj U)) := by
  haveI : Countable M := countable_of_fg83
  have hsch : ∀ i, ∃ U : BigFppfOver B S hS, Nonempty (attP (a.act i) N ≅ yoneda.obj U) := fun i => by
    obtain ⟨T₀, ⟨e⟩⟩ := hS' i
    obtain ⟨r⟩ := thm83_repr_general hZ hM (hX i) (hsep i) (hfp i) (a.act i) N
    obtain ⟨W, ⟨f⟩⟩ := scheme_of_repr r e
    exact ⟨W, ⟨repIso (attPRep (a.act i) N) r.rP ≪≫ f⟩⟩
  exact ⟨isIndScheme_attractor a N (fun i => attPRep (a.act i) N) hsch,
    indAttractorMap_rep_scheme_nat a N (fun i => attPRep (a.act i) N) (fun i => attToX (a.act i) N)
      (fun _ _ _ => rfl) hsch hS'⟩

end Prop144

end AlgMag.Final

#print axioms AlgMag.Final.thm83_v_general
#print axioms AlgMag.Final.thm83_vi_general
#print axioms AlgMag.Final.thm83_vii_general
#print axioms AlgMag.Final.prop144_rep_general
#print axioms AlgMag.Final.prop144_closed_general
#print axioms AlgMag.Final.prop144_scheme_general
