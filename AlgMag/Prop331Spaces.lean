/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec3Intersections
import AlgMag.PrintedProp51

/-!
# Proposition 3.31 (ii) for algebraic spaces

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026) 126–201, Proposition 3.31 (ii).

`M`, `Z` finitely generated abelian groups, `f : M → Z`, `Y` a magnet of `Z`, `N = f⁻¹(Y)`, `X` a separated
algebraic space with an `S`-affine equivariant atlas `U → X` which is `K`-FPR for `K = f⁻¹(Y^×)`:
`X^N_M = X^Y_Z`. The scheme case is `AlgMag.prop331_ii`.

Proof. A point `ψ` of `X^Y_Z` lifts, étale locally, to the atlas: its limit point is fixed by `D(Z/Y^×)`,
hence by `D(M/K)` (characters of `M/K ⊆ Z/Y^×` extend fppf locally, `AlgMag.mem_fixed_comap_of_along`), so
by the FPR property its lift lies in `U^K_M`, whose image is a point of `U^{Y^×}_Z`; Proposition 5.1
(`AlgMag.isFaceCartesian_of_fg`) for the face `Y^×` of `Y` gives a point of `U^Y_Z`. On the scheme `U` the
scheme case gives a point of `U^N_M`, pushed to `X^N_M`; these glue since `X^N → X` is a monomorphism.

## Main results

* `AlgMag.mem_fixed_comap_of_along`: `D(Z/Q)`-fixed points through `f` are `D(M/f⁻¹(Q))`-fixed, any sheaf.
* `AlgMag.prop331_ii_spaces`: **Proposition 3.31 (ii)**, `X` a separated algebraic space with a
  `f⁻¹(Y^×)`-FPR atlas, `Y` finitely generated or `X` limit preserving.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

set_option linter.unusedSectionVars false

namespace AlgMag

section Prop331Spaces

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

variable {M Z : Type u} [AddCommGroup M] [AddMonoid.FG M] [AddCommGroup Z] [AddMonoid.FG Z]

/-- A point of a sheaf fixed by `D(Z/Q)`, acting through `f : M → Z`, is fixed by `D(M/f⁻¹(Q))`: a
character of `M/f⁻¹(Q) ⊆ Z/Q` extends fppf locally to `Z/Q`. -/
theorem mem_fixed_comap_of_along {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presieve.IsSheaf (BigFppfOver.topology B S hS) F) (act : AAction (fppfO B S hS) M F)
    (f : M →+ Z) (Q : AddSubgroup Z) {T : (BigFppfOver B S hS)ᵒᵖ} {x : F.obj T}
    (hx : x ∈ (fixedPoints (quotientAction (actAlong f act) Q)).obj T) :
    x ∈ (fixedPoints (quotientAction act (Q.comap f))).obj T := by
  intro T' s h
  have : AddMonoid.FG (Z ⧸ Q) :=
    AddMonoid.fg_of_surjective (QuotientAddGroup.mk' Q) (QuotientAddGroup.mk'_surjective Q)
  have : AddGroup.FG (Z ⧸ Q) := AddGroup.fg_iff_addMonoid_fg.mpr inferInstance
  let φ : M →+ Z ⧸ Q := (QuotientAddGroup.mk' Q).comp f
  have hker : φ.ker = Q.comap f := by
    ext m
    simp [φ, QuotientAddGroup.eq_zero_iff]
  let e : φ.range →+ M ⧸ Q.comap f :=
    ((QuotientAddGroup.quotientKerEquivRange φ).symm.trans
      (QuotientAddGroup.quotientAddEquivOfEq hker)).toAddMonoidHom
  have he : ∀ m, e ⟨φ m, ⟨m, rfl⟩⟩ = (QuotientAddGroup.mk' (Q.comap f) m) := by
    intro m
    have h1 : (QuotientAddGroup.quotientKerEquivRange φ).symm ⟨φ m, ⟨m, rfl⟩⟩ =
        (QuotientAddGroup.mk m : M ⧸ φ.ker) :=
      (AddEquiv.symm_apply_eq _).2 rfl
    change QuotientAddGroup.quotientAddEquivOfEq hker
      ((QuotientAddGroup.quotientKerEquivRange φ).symm ⟨φ m, ⟨m, rfl⟩⟩) = _
    rw [h1]
    rfl
  let hJ : APt (fppfO B S hS) φ.range.toAddSubmonoid (op (unop T')) :=
    h.comp (AddMonoidHom.toMultiplicative e)
  have hcov := extSieve_mem (B := B) (S := S) (hS := hS) φ.range (T := unop T') hJ
  refine (hF _ hcov).isSeparatedFor.ext ?_
  rintro W g ⟨a, ha⟩
  change F.map g.op (act.smul (h.comp (AddMonoidHom.toMultiplicative (QuotientAddGroup.mk' (Q.comap f))))
    (F.map s x)) = _
  rw [act.map_smul]
  have key := hx (s ≫ g.op) a
  rw [Functor.map_comp_apply] at key
  have eq : APt.res g.op (h.comp (AddMonoidHom.toMultiplicative (QuotientAddGroup.mk' (Q.comap f)))) =
      (a.comp (AddMonoidHom.toMultiplicative (QuotientAddGroup.mk' Q))).comp
        (AddMonoidHom.toMultiplicative f) := by
    refine MonoidHom.ext fun m => ?_
    have h2 := DFunLike.congr_fun ha (Multiplicative.ofAdd ⟨φ (Multiplicative.toAdd m),
      ⟨_, rfl⟩⟩)
    change a _ = ((fppfO B S hS).map g.op).hom (h (Multiplicative.ofAdd
      (e ⟨φ (Multiplicative.toAdd m), ⟨_, rfl⟩⟩))) at h2
    rw [he] at h2
    exact h2.symm
  rw [eq]
  exact key

variable {U : BigFppfOver B S hS} [IsAffineHom U.hom.hom] {aU : AAction (fppfO B S hS) M (yoneda.obj U)}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {aX : AAction (fppfO B S hS) M X} {π : yoneda.obj U ⟶ X}

/-- **Proposition 3.31 (ii)** for algebraic spaces. `M`, `Z` finitely generated abelian groups,
`f : M → Z`, `Y` a magnet of `Z`, `N = f⁻¹(Y)`: `X^N_M = X^Y_Z`, i.e. `ptAlong` is bijective. `X` is a
separated algebraic space with an `S`-affine equivariant atlas `U → X` which is `f⁻¹(Y^×)`-FPR, and `Y` is
finitely generated or `X` is limit preserving. -/
theorem prop331_ii_spaces (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    (f : M →+ Z) (Y : AddSubmonoid Z) (hat : IsZFPRAtlas aU aX π ((unitsSubgroup Y).comap f))
    (hb : Y.FG ∨ IsLimitPreserving X) (T : BigFppfOver B S hS) :
    Function.Bijective
      (ptAlong aX : AttractorPt aX (Y.comap f) T → AttractorPt (actAlong f aX) Y T) := by
  have : AddGroup.FG M := AddGroup.fg_iff_addMonoid_fg.mpr inferInstance
  have : Countable M := countable_of_fg M
  have hsX := (isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf
  constructor
  · intro χ χ' h
    apply attractor_toPoint_injective_sep hX hsep
    rw [← toPoint_ptAlong χ, ← toPoint_ptAlong χ', h]
  · intro ψ
    suffices hχ : ∃ χ : AttractorPt aX (Y.comap f) T, χ.toPoint = ψ.toPoint by
      obtain ⟨χ, hχ⟩ := hχ
      exact ⟨χ, attractor_toPoint_injective_sep hX hsep _ _ ((toPoint_ptAlong χ).trans hχ)⟩
    let F : EquivariantHom aU aX := ⟨π, hat.atlas.equivariant⟩
    let FZ := homAlong f F
    let Q := unitsSubgroup Y
    have hQ : IsFace Q.toAddSubmonoid Y := isFace_units _
    let K : AddSubgroup M := Q.comap f
    let x₀ := AttractorPt.ofFace hQ ψ
    let g₀ : yoneda.obj T ⟶ X := yonedaEquiv.symm x₀.toPoint
    let rep := hat.atlas.etale.rep
    let T' := rep.pullback g₀
    let q : T' ⟶ T := rep.snd g₀
    let u : T' ⟶ U := rep.fst' g₀
    have hu : π.app (op T') u = X.map q.op x₀.toPoint := by
      have h2 : yoneda.map u ≫ π = yoneda.map q ≫ g₀ := by
        rw [Functor.relativelyRepresentable.map_fst']
        exact rep.w g₀
      have h3 := congrArg (fun k => k.app (op T') (𝟙 T')) h2
      have h4 : (yoneda.map u ≫ π).app (op T') (𝟙 T') = π.app (op T') u := by
        change π.app (op T') (𝟙 T' ≫ u) = _
        rw [Category.id_comp]
      have h5 : (yoneda.map q ≫ g₀).app (op T') (𝟙 T') = X.map q.op x₀.toPoint := by
        change g₀.app (op T') (𝟙 T' ≫ q) = _
        rw [Category.id_comp]
        simp [g₀, yonedaEquiv_symm_app_apply]
      exact h4.symm.trans (h3.trans h5)
    have hfixX : X.map q.op x₀.toPoint ∈ (fixedPoints (quotientAction aX K)).obj (op T') := by
      apply mem_fixed_comap_of_along hsX aX f Q
      rw [← AttractorPt.toPoint_baseChange]
      exact (AttractorPt.baseChange q x₀).toPoint_mem_fixedPoints
    have hfixU : u ∈ (fixedPoints (quotientAction aU K)).obj (op T') :=
      (isFPR_iff (IsEquivariant.comap (actU := aU) (actX := aX) (f := π) hat.atlas.equivariant
        (QuotientAddGroup.mk' K))).mp hat.isZFPR (op T') u (by rw [hu]; exact hfixX)
    have hcov : ∀ {W : BigFppfOver B S hS} (a : APt (fppfO B S hS) K.toAddSubmonoid (op W)),
        extSieve (fppfO B S hS) K a ∈ BigFppfOver.topology B S hS W :=
      fun a => extSieve_mem K a
    let w₀ : AttractorPt aU (Q.toAddSubmonoid.comap f) T' :=
      attractorFixedEquivOfCover (BigFppfOver.isSheaf_of_type_yoneda_obj U) hcov T' ⟨u, hfixU⟩
    have hw₀ : w₀.toPoint = u := congrArg Subtype.val ((attractorFixedEquivOfCover (act := aU)
      (BigFppfOver.isSheaf_of_type_yoneda_obj U) hcov T').symm_apply_apply ⟨u, hfixU⟩)
    let w : AttractorPt (actAlong f aU) Q.toAddSubmonoid T' := ptAlong aU (Y := Q.toAddSubmonoid) w₀
    have hpush : AttractorPt.ofFace hQ (AttractorPt.baseChange q ψ) = AttractorPt.push FZ w := by
      apply attractor_toPoint_injective_sep hX hsep
      change (AttractorPt.baseChange q x₀).toPoint = π.app (op T') (ptAlong aU (Y := Q.toAddSubmonoid) w₀).toPoint
      rw [AttractorPt.toPoint_baseChange, toPoint_ptAlong, hw₀, hu]
    have hcart : IsFaceCartesian FZ hQ := by
      rcases hb with hY | hl
      · exact isFaceCartesian_of_fg hX hsep FZ (isEtale_of_atlas hat.atlas) hQ hY
      · exact isFaceCartesian_of_separated hX hsep hl FZ (isEtale_of_atlas hat.atlas) hQ
    obtain ⟨w', hw'⟩ := (hcart T').2 ⟨(AttractorPt.baseChange q ψ, w), hpush⟩
    have hw'' : AttractorPt.push FZ w' = AttractorPt.baseChange q ψ := congrArg (fun p => p.1.1) hw'
    obtain ⟨v, hv⟩ := (prop331_ii (f := f) (Y := Y) (aX := aU) T').2 w'
    refine exists_toPoint_of_sieve hsX (N := Y.comap f)
      (fun T => attractor_toPoint_injective_sep hX hsep _ T) ψ.toPoint _
      (Space.sieve_generate_singleton_mem_topology_over B S hS q
        (hat.atlas.surjective.property_snd g₀) (hat.atlas.etale.property_snd g₀)) ?_
    rintro W g ⟨W', a, b, ⟨⟩, rfl⟩
    refine ⟨AttractorPt.baseChange a (AttractorPt.push F v), ?_⟩
    have h1 : (AttractorPt.push F v).toPoint = (AttractorPt.baseChange q ψ).toPoint := by
      rw [← hw'', ← hv]
      rfl
    rw [AttractorPt.toPoint_baseChange, h1, AttractorPt.toPoint_baseChange, ← Functor.map_comp_apply,
      ← op_comp]

end Prop331Spaces

end AlgMag

#print axioms AlgMag.prop331_ii_spaces
