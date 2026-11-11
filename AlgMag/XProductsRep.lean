/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.XProductsThm
import AlgMag.GeneralBaseCor
import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
import StacksFrontier.AlgebraicGeometry.Spaces.Category

/-!
# X-products of attractors: Proposition 4.3

Mayeux, *Algebraic magnetism: X-products of attractors via F₁-geometry*, §4.

## Main results

* `AlgMag.XP.prop43_moreover`: **Proposition 4.3**, "moreover": if `X → S` is affine, `X^𝒩 = X^{⋂ N_α}`.
* `AlgMag.XP.prop43_i`: **Proposition 4.3 (1)**: if `X → S` is affine, `X^𝒩` is representable, by a closed
  subscheme of `X`.
* `AlgMag.XP.prop43_ii`: **Proposition 4.3 (2)**: if `A` is finite and each `X^{N_α}` is representable,
  then `X^𝒩` is representable by an algebraic space. The conditions (a) and (b) of the printed statement
  are not needed.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

set_option linter.unusedSectionVars false

namespace AlgMag.XP

open GB

variable {M : Type u} [AddCommGroup M] {A : Type u} (𝓝 : MagnetFamily M A)

section Rep

variable {C : Type*} [Category.{v} C] (τ : C ⥤ Scheme.{u}) [Nonempty A]
variable {X : Cᵒᵖ ⥤ Type u} (act : AAction (τO τ) M X)

/-- A presheaf `Z` in the universe of the Stacks library represents `X^𝒩`: it has the same points,
naturally. Compare `AlgMag.RepresentsAttractor`. -/
structure RepresentsXN (Z : Cᵒᵖ ⥤ Type u) where
  /-- The bijection on `T`-points. -/
  equiv : ∀ T : C, Z.obj (op T) ≃ XNPt 𝓝 τ act T
  naturality : ∀ {T T' : C} (s : T' ⟶ T) (z : Z.obj (op T)),
    equiv T' (Z.map s.op z) = (equiv T z).baseChange s

end Rep

section Affine

variable {S : Scheme.{u}} {X : Over S} [IsAffineHom X.hom]
  (act : AAction (overO S) M (yoneda.obj X)) [Nonempty A]

/-- The map `X^{⋂ N_α} → X^𝒩`. -/
noncomputable def iInfToXN {T : Over S} (χ : AttractorPt act (⨅ α, 𝓝.N α) T) :
    XNPt 𝓝 (Over.forget S) act T :=
  (thm41Over 𝓝 act T).symm ⟨fun α => AttractorPt.ofLE (iInf_le _ α) χ, fun α β =>
    (AttractorPt.toPoint_ofLE _ _).trans (AttractorPt.toPoint_ofLE _ _).symm⟩

lemma toPoint_iInfToXN {T : Over S} (χ : AttractorPt act (⨅ α, 𝓝.N α) T) :
    (iInfToXN 𝓝 act χ).toPoint = χ.toPoint := by
  obtain ⟨α⟩ := ‹Nonempty A›
  have : (iInfToXN 𝓝 act χ).toProd = (⟨fun α => AttractorPt.ofLE (iInf_le _ α) χ, fun α β =>
      (AttractorPt.toPoint_ofLE _ _).trans (AttractorPt.toPoint_ofLE _ _).symm⟩ :
        XProdPt 𝓝 (Over.forget S) act T) :=
    (thm41Over 𝓝 act T).apply_symm_apply _
  refine (XNPt.toPoint_toProd (𝓝 := 𝓝) (iInfToXN 𝓝 act χ) α).symm.trans ?_
  rw [this]
  exact AttractorPt.toPoint_ofLE _ _

lemma XNPt_toPoint_injective {T : Over S} :
    Function.Injective (XNPt.toPoint : XNPt 𝓝 (Over.forget S) act T → (yoneda.obj X).obj (op T)) :=
  toPoint_injective_of_equiv (thm41Over 𝓝 act T).injective fun _ => toPoint_injective_global

/-- **Proposition 4.3**, "moreover": if `X → S` is affine, then `X^𝒩 = X^{⋂ N_α}`. -/
noncomputable def prop43_moreover (T : Over S) :
    AttractorPt act (⨅ α, 𝓝.N α) T ≃ XNPt 𝓝 (Over.forget S) act T :=
  Equiv.ofBijective (iInfToXN 𝓝 act) ⟨fun χ χ' h => toPoint_injective_global
      ((toPoint_iInfToXN 𝓝 act χ).symm.trans ((congrArg XNPt.toPoint h).trans
        (toPoint_iInfToXN 𝓝 act χ'))), fun ψ => by
    have hex := (exists_toPoint_iInf_iff act 𝓝.N ψ.toPoint).2 fun α =>
      ⟨ψ.toProd.1 α, XNPt.toPoint_toProd ψ α⟩
    obtain ⟨χ, hχ⟩ := hex
    exact ⟨χ, XNPt_toPoint_injective 𝓝 act ((toPoint_iInfToXN 𝓝 act χ).trans hχ)⟩⟩

lemma iInfToXN_baseChange {T T' : Over S} (s : T' ⟶ T) (χ : AttractorPt act (⨅ α, 𝓝.N α) T) :
    iInfToXN 𝓝 act (AttractorPt.baseChange s χ) = (iInfToXN 𝓝 act χ).baseChange s := by
  apply XNPt_toPoint_injective 𝓝 act
  refine (toPoint_iInfToXN 𝓝 act _).trans ?_
  refine (AttractorPt.toPoint_baseChange s χ).trans ?_
  refine Eq.trans ?_ (XNPt.toPoint_baseChange (act := act) s (iInfToXN 𝓝 act χ)).symm
  exact congrArg _ (toPoint_iInfToXN 𝓝 act χ).symm

/-- **Proposition 4.3 (1)**: if `X → S` is affine, `X^𝒩` is representable, by the closed subscheme
`Zatt act (⋂ N_α)` of `X` (Theorem 3.20 of [Algebraic Magnetism]). -/
noncomputable def prop43_i :
    RepresentsXN 𝓝 (Over.forget S) act (yoneda.obj (Zatt act (⨅ α, 𝓝.N α))) where
  equiv T := (attEquiv act _ T).trans (prop43_moreover 𝓝 act T)
  naturality {T T'} s z := by
    change iInfToXN 𝓝 act (attEquiv act _ T' (s ≫ z)) =
      (iInfToXN 𝓝 act (attEquiv act _ T z)).baseChange s
    rw [attEquiv_comp, iInfToXN_baseChange]

/-- **Proposition 4.3 (1)**: under the representation `prop43_i`, `X^𝒩 → X` is the closed immersion
`Z → X`. -/
theorem prop43_i_toPoint {T : Over S} (z : T ⟶ Zatt act (⨅ α, 𝓝.N α)) :
    ((prop43_i 𝓝 act).equiv T z).toPoint = z ≫ iAtt act _ :=
  (toPoint_iInfToXN 𝓝 act _).trans (toPoint_attEquiv act _ z)

end Affine

section Finite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "Sch" => BigFppfOver.toScheme B S hS

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (act : AAction (fppfO B S hS) M X)

/-- The explicit fibre product of presheaves. -/
def pullP {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ H) (g : G ⟶ H) :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type u where
  obj T := { q : F.obj T × G.obj T // f.app T q.1 = g.app T q.2 }
  map {T T'} s := ↾ fun q => ⟨(F.map s q.1.1, G.map s q.1.2), by
    have h1 := NatTrans.naturality_apply f s q.1.1
    have h2 := NatTrans.naturality_apply g s q.1.2
    change f.app T' (F.map s q.1.1) = g.app T' (G.map s q.1.2)
    rw [h1, h2, q.2]⟩
  map_id T := by
    ext q
    · exact Functor.map_id_apply F T q.1.1
    · exact Functor.map_id_apply G T q.1.2
  map_comp {T T' T''} a b := by
    ext q
    · exact Functor.map_comp_apply F a b q.1.1
    · exact Functor.map_comp_apply G a b q.1.2

/-- The first projection. -/
def pullFst {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ H) (g : G ⟶ H) : pullP f g ⟶ F where
  app T := ↾ fun q => q.1.1
  naturality _ _ _ := rfl

/-- The second projection. -/
def pullSnd {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ H) (g : G ⟶ H) : pullP f g ⟶ G where
  app T := ↾ fun q => q.1.2
  naturality _ _ _ := rfl

lemma pullP_w {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ H) (g : G ⟶ H) :
    pullFst f g ≫ f = pullSnd f g ≫ g := by
  ext T q
  exact q.2

/-- `pullP` is the categorical fibre product. -/
noncomputable def pullIso {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ H) (g : G ⟶ H) :
    pullP f g ≅ pullback f g where
  hom := pullback.lift (pullFst f g) (pullSnd f g) (pullP_w f g)
  inv :=
    { app := fun T => ↾ fun x => ⟨((pullback.fst f g).app T x, (pullback.snd f g).app T x),
        congrArg (fun k : pullback f g ⟶ H => k.app T x) pullback.condition⟩
      naturality := fun T T' s => by
        ext x
        refine Subtype.ext (Prod.ext ?_ ?_)
        · exact NatTrans.naturality_apply (pullback.fst f g) s x
        · exact NatTrans.naturality_apply (pullback.snd f g) s x }
  hom_inv_id := by
    ext T q
    refine Subtype.ext (Prod.ext ?_ ?_)
    · exact congrArg (fun k : pullP f g ⟶ F => k.app T q) (pullback.lift_fst _ _ (pullP_w f g))
    · exact congrArg (fun k : pullP f g ⟶ G => k.app T q) (pullback.lift_snd _ _ (pullP_w f g))
  inv_hom_id := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp]
      ext T x
      rfl
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp]
      ext T x
      rfl

/-- A fibre product of algebraic spaces is an algebraic space, in the explicit form. -/
theorem isAlgebraicSpace_pullP {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ H) (g : G ⟶ H)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hH : IsAlgebraicSpace B S hS H) : IsAlgebraicSpace B S hS (pullP f g) :=
  isAlgebraicSpace_of_iso B S hS (pullIso f g) (isAlgebraicSpace_pullback B S hS f g hF hG hH)

/-- The map `Z → X` of a presheaf representing `X^N`. -/
noncomputable def vert {N : AddSubmonoid M} {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (r : RepresentsAttractor act N Z) : Z ⟶ X where
  app T := ↾ fun z => (r.equiv (unop T) z).toPoint
  naturality T T' s := by
    ext z
    change (r.equiv (unop T') (Z.map s.unop.op z)).toPoint =
      X.map s.unop.op (r.equiv (unop T) z).toPoint
    rw [r.naturality, AttractorPt.toPoint_baseChange]

/-- Points of the fibre product of the `X^{N_α}`, `α ∈ s`, over `X`; there is a point of `X` so that
the product over the empty family is `X`. -/
def FP (s : Finset A) (T : BigFppfOver B S hS) : Type _ :=
  { p : X.obj (op T) × (∀ α, α ∈ s → AttractorPt act (𝓝.N α) T) //
    ∀ α h, (p.2 α h).toPoint = p.1 }

/-- Base change on `FP`. -/
noncomputable def FP.baseChange {𝓝 : MagnetFamily M A} {act : AAction (fppfO B S hS) M X} {s : Finset A}
    {T T' : BigFppfOver B S hS} (u : T' ⟶ T) (p : FP 𝓝 act s T) : FP 𝓝 act s T' :=
  ⟨(X.map u.op p.1.1, fun α h => AttractorPt.baseChange u (p.1.2 α h)), fun α h => by
    change (AttractorPt.baseChange u (p.1.2 α h)).toPoint = _
    rw [AttractorPt.toPoint_baseChange, p.2]⟩

lemma FP.ext' {𝓝 : MagnetFamily M A} {act : AAction (fppfO B S hS) M X} {s : Finset A}
    {T : BigFppfOver B S hS} {p q : FP 𝓝 act s T} (h1 : p.1.1 = q.1.1)
    (h2 : ∀ α h, p.1.2 α h = q.1.2 α h) : p = q :=
  Subtype.ext (Prod.ext h1 (funext fun α => funext fun h => h2 α h))

variable (Z : A → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (r : ∀ α, RepresentsAttractor act (𝓝.N α) (Z α))

include r in
/-- The induction of **Proposition 4.3 (2)**: a finite fibre product of algebraic spaces over `X`
represents the fibre product of the attractors. -/
theorem exists_rep_finset (hX : IsAlgebraicSpace B S hS X) (hZ : ∀ α, IsAlgebraicSpace B S hS (Z α))
    (s : Finset A) :
    ∃ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS Y) (ρ : Y ⟶ X)
      (e : ∀ T, Y.obj (op T) ≃ FP 𝓝 act s T),
      (∀ {T T'} (u : T' ⟶ T) (y : Y.obj (op T)), e T' (Y.map u.op y) = (e T y).baseChange u) ∧
      ∀ {T} (y : Y.obj (op T)), (e T y).1.1 = ρ.app (op T) y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨X, hX, 𝟙 X, fun T =>
      { toFun := fun x => ⟨(x, fun α h => absurd h (Finset.notMem_empty α)),
          fun α h => absurd h (Finset.notMem_empty α)⟩
        invFun := fun p => p.1.1
        left_inv := fun _ => rfl
        right_inv := fun p => FP.ext' rfl fun α h => absurd h (Finset.notMem_empty α) }, ?_, ?_⟩
    · intro T T' u y
      exact FP.ext' rfl fun α h => absurd h (Finset.notMem_empty α)
    · intro T y
      rfl
  | insert β s hβ ih =>
    obtain ⟨Y, hY, ρ, e, hnat, hρ⟩ := ih
    let res : ∀ T, FP 𝓝 act (insert β s) T → FP 𝓝 act s T := fun T p =>
      ⟨(p.1.1, fun α h => p.1.2 α (Finset.mem_insert_of_mem h)), fun α h => p.2 α _⟩
    refine ⟨pullP ρ (vert act (r β)), isAlgebraicSpace_pullP _ _ hY (hZ β) hX,
      pullFst _ _ ≫ ρ, fun T =>
      { toFun := fun q => ⟨(ρ.app (op T) q.1.1, fun α h => if h' : α = β then h' ▸ (r β).equiv T q.1.2
            else (e T q.1.1).1.2 α (Finset.mem_of_mem_insert_of_ne h h')), fun α h => by
          by_cases h' : α = β
          · subst h'
            simp only [dite_true]
            exact q.2.symm
          · simp only [h', dite_false]
            rw [(e T q.1.1).2, hρ]⟩
        invFun := fun p => ⟨((e T).symm (res T p),
            ((r β).equiv T).symm (p.1.2 β (Finset.mem_insert_self β s))), by
          change ρ.app (op T) ((e T).symm (res T p)) =
            ((r β).equiv T (((r β).equiv T).symm (p.1.2 β (Finset.mem_insert_self β s)))).toPoint
          rw [← hρ, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
          exact (p.2 β _).symm⟩
        left_inv := fun q => by
          refine Subtype.ext (Prod.ext ?_ ?_)
          · change (e T).symm (res T _) = q.1.1
            rw [Equiv.symm_apply_eq]
            refine FP.ext' ?_ fun α h => ?_
            · exact (hρ q.1.1).symm
            · have hne : α ≠ β := fun h' => hβ (h' ▸ h)
              change dite (α = β) _ _ = _
              rw [dif_neg hne]
          · change ((r β).equiv T).symm (dite (β = β) _ _) = q.1.2
            rw [dif_pos rfl]
            exact Equiv.symm_apply_apply _ _
        right_inv := fun p => by
          refine FP.ext' ?_ fun α h => ?_
          · change ρ.app (op T) ((e T).symm (res T p)) = _
            rw [← hρ, Equiv.apply_symm_apply]
          · change dite (α = β) _ _ = _
            by_cases h' : α = β
            · subst h'
              rw [dif_pos rfl]
              exact Equiv.apply_symm_apply _ _
            · rw [dif_neg h']
              change ((e T) ((e T).symm (res T p))).1.2 α _ = _
              rw [Equiv.apply_symm_apply] }, ?_, ?_⟩
    · intro T T' u q
      refine FP.ext' ?_ fun α h => ?_
      · exact NatTrans.naturality_apply ρ u.op q.1.1
      · change dite (α = β) _ _ = AttractorPt.baseChange u (dite (α = β) _ _)
        by_cases h' : α = β
        · subst h'
          rw [dif_pos rfl, dif_pos rfl]
          exact (r α).naturality u q.1.2
        · rw [dif_neg h', dif_neg h']
          have := hnat u q.1.1
          exact congrArg (fun p : FP 𝓝 act s T' => p.1.2 α (Finset.mem_of_mem_insert_of_ne h h')) this
    · intro T y
      rfl

variable [AddGroup.FG M] [Nonempty A]

include r in
/-- **Proposition 4.3 (2)**: if `A` is finite and each `X^{N_α}` is representable by an algebraic space,
then `X^𝒩` is representable by an algebraic space. The conditions (a), (b) of the printed statement are
those of Theorem 4.1 and are not needed. -/
theorem prop43_ii [Finite A] (hX : IsAlgebraicSpace B S hS X)
    (hZ : ∀ α, IsAlgebraicSpace B S hS (Z α)) :
    ∃ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS Y ∧
      Nonempty (RepresentsXN 𝓝 (Sch) act Y) := by
  classical
  have := Fintype.ofFinite A
  obtain ⟨Y, hY, ρ, e, hnat, hρ⟩ := exists_rep_finset 𝓝 act Z r hX hZ Finset.univ
  obtain ⟨α₀⟩ := ‹Nonempty A›
  let f : ∀ T, FP 𝓝 act Finset.univ T ≃ XProdPt 𝓝 (Sch) act T := fun T =>
    { toFun := fun p => ⟨fun α => p.1.2 α (Finset.mem_univ α), fun α β => (p.2 α _).trans (p.2 β _).symm⟩
      invFun := fun Φ => ⟨((Φ.1 α₀).toPoint, fun α _ => Φ.1 α), fun α _ => Φ.2 α _⟩
      left_inv := fun p => FP.ext' (p.2 _ _) fun α h => rfl
      right_inv := fun Φ => rfl }
  refine ⟨Y, hY, ⟨⟨fun T => (e T).trans ((f T).trans (thm41 𝓝 act hX T).symm), ?_⟩⟩⟩
  intro T T' s y
  apply (thm41 𝓝 act hX T').injective
  change (thm41 𝓝 act hX T') ((thm41 𝓝 act hX T').symm (f T' (e T' (Y.map s.op y)))) =
    (XNPt.baseChange s ((thm41 𝓝 act hX T).symm (f T (e T y)))).toProd
  rw [Equiv.apply_symm_apply]
  refine Eq.trans ?_ (toProd_baseChange (act := act) s _).symm
  change _ = XProdPt.baseChange s ((thm41 𝓝 act hX T) ((thm41 𝓝 act hX T).symm (f T (e T y))))
  rw [Equiv.apply_symm_apply, hnat]
  rfl

end Finite

end AlgMag.XP

#print axioms AlgMag.XP.prop43_moreover
#print axioms AlgMag.XP.prop43_i
#print axioms AlgMag.XP.prop43_i_toPoint
#print axioms AlgMag.XP.prop43_ii
