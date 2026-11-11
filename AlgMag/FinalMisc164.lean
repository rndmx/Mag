/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec16Remaining

/-!
# §16.4 (i) of *Algebraic Magnetism*, through Proposition 3.31

§16.4 (i): "By Remarks 3.12 and 3.11, `D(⟨α⟩)` and `D(M)` act on `X^{⟨α⟩}`, and using Proposition 3.31, we have
`(X^{⟨α⟩})^{[α⟩}_{⟨α⟩} = (X^{⟨α⟩})^{[α⟩}_M`". `X^{⟨α⟩}` lives in a larger universe than `X`, so Proposition 3.31 is
proved here in that universe, for `f : L → M` the inclusion of a subgroup, on the point sets `BigPt`.
The two actions of Remarks 3.12 and 3.11 agree through `D(M) → D(L)`, and `D(M) → D(L)` is an fppf epimorphism.
-/

open CategoryTheory Opposite AlgebraicGeometry

universe u

noncomputable section

namespace AlgMag.FinalMisc

open AlgMag.S16R

section General

variable {C : Type*} [Category C] {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}} {M : Type*} [AddCommMonoid M]

lemma up_mul {N L : AddSubmonoid M} (hNL : N ≤ L) {U V : Cᵒᵖ} (s : U ⟶ V) (b : APt 𝒪 L U)
    (a : APt 𝒪 (innerMagnet N L) U) (h : APt 𝒪 M V) (hh : APt.toMagnet L h = APt.res s b) :
    APt.res (𝒪 := 𝒪) s (S16R.upPt (𝒪 := 𝒪) hNL (APt.toMagnet (innerMagnet N L) b * a)) =
      APt.toMagnet N h * S16R.upPt (𝒪 := 𝒪) hNL (APt.res (𝒪 := 𝒪) s a) := by
  refine MonoidHom.ext fun n => ?_
  have h1 := DFunLike.congr_fun hh (Multiplicative.ofAdd ⟨_, hNL (Multiplicative.toAdd n).2⟩)
  exact (map_mul (𝒪.map s).hom _ _).trans (congrArg (· * _) h1.symm)

end General

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [AddGroup.FG M]
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {act : AAction (fppfO B S hS) M F}
  {Z : AddSubgroup M} {N : AddSubmonoid M}

/-- Remark 3.11 and Remark 3.12 agree through `D(M) → D(L)`. -/
lemma magnet_smul_toMagnet {U : (BigFppfOver B S hS)ᵒᵖ} (k : APt (fppfO B S hS) M U)
    (φ : AttractorPt act Z.toAddSubmonoid (unop U)) :
    (magnetAction act Z.toAddSubmonoid).smul (APt.toMagnet _ k) φ =
      (attractorAction act Z.toAddSubmonoid).smul k φ := by
  refine AttractorPt.ext ?_
  funext T' t a
  exact φ.equivariant t (APt.res t.op k) a

/-- The map of Proposition 3.31 for `f : L → M`, `Y = N ⊆ L`, on `X^L`. -/
def prop331Inner (hNL : N ≤ Z.toAddSubmonoid) {T : BigFppfOver B S hS}
    (ψ : BigPt (magnetAction act Z.toAddSubmonoid) (innerMagnet N Z.toAddSubmonoid) T) :
    BigPt (attractorAction act Z.toAddSubmonoid) N T where
  app t c := ψ.app t (S16R.downPt c)
  naturality s t c := ψ.naturality s t (S16R.downPt c)
  equivariant t k c := by
    have hc : S16R.downPt (APt.toMagnet N k * c) =
      APt.toMagnet (innerMagnet N Z.toAddSubmonoid) (APt.toMagnet Z.toAddSubmonoid k) * S16R.downPt c := rfl
    exact (congrArg (ψ.app t) hc).trans ((ψ.equivariant t _ (S16R.downPt c)).trans (magnet_smul_toMagnet k _))

/-- **Proposition 3.31** for `L → M`, on `X^L`, `X` an fppf sheaf: `(X^L)^{N}_{L} = (X^L)^{N}_{M}`. -/
def prop331InnerEquiv (hF : Presieve.IsSheaf (BigFppfOver.topology B S hS) F)
    (hNL : N ≤ Z.toAddSubmonoid) (T : BigFppfOver B S hS) :
    BigPt (magnetAction act Z.toAddSubmonoid) (innerMagnet N Z.toAddSubmonoid) T ≃
      BigPt (attractorAction act Z.toAddSubmonoid) N T where
  toFun := prop331Inner hNL
  invFun φ :=
    { app := fun t a => φ.app t (S16R.upPt hNL a)
      naturality := fun s t a => φ.naturality s t (S16R.upPt hNL a)
      equivariant := fun {T'} t b a => by
        have hsh := isSheaf_attractor act Z.toAddSubmonoid _ hF
        refine (hsh _ (extSieve_mem Z b)).isSeparatedFor.ext ?_
        rintro W s ⟨h, hh⟩
        have e := up_mul hNL s.op b a h hh
        have e1 := φ.naturality s t (S16R.upPt hNL (APt.toMagnet (innerMagnet N Z.toAddSubmonoid) b * a))
        have e2 := (magnetAction act Z.toAddSubmonoid).map_smul s.op b (φ.app t (S16R.upPt hNL a))
        have e3 := φ.naturality s t (S16R.upPt hNL a)
        refine e1.symm.trans ?_
        refine (congrArg (φ.app (s ≫ t)) e).trans ?_
        refine (φ.equivariant (s ≫ t) h _).trans ?_
        refine Eq.trans ?_ e2.symm
        rw [show APt.res s.op b = APt.toMagnet Z.toAddSubmonoid h from hh.symm]
        exact (congrArg ((attractorAction act Z.toAddSubmonoid).smul h) e3).trans
          (magnet_smul_toMagnet h _).symm }
  left_inv ψ := by
    refine BigPt.ext ?_
    funext T' t a
    rfl
  right_inv φ := by
    refine BigPt.ext ?_
    funext T' t a
    rfl

/-- `prop331InnerEquiv` is natural in `T`. -/
lemma prop331Inner_baseChange (hNL : N ≤ Z.toAddSubmonoid) {T T' : BigFppfOver B S hS} (s : T' ⟶ T)
    (ψ : BigPt (magnetAction act Z.toAddSubmonoid) (innerMagnet N Z.toAddSubmonoid) T) :
    prop331Inner hNL (ψ.baseChange s) = (prop331Inner hNL ψ).baseChange s := rfl

/-- **§16.4 (i)**, printed route. `X` an algebraic space, `M` finitely generated, `α ∈ M`, `L = ℤα`, `N = [α⟩`.
`Y₁` represents `X^L`, and it is the fixed-point functor of `D(M/L)` (Proposition 3.35). `Y₂` is the attractor of `Y₁`
under `D(L)` for `N` seen in `L` (Remark 3.12), and it represents `X^N` (Proposition 3.32). By Proposition 3.31, its
points are those of `(X^L)^N_M`, for the action of Remark 3.11. -/
theorem sec164_i_printed {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (act : AAction (fppfO B S hS) M X) (α : M) :
    let L := (AddSubgroup.zmultiples α).toAddSubmonoid
    let N := AddSubmonoid.closure {α}
    ∃ (Y₁ Y₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (r₁ : RepresentsAttractor act L Y₁)
      (r₂ : RepresentsAttractor ((smallModelOfRep r₁).transport (magnetAction act L)) (innerMagnet N L) Y₂),
      Nonempty (∀ T, Y₁.obj (op T) ≃
        (fixedPoints (quotientAction act (AddSubgroup.zmultiples α))).obj (op T)) ∧
      Nonempty (RepresentsAttractor act N Y₂) ∧
      Nonempty (∀ T, Y₂.obj (op T) ≃ BigPt (attractorAction act L) N T) := by
  intro L N
  have : Countable M := countable_of_fg M
  have hNL : N ≤ L := by
    refine (AddSubmonoid.closure_le).2 ?_
    rintro _ rfl
    exact AddSubgroup.mem_zmultiples _
  obtain ⟨Y₁, ⟨r₁⟩⟩ := exists_rep act L (nonempty_universalPoint L)
  obtain ⟨Y₂, ⟨r₂⟩⟩ := exists_rep ((smallModelOfRep r₁).transport (magnetAction act L))
    (innerMagnet N L) (nonempty_universalPoint _)
  have hsh : Presieve.IsSheaf (BigFppfOver.topology B S hS) X :=
    (isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf
  exact ⟨Y₁, Y₂, r₁, r₂, ⟨fun T => (r₁.equiv T).trans (fixedStep_fppf hX act α T).symm⟩,
    ⟨innerRep hNL r₁ r₂⟩,
    ⟨fun T => (r₂.equiv T).trans (((smallModelOfRep r₁).ptEquiv (magnetAction act L) _ T).trans
      (prop331InnerEquiv hsh hNL T))⟩⟩

end AlgMag.FinalMisc

#print axioms AlgMag.FinalMisc.sec164_i_printed
