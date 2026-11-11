/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.GenM332Scheme
import AlgMag.Sec3Final
import AlgMag.Sec15General

/-!
# Proposition 15.1 of *Algebraic Magnetism*

The printed proof: (ii) ⇒ (i) by Proposition 3.29; (i) ⇒ (ii) because `X^N = X^L` gives `X^N = X^{N ∩ L}` "by
Proposition 3.32". So `prop151_of_inter` assumes exactly that step and nothing else: any monoid, any functor.
Proposition 3.32 is printed under three alternative hypotheses, and §15 assumes none of them, so the
step is a real input. The cases below discharge it:

* `prop151_affine`: `X` affine over `S`, any `M` (3.32 (i)).
* `prop151_group_scheme`: `X` a separated scheme, `M` a countable group (3.32 (ii), f.g. removed).
* `prop151_embed_scheme`: `X` a separated scheme, `M` embedded in a f.g. group (3.32 (iii)).
* `prop151_of_prop332`: `X` a separated algebraic space, `M` a f.g. group, given Proposition 3.32 (ii).
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Cardinal

universe u

namespace AlgMag.Prop151

open AlgMag

section General
variable {C : Type*} [Category C] {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}} {M : Type*} [AddCommMonoid M]
  {F : Cᵒᵖ ⥤ Type u}

/-- **Proposition 15.1**, printed proof: the only input is the consequence of Proposition 3.32. Any
commutative monoid, any functor with an action. -/
theorem prop151_of_inter (act : AAction 𝒪 M F) (N : AddSubmonoid M)
    (hinter : ∀ L, attractorImage act N = attractorImage act L →
      attractorImage act (N ⊓ L) = attractorImage act N) :
    IsPure (attractorImage act) N ↔ ∀ L, L < N → attractorImage act L < attractorImage act N := by
  constructor
  · intro h L hL
    exact IsPure.attractorImage_lt act h hL
  · intro h L e
    by_contra hNL
    have hlt : N ⊓ L < N := lt_of_le_of_ne inf_le_left fun e' => hNL (inf_eq_left.mp e')
    have := h _ hlt
    rw [hinter L e] at this
    exact lt_irrefl _ this

end General

section Affine
variable {S : Scheme.{u}} {M : Type u} [AddCommMonoid M] {X : Over S} [IsAffineHom X.hom]

/-- **Proposition 15.1**, `X` affine over an arbitrary `S`, `M` any commutative monoid. -/
theorem prop151_affine (act : AAction (GB.overO S) M (yoneda.obj X)) (N : AddSubmonoid M) :
    IsPure (attractorImage act) N ↔ ∀ L, L < N → attractorImage act L < attractorImage act N :=
  isPure_iff_lt (attractorOrder_affine act) N

end Affine

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

section Iter
variable {M : Type u} [AddCommGroup M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {aX : AAction (fppfO B S hS) M X}

/-- `AlgMag.exists_iter_of_image_eq`, whose proof uses only that `X^N → X` is injective on points. -/
theorem exists_iter_of_inj {N L : AddSubmonoid M}
    (hinj : ∀ T, Function.Injective (AttractorPt.toPoint (act := aX) (N := N) (T := T)))
    (h : attractorImage aX N = attractorImage aX L)
    {T : BigFppfOver B S hS} (ψ : AttractorPt aX L T) :
    ∃ Ψ : IterPt aX N L T, Ψ.toPoint = ψ.toPoint := by
  classical
  have hG : ∀ {T' : BigFppfOver B S hS} (t : T' ⟶ T) (b : APt (fppfO B S hS) L (op T')),
      ∃ G : AttractorPt aX N T', G.toPoint = ψ.app t b := by
    intro T' t b
    have hm : ψ.app t b ∈ attractorImage aX L T' := by
      refine ⟨(magnetAction aX L).smul b (AttractorPt.baseChange t ψ), ?_⟩
      change ψ.app (𝟙 T' ≫ t) (APt.res (𝟙 T').op b * 1) = _
      have e : APt.res (𝟙 T').op b = b := APt.res_id b
      rw [e, mul_one, Category.id_comp]
    rw [← h] at hm
    exact hm
  choose G hGp using @hG
  refine ⟨⟨fun t b => G t b, ?_, ?_⟩, ?_⟩
  · intro T' T'' s t b
    apply hinj
    rw [hGp, AttractorPt.toPoint_baseChange, hGp, ψ.naturality]
  · intro T' t k b
    apply hinj
    rw [hGp, ψ.equivariant]
    change _ = aX.smul (APt.res (𝟙 T').op k) (G t b).toPoint
    have e : APt.res (𝟙 T').op k = k := APt.res_id k
    rw [e, hGp]
  · change (G (𝟙 T) 1).toPoint = _
    rw [hGp]
    rfl

end Iter

section Group
variable {M : Type u} [AddCommGroup M] [Countable M]
  {U : BigFppfOver B S hS} {aX : AAction (fppfO B S hS) M (yoneda.obj U)}

/-- `X^N → X` is injective on points, `X` a separated scheme, `M` countable (Corollary 3.30). -/
theorem toPoint_injective_scheme (hsep : IsSeparatedOver (yoneda.obj U)) (N : AddSubmonoid M)
    (T : BigFppfOver B S hS) :
    Function.Injective (AttractorPt.toPoint (act := aX) (N := N) (T := T)) := by
  haveI : Fact (#M < B.cutoff) := ⟨lt_of_le_of_lt mk_le_aleph0 B.aleph0_lt_cutoff⟩
  intro φ ψ h
  apply P337.ofLE_inj (BigFppfOver.isSheaf_of_type_yoneda_obj U) (hasDensePullback_of_separated hsep)
    (le_top : N ≤ ⊤) T
  exact (attractorTopEquiv aX T).injective h

/-- `X^N = X^L` implies `X^{N ∩ L} = X^N`, `X` a separated scheme, `M` a countable group. -/
theorem image_inf_group_scheme (hsep : IsSeparatedOver (yoneda.obj U)) {N L : AddSubmonoid M}
    (h : attractorImage aX N = attractorImage aX L) :
    attractorImage aX (N ⊓ L) = attractorImage aX N := by
  refine le_antisymm (attractorImage_monotone aX inf_le_left) ?_
  intro T x hx
  rw [h] at hx
  obtain ⟨ψ, rfl⟩ := hx
  obtain ⟨Ψ, hΨ⟩ := exists_iter_of_inj (toPoint_injective_scheme hsep N) h ψ
  obtain ⟨χ, hχ⟩ := GenM.exists_toBi Ψ.toBi
  refine ⟨χ, ?_⟩
  have e := AttractorPt.toPoint_toBi (hKinf N L) χ
  rw [hχ, IterPt.toPoint_toBi, hΨ] at e
  exact e.symm

/-- **Proposition 15.1**, `X` a separated scheme over an arbitrary `S`, `M` a countable abelian group, not
assumed finitely generated. Countability is the site cutoff of `AlgMag.specObj`. -/
theorem prop151_group_scheme (hsep : IsSeparatedOver (yoneda.obj U)) (N : AddSubmonoid M) :
    IsPure (attractorImage aX) N ↔ ∀ L, L < N → attractorImage aX L < attractorImage aX N :=
  prop151_of_inter aX N fun _ e => image_inf_group_scheme hsep e

end Group

section Embed
variable {M Z : Type u} [AddCommMonoid M] [AddCommGroup Z] [AddMonoid.FG Z] {f : M →+ Z}
  {U : BigFppfOver B S hS} {aX : AAction (fppfO B S hS) M (yoneda.obj U)}

/-- **Proposition 15.1**, `X` a separated scheme, `M` embedded in a finitely generated abelian group
(the case of Proposition 3.32 (iii)). -/
theorem prop151_embed_scheme (hf : Function.Injective f) (hsep : IsSeparatedOver (yoneda.obj U))
    (N : AddSubmonoid M) :
    IsPure (attractorImage aX) N ↔ ∀ L, L < N → attractorImage aX L < attractorImage aX N :=
  prop151_of_inter aX N fun L e => by
    have := fact334_iii_finite_scheme (aX := aX) hf hsep (s := {N, L}) (Set.toFinite _)
      ⟨N, Set.mem_insert _ _⟩ (attractorImage aX N) (by
        rintro K (rfl | rfl)
        · rfl
        · exact e.symm)
    rwa [sInf_pair] at this

end Embed

section Spaces
variable {M : Type u} [AddCommGroup M] [AddMonoid.FG M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {aX : AAction (fppfO B S hS) M X}

/-- **Proposition 15.1**, `X` a separated algebraic space, `M` a finitely generated group, given the printed
input Proposition 3.32 (ii) for `N, L` on points. No atlas. -/
theorem prop151_of_prop332 (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    (N : AddSubmonoid M)
    (h332 : ∀ (L : AddSubmonoid M) {T : BigFppfOver B S hS}
      (φ : AttractorPt (biAct aX) (N.prod L) T),
      ∃ χ : AttractorPt aX (N ⊓ L) T, χ.toPoint = φ.toPoint) :
    IsPure (attractorImage aX) N ↔ ∀ L, L < N → attractorImage aX L < attractorImage aX N :=
  prop151_of_inter aX N fun L e => by
    refine le_antisymm (attractorImage_monotone aX inf_le_left) ?_
    intro T x hx
    rw [e] at hx
    obtain ⟨ψ, rfl⟩ := hx
    obtain ⟨Ψ, hΨ⟩ := exists_iter_of_image_eq hX hsep e ψ
    obtain ⟨χ, hχ⟩ := h332 L Ψ.toBi
    exact ⟨χ, hχ.trans ((IterPt.toPoint_toBi _).trans hΨ)⟩

end Spaces

end AlgMag.Prop151

#print axioms AlgMag.Prop151.prop151_of_inter
#print axioms AlgMag.Prop151.prop151_affine
#print axioms AlgMag.Prop151.prop151_group_scheme
#print axioms AlgMag.Prop151.prop151_embed_scheme
#print axioms AlgMag.Prop151.prop151_of_prop332
