/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec3Final
import AlgMag.Sec5Etale
import AlgMag.Sec8Theorem83

/-!
# Proposition 5.1 (i): the printed reduction

Mayeux, *Algebraic Magnetism*, proof of Proposition 5.1 (i): "it is enough to treat the case `Q = N^×`"
(`AlgMag.IsFaceCartesian.of_face`), then "we can assume `N^× = 0` and that `N` is fine and sharp using the
map `M → M/N^×` and Proposition 3.31".

Proposition 3.31 (ii) is available for `X` a scheme, `M/N^×` finitely generated. For `X` an algebraic space it
is not formalized, and the printed Proposition 3.31 does not cover `M` not finitely generated, so the reduction
is proved here for `X` a scheme and `M` finitely generated. The direct proof for all faces,
`AlgMag.isFaceCartesian_of_fg`, stays; it provides the sharp case.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Along

variable {M Z : Type u} [AddCommGroup M] [AddCommGroup Z] [AddMonoid.FG Z]
  {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {aU : AAction (fppfO B S hS) M F} {aX : AAction (fppfO B S hS) M G}
  (f : M →+ Z)

/-- An equivariant morphism for `D(M)` is equivariant for `D(Z)`, through `f : M → Z`. -/
noncomputable def homAlong (g : EquivariantHom aU aX) :
    EquivariantHom (actAlong f aU) (actAlong f aX) where
  hom := g.hom
  map_smul h x := g.map_smul _ x

variable {f}

lemma ptAlong_push (g : EquivariantHom aU aX) {Y : AddSubmonoid Z} {T : BigFppfOver B S hS}
    (φ : AttractorPt aU (Y.comap f) T) :
    ptAlong aX (AttractorPt.push g φ) = AttractorPt.push (homAlong f g) (ptAlong aU φ) := rfl

lemma ptAlong_ofFace {Y E : AddSubmonoid Z} (hE : IsFace E Y) (hc : IsFace (E.comap f) (Y.comap f))
    {T : BigFppfOver B S hS} {A : AAction (fppfO B S hS) M F} (φ : AttractorPt A (Y.comap f) T) :
    ptAlong A (AttractorPt.ofFace hc φ) = AttractorPt.ofFace hE (ptAlong A φ) := by
  refine AttractorPt.ext ?_
  funext T' t a
  change φ.app t (APt.faceExt hc _) = φ.app t (_ )
  congr 1

/-- The reduction by **Proposition 3.31**: if the comparison maps for `Y`, `E` are bijective for the action of
`D(Z)`, and `X^N_M = X^Y_Z` on the magnets involved, then the comparison map for `f⁻¹(Y), f⁻¹(E)` is bijective
for the action of `D(M)`. -/
theorem isFaceCartesian_of_along {Y E : AddSubmonoid Z} (hE : IsFace E Y)
    {N Q : AddSubmonoid M} (hQ : IsFace Q N) (eN : Y.comap f = N) (eQ : E.comap f = Q)
    (g : EquivariantHom aU aX)
    (hUY : ∀ T, Function.Bijective (ptAlong aU : AttractorPt aU (Y.comap f) T → _))
    (hUE : ∀ T, Function.Injective (ptAlong aU : AttractorPt aU (E.comap f) T → _))
    (hXY : ∀ T, Function.Injective (ptAlong aX : AttractorPt aX (Y.comap f) T → _))
    (h : IsFaceCartesian (homAlong f g) hE) : IsFaceCartesian g hQ := by
  subst eN
  subst eQ
  intro T
  constructor
  · intro φ ψ e
    have h1 : AttractorPt.push g φ = AttractorPt.push g ψ := congrArg (fun p => p.1.1) e
    have h2 : AttractorPt.ofFace hQ φ = AttractorPt.ofFace hQ ψ := congrArg (fun p => p.1.2) e
    apply (hUY T).1
    apply (h T).1
    refine Subtype.ext (Prod.ext ?_ ?_)
    · change AttractorPt.push (homAlong f g) _ = AttractorPt.push (homAlong f g) _
      rw [← ptAlong_push, ← ptAlong_push, h1]
    · change AttractorPt.ofFace hE _ = AttractorPt.ofFace hE _
      rw [← ptAlong_ofFace hE hQ, ← ptAlong_ofFace hE hQ, h2]
  · rintro ⟨⟨x, w⟩, hxw⟩
    change AttractorPt.ofFace hQ x = AttractorPt.push g w at hxw
    obtain ⟨u', hu'⟩ := (h T).2 ⟨(ptAlong aX x, ptAlong aU w), by
      change AttractorPt.ofFace hE (ptAlong aX x) = AttractorPt.push (homAlong f g) (ptAlong aU w)
      rw [← ptAlong_ofFace hE hQ, hxw]
      rfl⟩
    obtain ⟨u, rfl⟩ := (hUY T).2 u'
    have h1 : AttractorPt.push (homAlong f g) (ptAlong aU u) = ptAlong aX x :=
      congrArg (fun p => p.1.1) hu'
    have h2 : AttractorPt.ofFace hE (ptAlong aU u) = ptAlong aU w := congrArg (fun p => p.1.2) hu'
    refine ⟨u, Subtype.ext (Prod.ext (hXY T h1) (hUE T ?_))⟩
    change ptAlong aU (AttractorPt.ofFace hQ u) = _
    rw [ptAlong_ofFace hE hQ, h2]

end Along

section Main

variable {M : Type u} [AddCommGroup M] [AddGroup.FG M] {U W : BigFppfOver B S hS} [IsAffineHom U.hom.hom]
  {aU : AAction (fppfO B S hS) M (yoneda.obj U)} {aX : AAction (fppfO B S hS) M (yoneda.obj W)}

/-- A face of a finitely generated monoid is finitely generated. -/
lemma fg_of_isFace {Q N : AddSubmonoid M} (hQ : IsFace Q N) (hN : N.FG) : Q.FG := by
  classical
  obtain ⟨s, hs⟩ := hN
  refine ⟨s.filter (· ∈ Q), le_antisymm ?_ ?_⟩
  · refine (AddSubmonoid.closure_le).2 fun x hx => ?_
    exact (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
  · have key : ∀ x ∈ N, x ∈ Q → x ∈ AddSubmonoid.closure ((s.filter (· ∈ Q) : Finset M) : Set M) := by
      intro x hx
      rw [← hs] at hx
      induction hx using AddSubmonoid.closure_induction with
      | mem y hy =>
        intro hyQ
        exact AddSubmonoid.subset_closure (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hy, hyQ⟩))
      | zero => exact fun _ => zero_mem _
      | add a b ha hb iha ihb =>
        intro hab
        have ha' : a ∈ N := hs ▸ ha
        have hb' : b ∈ N := hs ▸ hb
        obtain ⟨h1, h2⟩ := hQ.mem_of_add_mem ha' hb' hab
        exact add_mem (iha h1) (ihb h2)
    exact fun x hx => key x (hQ.le hx) hx

/-- `0` is a face of `N/N^×`, in `M/N^×`. -/
lemma isFace_bot_quot (N : AddSubmonoid M) :
    IsFace (⊥ : AddSubmonoid (M ⧸ unitsSub N)) (N.map (QuotientAddGroup.mk' (unitsSub N))) where
  le := bot_le
  mem_of_add_mem := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ h
    have h0 : a + b ∈ unitsSub N := by
      have : (QuotientAddGroup.mk' (unitsSub N)) (a + b) = 0 := by
        rw [map_add]; exact h
      exact (QuotientAddGroup.eq_zero_iff _).1 this
    have hn : -(a + b) ∈ N := h0.2
    have ha' : a ∈ unitsSub N := ⟨ha, by
      have : -a = -(a + b) + b := by abel
      rw [this]; exact N.add_mem hn hb⟩
    have hb' : b ∈ unitsSub N := ⟨hb, by
      have : -b = -(a + b) + a := by abel
      rw [this]; exact N.add_mem hn ha⟩
    exact ⟨(QuotientAddGroup.eq_zero_iff _).2 ha', (QuotientAddGroup.eq_zero_iff _).2 hb'⟩

lemma comap_map_quot (N : AddSubmonoid M) :
    (N.map (QuotientAddGroup.mk' (unitsSub N))).comap (QuotientAddGroup.mk' (unitsSub N)) = N := by
  refine le_antisymm ?_ (AddSubmonoid.le_comap_map N)
  rintro x ⟨a, ha, e⟩
  have e' : -a + x ∈ unitsSub N := (QuotientAddGroup.eq).1 e
  have : x = a + (-a + x) := by abel
  rw [this]
  exact N.add_mem ha e'.1

lemma comap_bot_quot (N : AddSubmonoid M) :
    (⊥ : AddSubmonoid (M ⧸ unitsSub N)).comap (QuotientAddGroup.mk' (unitsSub N)) =
      (unitsSub N).toAddSubmonoid := by
  ext x
  exact QuotientAddGroup.eq_zero_iff x

/-- The case `Q = N^×`, by the reduction to `N` sharp in `M/N^×`, Proposition 3.31 (ii), and
the sharp case. -/
theorem isFaceCartesian_units_printed (hsep : IsSeparatedOver (yoneda.obj W))
    (g : EquivariantHom aU aX) (hf : Space.IsEtale B S hS g.hom) {N : AddSubmonoid M} (hN : N.FG)
    (hQ : IsFace (unitsSub N).toAddSubmonoid N) : IsFaceCartesian g hQ := by
  let f : M →+ (M ⧸ unitsSub N) := QuotientAddGroup.mk' (unitsSub N)
  haveI : AddMonoid.FG (M ⧸ unitsSub N) := AddGroup.fg_iff_addMonoid_fg.mp inferInstance
  haveI : AddMonoid.FG M := AddGroup.fg_iff_addMonoid_fg.mp inferInstance
  haveI : Countable M := countable_of_fg M
  refine isFaceCartesian_of_along (f := f) (isFace_bot_quot N) hQ (comap_map_quot N) (comap_bot_quot N) g
    (fun T => prop331_ii T) (fun T => (prop331_ii T).1) (fun T => (prop331_ii T).1) ?_
  exact isFaceCartesian_of_fg (isAlgebraicSpace_yoneda B S hS W) hsep (homAlong f g) hf
    (isFace_bot_quot N) (hN.map _)

/-- **Proposition 5.1 (i)**, printed proof, for `X` a separated scheme and `M` finitely generated: reduction to
`Q = N^×`, then to `N` sharp by Proposition 3.31. -/
theorem prop51_i_printed (hsep : IsSeparatedOver (yoneda.obj W))
    (g : EquivariantHom aU aX) (hf : Space.IsEtale B S hS g.hom) {Q N : AddSubmonoid M} (hQ : IsFace Q N)
    (hN : N.FG) : IsFaceCartesian g hQ := by
  have eU : unitsSub Q = unitsSub N := by
    ext x
    constructor
    · rintro ⟨a, b⟩
      exact ⟨hQ.le a, hQ.le b⟩
    · intro hx
      have hx' : x ∈ N ∧ -x ∈ N := hx
      have h0 : x + -x ∈ Q := by rw [add_neg_cancel]; exact Q.zero_mem
      obtain ⟨a, b⟩ := hQ.mem_of_add_mem hx'.1 hx'.2 h0
      exact ⟨a, b⟩
  have hE : IsFace (unitsSub Q).toAddSubmonoid Q := isFace_unitsSub Q
  refine IsFaceCartesian.of_face g hE hQ ?_ ?_
  · have key : ∀ (K : AddSubgroup M) (_ : K = unitsSub N) (hK : IsFace K.toAddSubmonoid N),
        IsFaceCartesian g hK := by
      rintro K rfl hK
      exact isFaceCartesian_units_printed hsep g hf hN hK
    exact key _ eU _
  · exact isFaceCartesian_units_printed hsep g hf (fg_of_isFace hQ hN) hE

end Main

end AlgMag

#print axioms AlgMag.prop51_i_printed
