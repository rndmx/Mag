/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec11SpacesLift

/-!
# Corollary 10.3 for algebraic spaces, as a square of equivariant morphisms

Mayeux, *Algebraic Magnetism*, Corollary 10.3, with the agreed correction `X'` affine. `X' = Spec A₁`, and
`X = Spec A` is a first order thickening of it, so `X` is affine too. The actions of `D(M)` on `X'`, `X`, `Y`,
`Z` are actions on functors, the sides of the square are equivariant morphisms, and the conclusion is an
equivariant morphism. `M` is any commutative group below the cutoff of the site, and `X' → S`
need not be quasi-compact; `Y → Z` need not be locally of finite type. So the printed "M finitely generated",
"X → S quasi-compact and quasi-separated", "locally of finite type" are not used.

The coaction of `A₁` is recovered from the action at the universal point. The filling is the integration of
`g⁻¹ α g`, `AlgMag.SpacesLift.exists_equivariant_of_lift`, which is the content of Proposition 9.13 for the
coefficients at hand.
-/

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace AlgMag.SpacesLift

open AlgMag.GB AlgMag.Lifts

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A morphism of the site between spectra is the spectrum of a ring map. -/
lemma exists_ring_of_site {R R₁ : Type u} [CommRing R] [CommRing R₁] [SR B R] [SR B R₁]
    {s : Spec (CommRingCat.of R) ⟶ S} {s₁ : Spec (CommRingCat.of R₁) ⟶ S}
    (u : Sv B hS s₁ ⟶ Sv B hS s) :
    ∃ (g : R →+* R₁) (h : sp g ≫ s = s₁), u = svHom B hS g h := by
  let m : Spec (CommRingCat.of R₁) ⟶ Spec (CommRingCat.of R) := (BigFppfOver.toScheme B S hS).map u
  have hm : m ≫ s = s₁ := congrArg (fun k => k.hom) (Over.w u)
  have e : sp (Spec.preimage m).hom = m := by
    change Spec.map (CommRingCat.ofHom (Spec.preimage m).hom) = m
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  exact ⟨(Spec.preimage m).hom, (congrArg (· ≫ s) e).trans hm, site_ext e.symm⟩

lemma ring_ext_of_sp {R R₁ R₂ R₃ : Type u} [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing R₃]
    {g : R →+* R₁} {g₁ : R₁ →+* R₂} {g₃ : R →+* R₃} {g₄ : R₃ →+* R₂}
    (e : sp g₁ ≫ sp g = sp g₄ ≫ sp g₃) (x : R) : g₁ (g x) = g₄ (g₃ x) := by
  rw [← sp_comp, ← sp_comp] at e
  have h := Spec.map_injective e
  exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom h) x

/-- A morphism from a representable functor is its value at the identity, pulled back. -/
lemma app_eq_pb {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {W T : BigFppfOver B S hS}
    (α : yoneda.obj W ⟶ P) (x : T ⟶ W) : α.app (op T) x = pb P x (α.app (op W) (𝟙 W)) := by
  have := NatTrans.naturality_apply α x.op (𝟙 W)
  simpa using this

variable {M : Type u} [AddCommGroup M] {A₁ A : Type u} [CommRing A₁] [CommRing A] [SR B A₁] [SR B A]
  [SM B M]

/-- **Corollary 10.3**, `X'` affine, `Y`, `Z` algebraic spaces: the printed square. `X' = Spec A₁`,
`i : X = Spec A → X'` the first order thickening given by a surjection `φ` with square zero kernel. All four
functors carry actions of `D(M)`, the four sides are equivariant, and `Y → Z` is formally smooth. Then there
is an equivariant `l : X' → Y` with `l ∘ i = a` and `f ∘ l = b`. -/
theorem cor103_square (φ : A₁ →+* A) (hs : Function.Surjective φ)
    (hq : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0) (t : Spec (CommRingCat.of A₁) ⟶ S)
    {P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P)
    (hQ : IsAlgebraicSpace B S hS Q)
    {aX' : AAction (fppfO B S hS) M (yoneda.obj (Sv B hS t))}
    {aX : AAction (fppfO B S hS) M (yoneda.obj (Sv B hS (sp φ ≫ t)))}
    {aY : AAction (fppfO B S hS) M P} {aZ : AAction (fppfO B S hS) M Q}
    (i : EquivariantHom aX aX') (hi : i.hom = yoneda.map (svHom B hS φ rfl))
    (a : EquivariantHom aX aY) (b : EquivariantHom aX' aZ) (f : EquivariantHom aY aZ)
    (hf : Space.FormallySmooth f.hom) (w : a.hom ≫ f.hom = i.hom ≫ b.hom) :
    ∃ l : EquivariantHom aX' aY, i.hom ≫ l.hom = a.hom ∧ l.hom ≫ f.hom = b.hom := by
  let X' := Sv B hS t
  let iS : Sv B hS (sp φ ≫ t) ⟶ X' := svHom B hS φ rfl
  have hiapp : ∀ {T : BigFppfOver B S hS} (x : T ⟶ Sv B hS (sp φ ≫ t)),
      i.hom.app (op T) x = x ≫ iS := fun x => by rw [hi]; rfl
  -- the coaction of `A₁`
  let s₁ := sp (cst A₁ M) ≫ t
  let c : Sv B hS s₁ ⟶ X' := svHom B hS (cst A₁ M) rfl
  let E := eS B hS s₁ (eU A₁ M)
  let r : Sv B hS s₁ ⟶ X' := aX'.smul E c
  obtain ⟨ρ, hρt, hρ⟩ := exists_ring_of_site (hS := hS) r
  -- the coaction of `A`
  have h₀c : sp (cst A M) ≫ sp φ ≫ t = sp (AddMonoidAlgebra.mapRingHom M φ) ≫ sp (cst A₁ M) ≫ t :=
    tri (sp_sq (RingHom.ext fun w => (map_cst φ w).symm)) t
  let s₁₀ := sp (AddMonoidAlgebra.mapRingHom M φ) ≫ sp (cst A₁ M) ≫ t
  let c₀ : Sv B hS s₁₀ ⟶ Sv B hS (sp φ ≫ t) := svHom B hS (cst A M) h₀c
  let E₀ := eS B hS s₁₀ (eU A M)
  let r₀ : Sv B hS s₁₀ ⟶ Sv B hS (sp φ ≫ t) := aX.smul E₀ c₀
  obtain ⟨ρ₀, h₀ρ, hρ₀⟩ := exists_ring_of_site (hS := hS) r₀
  let m : Sv B hS s₁₀ ⟶ Sv B hS s₁ := svHom B hS (AddMonoidAlgebra.mapRingHom M φ) rfl
  have hmE : APt.res m.op E = E₀ := (res_eS _ _ _).trans (eS_congr _ (hof φ))
  have hmc : m ≫ c = c₀ ≫ iS := site_ext (sp_sq (RingHom.ext fun w => map_cst φ w))
  have key₁ : m ≫ r = r₀ ≫ iS := by
    have h₁ : r₀ ≫ iS = aX'.smul E₀ (c₀ ≫ iS) := by
      rw [← hiapp, ← hiapp]
      exact i.map_smul E₀ c₀
    have h₂ : m ≫ r = aX'.smul (APt.res m.op E) (m ≫ c) := pb_ss aX' m E c
    rw [h₁, h₂, hmE, hmc]
  have hρφ : ∀ x, AddMonoidAlgebra.mapRingHom M φ (ρ x) = ρ₀ (φ x) := by
    refine ring_ext_of_sp ?_
    have := congrArg (BigFppfOver.toScheme B S hS).map key₁
    rw [Functor.map_comp, Functor.map_comp, hρ, hρ₀] at this
    exact this
  -- the coaction axiom
  have hco : ∀ x, AddMonoidAlgebra.mapRingHom M ρ (ρ x) = diag A₁ M (ρ x) := by
    let s₂ := sp (cst (AddMonoidAlgebra A₁ M) M) ≫ sp (cst A₁ M) ≫ t
    let τ : Sv B hS s₂ ⟶ Sv B hS s₁ := svHom B hS (AddMonoidAlgebra.mapRingHom M ρ) (hτs t ρ hρt)
    let μ : Sv B hS s₂ ⟶ Sv B hS s₁ := svHom B hS (diag A₁ M) (hμs t)
    let c₂ : Sv B hS s₂ ⟶ Sv B hS s₁ := svHom B hS (cst (AddMonoidAlgebra A₁ M) M) rfl
    have hτc : τ ≫ c = c₂ ≫ r := by
      rw [hρ]
      exact site_ext (sp_sq (RingHom.ext fun x => map_cst ρ x))
    have hμc : μ ≫ c = c₂ ≫ c := site_ext (sp_sq (RingHom.ext fun x => diag_cst x))
    have e₁ : APt.res τ.op E = eS B hS s₂ (eU (AddMonoidAlgebra A₁ M) M) :=
      (res_eS _ _ _).trans (eS_congr _ (hof ρ))
    have e₂ : APt.res c₂.op E = eS B hS s₂ ((cst (AddMonoidAlgebra A₁ M) M).toMonoidHom.comp (eU A₁ M)) :=
      res_eS _ _ _
    have e₃ : APt.res μ.op E = eS B hS s₂ ((cst (AddMonoidAlgebra A₁ M) M).toMonoidHom.comp (eU A₁ M)) *
        eS B hS s₂ (eU (AddMonoidAlgebra A₁ M) M) :=
      (res_eS _ _ _).trans ((eS_congr _ hμe).trans (eS_mul _ _ _))
    have key₂ : τ ≫ r = μ ≫ r := by
      have h₁ : τ ≫ r = aX'.smul (APt.res τ.op E) (τ ≫ c) := pb_ss aX' τ E c
      have h₂ : μ ≫ r = aX'.smul (APt.res μ.op E) (μ ≫ c) := pb_ss aX' μ E c
      have h₃ : c₂ ≫ r = aX'.smul (APt.res c₂.op E) (c₂ ≫ c) := pb_ss aX' c₂ E c
      rw [h₁, h₂, hτc, h₃, hμc, e₁, e₂, e₃, mul_comm]
      exact ss_ss aX' _ _ _
    refine ring_ext_of_sp ?_
    have := congrArg (BigFppfOver.toScheme B S hS).map key₂
    rw [Functor.map_comp, Functor.map_comp, hρ] at this
    exact this
  -- the sides of the square, as sections
  let a₀ : P.obj (op (Sv B hS (sp φ ≫ t))) := a.hom.app _ (𝟙 _)
  let b₀ : Q.obj (op X') := b.hom.app _ (𝟙 X')
  have ha : pb P (svHom B hS ρ₀ h₀ρ) a₀ = ss aY (eS B hS _ (eU A M)) (pb P (svHom B hS (cst A M) h₀c) a₀) := by
    rw [← hρ₀, ← app_eq_pb, ← app_eq_pb]
    exact a.map_smul E₀ c₀
  have hb : pb Q (svHom B hS ρ hρt) b₀ =
      ss aZ (eS B hS (sp (cst A₁ M) ≫ t) (eU A₁ M)) (pb Q (svHom B hS (cst A₁ M) rfl) b₀) := by
    rw [← hρ, ← app_eq_pb, ← app_eq_pb]
    exact b.map_smul E c
  have hw : f.hom.app _ a₀ = pb Q (svHom B hS φ (s := t) rfl) b₀ := by
    have h₁ := congrArg (fun q => q.app (op (Sv B hS (sp φ ≫ t))) (𝟙 _)) w
    refine h₁.trans ?_
    change b.hom.app _ (i.hom.app _ (𝟙 _)) = _
    rw [hiapp, Category.id_comp, app_eq_pb]
  obtain ⟨α, hα₁, hα₂⟩ := hf _ _ (inferInstanceAs (IsAffine (Spec _)))
    (inferInstanceAs (IsAffine (Spec _))) (svHom B hS φ (s := t) rfl)
    (sqZero_svHom φ hs hq) a₀ b₀ hw
  obtain ⟨l, hl₁, hl₂, hl₃⟩ := exists_equivariant_of_lift φ hs hq t ρ ρ₀ hρt hρφ hco hP hQ f a₀ b₀ α hα₁ hα₂
    h₀ρ h₀c ha hb
  -- `l` is equivariant on every object of the site
  refine ⟨⟨yonedaEquiv.symm l, ?_⟩, ?_, ?_⟩
  · rintro ⟨T₁⟩ h (x : T₁ ⟶ X')
    obtain ⟨κ, hκ, he⟩ := exists_classifyS (M := M) (s₀ := t) x h
    have hκr : κ ≫ r = aX'.smul h x := by
      have h₁ : κ ≫ r = aX'.smul (APt.res κ.op E) (κ ≫ c) := pb_ss aX' κ E c
      rw [h₁, he, hκ]
    change pb P (aX'.smul h x) l = aY.smul h (pb P x l)
    have e₁ : pb P r l = ss aY E (pb P c l) := by rw [hρ]; exact hl₃
    have e₂ : pb P x l = pb P κ (pb P c l) := by rw [← hκ, pb_comp]
    rw [← hκr, pb_comp, e₁, e₂]
    refine (pb_ss aY κ _ _).trans ?_
    rw [he]
  · refine NatTrans.ext (funext fun U => ?_)
    obtain ⟨T⟩ := U
    ext (x : T ⟶ Sv B hS (sp φ ≫ t))
    change pb P (i.hom.app _ x) l = a.hom.app _ x
    rw [hiapp, pb_comp, hl₁, app_eq_pb]
  · refine NatTrans.ext (funext fun U => ?_)
    obtain ⟨T⟩ := U
    ext (x : T ⟶ X')
    change f.hom.app _ (pb P x l) = b.hom.app _ x
    rw [NatTrans.naturality_apply f.hom x.op l, hl₂, app_eq_pb]

end AlgMag.SpacesLift

#print axioms AlgMag.SpacesLift.cor103_square
