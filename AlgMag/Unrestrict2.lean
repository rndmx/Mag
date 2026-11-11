/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec3Remaining
import AlgMag.Prop337General

/-!
# Proposition 3.31 (iii) without finite generation of `Z`

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026) 126–201, Proposition 3.31 (iii). The proof of
`AlgMag.prop331_iii` (Sec3Remaining.lean) used `[AddMonoid.FG Z]` only to put `Spec R_T[Z × Z]` in the site
(`contains_M`). Here that step is `P337.contains_alg` under the size condition `#Z < B.cutoff`; the rest of the
proof is the printed one, unchanged.
-/

universe u

section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Cardinal

namespace AlgMag.Unrestrict

open AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "Sch" => BigFppfOver.toScheme B S hS

/-- `#(Z × Z) < cutoff` from `#Z < cutoff`. -/
lemma cardZZ_lt (B : BigFppfSite.{u}) (Z : Type u) [h : Fact (#Z < B.cutoff)] : #(Z × Z) < B.cutoff := by
  rw [mk_prod, lift_id]
  exact mul_lt_of_lt B.aleph0_lt_cutoff.le h.out h.out

section Prop331

variable {M Z : Type u} [AddCommMonoid M] [AddCommGroup Z] [Fact (#Z < B.cutoff)]
variable {f : M →+ Z} {Y : AddSubmonoid Z}
variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {act : AAction (fppfO B S hS) M F}
variable (hf : Function.Injective f) (hY : ∀ y ∈ Y, ∃ m, f m = y)

section Crux

lemma contains_of_injCard (T : BigFppfOver B S hS) [IsAffine ((Sch).obj T)] {P : Type u} [AddCommMonoid P] (g : P →+ Z × Z)
    (hg : Function.Injective g) : B.Contains (Spec (.of (AddMonoidAlgebra (RT T) P))) := by
  have hM : B.Contains (Spec (.of (AddMonoidAlgebra (RT T) (Z × Z)))) := P337.contains_alg (cardZZ_lt B Z) (contains_RT T)
  refine Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hM ?_
  exact (Cardinal.mk_le_of_injective (AddMonoidAlgebra.mapDomain_injective (R := RT T) hg)).trans
    (le_max_right _ _)

/-- The structure ring map `R → R[P]`. -/
noncomputable abbrev ρP (T : BigFppfOver B S hS) (P : Type u) [AddCommMonoid P] : RT T →+* AddMonoidAlgebra (RT T) P :=
  algebraMap _ _

/-- **Proposition 3.31 (iii)**, core: on an affine `T` an `𝔸(Z)`-equivariant map is `𝔸(M)`-equivariant:
pass to the universal point over `R[M × N]`, inject into `R[Z × N]` (`𝔸(N)×D(Z)` is schematically
dense in `𝔸(N)×𝔸(M)`) and use `HasDensePullback`. -/
theorem along_equivariantCard (T : BigFppfOver B S hS) [IsAffine ((Sch).obj T)] (hd : HasDensePullback F) (ψ : AttractorPt (actAlong f act) Y T)
    (h : APt (fppfO B S hS) M (op T)) (a : APt (fppfO B S hS) (Y.comap f) (op T)) :
    ψ.app (𝟙 T) ((APt.toMagnet (Y.comap f) h * a).comp (eInv hf hY)) =
      act.smul h (ψ.app (𝟙 T) (a.comp (eInv hf hY))) := by
  let N := Y.comap f
  let e := magnetIso hf hY
  let g₁ : M × N →+ Z × N := AddMonoidHom.prodMap f (AddMonoidHom.id N)
  have hg₁ : Function.Injective g₁ := fun x y hxy => by
    have h1 := congrArg Prod.fst hxy
    have h2 := congrArg Prod.snd hxy
    exact Prod.ext (hf h1) h2
  let k₂ : Z × N →+ Z × Z := AddMonoidHom.prodMap (AddMonoidHom.id Z) (f.comp N.subtype)
  have hk₂ : Function.Injective k₂ := fun x y hxy => by
    have h1 := congrArg Prod.fst hxy
    have h2 := congrArg Prod.snd hxy
    exact Prod.ext h1 (Subtype.ext (hf h2))
  have hC₁ : B.Contains (Spec (.of (AddMonoidAlgebra (RT T) (M × N)))) :=
    contains_of_injCard T (k₂.comp g₁) (hk₂.comp hg₁)
  have hC₂ : B.Contains (Spec (.of (AddMonoidAlgebra (RT T) (Z × N)))) :=
    contains_of_injCard T k₂ hk₂
  let π : AddMonoidAlgebra (RT T) (M × N) →+* AddMonoidAlgebra (RT T) (Z × N) :=
    AddMonoidAlgebra.mapDomainRingHom _ g₁
  have hπ : π.comp (ρP T (M × N)) = ρP T (Z × N) := by
    refine RingHom.ext fun r => ?_
    change AddMonoidAlgebra.mapDomain g₁ (AddMonoidAlgebra.single 0 r) = AddMonoidAlgebra.single 0 r
    rw [AddMonoidAlgebra.mapDomain_single, map_zero]
  have hπi : Function.Injective π := AddMonoidAlgebra.mapDomain_injective hg₁
  let of₁ := AddMonoidAlgebra.of (RT T) (M × N)
  let of₂ := AddMonoidAlgebra.of (RT T) (Z × N)
  let hu₁ : Multiplicative M →* AddMonoidAlgebra (RT T) (M × N) :=
    of₁.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inl M N))
  let au₁ : Multiplicative N →* AddMonoidAlgebra (RT T) (M × N) :=
    of₁.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inr M N))
  let hz : Multiplicative Z →* AddMonoidAlgebra (RT T) (Z × N) :=
    of₂.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inl Z N))
  let au₂ : Multiplicative N →* AddMonoidAlgebra (RT T) (Z × N) :=
    of₂.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inr Z N))
  let εi : Multiplicative Y →* Multiplicative N := eInv hf hY
  have he : ∀ y : Y, f ((Multiplicative.toAdd (εi (Multiplicative.ofAdd y)) : N) : M) = (y : Z) := by
    intro y
    exact congrArg Subtype.val ((magnetIso hf hY).apply_symm_apply y)
  let t₁ := spToT T (ρP T (M × N)) hC₁
  let t₂ := spToT T (ρP T (Z × N)) hC₂
  -- the identity at the universal point of `R[M × N]`
  have E1 : ψ.app t₁ (spPt ((((hu₁.comp (AddMonoidHom.toMultiplicative N.subtype)) * au₁)).comp εi)) =
      act.smul (spPt hu₁) (ψ.app t₁ (spPt (au₁.comp εi))) := by
    refine hd T (hC := hC₁) (hC' := hC₂) π hπ hπi ?_
    rw [act.map_smul, spPt_res]
    have hL := app_sp ψ π hπ ((((hu₁.comp (AddMonoidHom.toMultiplicative N.subtype)) * au₁)).comp εi)
      (hC := hC₁) (hC₀ := hC₂)
    have hR := app_sp ψ π hπ (au₁.comp εi) (hC := hC₁) (hC₀ := hC₂)
    refine hL.trans (Eq.trans ?_ (congrArg _ hR).symm)
    have hE := ψ.equivariant t₂ (spPt hz) (spPt (π.toMonoidHom.comp (au₁.comp εi)))
    refine Eq.trans (congrArg (ψ.app t₂) ?_) (Eq.trans hE ?_)
    · refine MonoidHom.ext fun y => ?_
      have e1 : ∀ y : Y, π (of₁ (Multiplicative.ofAdd
          (((Multiplicative.toAdd (εi (Multiplicative.ofAdd y)) : N) : M), (0 : N))) *
          of₁ (Multiplicative.ofAdd ((0 : M), (Multiplicative.toAdd (εi (Multiplicative.ofAdd y)) : N)))) =
          hz (Multiplicative.ofAdd (y : Z)) *
            π (of₁ (Multiplicative.ofAdd ((0 : M), (Multiplicative.toAdd (εi (Multiplicative.ofAdd y)) : N)))) := by
        intro y
        rw [map_mul]
        congr 1
        change AddMonoidAlgebra.mapDomain g₁ (AddMonoidAlgebra.single _ 1) = AddMonoidAlgebra.single _ 1
        rw [AddMonoidAlgebra.mapDomain_single]
        congr 1
        exact Prod.ext (he y) rfl
      change spSec T (ρP T (Z × N)) hC₂ (π _) =
        spSec T (ρP T (Z × N)) hC₂ (hz _) * spSec T (ρP T (Z × N)) hC₂ _
      rw [← map_mul]
      exact congrArg _ (e1 (Multiplicative.toAdd y))
    · change act.smul _ _ = act.smul _ _
      congr 1
      refine MonoidHom.ext fun m => ?_
      change spSec T (ρP T (Z × N)) hC₂ _ = spSec T (ρP T (Z × N)) hC₂ _
      refine congrArg _ ?_
      change _ = AddMonoidAlgebra.mapDomain g₁ (AddMonoidAlgebra.single _ 1)
      rw [AddMonoidAlgebra.mapDomain_single]
      rfl
  -- specialise to `(h, a)`
  let Γ' := Γ((Sch).obj T, ⊤)
  let gm : Multiplicative (M × N) →* Γ' :=
    { toFun := fun p => h (Multiplicative.ofAdd (Multiplicative.toAdd p).1) *
        a (Multiplicative.ofAdd (Multiplicative.toAdd p).2)
      map_one' := by
        change h 1 * a 1 = 1
        rw [map_one, map_one, mul_one]
      map_mul' := fun p q => by
        change h (Multiplicative.ofAdd _ * Multiplicative.ofAdd _) *
          a (Multiplicative.ofAdd _ * Multiplicative.ofAdd _) = _
        rw [map_mul, map_mul]
        exact mul_mul_mul_comm _ _ _ _ }
  let Ψ : AddMonoidAlgebra (RT T) (M × N) →+* Γ' :=
    (AddMonoidAlgebra.lift (RT T) Γ' (M × N) gm).toRingHom
  have hΨ : Ψ.comp (ρP T (M × N)) = ((Sch).map (𝟙 T)).appTop.hom := by
    refine RingHom.ext fun r => ?_
    have : ((Sch).map (𝟙 T)).appTop.hom r = r := by simp
    rw [this]
    exact (AddMonoidAlgebra.lift (RT T) Γ' (M × N) gm).commutes r
  let s : T ⟶ spObj T (ρP T (M × N)) hC₁ := spLift T _ hC₁ (𝟙 T) Ψ hΨ
  have hst : s ≫ t₁ = 𝟙 T := spLift_toT T _ hC₁ (𝟙 T) Ψ hΨ
  have hres : ∀ {P : Type u} [AddCommMonoid P] (b : Multiplicative P →* AddMonoidAlgebra (RT T) (M × N))
      (c : APt (fppfO B S hS) P (op T)), (∀ p, Ψ (b p) = c p) →
      APt.res s.op (spPt (T := T) (ρ := ρP T (M × N)) (hC := hC₁) b) = c := by
    intro P _ b c hb
    refine MonoidHom.ext fun p => ?_
    rw [res_spPt_apply]
    exact (spLift_appTop T _ hC₁ (𝟙 T) Ψ hΨ _).trans (hb p)
  have hΨof : ∀ p : M × N, Ψ (of₁ (Multiplicative.ofAdd p)) =
      h (Multiplicative.ofAdd p.1) * a (Multiplicative.ofAdd p.2) := by
    intro p
    exact AddMonoidAlgebra.lift_of gm _
  have hh : APt.res s.op (spPt (T := T) (ρ := ρP T (M × N)) (hC := hC₁) hu₁) = h :=
    hres _ _ fun m => by
      refine (hΨof _).trans ?_
      change h _ * a 1 = _
      rw [map_one, mul_one]
      rfl
  have haa : APt.res s.op (spPt (T := T) (ρ := ρP T (M × N)) (hC := hC₁) (au₁.comp εi)) = a.comp (eInv hf hY) :=
    hres _ _ fun y => by
      refine (hΨof _).trans ?_
      change h 1 * a _ = _
      rw [map_one, one_mul]
      rfl
  have hmix : APt.res s.op (spPt (T := T) (ρ := ρP T (M × N)) (hC := hC₁)
      (((hu₁.comp (AddMonoidHom.toMultiplicative N.subtype)) * au₁).comp εi)) =
      (APt.toMagnet N h * a).comp (eInv hf hY) :=
    hres _ _ fun y => by
      refine (map_mul Ψ _ _).trans ?_
      refine (congrArg₂ (· * ·) (hΨof _) (hΨof _)).trans ?_
      change h _ * a 1 * (h 1 * a _) = _
      rw [map_one, map_one, mul_one, one_mul]
      rfl
  have key := congrArg (F.map s.op) E1
  rw [act.map_smul, hh] at key
  have n1 := ψ.naturality s t₁ (spPt (T := T) (ρ := ρP T (M × N)) (hC := hC₁)
    (((hu₁.comp (AddMonoidHom.toMultiplicative N.subtype)) * au₁).comp εi))
  have n2 := ψ.naturality s t₁ (spPt (T := T) (ρ := ρP T (M × N)) (hC := hC₁) (au₁.comp εi))
  rw [hst, hmix] at n1
  rw [hst, haa] at n2
  rw [n1, n2]
  exact key

omit [Fact (#Z < B.cutoff)] in
/-- Evaluation at the identity after base change. -/
lemma app_baseChange_idCard {T T' : BigFppfOver B S hS} {act' : AAction (fppfO B S hS) Z F}
    (t : T' ⟶ T) (ψ : AttractorPt act' Y T) (a : APt (fppfO B S hS) Y (op T')) :
    (AttractorPt.baseChange t ψ).app (𝟙 T') a = ψ.app t a := by
  change ψ.app (𝟙 T' ≫ t) a = _
  rw [Category.id_comp]

end Crux

/-- A point of `X^Y` for `𝔸(Z)` is a point of `X^N` for `𝔸(M)`, `X` separated (via
`HasDensePullback`). -/
noncomputable def ptOfAlongCard (hF : Presieve.IsSheaf (BigFppfOver.topology B S hS) F)
    (hd : HasDensePullback F) {T : BigFppfOver B S hS} (ψ : AttractorPt (actAlong f act) Y T) :
    AttractorPt act (Y.comap f) T where
  app t a := ψ.app t (a.comp (eInv hf hY))
  naturality s t a := ψ.naturality s t (a.comp (eInv hf hY))
  equivariant {T'} t h a := by
    let m0 := (APt.toMagnet (Y.comap f) h * a).comp (eInv hf hY)
    let m1 := a.comp (eInv hf hY)
    change ψ.app t m0 = act.smul h (ψ.app t m1)
    obtain ⟨I, V, π, hV, hS'⟩ := exists_affine_cover T'
    refine (hF _ hS').isSeparatedFor.ext fun W g hg => ?_
    obtain ⟨W', c, b, ⟨i⟩, rfl⟩ := hg
    have : IsAffine ((Sch).obj (V i)) := hV i
    suffices main : F.map (π i).op (ψ.app t m0) = F.map (π i).op (act.smul h (ψ.app t m1)) by
      simp only [op_comp, Functor.map_comp_apply]
      rw [main]
    rw [act.map_smul, ← ψ.naturality, ← ψ.naturality]
    have hc := along_equivariantCard hf hY (V i) hd (AttractorPt.baseChange (π i ≫ t) ψ)
      (APt.res (π i).op h) (APt.res (π i).op a)
    rw [app_baseChange_idCard, app_baseChange_idCard] at hc
    refine Eq.trans (congrArg (ψ.app (π i ≫ t)) (MonoidHom.ext fun y =>
      map_mul ((fppfO B S hS).map (π i).op).hom _ _)) hc

/-- **Proposition 3.31 (iii).** Let `f : M → Z` be injective into a finitely generated group (e.g.
`M` cancellative, `Z = M^gp`), `Y ⊆ f(M)` a magnet of `Z`, `N = f⁻¹(Y)`. If `X` is a sheaf with
`HasDensePullback` (e.g. a separated algebraic space, `hasDensePullback_of_separated`), then
`X^N_M = X^Y_Z`. The finite generation of `Z` is the size hypothesis of the site. -/
noncomputable def prop331_iiiCard (hF : Presieve.IsSheaf (BigFppfOver.topology B S hS) F)
    (hd : HasDensePullback F) (T : BigFppfOver B S hS) :
    AttractorPt act (Y.comap f) T ≃ AttractorPt (actAlong f act) Y T where
  toFun := ptAlong act
  invFun := ptOfAlongCard hf hY hF hd
  left_inv φ := by
    refine AttractorPt.ext ?_
    funext T' t a
    refine congrArg (φ.app t) (MonoidHom.ext fun n => ?_)
    refine congrArg a ?_
    exact congrArg Multiplicative.ofAdd ((magnetIso hf hY).symm_apply_apply _)
  right_inv ψ := by
    refine AttractorPt.ext ?_
    funext T' t a
    refine congrArg (ψ.app t) (MonoidHom.ext fun n => ?_)
    refine congrArg a ?_
    exact congrArg Multiplicative.ofAdd ((magnetIso hf hY).apply_symm_apply _)


/-- **Proposition 3.31 (iii)** as printed: `M` cancellative, `Z = M^gp`, `N = Y`, `X` separated:
`X^{N ⊂ M} = X^{Y ⊂ Z}`. Here `f : M → Z` is the embedding, `Y ⊆ f(M)`, and the separated algebraic space is
replaced by its consequence `HasDensePullback`. Only the size condition `#Z < B.cutoff` of the site is assumed on `Z`. -/
noncomputable def prop331_iii_gp {M : Type u} [AddCommMonoid M] [IsCancelAdd M]
    [Fact (#(Algebra.GrothendieckAddGroup M) < B.cutoff)] {Y : AddSubmonoid (Algebra.GrothendieckAddGroup M)}
    (hY : ∀ y ∈ Y, ∃ m, Algebra.GrothendieckAddGroup.of m = y)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {act : AAction (fppfO B S hS) M F}
    (hF : Presieve.IsSheaf (BigFppfOver.topology B S hS) F) (hd : HasDensePullback F) (T : BigFppfOver B S hS) :
    AttractorPt act (Y.comap (Algebra.GrothendieckAddGroup.of : M →+ _)) T ≃
      AttractorPt (actAlong Algebra.GrothendieckAddGroup.of act) Y T :=
  prop331_iiiCard Algebra.GrothendieckAddGroup.of_injective hY hF hd T

end Prop331

end AlgMag.Unrestrict

end

#print axioms AlgMag.Unrestrict.prop331_iiiCard
#print axioms AlgMag.Unrestrict.prop331_iii_gp
