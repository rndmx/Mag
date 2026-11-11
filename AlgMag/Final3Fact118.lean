/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec11SpacesFace

/-!
# Fact 11.8, as printed

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026), Fact 11.8. `T = Spec D`,
`T̄ = Spec D₁`, `ι : D → D₁` a first order thickening (surjective, square zero kernel).
The push-out of `𝔸(F)_T ← 𝔸(F)_T̄ → 𝔸(N)_T̄` is `Spec` of `pushoutRing hF ι`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.Final3Fact118

open AlgMag.GB AlgMag.Lifts AlgMag.SmoothSchemes AlgMag.SpacesLift

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {M : Type u} [AddCommGroup M] [SM B M] [DecidableEq M]
  (N : AddSubmonoid M) {F : AddSubmonoid M} (hF : IsFace F N)
  {D D₁ : Type u} [CommRing D] [CommRing D₁] [SR B D] [SR B D₁] (ι : D →+* D₁)

/-- **Fact 11.8 (A)**: `Spec (pushoutRing)` is the push-out of `𝔸(F)_T ← 𝔸(F)_T̄ → 𝔸(N)_T̄` in
algebraic spaces over `S`: sections of any algebraic space glue uniquely. Here `s` is any
structure map of the push-out to `S`. -/
theorem fact118_pushout_spaces (hι : Function.Surjective ι)
    (hsq : ∀ x y, ι x = 0 → ι y = 0 → x * y = 0)
    (s : Spec (CommRingCat.of (pushoutRing hF ι)) ⟶ S)
    (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hP : IsAlgebraicSpace B S hS P)
    (f : P.obj (op (Sv B hS (sp (pFst N hF ι) ≫ s))))
    (g : P.obj (op (Sv B hS (sp (pSnd N hF ι) ≫ s))))
    (h : pb P (svHom B hS (AddMonoidAlgebra.mapRingHom F ι)
        (rfl : _ = sp (AddMonoidAlgebra.mapRingHom F ι) ≫ sp (pFst N hF ι) ≫ s)) f =
      pb P (svHom B hS (faceRingHom hF D₁) (by
        rw [← Category.assoc, ← Category.assoc, ← sp_comp, ← sp_comp]
        exact congrArg (fun φ => sp φ ≫ s) (RingHom.ext fun z => z.2.symm))) g) :
    ∃! k : P.obj (op (Sv B hS s)),
      pb P (svHom B hS (pFst N hF ι) rfl) k = f ∧ pb P (svHom B hS (pSnd N hF ι) rfl) k = g :=
  glue (milnor_pushout N hF ι hι) (pSnd_surjective N hF ι hι)
    (fun y hy => pFst_ker N hF ι y hy) (magnetAlgebra_mul_eq_zero ι hsq) rfl rfl rfl _ P hP f g h

/-- **Fact 11.8 (A), over `T`**: if `f, g` are morphisms over `T` (through a map `π : P ⟶ T` and a
structure map `τ` of the push-out to `T`), the glued `k` is over `T`. -/
theorem fact118_overT (hι : Function.Surjective ι)
    (hsq : ∀ x y, ι x = 0 → ι y = 0 → x * y = 0)
    (s : Spec (CommRingCat.of (pushoutRing hF ι)) ⟶ S)
    (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (T : BigFppfOver B S hS) (π : P ⟶ yoneda.obj T) (τ : Sv B hS s ⟶ T)
    (k : P.obj (op (Sv B hS s)))
    (hf : π.app _ (pb P (svHom B hS (pFst N hF ι) rfl) k) = svHom B hS (pFst N hF ι) rfl ≫ τ)
    (hg : π.app _ (pb P (svHom B hS (pSnd N hF ι) rfl) k) = svHom B hS (pSnd N hF ι) rfl ≫ τ) :
    π.app _ k = τ := by
  have nat : ∀ {W W' : BigFppfOver B S hS} (u : W' ⟶ W) (z : P.obj (op W)),
      π.app _ (pb P u z) = pb (yoneda.obj T) u (π.app _ z) := fun u z =>
    NatTrans.naturality_apply π u.op z
  obtain ⟨_, _, hu⟩ := fact118_pushout_spaces N hF ι hι hsq s (yoneda.obj T)
    (isAlgebraicSpace_yoneda B S hS T)
    (svHom B hS (pFst N hF ι) rfl ≫ τ) (svHom B hS (pSnd N hF ι) rfl ≫ τ) (by
      change _ ≫ _ ≫ τ = _ ≫ _ ≫ τ
      refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ τ) ?_).trans (Category.assoc _ _ _))
      exact site_ext (sp_sq (RingHom.ext fun z => (milnor_pushout N hF ι hι).comm z)))
  have e1 := hu (π.app _ k) ⟨by rw [← nat]; exact hf, by rw [← nat]; exact hg⟩
  have e2 := hu τ ⟨rfl, rfl⟩
  exact e1.trans e2.symm

/-- **Fact 11.8 (C)**: the coaction `coactP` of `M` on the push-out ring makes `ν₁` (`pFst`)
`D(M)_T`-equivariant. -/
theorem fact118_equivariant_fst (hι : Function.Surjective ι) :
    (AddMonoidAlgebra.mapRingHom M (pFst N hF ι)).comp (coactP (M := M) N hF ι hι) =
      (coactN (M := M) F D).comp (pFst N hF ι) :=
  RingHom.ext fun p => coactP_fst N hF ι hι p

/-- **Fact 11.8 (C)**: `ν₂` (`pSnd`) is `D(M)_T`-equivariant. -/
theorem fact118_equivariant_snd (hι : Function.Surjective ι) :
    (AddMonoidAlgebra.mapRingHom M (pSnd N hF ι)).comp (coactP (M := M) N hF ι hι) =
      (coactN (M := M) N D₁).comp (pSnd N hF ι) :=
  RingHom.ext fun p => coactP_snd N hF ι hι p

section Equivariant

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (aX : AAction (fppfO B S hS) M X)
  (hι : Function.Surjective ι)
  (s : Spec (CommRingCat.of (pushoutRing hF ι)) ⟶ S)
  (s₁ : Spec (CommRingCat.of (AddMonoidAlgebra (pushoutRing hF ι) M)) ⟶ S)

omit [DecidableEq M] in
lemma fstC (hc : sp (cst (pushoutRing hF ι) M) ≫ s = s₁) :
    sp (cst _ M) ≫ sp (pFst N hF ι) ≫ s = sp (AddMonoidAlgebra.mapRingHom M (pFst N hF ι)) ≫ s₁ :=
  (tri (sp_sq (RingHom.ext fun p => (map_cst (pFst N hF ι) p).symm)) s).trans
    (congrArg (sp _ ≫ ·) hc)

omit [DecidableEq M] in
lemma sndC (hc : sp (cst (pushoutRing hF ι) M) ≫ s = s₁) :
    sp (cst _ M) ≫ sp (pSnd N hF ι) ≫ s = sp (AddMonoidAlgebra.mapRingHom M (pSnd N hF ι)) ≫ s₁ :=
  (tri (sp_sq (RingHom.ext fun p => (map_cst (pSnd N hF ι) p).symm)) s).trans
    (congrArg (sp _ ≫ ·) hc)

lemma fstR (hρ : sp (coactP (M := M) N hF ι hι) ≫ s = s₁) :
    sp (coactN (M := M) F D) ≫ sp (pFst N hF ι) ≫ s =
      sp (AddMonoidAlgebra.mapRingHom M (pFst N hF ι)) ≫ s₁ :=
  (tri (sp_sq (RingHom.ext fun p => (coactP_fst N hF ι hι p).symm)) s).trans
    (congrArg (sp _ ≫ ·) hρ)

lemma sndR (hρ : sp (coactP (M := M) N hF ι hι) ≫ s = s₁) :
    sp (coactN (M := M) N D₁) ≫ sp (pSnd N hF ι) ≫ s =
      sp (AddMonoidAlgebra.mapRingHom M (pSnd N hF ι)) ≫ s₁ :=
  (tri (sp_sq (RingHom.ext fun p => (coactP_snd N hF ι hι p).symm)) s).trans
    (congrArg (sp _ ≫ ·) hρ)

/-- **Fact 11.8 (D)**: the push-out is a push-out for `D(M)_T`-equivariant morphisms. If a section
`k` of an algebraic space `X` with `D(M)`-action `aX` over the push-out restricts along `ν₁`, `ν₂`
to equivariant sections, then `k` is equivariant. Equivariance is written through the universal
point of `D(M)`, as in `Sec11SpacesFace`. Together with `fact118_pushout_spaces` (existence and
uniqueness of `k`), this is the push-out in the equivariant category. -/
theorem fact118_equivariant_desc (hsq : ∀ x y, ι x = 0 → ι y = 0 → x * y = 0)
    (hρ : sp (coactP (M := M) N hF ι hι) ≫ s = s₁) (hc : sp (cst (pushoutRing hF ι) M) ≫ s = s₁)
    (hX : IsAlgebraicSpace B S hS X) (k : X.obj (op (Sv B hS s)))
    (hf : pb X (svHom B hS (coactN (M := M) F D) (fstR N hF ι hι s s₁ hρ))
        (pb X (svHom B hS (pFst N hF ι) rfl) k) =
      ss aX (eS B hS _ (eU _ M)) (pb X (svHom B hS (cst _ M) (fstC N hF ι s s₁ hc))
        (pb X (svHom B hS (pFst N hF ι) rfl) k)))
    (hg : pb X (svHom B hS (coactN (M := M) N D₁) (sndR N hF ι hι s s₁ hρ))
        (pb X (svHom B hS (pSnd N hF ι) rfl) k) =
      ss aX (eS B hS _ (eU _ M)) (pb X (svHom B hS (cst _ M) (sndC N hF ι s s₁ hc))
        (pb X (svHom B hS (pSnd N hF ι) rfl) k))) :
    pb X (svHom B hS (coactP (M := M) N hF ι hι) hρ) k =
      ss aX (eS B hS s₁ (eU (pushoutRing hF ι) M)) (pb X (svHom B hS (cst _ M) hc) k) := by
  let H := milnor_pushout N hF ι hι
  let HM := milnor_map (M := M) H
  let pF : Sv B hS (sp (pFst N hF ι) ≫ s) ⟶ Sv B hS s := svHom B hS (pFst N hF ι) rfl
  let pS : Sv B hS (sp (pSnd N hF ι) ≫ s) ⟶ Sv B hS s := svHom B hS (pSnd N hF ι) rfl
  let sF₁ := sp (AddMonoidAlgebra.mapRingHom M (pFst N hF ι)) ≫ s₁
  let s₀₁ := sp (AddMonoidAlgebra.mapRingHom M (pSnd N hF ι)) ≫ s₁
  let PM : Sv B hS sF₁ ⟶ Sv B hS s₁ := svHom B hS (AddMonoidAlgebra.mapRingHom M (pFst N hF ι)) rfl
  let QM : Sv B hS s₀₁ ⟶ Sv B hS s₁ := svHom B hS (AddMonoidAlgebra.mapRingHom M (pSnd N hF ι)) rfl
  have hιq : ∀ a b, AddMonoidAlgebra.mapRingHom F ι a = 0 → AddMonoidAlgebra.mapRingHom F ι b = 0 →
      a * b = 0 := magnetAlgebra_mul_eq_zero ι hsq
  have hsqM : (AddMonoidAlgebra.mapRingHom M (AddMonoidAlgebra.mapRingHom F ι)).comp
      (AddMonoidAlgebra.mapRingHom M (pFst N hF ι)) =
      (AddMonoidAlgebra.mapRingHom M (faceRingHom hF D₁)).comp
        (AddMonoidAlgebra.mapRingHom M (pSnd N hF ι)) := RingHom.ext fun w => HM.comm w
  have hd₀ : sp (AddMonoidAlgebra.mapRingHom M (faceRingHom hF D₁)) ≫ s₀₁ =
      sp (AddMonoidAlgebra.mapRingHom M (AddMonoidAlgebra.mapRingHom F ι)) ≫ sF₁ :=
    (tri (sp_sq hsqM) s₁).symm
  refine (glue HM (mapRingHom_surjective _ (pSnd_surjective N hF ι hι)) (fun y hy => by
      obtain ⟨z, h₁, h₂⟩ := HM.ex y 0 (by rw [hy, map_zero])
      exact ⟨z, h₁, h₂⟩)
    (map_sq_zero _ hιq) rfl rfl rfl hd₀ X hX _ _ ?_).unique ⟨rfl, rfl⟩ ⟨?_, ?_⟩
  · refine pb_sq X ?_ _
    exact site_ext (sp_sq hsqM)
  · have l₁ := pb_sq X (u := PM) (v := svHom B hS (cst _ M) hc)
      (w := svHom B hS (cst _ M) (fstC N hF ι s s₁ hc)) (x := pF)
      (site_ext (sp_sq (RingHom.ext fun p => map_cst _ p))) k
    have l₃ : APt.res PM.op (eS B hS s₁ (eU (pushoutRing hF ι) M)) = eS B hS sF₁ (eU _ M) :=
      (res_eS _ _ _).trans (eS_congr _ (hof _))
    have l₀ := pb_sq X (u := PM) (v := svHom B hS (coactP (M := M) N hF ι hι) hρ)
      (w := svHom B hS (coactN (M := M) F D) (fstR N hF ι hι s s₁ hρ)) (x := pF)
      (site_ext (sp_sq (RingHom.ext fun p => coactP_fst N hF ι hι p))) k
    refine Eq.symm ?_
    rw [pb_ss, l₃, l₁]
    exact l₀.trans hf
  · have l₁ := pb_sq X (u := QM) (v := svHom B hS (cst _ M) hc)
      (w := svHom B hS (cst _ M) (sndC N hF ι s s₁ hc)) (x := pS)
      (site_ext (sp_sq (RingHom.ext fun p => map_cst _ p))) k
    have l₃ : APt.res QM.op (eS B hS s₁ (eU (pushoutRing hF ι) M)) = eS B hS s₀₁ (eU _ M) :=
      (res_eS _ _ _).trans (eS_congr _ (hof _))
    have l₀ := pb_sq X (u := QM) (v := svHom B hS (coactP (M := M) N hF ι hι) hρ)
      (w := svHom B hS (coactN (M := M) N D₁) (sndR N hF ι hι s s₁ hρ)) (x := pS)
      (site_ext (sp_sq (RingHom.ext fun p => coactP_snd N hF ι hι p))) k
    refine Eq.symm ?_
    rw [pb_ss, l₃, l₁]
    exact l₀.trans hg

end Equivariant

end AlgMag.Final3Fact118
