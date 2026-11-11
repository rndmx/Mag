/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec12PrintedRing
import AlgMag.GeneralBase
import AlgMag.Sec11Formal
import AlgMag.Sec12Topology
import Mathlib.Algebra.MonoidAlgebra.Grading
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Corollary 12.5

Mayeux, *Algebraic Magnetism*, Corollary 12.5: for `N` fine and sharp, if `𝔸(N)_S → S` is smooth, it
is a vector bundle. "Corollary 12.5 follows from the proof of Theorem 12.4": over an affine `T → S`,
`O(𝔸(N)_T) = R[N]` is `N`-graded with degree zero part `R`; `printed_ring` applies with `I/I²` of
`R[N] → R`.
-/

suppress_compilation

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

open scoped Classical

universe u

namespace AlgMag.Sec12Printed

open AlgMag.GB

variable {S : Scheme.{u}} {M : Type u} [AddCommGroup M] (N : AddSubmonoid M)

/-- `𝔸(N)_T = 𝔸(N)_S ×_S T`, for `T` affine over `S`. -/
theorem isPullback_magnet (T : Over S) [IsAffine T.left] :
    IsPullback ((pts (Over.mk (magnetπ N T.left ≫ T.hom))).symm (magnetU N T.left)).left
      (magnetπ N T.left) (A N S).hom T.hom := by
  let Tm : Over S := Over.mk (magnetπ N T.left ≫ T.hom)
  let h := (pts Tm).symm (magnetU N T.left)
  have key : ∀ {W : Over S} (l : W ⟶ Tm) (n), (pts W (l ≫ h)) n = l.left.appTop.hom (magnetU N T.left n) := by
    intro W l n
    have e := (pts Tm).apply_symm_apply (magnetU N T.left)
    have e2 : (pts Tm h) n = magnetU N T.left n := DFunLike.congr_fun e n
    rw [pts_comp]
    exact congrArg l.left.appTop.hom e2
  refine ⟨⟨Over.w h⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => ?_) (fun s => ?_) (fun s => ?_) (fun s m h₁ h₂ => ?_)⟩⟩
  · exact magnetLift N s.snd (pts (Over.mk (s.snd ≫ T.hom)) (Over.homMk s.fst s.condition))
  · let a' : Over.mk (s.snd ≫ T.hom) ⟶ A N S := Over.homMk s.fst s.condition
    let l : Over.mk (s.snd ≫ T.hom) ⟶ Tm := Over.homMk (magnetLift N s.snd (pts _ a')) (by
      change _ ≫ magnetπ N T.left ≫ T.hom = s.snd ≫ T.hom
      rw [← Category.assoc]
      exact congrArg (· ≫ T.hom) (magnetLift_π N s.snd _))
    have e : l ≫ h = a' := by
      refine (pts _).injective (MonoidHom.ext fun n => ?_)
      rw [key]
      exact magnetLift_res N s.snd (pts _ a') n
    exact congrArg (fun k => k.left) e
  · exact magnetLift_π N s.snd _
  · let a' : Over.mk (s.snd ≫ T.hom) ⟶ A N S := Over.homMk s.fst s.condition
    let l : Over.mk (s.snd ≫ T.hom) ⟶ Tm := Over.homMk m (by
      change m ≫ magnetπ N T.left ≫ T.hom = _
      rw [← Category.assoc, h₂]
      rfl)
    refine magnetLift_uniq N s.snd _ m h₂ fun n => ?_
    have e : l ≫ h = a' := Over.OverMorphism.ext h₁
    have := key l n
    rw [e] at this
    exact this.symm

/-- **Corollary 12.5.** `N` is finitely generated and sharp. If `𝔸(N)_S → S` is smooth, then for
every affine `T → S`, with `R = Γ(T)`, the module `P = I/I²` of the augmentation `R[N] → R` is finite
projective and `R[N] = Sym_R(P)`. -/
theorem cor125 (hfg : N.FG) (hsharp : ∀ x ∈ N, -x ∈ N → x = 0) [Smooth (A N S).hom] (T : Over S)
    [IsAffine T.left] :
    ∃ π : AddMonoidAlgebra Γ(T.left, ⊤) N →ₐ[Γ(T.left, ⊤)] Γ(T.left, ⊤),
      Module.Finite Γ(T.left, ⊤) (Conormal π) ∧ Module.Projective Γ(T.left, ⊤) (Conormal π) ∧
      Nonempty (SymmetricAlgebra Γ(T.left, ⊤) (Conormal π) ≃ₐ[Γ(T.left, ⊤)]
        AddMonoidAlgebra Γ(T.left, ⊤) N) := by
  have hface : IsFace (⊥ : AddSubmonoid M) N := by
    refine ⟨bot_le, fun {x y} hx hy h => ?_⟩
    have e : x + y = 0 := h
    have hx0 : x = 0 := hsharp x hx (by rwa [neg_eq_of_add_eq_zero_right e])
    have hy0 : y = 0 := by simpa [hx0] using e
    exact ⟨hx0, hy0⟩
  obtain ⟨w, hw⟩ := exists_weight_of_isFace hface hfg
  have hzero : ∀ n : N, ∀ n' : N, n + n' = 0 → n = 0 := by
    rintro ⟨n, hn⟩ ⟨n', hn'⟩ e
    have e' : n + n' = 0 := congrArg Subtype.val e
    exact Subtype.ext (hsharp n hn (by rwa [neg_eq_of_add_eq_zero_right e']))
  let χ : Multiplicative N →* Γ(T.left, ⊤) :=
    { toFun := fun n => if Multiplicative.toAdd n = 0 then 1 else 0
      map_one' := if_pos rfl
      map_mul' := fun a b => by
        by_cases ha : Multiplicative.toAdd a = 0
        · by_cases hb : Multiplicative.toAdd b = 0
          · simp [ha, hb]
          · have : Multiplicative.toAdd (a * b) ≠ 0 := fun e => hb (by
              have := hzero (Multiplicative.toAdd b) (Multiplicative.toAdd a)
                (by rw [add_comm]; exact e)
              exact this)
            simp [ha, hb]
        · have : Multiplicative.toAdd (a * b) ≠ 0 := fun e =>
            ha (hzero (Multiplicative.toAdd a) (Multiplicative.toAdd b) e)
          simp [ha]
          intro e
          exact absurd (hzero _ _ e) ha }
  let π : AddMonoidAlgebra Γ(T.left, ⊤) N →ₐ[Γ(T.left, ⊤)] Γ(T.left, ⊤) :=
    AddMonoidAlgebra.lift Γ(T.left, ⊤) Γ(T.left, ⊤) N χ
  have hπ_s : ∀ (n : N) (c : Γ(T.left, ⊤)), π (AddMonoidAlgebra.single n c) =
      c * (if n = 0 then 1 else 0) := by
    intro n c
    simp [π, AddMonoidAlgebra.lift_single, χ]
  have hsm : Smooth (magnetπ N T.left) :=
    MorphismProperty.of_isPullback (P := @Smooth) (isPullback_magnet N T) inferInstance
  have hsm₂ : Smooth (Spec.map (magnetConst N T.left)) := by
    have e : Spec.map (magnetConst N T.left) = magnetπ N T.left ≫ T.left.isoSpec.hom := by
      simp [magnetπ]
    rw [e]
    infer_instance
  have hR : (magnetConst N T.left).hom.Smooth := (HasRingHomProperty.Spec_iff (P := @Smooth)).1 hsm₂
  have hS : Algebra.Smooth Γ(T.left, ⊤) (AddMonoidAlgebra Γ(T.left, ⊤) N) := by
    have : (magnetConst N T.left).hom = algebraMap Γ(T.left, ⊤) (AddMonoidAlgebra Γ(T.left, ⊤) N) := rfl
    rw [this] at hR
    exact (RingHom.smooth_algebraMap).1 hR
  have hA : IsAug (AddMonoidAlgebra.grade (R := Γ(T.left, ⊤)) (M := N)) π (fun n => w n) := by
    refine ⟨fun y b _ _ e => Subtype.ext ((hw y).1 e), fun u _ _ _ v _ _ _ => map_add _ _ _,
      fun y hy b hb => ?_, fun b hb => ?_⟩
    · obtain ⟨c, rfl⟩ := (AddMonoidAlgebra.mem_grade_iff' _ _ _).1 hb
      change π (AddMonoidAlgebra.single y c) = 0
      rw [hπ_s, if_neg hy, mul_zero]
    · obtain ⟨c, rfl⟩ := (AddMonoidAlgebra.mem_grade_iff' _ _ _).1 hb
      change algebraMap _ _ (π (AddMonoidAlgebra.single 0 c)) = AddMonoidAlgebra.single 0 c
      rw [hπ_s, if_pos rfl, mul_one]
      rfl
  exact ⟨π, printed_ring hA⟩

#print axioms AlgMag.Sec12Printed.cor125

end AlgMag.Sec12Printed
