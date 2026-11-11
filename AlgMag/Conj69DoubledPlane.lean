/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Conj69DoubledCore

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

/-!
# The plane with doubled origin

Two copies of the plane glued along the complement of `x = y = 0`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TopologicalSpace

universe u

namespace AlgMag.Conj69

variable (k : Type u) [Field k]

/-- The punctured plane, the complement of `x = y = 0`. -/
noncomputable def punctured : (Pl k).Opens :=
  ⟨{z | ¬ VanishesXY z}, by
    have : {z : Pl k | ¬ VanishesXY z} =
        (PrimeSpectrum.zeroLocus ({X 0, X 1} : Set (A2 k)))ᶜ := by
      ext z
      change ¬ VanishesXY z ↔ ¬ (({X 0, X 1} : Set (A2 k)) ⊆ (z.asIdeal : Set (A2 k)))
      rw [Set.insert_subset_iff, Set.singleton_subset_iff]
      rfl
    rw [this]
    exact (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩

/-- The span of two copies of the plane under the punctured plane. -/
noncomputable def glueF : WalkingSpan ⥤ Scheme.{u} := span (punctured k).ι (punctured k).ι

instance glueF_open {i j : WalkingSpan} (f : i ⟶ j) : IsOpenImmersion ((glueF k).map f) := by
  rcases f with _ | (_ | _)
  · simp only [WidePushoutShape.hom_id, Functor.map_id]; infer_instance
  · exact inferInstanceAs (IsOpenImmersion (punctured k).ι)
  · exact inferInstanceAs (IsOpenImmersion (punctured k).ι)

instance glueF_dir : ((glueF k) ⋙ Scheme.forget).IsLocallyDirected := by
  haveI : ∀ i : WalkingPair, Mono (((glueF k) ⋙ Scheme.forget).map (WidePushoutShape.Hom.init i)) := fun i => by
    rw [CategoryTheory.mono_iff_injective]
    cases i
    · exact (punctured k).ι.isOpenEmbedding.injective
    · exact (punctured k).ι.isOpenEmbedding.injective
  infer_instance

/-- The plane with doubled origin. -/
noncomputable def doubledPlane : Scheme.{u} := colimit (glueF k)

/-- The first chart. -/
noncomputable def chart₁ : Pl k ⟶ doubledPlane k := colimit.ι (glueF k) WalkingSpan.left
/-- The second chart. -/
noncomputable def chart₂ : Pl k ⟶ doubledPlane k := colimit.ι (glueF k) WalkingSpan.right

instance : IsOpenImmersion (chart₁ k) := inferInstanceAs (IsOpenImmersion (colimit.ι (glueF k) _))
instance : IsOpenImmersion (chart₂ k) := inferInstanceAs (IsOpenImmersion (colimit.ι (glueF k) _))

/-- The first chart meets the second exactly in the punctured plane. -/
theorem chart₁_mem_iff (z : Pl k) : chart₁ k z ∈ (chart₂ k).opensRange ↔ ¬ VanishesXY z := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨c, fi, fj, w, h1, h2⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff (F := glueF k) (i := WalkingSpan.right)
        (j := WalkingSpan.left) (xi := y) (xj := z)).1 hy
    rcases c with _ | (_ | _)
    · have ef : fj = WalkingSpan.Hom.fst := Subsingleton.elim _ _
      subst ef
      have : z = ((punctured k).ι w : Pl k) := h2.symm
      rw [this]
      exact w.2
    · have f' : WidePushoutShape.Hom (some WalkingPair.left) (some WalkingPair.right) := fi
      cases f'
    · have f' : WidePushoutShape.Hom (some WalkingPair.right) (some WalkingPair.left) := fj
      cases f'
  · intro hz
    let p : (punctured k).toScheme := ⟨z, hz⟩
    have e1 : (punctured k).ι ≫ chart₁ k = (punctured k).ι ≫ chart₂ k :=
      (colimit.w (glueF k) (WidePushoutShape.Hom.init WalkingPair.left)).trans
        (colimit.w (glueF k) (WidePushoutShape.Hom.init WalkingPair.right)).symm
    have e2 := congrArg (fun m => m p) e1
    have e3 : chart₁ k ((punctured k).ι p) = chart₂ k ((punctured k).ι p) := by simpa using e2
    exact ⟨(punctured k).ι p, e3.symm⟩

/-- A point of the plane where `x, y` vanish. -/
theorem exists_origin : ∃ z : Pl k, VanishesXY z := by
  let I : Ideal (A2 k) := RingHom.ker (constantCoeff : A2 k →+* k)
  haveI : I.IsPrime := RingHom.ker_isPrime _
  exact ⟨⟨I, inferInstance⟩, by simp [I, RingHom.mem_ker], by simp [I, RingHom.mem_ker]⟩

end AlgMag.Conj69
