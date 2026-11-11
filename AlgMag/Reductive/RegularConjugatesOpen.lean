/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.IdentityComponentRoots
import AlgMag.Reductive.OpenCell.IrreducibleOfConnected
import AlgMag.Reductive.OpenCell.TensorDomain
import TauCeti.Algebra.AlgebraicGroup.Hopf.PointConjugation

/-!
# Step C2: the Zariski topology on `K(k)`, irreducibility, continuity of conjugation

Notes: `algmag-notes/reductive/components-NGT-B.md`, step C2 (topological inputs of C3).

Over an algebraically closed field `k`, `k`-points `x : H →ₐ[k] k` are identified with the
closed points `ker x` of `Spec H`; we give them the induced (Zariski) topology.

* `kerPt`: the point `ker x ∈ Spec H`;
* `zariski`: the induced topology on `WithConv (H →ₐ[k] k)` (scoped instance);
* `continuous_conj`: conjugation by any `k`-point is continuous;
* `irreducibleSpace_points`: if `K` is a set of `k`-points equal to `{x | compIdeal π N ≤ ker x}`,
  then `K` is irreducible (identity component connected ⇒ irreducible, density of `k`-points).
-/

suppress_compilation

open Magnetism TauCeti WithConv

namespace AlgMag.Reductive

universe u

section Points

variable {k : Type u} {H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]

/-- The closed point `ker x` of `Spec H` attached to a `k`-point. -/
def kerPt (x : WithConv (H →ₐ[k] k)) : PrimeSpectrum H :=
  ⟨RingHom.ker x.ofConv, RingHom.ker_isPrime _⟩

/-- The Zariski topology on `k`-points, induced from `Spec H`. -/
@[instance_reducible] def zariski : TopologicalSpace (WithConv (H →ₐ[k] k)) :=
  TopologicalSpace.induced kerPt inferInstance

namespace Zariski
scoped[AlgMag.Reductive.Zariski] attribute [instance] AlgMag.Reductive.zariski
end Zariski

open scoped Zariski

lemma isInducing_kerPt : Topology.IsInducing (kerPt : WithConv (H →ₐ[k] k) → PrimeSpectrum H) :=
  ⟨rfl⟩

/-- `ker (a x a⁻¹) = φ_a⁻¹ (ker x)` for the point-conjugation coordinate map `φ_a`. -/
lemma kerPt_conj (a x : WithConv (H →ₐ[k] k)) :
    kerPt (a * x * a⁻¹) =
      PrimeSpectrum.comap (HopfAlgebra.pointConjugationAlgHom a).toRingHom (kerPt x) := by
  have h := HopfAlgebra.comp_pointConjugationAlgHom (A := k) a x
  have hid : AlgHom.mapValue (H := H) (Algebra.ofId k k) = MonoidHom.id _ := by
    rw [show Algebra.ofId k k = AlgHom.id k k from Subsingleton.elim _ _]
    exact AlgHom.mapValue_id
  rw [hid, MonoidHom.id_apply] at h
  rw [← h]
  ext y
  simp [kerPt, PrimeSpectrum.comap_asIdeal]

/-- **(c)** Conjugation by a `k`-point is continuous for the Zariski topology. -/
theorem continuous_conj (a : WithConv (H →ₐ[k] k)) :
    Continuous fun x : WithConv (H →ₐ[k] k) => a * x * a⁻¹ := by
  rw [isInducing_kerPt.continuous_iff]
  have : (kerPt ∘ fun x : WithConv (H →ₐ[k] k) => a * x * a⁻¹) =
      PrimeSpectrum.comap (HopfAlgebra.pointConjugationAlgHom a).toRingHom ∘ kerPt := by
    funext x; exact kerPt_conj a x
  rw [this]
  exact (PrimeSpectrum.continuous_comap _).comp isInducing_kerPt.continuous

/-- **(c), subgroup form** (the `hcont` of `exists_mul_normalizer_of_irreducible`). -/
theorem continuous_conj_subtype (K : Set (WithConv (H →ₐ[k] k))) (a : WithConv (H →ₐ[k] k))
    (hK : ∀ x ∈ K, a * x * a⁻¹ ∈ K) :
    Continuous fun x : K => (⟨a * x * a⁻¹, hK x x.2⟩ : K) :=
  ((continuous_conj a).comp continuous_subtype_val).subtype_mk _

end Points

/-- An inducing map with preirreducible range from a nonempty space: irreducible source. -/
theorem irreducibleSpace_of_isInducing {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Topology.IsInducing f) [Nonempty X] (h : IsPreirreducible (Set.range f)) :
    IrreducibleSpace X where
  isPreirreducible_univ := by
    rintro u v hu hv ⟨x, -, hx⟩ ⟨y, -, hy⟩
    obtain ⟨u', hu', rfl⟩ := hf.isOpen_iff.1 hu
    obtain ⟨v', hv', rfl⟩ := hf.isOpen_iff.1 hv
    obtain ⟨_, ⟨z, rfl⟩, hz⟩ := h u' v' hu' hv' ⟨f x, ⟨x, rfl⟩, hx⟩ ⟨f y, ⟨y, rfl⟩, hy⟩
    exact ⟨z, trivial, hz⟩
  toNonempty := inferInstance

section Irreducible

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X)
variable [IsAlgClosed k] [Algebra.FiniteType k H]

open scoped Zariski

/-- `Spec O((G^N)°)` is irreducible. -/
lemma irreducibleSpace_comp (N : Magnet (Additive X)) :
    IrreducibleSpace (PrimeSpectrum
      ((H ⧸ (magnetHopfIdeal π N).toIdeal) ⧸ (attrComp π N).toIdeal)) := by
  set B := H ⧸ (magnetHopfIdeal π N).toIdeal
  have : Algebra.FiniteType k B :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k _) (Ideal.Quotient.mkₐ_surjective k _)
  have : Algebra.FiniteType k (B ⧸ (attrComp π N).toIdeal) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k _) (Ideal.Quotient.mkₐ_surjective k _)
  have : ConnectedSpace (PrimeSpectrum (B ⧸ (attrComp π N).toIdeal)) := by
    let _ : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
    let _ : LocallyConnectedSpace (PrimeSpectrum B) := inferInstance
    show ConnectedSpace (PrimeSpectrum
      (B ⧸ (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := B)).toIdeal))
    rw [HopfAlgebra.identityComponentHopfIdeal_toIdeal]
    exact PrimeSpectrum.connectedSpace_quotient_connectedComponentIdeal _
  exact OpenCellNotes.irreducibleSpace_of_connectedSpace k

/-- **(b)** `K(k)`, with the Zariski topology, is irreducible. -/
theorem irreducibleSpace_points (N : Magnet (Additive X)) (K : Set (WithConv (H →ₐ[k] k)))
    (hK : ∀ x, x ∈ K ↔ compIdeal π N ≤ RingHom.ker x.ofConv) : IrreducibleSpace K := by
  set c := compIdeal π N
  set q : H →+* _ := (compMk π N).toAlgHom.toRingHom
  have hq : Function.Surjective q := compMk_surjective π N
  -- `V(c)` is irreducible.
  have hZ : IsIrreducible (PrimeSpectrum.zeroLocus (c : Set H)) := by
    have := irreducibleSpace_comp π N
    have h := (IrreducibleSpace.isIrreducible_univ _).image (PrimeSpectrum.comap q)
      (PrimeSpectrum.continuous_comap q).continuousOn
    rwa [Set.image_univ, range_comap_of_surjective _ q hq] at h
  set S : Set (PrimeSpectrum H) := Set.range fun x : K => kerPt (x : WithConv (H →ₐ[k] k))
  -- `k`-points of `V(c)` are dense in `V(c)`.
  have hcl : closure S = PrimeSpectrum.zeroLocus (c : Set H) := by
    apply le_antisymm
    · rw [(PrimeSpectrum.isClosed_zeroLocus _).closure_subset_iff]
      rintro _ ⟨x, rfl⟩
      exact ((hK x).1 x.2 : _)
    · rw [← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
      intro p hp f hf
      rw [PrimeSpectrum.mem_zeroLocus] at hp
      have hJR : IsJacobsonRing H := isJacobsonRing_of_finiteType (A := k)
      have hrad : c.radical.jacobson = c.radical :=
        IsJacobsonRing.out hJR (Ideal.radical_isRadical c)
      have hfj : f ∈ c.radical.jacobson := by
        rw [Ideal.jacobson, Ideal.mem_sInf]
        rintro m ⟨hcm, hm⟩
        obtain ⟨φ, hφ⟩ := OpenCellNotes.exists_algHom_ker_eq (K := k) m
        have hφK : toConv φ ∈ K := (hK _).2 (by
          rw [ofConv_toConv, hφ]; exact Ideal.le_radical.trans hcm)
        have := (PrimeSpectrum.mem_vanishingIdeal _ _).1 hf _ ⟨⟨_, hφK⟩, rfl⟩
        rw [← hφ]; exact this
      rw [hrad] at hfj
      exact (Ideal.IsPrime.radical_le_iff p.isPrime).2 hp hfj
  have hSirr : IsIrreducible S := isIrreducible_iff_closure.1 (hcl ▸ hZ)
  have : Nonempty K := by
    obtain ⟨_, ⟨x, rfl⟩⟩ := hSirr.nonempty
    exact ⟨x⟩
  exact irreducibleSpace_of_isInducing (f := fun x : K => kerPt (x : WithConv (H →ₐ[k] k)))
    (isInducing_kerPt.comp Topology.IsInducing.subtypeVal) hSirr.isPreirreducible

end Irreducible

end AlgMag.Reductive
