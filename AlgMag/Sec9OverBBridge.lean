/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec9OverBFinal

/-!
# §9 of *Algebraic Magnetism* over an algebraic space `B`: the Zariski sheaf condition is automatic

`AlgMag.S9BF.isQCoh_of_local` assumed the Zariski sheaf condition besides the local datum
`LocalAssoc`. It follows from the local datum: over `T`, the module is the associated module of a
quasi-coherent module on `T`, and that is a sheaf. So (`isQCoh_of_localAssoc`) a module on the big
site of `B` which is, over each `T`, the associated module of a Stacks quasi-coherent module on `T`
is quasi-coherent in the sense of §9, with no other hypothesis.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits

noncomputable section

variable {Bs : BigFppfSite.{u}} {S : Scheme.{u}} {hS : Bs.Contains S}
  {Bsp : (BigFppfOver Bs S hS)ᵒᵖ ⥤ Type u}

namespace AlgMag.S9BF

open AlgMag.S9B AlgMag.Leftover
open AlgMag.S9 (PMod)

variable {F : PMod (OB Bsp)} {T : SB Bsp}

attribute [local instance] LocalAssoc.qc

/-- `f : W ⟶ T` as an object over the scheme of `T`. -/
abbrev overT {W : SB Bsp} (f : W ⟶ T) : Over T.left := Over.mk (SB.Hom.left f)

/-- A factorization `k = s ≫ u` as a morphism over the scheme of `T`. -/
def mpT {W A : SB Bsp} (s : W ⟶ A) (u : A ⟶ T) (k : W ⟶ T) (hk : s ≫ u = k) : overT k ⟶ overT u :=
  Over.homMk (SB.Hom.left s) (by subst hk; exact (SB.comp_left s u).symm)

lemma LocalAssoc.nat' (D : LocalAssoc F T) {W A : SB Bsp} (s : W ⟶ A) (u : A ⟶ T) (k : W ⟶ T)
    (hk : s ≫ u = k) (x : F.obj (op A)) :
    D.ι k (F.map s.op x) = (assocPMod D.G).map (mpT s u k hk).op (D.ι u x) := by
  subst hk
  exact D.nat s u x

/-- A module with the local datum over `T` is separated for open covers of objects over `T`. -/
lemma LocalAssoc.sep (D : LocalAssoc F T) {W : SB Bsp} (f : W ⟶ T)
    (𝒰 : Scheme.OpenCover.{u} W.left) {b b' : F.obj (op W)}
    (h : ∀ j, F.map (coverHom W 𝒰 j).op b = F.map (coverHom W 𝒰 j).op b') : b = b' := by
  haveI := D.qc
  apply (D.ι f).injective
  refine AlgMag.S9.sep_cover (isQCoh_assocPMod D.G) (overT f) 𝒰 fun j => ?_
  let v : AlgMag.S9.coverPiece (overT f) 𝒰 j ⟶ overT (coverHom W 𝒰 j ≫ f) :=
    Over.homMk (𝟙 _) (by
      change 𝟙 _ ≫ SB.Hom.left (coverHom W 𝒰 j ≫ f) = 𝒰.f j ≫ SB.Hom.left f
      rw [Category.id_comp, SB.comp_left]
      rfl)
  have e : AlgMag.S9.coverHom (overT f) 𝒰 j = v ≫ mpT (coverHom W 𝒰 j) f _ rfl :=
    Over.OverMorphism.ext (Category.id_comp _).symm
  rw [e, op_comp, (assocPMod D.G).map_comp, (assocPMod D.G).map_comp,
    ← D.nat' (coverHom W 𝒰 j) f _ rfl, ← D.nat' (coverHom W 𝒰 j) f _ rfl, h]

/-- Over a piece of `W ×_T 𝒰.X j`: the map to the piece `j` of `T`. -/
def pieceMap {T W : SB Bsp} (𝒰 : Scheme.OpenCover.{u} T.left) (f : W ⟶ T) (j : 𝒰.I₀) :
    coverPiece W (𝒰.pullback₁ (SB.Hom.left f)) j ⟶ coverPiece T 𝒰 j :=
  SB.ofMapLift (coverContains T 𝒰 j) (coverHom W (𝒰.pullback₁ (SB.Hom.left f)) j ≫ f)
    (pullback.snd (SB.Hom.left f) (𝒰.f j)) (by
      rw [SB.comp_left]
      exact (pullback.condition (f := SB.Hom.left f) (g := 𝒰.f j)).symm)

lemma pieceMap_ι {T W : SB Bsp} (𝒰 : Scheme.OpenCover.{u} T.left) (f : W ⟶ T) (j : 𝒰.I₀) :
    pieceMap 𝒰 f j ≫ coverHom T 𝒰 j = coverHom W (𝒰.pullback₁ (SB.Hom.left f)) j ≫ f :=
  SB.ofMapLift_ι _ _ _ _

/-- The Zariski sheaf condition of `AlgMag.S9B.IsQCoh`, from the local datum over `T` alone. -/
theorem LocalAssoc.isSheafFor (D : LocalAssoc F T) (𝒰 : Scheme.OpenCover.{u} T.left) (R : Sieve T)
    (hR : coverSieve T 𝒰 ≤ R) : Presieve.IsSheafFor F.toPresheaf R.arrows := by
  haveI := D.qc
  have hH := isQCoh_assocPMod D.G
  intro x hx
  have hsc := (Presieve.compatible_iff_sieveCompatible x).1 hx
  have mem : ∀ i, R (coverHom T 𝒰 i) := fun i => hR _ ⟨i, 𝟙 _, (Category.id_comp _).symm⟩
  let y : ∀ i, F.obj (op (coverPiece T 𝒰 i)) := fun i => x (coverHom T 𝒰 i) (mem i)
  have hpiece : ∀ {W : SB Bsp} (f : W ⟶ T) (hf : R f) (j : 𝒰.I₀),
      F.map (coverHom W (𝒰.pullback₁ (SB.Hom.left f)) j).op (x f hf) =
        F.map (pieceMap 𝒰 f j).op (y j) := by
    intro W f hf j
    have h1 := hsc f (coverHom W (𝒰.pullback₁ (SB.Hom.left f)) j) hf
    have h2 := hsc (coverHom T 𝒰 j) (pieceMap 𝒰 f j) (mem j)
    have e := pieceMap_ι 𝒰 f j
    refine h1.symm.trans (Eq.trans ?_ h2)
    congr 1
    exact e.symm
  let H := assocPMod D.G
  let c := fun i => coverHom T 𝒰 i
  have wd : ∀ {W : Over T.left} (i j : 𝒰.I₀) (u : W ⟶ overT (c i)) (v : W ⟶ overT (c j)),
      H.map u.op (D.ι (c i) (y i)) = H.map v.op (D.ι (c j) (y j)) := by
    intro W i j u v
    have huv : u.left ≫ 𝒰.f i = v.left ≫ 𝒰.f j := (Over.w u).trans (Over.w v).symm
    let 𝒰p := 𝒰.pullback₁ (SB.Hom.left (c i))
    let q := coverHom (coverPiece T 𝒰 i) 𝒰p j
    let k := q ≫ c i
    let l : W ⟶ overT k := Over.homMk (pullback.lift u.left v.left huv) (by
      change pullback.lift u.left v.left huv ≫ SB.Hom.left (q ≫ c i) = W.hom
      rw [SB.comp_left]
      change pullback.lift u.left v.left huv ≫ pullback.fst _ _ ≫ 𝒰.f i = W.hom
      exact (pullback.lift_fst_assoc u.left v.left huv (𝒰.f i)).trans (Over.w u))
    have hu : u = l ≫ mpT q (c i) k rfl :=
      Over.OverMorphism.ext (pullback.lift_fst _ _ huv).symm
    have hv : v = l ≫ mpT (pieceMap 𝒰 (c i) j) (c j) k (pieceMap_ι 𝒰 (c i) j) :=
      Over.OverMorphism.ext (pullback.lift_snd _ _ huv).symm
    have hp := hpiece (c i) (mem i) j
    rw [hu, hv, op_comp, op_comp, H.map_comp, H.map_comp, ← D.nat' q (c i) k rfl,
      ← D.nat' (pieceMap 𝒰 (c i) j) (c j) k (pieceMap_ι 𝒰 (c i) j)]
    exact congrArg (fun z => H.map l.op (D.ι k z)) hp
  let A : Over T.left := overT (𝟙 T)
  have lift : ∀ {W : Over T.left} (g : W ⟶ A), (AlgMag.S9.coverSieve A 𝒰).arrows g →
      ∃ (i : 𝒰.I₀), Nonempty (W ⟶ overT (c i)) := by
    rintro W g ⟨i, u, hu⟩
    refine ⟨i, ⟨Over.homMk u ?_⟩⟩
    have hA : A.hom = 𝟙 _ := SB.id_left T
    have hw := Over.w g
    rw [hA, Category.comp_id, hu] at hw
    exact hw
  choose ci cu using @lift
  let z : Presieve.FamilyOfElements H.toPresheaf (AlgMag.S9.coverSieve A 𝒰).arrows :=
    fun W g hg => H.map (cu g hg).some.op (D.ι (c (ci g hg)) (y (ci g hg)))
  have hz : z.Compatible := by
    refine (Presieve.compatible_iff_sieveCompatible z).2 ?_
    intro W W' g h hg
    refine Eq.trans ?_ (H.map_comp (cu g hg).some.op h.op (D.ι (c (ci g hg)) (y (ci g hg))))
    exact wd _ _ _ _
  obtain ⟨a, ham, -⟩ := hH.sheaf _ (AlgMag.S9.coverSieve_mem A 𝒰) z hz
  let a0 : F.obj (op T) := (D.ι (𝟙 T)).symm a
  have ha : ∀ i, F.map (c i).op a0 = y i := by
    intro i
    apply (D.ι (c i)).injective
    rw [D.nat' (c i) (𝟙 T) (c i) (Category.comp_id _),
      show D.ι (𝟙 T) a0 = a from (D.ι (𝟙 T)).apply_symm_apply a]
    let m := mpT (c i) (𝟙 T) (c i) (Category.comp_id _)
    have hg : (AlgMag.S9.coverSieve A 𝒰).arrows m := ⟨i, 𝟙 _, (Category.id_comp _).symm⟩
    refine (ham m hg).trans ((wd _ i _ (𝟙 _)).trans ?_)
    exact H.map_id _ _
  refine ⟨a0, ?_, ?_⟩
  · intro W f hf
    refine D.sep f (𝒰.pullback₁ (SB.Hom.left f)) fun j => ?_
    refine Eq.trans ?_ (hpiece f hf j).symm
    refine Eq.trans ?_ (congrArg (F.map (pieceMap 𝒰 f j).op) (ha j))
    refine (F.map_comp f.op (coverHom W (𝒰.pullback₁ (SB.Hom.left f)) j).op a0).symm.trans
      (Eq.trans (congrArg (fun k => F.map k a0) ?_) (F.map_comp (c j).op (pieceMap 𝒰 f j).op a0))
    rw [← op_comp, ← op_comp]
    exact congrArg Quiver.Hom.op (pieceMap_ι 𝒰 f j).symm
  · intro t ht
    refine D.sep (𝟙 T) 𝒰 fun i => ?_
    exact (ht _ (mem i)).trans (ha i).symm

/-- **Bridge to Stacks quasi-coherent modules.** A module on the big site of the algebraic space `B`
which is, over every `T`, the associated module of a Stacks quasi-coherent module on `T`
(`LocalAssoc`, compare `BigFppfOver.HasLocalAssociatedModule`, Tag 03DX (1)) is `IsQCoh`. -/
theorem isQCoh_of_localAssoc (F : PMod (OB Bsp)) (L : ∀ T : SB Bsp, LocalAssoc F T) : IsQCoh F :=
  isQCoh_of_local F (fun T 𝒰 R hR => (L T).isSheafFor 𝒰 R hR) L

end AlgMag.S9BF

#print axioms AlgMag.S9BF.LocalAssoc.isSheafFor
#print axioms AlgMag.S9BF.isQCoh_of_localAssoc
