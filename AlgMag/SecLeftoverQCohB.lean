/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec9OverB

/-!
# Quasi-coherent modules on a scheme `Y`, restricted to the site `SB Bsp`

Let every `T` of `SB Bsp` carry a morphism `π T : T → Y` to a scheme `Y`, natural in `T`. A module `F`
with `AlgMag.S9.IsQCoh` on `Over Y` restricts to a module with `AlgMag.S9B.IsQCoh` on `SB Bsp`
(`isQCoh_restr`). This covers `B` a scheme (`Y = B`, §9.3 of *Algebraic Magnetism*), and, for `Y = S`,
pullbacks to `B` of quasi-coherent modules on `S`.
-/

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits

universe u

noncomputable section

namespace AlgMag.Leftover

open AlgMag.S9B
open AlgMag.S9 (PMod IsBC)

variable {Bs : BigFppfSite.{u}} {S : Scheme.{u}} {hS : Bs.Contains S}
  {Bsp : (BigFppfOver Bs S hS)ᵒᵖ ⥤ Type u} {Y : Scheme.{u}}

/-- A natural morphism from the objects of `SB Bsp` to `Y`. -/
structure ToScheme (Bsp : (BigFppfOver Bs S hS)ᵒᵖ ⥤ Type u) (Y : Scheme.{u}) where
  /-- the morphism -/
  π : ∀ T : SB Bsp, T.left ⟶ Y
  w : ∀ {T T' : SB Bsp} (s : T' ⟶ T), SB.Hom.left s ≫ π T = π T'

variable (P : ToScheme Bsp Y)

/-- `T` as an object over `Y`. -/
abbrev ToScheme.ob (T : SB Bsp) : Over Y := Over.mk (P.π T)

/-- `s` as a morphism over `Y`. -/
abbrev ToScheme.mp {T T' : SB Bsp} (s : T' ⟶ T) : P.ob T' ⟶ P.ob T :=
  Over.homMk (SB.Hom.left s) (P.w s)

lemma ToScheme.mp_id (T : SB Bsp) : P.mp (𝟙 T) = 𝟙 _ :=
  Over.OverMorphism.ext (SB.id_left T)

lemma ToScheme.mp_comp {T T' T'' : SB Bsp} (s : T'' ⟶ T') (t : T' ⟶ T) :
    P.mp (s ≫ t) = P.mp s ≫ P.mp t :=
  Over.OverMorphism.ext (SB.comp_left s t)

/-- The restriction of a module on `Over Y` to `SB Bsp`. -/
def restr (F : PMod (GB.overO Y)) : PMod (OB Bsp) where
  obj T := F.obj (op (P.ob (unop T)))
  grp T := F.grp _
  mod T := F.mod (op (P.ob (unop T)))
  map f := F.map (P.mp f.unop).op
  map_smul f r x := F.map_smul (P.mp f.unop).op r x
  map_id T x := by
    change F.map (P.mp (𝟙 (unop T))).op x = x
    rw [P.mp_id]
    exact F.map_id _ x
  map_comp f g x := by
    change F.map (P.mp (g.unop ≫ f.unop)).op x = _
    rw [P.mp_comp, op_comp]
    exact F.map_comp _ _ x

variable {F : PMod (GB.overO Y)}

/-- Over a piece `P` of `W ×_T 𝒰.X j`: the map of `P` to the piece `j` of `T`. -/
private def pieceTo {T W : SB Bsp} (𝒰 : Scheme.OpenCover.{u} T.left) (f : W ⟶ T) (j : 𝒰.I₀) :
    coverPiece W (𝒰.pullback₁ (SB.Hom.left f)) j ⟶ coverPiece T 𝒰 j :=
  SB.ofMapLift (coverContains T 𝒰 j) (coverHom W (𝒰.pullback₁ (SB.Hom.left f)) j ≫ f)
    (pullback.snd (SB.Hom.left f) (𝒰.f j)) (by
      rw [SB.comp_left]
      exact (pullback.condition (f := SB.Hom.left f) (g := 𝒰.f j)).symm)

private lemma pieceTo_ι {T W : SB Bsp} (𝒰 : Scheme.OpenCover.{u} T.left) (f : W ⟶ T) (j : 𝒰.I₀) :
    pieceTo 𝒰 f j ≫ coverHom T 𝒰 j = coverHom W (𝒰.pullback₁ (SB.Hom.left f)) j ≫ f :=
  SB.ofMapLift_ι _ _ _ _

/-- **Bridge.** A quasi-coherent module on `Y` restricts to a quasi-coherent module on `SB Bsp`. -/
theorem isQCoh_restr (hF : AlgMag.S9.IsQCoh F) : IsQCoh (restr P F) where
  base_change {T T'} s _ _ := by
    haveI : IsAffine (P.ob T).left := ‹IsAffine T.left›
    haveI : IsAffine (P.ob T').left := ‹IsAffine T'.left›
    exact hF.base_change (P.mp s)
  sheaf T 𝒰 R hR := by
    intro x hx
    have hsc := (Presieve.compatible_iff_sieveCompatible x).1 hx
    let y : ∀ i, F.obj (op (P.ob (coverPiece T 𝒰 i))) := fun i =>
      x (coverHom T 𝒰 i) (hR _ ⟨i, 𝟙 _, (Category.id_comp _).symm⟩)
    -- the value of `x` on a piece of `W`
    have hpiece : ∀ {W : SB Bsp} (f : W ⟶ T) (hf : R f) (j : 𝒰.I₀),
        F.map (P.mp (coverHom W (𝒰.pullback₁ (SB.Hom.left f)) j)).op (x f hf) =
          F.map (P.mp (pieceTo 𝒰 f j)).op (y j) := by
      intro W f hf j
      have h1 := hsc f (coverHom W (𝒰.pullback₁ (SB.Hom.left f)) j) hf
      have h2 := hsc (coverHom T 𝒰 j) (pieceTo 𝒰 f j)
        (hR _ ⟨j, 𝟙 _, (Category.id_comp _).symm⟩)
      have e := pieceTo_ι 𝒰 f j
      refine h1.symm.trans (Eq.trans ?_ h2)
      congr 1
      exact e.symm
    -- two witnesses over `Over Y` give the same value
    have wd : ∀ {W : Over Y} (i j : 𝒰.I₀) (u : W ⟶ P.ob (coverPiece T 𝒰 i))
        (v : W ⟶ P.ob (coverPiece T 𝒰 j)), u.left ≫ 𝒰.f i = v.left ≫ 𝒰.f j →
        F.map u.op (y i) = F.map v.op (y j) := by
      intro W i j u v huv
      let c := coverHom T 𝒰 i
      let Q := coverPiece (coverPiece T 𝒰 i) (𝒰.pullback₁ (SB.Hom.left c)) j
      let l : W ⟶ P.ob Q := Over.homMk
        (pullback.lift u.left v.left huv) (by
          change pullback.lift u.left v.left huv ≫ P.π Q = W.hom
          have := P.w (coverHom (coverPiece T 𝒰 i) (𝒰.pullback₁ (SB.Hom.left c)) j)
          rw [← this]
          change pullback.lift u.left v.left huv ≫ pullback.fst _ _ ≫ _ = _
          rw [← Category.assoc]
          exact (congrArg (· ≫ P.π (coverPiece T 𝒰 i)) (pullback.lift_fst u.left v.left huv)).trans
            (Over.w u))
      have hu : u = l ≫ P.mp (coverHom (coverPiece T 𝒰 i) (𝒰.pullback₁ (SB.Hom.left c)) j) :=
        Over.OverMorphism.ext (pullback.lift_fst _ _ huv).symm
      have hv : v = l ≫ P.mp (pieceTo 𝒰 c j) :=
        Over.OverMorphism.ext (pullback.lift_snd _ _ huv).symm
      have hp := hpiece c (hR _ ⟨i, 𝟙 _, (Category.id_comp _).symm⟩) j
      rw [hu, hv, op_comp, op_comp, F.map_comp, F.map_comp]
      exact congrArg (F.map l.op) hp
    -- the family on the sieve of `𝒰` over `Y`
    have hmem := AlgMag.S9.coverSieve_mem (S := Y) (P.ob T) 𝒰
    have lift : ∀ {W : Over Y} (g : W ⟶ P.ob T),
        (AlgMag.S9.coverSieve (P.ob T) 𝒰).arrows g →
        ∃ (i : 𝒰.I₀) (u' : W ⟶ P.ob (coverPiece T 𝒰 i)), g.left = u'.left ≫ 𝒰.f i := by
      rintro W g ⟨i, u, hu⟩
      refine ⟨i, Over.homMk u ?_, hu⟩
      have := P.w (coverHom T 𝒰 i)
      change u ≫ P.π (coverPiece T 𝒰 i) = W.hom
      rw [← this]
      change u ≫ 𝒰.f i ≫ P.π T = W.hom
      rw [← Category.assoc, ← hu]
      exact Over.w g
    choose ci cu chu using @lift
    let z : Presieve.FamilyOfElements F.toPresheaf (AlgMag.S9.coverSieve (P.ob T) 𝒰).arrows :=
      fun W g hg => F.map (cu g hg).op (y (ci g hg))
    have hz : z.Compatible := by
      refine (Presieve.compatible_iff_sieveCompatible z).2 ?_
      intro W W' g h hg
      refine Eq.trans ?_ (F.map_comp (cu g hg).op h.op (y (ci g hg)))
      refine wd _ _ _ _ ?_
      rw [← chu, Over.comp_left, chu g hg]
      exact (Category.assoc _ _ _).symm
    obtain ⟨a, ham, -⟩ := hF.sheaf _ hmem z hz
    have ha : ∀ i, F.map (P.mp (coverHom T 𝒰 i)).op a = y i := by
      intro i
      have hg : (AlgMag.S9.coverSieve (P.ob T) 𝒰).arrows (P.mp (coverHom T 𝒰 i)) :=
        ⟨i, 𝟙 _, (Category.id_comp _).symm⟩
      refine (ham _ hg).trans ((wd _ i _ (𝟙 _) ?_).trans (F.map_id _ _))
      rw [← chu]
      exact (Category.id_comp _).symm
    have sepP : ∀ {W : SB Bsp} (𝒰' : Scheme.OpenCover.{u} W.left) (b b' : F.obj (op (P.ob W))),
        (∀ j, F.map (P.mp (coverHom W 𝒰' j)).op b = F.map (P.mp (coverHom W 𝒰' j)).op b') →
        b = b' := by
      intro W 𝒰' b b' h
      refine AlgMag.S9.sep_cover hF (P.ob W) 𝒰' fun j => ?_
      let v : AlgMag.S9.coverPiece (P.ob W) 𝒰' j ⟶ P.ob (coverPiece W 𝒰' j) :=
        Over.homMk (𝟙 _) (by
          have := P.w (coverHom W 𝒰' j)
          change 𝟙 _ ≫ P.π (coverPiece W 𝒰' j) = 𝒰'.f j ≫ P.π W
          rw [Category.id_comp, ← this]
          rfl)
      have e : AlgMag.S9.coverHom (P.ob W) 𝒰' j = v ≫ P.mp (coverHom W 𝒰' j) :=
        Over.OverMorphism.ext (Category.id_comp _).symm
      rw [e, op_comp, F.map_comp, F.map_comp, h]
    refine ⟨a, ?_, ?_⟩
    · intro W f hf
      refine sepP (𝒰.pullback₁ (SB.Hom.left f)) _ _ fun j => ?_
      refine Eq.trans ?_ (hpiece f hf j).symm
      refine Eq.trans ?_ (congrArg (F.map (P.mp (pieceTo 𝒰 f j)).op) (ha j))
      refine (F.map_comp (P.mp f).op (P.mp (coverHom W (𝒰.pullback₁ (SB.Hom.left f)) j)).op a).symm.trans
        (Eq.trans (congrArg (fun k => F.map k a) ?_)
          (F.map_comp (P.mp (coverHom T 𝒰 j)).op (P.mp (pieceTo 𝒰 f j)).op a))
      rw [← op_comp, ← op_comp, ← P.mp_comp, ← P.mp_comp]
      exact congrArg (fun k => (P.mp k).op) (pieceTo_ι 𝒰 f j).symm
    · intro t ht
      refine sepP 𝒰 _ _ fun i => ?_
      exact (ht _ (hR _ ⟨i, 𝟙 _, (Category.id_comp _).symm⟩)).trans (ha i).symm

end AlgMag.Leftover

#print axioms AlgMag.Leftover.isQCoh_restr
