/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartQSLocalCmp
import StacksFrontier.AlgebraicGeometry.Smooth.SmoothFormallySmooth

/-!
# A point of `X` on a complete affine, from a lift to a chart modulo `J`

For `LocalModelStep`: for `Y` affine and `J`-adically complete, `V → X`
étale from an affine, a compatible system `t l` on `V(J^(l+1))` and a lift of `t 0` to `V`: then the system is
the restriction of a map `Y → V`. The lifts along the first order thickenings are the infinitesimal lifting
property of étale morphisms (`Stacks.Smooth.formallySmoothScheme_of_etale`), the limit is a limit of rings.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Space

universe u

namespace AlgMag.ChartMain.DeligneQS.ChartQSLocal

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

set_option maxHeartbeats 2000000 in
/-- Infinitesimal lifting along an étale chart. -/
lemma exists_lift_thick {V : BigFppfOver B S hS} {φ : yoneda.obj V ⟶ X}
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
    {Z₀ Z : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj Z₀)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Z)] (k : Z₀ ⟶ Z)
    (hk : Stacks.Thickenings.IsFirstOrderThickening ((SCH).map k)) (t : X.obj (op Z)) (c₀ : Z₀ ⟶ V)
    (h : φ.app (op Z₀) c₀ = X.map k.op t) :
    ∃ c : Z ⟶ V, φ.app (op Z) c = t ∧ k ≫ c = c₀ := by
  let t' : yoneda.obj Z ⟶ X := yonedaEquiv.symm t
  have hc : yoneda.map c₀ ≫ φ = yoneda.map k ≫ t' := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_yoneda_map, h]
    simp [t']
  let F := he.rep.pullback t'
  let sn : F ⟶ Z := he.rep.snd t'
  let l : Z₀ ⟶ F := he.rep.lift (yoneda.map c₀) k hc
  haveI hsnE : Etale ((SCH).map sn) := he.property_snd t'
  have hls : l ≫ sn = k := he.rep.lift_snd _ _ _
  obtain ⟨g', hg₁, hg₂⟩ := Stacks.Smooth.formallySmoothScheme_of_etale ((SCH).map sn) inferInstance
    inferInstance ((SCH).map k) hk ((SCH).map l) (𝟙 _) (by
      rw [← Functor.map_comp, hls, Category.comp_id])
  have hw : g' ≫ F.hom.hom = Z.hom.hom := by
    rw [← site_w sn, ← Category.assoc, hg₁, Category.id_comp]
  let b : Z ⟶ F := siteHom g' hw
  have hb : b ≫ sn = 𝟙 Z := (SCH).map_injective (by
    rw [Functor.map_comp, CategoryTheory.Functor.map_id]
    exact hg₁)
  have hkb : k ≫ b = l := (SCH).map_injective (by
    rw [Functor.map_comp]
    exact hg₂)
  let fs : F ⟶ V := yoneda.preimage (he.rep.fst t')
  have hfsy : yoneda.map fs = he.rep.fst t' := Functor.map_preimage _ _
  have hfs : l ≫ fs = c₀ := yoneda.map_injective (by
    rw [Functor.map_comp, hfsy]
    exact he.rep.lift_fst _ _ _)
  have hwf : yoneda.map fs ≫ φ = yoneda.map sn ≫ t' := by
    rw [hfsy]
    exact he.rep.w t'
  refine ⟨b ≫ fs, ?_, ?_⟩
  · have e := congrArg (fun z => yonedaEquiv (yoneda.map b ≫ z)) hwf
    simp only [← Category.assoc, ← Functor.map_comp] at e
    rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_yoneda_map, hb] at e
    refine e.trans ?_
    simp [t']
  · rw [← Category.assoc, hkb, hfs]

/-- The ring limit. -/
lemma exists_ringHom_limit {A D : Type*} [CommRing A] [CommRing D] (J : Ideal D) [IsAdicComplete J D]
    {E : ℕ → Type*} [∀ l, CommRing (E l)] (π : ∀ l, D →+* E l) (hs : ∀ l, Function.Surjective (π l))
    (hk : ∀ l c, π l c = 0 ↔ c ∈ J ^ (l + 1)) (f : ∀ l, A →+* E l)
    (τ : ∀ l, E (l + 1) →+* E l) (hτπ : ∀ l c, τ l (π (l + 1) c) = π l c)
    (hτf : ∀ l a, τ l (f (l + 1) a) = f l a) :
    ∃ Λ : A →+* D, ∀ l a, π l (Λ a) = f l a := by
  have hex : ∀ a, ∃ z : D, ∀ l, π l z = f l a := by
    intro a
    choose y hy using fun l => hs l (f l a)
    have hstep : ∀ l, y (l + 1) - y l ∈ J ^ (l + 1) := fun l => by
      refine (hk l _).1 ?_
      rw [map_sub, hy, ← hτπ, hy, hτf, sub_self]
    have hle : ∀ m n, m ≤ n → y n - y m ∈ J ^ (m + 1) := by
      intro m n hmn
      induction n, hmn using Nat.le_induction with
      | base => simp
      | succ n hmn ih =>
        have := Ideal.add_mem _ ih (Ideal.pow_le_pow_right (Nat.succ_le_succ hmn) (hstep n))
        convert this using 1
        ring
    let w : ℕ → D := fun n => if n = 0 then 0 else y (n - 1)
    obtain ⟨z, hz⟩ := (inferInstance : IsAdicComplete J D).toIsPrecomplete.prec (f := w) (by
      intro m n hmn
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp
      · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        simp only [w, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
        have := Ideal.neg_mem_iff _ |>.2 (hle m' n' (by omega))
        simpa using this)
    refine ⟨z, fun l => ?_⟩
    have := hz (l + 1)
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
    simp only [w, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel] at this
    have e := (hk l _).2 this
    rw [map_sub, sub_eq_zero] at e
    rw [← e, hy]
  choose Z hZ using hex
  have huniq : ∀ u v : D, (∀ l, π l u = π l v) → u = v := by
    intro u v h
    have : u - v = 0 := by
      refine (inferInstance : IsAdicComplete J D).toIsHausdorff.haus _ fun n => ?_
      rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
      refine Ideal.pow_le_pow_right (Nat.le_succ n) ((hk n _).1 ?_)
      rw [map_sub, h, sub_self]
    exact sub_eq_zero.1 this
  refine ⟨{ toFun := Z
            map_one' := huniq _ _ fun l => by rw [hZ, map_one, map_one]
            map_mul' := fun a b => huniq _ _ fun l => by rw [map_mul, hZ, hZ, hZ, map_mul]
            map_zero' := huniq _ _ fun l => by rw [hZ, map_zero, map_zero]
            map_add' := fun a b => huniq _ _ fun l => by rw [map_add, hZ, hZ, hZ, map_add] }, fun l a => hZ a l⟩

lemma closed_of_comp {A A' C : Scheme.{u}} (f : A ⟶ A') (g : A' ⟶ C) (h : A ⟶ C) (he : f ≫ g = h)
    [IsClosedImmersion h] [IsClosedImmersion g] : IsClosedImmersion f := by
  subst he
  exact IsClosedImmersion.of_comp f g

lemma ker_sq_aux {D E E' : Type*} [CommRing D] [CommRing E] [CommRing E'] (A A' : Ideal D)
    (π : D →+* E') (hs : Function.Surjective π) (κ : E' →+* E) (π' : D →+* E)
    (hc : ∀ c, κ (π c) = π' c) (hk : ∀ c, π c = 0 ↔ c ∈ A) (hk' : ∀ c, π' c = 0 ↔ c ∈ A')
    (hle : A' * A' ≤ A) : RingHom.ker κ ^ 2 = ⊥ := by
  have hmem : ∀ z ∈ RingHom.ker κ, ∃ y ∈ A', π y = z := by
    intro z hz
    obtain ⟨y, hy⟩ := hs z
    refine ⟨y, (hk' y).1 ?_, hy⟩
    rw [← hc, hy]
    exact hz
  rw [eq_bot_iff, sq, Ideal.mul_le]
  intro r hr s hs
  obtain ⟨y, hy, rfl⟩ := hmem r hr
  obtain ⟨y', hy', rfl⟩ := hmem s hs
  rw [Ideal.mem_bot, ← map_mul]
  exact (hk _).2 (hle (Ideal.mul_mem_mul hy hy'))

variable {Y : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj Y)]

/-- The transition `V(J^l) → V(J^(l+1))`. -/
lemma exists_trans (J : Ideal Γ((SCH).obj Y, ⊤)) (l : ℕ) :
    ∃ k : Vc Y (J ^ (l + 1)) ⟶ Vc Y (J ^ (l + 1 + 1)),
      k ≫ ιc Y (J ^ (l + 1 + 1)) = ιc Y (J ^ (l + 1)) :=
  exists_factor_closed _ _ fun z hz =>
    closedι_appTop_of_mem _ (Ideal.pow_le_pow_right (Nat.le_succ _) hz)

set_option maxHeartbeats 1000000 in
/-- `V(J^(l+1)) ⊂ V(J^(l+2))` is a first order thickening. -/
lemma isFirstOrder_trans (J : Ideal Γ((SCH).obj Y, ⊤)) (l : ℕ)
    (k : Vc Y (J ^ (l + 1)) ⟶ Vc Y (J ^ (l + 1 + 1)))
    (hk : k ≫ ιc Y (J ^ (l + 1 + 1)) = ιc Y (J ^ (l + 1))) :
    Stacks.Thickenings.IsFirstOrderThickening ((SCH).map k) := by
  have h1 : IsClosedImmersion ((SCH).map (ιc Y (J ^ (l + 1)))) :=
    inferInstanceAs (IsClosedImmersion (Chart.closedι ((SCH).obj Y) (J ^ (l + 1))))
  have h2 : IsClosedImmersion ((SCH).map (ιc Y (J ^ (l + 1 + 1)))) :=
    inferInstanceAs (IsClosedImmersion (Chart.closedι ((SCH).obj Y) (J ^ (l + 1 + 1))))
  refine ⟨closed_of_comp _ _ _ ((Functor.map_comp (SCH) k _).symm.trans (congrArg (SCH).map hk)),
    (Stacks.Smooth.ker_pow_eq_bot_iff_of_isAffine _ 2).2 ?_⟩
  exact ker_sq_aux (J ^ (l + 1 + 1)) (J ^ (l + 1)) _ (ιc_surj _) _ _
    (fun c => (sec_comp k (ιc Y (J ^ (l + 1 + 1))) c).symm.trans (congrArg (fun z => (sec z) c) hk))
    (fun c => ιc_ker _ c) (fun c => ιc_ker _ c)
    (by rw [← pow_add]; exact Ideal.pow_le_pow_right (by omega))

set_option maxHeartbeats 4000000 in
/-- **The map to the chart.** -/
theorem exists_map_chart [IsAffine S] {V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    {φ : yoneda.obj V ⟶ X}
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
    (J : Ideal Γ((SCH).obj Y, ⊤)) [IsAdicComplete J Γ((SCH).obj Y, ⊤)]
    (t : ∀ l : ℕ, X.obj (op (Vc Y (J ^ (l + 1)))))
    (ht : ∀ l (k : Vc Y (J ^ (l + 1)) ⟶ Vc Y (J ^ (l + 1 + 1))),
      k ≫ ιc Y (J ^ (l + 1 + 1)) = ιc Y (J ^ (l + 1)) → X.map k.op (t (l + 1)) = t l)
    (c₀ : Vc Y (J ^ (0 + 1)) ⟶ V) (hc₀ : φ.app (op _) c₀ = t 0) :
    ∃ c : Y ⟶ V, ∀ l, X.map (ιc Y (J ^ (l + 1))).op (φ.app (op Y) c) = t l := by
  choose kk hkk using fun l => exists_trans J l
  have hstep : ∀ l (c : Vc Y (J ^ (l + 1)) ⟶ V), φ.app (op _) c = t l →
      ∃ c' : Vc Y (J ^ (l + 1 + 1)) ⟶ V, φ.app (op _) c' = t (l + 1) ∧ kk l ≫ c' = c := by
    intro l c hc
    exact exists_lift_thick he (kk l) (isFirstOrder_trans J l _ (hkk l)) (t (l + 1)) c
      (hc.trans (ht l _ (hkk l)).symm)
  let seq : ∀ l, { c : Vc Y (J ^ (l + 1)) ⟶ V // φ.app (op _) c = t l } := fun l =>
    Nat.rec ⟨c₀, hc₀⟩ (fun l c => ⟨(hstep l c.1 c.2).choose, (hstep l c.1 c.2).choose_spec.1⟩) l
  have hseq : ∀ l, kk l ≫ (seq (l + 1)).1 = (seq l).1 := fun l =>
    (hstep l (seq l).1 (seq l).2).choose_spec.2
  obtain ⟨Λ, hΛ⟩ := exists_ringHom_limit J (fun l => sec (ιc Y (J ^ (l + 1))))
    (fun l => ιc_surj _) (fun l c => ιc_ker _ c) (fun l => sec (seq l).1)
    (fun l => sec (kk l))
    (fun l c => ((sec_comp (kk l) _ c).symm).trans (congrArg (fun z => (sec z) c) (hkk l)))
    (fun l a => ((sec_comp (kk l) _ a).symm).trans (congrArg (fun z => (sec z) a) (hseq l)))
  haveI : IsAffine (B.obj hS).obj := ‹IsAffine S›
  have hw : toAffine Λ ≫ V.hom.hom = Y.hom.hom := by
    refine toAffine_ext (RingHom.ext fun b => ?_)
    rw [Scheme.Hom.comp_appTop]
    change (toAffine Λ).appTop.hom (V.hom.hom.appTop.hom b) = _
    rw [toAffine_appTop]
    have hsep : ∀ u v : Γ((SCH).obj Y, ⊤), (∀ l, (sec (ιc Y (J ^ (l + 1)))) u =
        (sec (ιc Y (J ^ (l + 1)))) v) → u = v := by
      intro u v h
      have : u - v = 0 := by
        refine (inferInstance : IsAdicComplete J Γ((SCH).obj Y, ⊤)).toIsHausdorff.haus _ fun n => ?_
        rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
        refine Ideal.pow_le_pow_right (Nat.le_succ n) ((ιc_ker _ _).1 ?_)
        rw [map_sub, h, sub_self]
      exact sub_eq_zero.1 this
    refine hsep _ _ fun l => ?_
    rw [hΛ]
    exact (sec_str (seq l).1 b).trans (sec_str (ιc Y (J ^ (l + 1))) b).symm
  let c : Y ⟶ V := siteHom (toAffine Λ) hw
  have he' : ∀ f, (sec c) f = Λ f := fun f => by
    change (toAffine Λ).appTop.hom f = _
    rw [toAffine_appTop]
  refine ⟨c, fun l => ?_⟩
  have e : ιc Y (J ^ (l + 1)) ≫ c = (seq l).1 :=
    siteExt (toAffine_ext (RingHom.ext fun f => by
      refine ((sec_comp _ c f).trans ?_)
      rw [he', hΛ]))
  exact (map_yoneda_app (φ := φ) (ιc Y (J ^ (l + 1))) c).symm.trans
    ((congrArg (fun z => φ.app (op _) z) e).trans (seq l).2)

end AlgMag.ChartMain.DeligneQS.ChartQSLocal
