/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Rooted.MinimalRootReductive
import AlgMag.Table.Compute

/-!
# Table 1: link between the computable columns and `weylMagnet` / `weylMagnetLower`

For a concrete root datum `G : RD` put `M = Fin n → ℤ`, `Φ = PhiG G ⊆ M` (the computed roots),
`W = Fin |G.weyl|` and `act w` = the integer matrix `G.weyl[w]` acting on `M`. Then `Z_w =
weylMagnet (act w)` and `weylMagnetLower Φ act w = [Φ ∩ Z_w⟩ + Σ_{Z_v ⊊ Z_w} Z_v` are exactly the
objects of `joinIrreducibles_reductive` (`AlgMag/Rooted/MinimalRootReductive.lean`).

`nonRed_ncard`: if the Boolean certificate checker `checkAll G` returns `true`, then
`ncard {Z | ∃ w, Z = Z_w ∧ Z_w ≠ weylMagnetLower Φ act w} = (repsG G).length`.

The checker is verified, the certificate producer (integer echelon form, `echelon`/`reduce`) is
not: every membership `x ∈ ℤ⟨E⟩` is certified by `x = Σ qₖ eₖ`, every non-membership by an
echelon remainder (`span_echelon_eq_zero`).
-/

namespace AlgMag.Table

open AlgMag.Rooted

/-! ### Vectors -/

def toV (n : ℕ) (l : Vec) : Fin n → ℤ := fun i => l.getD i.val 0

/-- Evaluation at coordinate `p` (zero if `p ≥ n`). -/
def ev (n p : ℕ) : (Fin n → ℤ) →+ ℤ :=
  if h : p < n then Pi.evalAddMonoidHom (fun _ => ℤ) ⟨p, h⟩ else 0

lemma ev_toV {n p : ℕ} (h : p < n) (l : Vec) : ev n p (toV n l) = l.getD p 0 := by
  simp [ev, h, toV]

/-- `ℤ⟨L⟩ ⊆ M`. -/
def spanV (n : ℕ) (L : List Vec) : AddSubgroup (Fin n → ℤ) :=
  AddSubgroup.closure {x | ∃ l ∈ L, x = toV n l}

lemma mem_spanV {n : ℕ} {L : List Vec} {l : Vec} (h : l ∈ L) : toV n l ∈ spanV n L :=
  AddSubgroup.subset_closure ⟨l, h, rfl⟩

lemma spanV_mono {n : ℕ} {L L' : List Vec} (h : ∀ l ∈ L, l ∈ L') : spanV n L ≤ spanV n L' :=
  AddSubgroup.closure_mono fun _ ⟨l, hl, e⟩ => ⟨l, h l hl, e⟩

lemma spanV_le {n : ℕ} {L : List Vec} {H : AddSubgroup (Fin n → ℤ)}
    (h : ∀ l ∈ L, toV n l ∈ H) : spanV n L ≤ H :=
  (AddSubgroup.closure_le H).2 fun _ ⟨l, hl, e⟩ => e ▸ h l hl

lemma mem_spanV_cons {n : ℕ} {e : Vec} {L : List Vec} {x : Fin n → ℤ}
    (hx : x ∈ spanV n (e :: L)) : ∃ a : ℤ, x - a • toV n e ∈ spanV n L := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    rcases List.mem_cons.1 hl with rfl | hl
    · exact ⟨1, by simp [zero_mem]⟩
    · exact ⟨0, by simpa using mem_spanV hl⟩
  | zero => exact ⟨0, by simp [zero_mem]⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha⟩ := hy
    obtain ⟨b, hb⟩ := hz
    refine ⟨a + b, ?_⟩
    have := add_mem ha hb
    rwa [show y - a • toV n e + (z - b • toV n e) = y + z - (a + b) • toV n e by
      rw [add_smul]; abel] at this
  | neg y _ hy =>
    obtain ⟨a, ha⟩ := hy
    refine ⟨-a, ?_⟩
    have := neg_mem ha
    rwa [show -(y - a • toV n e) = -y - (-a) • toV n e by rw [neg_smul]; abel] at this

/-- `Σ qₖ eₖ` at coordinate `i`. -/
def comboI : List Int → List Vec → Nat → Int
  | q :: qs, e :: es, i => q * e.getD i 0 + comboI qs es i
  | _, _, _ => 0

lemma combo_mem (n : ℕ) : ∀ (q : List Int) (es : List Vec),
    (fun i : Fin n => comboI q es i) ∈ spanV n es
  | q :: qs, e :: es => by
    have h1 := combo_mem n qs es
    have h2 : (fun i : Fin n => comboI (q :: qs) (e :: es) i) =
        q • toV n e + fun i : Fin n => comboI qs es i := by
      funext i; simp [comboI, toV]
    rw [h2]
    exact add_mem (zsmul_mem (mem_spanV List.mem_cons_self) _)
      (spanV_mono (fun l hl => List.mem_cons_of_mem _ hl) h1)
  | [], es => by
    have : (fun i : Fin n => comboI [] es i) = 0 := by funext i; cases es <;> rfl
    rw [this]; exact zero_mem _
  | q :: qs, [] => by
    have : (fun i : Fin n => comboI (q :: qs) [] i) = 0 := by funext i; rfl
    rw [this]; exact zero_mem _

/-! ### Certified membership in an echelon lattice -/

def zeroB (n : Nat) (r : Vec) : Bool := (List.range n).all fun i => r.getD i 0 == 0

def nonzeroB (n : Nat) (r : Vec) : Bool := (List.range n).any fun i => r.getD i 0 != 0

lemma toV_of_zeroB {n : ℕ} {r : Vec} (h : zeroB n r = true) : toV n r = 0 := by
  funext i
  simp only [zeroB, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h i i.isLt

lemma toV_ne_of_nonzeroB {n : ℕ} {r : Vec} (h : nonzeroB n r = true) : toV n r ≠ 0 := by
  simp only [nonzeroB, List.any_eq_true, List.mem_range, bne_iff_ne, ne_eq] at h
  obtain ⟨i, hi, hne⟩ := h
  intro h0
  exact hne (congrFun h0 ⟨i, hi⟩)

def rowsOf (E : List (Nat × Row)) : List Vec := E.map fun e => e.2.1

/-- Pivots in range, positive pivot entries, later rows vanish at earlier pivots. -/
def echB (n : Nat) : List (Nat × Row) → Bool
  | [] => true
  | (p, e) :: rest => decide (p < n) && decide (0 < e.1.getD p 0) &&
      rest.all (fun f => f.2.1.getD p 0 == 0) && echB n rest

def boundB (r : Vec) : List (Nat × Row) → Bool
  | [] => true
  | (p, e) :: rest => decide (0 ≤ r.getD p 0) && decide (r.getD p 0 < e.1.getD p 0) &&
      boundB r rest

/-- An echelon remainder lying in the lattice is zero. -/
theorem span_echelon_eq_zero {n : ℕ} {r : Vec} :
    ∀ E : List (Nat × Row), echB n E = true → boundB r E = true →
      toV n r ∈ spanV n (rowsOf E) → toV n r = 0
  | [], _, _, h => by
    simpa [rowsOf, spanV] using h
  | (p, e) :: rest, he, hb, hr => by
    simp only [echB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at he
    obtain ⟨⟨⟨hp, hpos⟩, hzero⟩, hrest⟩ := he
    simp only [boundB, Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨⟨hb0, hb1⟩, hbrest⟩ := hb
    obtain ⟨a, ha⟩ := mem_spanV_cons (L := rowsOf rest) hr
    have hev : ∀ x ∈ spanV n (rowsOf rest), ev n p x = 0 := by
      intro x hx
      have : spanV n (rowsOf rest) ≤ (ev n p).ker := spanV_le fun l hl => by
        simp only [rowsOf, List.mem_map] at hl
        obtain ⟨f, hf, rfl⟩ := hl
        rw [AddMonoidHom.mem_ker, ev_toV hp]; exact hzero f hf
      exact this hx
    have h1 := hev _ ha
    rw [map_sub, map_zsmul, ev_toV hp, ev_toV hp, smul_eq_mul] at h1
    have ha0 : a = 0 := by
      rcases lt_trichotomy a 0 with h | h | h
      · nlinarith
      · exact h
      · nlinarith
    subst ha0
    simp only [zero_smul, sub_zero] at ha
    exact span_echelon_eq_zero rest hrest hbrest ha

/-- `x = r + Σ qₖ eₖ` coordinatewise. -/
def reprB (n : Nat) (es : List Vec) (x r : Vec) (q : List Int) : Bool :=
  (List.range n).all fun i => x.getD i 0 == r.getD i 0 + comboI q es i

lemma toV_of_reprB {n : ℕ} {es : List Vec} {x r : Vec} {q : List Int}
    (h : reprB n es x r q = true) :
    toV n x = toV n r + fun i : Fin n => comboI q es i := by
  funext i
  simp only [reprB, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h i i.isLt

/-- Certified decision of `x ∈ ℤ⟨E⟩`. -/
def memDec (n : Nat) (E : List (Nat × Row)) (x : Vec) : Option Bool :=
  let rq := reduce E x
  if reprB n (rowsOf E) x rq.1 rq.2 then
    (if zeroB n rq.1 then some true
     else if nonzeroB n rq.1 && boundB rq.1 E then some false else none)
  else none

lemma memDec_true {n : ℕ} {E : List (Nat × Row)} {x : Vec} (h : memDec n E x = some true) :
    toV n x ∈ spanV n (rowsOf E) := by
  simp only [memDec] at h
  by_cases h1 : reprB n (rowsOf E) x (reduce E x).1 (reduce E x).2 = true
  · rw [if_pos h1] at h
    by_cases h2 : zeroB n (reduce E x).1 = true
    · rw [toV_of_reprB h1, toV_of_zeroB h2, zero_add]
      exact combo_mem n _ _
    · rw [if_neg h2] at h
      split_ifs at h <;> cases h
  · rw [if_neg h1] at h; cases h

lemma memDec_false {n : ℕ} {E : List (Nat × Row)} {x : Vec} (hE : echB n E = true)
    (h : memDec n E x = some false) : toV n x ∉ spanV n (rowsOf E) := by
  simp only [memDec] at h
  by_cases h1 : reprB n (rowsOf E) x (reduce E x).1 (reduce E x).2 = true
  · rw [if_pos h1] at h
    by_cases h2 : zeroB n (reduce E x).1 = true
    · rw [if_pos h2] at h; cases h
    · rw [if_neg h2] at h
      by_cases h3 : (nonzeroB n (reduce E x).1 && boundB (reduce E x).1 E) = true
      · simp only [Bool.and_eq_true] at h3
        intro hx
        have hr : toV n (reduce E x).1 ∈ spanV n (rowsOf E) := by
          have := sub_mem hx (combo_mem n (reduce E x).2 (rowsOf E))
          rwa [toV_of_reprB h1, add_sub_cancel_right] at this
        exact toV_ne_of_nonzeroB h3.1 (span_echelon_eq_zero E hE h3.2 hr)
      · rw [if_neg h3] at h; cases h
  · rw [if_neg h1] at h; cases h

/-- `E` is an echelon basis of `ℤ⟨gens⟩`. -/
def latB (n : Nat) (gens : List Vec) (E : List (Nat × Row)) : Bool :=
  echB n E && E.all (fun e => (List.range n).all fun i => e.2.1.getD i 0 == comboI e.2.2 gens i)
    && gens.all (fun g => memDec n E g == some true)

lemma spanV_of_latB {n : ℕ} {gens : List Vec} {E : List (Nat × Row)}
    (h : latB n gens E = true) : spanV n (rowsOf E) = spanV n gens := by
  simp only [latB, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨⟨_, hrows⟩, hgens⟩ := h
  apply le_antisymm
  · refine spanV_le fun l hl => ?_
    simp only [rowsOf, List.mem_map] at hl
    obtain ⟨e, he, rfl⟩ := hl
    have : toV n e.2.1 = fun i : Fin n => comboI e.2.2 gens i := by
      funext i; exact hrows e he i i.isLt
    rw [this]; exact combo_mem n _ _
  · exact spanV_le fun g hg => memDec_true (hgens g hg)

lemma echB_of_latB {n : ℕ} {gens : List Vec} {E : List (Nat × Row)}
    (h : latB n gens E = true) : echB n E = true := by
  simp only [latB, Bool.and_eq_true] at h; exact h.1.1

/-! ### Matrices acting on `M = Fin n → ℤ` and Weyl magnets -/

def entry (A : Mat) (r c : Nat) : Int := (A.getD r []).getD c 0

/-- The integer matrix `A` acting on `M = Fin n → ℤ`. -/
def matHom (n : ℕ) (A : Mat) : (Fin n → ℤ) →+ (Fin n → ℤ) where
  toFun v := fun r => ∑ c : Fin n, entry A r c * v c
  map_zero' := by funext r; simp
  map_add' v w := by funext r; simp [mul_add, Finset.sum_add_distrib]

/-- Generators of `Z_A = (1 - A)M`: the columns of `1 - A`. -/
def zg (n : Nat) (A : Mat) : List Vec :=
  (List.range n).map fun j => (List.range n).map fun r => (if r == j then 1 else 0) - entry A r j

lemma toV_zg_col {n j : ℕ} (hj : j < n) (A : Mat) :
    toV n ((List.range n).map fun r => (if r == j then 1 else 0) - entry A r j) =
      (AddMonoidHom.id (Fin n → ℤ) - matHom n A) (Pi.single ⟨j, hj⟩ 1) := by
  funext r
  have hr := r.isLt
  have e1 : ((List.range n).map fun r => (if r == j then (1 : Int) else 0) - entry A r j).getD r 0
      = (if r.val == j then 1 else 0) - entry A r j := by
    simp [List.getD_eq_getElem?_getD, hr]
  have e2 : (matHom n A) (Pi.single ⟨j, hj⟩ 1) r = entry A r j := by
    show ∑ c : Fin n, entry A r c * (Pi.single (⟨j, hj⟩ : Fin n) (1 : ℤ) : Fin n → ℤ) c =
      entry A r j
    simp [Pi.single_apply]
  simp only [toV, AddMonoidHom.sub_apply, AddMonoidHom.id_apply, Pi.sub_apply, e1, e2]
  by_cases h : r.val = j
  · have : r = ⟨j, hj⟩ := Fin.ext h
    subst this; simp
  · have : r ≠ ⟨j, hj⟩ := fun e => h (congrArg Fin.val e)
    simp [Pi.single_apply, h, this]

/-- `Z_A = (1 - A)M` is spanned by the columns `zg n A`. -/
theorem weylMagnet_eq_spanV (n : ℕ) (A : Mat) :
    (weylMagnet (matHom n A) : Set (Fin n → ℤ)) = spanV n (zg n A) := by
  set f := AddMonoidHom.id (Fin n → ℤ) - matHom n A
  apply Set.Subset.antisymm
  · rintro _ ⟨v, rfl⟩
    show f v ∈ spanV n (zg n A)
    have hv : v = ∑ j : Fin n, v j • Pi.single j (1 : ℤ) := by
      funext i; simp [Finset.sum_apply, Pi.single_apply]
    rw [hv, map_sum]
    refine sum_mem fun j _ => ?_
    rw [map_zsmul]
    refine zsmul_mem ?_ _
    rw [← toV_zg_col j.isLt]
    exact mem_spanV (List.mem_map.2 ⟨j, List.mem_range.2 j.isLt, rfl⟩)
  · have : spanV n (zg n A) ≤ f.range := spanV_le fun l hl => by
      simp only [zg, List.mem_map, List.mem_range] at hl
      obtain ⟨j, hj, rfl⟩ := hl
      rw [toV_zg_col hj]; exact ⟨_, rfl⟩
    intro x hx
    obtain ⟨v, hv⟩ := this hx
    exact ⟨v, hv⟩

/-! ### The checker for a root datum -/

/-- Echelon basis of `Z_w`, `w` the `i`-th element of `W`. -/
def RD.ez (G : RD) (i : Nat) : List (Nat × Row) := echelon G.n (zg G.n (G.weyl.getD i []))

/-- Certified decision of `Z_v ⊆ Z_w`. -/
def RD.leDec (G : RD) (v w : Nat) : Option Bool :=
  let res := (zg G.n (G.weyl.getD v [])).map (memDec G.n (G.ez w))
  if res.all (· == some true) then some true
  else if res.any (· == some false) then some false else none

/-- Generators of `[Φ ∩ Z_w⟩ + Σ_{Z_v ⊊ Z_w} Z_v`. -/
def RD.lowerG (G : RD) (w : Nat) : List Vec :=
  G.rootsM.filter (fun a => memDec G.n (G.ez w) a == some true) ++
    (List.range G.weyl.length).flatMap fun v =>
      if G.leDec v w == some true && G.leDec w v == some false then zg G.n (G.weyl.getD v [])
      else []

def RD.fl (G : RD) (w : Nat) : List (Nat × Row) := echelon G.n (G.lowerG w)

/-- `some true`: non-redundant, `some false`: redundant. -/
def RD.nrDec (G : RD) (w : Nat) : Option Bool :=
  let res := (zg G.n (G.weyl.getD w [])).map (memDec G.n (G.fl w))
  if res.all (· == some true) then some false
  else if res.any (· == some false) then some true else none

/-- One representative index per distinct non-redundant `Z_w`. -/
def RD.repsG (G : RD) : List Nat :=
  ((List.range G.weyl.length).filter fun w => G.nrDec w == some true).foldl
    (fun acc w => if acc.any (fun r => G.leDec w r == some true && G.leDec r w == some true)
      then acc else acc ++ [w]) []

def RD.symB (G : RD) : Bool :=
  G.rootsM.all fun a => G.rootsM.any fun b =>
    (List.range G.n).all fun i => b.getD i 0 == -(a.getD i 0)

def distinctB (G : RD) : List Nat → Bool
  | [] => true
  | a :: rest => rest.all (fun b => G.leDec a b == some false || G.leDec b a == some false) &&
      distinctB G rest

/-- The full Boolean certificate check. -/
def RD.checkAll (G : RD) : Bool :=
  let N := G.weyl.length
  let ws := List.range N
  G.symB &&
  ws.all (fun w => latB G.n (zg G.n (G.weyl.getD w [])) (G.ez w)) &&
  ws.all (fun w => G.rootsM.all fun a => memDec G.n (G.ez w) a != none) &&
  ws.all (fun v => ws.all fun w => G.leDec v w != none) &&
  ws.all (fun w => latB G.n (G.lowerG w) (G.fl w) && G.nrDec w != none) &&
  G.repsG.all (fun r => decide (r < N) && G.nrDec r == some true) &&
  ws.all (fun w => G.nrDec w != some true ||
    G.repsG.any fun r => G.leDec w r == some true && G.leDec r w == some true) &&
  distinctB G G.repsG

/-! ### Soundness -/

lemma ite3_true {a b : Bool} (h : (if a = true then some true else
    if b = true then some false else none) = some true) : a = true := by
  cases a <;> cases b <;> simp_all

lemma ite3_false {a b : Bool} (h : (if a = true then some true else
    if b = true then some false else none) = some false) : b = true := by
  cases a <;> cases b <;> simp_all

lemma ite3'_true {a b : Bool} (h : (if a = true then some false else
    if b = true then some true else none) = some true) : b = true := by
  cases a <;> cases b <;> simp_all

lemma ite3'_false {a b : Bool} (h : (if a = true then some false else
    if b = true then some true else none) = some false) : a = true := by
  cases a <;> cases b <;> simp_all

lemma closure_le_of_neg {M : Type*} [AddCommGroup M] {S : Set M} {L : AddSubmonoid M}
    (h1 : S ⊆ L) (h2 : ∀ x ∈ S, -x ∈ L) : (AddSubgroup.closure S).toAddSubmonoid ≤ L := by
  rw [AddSubgroup.closure_toAddSubmonoid]
  refine AddSubmonoid.closure_le.2 ?_
  rintro x (hx | hx)
  · exact h1 hx
  · have := h2 (-x) hx; simpa using this

variable (G : RD)

/-- The roots, in `M = Fin n → ℤ`. -/
def RD.PhiG : Set (Fin G.n → ℤ) := {x | ∃ a ∈ G.rootsM, x = toV G.n a}

/-- `act w` for `w : W = Fin |G.weyl|`. -/
def RD.actG (w : Fin G.weyl.length) : (Fin G.n → ℤ) →+ (Fin G.n → ℤ) :=
  matHom G.n (G.weyl.getD w.val [])

/-- `Z_w` as an additive subgroup. -/
def RD.zSub (i : Nat) : AddSubgroup (Fin G.n → ℤ) := spanV G.n (zg G.n (G.weyl.getD i []))

lemma RD.coe_weylMagnet (w : Fin G.weyl.length) :
    (weylMagnet (G.actG w) : Set (Fin G.n → ℤ)) = G.zSub w.val :=
  weylMagnet_eq_spanV _ _

lemma RD.weylMagnet_le_iff (v w : Fin G.weyl.length) :
    weylMagnet (G.actG v) ≤ weylMagnet (G.actG w) ↔ G.zSub v.val ≤ G.zSub w.val := by
  constructor
  · intro h
    have := SetLike.coe_subset_coe.2 h
    rw [G.coe_weylMagnet, G.coe_weylMagnet] at this
    exact SetLike.coe_subset_coe.1 this
  · intro h
    have := SetLike.coe_subset_coe.2 h
    rw [← G.coe_weylMagnet, ← G.coe_weylMagnet] at this
    exact SetLike.coe_subset_coe.1 this

section Sound

variable {G}
variable (hc : G.checkAll = true)
include hc

lemma RD.parts : G.symB = true ∧
    (∀ w < G.weyl.length, latB G.n (zg G.n (G.weyl.getD w [])) (G.ez w) = true) ∧
    (∀ w < G.weyl.length, ∀ a ∈ G.rootsM, memDec G.n (G.ez w) a ≠ none) ∧
    (∀ v < G.weyl.length, ∀ w < G.weyl.length, G.leDec v w ≠ none) ∧
    (∀ w < G.weyl.length, latB G.n (G.lowerG w) (G.fl w) = true ∧ G.nrDec w ≠ none) ∧
    (∀ r ∈ G.repsG, r < G.weyl.length ∧ G.nrDec r = some true) ∧
    (∀ w < G.weyl.length, G.nrDec w = some true →
      ∃ r ∈ G.repsG, G.leDec w r = some true ∧ G.leDec r w = some true) ∧
    distinctB G G.repsG = true := by
  simp only [RD.checkAll, Bool.and_eq_true, List.all_eq_true, List.mem_range, bne_iff_ne,
    ne_eq, decide_eq_true_eq, beq_iff_eq, List.any_eq_true, Bool.or_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := hc
  refine ⟨h1, h2, h3, h4, fun w hw => ⟨(h5 w hw).1, (h5 w hw).2⟩, h6, fun w hw hnr => ?_, h8⟩
  rcases h7 w hw with h | h
  · exact absurd hnr h
  · exact h

lemma RD.span_ez {w : Nat} (hw : w < G.weyl.length) : spanV G.n (rowsOf (G.ez w)) = G.zSub w :=
  spanV_of_latB ((G.parts hc).2.1 w hw)

lemma RD.leDec_sound {v w : Nat} (hw : w < G.weyl.length) :
    (G.leDec v w = some true → G.zSub v ≤ G.zSub w) ∧
    (G.leDec v w = some false → ¬ G.zSub v ≤ G.zSub w) := by
  have hE := echB_of_latB ((G.parts hc).2.1 w hw)
  constructor
  · intro h
    simp only [RD.leDec] at h
    have h1 := ite3_true h
    simp only [List.all_eq_true, List.mem_map, beq_iff_eq, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂] at h1
    refine spanV_le fun g hg => ?_
    rw [← G.span_ez hc hw]; exact memDec_true (h1 g hg)
  · intro h hle
    simp only [RD.leDec] at h
    have h2 := ite3_false h
    simp only [List.any_eq_true, List.mem_map, beq_iff_eq] at h2
    obtain ⟨_, ⟨g, hg, rfl⟩, hgf⟩ := h2
    have := hle (mem_spanV hg)
    rw [← G.span_ez hc hw] at this
    exact memDec_false hE hgf this

lemma RD.leDec_iff {v w : Nat} (hv : v < G.weyl.length) (hw : w < G.weyl.length) :
    G.leDec v w = some true ↔ G.zSub v ≤ G.zSub w := by
  refine ⟨(G.leDec_sound hc hw).1, fun hle => ?_⟩
  have hne := (G.parts hc).2.2.2.1 v hv w hw
  rcases h : G.leDec v w with _ | _ | _
  · exact absurd h hne
  · exact absurd hle ((G.leDec_sound hc hw).2 h)
  · rfl

lemma RD.leDec_false_iff {v w : Nat} (hv : v < G.weyl.length) (hw : w < G.weyl.length) :
    G.leDec v w = some false ↔ ¬ G.zSub v ≤ G.zSub w := by
  refine ⟨(G.leDec_sound hc hw).2, fun hle => ?_⟩
  have hne := (G.parts hc).2.2.2.1 v hv w hw
  rcases h : G.leDec v w with _ | _ | _
  · exact absurd h hne
  · rfl
  · exact absurd ((G.leDec_sound hc hw).1 h) hle

/-- The Boolean non-redundancy decision is the mathematical one. -/
theorem RD.nrDec_iff (w : Fin G.weyl.length) :
    G.nrDec w.val = some true ↔
      weylMagnet (G.actG w) ≠ weylMagnetLower G.PhiG G.actG w := by
  obtain ⟨hsym, _, hroot, _, hlow, _⟩ := G.parts hc
  have hw := w.isLt
  have hZ := G.coe_weylMagnet w
  have hspanF := spanV_of_latB (hlow w hw).1
  have hEF := echB_of_latB (hlow w hw).1
  -- the generators of `lowerG` lie in `weylMagnetLower`, with their negatives
  have hgen : ∀ l ∈ G.lowerG w, toV G.n l ∈ weylMagnetLower G.PhiG G.actG w ∧
      -toV G.n l ∈ weylMagnetLower G.PhiG G.actG w := by
    intro l hl
    simp only [RD.lowerG, List.mem_append, List.mem_filter, beq_iff_eq, List.mem_flatMap,
      List.mem_range] at hl
    rcases hl with ⟨ha, hmem⟩ | ⟨v, hv, hlv⟩
    · have hZw : toV G.n l ∈ G.zSub w := by rw [← G.span_ez hc hw]; exact memDec_true hmem
      obtain ⟨b, hb, hbneg⟩ := by
        simp only [RD.symB, List.all_eq_true, List.any_eq_true, List.mem_range,
          beq_iff_eq] at hsym
        exact hsym l ha
      have hneg : toV G.n b = -toV G.n l := by
        funext i; show b.getD i 0 = -(l.getD i 0); exact hbneg i i.isLt
      have key : ∀ x, x ∈ G.PhiG → x ∈ G.zSub w →
          x ∈ weylMagnetLower G.PhiG G.actG w := fun x hxΦ hxZ =>
        AddSubmonoid.mem_sup_left (AddSubmonoid.subset_closure
          ⟨by rw [SetLike.mem_coe, ← SetLike.mem_coe, hZ]; exact hxZ, hxΦ⟩)
      exact ⟨key _ ⟨l, ha, rfl⟩ hZw, key _ ⟨b, hb, hneg.symm⟩ (hneg ▸ neg_mem hZw)⟩
    · split_ifs at hlv with hvw
      · simp only [Bool.and_eq_true, beq_iff_eq] at hvw
        have hlt : weylMagnet (G.actG ⟨v, hv⟩) < weylMagnet (G.actG w) := by
          refine lt_of_le_not_ge ?_ ?_
          · rw [G.weylMagnet_le_iff]; exact (G.leDec_iff hc hv hw).1 hvw.1
          · rw [G.weylMagnet_le_iff]; exact (G.leDec_false_iff hc hw hv).1 hvw.2
        have hsub : weylMagnet (G.actG ⟨v, hv⟩) ≤ weylMagnetLower G.PhiG G.actG w :=
          le_sup_of_le_right (le_iSup₂_of_le (f := fun v
            (_ : v ∈ {v | weylMagnet (G.actG v) < weylMagnet (G.actG w)}) =>
              weylMagnet (G.actG v)) ⟨v, hv⟩ hlt le_rfl)
        have hl : toV G.n l ∈ G.zSub v := mem_spanV hlv
        have hZv := G.coe_weylMagnet ⟨v, hv⟩
        refine ⟨hsub ?_, hsub ?_⟩
        · rw [← SetLike.mem_coe, hZv]; exact hl
        · rw [← SetLike.mem_coe, hZv]; exact neg_mem hl
      · simp at hlv
  -- `weylMagnetLower ≤ ℤ⟨lowerG⟩`
  have hlower : ∀ x ∈ weylMagnetLower G.PhiG G.actG w, x ∈ spanV G.n (G.lowerG w) := by
    have : weylMagnetLower G.PhiG G.actG w ≤ (spanV G.n (G.lowerG w)).toAddSubmonoid := by
      refine sup_le (AddSubmonoid.closure_le.2 ?_) (iSup₂_le fun v hv => ?_)
      · rintro x ⟨hxZ, ⟨a, ha, rfl⟩⟩
        rw [SetLike.mem_coe, ← SetLike.mem_coe, hZ] at hxZ
        have hdec := hroot w hw a ha
        rcases hm : memDec G.n (G.ez w) a with _ | _ | _
        · exact absurd hm hdec
        · exact absurd (by rw [G.span_ez hc hw]; exact hxZ) (memDec_false
            (echB_of_latB ((G.parts hc).2.1 w hw)) hm)
        · exact mem_spanV (List.mem_append_left _ (List.mem_filter.2 ⟨ha, by simp [hm]⟩))
      · have hvle : G.zSub v.val ≤ G.zSub w.val := (G.weylMagnet_le_iff v w).1 hv.le
        have hwv : ¬ G.zSub w.val ≤ G.zSub v.val := fun h => hv.not_ge ((G.weylMagnet_le_iff w v).2 h)
        have h1 := (G.leDec_iff hc v.isLt hw).2 hvle
        have h2 := (G.leDec_false_iff hc hw v.isLt).2 hwv
        intro x hx
        rw [← SetLike.mem_coe, G.coe_weylMagnet] at hx
        refine spanV_mono (fun l hl => List.mem_append_right _ ?_) hx
        exact List.mem_flatMap.2 ⟨v.val, List.mem_range.2 v.isLt, by simpa [h1, h2] using hl⟩
    exact fun x hx => this hx
  constructor
  · -- non-redundant
    intro h heq
    simp only [RD.nrDec] at h
    have h2 := ite3'_true h
    simp only [List.any_eq_true, List.mem_map, beq_iff_eq] at h2
    obtain ⟨_, ⟨g, hg, rfl⟩, hgf⟩ := h2
    have hgZ : toV G.n g ∈ weylMagnet (G.actG w) := by
      rw [← SetLike.mem_coe, hZ]; exact mem_spanV hg
    rw [heq] at hgZ
    have := hlower _ hgZ
    rw [← hspanF] at this
    exact memDec_false hEF hgf this
  · -- redundant ⇒ equality
    intro hne
    rcases hd : G.nrDec w.val with _ | _ | _
    · exact absurd hd (hlow w hw).2
    · exfalso; apply hne
      simp only [RD.nrDec] at hd
      have h1 := ite3'_false hd
      simp only [List.all_eq_true, List.mem_map, beq_iff_eq, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂] at h1
      apply le_antisymm
      · -- `Z_w ≤ lower`
        intro x hx
        rw [← SetLike.mem_coe, hZ] at hx
        have hle : spanV G.n (zg G.n (G.weyl.getD w.val [])) ≤ spanV G.n (G.lowerG w) :=
          spanV_le fun g hg => by rw [← hspanF]; exact memDec_true (h1 g hg)
        have hfin : (spanV G.n (G.lowerG w)).toAddSubmonoid ≤ weylMagnetLower G.PhiG G.actG w :=
          closure_le_of_neg (fun y ⟨l, hl, e⟩ => e ▸ (hgen l hl).1)
            (fun y ⟨l, hl, e⟩ => e ▸ (hgen l hl).2)
        exact hfin (hle hx)
      · -- `lower ≤ Z_w`
        refine sup_le (AddSubmonoid.closure_le.2 fun x hx => hx.1) (iSup₂_le fun v hv => hv.le)
    · rfl

/-- **Table certificate.** The number of non-redundant Weyl (cyclotomic) roots of `G`, in the sense
of `joinIrreducibles_reductive`, is `(repsG G).length`. -/
theorem RD.nonRed_ncard :
    Set.ncard {Z : AddSubmonoid (Fin G.n → ℤ) | ∃ w, Z = weylMagnet (G.actG w) ∧
      weylMagnet (G.actG w) ≠ weylMagnetLower G.PhiG G.actG w} = G.repsG.length := by
  classical
  obtain ⟨_, _, _, _, _, hreps, hcover, hdist⟩ := G.parts hc
  let Zr : Nat → AddSubgroup (Fin G.n → ℤ) := G.zSub
  have hset : {Z : AddSubmonoid (Fin G.n → ℤ) | ∃ w, Z = weylMagnet (G.actG w) ∧
      weylMagnet (G.actG w) ≠ weylMagnetLower G.PhiG G.actG w} =
      ((G.repsG.map fun r => (Zr r).toAddSubmonoid).toFinset : Set _) := by
    ext Z
    simp only [Set.mem_setOf_eq, List.coe_toFinset, List.mem_map]
    constructor
    · rintro ⟨w, rfl, hw⟩
      obtain ⟨r, hr, h1, h2⟩ := hcover w.val w.isLt ((G.nrDec_iff hc w).2 hw)
      have hrN := (hreps r hr).1
      refine ⟨r, hr, ?_⟩
      apply SetLike.coe_injective
      rw [G.coe_weylMagnet]
      exact congrArg _ (le_antisymm ((G.leDec_iff hc hrN w.isLt).1 h2)
        ((G.leDec_iff hc w.isLt hrN).1 h1))
    · rintro ⟨r, hr, rfl⟩
      have hrN := (hreps r hr).1
      refine ⟨⟨r, hrN⟩, ?_, (G.nrDec_iff hc ⟨r, hrN⟩).1 (hreps r hr).2⟩
      apply SetLike.coe_injective
      rw [G.coe_weylMagnet]; rfl
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup]
  · simp
  · -- distinct representatives give distinct subgroups
    have key : ∀ L : List Nat, (∀ r ∈ L, r ∈ G.repsG) → distinctB G L = true →
        (L.map fun r => (Zr r).toAddSubmonoid).Nodup := by
      intro L
      induction L with
      | nil => intros; simp
      | cons a L ih =>
        intro hL hd
        simp only [distinctB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
          beq_iff_eq] at hd
        simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
        refine ⟨fun b hb heq => ?_, ih (fun r hr => hL r (List.mem_cons_of_mem _ hr)) hd.2⟩
        have ha := (hreps a (hL a List.mem_cons_self)).1
        have hb' := (hreps b (hL b (List.mem_cons_of_mem _ hb))).1
        have heq' : G.zSub b = G.zSub a := AddSubgroup.toAddSubmonoid_injective heq
        rcases hd.1 b hb with h | h
        · exact (G.leDec_false_iff hc ha hb').1 h heq'.symm.le
        · exact (G.leDec_false_iff hc hb' ha).1 h heq'.le
    exact key _ (fun r hr => hr) hdist

end Sound

end AlgMag.Table
