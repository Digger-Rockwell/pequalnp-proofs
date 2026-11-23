import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_701_aux

abbrev W := BitVec 55

def wide (x : W) : Bool :=
  let s := x.toNat / 1125899906842624
  (s &&& (s - 1)) != 0

def ops1List (x y : W) : List W :=
  let o := x ||| y
  if wide o then [x &&& y, o] else [x &&& y]

def ops2List (x y : W) : List W :=
  let o := x ||| y
  if wide o then [] else [o]

abbrev basicOps1 (a b : W) : Finset W := (ops1List a b).toFinset
abbrev basicOps2 (a b : W) : Finset W := (ops2List a b).toFinset

def sep (x : W) : BitVec 25 := ((x >>> 25) &&& ~~~x).setWidth 25

def cuts (ws : List W) : BitVec 25 := ws.foldr (fun w v => sep w ||| v) 0

def goal : W := 0x3fffffe000000

def x0 : W := 0x41f07fe108421
def x1 : W := 0x800f83ea5294a
def x2 : W := 0x1000ffc14a5294
def x3 : W := 0x23ff00006318c6
def x4 : W := 0x43e000019ce739

def rawInputs : List W := [x0, x1, x2, x3, x4]

def inputs : List W := rawInputs

section Trace

def build (ops1 ops2 : W → W → Finset W) (g : W) : ℕ → Finset W → Prop
  | 0, available => g ∈ available
  | 1, available => build ops1 ops2 g 0 available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops1 a b, z ∉ available ∧ build ops1 ops2 g 0 (insert z available)
  | k + 2, available => build ops1 ops2 g (k + 1) available ∨
    (∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops1 a b, z ∉ available ∧ build ops1 ops2 g (k + 1) (insert z available)) ∨
    (∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops2 a b, z ∉ available ∧ build ops1 ops2 g k (insert z available))

theorem build_step {ops1 ops2 : W → W → Finset W} {g : W} {k : ℕ} {av : Finset W}
    (h : build ops1 ops2 g k av) : build ops1 ops2 g (k + 1) av := by
  cases k with
  | zero => exact Or.inl h
  | succ k => exact Or.inl h

theorem extend_build {ops1 ops2 : W → W → Finset W} {g : W} {m n : ℕ} {av : Finset W}
    (le : m ≤ n) (h : build ops1 ops2 g m av) : build ops1 ops2 g n av := by
  induction le with
  | refl => exact h
  | step _ ih => exact build_step ih

theorem build_step1 {ops1 ops2 : W → W → Finset W} {g : W} {k : ℕ} {av : Finset W}
    {a b z : W} (ha : a ∈ av) (hb : b ∈ av) (hab : a ≠ b) (hz : z ∈ ops1 a b) (hzout : z ∉ av)
    (ht : build ops1 ops2 g k (insert z av)) : build ops1 ops2 g (k + 1) av := by
  cases k with
  | zero => exact Or.inr ⟨a, ha, b, hb, hab, z, hz, hzout, ht⟩
  | succ k => exact Or.inr (Or.inl ⟨a, ha, b, hb, hab, z, hz, hzout, ht⟩)

def stepCost (is2 : Bool) : ℕ := if is2 then 2 else 1

def traceCost : List (W × W × W × Bool) → ℕ
  | [] => 0
  | (_, _, _, is2) :: t => stepCost is2 + traceCost t

def validTrace (ops1 ops2 : W → W → Finset W) (g : W) :
    List (W × W × W × Bool) → Finset W → Finset W → Prop
  | [], _, s => s = {g}
  | (a, b, z, is2) :: t, seen, s =>
      a ∈ s ∧ b ∈ s ∧ a ≠ b ∧
      z ∈ (if is2 then ops2 a b else ops1 a b) ∧
      z ∉ seen ∧
      ∃ rest : Finset W, s = insert a (insert b rest) ∧
        validTrace ops1 ops2 g t (insert z seen) (insert z rest)

theorem validTrace_mono {ops1 ops2 : W → W → Finset W} {g : W} :
    ∀ {T : List (W × W × W × Bool)} {seen1 seen2 s : Finset W},
    seen1 ⊆ seen2 → validTrace ops1 ops2 g T seen2 s → validTrace ops1 ops2 g T seen1 s
  | [], _, _, _, _, h => h
  | (_, _, z, _) :: _, _, _, _, hsub, ⟨ha, hb, hab, hz, hout, rest, hs, tail⟩ =>
    ⟨ha, hb, hab, hz, fun hm => hout (hsub hm), rest, hs,
      validTrace_mono (Finset.insert_subset_insert z hsub) tail⟩

private theorem compress_step {ops1 ops2 : W → W → Finset W} {g : W}
    {T : List (W × W × W × Bool)} {av t : Finset W} {a b z : W} {is2 : Bool}
    (ha : a ∈ av) (hb : b ∈ av) (hab : a ≠ b)
    (hz : z ∈ (if is2 then ops2 a b else ops1 a b)) (hzout : z ∉ av)
    (ht : t ⊆ insert z av) (hrun : validTrace ops1 ops2 g T (insert z av) t) :
    ∃ T' s, s ⊆ av ∧ traceCost T' ≤ stepCost is2 + traceCost T ∧ validTrace ops1 ops2 g T' av s := by
  by_cases sub : t ⊆ av
  · exact ⟨T, t, sub, Nat.le_add_left _ _, validTrace_mono (Finset.subset_insert z av) hrun⟩
  · have hzmem : z ∈ t := by
      by_contra hn
      apply sub
      intro u hu
      rcases Finset.mem_insert.mp (ht hu) with rfl | ok
      · exact False.elim (hn hu)
      · exact ok
    let rest := t.erase z
    have hrest : rest ⊆ av := by
      intro u hu
      have hu' := Finset.mem_erase.mp hu
      exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
    let s := insert a (insert b rest)
    have hs : s ⊆ av := Finset.insert_subset ha (Finset.insert_subset hb hrest)
    refine ⟨(a, b, z, is2) :: T, s, hs, Nat.le_refl _, ?_⟩
    refine ⟨by simp [s], by simp [s], hab, hz, hzout, rest, rfl, ?_⟩
    simpa [rest, Finset.insert_erase hzmem] using hrun

theorem compress {ops1 ops2 : W → W → Finset W} {g : W} :
    ∀ {k : ℕ} {av : Finset W}, build ops1 ops2 g k av →
    ∃ T s, s ⊆ av ∧ traceCost T ≤ k ∧ validTrace ops1 ops2 g T av s
  | 0, _, h => ⟨[], {g}, Finset.singleton_subset_iff.mpr h, Nat.le_refl 0, rfl⟩
  | 1, av, h => by
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hzout, tail⟩
    · obtain ⟨T, s, hs, hc, hrun⟩ := compress skip
      exact ⟨T, s, hs, hc.trans (by omega), hrun⟩
    · obtain ⟨T, t, ht, hc, hrun⟩ := compress tail
      obtain ⟨T', s, hs, hc', hrun'⟩ := compress_step (is2 := false) ha hb hab hz hzout ht hrun
      exact ⟨T', s, hs, hc'.trans (by simp [stepCost]; omega), hrun'⟩
  | k + 2, av, h => by
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hzout, tail⟩ | ⟨a, ha, b, hb, hab, z, hz, hzout, tail⟩
    · obtain ⟨T, s, hs, hc, hrun⟩ := compress skip
      exact ⟨T, s, hs, hc.trans (by omega), hrun⟩
    · obtain ⟨T, t, ht, hc, hrun⟩ := compress tail
      obtain ⟨T', s, hs, hc', hrun'⟩ := compress_step (is2 := false) ha hb hab hz hzout ht hrun
      exact ⟨T', s, hs, hc'.trans (by simp [stepCost]; omega), hrun'⟩
    · obtain ⟨T, t, ht, hc, hrun⟩ := compress tail
      obtain ⟨T', s, hs, hc', hrun'⟩ := compress_step (is2 := true) ha hb hab hz hzout ht hrun
      exact ⟨T', s, hs, hc'.trans (by simp [stepCost]; omega), hrun'⟩

theorem trace_card {ops1 ops2 : W → W → Finset W} {g : W} :
    ∀ {T : List (W × W × W × Bool)} {seen s : Finset W},
    s ⊆ seen → validTrace ops1 ops2 g T seen s → s.card ≤ traceCost T + 1
  | [], _, s, _, h => by change s = {g} at h; simp [h, traceCost]
  | (a, b, z, is2) :: t, seen, s, hsub, ⟨_, _, _, _, hout, rest, hs, tail⟩ => by
    subst hs
    have hrest_sub : rest ⊆ seen := fun u hu => hsub (by simp [hu])
    have hzrest : z ∉ rest := fun hm => hout (hrest_sub hm)
    have hsub' : insert z rest ⊆ insert z seen := Finset.insert_subset_insert z hrest_sub
    have htail := trace_card hsub' tail
    rw [Finset.card_insert_of_notMem hzrest] at htail
    have h1 := Finset.card_insert_le a (insert b rest)
    have h2 := Finset.card_insert_le b rest
    have hsc : 1 ≤ stepCost is2 := by cases is2 <;> simp [stepCost]
    simp only [traceCost]
    omega

theorem trace_separates {ops1 ops2 : W → W → Finset W} {g : W} (D : W → Prop)
    (hd : D g)
    (hops1 : ∀ a b, ∀ z ∈ ops1 a b, D z → D a ∨ D b)
    (hops2 : ∀ a b, ∀ z ∈ ops2 a b, D z → D a ∨ D b) :
    ∀ {T : List (W × W × W × Bool)} {seen s : Finset W},
    validTrace ops1 ops2 g T seen s → ∃ w ∈ s, D w
  | [], _, s, h => by change s = {g} at h; exact ⟨g, by simp [h], hd⟩
  | (a, b, z, is2) :: t, _, s, ⟨ha, hb, _, hz, _, rest, hs, tail⟩ => by
    subst hs
    obtain ⟨w, hw, hD⟩ := trace_separates D hd hops1 hops2 tail
    rcases Finset.mem_insert.mp hw with rfl | hw
    · cases is2 with
      | false =>
        rcases hops1 a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      | true =>
        rcases hops2 a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
    · exact ⟨w, by simp [hw], hD⟩

theorem swap_valid {ops1 ops2 : W → W → Finset W} {g : W}
    {a1 b1 z1 a2 b2 z2 : W} {c1 c2 : Bool} {t : List (W × W × W × Bool)} {seen s : Finset W}
    (hsub : s ⊆ seen) (ha2 : a2 ≠ z1) (hb2 : b2 ≠ z1)
    (h : validTrace ops1 ops2 g ((a1, b1, z1, c1) :: (a2, b2, z2, c2) :: t) seen s) :
    validTrace ops1 ops2 g ((a2, b2, z2, c2) :: (a1, b1, z1, c1) :: t) seen s := by
  obtain ⟨ha1s, hb1s, hab1, hz1, hz1out, r1, hs1, ha2s1, hb2s1, hab2, hz2, hz2out, r2, hs2, tail⟩ := h
  have hr1sub : r1 ⊆ seen := fun u hu => hsub (hs1 ▸ by simp [hu])
  have hz1r1 : z1 ∉ r1 := fun hm => hz1out (hr1sub hm)
  have ha2r1 : a2 ∈ r1 := (Finset.mem_insert.mp ha2s1).resolve_left ha2
  have hb2r1 : b2 ∈ r1 := (Finset.mem_insert.mp hb2s1).resolve_left hb2
  have ha2s : a2 ∈ s := hs1 ▸ by simp [ha2r1]
  have hb2s : b2 ∈ s := hs1 ▸ by simp [hb2r1]
  have hz2out0 : z2 ∉ seen := fun hm => hz2out (Finset.mem_insert_of_mem hm)
  have hz2ne : z2 ≠ z1 := fun e => hz2out (e ▸ Finset.mem_insert_self z1 seen)
  have hz1r2 : z1 ∈ r2 := by
    have hm : z1 ∈ insert a2 (insert b2 r2) := hs2 ▸ Finset.mem_insert_self z1 r1
    exact (Finset.mem_insert.mp ((Finset.mem_insert.mp hm).resolve_left ha2.symm)).resolve_left hb2.symm
  let r' := r2.erase z1
  have hr2eq : insert z1 r' = r2 := Finset.insert_erase hz1r2
  have hz1r' : z1 ∉ r' := Finset.notMem_erase z1 r2
  have hr1eq : r1 = insert a2 (insert b2 r') := by
    ext u
    by_cases hu : u = z1
    · subst hu
      simp [hz1r1, hz1r', ha2.symm, hb2.symm]
    · have hiff : u ∈ insert z1 r1 ↔ u ∈ insert a2 (insert b2 (insert z1 r')) := by
        rw [hs2, hr2eq]
      simp only [Finset.mem_insert, hu, false_or] at hiff ⊢
      exact hiff
  have hs_swap : s = insert a2 (insert b2 (insert a1 (insert b1 r'))) := by
    rw [hs1, hr1eq]
    ext u; simp only [Finset.mem_insert]; tauto
  have hs1'_eq : insert z2 (insert a1 (insert b1 r')) = insert a1 (insert b1 (insert z2 r')) := by
    ext u; simp only [Finset.mem_insert]; tauto
  have hs2'_eq : insert z1 (insert z2 r') = insert z2 r2 := by
    rw [← hr2eq, Finset.insert_comm]
  have hseen_eq : insert z1 (insert z2 seen) = insert z2 (insert z1 seen) := Finset.insert_comm _ _ _
  refine ⟨ha2s, hb2s, hab2, hz2, hz2out0, insert a1 (insert b1 r'), hs_swap, ?_⟩
  refine ⟨by simp, by simp, hab1, hz1, ?_, insert z2 r', hs1'_eq, ?_⟩
  · intro hm
    rcases Finset.mem_insert.mp hm with h1 | h2
    · exact hz2ne h1.symm
    · exact hz1out h2
  · rw [hs2'_eq, hseen_eq]
    exact tail

def isSorted : W → List (W × W × W × Bool) → Prop
  | _, [] => True
  | prevZ, (a, b, z, _) :: t =>
      (a = prevZ ∨ b = prevZ ∨ z.toNat ≤ prevZ.toNat) ∧ isSorted z t

def invCount : List (W × W × W × Bool) → ℕ
  | [] => 0
  | (_, _, z, _) :: t => t.countP (fun e => decide (z.toNat < e.2.2.1.toNat)) + invCount t

private theorem invCount_swap (a1 b1 z1 a2 b2 z2 : W) (c1 c2 : Bool)
    (t : List (W × W × W × Bool)) (hlt : z1.toNat < z2.toNat) :
    invCount ((a2, b2, z2, c2) :: (a1, b1, z1, c1) :: t) <
    invCount ((a1, b1, z1, c1) :: (a2, b2, z2, c2) :: t) := by
  have hnot : ¬ (z2.toNat < z1.toNat) := by omega
  simp only [invCount, List.countP_cons, hlt, hnot, decide_true, decide_false,
    Bool.false_eq_true, ↓reduceIte]
  omega

private theorem step_or_sorted {ops1 ops2 : W → W → Finset W} {g : W} :
    ∀ (T : List (W × W × W × Bool)) (prevZ : W) (seen s : Finset W),
    s ⊆ seen → validTrace ops1 ops2 g T seen s →
    (∀ a b z c t, T = (a, b, z, c) :: t → a = prevZ ∨ b = prevZ ∨ z.toNat ≤ prevZ.toNat) →
    isSorted prevZ T ∨
    ∃ T', validTrace ops1 ops2 g T' seen s ∧ traceCost T' = traceCost T ∧
      T'.Perm T ∧ invCount T' < invCount T
  | [], _, _, _, _, _, _ => Or.inl trivial
  | [(a1, b1, z1, c1)], prevZ, _, _, _, _, hhead =>
    Or.inl ⟨hhead a1 b1 z1 c1 [] rfl, trivial⟩
  | (a1, b1, z1, c1) :: (a2, b2, z2, c2) :: t, prevZ, seen, s, hsub, hv, hhead => by
    by_cases hord : a2 = z1 ∨ b2 = z1 ∨ z2.toNat ≤ z1.toNat
    · obtain ⟨ha1, hb1, hab1, hz1, hz1out, rest1, hs1, tail⟩ := hv
      have hsub1 : insert z1 rest1 ⊆ insert z1 seen :=
        Finset.insert_subset_insert z1 (fun u hu => hsub (hs1 ▸ by simp [hu]))
      rcases step_or_sorted ((a2, b2, z2, c2) :: t) z1 (insert z1 seen) (insert z1 rest1) hsub1 tail
          (fun a b z c t' heq => by cases heq; exact hord) with hsorted | ⟨t', ht', hct', hpt', hinv'⟩
      · exact Or.inl ⟨hhead a1 b1 z1 c1 _ rfl, hsorted⟩
      · refine Or.inr ⟨(a1, b1, z1, c1) :: t', ⟨ha1, hb1, hab1, hz1, hz1out, rest1, hs1, ht'⟩, ?_,
          hpt'.cons _, ?_⟩
        · simp [traceCost, hct']
        · change t'.countP (fun e => decide (z1.toNat < e.2.2.1.toNat)) + invCount t' <
            ((a2, b2, z2, c2) :: t).countP (fun e => decide (z1.toNat < e.2.2.1.toNat)) +
              invCount ((a2, b2, z2, c2) :: t)
          rw [hpt'.countP_eq]
          omega
    · push Not at hord
      obtain ⟨ha2, hb2, hlt⟩ := hord
      refine Or.inr ⟨(a2, b2, z2, c2) :: (a1, b1, z1, c1) :: t,
        swap_valid hsub ha2 hb2 hv, ?_, List.Perm.swap _ _ _, invCount_swap _ _ _ _ _ _ _ _ _ hlt⟩
      simp [traceCost]; omega

theorem exists_sorted_trace {ops1 ops2 : W → W → Finset W} {g : W}
    {seen s : Finset W} (hsub : s ⊆ seen) :
    ∀ {T : List (W × W × W × Bool)},
    validTrace ops1 ops2 g T seen s →
    ∃ T', validTrace ops1 ops2 g T' seen s ∧ traceCost T' = traceCost T ∧
      isSorted (BitVec.allOnes 55) T' := by
  intro T
  induction h : invCount T using Nat.strong_induction_on generalizing T with
  | ind m ih =>
    intro hv
    have hhead : ∀ a b z c t, T = (a, b, z, c) :: t →
        a = BitVec.allOnes 55 ∨ b = BitVec.allOnes 55 ∨ z.toNat ≤ (BitVec.allOnes 55).toNat := by
      intro a b z c t _
      right; right
      have hlt := z.isLt
      have ha : (BitVec.allOnes 55).toNat = 2 ^ 55 - 1 := by decide
      omega
    rcases step_or_sorted T (BitVec.allOnes 55) seen s hsub hv hhead with hsorted | ⟨T', hv', hc', _, hinv'⟩
    · exact ⟨T, hv, rfl, hsorted⟩
    · obtain ⟨T'', hv'', hc'', hs''⟩ := ih (invCount T') (h ▸ hinv') rfl hv'
      exact ⟨T'', hv'', hc''.trans hc', hs''⟩

end Trace

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

def differs (i : Fin 25) (w : W) : Prop :=
  w.getLsbD (25 + i.val) = true ∧ w.getLsbD i.val = false

theorem and_or_differs (i : Fin 25) (a b z : W) (hz : z = a &&& b ∨ z = a ||| b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  unfold differs at hd ⊢
  rcases hz with rfl | rfl <;> revert hd <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] <;>
    cases a.getLsbD (25 + i.val) <;> cases a.getLsbD i.val <;>
    cases b.getLsbD (25 + i.val) <;> cases b.getLsbD i.val <;> simp

theorem ops1_differs (i : Fin 25) (a b z : W) (hz : z ∈ basicOps1 a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  apply and_or_differs i a b z _ hd
  simp only [basicOps1, ops1List, List.mem_toFinset] at hz
  split at hz <;> simp_all

theorem ops2_differs (i : Fin 25) (a b z : W) (hz : z ∈ basicOps2 a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  apply and_or_differs i a b z _ hd
  simp only [basicOps2, ops2List, List.mem_toFinset] at hz
  split at hz <;> simp_all

theorem goal_differs : ∀ i : Fin 25, differs i goal := by
  unfold differs
  decide

theorem cuts_spec (ws : List W) (i : Fin 25) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have hi : i.val < 55 := by omega
    simp [sep, i.isLt, differs, hi, Nat.add_comm]

theorem cuts_full {T : List (W × W × W × Bool)} {seen : Finset W} {ws : List W}
    (h : validTrace basicOps1 basicOps2 goal T seen ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := trace_separates (differs ⟨j, hj⟩) (goal_differs ⟨j, hj⟩)
    (ops1_differs ⟨j, hj⟩) (ops2_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 25)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops1_swap (a b : W) : basicOps1 a b = basicOps1 b a := by
  ext z
  simp only [basicOps1, ops1List, List.mem_toFinset, BitVec.and_comm, BitVec.or_comm]

theorem ops2_swap (a b : W) : basicOps2 a b = basicOps2 b a := by
  ext z
  simp only [basicOps2, ops2List, List.mem_toFinset, BitVec.or_comm]

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem keepChoices_len_ge {a b : W} {r kept : List W} (hk : kept ∈ keepChoices a b r) :
    r.length ≤ kept.length := by
  simp only [keepChoices, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl <;> simp +arith

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def bit (k : Fin 55) (z : W) : Bool := z[k.val]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 55) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

private theorem read_wire (w : List W) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

def evalGateW (w : List W) (g : Gate) : W :=
  match g.op, g.inputs with
  | .and, [] => BitVec.allOnes 55
  | .and, [i] => w.getD i 0
  | .and, [i, j] => w.getD i 0 &&& w.getD j 0
  | .or, [] => 0
  | .or, [i] => w.getD i 0
  | .or, [i, j] => w.getD i 0 ||| w.getD j 0
  | _, _ => 0

def stepW (w : List W) (g : Gate) : List W :=
  w ++ [evalGateW w g]

private theorem stepW_map (w : List W) (g : Gate) (hg : legal g) (k : Fin 55) :
    step (w.map (bit k)) g = (stepW w g).map (bit k) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl
    · simp only [step, stepW, evalGateW, List.map_append, List.map_nil, List.map_cons,
        GateOp.eval, List.all_nil, bit, BitVec.getElem_allOnes]
    · simp [step, stepW, evalGateW, GateOp.eval, bit]
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl
      · simp only [step, stepW, evalGateW, List.map_append, List.map_cons, List.map_nil, read_bit]
        simp [GateOp.eval]
      · simp only [step, stepW, evalGateW, List.map_append, List.map_cons, List.map_nil, read_bit]
        simp [GateOp.eval]
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl
        · simp only [step, stepW, evalGateW, List.map_append, List.map_cons, List.map_nil, read_bit]
          simp [GateOp.eval, bit]
        · simp only [step, stepW, evalGateW, List.map_append, List.map_cons, List.map_nil, read_bit]
          simp [GateOp.eval, bit]

private theorem foldl_stepW_map (gs : List Gate) (hg : ∀ g ∈ gs, legal g) (w : List W) (k : Fin 55) :
    gs.foldl step (w.map (bit k)) = (gs.foldl stepW w).map (bit k) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [stepW_map w g (hg g (by simp)) k]
    exact ih (fun g' h => hg g' (by simp [h])) (stepW w g)

private theorem foldl_stepW_getD_lt (gs : List Gate) (w : List W) {i : ℕ} (hi : i < w.length) :
    (gs.foldl stepW w).getD i 0 = w.getD i 0 := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hi' : i < (stepW w g).length := by simp [stepW]; omega
    rw [ih (stepW w g) hi']
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

def gateCost (w : List W) (g : Gate) : ℕ :=
  match g.op with
  | .and => 1
  | .or => if wide (evalGateW w g) then 1 else 2
  | _ => 0

def costList (w : List W) : List Gate → ℕ
  | [] => 0
  | g :: gs => gateCost w g + costList (stepW w g) gs

def represents (available : Finset W) (w : List W) : Prop :=
  ∀ u ∈ w, u = 0 ∨ u = BitVec.allOnes 55 ∨ u ∈ available

private theorem represent_wire {av : Finset W} {w : List W} (hw : represents av w) (i : ℕ) :
    w.getD i 0 = 0 ∨ w.getD i 0 = BitVec.allOnes 55 ∨ w.getD i 0 ∈ av := by
  rcases read_wire w i with h | h
  · exact Or.inl h
  · exact hw _ h

private theorem classify_eval {av : Finset W} {w : List W} (hw : represents av w)
    {g : Gate} (hg : legal g) :
    evalGateW w g = 0 ∨ evalGateW w g = BitVec.allOnes 55 ∨ evalGateW w g ∈ av ∨
      (g.op = .and ∧ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ evalGateW w g = a &&& b) ∨
      (g.op = .or ∧ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ evalGateW w g = a ||| b) := by
  have lift {t : W} (h : t = 0 ∨ t = BitVec.allOnes 55 ∨ t ∈ av) :
      t = 0 ∨ t = BitVec.allOnes 55 ∨ t ∈ av ∨
        (g.op = .and ∧ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ t = a &&& b) ∨
        (g.op = .or ∧ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ t = a ||| b) :=
    h.imp_right (Or.imp_right Or.inl)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl <;> exact lift (represent_wire hw i)
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl
        · simp only [evalGateW]
          rcases represent_wire hw i with hi | hi | hi
          · left; rw [hi]; simp
          · rw [hi, BitVec.allOnes_and]
            rcases represent_wire hw j with hj | hj | hj
            · exact Or.inl hj
            · exact Or.inr (Or.inl hj)
            · exact Or.inr (Or.inr (Or.inl hj))
          · rcases represent_wire hw j with hj | hj | hj
            · left; rw [hj]; simp
            · rw [hj, BitVec.and_allOnes]; exact Or.inr (Or.inr (Or.inl hi))
            · by_cases heq : w.getD i 0 = w.getD j 0
              · rw [heq, BitVec.and_self]; exact Or.inr (Or.inr (Or.inl hj))
              · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨trivial, w.getD i 0, hi, w.getD j 0, hj, heq, rfl⟩)))
        · simp only [evalGateW]
          rcases represent_wire hw i with hi | hi | hi
          · rw [hi, show (0 : W) ||| w.getD j 0 = w.getD j 0 by ext k hk; simp]
            rcases represent_wire hw j with hj | hj | hj
            · exact Or.inl hj
            · exact Or.inr (Or.inl hj)
            · exact Or.inr (Or.inr (Or.inl hj))
          · right; left; rw [hi]; exact BitVec.allOnes_or
          · rcases represent_wire hw j with hj | hj | hj
            · rw [hj, show w.getD i 0 ||| (0 : W) = w.getD i 0 by ext k hk; simp]
              exact Or.inr (Or.inr (Or.inl hi))
            · right; left; rw [hj]; exact BitVec.or_allOnes
            · by_cases heq : w.getD i 0 = w.getD j 0
              · rw [heq, BitVec.or_self]; exact Or.inr (Or.inr (Or.inl hj))
              · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨trivial, w.getD i 0, hi, w.getD j 0, hj, heq, rfl⟩)))

private theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : represents av w)
    (he : (gs.foldl stepW w).getD out 0 = goal) :
    build basicOps1 basicOps2 goal (costList w gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hval : w.getD out 0 = goal := he
    have hr := read_wire w out
    rw [hval] at hr
    rcases hr with hz | hm
    · exact False.elim ((by decide : goal ≠ (0 : W)) hz)
    · rcases hw _ hm with h | h | h
      · exact False.elim ((by decide : goal ≠ (0 : W)) h)
      · exact False.elim ((by decide : goal ≠ BitVec.allOnes 55) h)
      · exact h
  | cons g gs ih =>
    have hg0 : legal g := hg g (by simp)
    have hgs : ∀ g' ∈ gs, legal g' := fun g' h => hg g' (by simp [h])
    set z := evalGateW w g
    have appendOK (h : z = 0 ∨ z = BitVec.allOnes 55 ∨ z ∈ av) : represents av (stepW w g) := by
      intro u hu
      rcases List.mem_append.mp hu with old | fresh
      · exact hw _ old
      · have eq : u = z := List.mem_singleton.mp fresh
        exact eq ▸ h
    have appendIns : represents (insert z av) (stepW w g) := by
      intro u hu
      rcases List.mem_append.mp hu with old | fresh
      · exact (hw _ old).imp_right (Or.imp_right (Finset.mem_insert_of_mem ·))
      · have eq : u = z := List.mem_singleton.mp fresh
        exact Or.inr (Or.inr (eq ▸ Finset.mem_insert_self z av))
    have he' : (gs.foldl stepW (stepW w g)).getD out 0 = goal := he
    simp only [costList]
    rcases classify_eval hw hg0 with h | h | h | ⟨hop, a, ha, b, hb, hab, hzeq⟩ | ⟨hop, a, ha, b, hb, hab, hzeq⟩
    · exact extend_build (Nat.le_add_left _ _) (ih hgs (stepW w g) av (appendOK (.inl h)) he')
    · exact extend_build (Nat.le_add_left _ _) (ih hgs (stepW w g) av (appendOK (.inr (.inl h))) he')
    · exact extend_build (Nat.le_add_left _ _) (ih hgs (stepW w g) av (appendOK (.inr (.inr h))) he')
    · by_cases hmem : z ∈ av
      · exact extend_build (Nat.le_add_left _ _) (ih hgs (stepW w g) av (appendOK (.inr (.inr hmem))) he')
      · have hc : gateCost w g = 1 := by simp [gateCost, hop]
        rw [hc, Nat.add_comm]
        have hzmem : z ∈ basicOps1 a b := by
          simp only [basicOps1, ops1List, List.mem_toFinset]
          split <;> simp [z, hzeq]
        exact build_step1 ha hb hab hzmem hmem (ih hgs (stepW w g) (insert z av) appendIns he')
    · by_cases hmem : z ∈ av
      · exact extend_build (Nat.le_add_left _ _) (ih hgs (stepW w g) av (appendOK (.inr (.inr hmem))) he')
      · by_cases hwz : wide z = true
        · have hc : gateCost w g = 1 := by simp [gateCost, hop, z, hwz]
          rw [hc, Nat.add_comm]
          have hzmem : z ∈ basicOps1 a b := by
            simp only [basicOps1, ops1List, List.mem_toFinset]
            have hwo : wide (a ||| b) = true := by simpa [z, hzeq] using hwz
            simp [hwo, z, hzeq]
          exact build_step1 ha hb hab hzmem hmem (ih hgs (stepW w g) (insert z av) appendIns he')
        · have hwz' : wide z = false := Bool.eq_false_iff.mpr hwz
          have hc : gateCost w g = 2 := by simp [gateCost, hop, z, hwz']
          rw [hc, Nat.add_comm]
          have hzmem : z ∈ basicOps2 a b := by
            simp only [basicOps2, ops2List, List.mem_toFinset]
            have hwo : wide (a ||| b) = false := by simpa [z, hzeq] using hwz'
            simp [hwo, z, hzeq]
          exact Or.inr (Or.inr ⟨a, ha, b, hb, hab, z, hzmem, hmem, ih hgs (stepW w g) (insert z av) appendIns he'⟩)

def edges : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (1, 2), (0, 3), (3, 4)]

def assignment (k : Fin 55) (i : Fin 5) : Bool := bit k (rawInputs.getD i.val 0)

theorem full_inputs {T : List (W × W × W × Bool)} {seen s : Finset W}
    (hs : s ⊆ inputs.toFinset)
    (hr : validTrace basicOps1 basicOps2 goal T seen s) : s = inputs.toFinset := by
  apply Finset.Subset.antisymm hs
  intro a ha
  let sites : List (Fin 25) := [1, 0, 5, 15, 21]
  have necessary : inputs.all (fun a => sites.any (fun i => inputs.all (fun b =>
      !(b.getLsbD (25 + i.val) && !b.getLsbD i.val) || b == a))) = true := by decide
  obtain ⟨i, _, hAll⟩ := List.any_eq_true.mp (List.all_eq_true.mp necessary a (List.mem_toFinset.mp ha))
  have hi (b : W) (hb : b ∈ inputs) (hd : differs i b) : b = a := by
    have hrow := List.all_eq_true.mp hAll b hb
    obtain ⟨h1, h2⟩ := hd
    simpa [h1, h2] using hrow
  obtain ⟨b, hb, hd⟩ := trace_separates (differs i) (goal_differs i) (ops1_differs i) (ops2_differs i) hr
  exact hi b (List.mem_toFinset.mp (hs hb)) hd ▸ hb

theorem input_rows (k : Fin 55) : List.ofFn (assignment k) = rawInputs.map (bit k) := by
  rfl

theorem graph_rows : ∀ k : Fin 55, (∃ u v : Fin 5, (u.val, v.val) ∈ edges ∧
    assignment k u = true ∧ assignment k v = true) ↔ bit k goal = true := by
  decide +kernel

theorem singleton_row (u : Fin 5) :
    assignment ⟨50 + u.val, by omega⟩ = fun i : Fin 5 => decide (i = u) := by
  funext i
  fin_cases u <;> fin_cases i <;> decide

private theorem wide5_iff : ∀ s : BitVec 5,
    ((s.toNat &&& (s.toNat - 1)) != 0) = true ↔
    ∃ u v : Fin 5, u ≠ v ∧ s[u.val] = true ∧ s[v.val] = true := by
  decide

theorem wide_iff (z : W) :
    wide z = true ↔ ∃ u v : Fin 5, u ≠ v ∧
      bit ⟨50 + u.val, by omega⟩ z = true ∧ bit ⟨50 + v.val, by omega⟩ z = true := by
  let s : BitVec 5 := (z >>> 50).setWidth 5
  have hs_toNat : s.toNat = z.toNat / 1125899906842624 := by
    have hlt : z.toNat / 1125899906842624 < 32 := by
      have hz := z.isLt
      omega
    simp only [s, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    exact Nat.mod_eq_of_lt hlt
  have hbit (u : Fin 5) : s[u.val] = bit ⟨50 + u.val, by omega⟩ z := by
    have hlt : u.val + 50 < 55 := by omega
    simp [s, bit, Nat.add_comm, BitVec.getLsbD_eq_getElem hlt]
  unfold wide
  rw [← hs_toNat, wide5_iff]
  simp only [hbit]

theorem rows_eval (C : Circuit) (hm : Monotone2 C)
    (he : ∀ x : Fin 5 → Bool, (C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 5, (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true)) :
    (C.gates.foldl stepW rawInputs).getD C.output 0 = goal := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have h1 : (C.gates.foldl step (rawInputs.map (bit ⟨i, hi⟩))).getD C.output false = bit ⟨i, hi⟩ goal := by
    rw [← input_rows]
    exact Bool.eq_iff_iff.mpr ((he (assignment ⟨i, hi⟩)).trans (graph_rows ⟨i, hi⟩))
  rw [foldl_stepW_map C.gates hm rawInputs ⟨i, hi⟩, read_bit] at h1
  exact h1

theorem wire_singleton (C : Circuit) (hm : Monotone2 C) (u : Fin 5) (j : ℕ) :
    (C.wires (List.ofFn (fun i : Fin 5 => decide (i = u)))).getD (5 + j) false =
      bit ⟨50 + u.val, by omega⟩ ((C.gates.foldl stepW rawInputs).getD (5 + j) 0) := by
  rw [← singleton_row u, input_rows]
  change (C.gates.foldl step (rawInputs.map (bit ⟨50 + u.val, by omega⟩))).getD (5 + j) false = _
  rw [foldl_stepW_map C.gates hm rawInputs ⟨50 + u.val, by omega⟩, read_bit]

private theorem costList_le_sum (A B D : Finset ℕ) (gs : List Gate) (n : ℕ) (w : List W)
    (hwlen : w.length = 5 + n) (hg : ∀ g ∈ gs, legal g)
    (hA : ∀ (j : ℕ) (g : Gate), gs[j]? = some g → g.op = .and → n + j ∈ A)
    (hB : ∀ (j : ℕ) (g : Gate), gs[j]? = some g → g.op = .or →
      wide ((gs.foldl stepW w).getD (5 + (n + j)) 0) = true → n + j ∈ B)
    (hD : ∀ (j : ℕ) (g : Gate), gs[j]? = some g → g.op = .or →
      wide ((gs.foldl stepW w).getD (5 + (n + j)) 0) = false → n + j ∈ D) :
    costList w gs ≤ ∑ j ∈ Finset.range gs.length,
      ((if n + j ∈ A then 1 else 0) + (if n + j ∈ B then 1 else 0) + 2 * (if n + j ∈ D then 1 else 0)) := by
  induction gs generalizing n w with
  | nil => simp [costList]
  | cons g gs ih =>
    simp only [costList, List.length_cons, Finset.sum_range_succ']
    have h0wire : ((g :: gs).foldl stepW w).getD (5 + (n + 0)) 0 = evalGateW w g := by
      simp only [List.foldl_cons, Nat.add_zero]
      have hlt : 5 + n < (stepW w g).length := by simp [stepW, hwlen]
      rw [foldl_stepW_getD_lt gs (stepW w g) hlt]
      simp [stepW, hwlen, List.getD_eq_getElem?_getD]
    have hhead : gateCost w g ≤
        (if n + 0 ∈ A then 1 else 0) + (if n + 0 ∈ B then 1 else 0) + 2 * (if n + 0 ∈ D then 1 else 0) := by
      have hop : g.op = .and ∨ g.op = .or := (hg g (by simp)).1
      rcases hop with hop | hop
      · have hmem : n ∈ A := by simpa using hA 0 g rfl hop
        simp [gateCost, hop, hmem]; omega
      · by_cases hw : wide (evalGateW w g) = true
        · have hmem : n ∈ B := by simpa using hB 0 g rfl hop (h0wire.symm ▸ hw)
          simp [gateCost, hop, hw, hmem]; omega
        · have hw' : wide (evalGateW w g) = false := Bool.eq_false_iff.mpr hw
          have hmem : n ∈ D := by simpa using hD 0 g rfl hop (h0wire.symm ▸ hw')
          simp [gateCost, hop, hw', hmem]
    have htail : costList (stepW w g) gs ≤ ∑ j ∈ Finset.range gs.length,
        ((if (n + 1) + j ∈ A then 1 else 0) + (if (n + 1) + j ∈ B then 1 else 0) +
          2 * (if (n + 1) + j ∈ D then 1 else 0)) := by
      apply ih (n + 1) (stepW w g) (by simp [stepW, hwlen]; omega) (fun g' h => hg g' (by simp [h]))
      · intro j g' hj hop
        have := hA (j + 1) g' (by simpa using hj) hop
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
      · intro j g' hj hop hw'
        have := hB (j + 1) g' (by simpa using hj) hop (by
          simpa [List.foldl_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw')
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
      · intro j g' hj hop hw'
        have := hD (j + 1) g' (by simpa using hj) hop (by
          simpa [List.foldl_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw')
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
    have hshift : (∑ j ∈ Finset.range gs.length,
        ((if (n + 1) + j ∈ A then 1 else 0) + (if (n + 1) + j ∈ B then 1 else 0) +
          2 * (if (n + 1) + j ∈ D then 1 else 0))) =
        (∑ j ∈ Finset.range gs.length,
        ((if n + (j + 1) ∈ A then 1 else 0) + (if n + (j + 1) ∈ B then 1 else 0) +
          2 * (if n + (j + 1) ∈ D then 1 else 0))) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    omega

private theorem sum_ite_mem_le_card (S : Finset ℕ) (m : ℕ) :
    (∑ j ∈ Finset.range m, if j ∈ S then 1 else 0) ≤ S.card := by
  rw [Finset.sum_boole]
  simpa only [Nat.cast_id] using Finset.card_le_card (fun x hx => (Finset.mem_filter.mp hx).2)

theorem cost_bound (C : Circuit) (A B D : Finset ℕ) (hm : Monotone2 C)
    (hA : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = .and → j ∈ A)
    (hB : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = .or →
      (∃ u v : Fin 5, u ≠ v ∧
        (C.wires (List.ofFn (fun i : Fin 5 => decide (i = u)))).getD (5 + j) false = true ∧
        (C.wires (List.ofFn (fun i : Fin 5 => decide (i = v)))).getD (5 + j) false = true) → j ∈ B)
    (hD : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = .or →
      ¬ (∃ u v : Fin 5, u ≠ v ∧
        (C.wires (List.ofFn (fun i : Fin 5 => decide (i = u)))).getD (5 + j) false = true ∧
        (C.wires (List.ofFn (fun i : Fin 5 => decide (i = v)))).getD (5 + j) false = true) → j ∈ D) :
    costList rawInputs C.gates ≤ A.card + B.card + 2 * D.card := by
  have hle := costList_le_sum A B D C.gates 0 rawInputs (by decide) hm
    (fun j g hj hop => by simpa using hA j g hj hop)
    (fun j g hj hop hw => by
      simp only [Nat.zero_add] at hw ⊢
      apply hB j g hj hop
      have := (wide_iff _).mp hw
      simpa only [wire_singleton C hm] using this)
    (fun j g hj hop hw => by
      simp only [Nat.zero_add] at hw ⊢
      apply hD j g hj hop
      intro hex
      have hwide : wide ((C.gates.foldl stepW rawInputs).getD (5 + j) 0) = true := by
        apply (wide_iff _).mpr
        simpa only [← wire_singleton C hm] using hex
      rw [hw] at hwide
      exact Bool.noConfusion hwide)
  have hsum : (∑ j ∈ Finset.range C.gates.length,
      ((if 0 + j ∈ A then 1 else 0) + (if 0 + j ∈ B then 1 else 0) + 2 * (if 0 + j ∈ D then 1 else 0))) ≤
      A.card + B.card + 2 * D.card := by
    simp only [Nat.zero_add, Finset.sum_add_distrib, ← Finset.mul_sum]
    have ha := sum_ite_mem_le_card A C.gates.length
    have hb := sum_ite_mem_le_card B C.gates.length
    have hd := sum_ite_mem_le_card D C.gates.length
    omega
  exact hle.trans hsum

theorem initial_rep : represents inputs.toFinset rawInputs := by
  intro u hu
  exact .inr (.inr (List.mem_toFinset.mpr hu))

theorem get_build (C : Circuit) (hm : Monotone2 C)
    (he : ∀ x : Fin 5 → Bool, (C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 5, (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true)) :
    build basicOps1 basicOps2 goal (costList rawInputs C.gates) inputs.toFinset :=
  compile C.gates C.output hm rawInputs inputs.toFinset initial_rep (rows_eval C hm he)

def check3 (x y z : W) : Bool :=
  (((x &&& y) &&& z) == goal) || (wide (x ||| y) && (((x ||| y) &&& z) == goal))

def tryStep (e : ℕ) (prevZ : W) (next : ℕ → W → List W → Bool)
    (a b : W) (r : List W) (base : BitVec 25) (w : W) : Bool :=
  if w == a || w == b || (a != prevZ && b != prevZ && Nat.blt prevZ.toNat w.toNat) then false
  else
    let v := sep w ||| base
    ((v == -1) && next e w (w :: r)) ||
    ((e != 0) && (((v ||| sep a == -1) && next (e - 1) w (w :: a :: r)) ||
                   ((v ||| sep b == -1) && next (e - 1) w (w :: b :: r)))) ||
    ((e ≥ 2) && (v ||| sep a ||| sep b == -1) && next (e - 2) w (w :: a :: b :: r))

def dispatch (extra : ℕ) (prevZ : W) (next1 next2 : ℕ → W → List W → Bool)
    (a b : W) (r : List W) : Bool :=
  let base := cuts r
  let o := a ||| b
  tryStep extra prevZ next1 a b r base (a &&& b) ||
    if wide o then tryStep extra prevZ next1 a b r base o
    else (extra != 0) && tryStep (extra - 1) prevZ next2 a b r base o

def optimized : ℕ → ℕ → W → List W → Bool
  | 0, _, _, ws => ws == [goal]
  | 1, _, _, ws => match ws with
    | [a] => a == goal
    | [a, b] => (a &&& b) == goal
    | _ => false
  | 2, _, _, ws => match ws with
    | [a] => a == goal
    | [a, b] => ((a &&& b) == goal) || ((a ||| b) == goal)
    | [a, b, c] => check3 a b c || check3 a c b || check3 b c a
    | _ => false
  | k + 3, extra, prevZ, ws => ws == [goal] ||
    (pairs ws).any (fun (a, b, r) => dispatch extra prevZ (optimized (k + 2)) (optimized (k + 1)) a b r)

theorem tryStep_complete {m e : ℕ} {prevZ a b z : W} {r kept : List W}
    (next : ℕ → W → List W → Bool)
    (hza : z ≠ a) (hzb : z ≠ b)
    (hord : a = prevZ ∨ b = prevZ ∨ z.toNat ≤ prevZ.toNat)
    (hk : kept ∈ keepChoices a b r)
    (he : e + r.length = m) (hn : kept.length ≤ m)
    (hc : cuts (z :: kept) = -1) (ht : next (m - kept.length) z (z :: kept) = true) :
    tryStep e prevZ next a b r (cuts r) z = true := by
  have hordb : (a != prevZ && b != prevZ && Nat.blt prevZ.toNat z.toNat) = false := by
    rcases hord with rfl | rfl | hle
    · simp
    · simp
    · have hblt : Nat.blt prevZ.toNat z.toNat = false :=
        Bool.eq_false_iff.mpr (fun h => by rw [Nat.blt_eq] at h; omega)
      simp [hblt]
  have hne : (z == a || z == b || (a != prevZ && b != prevZ && Nat.blt prevZ.toNat z.toNat)) = false := by
    simp [hza, hzb, hordb]
  simp only [tryStep, hne, Bool.false_eq_true, ↓reduceIte]
  simp only [keepChoices, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem dispatch_complete1 {k extra : ℕ} {prevZ a b z : W} {r kept : List W}
    (next1 next2 : ℕ → W → List W → Bool)
    (hz : z ∈ basicOps1 a b) (hza : z ≠ a) (hzb : z ≠ b)
    (hord : a = prevZ ∨ b = prevZ ∨ z.toNat ≤ prevZ.toNat)
    (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k + 2) (hn : kept.length ≤ k + 2)
    (hc : cuts (z :: kept) = -1) (ht : next1 (k + 2 - kept.length) z (z :: kept) = true) :
    dispatch extra prevZ next1 next2 a b r = true := by
  have hts := tryStep_complete (e := extra) (prevZ := prevZ) next1 hza hzb hord hk he hn hc ht
  simp only [basicOps1, ops1List, List.mem_toFinset] at hz
  simp only [dispatch, Bool.or_eq_true]
  by_cases hwo : wide (a ||| b) = true
  · simp only [hwo, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · exact Or.inl hts
    · exact Or.inr (by simp [hwo, hts])
  · have hwo' : wide (a ||| b) = false := Bool.eq_false_iff.mpr hwo
    simp only [hwo', Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at hz
    subst hz
    exact Or.inl hts

theorem dispatch_complete2 {k extra : ℕ} {prevZ a b z : W} {r kept : List W}
    (next1 next2 : ℕ → W → List W → Bool)
    (hz : z ∈ basicOps2 a b) (hza : z ≠ a) (hzb : z ≠ b)
    (hord : a = prevZ ∨ b = prevZ ∨ z.toNat ≤ prevZ.toNat)
    (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k + 2) (hn : kept.length ≤ k + 1)
    (hc : cuts (z :: kept) = -1) (ht : next2 (k + 1 - kept.length) z (z :: kept) = true) :
    dispatch extra prevZ next1 next2 a b r = true := by
  have hlen := keepChoices_len_ge hk
  have hex : extra ≠ 0 := by omega
  have hts := tryStep_complete (e := extra - 1) (prevZ := prevZ) next2 hza hzb hord hk (by omega) hn hc ht
  simp only [basicOps2, ops2List, List.mem_toFinset] at hz
  simp only [dispatch, Bool.or_eq_true]
  by_cases hwo : wide (a ||| b) = true
  · simp [hwo] at hz
  · have hwo' : wide (a ||| b) = false := Bool.eq_false_iff.mpr hwo
    simp only [hwo', Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at hz
    subst hz
    right
    simp [hwo', hex, hts]

private theorem goal_not_wide : wide goal = false := by decide

private theorem ops1_eq_goal {a b : W} (hz : goal ∈ basicOps1 a b) : a &&& b = goal := by
  simp only [basicOps1, ops1List, List.mem_toFinset] at hz
  by_cases hwo : wide (a ||| b) = true
  · simp only [hwo, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with h1 | h2
    · exact h1.symm
    · rw [← h2, goal_not_wide] at hwo
      exact Bool.noConfusion hwo
  · have hwo' : wide (a ||| b) = false := Bool.eq_false_iff.mpr hwo
    simp only [hwo', Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at hz
    exact hz.symm

private theorem step_to_goal_finset {a b z : W} {is2 : Bool} {seen s : Finset W}
    (hsub : s ⊆ seen)
    (hv : validTrace basicOps1 basicOps2 goal [(a, b, z, is2)] seen s) :
    z = goal ∧ s = {a, b} ∧ a ≠ b ∧ z ∈ (if is2 then basicOps2 a b else basicOps1 a b) := by
  obtain ⟨_, _, hab, hz, hzout, rest, hs, tail⟩ := hv
  change insert z rest = {goal} at tail
  have hzgoal : z = goal := Finset.mem_singleton.mp (tail ▸ Finset.mem_insert_self z rest)
  have hrest : rest = ∅ := by
    ext u
    simp only [Finset.notMem_empty, iff_false]
    intro hu
    have hueq : u = goal := Finset.mem_singleton.mp (tail ▸ Finset.mem_insert_of_mem hu)
    exact hzout (hsub (hs ▸ by simp [hzgoal, ← hueq, hu]))
  rw [hrest] at hs
  exact ⟨hzgoal, hs, hab, hz⟩

private theorem check3_comm (x y z : W) : check3 x y z = check3 y x z := by
  simp [check3, BitVec.and_comm, BitVec.or_comm]

private theorem check3_of_ops1 {a b c z : W} (hz : z ∈ basicOps1 a b) (hg : z &&& c = goal) :
    check3 a b c = true := by
  simp only [basicOps1, ops1List, List.mem_toFinset] at hz
  simp only [check3, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  by_cases hwo : wide (a ||| b) = true
  · simp only [hwo, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · exact Or.inl hg
    · exact Or.inr ⟨hwo, hg⟩
  · have hwo' : wide (a ||| b) = false := Bool.eq_false_iff.mpr hwo
    simp only [hwo', Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at hz
    subst hz
    exact Or.inl hg

private theorem and_and_left (x y : W) : (x &&& y) &&& x = x &&& y := by
  ext i hi; simp; cases x[i] <;> simp

private theorem and_and_right (x y : W) : (x &&& y) &&& y = x &&& y := by
  ext i hi; simp

private theorem or_and_left (x y : W) : (x ||| y) &&& x = x := by
  ext i hi; simp; cases x[i] <;> simp

private theorem or_and_right (x y : W) : (x ||| y) &&& y = y := by
  ext i hi; simp; cases y[i] <;> simp

private theorem optimized2_complete {T : List (W × W × W × Bool)} {seen : Finset W} {ws : List W}
    (hn : ws.Nodup) (hsub : ws.toFinset ⊆ seen) (hc : traceCost T ≤ 2)
    (hv : validTrace basicOps1 basicOps2 goal T seen ws.toFinset) :
    optimized 2 0 (BitVec.allOnes 55) ws = true := by
  match T with
  | [] =>
    rw [singleton_list hn hv]; simp [optimized]
  | [(a, b, z, is2)] =>
    obtain ⟨rfl, hs, hab, hz⟩ := step_to_goal_finset hsub hv
    have hcard : ws.length = 2 := by
      have hc' := List.toFinset_card_of_nodup hn
      rw [hs, Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton] at hc'
      omega
    have hdisj : a &&& b = goal ∨ a ||| b = goal := by
      cases is2 with
      | false => exact Or.inl (ops1_eq_goal hz)
      | true =>
        simp only [↓reduceIte, basicOps2, ops2List, List.mem_toFinset] at hz
        split at hz <;> simp_all
    rcases ws with _ | ⟨x, _ | ⟨y, _ | _⟩⟩ <;> simp at hcard
    have hx : x ∈ ({a, b} : Finset W) := by rw [← hs]; simp
    have hy : y ∈ ({a, b} : Finset W) := by rw [← hs]; simp
    have hxy : x ≠ y := by simp only [List.nodup_cons, List.mem_singleton] at hn; exact hn.1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    simp only [optimized, Bool.or_eq_true, beq_iff_eq]
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact False.elim (hxy rfl)
    · exact hdisj
    · rwa [BitVec.and_comm, BitVec.or_comm]
    · exact False.elim (hxy rfl)
  | [(a1, b1, z1, is2_1), (a2, b2, z2, is2_2)] =>
    have his1 : is2_1 = false := by
      cases is2_1 <;> cases is2_2 <;> simp [traceCost, stepCost] at hc ⊢
    have his2 : is2_2 = false := by
      cases is2_1 <;> cases is2_2 <;> simp [traceCost, stepCost] at hc ⊢
    subst his1; subst his2
    obtain ⟨ha1, hb1, hab1, hz1, hz1out, r1, hs1, tail⟩ := hv
    have hsub1 : insert z1 r1 ⊆ insert z1 seen :=
      Finset.insert_subset_insert z1 (fun u hu => hsub (hs1 ▸ by simp [hu]))
    obtain ⟨rfl, hs2, hab2, hz2⟩ := step_to_goal_finset hsub1 tail
    have hgoal2 : a2 &&& b2 = goal := ops1_eq_goal hz2
    have hr1sub : r1 ⊆ seen := fun u hu => hsub (hs1 ▸ by simp [hu])
    have hz1r1 : z1 ∉ r1 := fun hm => hz1out (hr1sub hm)
    have hz1mem : z1 ∈ ({a2, b2} : Finset W) := hs2 ▸ Finset.mem_insert_self z1 r1
    have hother : ∃ c, r1 = {c} ∧ z1 &&& c = goal := by
      rcases Finset.mem_insert.mp hz1mem with rfl | hmem
      · refine ⟨b2, ?_, hgoal2⟩
        ext u
        by_cases hu : u = z1
        · subst hu; simp [hz1r1, hab2]
        · have hiff : u ∈ insert z1 r1 ↔ u ∈ ({z1, b2} : Finset W) := by rw [hs2]
          simp only [Finset.mem_insert, Finset.mem_singleton, hu, false_or] at hiff ⊢
          exact hiff
      · have hzb : z1 = b2 := Finset.mem_singleton.mp hmem
        subst hzb
        refine ⟨a2, ?_, by rw [BitVec.and_comm]; exact hgoal2⟩
        ext u
        by_cases hu : u = z1
        · subst hu; simp [hz1r1, hab2.symm]
        · have hiff : u ∈ insert z1 r1 ↔ u ∈ ({a2, z1} : Finset W) := by rw [hs2]
          simp only [Finset.mem_insert, Finset.mem_singleton, hu, or_false, false_or] at hiff ⊢
          exact hiff
    obtain ⟨c, rfl, hzc⟩ := hother
    have hgoal_out : goal ∉ seen := by
      have hm := tail.2.2.2.2.1
      exact fun h => hm (Finset.mem_insert_of_mem h)
    have ha1g : a1 ≠ goal := fun e => hgoal_out (e ▸ hsub ha1)
    have hb1g : b1 ≠ goal := fun e => hgoal_out (e ▸ hsub hb1)
    by_cases hca : c = a1 ∨ c = b1
    · have hs_pair : ws.toFinset = {a1, b1} := by
        rw [hs1]
        rcases hca with rfl | rfl <;> (ext u; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
      have hab_goal : a1 &&& b1 = goal := by
        simp only [Bool.false_eq_true, ↓reduceIte, basicOps1, ops1List, List.mem_toFinset] at hz1
        have hdisj : z1 = a1 &&& b1 ∨ z1 = a1 ||| b1 := by split at hz1 <;> simp_all
        rcases hdisj with rfl | rfl
        · rcases hca with rfl | rfl
          · rw [and_and_left] at hzc; exact hzc
          · rw [and_and_right] at hzc; exact hzc
        · rcases hca with rfl | rfl
          · rw [or_and_left] at hzc; exact False.elim (ha1g hzc)
          · rw [or_and_right] at hzc; exact False.elim (hb1g hzc)
      have hcard : ws.length = 2 := by
        have hc' := List.toFinset_card_of_nodup hn
        rw [hs_pair, Finset.card_insert_of_notMem (by simp [hab1]), Finset.card_singleton] at hc'
        omega
      rcases ws with _ | ⟨x, _ | ⟨y, _ | _⟩⟩ <;> simp at hcard
      have hx : x ∈ ({a1, b1} : Finset W) := by rw [← hs_pair]; simp
      have hy : y ∈ ({a1, b1} : Finset W) := by rw [← hs_pair]; simp
      have hxy : x ≠ y := by simp only [List.nodup_cons, List.mem_singleton] at hn; exact hn.1
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      simp only [optimized, Bool.or_eq_true, beq_iff_eq]
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact False.elim (hxy rfl)
      · exact Or.inl hab_goal
      · rw [BitVec.and_comm]; exact Or.inl hab_goal
      · exact False.elim (hxy rfl)
    · push Not at hca
      obtain ⟨hca1, hcb1⟩ := hca
      have hcard : ws.length = 3 := by
        have hc' := List.toFinset_card_of_nodup hn
        rw [hs1, Finset.card_insert_of_notMem (by simp [hab1, hca1.symm]),
          Finset.card_insert_of_notMem (by simp [hcb1.symm]), Finset.card_singleton] at hc'
        omega
      have hchk : check3 a1 b1 c = true := check3_of_ops1 hz1 hzc
      rcases ws with _ | ⟨u, _ | ⟨v, _ | ⟨w, _ | _⟩⟩⟩ <;> simp at hcard
      have hnd : u ≠ v ∧ u ≠ w ∧ v ≠ w := by
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
        exact ⟨hn.1.1, hn.1.2, hn.2.1⟩
      have hu : u ∈ ({a1, b1, c} : Finset W) := by rw [← hs1]; simp
      have hv' : v ∈ ({a1, b1, c} : Finset W) := by rw [← hs1]; simp
      have hw : w ∈ ({a1, b1, c} : Finset W) := by rw [← hs1]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv' hw
      simp only [optimized, Bool.or_eq_true]
      rcases hu with rfl | rfl | rfl <;> rcases hv' with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl
      all_goals first
        | exact False.elim (hnd.1 rfl)
        | exact False.elim (hnd.2.1 rfl)
        | exact False.elim (hnd.2.2 rfl)
        | exact Or.inl (Or.inl hchk)
        | exact Or.inl (Or.inl (by rw [check3_comm]; exact hchk))
        | exact Or.inl (Or.inr hchk)
        | exact Or.inl (Or.inr (by rw [check3_comm]; exact hchk))
        | exact Or.inr hchk
        | exact Or.inr (by rw [check3_comm]; exact hchk)
  | (_, _, _, c1) :: (_, _, _, c2) :: (_, _, _, c3) :: t =>
    have h1 : 1 ≤ stepCost c1 := by cases c1 <;> simp [stepCost]
    have h2 : 1 ≤ stepCost c2 := by cases c2 <;> simp [stepCost]
    have h3 : 1 ≤ stepCost c3 := by cases c3 <;> simp [stepCost]
    simp only [traceCost] at hc
    omega

theorem optimized_complete : ∀ (n : ℕ) (ws : List W) (extra : ℕ) (prevZ : W)
    (T : List (W × W × W × Bool)) (seen : Finset W),
    ws.Nodup → ws.toFinset ⊆ seen →
    extra + ws.length = n + 1 →
    traceCost T ≤ n →
    validTrace basicOps1 basicOps2 goal T seen ws.toFinset →
    isSorted prevZ T →
    optimized n extra prevZ ws = true
  | 0, ws, _, _, T, _, hn, _, _, hcost, hv, _ => by
    cases T with
    | nil => simp [optimized, singleton_list hn hv]
    | cons e t =>
      rcases e with ⟨_, _, _, c⟩
      have hsc : 1 ≤ stepCost c := by cases c <;> simp [stepCost]
      simp only [traceCost] at hcost; omega
  | 1, ws, _, _, T, seen, hn, hsub, _, hcost, hv, _ => by
    cases T with
    | nil => rw [singleton_list hn hv]; simp [optimized]
    | cons e t =>
      cases t with
      | nil =>
        rcases e with ⟨a, b, z, is2⟩
        have his : is2 = false := by cases is2 <;> simp [traceCost, stepCost] at hcost ⊢
        subst his
        obtain ⟨rfl, hs, hab, hz⟩ := step_to_goal_finset hsub hv
        have hgoal := ops1_eq_goal hz
        have hcard : ws.length = 2 := by
          have hc' := List.toFinset_card_of_nodup hn
          rw [hs, Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton] at hc'
          omega
        rcases ws with _ | ⟨x, _ | ⟨y, _ | _⟩⟩ <;> simp at hcard
        have hx : x ∈ ({a, b} : Finset W) := by rw [← hs]; simp
        have hy : y ∈ ({a, b} : Finset W) := by rw [← hs]; simp
        have hxy : x ≠ y := by simp only [List.nodup_cons, List.mem_singleton] at hn; exact hn.1
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
        simp only [optimized, beq_iff_eq]
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · exact False.elim (hxy rfl)
        · exact hgoal
        · rw [BitVec.and_comm]; exact hgoal
        · exact False.elim (hxy rfl)
      | cons e2 t2 =>
        rcases e with ⟨_, _, _, c1⟩
        rcases e2 with ⟨_, _, _, c2⟩
        have h1 : 1 ≤ stepCost c1 := by cases c1 <;> simp [stepCost]
        have h2 : 1 ≤ stepCost c2 := by cases c2 <;> simp [stepCost]
        simp only [traceCost] at hcost; omega
  | 2, ws, _, _, T, seen, hn, hsub, _, hcost, hv, _ =>
    optimized2_complete hn hsub hcost hv
  | k + 3, ws, extra, prevZ, T, seen, hn, hsub, room, hcost, hv, hsort => by
    cases T with
    | nil => simp [optimized, singleton_list hn hv]
    | cons e t =>
      rcases e with ⟨a, b, z, is2⟩
      obtain ⟨ha, hb, hab, hz, hout, needed, hs, tail⟩ := hv
      obtain ⟨hord, hsort'⟩ := hsort
      obtain ⟨r, hmem, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      cases is2 with
      | false =>
        have hcost' : traceCost t ≤ k + 2 := by simp [traceCost, stepCost] at hcost; omega
        have go {a b : W} (ha' : a ∈ ws.toFinset) (hb' : b ∈ ws.toFinset)
            (perm : ws.Perm (a :: b :: r))
            (hset : ws.toFinset = insert a (insert b needed))
            (hop : z ∈ basicOps1 a b)
            (ho : a = prevZ ∨ b = prevZ ∨ z.toNat ≤ prevZ.toNat) :
            dispatch extra prevZ (optimized (k + 2)) (optimized (k + 1)) a b r = true := by
          obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
          have hznew : z ∉ kept := by
            intro hu
            apply hout
            apply hsub
            rw [hset]
            exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
          have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
          have hl : validTrace basicOps1 basicOps2 goal t (insert z seen) (z :: kept).toFinset := by
            simpa [hfin] using tail
          have hsub' : (z :: kept).toFinset ⊆ insert z seen := by
            simp only [List.toFinset_cons, hfin]
            exact Finset.insert_subset_insert z (fun u hu => hsub (hset ▸ by simp [hu]))
          have hc := trace_card hsub' hl
          rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
          have len := perm.length_eq
          simp only [List.length_cons] at len
          have hza : z ≠ a := fun e => hout (hsub (e ▸ ha'))
          have hzb : z ≠ b := fun e => hout (hsub (e ▸ hb'))
          apply dispatch_complete1 (k := k) (extra := extra) (prevZ := prevZ)
            (optimized (k + 2)) (optimized (k + 1)) hop hza hzb ho hk
            (by omega) (by omega) (cuts_full hl)
          apply optimized_complete (k + 2) _ _ z t (insert z seen) hnd hsub' _ hcost' hl hsort'
          simp only [List.length_cons]; omega
        simp only [optimized, Bool.or_eq_true, List.any_eq_true]
        right
        rcases hmem with direct | swap
        · exact ⟨(a, b, r), direct, go ha hb hp hs hz hord⟩
        · exact ⟨(b, a, r), swap, go hb ha (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm])
            (ops1_swap a b ▸ hz) (by rcases hord with h | h | h; exact .inr (.inl h); exact .inl h; exact .inr (.inr h))⟩
      | true =>
        have hcost' : traceCost t ≤ k + 1 := by simp [traceCost, stepCost] at hcost; omega
        have go {a b : W} (ha' : a ∈ ws.toFinset) (hb' : b ∈ ws.toFinset)
            (perm : ws.Perm (a :: b :: r))
            (hset : ws.toFinset = insert a (insert b needed))
            (hop : z ∈ basicOps2 a b)
            (ho : a = prevZ ∨ b = prevZ ∨ z.toNat ≤ prevZ.toNat) :
            dispatch extra prevZ (optimized (k + 2)) (optimized (k + 1)) a b r = true := by
          obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
          have hznew : z ∉ kept := by
            intro hu
            apply hout
            apply hsub
            rw [hset]
            exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
          have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
          have hl : validTrace basicOps1 basicOps2 goal t (insert z seen) (z :: kept).toFinset := by
            simpa [hfin] using tail
          have hsub' : (z :: kept).toFinset ⊆ insert z seen := by
            simp only [List.toFinset_cons, hfin]
            exact Finset.insert_subset_insert z (fun u hu => hsub (hset ▸ by simp [hu]))
          have hc := trace_card hsub' hl
          rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
          have len := perm.length_eq
          simp only [List.length_cons] at len
          have hza : z ≠ a := fun e => hout (hsub (e ▸ ha'))
          have hzb : z ≠ b := fun e => hout (hsub (e ▸ hb'))
          apply dispatch_complete2 (k := k) (extra := extra) (prevZ := prevZ)
            (optimized (k + 2)) (optimized (k + 1)) hop hza hzb ho hk
            (by omega) (by omega) (cuts_full hl)
          apply optimized_complete (k + 1) _ _ z t (insert z seen) hnd hsub' _ hcost' hl hsort'
          simp only [List.length_cons]; omega
        simp only [optimized, Bool.or_eq_true, List.any_eq_true]
        right
        rcases hmem with direct | swap
        · exact ⟨(a, b, r), direct, go ha hb hp hs hz hord⟩
        · exact ⟨(b, a, r), swap, go hb ha (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm])
            (ops2_swap a b ▸ hz) (by rcases hord with h | h | h; exact .inr (.inl h); exact .inl h; exact .inr (.inr h))⟩

def runTop (a b : W) (r : List W) : Bool :=
  dispatch 4 (BitVec.allOnes 55) (optimized 7) (optimized 6) a b r

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
private theorem top_01 : runTop x0 x1 [x2, x3, x4] = false := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
private theorem top_02 : runTop x0 x2 [x1, x3, x4] = false := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
private theorem top_03 : runTop x0 x3 [x1, x2, x4] = false := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
private theorem top_04_and :
    tryStep 4 (BitVec.allOnes 55) (optimized 7) x0 x4 [x1, x2, x3] (cuts [x1, x2, x3]) (x0 &&& x4) = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
private theorem top_04_or :
    tryStep 4 (BitVec.allOnes 55) (optimized 7) x0 x4 [x1, x2, x3] (cuts [x1, x2, x3]) (x0 ||| x4) = false := by
  decide +kernel

private theorem top_04 : runTop x0 x4 [x1, x2, x3] = false := by
  have hw : wide (x0 ||| x4) = true := by decide
  unfold runTop dispatch
  dsimp only
  rw [hw]
  simp only [↓reduceIte, top_04_and, top_04_or, Bool.or_self]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
private theorem top_12 : runTop x1 x2 [x0, x3, x4] = false := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
private theorem top_13 : runTop x1 x3 [x0, x2, x4] = false := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
private theorem top_14 : runTop x1 x4 [x0, x2, x3] = false := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
private theorem top_23 : runTop x2 x3 [x0, x1, x4] = false := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
private theorem top_24 : runTop x2 x4 [x0, x1, x3] = false := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
private theorem top_34 : runTop x3 x4 [x0, x1, x2] = false := by decide +kernel

private theorem pairs_inputs_eq : pairs inputs =
    [(x0, x1, [x2, x3, x4]), (x0, x2, [x1, x3, x4]), (x0, x3, [x1, x2, x4]),
     (x0, x4, [x1, x2, x3]), (x1, x2, [x0, x3, x4]), (x1, x3, [x0, x2, x4]),
     (x1, x4, [x0, x2, x3]), (x2, x3, [x0, x1, x4]), (x2, x4, [x0, x1, x3]),
     (x3, x4, [x0, x1, x2])] := rfl

private theorem runTop_eq (a b : W) (r : List W) :
    dispatch 4 (BitVec.allOnes 55) (optimized (5 + 2)) (optimized (5 + 1)) a b r = runTop a b r := rfl

theorem all_front : optimized 8 4 (BitVec.allOnes 55) inputs = false := by
  have hne : (inputs == [goal]) = false := by decide
  rw [optimized, hne, pairs_inputs_eq]
  simp only [Bool.false_or, List.any_cons, List.any_nil, runTop_eq,
    top_01, top_02, top_03, top_04, top_12, top_13, top_14, top_23, top_24, top_34]

theorem no_small (C : PEqualNP.CircuitLowerBounds.Circuit) (A B D : Finset ℕ)
    (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (he : ∀ x : Fin 5 → Bool, (C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 5, (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true))
    (hA : ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A)
    (hB : ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or →
      (∃ u v : Fin 5, u ≠ v ∧
        (C.wires (List.ofFn (fun i : Fin 5 => decide (i = u)))).getD (5 + j) false = true ∧
        (C.wires (List.ofFn (fun i : Fin 5 => decide (i = v)))).getD (5 + j) false = true) → j ∈ B)
    (hD : ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or →
      ¬ (∃ u v : Fin 5, u ≠ v ∧
        (C.wires (List.ofFn (fun i : Fin 5 => decide (i = u)))).getD (5 + j) false = true ∧
        (C.wires (List.ofFn (fun i : Fin 5 => decide (i = v)))).getD (5 + j) false = true) → j ∈ D)
    (hbd : A.card + B.card + 2 * D.card ≤ 8) : False := by
  have hcost : costList rawInputs C.gates ≤ 8 := (cost_bound C A B D hm hA hB hD).trans hbd
  obtain ⟨T, s, hsub, htc, hvalid⟩ := compress (extend_build hcost (get_build C hm he))
  have hs_eq : s = inputs.toFinset := full_inputs hsub hvalid
  subst hs_eq
  obtain ⟨T', hv', htc', hsorted⟩ := exists_sorted_trace (Finset.Subset.refl _) hvalid
  have searched := optimized_complete 8 inputs 4 (BitVec.allOnes 55) T' inputs.toFinset
    (by decide) (Finset.Subset.refl _) (by decide) (htc' ▸ htc) hv' hsorted
  exact Bool.noConfusion (all_front.symm.trans searched)

end PEqualNP.Outside.L_meta_701_aux

theorem PEqualNP.Outside.L_meta_701 :
    ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (A B D : Finset ℕ), PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 5, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (3, 4)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → (∃ u v : Fin 5, u ≠ v ∧ (C.wires (List.ofFn (fun i : Fin 5 => decide (i = u)))).getD (5 + j) false = true ∧ (C.wires (List.ofFn (fun i : Fin 5 => decide (i = v)))).getD (5 + j) false = true) → j ∈ B) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → ¬ (∃ u v : Fin 5, u ≠ v ∧ (C.wires (List.ofFn (fun i : Fin 5 => decide (i = u)))).getD (5 + j) false = true ∧ (C.wires (List.ofFn (fun i : Fin 5 => decide (i = v)))).getD (5 + j) false = true) → j ∈ D) → 9 ≤ A.card + B.card + 2 * D.card := by
  intro C A B D hm he hA hB hD
  by_contra hlt
  exact PEqualNP.Outside.L_meta_701_aux.no_small C A B D hm he hA hB hD (by omega)
