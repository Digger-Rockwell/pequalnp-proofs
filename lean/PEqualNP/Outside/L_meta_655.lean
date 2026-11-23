import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_655_aux

abbrev E10 : List (ℕ × ℕ) :=
  [(0, 4), (4, 1), (0, 5), (5, 2), (0, 6), (6, 3), (1, 7), (7, 2), (1, 8), (8, 3), (2, 9), (9, 3)]

def adj10b (u v : Fin 10) : Bool :=
  decide ((u.val, v.val) ∈ E10 ∨ (v.val, u.val) ∈ E10)

abbrev G10 : SimpleGraph (Fin 10) where
  Adj u v := adj10b u v = true
  symm := ⟨fun _ _ h => by simp only [adj10b, decide_eq_true_eq] at h ⊢; exact h.symm⟩
  loopless := ⟨fun v h => by revert v; decide⟩

lemma G10_noC4 : ∀ u v w1 w2 : Fin 10, u ≠ v → w1 ≠ w2 →
    G10.Adj u w1 → G10.Adj u w2 → G10.Adj v w1 → ¬ G10.Adj v w2 := by
  decide

lemma G10_edge04 : G10.Adj 0 4 := by decide

lemma G10_vc : ∀ K : Finset (Fin 10), (∀ u v : Fin 10, G10.Adj u v → u ∈ K ∨ v ∈ K) → 4 ≤ K.card := by
  intro K hK
  have h1 : (0 : Fin 10) ∈ K ∨ (4 : Fin 10) ∈ K := hK 0 4 (by decide)
  have h2 : (1 : Fin 10) ∈ K ∨ (7 : Fin 10) ∈ K := hK 1 7 (by decide)
  have h3 : (2 : Fin 10) ∈ K ∨ (9 : Fin 10) ∈ K := hK 2 9 (by decide)
  have h4 : (3 : Fin 10) ∈ K ∨ (6 : Fin 10) ∈ K := hK 3 6 (by decide)
  have pick : ∀ a b : Fin 10, a ∈ K ∨ b ∈ K → ∃ x ∈ K, x = a ∨ x = b := by
    intro a b hab; rcases hab with ha | hb
    · exact ⟨a, ha, Or.inl rfl⟩
    · exact ⟨b, hb, Or.inr rfl⟩
  obtain ⟨x1, hx1, h1'⟩ := pick 0 4 h1
  obtain ⟨x2, hx2, h2'⟩ := pick 1 7 h2
  obtain ⟨x3, hx3, h3'⟩ := pick 2 9 h3
  obtain ⟨x4, hx4, h4'⟩ := pick 3 6 h4
  have hsub : ({x1, x2, x3, x4} : Finset (Fin 10)) ⊆ K := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hcard : ({x1, x2, x3, x4} : Finset (Fin 10)).card = 4 := by
    rcases h1' with rfl | rfl <;> rcases h2' with rfl | rfl <;>
      rcases h3' with rfl | rfl <;> rcases h4' with rfl | rfl <;> decide
  calc 4 = ({x1, x2, x3, x4} : Finset (Fin 10)).card := hcard.symm
    _ ≤ K.card := Finset.card_le_card hsub

def LA : Finset (Fin 10) := Finset.univ.filter (fun i : Fin 10 => i.val < 4)

def LB : Finset (Fin 10) := Finset.univ.filter (fun i : Fin 10 => 4 ≤ i.val)

lemma G10_bip_A : ∀ u v : Fin 10, G10.Adj u v → (u ∈ LA ↔ v ∉ LA) := by decide

lemma G10_bip_B : ∀ u v : Fin 10, G10.Adj u v → (u ∈ LB ↔ v ∉ LB) := by decide

lemma G10_edges_A_dec : ((LA ×ˢ (Finset.univ \ LA)).filter (fun p : Fin 10 × Fin 10 => adj10b p.1 p.2 = true)).card = 12 := by
  decide

lemma G10_edges_B_dec : ((LB ×ˢ (Finset.univ \ LB)).filter (fun p : Fin 10 × Fin 10 => adj10b p.1 p.2 = true)).card = 12 := by
  decide

section ClassicalProof

open Classical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma G10_edges_A (d : DecidablePred (fun p : Fin 10 × Fin 10 => G10.Adj p.1 p.2)) :
    (@Finset.filter _ (fun p => G10.Adj p.1 p.2) d (LA ×ˢ (Finset.univ \ LA))).card = 12 := by
  rw [← G10_edges_A_dec]
  congr 1
  ext p
  simp only [Finset.mem_filter]

lemma G10_edges_B (d : DecidablePred (fun p : Fin 10 × Fin 10 => G10.Adj p.1 p.2)) :
    (@Finset.filter _ (fun p => G10.Adj p.1 p.2) d (LB ×ˢ (Finset.univ \ LB))).card = 12 := by
  rw [← G10_edges_B_dec]
  congr 1
  ext p
  simp only [Finset.mem_filter]

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_step_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_append_lt (w t : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_self (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl w.length),
    Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]

lemma getD_ge_len (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

lemma foldl_step_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (step w g).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (step w g) hlt]
    exact getD_append_lt w _ i hi

lemma foldl_step_getD_ge (gs : List Gate) (w : List Bool) (i : ℕ) (hi : w.length + gs.length ≤ i) :
    (gs.foldl step w).getD i false = false := by
  apply getD_ge_len
  rw [foldl_step_len]
  exact hi

lemma foldl_step_gate (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate) (hj : gs[j]? = some g) :
    (gs.foldl step w).getD (w.length + j) false =
      g.op.eval (g.inputs.map fun i =>
        if i < w.length + j then (gs.foldl step w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g0 gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      rw [Nat.add_zero, List.foldl_cons]
      have hlt : w.length < (step w g0).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [foldl_step_getD_lt gs (step w g0) w.length hlt]
      have hself : (step w g0).getD w.length false = g0.op.eval (g0.inputs.map fun i => w.getD i false) :=
        getD_append_self w _
      rw [hself]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · have hilt : i < (step w g0).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]
          omega
        simp only [hi, ↓reduceIte, foldl_step_getD_lt gs (step w g0) i hilt]
        exact (getD_append_lt w _ i hi).symm
      · simp only [hi, ↓reduceIte]
        exact getD_ge_len w i (Nat.le_of_not_lt hi)
    | succ j' =>
      simp only [List.getElem?_cons_succ] at hj
      have hlen : (step w g0).length + j' = w.length + (j' + 1) := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [List.foldl_cons, ← hlen]
      exact ih (step w g0) j' hj

def val (C : Circuit) (n : ℕ) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wires_eq_foldl (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

lemma ofFn_getD_lt {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (List.ofFn x).getD w false = x ⟨w, hw⟩ := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, ↓reduceDIte, Option.getD_some]

lemma val_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val C n x w = x ⟨w, hw⟩ := by
  unfold val
  rw [wires_eq_foldl, foldl_step_getD_lt C.gates (List.ofFn x) w (by simp [hw]), ofFn_getD_lt]

lemma val_oob {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    val C n x w = false := by
  unfold val
  rw [wires_eq_foldl]
  exact foldl_step_getD_ge C.gates (List.ofFn x) w (by simp [hw])

lemma val_none {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (hj : C.gates[j]? = none) :
    val C n x (n + j) = false := by
  apply val_oob
  have := List.getElem?_eq_none_iff.mp hj
  omega

lemma val_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hj : C.gates[j]? = some g) :
    val C n x (n + j) =
      g.op.eval (g.inputs.map fun i => if i < n + j then val C n x i else false) := by
  unfold val
  have h := foldl_step_gate C.gates (List.ofFn x) j g hj
  simpa only [List.length_ofFn, ← wires_eq_foldl] using h

lemma val_or {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hj : C.gates[j]? = some g) (hop : g.op = GateOp.or) :
    val C n x (n + j) = true ↔ ∃ w ∈ g.inputs, w < n + j ∧ val C n x w = true := by
  rw [val_gate C x j g hj, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
  constructor
  · rintro ⟨w, hw, hv⟩
    by_cases hlt : w < n + j
    · exact ⟨w, hw, hlt, by simpa [hlt] using hv⟩
    · simp [hlt] at hv
  · rintro ⟨w, hw, hlt, hv⟩
    exact ⟨w, hw, by simpa [hlt] using hv⟩

lemma val_and {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hj : C.gates[j]? = some g) (hop : g.op = GateOp.and) :
    val C n x (n + j) = true ↔ ∀ w ∈ g.inputs, w < n + j ∧ val C n x w = true := by
  rw [val_gate C x j g hj, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id]
  constructor
  · intro hall w hw
    have hv := hall w hw
    by_cases hlt : w < n + j
    · exact ⟨hlt, by simpa [hlt] using hv⟩
    · simp [hlt] at hv
  · intro hall w hw
    obtain ⟨hlt, hv⟩ := hall w hw
    simpa [hlt] using hv

lemma gateOp_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (f1 f2 : ℕ → Bool) (hle : ∀ i ∈ l, f1 i = true → f2 i = true) :
    op.eval (l.map f1) = true → op.eval (l.map f2) = true := by
  rcases hop with rfl | rfl
  · intro h
    change (l.map f1).all id = true at h
    change (l.map f2).all id = true
    rw [List.all_eq_true] at h ⊢
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact hle i hi (h _ (List.mem_map_of_mem hi))
  · intro h
    change (l.map f1).any id = true at h
    change (l.map f2).any id = true
    rw [List.any_eq_true] at h ⊢
    obtain ⟨b, hb, hbt⟩ := h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact ⟨f2 i, List.mem_map_of_mem hi, hle i hi hbt⟩

lemma val_mono {n : ℕ} (C : Circuit) (hmono : Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ u, x u = true → y u = true) :
    ∀ w : ℕ, val C n x w = true → val C n y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw1 : w < n
    · rw [val_input C x w hw1, val_input C y w hw1]
      exact hxy ⟨w, hw1⟩
    · by_cases hw2 : n + C.gates.length ≤ w
      · rw [val_oob C x w hw2]; intro h; cases h
      · have hjlt : w - n < C.gates.length := by omega
        set j := w - n
        have hwj : w = n + j := by omega
        have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
        have hgop : (C.gates[j]'hjlt).op = GateOp.and ∨ (C.gates[j]'hjlt).op = GateOp.or := by
          simpa using (hmono _ (List.mem_of_getElem? hg)).1
        rw [hwj, val_gate C x j _ hg, val_gate C y j _ hg]
        apply gateOp_mono _ hgop
        intro i _ hi
        by_cases hilt : i < n + j
        · simp only [hilt, ↓reduceIte] at hi ⊢
          exact ih i (by omega) hi
        · simp only [hilt, ↓reduceIte] at hi; cases hi

lemma val_take {n : ℕ} (C : Circuit) (k : ℕ) (x : Fin n → Bool) (w : ℕ) (hw : w < n + k) :
    val ⟨C.gates.take k, C.output⟩ n x w = val C n x w := by
  unfold val
  rw [wires_eq_foldl, wires_eq_foldl]
  by_cases hkl : k ≤ C.gates.length
  · conv_rhs => rw [← List.take_append_drop k C.gates, List.foldl_append]
    symm
    apply foldl_step_getD_lt
    rw [foldl_step_len, List.length_ofFn, List.length_take, Nat.min_eq_left hkl]
    exact hw
  · rw [List.take_of_length_le (by omega)]

def ValidS {n : ℕ} (L : Finset (Fin n)) (C : Circuit) (S : Set ℕ) : Prop :=
  (∀ l ∈ L, l.val ∈ S) ∧
  (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
    ∀ i ∈ g.inputs, i < n + j → i ∈ S → n + j ∈ S) ∧
  (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.and →
    ∀ a b : ℕ, g.inputs = [a, b] → a < n + j → b < n + j → ¬ (a ∈ S ∧ b ∈ S))

def y0 {n : ℕ} (L : Finset (Fin n)) : Fin n → Bool :=
  fun i => decide (i ∉ L)

noncomputable def yl {n : ℕ} (G : SimpleGraph (Fin n)) (L : Finset (Fin n)) (l : Fin n) : Fin n → Bool :=
  fun i => decide (i = l ∨ (i ∉ L ∧ ¬ G.Adj i l))

def e1 {n : ℕ} (v : Fin n) : Fin n → Bool :=
  fun i => decide (i = v)

def e2 {n : ℕ} (u v : Fin n) : Fin n → Bool :=
  fun i => decide (i = u ∨ i = v)

lemma val_indep_of_not_inS {n : ℕ} (L : Finset (Fin n)) (C : Circuit) (S : Set ℕ)
    (hS : ValidS L C S) (x y : Fin n → Bool) (hxy : ∀ r : Fin n, r ∉ L → x r = y r) :
    ∀ w : ℕ, w ∉ S → val C n x w = val C n y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwS
    by_cases hwn : w < n
    · rw [val_input C x w hwn, val_input C y w hwn]
      have hnotL : (⟨w, hwn⟩ : Fin n) ∉ L := fun hL => hwS (hS.1 ⟨w, hwn⟩ hL)
      exact hxy ⟨w, hwn⟩ hnotL
    · set j := w - n
      have hwj : w = n + j := by omega
      cases hg : C.gates[j]? with
      | none =>
        rw [hwj, val_none C x j hg, val_none C y j hg]
      | some g =>
        rw [hwj, val_gate C x j g hg, val_gate C y j g hg]
        congr 1
        apply List.map_congr_left
        intro i hi
        by_cases hilt : i < n + j
        · simp only [hilt, ↓reduceIte]
          have hiS : i ∉ S := fun h => hwS (hwj ▸ hS.2.1 j g hg i hi hilt h)
          exact ih i (by omega) hiS
        · simp only [hilt, ↓reduceIte]

lemma prefix_inv {n : ℕ} (G : SimpleGraph (Fin n)) (L : Finset (Fin n))
    (C : Circuit) (S : Set ℕ) (hmono : Monotone2 C) (hS : ValidS L C S)
    (x : Fin n → Bool) (hNoEdge : ∀ u v : Fin n, G.Adj u v → ¬ (x u = true ∧ x v = true)) :
    ∀ w : ℕ, val C n x w = true →
      (w ∉ S → val C n (y0 L) w = true ∧
        ∀ l ∈ L, x l = true → val C n (yl G L l) w = true) ∧
      ((val C n (y0 L) w = true ∧
        ∀ l ∈ L, x l = true → val C n (yl G L l) w = true) ∨
       (∃ l ∈ L, x l = true ∧ val C n (yl G L l) w = true)) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hx
    by_cases hwn : w < n
    · rw [val_input C x w hwn] at hx
      by_cases hmem : (⟨w, hwn⟩ : Fin n) ∈ L
      · have hwS : w ∈ S := hS.1 ⟨w, hwn⟩ hmem
        refine ⟨fun hnot => absurd hwS hnot, Or.inr ⟨⟨w, hwn⟩, hmem, hx, ?_⟩⟩
        rw [val_input C _ w hwn]; simp [yl]
      · have hP : val C n (y0 L) w = true ∧
            ∀ l ∈ L, x l = true → val C n (yl G L l) w = true := by
          refine ⟨by rw [val_input C _ w hwn]; simp [y0, hmem], ?_⟩
          intro l _ hxl
          rw [val_input C _ w hwn]
          have hna : ¬ G.Adj ⟨w, hwn⟩ l := fun hadj => hNoEdge ⟨w, hwn⟩ l hadj ⟨hx, hxl⟩
          simp [yl, hmem, hna]
        exact ⟨fun _ => hP, Or.inl hP⟩
    · set j := w - n
      have hwj : w = n + j := by omega
      cases hg : C.gates[j]? with
      | none =>
        rw [hwj, val_none C x j hg] at hx; cases hx
      | some g =>
        have hgM := hmono g (List.mem_of_getElem? hg)
        have hglen : g.inputs.length ≤ 2 := hgM.2
        have hgop : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using hgM.1
        rw [hwj] at hx ⊢
        rcases hgop with hand | hor
        · have hall := (val_and C x j g hg hand).mp hx
          rcases hli : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩
          · have hP : val C n (y0 L) (n + j) = true ∧
                ∀ l ∈ L, x l = true → val C n (yl G L l) (n + j) = true := by
              refine ⟨(val_and C _ j g hg hand).mpr (by rw [hli]; simp),
                fun l _ _ => (val_and C _ j g hg hand).mpr (by rw [hli]; simp)⟩
            exact ⟨fun _ => hP, Or.inl hP⟩
          · rw [hli] at hall
            obtain ⟨ha_lt, hxa⟩ := hall a (by simp)
            have ha_mem : a ∈ g.inputs := by rw [hli]; simp
            obtain ⟨ha1, ha2⟩ := ih a (by omega) hxa
            have hup : ∀ z : Fin n → Bool, val C n z a = true → val C n z (n + j) = true := by
              intro z hz
              refine (val_and C z j g hg hand).mpr ?_
              rw [hli]; intro u hu; simp at hu; subst hu; exact ⟨ha_lt, hz⟩
            refine ⟨fun hnot => ?_, ?_⟩
            · have ha_not : a ∉ S := fun haS => hnot (hS.2.1 j g hg a ha_mem ha_lt haS)
              obtain ⟨h1, h2⟩ := ha1 ha_not
              exact ⟨hup _ h1, fun l hl hxl => hup _ (h2 l hl hxl)⟩
            · rcases ha2 with ⟨h1, h2⟩ | ⟨l, hl, hxl, h3⟩
              · exact Or.inl ⟨hup _ h1, fun l hl hxl => hup _ (h2 l hl hxl)⟩
              · exact Or.inr ⟨l, hl, hxl, hup _ h3⟩
          · rw [hli] at hall
            obtain ⟨ha_lt, hxa⟩ := hall a (by simp)
            obtain ⟨hb_lt, hxb⟩ := hall b (by simp)
            have ha_mem : a ∈ g.inputs := by rw [hli]; simp
            have hb_mem : b ∈ g.inputs := by rw [hli]; simp
            obtain ⟨ha1, ha2⟩ := ih a (by omega) hxa
            obtain ⟨hb1, hb2⟩ := ih b (by omega) hxb
            have hup : ∀ z : Fin n → Bool, val C n z a = true → val C n z b = true →
                val C n z (n + j) = true := by
              intro z hza hzb
              refine (val_and C z j g hg hand).mpr ?_
              rw [hli]; intro u hu; simp at hu
              rcases hu with rfl | rfl
              · exact ⟨ha_lt, hza⟩
              · exact ⟨hb_lt, hzb⟩
            constructor
            · intro hnot
              have ha_not : a ∉ S := fun haS => hnot (hS.2.1 j g hg a ha_mem ha_lt haS)
              have hb_not : b ∉ S := fun hbS => hnot (hS.2.1 j g hg b hb_mem hb_lt hbS)
              obtain ⟨ha_y0, ha_yl⟩ := ha1 ha_not
              obtain ⟨hb_y0, hb_yl⟩ := hb1 hb_not
              exact ⟨hup _ ha_y0 hb_y0, fun l hl hxl => hup _ (ha_yl l hl hxl) (hb_yl l hl hxl)⟩
            · have hnotboth : ¬ (a ∈ S ∧ b ∈ S) := hS.2.2 j g hg hand a b hli ha_lt hb_lt
              by_cases haS : a ∈ S
              · have hb_not : b ∉ S := fun hbS => hnotboth ⟨haS, hbS⟩
                obtain ⟨hb_y0, hb_yl⟩ := hb1 hb_not
                rcases ha2 with ⟨ha_y0, ha_yl⟩ | ⟨l, hl, hxl, ha_l⟩
                · exact Or.inl ⟨hup _ ha_y0 hb_y0, fun l hl hxl => hup _ (ha_yl l hl hxl) (hb_yl l hl hxl)⟩
                · exact Or.inr ⟨l, hl, hxl, hup _ ha_l (hb_yl l hl hxl)⟩
              · obtain ⟨ha_y0, ha_yl⟩ := ha1 haS
                rcases hb2 with ⟨hb_y0, hb_yl⟩ | ⟨l, hl, hxl, hb_l⟩
                · exact Or.inl ⟨hup _ ha_y0 hb_y0, fun l hl hxl => hup _ (ha_yl l hl hxl) (hb_yl l hl hxl)⟩
                · exact Or.inr ⟨l, hl, hxl, hup _ (ha_yl l hl hxl) hb_l⟩
          · rw [hli] at hglen; simp at hglen
        · obtain ⟨u, hu_mem, hu_lt, hxu⟩ := (val_or C x j g hg hor).mp hx
          obtain ⟨hu1, hu2⟩ := ih u (by omega) hxu
          have hup : ∀ z : Fin n → Bool, val C n z u = true → val C n z (n + j) = true :=
            fun z hz => (val_or C z j g hg hor).mpr ⟨u, hu_mem, hu_lt, hz⟩
          constructor
          · intro hnot
            have hu_not : u ∉ S := fun huS => hnot (hS.2.1 j g hg u hu_mem hu_lt huS)
            obtain ⟨h1, h2⟩ := hu1 hu_not
            exact ⟨hup _ h1, fun l hl hxl => hup _ (h2 l hl hxl)⟩
          · rcases hu2 with ⟨h1, h2⟩ | ⟨l, hl, hxl, h3⟩
            · exact Or.inl ⟨hup _ h1, fun l hl hxl => hup _ (h2 l hl hxl)⟩
            · exact Or.inr ⟨l, hl, hxl, hup _ h3⟩

lemma bipartite_test_iff {n : ℕ} (G : SimpleGraph (Fin n)) (L : Finset (Fin n))
    (C : Circuit) (S : Set ℕ) (hmono : Monotone2 C) (hS : ValidS L C S)
    (hEdge : ∀ u v : Fin n, G.Adj u v → val C n (e2 u v) C.output = true)
    (hY0 : val C n (y0 L) C.output = false)
    (hYl : ∀ l ∈ L, val C n (yl G L l) C.output = false) :
    ∀ x : Fin n → Bool, val C n x C.output = true ↔
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  intro x
  constructor
  · intro hC
    by_contra hNo
    have hNoEdge : ∀ u v : Fin n, G.Adj u v → ¬ (x u = true ∧ x v = true) :=
      fun u v hadj h => hNo ⟨u, v, hadj, h.1, h.2⟩
    have hinv := prefix_inv G L C S hmono hS x hNoEdge C.output hC
    rcases hinv.2 with ⟨hy0t, _⟩ | ⟨l, hl, _, hylt⟩
    · rw [hY0] at hy0t; cases hy0t
    · rw [hYl l hl] at hylt; cases hylt
  · rintro ⟨u, v, hadj, hxu, hxv⟩
    refine val_mono C hmono (e2 u v) x ?_ C.output (hEdge u v hadj)
    intro i hi
    simp only [e2, decide_eq_true_eq] at hi
    rcases hi with rfl | rfl
    · exact hxu
    · exact hxv

def wireInS {n : ℕ} (L : Finset (Fin n)) (gs : List Gate) (w : ℕ) : Bool :=
  if hw : w < n then
    decide (⟨w, hw⟩ ∈ L)
  else
    match gs[w - n]? with
    | none => false
    | some g => g.inputs.attach.any (fun i => if _ : i.1 < w then wireInS L gs i.1 else false)
termination_by w

lemma wireInS_input {n : ℕ} (L : Finset (Fin n)) (gs : List Gate) (w : ℕ) (hw : w < n) :
    wireInS L gs w = decide (⟨w, hw⟩ ∈ L) := by
  rw [wireInS]
  simp [hw]

lemma wireInS_gate {n : ℕ} (L : Finset (Fin n)) (gs : List Gate) (j : ℕ) (g : Gate)
    (hj : gs[j]? = some g) :
    wireInS L gs (n + j) = true ↔ ∃ i ∈ g.inputs, i < n + j ∧ wireInS L gs i = true := by
  conv_lhs => rw [wireInS]
  have hnot : ¬ n + j < n := by omega
  simp only [hnot, ↓reduceDIte, Nat.add_sub_cancel_left, hj, List.any_eq_true]
  constructor
  · rintro ⟨⟨i, hi⟩, _, hv⟩
    by_cases hlt : i < n + j
    · exact ⟨i, hi, hlt, by simpa [hlt] using hv⟩
    · simp [hlt] at hv
  · rintro ⟨i, hi, hlt, hv⟩
    exact ⟨⟨i, hi⟩, List.mem_attach _ _, by simpa [hlt] using hv⟩

lemma wireInS_none {n : ℕ} (L : Finset (Fin n)) (gs : List Gate) (j : ℕ) (hj : gs[j]? = none) :
    wireInS L gs (n + j) = false := by
  rw [wireInS]
  have hnot : ¬ n + j < n := by omega
  simp [hnot, hj]

lemma wireInS_append {n : ℕ} (L : Finset (Fin n)) (gs gs' : List Gate) :
    ∀ w : ℕ, w < n + gs.length → wireInS L (gs ++ gs') w = wireInS L gs w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · rw [wireInS_input L _ w hwn, wireInS_input L _ w hwn]
    · set j := w - n
      have hwj : w = n + j := by omega
      have hj : j < gs.length := by omega
      have hg1 : (gs ++ gs')[j]? = some (gs[j]'hj) := by
        rw [List.getElem?_append_left hj, List.getElem?_eq_getElem hj]
      have hg2 : gs[j]? = some (gs[j]'hj) := List.getElem?_eq_getElem hj
      rw [hwj, Bool.eq_iff_iff, wireInS_gate L _ j _ hg1, wireInS_gate L _ j _ hg2]
      constructor
      · rintro ⟨i, hi, hlt, hv⟩
        exact ⟨i, hi, hlt, by rw [← ih i (by omega) (by omega)]; exact hv⟩
      · rintro ⟨i, hi, hlt, hv⟩
        exact ⟨i, hi, hlt, by rw [ih i (by omega) (by omega)]; exact hv⟩

lemma wireInS_subset {n : ℕ} (L : Finset (Fin n)) (C : Circuit) (S : Set ℕ)
    (hS : ValidS L C S) : ∀ w : ℕ, wireInS L C.gates w = true → w ∈ S := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · rw [wireInS_input L _ w hwn, decide_eq_true_eq] at hw
      exact hS.1 ⟨w, hwn⟩ hw
    · set j := w - n
      have hwj : w = n + j := by omega
      rw [hwj] at hw ⊢
      cases hg : C.gates[j]? with
      | none => rw [wireInS_none L _ j hg] at hw; cases hw
      | some g =>
        obtain ⟨i, hi, hlt, hwi⟩ := (wireInS_gate L _ j g hg).mp hw
        exact hS.2.1 j g hg i hi hlt (ih i (by omega) hwi)

lemma validS_wireInS {n : ℕ} (L : Finset (Fin n)) (C : Circuit) (S : Set ℕ)
    (hS : ValidS L C S) : ValidS L C { w : ℕ | wireInS L C.gates w = true } := by
  refine ⟨?_, ?_, ?_⟩
  · intro l hl
    change wireInS L C.gates l.val = true
    rw [wireInS_input L _ l.val l.isLt]
    simp [hl]
  · intro j g hg i hi hlt hiS
    change wireInS L C.gates (n + j) = true
    exact (wireInS_gate L _ j g hg).mpr ⟨i, hi, hlt, hiS⟩
  · intro j g hg hop a b hab ha hb hboth
    exact hS.2.2 j g hg hop a b hab ha hb
      ⟨wireInS_subset L C S hS a hboth.1, wireInS_subset L C S hS b hboth.2⟩

abbrev Stat := Sum Bool ℕ

def statVal (w : List Bool) : Stat → Bool
  | Sum.inl b => b
  | Sum.inr k => w.getD k false

def statValid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr k => k < m

lemma statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hk => lt_of_lt_of_le hk h

def simpMono (op : GateOp) (m : ℕ) (ins : List Stat) : Stat × Option Gate :=
  match op with
  | GateOp.and =>
    match ins with
    | [] => (Sum.inl true, none)
    | [s] => (s, none)
    | [s1, s2] =>
      match s1, s2 with
      | Sum.inl false, _ => (Sum.inl false, none)
      | _, Sum.inl false => (Sum.inl false, none)
      | Sum.inl true, s => (s, none)
      | s, Sum.inl true => (s, none)
      | Sum.inr a, Sum.inr b => (Sum.inr m, some ⟨GateOp.and, [a, b]⟩)
    | _ => (Sum.inl false, none)
  | GateOp.or =>
    match ins with
    | [] => (Sum.inl false, none)
    | [s] => (s, none)
    | [s1, s2] =>
      match s1, s2 with
      | Sum.inl true, _ => (Sum.inl true, none)
      | _, Sum.inl true => (Sum.inl true, none)
      | Sum.inl false, s => (s, none)
      | s, Sum.inl false => (s, none)
      | Sum.inr a, Sum.inr b => (Sum.inr m, some ⟨GateOp.or, [a, b]⟩)
    | _ => (Sum.inl false, none)
  | _ => (Sum.inl false, none)

lemma simpMono_ok (op : GateOp) (m : ℕ) (ins : List Stat)
    (hins : ∀ s ∈ ins, statValid m s) :
    let res := simpMono op m ins
    statValid (m + res.2.toList.length) res.1 ∧
    ∀ g, res.2 = some g → (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  cases op with
  | and =>
    rcases ins with _ | ⟨s1, _ | ⟨s2, _ | _⟩⟩
    · simp [simpMono, statValid]
    · refine ⟨by simpa [simpMono] using hins s1 (by simp), fun _ h => by simp [simpMono] at h⟩
    · cases s1 with
      | inl b1 =>
        cases b1
        · cases s2 with
          | inl b2 => cases b2 <;> simp [simpMono, statValid]
          | inr _ => simp [simpMono, statValid]
        · cases s2 with
          | inl b2 => cases b2 <;> simp [simpMono, statValid]
          | inr b => refine ⟨by simpa [simpMono] using hins (Sum.inr b) (by simp), fun _ h => by simp [simpMono] at h⟩
      | inr a =>
        cases s2 with
        | inl b2 =>
          cases b2
          · simp [simpMono, statValid]
          · refine ⟨by simpa [simpMono] using hins (Sum.inr a) (by simp), fun _ h => by simp [simpMono] at h⟩
        | inr b => simp [simpMono, statValid]
    · simp [simpMono, statValid]
  | or =>
    rcases ins with _ | ⟨s1, _ | ⟨s2, _ | _⟩⟩
    · simp [simpMono, statValid]
    · refine ⟨by simpa [simpMono] using hins s1 (by simp), fun _ h => by simp [simpMono] at h⟩
    · cases s1 with
      | inl b1 =>
        cases b1
        · cases s2 with
          | inl b2 => cases b2 <;> simp [simpMono, statValid]
          | inr b => refine ⟨by simpa [simpMono] using hins (Sum.inr b) (by simp), fun _ h => by simp [simpMono] at h⟩
        · cases s2 with
          | inl b2 => cases b2 <;> simp [simpMono, statValid]
          | inr _ => simp [simpMono, statValid]
      | inr a =>
        cases s2 with
        | inl b2 =>
          cases b2
          · refine ⟨by simpa [simpMono] using hins (Sum.inr a) (by simp), fun _ h => by simp [simpMono] at h⟩
          · simp [simpMono, statValid]
        | inr b => simp [simpMono, statValid]
    · simp [simpMono, statValid]
  | not => simp [simpMono, statValid]
  | mod _ => simp [simpMono, statValid]
  | maj => simp [simpMono, statValid]

lemma simpMono_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2) :
    let res := simpMono op w.length ins
    statVal (res.2.toList.foldl step w) res.1 = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨s1, _ | ⟨s2, _ | _⟩⟩
    · simp [simpMono, statVal, GateOp.eval]
    · simp [simpMono, statVal, GateOp.eval]
    · cases s1 with
      | inl b1 =>
        cases b1 <;> cases s2 with
          | inl b2 => cases b2 <;> simp [simpMono, statVal, GateOp.eval]
          | inr _ => simp [simpMono, statVal, GateOp.eval]
      | inr a =>
        cases s2 with
        | inl b2 => cases b2 <;> simp [simpMono, statVal, GateOp.eval]
        | inr b =>
          simp only [simpMono, Option.toList_some, List.foldl_cons, List.foldl_nil, step,
            statVal, getD_append_self, GateOp.eval, List.map_cons, List.map_nil]
    · simp at hlen
  · rcases ins with _ | ⟨s1, _ | ⟨s2, _ | _⟩⟩
    · simp [simpMono, statVal, GateOp.eval]
    · simp [simpMono, statVal, GateOp.eval]
    · cases s1 with
      | inl b1 =>
        cases b1 <;> cases s2 with
          | inl b2 => cases b2 <;> simp [simpMono, statVal, GateOp.eval]
          | inr _ => simp [simpMono, statVal, GateOp.eval]
      | inr a =>
        cases s2 with
        | inl b2 => cases b2 <;> simp [simpMono, statVal, GateOp.eval]
        | inr b =>
          simp only [simpMono, Option.toList_some, List.foldl_cons, List.foldl_nil, step,
            statVal, getD_append_self, GateOp.eval, List.map_cons, List.map_nil]
    · simp at hlen

lemma simpMono_inr (op : GateOp) (m : ℕ) (ins : List Stat) (w : ℕ)
    (h : (simpMono op m ins).1 = Sum.inr w) :
    (Sum.inr w ∈ ins ∧ (simpMono op m ins).2 = none) ∨
    (∃ a b : ℕ, ins = [Sum.inr a, Sum.inr b] ∧ w = m ∧
      (simpMono op m ins).2 = some ⟨op, [a, b]⟩ ∧ (op = GateOp.and ∨ op = GateOp.or)) := by
  cases op with
  | and =>
    rcases ins with _ | ⟨s1, _ | ⟨s2, _ | _⟩⟩
    · simp [simpMono] at h
    · dsimp only [simpMono] at h ⊢; exact Or.inl ⟨by simp [h], rfl⟩
    · cases s1 with
      | inl b1 =>
        cases b1
        · cases s2 with
          | inl b2 => cases b2 <;> simp [simpMono] at h
          | inr b => simp [simpMono] at h
        · cases s2 with
          | inl b2 => cases b2 <;> simp [simpMono] at h
          | inr b =>
            dsimp only [simpMono] at h ⊢
            cases h; exact Or.inl ⟨by simp, rfl⟩
      | inr a =>
        cases s2 with
        | inl b2 =>
          cases b2
          · simp [simpMono] at h
          · dsimp only [simpMono] at h ⊢
            cases h; exact Or.inl ⟨by simp, rfl⟩
        | inr b =>
          dsimp only [simpMono] at h ⊢
          cases h; exact Or.inr ⟨a, b, rfl, rfl, rfl, Or.inl rfl⟩
    · simp [simpMono] at h
  | or =>
    rcases ins with _ | ⟨s1, _ | ⟨s2, _ | _⟩⟩
    · simp [simpMono] at h
    · dsimp only [simpMono] at h ⊢; exact Or.inl ⟨by simp [h], rfl⟩
    · cases s1 with
      | inl b1 =>
        cases b1
        · cases s2 with
          | inl b2 => cases b2 <;> simp [simpMono] at h
          | inr b =>
            dsimp only [simpMono] at h ⊢
            cases h; exact Or.inl ⟨by simp, rfl⟩
        · cases s2 with
          | inl b2 => cases b2 <;> simp [simpMono] at h
          | inr b => simp [simpMono] at h
      | inr a =>
        cases s2 with
        | inl b2 =>
          cases b2
          · dsimp only [simpMono] at h ⊢
            cases h; exact Or.inl ⟨by simp, rfl⟩
          · simp [simpMono] at h
        | inr b =>
          dsimp only [simpMono] at h ⊢
          cases h; exact Or.inr ⟨a, b, rfl, rfl, rfl, Or.inr rfl⟩
    · simp [simpMono] at h
  | not => simp [simpMono] at h
  | mod _ => simp [simpMono] at h
  | maj => simp [simpMono] at h

lemma simpMono_some (op : GateOp) (m : ℕ) (ins : List Stat) (g : Gate)
    (h : (simpMono op m ins).2 = some g) :
    ∃ a b : ℕ, ins = [Sum.inr a, Sum.inr b] ∧ g = ⟨op, [a, b]⟩ ∧
      (op = GateOp.and ∨ op = GateOp.or) := by
  cases op with
  | and =>
    rcases ins with _ | ⟨s1, _ | ⟨s2, _ | _⟩⟩
    · simp [simpMono] at h
    · simp [simpMono] at h
    · cases s1 with
      | inl b1 => cases b1 <;> cases s2 with | inl b2 => cases b2 <;> simp [simpMono] at h | inr _ => simp [simpMono] at h
      | inr a =>
        cases s2 with
        | inl b2 => cases b2 <;> simp [simpMono] at h
        | inr b =>
          simp only [simpMono, Option.some.injEq] at h
          exact ⟨a, b, rfl, h.symm, Or.inl rfl⟩
    · simp [simpMono] at h
  | or =>
    rcases ins with _ | ⟨s1, _ | ⟨s2, _ | _⟩⟩
    · simp [simpMono] at h
    · simp [simpMono] at h
    · cases s1 with
      | inl b1 => cases b1 <;> cases s2 with | inl b2 => cases b2 <;> simp [simpMono] at h | inr _ => simp [simpMono] at h
      | inr a =>
        cases s2 with
        | inl b2 => cases b2 <;> simp [simpMono] at h
        | inr b =>
          simp only [simpMono, Option.some.injEq] at h
          exact ⟨a, b, rfl, h.symm, Or.inr rfl⟩
    · simp [simpMono] at h
  | not => simp [simpMono] at h
  | mod _ => simp [simpMono] at h
  | maj => simp [simpMono] at h

def elimPass (n j0 : ℕ) (repl : List Stat → Stat) (gs : List Gate) : List Stat × List Gate :=
  (gs.zipIdx).foldl (fun acc p =>
    let tbl := acc.1
    let outG := acc.2
    if p.2 = j0 then
      (tbl ++ [repl tbl], outG)
    else
      let ins := p.1.inputs.map (fun i => if i < n + p.2 then tbl.getD i (Sum.inl false) else Sum.inl false)
      let res := simpMono p.1.op (n + outG.length) ins
      (tbl ++ [res.1], outG ++ res.2.toList))
    (List.ofFn (fun i : Fin n => (Sum.inr i.val : Stat)), [])

lemma elim_step_struct {n : ℕ} (L : Finset (Fin n)) (j0 : ℕ) (repl : List Stat → Stat)
    (C : Circuit) (S : Set ℕ) (_hmono : Monotone2 C) (hS : ValidS L C S)
    (hj0 : j0 < C.gates.length)
    (hrepl_valid : ∀ tbl : List Stat, tbl.length = n + j0 →
      (∀ i < n + j0, statValid (n + (elimPass n j0 repl (C.gates.take j0)).2.length) (tbl.getD i (Sum.inl false))) →
      statValid (n + (elimPass n j0 repl (C.gates.take j0)).2.length) (repl tbl))
    (hrepl_S : ∀ tbl : List Stat, tbl.length = n + j0 →
      (∀ i < n + j0, ∀ m, tbl.getD i (Sum.inl false) = Sum.inr m →
        wireInS L (elimPass n j0 repl (C.gates.take j0)).2 m = true → i ∈ S) →
      ∀ m, repl tbl = Sum.inr m →
        wireInS L (elimPass n j0 repl (C.gates.take j0)).2 m = true → n + j0 ∈ S) :
    let res := elimPass n j0 repl C.gates
    res.1.length = n + C.gates.length ∧
    res.2.length < C.gates.length ∧
    (∀ g ∈ res.2, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
    (∀ i < n + C.gates.length, statValid (n + res.2.length) (res.1.getD i (Sum.inl false))) ∧
    (∀ (j : ℕ) (g : Gate), res.2[j]? = some g → g.op = GateOp.and →
      ∀ a b : ℕ, g.inputs = [a, b] → a < n + j → b < n + j →
      ¬ (wireInS L res.2 a = true ∧ wireInS L res.2 b = true)) := by
  have hpref : ∀ k ≤ C.gates.length,
      let res := elimPass n j0 repl (C.gates.take k)
      res.1.length = n + k ∧
      res.2.length ≤ (if j0 < k then k - 1 else k) ∧
      (∀ g ∈ res.2, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      (∀ i < n + k, statValid (n + res.2.length) (res.1.getD i (Sum.inl false))) ∧
      (∀ i < n + k, ∀ m, res.1.getD i (Sum.inl false) = Sum.inr m →
        wireInS L res.2 m = true → i ∈ S) ∧
      (∀ (j : ℕ) (g : Gate), res.2[j]? = some g → g.op = GateOp.and →
        ∀ a b : ℕ, g.inputs = [a, b] → a < n + j → b < n + j →
        ¬ (wireInS L res.2 a = true ∧ wireInS L res.2 b = true)) := by
    intro k hk
    induction k with
    | zero =>
      simp only [List.take_zero, elimPass, List.zipIdx_nil, List.foldl_nil, List.length_ofFn,
        Nat.add_zero, List.length_nil, Nat.not_lt_zero, ↓reduceIte, le_refl, List.not_mem_nil,
        IsEmpty.forall_iff, imp_true_iff, true_and]
      refine ⟨?_, ?_, ?_⟩
      · intro i hi
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte,
          Option.getD_some, statValid]
      · intro i hi m hm hwm
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte,
          Option.getD_some, Sum.inr.injEq] at hm
        subst hm
        rw [wireInS_input L [] i hi, decide_eq_true_eq] at hwm
        exact hS.1 ⟨i, hi⟩ hwm
      · intro j g hg; simp at hg
    | succ k ih =>
      obtain ⟨hlen, hsz, hgm, hval, hSinv, hSand⟩ := ih (by omega)
      have hklt : k < C.gates.length := by omega
      have htake : C.gates.take (k + 1) = C.gates.take k ++ [C.gates[k]'hklt] :=
        List.take_succ_eq_append_getElem hklt
      have hzip : (C.gates.take (k + 1)).zipIdx = (C.gates.take k).zipIdx ++ [(C.gates[k]'hklt, k)] := by
        rw [htake, List.zipIdx_append]
        simp [List.length_take, Nat.min_eq_left (by omega : k ≤ C.gates.length)]
      set prev := elimPass n j0 repl (C.gates.take k)
      have hstep : elimPass n j0 repl (C.gates.take (k + 1)) =
          if k = j0 then
            (prev.1 ++ [repl prev.1], prev.2)
          else
            let ins := (C.gates[k]'hklt).inputs.map (fun i => if i < n + k then prev.1.getD i (Sum.inl false) else Sum.inl false)
            let res := simpMono (C.gates[k]'hklt).op (n + prev.2.length) ins
            (prev.1 ++ [res.1], prev.2 ++ res.2.toList) := by
        show ((C.gates.take (k + 1)).zipIdx).foldl _ _ = _
        rw [hzip, List.foldl_append, List.foldl_cons, List.foldl_nil]
        rfl
      rw [hstep]
      by_cases hkj : k = j0
      · subst hkj
        simp only [↓reduceIte, lt_irrefl, Nat.lt_succ_self] at hsz ⊢
        refine ⟨by simp [hlen]; omega, by omega, hgm, ?_, ?_, hSand⟩
        · intro i hi
          by_cases hik : i < n + k
          · have hget : (prev.1 ++ [repl prev.1]).getD i (Sum.inl false) = prev.1.getD i (Sum.inl false) := by
              simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < prev.1.length)]
            rw [hget]; exact hval i hik
          · have heq : i = n + k := by omega
            subst heq
            have hget : (prev.1 ++ [repl prev.1]).getD (n + k) (Sum.inl false) = repl prev.1 := by
              rw [← hlen]; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            rw [hget]; exact hrepl_valid prev.1 hlen hval
        · intro i hi m hm hwm
          by_cases hik : i < n + k
          · have hget : (prev.1 ++ [repl prev.1]).getD i (Sum.inl false) = prev.1.getD i (Sum.inl false) := by
              simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < prev.1.length)]
            rw [hget] at hm; exact hSinv i hik m hm hwm
          · have heq : i = n + k := by omega
            subst heq
            have hget : (prev.1 ++ [repl prev.1]).getD (n + k) (Sum.inl false) = repl prev.1 := by
              rw [← hlen]; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            rw [hget] at hm; exact hrepl_S prev.1 hlen hSinv m hm hwm
      · simp only [hkj, ↓reduceIte]
        set g := C.gates[k]'hklt
        set ins := g.inputs.map (fun i => if i < n + k then prev.1.getD i (Sum.inl false) else Sum.inl false)
        set sm := simpMono g.op (n + prev.2.length) ins
        have hgetk : C.gates[k]? = some g := List.getElem?_eq_getElem hklt
        have hsm_ok := simpMono_ok g.op (n + prev.2.length) ins (fun s hs => by
          obtain ⟨i, _, rfl⟩ := List.mem_map.mp hs
          by_cases hi : i < n + k
          · simp only [hi, ↓reduceIte]; exact hval i hi
          · simp only [hi, ↓reduceIte, statValid])
        have htolen : sm.2.toList.length ≤ 1 := by cases sm.2 <;> simp
        refine ⟨by simp [hlen]; omega, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [List.length_append]
          split_ifs at hsz ⊢ <;> omega
        · intro g' hg'
          rcases List.mem_append.mp hg' with hm | hm
          · exact hgm g' hm
          · cases h2 : sm.2 with
            | none => rw [h2] at hm; simp at hm
            | some g0 =>
              rw [h2] at hm; simp only [Option.toList_some, List.mem_singleton] at hm
              subst hm; exact hsm_ok.2 g' h2
        · intro i hi
          simp only [List.length_append]
          by_cases hik : i < n + k
          · have hget : (prev.1 ++ [sm.1]).getD i (Sum.inl false) = prev.1.getD i (Sum.inl false) := by
              simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < prev.1.length)]
            rw [hget]; exact statValid_mono (by omega) _ (hval i hik)
          · have heq : i = n + k := by omega
            subst heq
            have hget : (prev.1 ++ [sm.1]).getD (n + k) (Sum.inl false) = sm.1 := by
              rw [← hlen]; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            rw [hget, ← Nat.add_assoc]; exact hsm_ok.1
        · intro i hi m hm hwm
          by_cases hik : i < n + k
          · have hget : (prev.1 ++ [sm.1]).getD i (Sum.inl false) = prev.1.getD i (Sum.inl false) := by
              simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < prev.1.length)]
            rw [hget] at hm
            have hm_lt : m < n + prev.2.length := by have := hval i hik; rw [hm] at this; exact this
            rw [wireInS_append L prev.2 sm.2.toList m hm_lt] at hwm
            exact hSinv i hik m hm hwm
          · have heq : i = n + k := by omega
            subst heq
            have hget : (prev.1 ++ [sm.1]).getD (n + k) (Sum.inl false) = sm.1 := by
              rw [← hlen]; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            rw [hget] at hm
            rcases simpMono_inr g.op (n + prev.2.length) ins m hm with ⟨hmem, hnone⟩ | ⟨a', b', hins, rfl, hsome, _⟩
            · obtain ⟨u, hu, huf⟩ := List.mem_map.mp hmem
              by_cases hult : u < n + k
              · simp only [hult, ↓reduceIte] at huf
                rw [hnone] at hwm
                simp only [Option.toList_none, List.append_nil] at hwm
                exact hS.2.1 k g hgetk u hu hult (hSinv u hult m huf hwm)
              · simp [hult] at huf
            · rw [hsome] at hwm
              simp only [Option.toList_some] at hwm
              have hgnew : (prev.2 ++ [⟨g.op, [a', b']⟩])[prev.2.length]? = some ⟨g.op, [a', b']⟩ := by
                simp
              obtain ⟨w, hwmem, _, hww⟩ := (wireInS_gate L _ prev.2.length _ hgnew).mp hwm
              rcases hli : g.inputs with _ | ⟨u, _ | ⟨v, _ | _⟩⟩
              · simp [ins, hli] at hins
              · simp [ins, hli] at hins
              · simp only [ins, hli, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hins
                obtain ⟨hu1, hv1⟩ := hins
                have hult : u < n + k := by by_contra h; simp [h] at hu1
                have hvlt : v < n + k := by by_contra h; simp [h] at hv1
                simp only [hult, ↓reduceIte] at hu1
                simp only [hvlt, ↓reduceIte] at hv1
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hwmem
                rcases hwmem with hw1 | hw2
                · subst hw1
                  have ha_lt : w < n + prev.2.length := by have := hval u hult; rw [hu1] at this; exact this
                  rw [wireInS_append L prev.2 _ w ha_lt] at hww
                  exact hS.2.1 k g hgetk u (by rw [hli]; simp) hult (hSinv u hult w hu1 hww)
                · subst hw2
                  have hb_lt : w < n + prev.2.length := by have := hval v hvlt; rw [hv1] at this; exact this
                  rw [wireInS_append L prev.2 _ w hb_lt] at hww
                  exact hS.2.1 k g hgetk v (by rw [hli]; simp) hvlt (hSinv v hvlt w hv1 hww)
              · simp [ins, hli] at hins
        · intro j g' hjg' hop' a' b' hab' ha' hb' hboth
          by_cases hjlt : j < prev.2.length
          · rw [List.getElem?_append_left hjlt] at hjg'
            rw [wireInS_append L prev.2 sm.2.toList a' (by omega),
              wireInS_append L prev.2 sm.2.toList b' (by omega)] at hboth
            exact hSand j g' hjg' hop' a' b' hab' ha' hb' hboth
          · rw [List.getElem?_append_right (by omega)] at hjg'
            cases h2 : sm.2 with
            | none => rw [h2] at hjg'; simp at hjg'
            | some g0 =>
              rw [h2] at hjg'
              have hj0eq : j = prev.2.length := by
                rcases hdiff : j - prev.2.length with _ | d
                · omega
                · rw [hdiff] at hjg'; simp at hjg'
              subst hj0eq
              simp only [Nat.sub_self, Option.toList_some, List.getElem?_cons_zero, Option.some.injEq] at hjg'
              subst hjg'
              rw [wireInS_append L prev.2 _ a' ha', wireInS_append L prev.2 _ b' hb'] at hboth
              obtain ⟨a0, b0, hins, hg0eq, _⟩ := simpMono_some g.op (n + prev.2.length) ins g0 h2
              rw [hg0eq] at hop' hab'
              simp only [List.cons.injEq, and_true] at hab'
              obtain ⟨rfl, rfl⟩ := hab'
              rcases hli : g.inputs with _ | ⟨u, _ | ⟨v, _ | _⟩⟩
              · simp [ins, hli] at hins
              · simp [ins, hli] at hins
              · simp only [ins, hli, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hins
                obtain ⟨hu1, hv1⟩ := hins
                have hult : u < n + k := by by_contra h; simp [h] at hu1
                have hvlt : v < n + k := by by_contra h; simp [h] at hv1
                simp only [hult, ↓reduceIte] at hu1
                simp only [hvlt, ↓reduceIte] at hv1
                exact hS.2.2 k g hgetk hop' u v hli hult hvlt
                  ⟨hSinv u hult a0 hu1 hboth.1, hSinv v hvlt b0 hv1 hboth.2⟩
              · simp [ins, hli] at hins
  have hfull := hpref C.gates.length (le_refl _)
  rw [List.take_length] at hfull
  simp only [hj0, ↓reduceIte] at hfull
  exact ⟨hfull.1, by omega, hfull.2.2.1, hfull.2.2.2.1, hfull.2.2.2.2.2⟩

lemma elim_step_core {n : ℕ} (L : Finset (Fin n)) (j0 : ℕ) (repl : List Stat → Stat)
    (C : Circuit) (S : Set ℕ) (hmono : Monotone2 C) (hS : ValidS L C S)
    (hj0 : j0 < C.gates.length) (skip : Bool)
    (hrepl_valid : ∀ tbl : List Stat, tbl.length = n + j0 →
      (∀ i < n + j0, statValid (n + (elimPass n j0 repl (C.gates.take j0)).2.length) (tbl.getD i (Sum.inl false))) →
      statValid (n + (elimPass n j0 repl (C.gates.take j0)).2.length) (repl tbl))
    (hrepl_S : ∀ tbl : List Stat, tbl.length = n + j0 →
      (∀ i < n + j0, ∀ m, tbl.getD i (Sum.inl false) = Sum.inr m →
        wireInS L (elimPass n j0 repl (C.gates.take j0)).2 m = true → i ∈ S) →
      ∀ m, repl tbl = Sum.inr m →
        wireInS L (elimPass n j0 repl (C.gates.take j0)).2 m = true → n + j0 ∈ S)
    (hrepl_val : skip = false → ∀ (x : Fin n → Bool) (tbl : List Stat) (w' : List Bool),
      tbl.length = n + j0 →
      (∀ i < n + j0, statVal w' (tbl.getD i (Sum.inl false)) = val C n x i) →
      statVal w' (repl tbl) = val C n x (n + j0))
    (hunused : skip = true → ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → j0 < j → n + j0 ∉ g.inputs) :
    let res := elimPass n j0 repl C.gates
    res.1.length = n + C.gates.length ∧
    res.2.length < C.gates.length ∧
    (∀ g ∈ res.2, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
    (∀ i < n + C.gates.length, statValid (n + res.2.length) (res.1.getD i (Sum.inl false))) ∧
    (∀ (j : ℕ) (g : Gate), res.2[j]? = some g → g.op = GateOp.and →
      ∀ a b : ℕ, g.inputs = [a, b] → a < n + j → b < n + j →
      ¬ (wireInS L res.2 a = true ∧ wireInS L res.2 b = true)) ∧
    (∀ (x : Fin n → Bool) (i : ℕ), i < n + C.gates.length → (skip = true → i ≠ n + j0) →
      statVal (res.2.foldl step (List.ofFn x)) (res.1.getD i (Sum.inl false)) = val C n x i) := by
  have hst := elim_step_struct L j0 repl C S hmono hS hj0 hrepl_valid hrepl_S
  have hpref : ∀ k ≤ C.gates.length,
      let res := elimPass n j0 repl (C.gates.take k)
      res.1.length = n + k ∧
      (∀ i < n + k, statValid (n + res.2.length) (res.1.getD i (Sum.inl false))) ∧
      (∀ (x : Fin n → Bool) (i : ℕ), i < n + k → (skip = true → i ≠ n + j0) →
        statVal (res.2.foldl step (List.ofFn x)) (res.1.getD i (Sum.inl false)) = val C n x i) := by
    intro k hk
    induction k with
    | zero =>
      simp only [List.take_zero, elimPass, List.zipIdx_nil, List.foldl_nil, List.length_ofFn,
        Nat.add_zero, List.length_nil, true_and]
      refine ⟨?_, ?_⟩
      · intro i hi
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte,
          Option.getD_some, statValid]
      · intro x i hi _
        have hget : (List.ofFn (fun i : Fin n => (Sum.inr i.val : Stat))).getD i (Sum.inl false) = Sum.inr i := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some]
        rw [hget]
        simp only [statVal, val_input C x i hi, ofFn_getD_lt x i hi]
    | succ k ih =>
      obtain ⟨hlen, hval, hsnd⟩ := ih (by omega)
      have hklt : k < C.gates.length := by omega
      have htake : C.gates.take (k + 1) = C.gates.take k ++ [C.gates[k]'hklt] :=
        List.take_succ_eq_append_getElem hklt
      have hzip : (C.gates.take (k + 1)).zipIdx = (C.gates.take k).zipIdx ++ [(C.gates[k]'hklt, k)] := by
        rw [htake, List.zipIdx_append]
        simp [List.length_take, Nat.min_eq_left (by omega : k ≤ C.gates.length)]
      set prev := elimPass n j0 repl (C.gates.take k)
      have hstep : elimPass n j0 repl (C.gates.take (k + 1)) =
          if k = j0 then
            (prev.1 ++ [repl prev.1], prev.2)
          else
            let ins := (C.gates[k]'hklt).inputs.map (fun i => if i < n + k then prev.1.getD i (Sum.inl false) else Sum.inl false)
            let res := simpMono (C.gates[k]'hklt).op (n + prev.2.length) ins
            (prev.1 ++ [res.1], prev.2 ++ res.2.toList) := by
        show ((C.gates.take (k + 1)).zipIdx).foldl _ _ = _
        rw [hzip, List.foldl_append, List.foldl_cons, List.foldl_nil]
        rfl
      rw [hstep]
      by_cases hkj : k = j0
      · subst hkj
        simp only [↓reduceIte]
        refine ⟨by simp [hlen]; omega, ?_, ?_⟩
        · intro i hi
          by_cases hik : i < n + k
          · have hget : (prev.1 ++ [repl prev.1]).getD i (Sum.inl false) = prev.1.getD i (Sum.inl false) := by
              simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < prev.1.length)]
            rw [hget]; exact hval i hik
          · have heq : i = n + k := by omega
            subst heq
            have hget : (prev.1 ++ [repl prev.1]).getD (n + k) (Sum.inl false) = repl prev.1 := by
              rw [← hlen]; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            rw [hget]; exact hrepl_valid prev.1 hlen hval
        · intro x i hi hsk
          by_cases hik : i < n + k
          · have hget : (prev.1 ++ [repl prev.1]).getD i (Sum.inl false) = prev.1.getD i (Sum.inl false) := by
              simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < prev.1.length)]
            rw [hget]; exact hsnd x i hik hsk
          · have heq : i = n + k := by omega
            subst heq
            have hskf : skip = false := by
              cases h : skip with
              | false => rfl
              | true => exact absurd rfl (hsk h)
            have hget : (prev.1 ++ [repl prev.1]).getD (n + k) (Sum.inl false) = repl prev.1 := by
              rw [← hlen]; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            rw [hget]
            exact hrepl_val hskf x prev.1 (prev.2.foldl step (List.ofFn x)) hlen
              (fun i hi => hsnd x i hi (by intro h; rw [hskf] at h; cases h))
      · simp only [hkj, ↓reduceIte]
        set g := C.gates[k]'hklt
        set ins := g.inputs.map (fun i => if i < n + k then prev.1.getD i (Sum.inl false) else Sum.inl false)
        set sm := simpMono g.op (n + prev.2.length) ins
        have hgetk : C.gates[k]? = some g := List.getElem?_eq_getElem hklt
        have hgmem : g ∈ C.gates := List.getElem_mem hklt
        have hgop : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using (hmono g hgmem).1
        have hglen : g.inputs.length ≤ 2 := (hmono g hgmem).2
        have hsm_ok := simpMono_ok g.op (n + prev.2.length) ins (fun s hs => by
          obtain ⟨i, _, rfl⟩ := List.mem_map.mp hs
          by_cases hi : i < n + k
          · simp only [hi, ↓reduceIte]; exact hval i hi
          · simp only [hi, ↓reduceIte, statValid])
        refine ⟨by simp [hlen]; omega, ?_, ?_⟩
        · intro i hi
          simp only [List.length_append]
          by_cases hik : i < n + k
          · have hget : (prev.1 ++ [sm.1]).getD i (Sum.inl false) = prev.1.getD i (Sum.inl false) := by
              simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < prev.1.length)]
            rw [hget]; exact statValid_mono (by omega) _ (hval i hik)
          · have heq : i = n + k := by omega
            subst heq
            have hget : (prev.1 ++ [sm.1]).getD (n + k) (Sum.inl false) = sm.1 := by
              rw [← hlen]; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            rw [hget, ← Nat.add_assoc]; exact hsm_ok.1
        · intro x i hi hsk
          rw [List.foldl_append]
          have hprevlen : (prev.2.foldl step (List.ofFn x)).length = n + prev.2.length := by
            rw [foldl_step_len, List.length_ofFn]
          by_cases hik : i < n + k
          · have hget : (prev.1 ++ [sm.1]).getD i (Sum.inl false) = prev.1.getD i (Sum.inl false) := by
              simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < prev.1.length)]
            rw [hget]
            have hkeep : statVal (sm.2.toList.foldl step (prev.2.foldl step (List.ofFn x))) (prev.1.getD i (Sum.inl false)) =
                statVal (prev.2.foldl step (List.ofFn x)) (prev.1.getD i (Sum.inl false)) := by
              have hvi := hval i hik
              cases hs : prev.1.getD i (Sum.inl false) with
              | inl b => rfl
              | inr m =>
                rw [hs] at hvi
                exact foldl_step_getD_lt sm.2.toList _ m (by rw [hprevlen]; exact hvi)
            rw [hkeep]; exact hsnd x i hik hsk
          · have heq : i = n + k := by omega
            subst heq
            have hget : (prev.1 ++ [sm.1]).getD (n + k) (Sum.inl false) = sm.1 := by
              rw [← hlen]; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            rw [hget]
            have hglen' : ins.length ≤ 2 := by simp only [ins, List.length_map]; exact hglen
            have hsms := simpMono_sound g.op hgop (prev.2.foldl step (List.ofFn x)) ins hglen'
            rw [hprevlen] at hsms
            change statVal (sm.2.toList.foldl step (prev.2.foldl step (List.ofFn x))) sm.1 = _
            rw [hsms, val_gate C x k g hgetk]
            congr 1
            simp only [ins, List.map_map]
            apply List.map_congr_left
            intro u hu
            simp only [Function.comp_apply]
            by_cases hu_lt : u < n + k
            · simp only [hu_lt, ↓reduceIte]
              apply hsnd x u hu_lt
              intro hskt hequ
              subst hequ
              exact hunused hskt k g hgetk (by omega) hu
            · simp only [hu_lt, ↓reduceIte, statVal]
  have hfull := hpref C.gates.length (le_refl _)
  rw [List.take_length] at hfull
  exact ⟨hst.1, hst.2.1, hst.2.2.1, hst.2.2.2.1, hst.2.2.2.2, hfull.2.2⟩

lemma elim_smaller {n : ℕ} (G : SimpleGraph (Fin n)) (L : Finset (Fin n))
    (C : Circuit) (S : Set ℕ) (hmono : Monotone2 C) (hS : ValidS L C S)
    (hedge : ∃ u v : Fin n, G.Adj u v)
    (hfun : ∀ x : Fin n → Bool, val C n x C.output = true ↔
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)
    (j0 : ℕ) (hj0 : j0 < C.gates.length)
    (repl : List Stat → Stat) (skip : Bool)
    (hrepl_valid : ∀ tbl : List Stat, tbl.length = n + j0 →
      (∀ i < n + j0, statValid (n + (elimPass n j0 repl (C.gates.take j0)).2.length) (tbl.getD i (Sum.inl false))) →
      statValid (n + (elimPass n j0 repl (C.gates.take j0)).2.length) (repl tbl))
    (hrepl_S : ∀ tbl : List Stat, tbl.length = n + j0 →
      (∀ i < n + j0, ∀ m, tbl.getD i (Sum.inl false) = Sum.inr m →
        wireInS L (elimPass n j0 repl (C.gates.take j0)).2 m = true → i ∈ S) →
      ∀ m, repl tbl = Sum.inr m →
        wireInS L (elimPass n j0 repl (C.gates.take j0)).2 m = true → n + j0 ∈ S)
    (hrepl_val : skip = false → ∀ (x : Fin n → Bool) (tbl : List Stat) (w' : List Bool),
      tbl.length = n + j0 →
      (∀ i < n + j0, statVal w' (tbl.getD i (Sum.inl false)) = val C n x i) →
      statVal w' (repl tbl) = val C n x (n + j0))
    (hunused : skip = true → (C.output ≠ n + j0 ∧ ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → j0 < j → n + j0 ∉ g.inputs)) :
    ∃ C' : Circuit, Monotone2 C' ∧ C'.size < C.size ∧
      (∃ S' : Set ℕ, ValidS L C' S') ∧
      ∀ x : Fin n → Bool, val C' n x C'.output = val C n x C.output := by
  have hcore := elim_step_core L j0 repl C S hmono hS hj0 skip hrepl_valid hrepl_S hrepl_val (fun h => (hunused h).2)
  set res := elimPass n j0 repl C.gates
  obtain ⟨u0, v0, huv0⟩ := hedge
  have hout_lt : C.output < n + C.gates.length := by
    by_contra hge
    have ht : val C n (e2 u0 v0) C.output = true := (hfun _).mpr ⟨u0, v0, huv0, by simp [e2], by simp [e2]⟩
    rw [val_oob C _ C.output (by omega)] at ht; cases ht
  have hzero : val C n (fun _ => false) C.output = false := by
    cases h : val C n (fun _ => false) C.output with
    | false => rfl
    | true => obtain ⟨_, _, _, hu, _⟩ := (hfun _).mp h; cases hu
  have hout_ne : skip = true → C.output ≠ n + j0 := fun h => (hunused h).1
  cases hout : res.1.getD C.output (Sum.inl false) with
  | inl b =>
    cases b
    · have ht := hcore.2.2.2.2.2 (e2 u0 v0) C.output hout_lt hout_ne
      rw [hout] at ht
      have ht2 : val C n (e2 u0 v0) C.output = true := (hfun _).mpr ⟨u0, v0, huv0, by simp [e2], by simp [e2]⟩
      rw [ht2] at ht; cases ht
    · have ht := hcore.2.2.2.2.2 (fun _ => false) C.output hout_lt hout_ne
      rw [hout] at ht
      rw [hzero] at ht; cases ht
  | inr wout =>
    refine ⟨⟨res.2, wout⟩, ?_, hcore.2.1, ⟨{ w | wireInS L res.2 w = true }, ?_⟩, ?_⟩
    · intro g hg; have := hcore.2.2.1 g hg; exact ⟨by simpa using this.1, this.2⟩
    · refine ⟨?_, ?_, hcore.2.2.2.2.1⟩
      · intro l hl
        change wireInS L res.2 l.val = true
        rw [wireInS_input L _ l.val l.isLt]; simp [hl]
      · intro j g hg i hi hlt hiS
        change wireInS L res.2 (n + j) = true
        exact (wireInS_gate L _ j g hg).mpr ⟨i, hi, hlt, hiS⟩
    · intro x
      have hx := hcore.2.2.2.2.2 x C.output hout_lt hout_ne
      rw [hout] at hx
      exact hx

def valRepl (C : Circuit) (n j0 : ℕ) (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) (w : ℕ) : Bool :=
  if hw : w < n then
    x ⟨w, hw⟩
  else if w = n + j0 then
    f x
  else
    match C.gates[w - n]? with
    | none => false
    | some g => g.op.eval (g.inputs.attach.map fun i => if _ : i.1 < w then valRepl C n j0 f x i.1 else false)
termination_by w

lemma valRepl_input (C : Circuit) (n j0 : ℕ) (f : (Fin n → Bool) → Bool) (x : Fin n → Bool)
    (w : ℕ) (hw : w < n) : valRepl C n j0 f x w = x ⟨w, hw⟩ := by
  rw [valRepl]; simp [hw]

lemma valRepl_j0 (C : Circuit) (n j0 : ℕ) (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    valRepl C n j0 f x (n + j0) = f x := by
  rw [valRepl]
  have hnot : ¬ n + j0 < n := by omega
  simp [hnot]

lemma valRepl_gate_ne (C : Circuit) (n j0 : ℕ) (f : (Fin n → Bool) → Bool) (x : Fin n → Bool)
    (j : ℕ) (hjne : j ≠ j0) (g : Gate) (hg : C.gates[j]? = some g) :
    valRepl C n j0 f x (n + j) =
      g.op.eval (g.inputs.map fun i => if i < n + j then valRepl C n j0 f x i else false) := by
  conv_lhs => rw [valRepl]
  have h1 : ¬ n + j < n := by omega
  have h2 : n + j ≠ n + j0 := by omega
  simp only [h1, h2, ↓reduceDIte, ↓reduceIte, Nat.add_sub_cancel_left, hg]
  congr 1
  rw [List.map_attach_eq_pmap]
  induction g.inputs with
  | nil => rfl
  | cons a l ih => simp

lemma valRepl_none_ne (C : Circuit) (n j0 : ℕ) (f : (Fin n → Bool) → Bool) (x : Fin n → Bool)
    (j : ℕ) (hjne : j ≠ j0) (hg : C.gates[j]? = none) :
    valRepl C n j0 f x (n + j) = false := by
  rw [valRepl]
  have h1 : ¬ n + j < n := by omega
  have h2 : n + j ≠ n + j0 := by omega
  simp only [h1, h2, ↓reduceDIte, ↓reduceIte, Nat.add_sub_cancel_left, hg]

lemma valRepl_eq_val_lt (C : Circuit) (n j0 : ℕ) (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    ∀ w < n + j0, valRepl C n j0 f x w = val C n x w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · rw [valRepl_input _ _ _ _ _ w hwn, val_input C x w hwn]
    · set j := w - n
      have hwj : w = n + j := by omega
      have hjne : j ≠ j0 := by omega
      cases hg : C.gates[j]? with
      | none => rw [hwj, valRepl_none_ne _ _ _ _ _ j hjne hg, val_none C x j hg]
      | some g =>
        rw [hwj, valRepl_gate_ne _ _ _ _ _ j hjne g hg, val_gate C x j g hg]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hilt : i < n + j
        · simp only [hilt, ↓reduceIte]
          exact ih i (by omega) (by omega)
        · simp only [hilt, ↓reduceIte]

lemma valRepl_le_val (C : Circuit) (n j0 : ℕ) (hmono : Monotone2 C) (f : (Fin n → Bool) → Bool)
    (x : Fin n → Bool) (hf : f x = true → val C n x (n + j0) = true) :
    ∀ w : ℕ, valRepl C n j0 f x w = true → val C n x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro h
    by_cases hwn : w < n
    · rw [valRepl_input _ _ _ _ _ w hwn] at h
      rw [val_input C x w hwn]; exact h
    · set j := w - n
      have hwj : w = n + j := by omega
      rw [hwj] at h ⊢
      by_cases hjeq : j = j0
      · subst hjeq; rw [valRepl_j0] at h; exact hf h
      · cases hg : C.gates[j]? with
        | none => rw [valRepl_none_ne _ _ _ _ _ j hjeq hg] at h; cases h
        | some g =>
          rw [valRepl_gate_ne _ _ _ _ _ j hjeq g hg] at h
          rw [val_gate C x j g hg]
          have hgop : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using (hmono g (List.mem_of_getElem? hg)).1
          apply gateOp_mono g.op hgop _ _ _ ?_ h
          intro i _ hi
          by_cases hilt : i < n + j
          · simp only [hilt, ↓reduceIte] at hi ⊢
            exact ih i (by omega) hi
          · simp only [hilt, ↓reduceIte] at hi; cases hi

lemma val_le_valRepl (C : Circuit) (n j0 : ℕ) (hmono : Monotone2 C) (f : (Fin n → Bool) → Bool)
    (x : Fin n → Bool) (hf : val C n x (n + j0) = true → f x = true) :
    ∀ w : ℕ, val C n x w = true → valRepl C n j0 f x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro h
    by_cases hwn : w < n
    · rw [val_input C x w hwn] at h
      rw [valRepl_input _ _ _ _ _ w hwn]; exact h
    · set j := w - n
      have hwj : w = n + j := by omega
      rw [hwj] at h ⊢
      by_cases hjeq : j = j0
      · subst hjeq; rw [valRepl_j0]; exact hf h
      · cases hg : C.gates[j]? with
        | none => rw [val_none C x j hg] at h; cases h
        | some g =>
          rw [val_gate C x j g hg] at h
          rw [valRepl_gate_ne _ _ _ _ _ j hjeq g hg]
          have hgop : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using (hmono g (List.mem_of_getElem? hg)).1
          apply gateOp_mono g.op hgop _ _ _ ?_ h
          intro i _ hi
          by_cases hilt : i < n + j
          · simp only [hilt, ↓reduceIte] at hi ⊢
            exact ih i (by omega) hi
          · simp only [hilt, ↓reduceIte] at hi; cases hi

lemma valRepl_eq_val_of_eq (C : Circuit) (n j0 : ℕ) (f : (Fin n → Bool) → Bool)
    (x : Fin n → Bool) (hf : f x = val C n x (n + j0)) :
    ∀ w : ℕ, valRepl C n j0 f x w = val C n x w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hwn : w < n
    · rw [valRepl_input _ _ _ _ _ w hwn, val_input C x w hwn]
    · set j := w - n
      have hwj : w = n + j := by omega
      rw [hwj]
      by_cases hjeq : j = j0
      · subst hjeq; rw [valRepl_j0, hf]
      · cases hg : C.gates[j]? with
        | none => rw [valRepl_none_ne _ _ _ _ _ j hjeq hg, val_none C x j hg]
        | some g =>
          rw [valRepl_gate_ne _ _ _ _ _ j hjeq g hg, val_gate C x j g hg]
          congr 1
          apply List.map_congr_left
          intro i _
          by_cases hilt : i < n + j
          · simp only [hilt, ↓reduceIte]; exact ih i (by omega)
          · simp only [hilt, ↓reduceIte]

lemma valRepl_eq_of_not_inS {n : ℕ} (L : Finset (Fin n)) (C : Circuit) (S : Set ℕ)
    (hS : ValidS L C S) (j0 : ℕ) (hjS : n + j0 ∈ S) (f : (Fin n → Bool) → Bool)
    (x : Fin n → Bool) :
    ∀ w : ℕ, w ∉ S → valRepl C n j0 f x w = val C n x w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwS
    by_cases hwn : w < n
    · rw [valRepl_input _ _ _ _ _ w hwn, val_input C x w hwn]
    · set j := w - n
      have hwj : w = n + j := by omega
      have hjne : j ≠ j0 := fun h => hwS (hwj ▸ h ▸ hjS)
      cases hg : C.gates[j]? with
      | none => rw [hwj, valRepl_none_ne _ _ _ _ _ j hjne hg, val_none C x j hg]
      | some g =>
        rw [hwj, valRepl_gate_ne _ _ _ _ _ j hjne g hg, val_gate C x j g hg]
        congr 1
        apply List.map_congr_left
        intro i hi
        by_cases hilt : i < n + j
        · simp only [hilt, ↓reduceIte]
          have hiS : i ∉ S := fun h => hwS (hwj ▸ hS.2.1 j g hg i hi hilt h)
          exact ih i (by omega) hiS
        · simp only [hilt, ↓reduceIte]

lemma elim_step_valRepl {n : ℕ} (L : Finset (Fin n)) (j0 : ℕ) (repl : List Stat → Stat)
    (f : (Fin n → Bool) → Bool)
    (C : Circuit) (S : Set ℕ) (hmono : Monotone2 C) (hS : ValidS L C S)
    (hj0 : j0 < C.gates.length)
    (hrepl_valid : ∀ tbl : List Stat, tbl.length = n + j0 →
      (∀ i < n + j0, statValid (n + (elimPass n j0 repl (C.gates.take j0)).2.length) (tbl.getD i (Sum.inl false))) →
      statValid (n + (elimPass n j0 repl (C.gates.take j0)).2.length) (repl tbl))
    (hrepl_S : ∀ tbl : List Stat, tbl.length = n + j0 →
      (∀ i < n + j0, ∀ m, tbl.getD i (Sum.inl false) = Sum.inr m →
        wireInS L (elimPass n j0 repl (C.gates.take j0)).2 m = true → i ∈ S) →
      ∀ m, repl tbl = Sum.inr m →
        wireInS L (elimPass n j0 repl (C.gates.take j0)).2 m = true → n + j0 ∈ S)
    (hrepl_f : ∀ (x : Fin n → Bool) (tbl : List Stat) (w' : List Bool),
      tbl.length = n + j0 →
      (∀ i < n + j0, statVal w' (tbl.getD i (Sum.inl false)) = val C n x i) →
      statVal w' (repl tbl) = f x) :
    let res := elimPass n j0 repl C.gates
    res.1.length = n + C.gates.length ∧
    res.2.length < C.gates.length ∧
    (∀ g ∈ res.2, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
    (∀ (j : ℕ) (g : Gate), res.2[j]? = some g → g.op = GateOp.and →
      ∀ a b : ℕ, g.inputs = [a, b] → a < n + j → b < n + j →
      ¬ (wireInS L res.2 a = true ∧ wireInS L res.2 b = true)) ∧
    (∀ (x : Fin n → Bool) (i : ℕ), i < n + C.gates.length →
      statVal (res.2.foldl step (List.ofFn x)) (res.1.getD i (Sum.inl false)) = valRepl C n j0 f x i) := by
  have hcore := elim_step_struct L j0 repl C S hmono hS hj0 hrepl_valid hrepl_S
  have hpref_val : ∀ k ≤ C.gates.length,
      let res := elimPass n j0 repl (C.gates.take k)
      res.1.length = n + k ∧
      (∀ i < n + k, statValid (n + res.2.length) (res.1.getD i (Sum.inl false))) ∧
      (∀ (x : Fin n → Bool) (i : ℕ), i < n + k →
        statVal (res.2.foldl step (List.ofFn x)) (res.1.getD i (Sum.inl false)) = valRepl C n j0 f x i) := by
    intro k hk
    induction k with
    | zero =>
      simp only [List.take_zero, elimPass, List.zipIdx_nil, List.foldl_nil, List.length_ofFn,
        Nat.add_zero, List.length_nil, true_and]
      refine ⟨?_, ?_⟩
      · intro i hi
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte,
          Option.getD_some, statValid]
      · intro x i hi
        have hget : (List.ofFn (fun i : Fin n => (Sum.inr i.val : Stat))).getD i (Sum.inl false) = Sum.inr i := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some]
        rw [hget]
        simp only [statVal, valRepl_input _ _ _ _ _ i hi, ofFn_getD_lt x i hi]
    | succ k ih =>
      obtain ⟨hlen, hval, hsnd⟩ := ih (by omega)
      have hklt : k < C.gates.length := by omega
      have htake : C.gates.take (k + 1) = C.gates.take k ++ [C.gates[k]'hklt] :=
        List.take_succ_eq_append_getElem hklt
      have hzip : (C.gates.take (k + 1)).zipIdx = (C.gates.take k).zipIdx ++ [(C.gates[k]'hklt, k)] := by
        rw [htake, List.zipIdx_append]
        simp [List.length_take, Nat.min_eq_left (by omega : k ≤ C.gates.length)]
      set prev := elimPass n j0 repl (C.gates.take k)
      have hstep : elimPass n j0 repl (C.gates.take (k + 1)) =
          if k = j0 then
            (prev.1 ++ [repl prev.1], prev.2)
          else
            let ins := (C.gates[k]'hklt).inputs.map (fun i => if i < n + k then prev.1.getD i (Sum.inl false) else Sum.inl false)
            let res := simpMono (C.gates[k]'hklt).op (n + prev.2.length) ins
            (prev.1 ++ [res.1], prev.2 ++ res.2.toList) := by
        show ((C.gates.take (k + 1)).zipIdx).foldl _ _ = _
        rw [hzip, List.foldl_append, List.foldl_cons, List.foldl_nil]
        rfl
      rw [hstep]
      by_cases hkj : k = j0
      · subst hkj
        simp only [↓reduceIte]
        refine ⟨by simp [hlen]; omega, ?_, ?_⟩
        · intro i hi
          by_cases hik : i < n + k
          · have hget : (prev.1 ++ [repl prev.1]).getD i (Sum.inl false) = prev.1.getD i (Sum.inl false) := by
              simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < prev.1.length)]
            rw [hget]; exact hval i hik
          · have heq : i = n + k := by omega
            subst heq
            have hget : (prev.1 ++ [repl prev.1]).getD (n + k) (Sum.inl false) = repl prev.1 := by
              rw [← hlen]; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            rw [hget]; exact hrepl_valid prev.1 hlen hval
        · intro x i hi
          by_cases hik : i < n + k
          · have hget : (prev.1 ++ [repl prev.1]).getD i (Sum.inl false) = prev.1.getD i (Sum.inl false) := by
              simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < prev.1.length)]
            rw [hget]; exact hsnd x i hik
          · have heq : i = n + k := by omega
            subst heq
            have hget : (prev.1 ++ [repl prev.1]).getD (n + k) (Sum.inl false) = repl prev.1 := by
              rw [← hlen]; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            rw [hget, valRepl_j0]
            exact hrepl_f x prev.1 (prev.2.foldl step (List.ofFn x)) hlen
              (fun i hi => (hsnd x i hi).trans (valRepl_eq_val_lt C n k f x i hi))
      · simp only [hkj, ↓reduceIte]
        set g := C.gates[k]'hklt
        set ins := g.inputs.map (fun i => if i < n + k then prev.1.getD i (Sum.inl false) else Sum.inl false)
        set sm := simpMono g.op (n + prev.2.length) ins
        have hgetk : C.gates[k]? = some g := List.getElem?_eq_getElem hklt
        have hgmem : g ∈ C.gates := List.getElem_mem hklt
        have hgop : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using (hmono g hgmem).1
        have hglen : g.inputs.length ≤ 2 := (hmono g hgmem).2
        have hsm_ok := simpMono_ok g.op (n + prev.2.length) ins (fun s hs => by
          obtain ⟨i, _, rfl⟩ := List.mem_map.mp hs
          by_cases hi : i < n + k
          · simp only [hi, ↓reduceIte]; exact hval i hi
          · simp only [hi, ↓reduceIte, statValid])
        refine ⟨by simp [hlen]; omega, ?_, ?_⟩
        · intro i hi
          simp only [List.length_append]
          by_cases hik : i < n + k
          · have hget : (prev.1 ++ [sm.1]).getD i (Sum.inl false) = prev.1.getD i (Sum.inl false) := by
              simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < prev.1.length)]
            rw [hget]
            exact statValid_mono (by omega) _ (hval i hik)
          · have heq : i = n + k := by omega
            subst heq
            have hget : (prev.1 ++ [sm.1]).getD (n + k) (Sum.inl false) = sm.1 := by
              rw [← hlen]; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            rw [hget, ← Nat.add_assoc]; exact hsm_ok.1
        · intro x i hi
          rw [List.foldl_append]
          have hprevlen : (prev.2.foldl step (List.ofFn x)).length = n + prev.2.length := by
            rw [foldl_step_len, List.length_ofFn]
          by_cases hik : i < n + k
          · have hget : (prev.1 ++ [sm.1]).getD i (Sum.inl false) = prev.1.getD i (Sum.inl false) := by
              simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < prev.1.length)]
            rw [hget]
            have hkeep : statVal (sm.2.toList.foldl step (prev.2.foldl step (List.ofFn x))) (prev.1.getD i (Sum.inl false)) =
                statVal (prev.2.foldl step (List.ofFn x)) (prev.1.getD i (Sum.inl false)) := by
              have hvi := hval i hik
              cases hs : prev.1.getD i (Sum.inl false) with
              | inl b => rfl
              | inr m =>
                rw [hs] at hvi
                exact foldl_step_getD_lt sm.2.toList _ m (by rw [hprevlen]; exact hvi)
            rw [hkeep]; exact hsnd x i hik
          · have heq : i = n + k := by omega
            subst heq
            have hget : (prev.1 ++ [sm.1]).getD (n + k) (Sum.inl false) = sm.1 := by
              rw [← hlen]; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            rw [hget]
            have hglen' : ins.length ≤ 2 := by simp only [ins, List.length_map]; exact hglen
            have hsms := simpMono_sound g.op hgop (prev.2.foldl step (List.ofFn x)) ins hglen'
            rw [hprevlen] at hsms
            change statVal (sm.2.toList.foldl step (prev.2.foldl step (List.ofFn x))) sm.1 = _
            rw [hsms, valRepl_gate_ne C n j0 f x k hkj g hgetk]
            congr 1
            simp only [ins, List.map_map]
            apply List.map_congr_left
            intro u _
            simp only [Function.comp_apply]
            by_cases hu_lt : u < n + k
            · simp only [hu_lt, ↓reduceIte]; exact hsnd x u hu_lt
            · simp only [hu_lt, ↓reduceIte, statVal]
  have hfull := hpref_val C.gates.length (le_refl _)
  rw [List.take_length] at hfull
  exact ⟨hcore.1, hcore.2.1, hcore.2.2.1, hcore.2.2.2.2, hfull.2.2⟩

lemma elim_smaller_by_valRepl {n : ℕ} (G : SimpleGraph (Fin n)) (L : Finset (Fin n))
    (C : Circuit) (S : Set ℕ) (hmono : Monotone2 C) (hS : ValidS L C S)
    (hedge : ∃ u v : Fin n, G.Adj u v)
    (hout_lt : C.output < n + C.gates.length)
    (j0 : ℕ) (hj0 : j0 < C.gates.length)
    (repl : List Stat → Stat) (f : (Fin n → Bool) → Bool)
    (hrepl_valid : ∀ tbl : List Stat, tbl.length = n + j0 →
      (∀ i < n + j0, statValid (n + (elimPass n j0 repl (C.gates.take j0)).2.length) (tbl.getD i (Sum.inl false))) →
      statValid (n + (elimPass n j0 repl (C.gates.take j0)).2.length) (repl tbl))
    (hrepl_S : ∀ tbl : List Stat, tbl.length = n + j0 →
      (∀ i < n + j0, ∀ m, tbl.getD i (Sum.inl false) = Sum.inr m →
        wireInS L (elimPass n j0 repl (C.gates.take j0)).2 m = true → i ∈ S) →
      ∀ m, repl tbl = Sum.inr m →
        wireInS L (elimPass n j0 repl (C.gates.take j0)).2 m = true → n + j0 ∈ S)
    (hrepl_f : ∀ (x : Fin n → Bool) (tbl : List Stat) (w' : List Bool),
      tbl.length = n + j0 →
      (∀ i < n + j0, statVal w' (tbl.getD i (Sum.inl false)) = val C n x i) →
      statVal w' (repl tbl) = f x)
    (hEdge : ∀ u v : Fin n, G.Adj u v → valRepl C n j0 f (e2 u v) C.output = true)
    (hY0 : valRepl C n j0 f (y0 L) C.output = false)
    (hYl : ∀ l ∈ L, valRepl C n j0 f (yl G L l) C.output = false) :
    ∃ C' : Circuit, Monotone2 C' ∧ C'.size < C.size ∧
      (∃ S' : Set ℕ, ValidS L C' S') ∧
      ∀ x : Fin n → Bool, val C' n x C'.output = true ↔
        ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  have hcore := elim_step_valRepl L j0 repl f C S hmono hS hj0 hrepl_valid hrepl_S hrepl_f
  set res := elimPass n j0 repl C.gates
  obtain ⟨u0, v0, huv0⟩ := hedge
  cases hout : res.1.getD C.output (Sum.inl false) with
  | inl b =>
    cases b
    · have ht := hcore.2.2.2.2 (e2 u0 v0) C.output hout_lt
      rw [hout, hEdge u0 v0 huv0] at ht; cases ht
    · have ht := hcore.2.2.2.2 (y0 L) C.output hout_lt
      rw [hout, hY0] at ht; cases ht
  | inr wout =>
    have hM' : Monotone2 ⟨res.2, wout⟩ := fun g hg =>
      let h := hcore.2.2.1 g hg; ⟨by simpa using h.1, h.2⟩
    have hS' : ValidS L ⟨res.2, wout⟩ { w | wireInS L res.2 w = true } := by
      refine ⟨?_, ?_, hcore.2.2.2.1⟩
      · intro l hl; change wireInS L res.2 l.val = true
        rw [wireInS_input L _ l.val l.isLt]; simp [hl]
      · intro j g hg i hi hlt hiS; change wireInS L res.2 (n + j) = true
        exact (wireInS_gate L _ j g hg).mpr ⟨i, hi, hlt, hiS⟩
    have heval : ∀ x, val ⟨res.2, wout⟩ n x wout = valRepl C n j0 f x C.output := by
      intro x
      have hx := hcore.2.2.2.2 x C.output hout_lt
      rw [hout] at hx
      exact hx
    refine ⟨⟨res.2, wout⟩, hM', hcore.2.1, ⟨_, hS'⟩, ?_⟩
    exact bipartite_test_iff G L ⟨res.2, wout⟩ _ hM' hS'
      (fun u v hadj => by rw [heval]; exact hEdge u v hadj)
      (by rw [heval]; exact hY0)
      (fun l hl => by rw [heval]; exact hYl l hl)

lemma super_killer {n : ℕ} (G : SimpleGraph (Fin n)) (L : Finset (Fin n))
    (C : Circuit) (S : Set ℕ) (hmono : Monotone2 C) (hS : ValidS L C S)
    (j0 : ℕ) (hjS : n + j0 ∈ S) (g0 : Gate) (hg0 : C.gates[j0]? = some g0)
    (hop0 : g0.op = GateOp.and) (sW rW : ℕ)
    (hsW : sW ∈ g0.inputs) (hrW : rW ∈ g0.inputs)
    (hsW_lt : sW < n + j0) (hrW_lt : rW < n + j0)
    (hsW_S : sW ∈ S) (hrW_notS : rW ∉ S)
    (l l' r : Fin n) (hl : l ∈ L) (hr : r ∉ L) (hna : ¬ G.Adj l' r)
    (ha_yl' : val C n (yl G L l') sW = true) :
    ∀ w : ℕ, val C n (e2 l r) w = true →
      valRepl C n j0 (fun _ => false) (e2 l r) w = false →
      val C n (yl G L l') w = true := by
  have hr_yl' : yl G L l' r = true := by
    simp only [yl, decide_eq_true_eq]
    exact Or.inr ⟨hr, fun h => hna h.symm⟩
  have hR_to_yl' : ∀ b : ℕ, b ∉ S → val C n (e2 l r) b = true → val C n (yl G L l') b = true := by
    intro b hbS hbe
    have h1 : val C n (e1 r) b = true := by
      rw [← val_indep_of_not_inS L C S hS (e2 l r) (e1 r) ?_ b hbS]
      · exact hbe
      · intro v hv
        have hvl : v ≠ l := fun h => hv (h ▸ hl)
        simp [e2, e1, hvl]
    refine val_mono C hmono (e1 r) (yl G L l') ?_ b h1
    intro v hv
    simp only [e1, decide_eq_true_eq] at hv
    subst hv; exact hr_yl'
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hC hK
    by_cases hwn : w < n
    · rw [val_input C _ w hwn] at hC
      rw [valRepl_input _ _ _ _ _ w hwn] at hK
      rw [hC] at hK; cases hK
    · set j := w - n
      have hwj : w = n + j := by omega
      rw [hwj] at hC hK ⊢
      by_cases hjeq : j = j0
      · subst hjeq
        have hall := (val_and C _ j g0 hg0 hop0).mp hC
        have h2 : val C n (yl G L l') rW = true := hR_to_yl' rW hrW_notS (hall rW hrW).2
        refine (val_and C _ j g0 hg0 hop0).mpr ?_
        have hlen := (hmono g0 (List.mem_of_getElem? hg0)).2
        have hne : sW ≠ rW := fun heq => hrW_notS (heq ▸ hsW_S)
        intro z hz
        rcases hli : g0.inputs with _ | ⟨u, _ | ⟨v, _ | _⟩⟩
        · rw [hli] at hz; simp at hz
        · rw [hli] at hsW hrW hz
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hsW hrW hz
          exact absurd (hsW.trans hrW.symm) hne
        · rw [hli] at hsW hrW hz
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hsW hrW hz
          rcases hsW with rfl | rfl <;> rcases hrW with h1 | h2'
          · exact absurd h1.symm hne
          · subst h2'
            rcases hz with rfl | rfl
            · exact ⟨hsW_lt, ha_yl'⟩
            · exact ⟨hrW_lt, h2⟩
          · subst h1
            rcases hz with rfl | rfl
            · exact ⟨hrW_lt, h2⟩
            · exact ⟨hsW_lt, ha_yl'⟩
          · exact absurd h2'.symm hne
        · rw [hli] at hlen; simp at hlen
      · cases hg : C.gates[j]? with
        | none => rw [val_none C _ j hg] at hC; cases hC
        | some g =>
          by_cases hwS : n + j ∈ S
          · have hgop : g.op = GateOp.and ∨ g.op = GateOp.or := by
              simpa using (hmono g (List.mem_of_getElem? hg)).1
            rcases hgop with hand | hor
            · have hall := (val_and C _ j g hg hand).mp hC
              have hK_not : ¬ ∀ u ∈ g.inputs, u < n + j ∧ valRepl C n j0 (fun _ => false) (e2 l r) u = true := by
                intro h
                have htrue : valRepl C n j0 (fun _ => false) (e2 l r) (n + j) = true := by
                  rw [valRepl_gate_ne _ _ _ _ _ j hjeq g hg, hand]
                  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id]
                  intro u hu
                  obtain ⟨hlt, hv⟩ := h u hu
                  simpa [hlt] using hv
                rw [htrue] at hK; cases hK
              push Not at hK_not
              obtain ⟨u0, hu0, hfail⟩ := hK_not
              obtain ⟨hu0_lt, hu0_C⟩ := hall u0 hu0
              have hu0_K : valRepl C n j0 (fun _ => false) (e2 l r) u0 = false := by
                cases hv : valRepl C n j0 (fun _ => false) (e2 l r) u0 with
                | false => rfl
                | true => exact absurd hv (hfail hu0_lt)
              have hu0_S : u0 ∈ S := by
                by_contra hnot
                have := valRepl_eq_of_not_inS L C S hS j0 hjS (fun _ => false) (e2 l r) u0 hnot
                rw [hu0_K, hu0_C] at this; cases this
              have hu0_yl' : val C n (yl G L l') u0 = true := ih u0 (by omega) hu0_C hu0_K
              refine (val_and C _ j g hg hand).mpr ?_
              intro v hv
              obtain ⟨hv_lt, hv_C⟩ := hall v hv
              refine ⟨hv_lt, ?_⟩
              by_cases hvu : v = u0
              · subst hvu; exact hu0_yl'
              · have hv_notS : v ∉ S := by
                  intro hvS
                  have hlen := (hmono g (List.mem_of_getElem? hg)).2
                  rcases hli : g.inputs with _ | ⟨x1, _ | ⟨x2, _ | _⟩⟩
                  · rw [hli] at hv; simp at hv
                  · rw [hli] at hv hu0; simp at hv hu0; exact hvu (hv.trans hu0.symm)
                  · rw [hli] at hv hu0; simp at hv hu0
                    rcases hv with rfl | rfl <;> rcases hu0 with rfl | rfl
                    · exact hvu rfl
                    · exact hS.2.2 j g hg hand v u0 hli hv_lt hu0_lt ⟨hvS, hu0_S⟩
                    · exact hS.2.2 j g hg hand u0 v hli hu0_lt hv_lt ⟨hu0_S, hvS⟩
                    · exact hvu rfl
                  · rw [hli] at hlen; simp at hlen
                exact hR_to_yl' v hv_notS hv_C
            · obtain ⟨u, hu, hu_lt, hu_C⟩ := (val_or C _ j g hg hor).mp hC
              have hu_K : valRepl C n j0 (fun _ => false) (e2 l r) u = false := by
                cases hv : valRepl C n j0 (fun _ => false) (e2 l r) u with
                | false => rfl
                | true =>
                  have htrue : valRepl C n j0 (fun _ => false) (e2 l r) (n + j) = true := by
                    rw [valRepl_gate_ne _ _ _ _ _ j hjeq g hg, hor]
                    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
                    exact ⟨u, hu, by simpa [hu_lt] using hv⟩
                  rw [htrue] at hK; cases hK
              exact (val_or C _ j g hg hor).mpr ⟨u, hu, hu_lt, ih u (by omega) hu_C hu_K⟩
          · have heq := valRepl_eq_of_not_inS L C S hS j0 hjS (fun _ => false) (e2 l r) (n + j) hwS
            rw [hK, hC] at heq; cases heq

def bigInputCount (n : ℕ) (C : Circuit) : ℕ :=
  (C.gates.map fun g => g.inputs.countP (fun i => decide (n ≤ i))).sum

lemma set_gate_val {n : ℕ} (C : Circuit) (j0 : ℕ) (hj0 : j0 < C.gates.length)
    (g' : Gate)
    (C' : Circuit) (hC' : C' = ⟨C.gates.set j0 g', C.output⟩) (x : Fin n → Bool) :
    ∀ w : ℕ, val C' n x w =
      valRepl C n j0 (fun z => g'.op.eval (g'.inputs.map fun i => if i < n + j0 then val C n z i else false)) x w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hwn : w < n
    · rw [val_input C' x w hwn, valRepl_input _ _ _ _ _ w hwn]
    · set j := w - n
      have hwj : w = n + j := by omega
      rw [hwj]
      by_cases hjeq : j = j0
      · subst hjeq
        have hget' : C'.gates[j]? = some g' := by
          rw [hC']; simp [List.getElem?_set_self hj0]
        rw [val_gate C' x j g' hget', valRepl_j0]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hilt : i < n + j
        · simp only [hilt, ↓reduceIte]
          rw [ih i (by omega), valRepl_eq_val_lt C n j _ x i hilt]
        · simp only [hilt, ↓reduceIte]
      · have hget' : C'.gates[j]? = C.gates[j]? := by
          rw [hC']; exact List.getElem?_set_ne (Ne.symm hjeq)
        cases hg : C.gates[j]? with
        | none =>
          rw [hg] at hget'
          rw [val_none C' x j hget', valRepl_none_ne _ _ _ _ _ j hjeq hg]
        | some g =>
          rw [hg] at hget'
          rw [val_gate C' x j g hget', valRepl_gate_ne _ _ _ _ _ j hjeq g hg]
          congr 1
          apply List.map_congr_left
          intro i _
          by_cases hilt : i < n + j
          · simp only [hilt, ↓reduceIte]; exact ih i (by omega)
          · simp only [hilt, ↓reduceIte]

lemma bigInputCount_set_lt (n : ℕ) (C : Circuit) (j0 : ℕ) (hj0 : j0 < C.gates.length)
    (g' : Gate)
    (hcnt : g'.inputs.countP (fun i => decide (n ≤ i)) <
      (C.gates[j0]'hj0).inputs.countP (fun i => decide (n ≤ i))) :
    bigInputCount n ⟨C.gates.set j0 g', C.output⟩ < bigInputCount n C := by
  unfold bigInputCount
  dsimp only
  have h1 : ∀ (l : List Gate) (j : ℕ) (hj : j < l.length) (g' : Gate),
      g'.inputs.countP (fun i => decide (n ≤ i)) <
        (l[j]'hj).inputs.countP (fun i => decide (n ≤ i)) →
      ((l.set j g').map fun g => g.inputs.countP (fun i => decide (n ≤ i))).sum <
        (l.map fun g => g.inputs.countP (fun i => decide (n ≤ i))).sum := by
    intro l
    induction l with
    | nil => intro j hj; simp at hj
    | cons a l ih =>
      intro j hj g' hc
      cases j with
      | zero =>
        simp only [List.set_cons_zero, List.map_cons, List.sum_cons]
        simp only [List.getElem_cons_zero] at hc
        omega
      | succ j =>
        simp only [List.set_cons_succ, List.map_cons, List.sum_cons]
        simp only [List.getElem_cons_succ] at hc
        have := ih j (by simpa using hj) g' hc
        omega
  exact h1 C.gates j0 hj0 g' hcnt

lemma card_le_of_rel {α β : Type} (s : Finset α) (t : Finset β) (Q : α → β → Prop)
    (h1 : ∀ a ∈ s, ∃ b ∈ t, Q a b)
    (h2 : ∀ a1 ∈ s, ∀ a2 ∈ s, ∀ b, Q a1 b → Q a2 b → a1 = a2) : s.card ≤ t.card := by
  have hsub : s ⊆ t.biUnion (fun b => s.filter (fun a => Q a b)) := by
    intro a ha
    obtain ⟨b, hb, hq⟩ := h1 a ha
    exact Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_filter.mpr ⟨ha, hq⟩⟩
  calc s.card ≤ (t.biUnion fun b => s.filter fun a => Q a b).card := Finset.card_le_card hsub
    _ ≤ ∑ b ∈ t, (s.filter fun a => Q a b).card := Finset.card_biUnion_le
    _ ≤ ∑ b ∈ t, 1 := Finset.sum_le_sum (fun b _ => Finset.card_le_one.mpr (by
        intro a1 h1' a2 h2'
        rw [Finset.mem_filter] at h1' h2'
        exact h2 a1 h1'.1 a2 h2'.1 b h1'.2 h2'.2))
    _ = t.card := by simp

lemma r_leaf_trace {n : ℕ} (G : SimpleGraph (Fin n)) (L : Finset (Fin n))
    (C : Circuit) (S : Set ℕ) (hS : ValidS L C S)
    (T : ℕ → Finset (Fin n))
    (hT_spec : ∀ w, w ∉ S → w < n + C.size →
      ∀ r : Fin n, r ∈ T w ↔ r ∉ L ∧ val C n (e1 r) w = true)
    (hR_or : ∀ j < C.size, n + j ∉ S → ∀ g, C.gates[j]? = some g → g.op = GateOp.or)
    (_hshape : ∀ j < C.size, ∀ g, C.gates[j]? = some g →
      ∃ a b, g.inputs = [a, b] ∧ a < n + j ∧ b < n + j)
    (hR_ge2 : ∀ j < C.size, n + j ∉ S → 2 ≤ (T (n + j)).card)
    (l r : Fin n) (hr : r ∉ L) :
    ∀ w : ℕ, w < n + C.size → w ∉ S → n ≤ w → r ∈ T w →
      (∀ r' ∈ T w, G.Adj l r') →
      ∃ gR : ℕ, gR < C.size ∧ n + gR ∉ S ∧
        (∃ g : Gate, C.gates[gR]? = some g ∧ r.val ∈ g.inputs) ∧
        2 ≤ (T (n + gR)).card ∧ (∀ r' ∈ T (n + gR), G.Adj l r') := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwlt hwS hwn hrT hadj
    set j := w - n
    have hwj : w = n + j := by omega
    have hjlt : j < C.size := by omega
    have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
    set g := C.gates[j]'hjlt
    have hwjS : n + j ∉ S := hwj ▸ hwS
    have hor := hR_or j hjlt hwjS g hg
    have hrval : val C n (e1 r) (n + j) = true := ((hT_spec (n + j) hwjS (by omega) r).mp (hwj ▸ hrT)).2
    obtain ⟨u, hu_mem, hu_lt, hu_val⟩ := (val_or C (e1 r) j g hg hor).mp hrval
    have huS : u ∉ S := fun huin => hwjS (hS.2.1 j g hg u hu_mem hu_lt huin)
    have huT : r ∈ T u := (hT_spec u huS (by omega) r).mpr ⟨hr, hu_val⟩
    have hu_sub : ∀ r' ∈ T u, r' ∈ T (n + j) := by
      intro r' hr'
      obtain ⟨hr'L, hr'v⟩ := (hT_spec u huS (by omega) r').mp hr'
      exact (hT_spec (n + j) hwjS (by omega) r').mpr ⟨hr'L, (val_or C (e1 r') j g hg hor).mpr ⟨u, hu_mem, hu_lt, hr'v⟩⟩
    have hu_adj : ∀ r' ∈ T u, G.Adj l r' := fun r' hr' => hadj r' (hwj ▸ hu_sub r' hr')
    by_cases hun : u < n
    · have hueq : u = r.val := by
        rw [val_input C (e1 r) u hun] at hu_val
        simp only [e1, decide_eq_true_eq] at hu_val
        exact congrArg Fin.val hu_val
      subst hueq
      exact ⟨j, hjlt, hwjS, ⟨g, hg, hu_mem⟩, hR_ge2 j hjlt hwjS, hwj ▸ hadj⟩
    · exact ih u (by omega) (by omega) huS (by omega) huT hu_adj

lemma er_crit_trace {n : ℕ} (G : SimpleGraph (Fin n)) (L : Finset (Fin n))
    (C : Circuit) (S : Set ℕ) (hmono : Monotone2 C)
    (hS_in : ∀ w (hw : w < n), w ∈ S ↔ (⟨w, hw⟩ : Fin n) ∈ L)
    (hSOR : ∀ j < C.size, n + j ∈ S → ∀ g, C.gates[j]? = some g → g.op = GateOp.or →
      ∀ i ∈ g.inputs, i ∈ S)
    (hSAND : ∀ j < C.size, n + j ∈ S → ∀ g, C.gates[j]? = some g → g.op = GateOp.and →
      ∃ sW rW, (g.inputs = [sW, rW] ∨ g.inputs = [rW, sW]) ∧ sW < n + j ∧ rW < n + j ∧ sW ∈ S ∧ rW ∉ S)
    (l r : Fin n) (hr : r ∉ L) :
    ∀ w : ℕ, w < n + C.size → w ∈ S →
      val C n (e2 l r) w = true → val C n (yl G L l) w = false →
      ∃ j < C.size, n + j ∈ S ∧ ∃ g : Gate, C.gates[j]? = some g ∧ g.op = GateOp.and ∧
        ∃ sW rW, (g.inputs = [sW, rW] ∨ g.inputs = [rW, sW]) ∧ sW < n + j ∧ rW < n + j ∧
          sW ∈ S ∧ rW ∉ S ∧ val C n (e2 l r) sW = true ∧ val C n (e2 l r) rW = true ∧
          val C n (yl G L l) sW = true ∧ val C n (yl G L l) rW = false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwlt hwS hte hfl
    by_cases hwn : w < n
    · rw [val_input C _ w hwn] at hte hfl
      simp only [e2, decide_eq_true_eq] at hte
      rcases hte with h1 | h2
      · rw [h1] at hfl; simp [yl] at hfl
      · have hL : (⟨w, hwn⟩ : Fin n) ∈ L := (hS_in w hwn).mp hwS
        rw [h2] at hL; exact absurd hL hr
    · set j := w - n
      have hwj : w = n + j := by omega
      have hjlt : j < C.size := by omega
      have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
      set g := C.gates[j]'hjlt
      have hwjS : n + j ∈ S := hwj ▸ hwS
      have hgop : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using (hmono g (List.mem_of_getElem? hg)).1
      rcases hgop with hand | hor
      · obtain ⟨sW, rW, hinp, hsW_lt, hrW_lt, hsW_S, hrW_notS⟩ := hSAND j hjlt hwjS g hg hand
        have hall := (val_and C (e2 l r) j g hg hand).mp (hwj ▸ hte)
        have hsW_mem : sW ∈ g.inputs := by rcases hinp with h | h <;> rw [h] <;> simp
        have hrW_mem : rW ∈ g.inputs := by rcases hinp with h | h <;> rw [h] <;> simp
        have hsW_e : val C n (e2 l r) sW = true := (hall sW hsW_mem).2
        have hrW_e : val C n (e2 l r) rW = true := (hall rW hrW_mem).2
        cases hsW_y : val C n (yl G L l) sW with
        | false =>
          exact ih sW (by omega) (by omega) hsW_S hsW_e hsW_y
        | true =>
          have hrW_y : val C n (yl G L l) rW = false := by
            cases hrv : val C n (yl G L l) rW with
            | false => rfl
            | true =>
              have ht : val C n (yl G L l) (n + j) = true := by
                refine (val_and C _ j g hg hand).mpr ?_
                intro u hu
                rcases hinp with h | h <;> rw [h] at hu <;> simp at hu <;> rcases hu with rfl | rfl
                · exact ⟨hsW_lt, hsW_y⟩
                · exact ⟨hrW_lt, hrv⟩
                · exact ⟨hrW_lt, hrv⟩
                · exact ⟨hsW_lt, hsW_y⟩
              rw [hwj] at hfl; rw [ht] at hfl; cases hfl
          exact ⟨j, hjlt, hwjS, g, hg, hand, sW, rW, hinp, hsW_lt, hrW_lt, hsW_S, hrW_notS,
            hsW_e, hrW_e, hsW_y, hrW_y⟩
      · obtain ⟨u, hu_mem, hu_lt, hu_e⟩ := (val_or C (e2 l r) j g hg hor).mp (hwj ▸ hte)
        have hu_S : u ∈ S := hSOR j hjlt hwjS g hg hor u hu_mem
        have hu_y : val C n (yl G L l) u = false := by
          cases hv : val C n (yl G L l) u with
          | false => rfl
          | true =>
            have ht : val C n (yl G L l) (n + j) = true :=
              (val_or C _ j g hg hor).mpr ⟨u, hu_mem, hu_lt, hv⟩
            rw [hwj] at hfl; rw [ht] at hfl; cases hfl
        exact ih u (by omega) (by omega) hu_S hu_e hu_y

lemma s_multi_trace {n : ℕ} (G : SimpleGraph (Fin n)) (_L : Finset (Fin n))
    (C : Circuit) (S : Set ℕ) (hmono : Monotone2 C)
    (Alive : ℕ → Finset (Fin n))
    (hAlive_in : ∀ w < n, w ∈ S → (Alive w).card = 1)
    (hAlive_or : ∀ j < C.size, n + j ∈ S → ∀ g, C.gates[j]? = some g → g.op = GateOp.or →
      ∃ a b, g.inputs = [a, b] ∧ a < n + j ∧ b < n + j ∧ a ∈ S ∧ b ∈ S ∧ Alive (n + j) = Alive a ∪ Alive b)
    (hAlive_and_lt2 : ∀ j < C.size, n + j ∈ S → ∀ g, C.gates[j]? = some g → g.op = GateOp.and →
      (Alive (n + j)).card < 2)
    (l r : Fin n) :
    ∀ w : ℕ, w < n + C.size → w ∈ S → l ∈ Alive w → 2 ≤ (Alive w).card →
      (∀ l' ∈ Alive w, G.Adj l' r) →
      ∃ k < C.size, n + k ∈ S ∧ (∃ g : Gate, C.gates[k]? = some g ∧ g.op = GateOp.or ∧
        ∃ w' ∈ g.inputs, w' < n + k ∧ w' ∈ S ∧ Alive w' = {l}) ∧
        2 ≤ (Alive (n + k)).card ∧ (∀ l' ∈ Alive (n + k), G.Adj l' r) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwlt hwS hlA hcard hadj
    by_cases hwn : w < n
    · have := hAlive_in w hwn hwS; omega
    · set k := w - n
      have hwk : w = n + k := by omega
      have hklt : k < C.size := by omega
      have hg : C.gates[k]? = some (C.gates[k]'hklt) := List.getElem?_eq_getElem hklt
      set g := C.gates[k]'hklt
      have hwkS : n + k ∈ S := hwk ▸ hwS
      have hgop : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using (hmono g (List.mem_of_getElem? hg)).1
      rcases hgop with hand | hor
      · have := hAlive_and_lt2 k hklt hwkS g hg hand
        rw [hwk] at hcard; omega
      · obtain ⟨a, b, hinp, ha_lt, hb_lt, ha_S, hb_S, hAeq⟩ := hAlive_or k hklt hwkS g hg hor
        have hl_ab : l ∈ Alive a ∨ l ∈ Alive b := by
          rw [hwk, hAeq, Finset.mem_union] at hlA; exact hlA
        have step_child : ∀ u, u ∈ g.inputs → u < n + k → u ∈ S → l ∈ Alive u → Alive u ⊆ Alive (n + k) →
            ∃ k' < C.size, n + k' ∈ S ∧ (∃ g' : Gate, C.gates[k']? = some g' ∧ g'.op = GateOp.or ∧
              ∃ w' ∈ g'.inputs, w' < n + k' ∧ w' ∈ S ∧ Alive w' = {l}) ∧
              2 ≤ (Alive (n + k')).card ∧ (∀ l' ∈ Alive (n + k'), G.Adj l' r) := by
          intro u hu_mem hu_lt hu_S hlu hsub
          by_cases huc : 2 ≤ (Alive u).card
          · exact ih u (by omega) (by omega) hu_S hlu huc (fun l' hl' => hadj l' (hwk ▸ hsub hl'))
          · have hcard1 : (Alive u).card = 1 := by
              have hpos : 0 < (Alive u).card := Finset.card_pos.mpr ⟨l, hlu⟩
              omega
            have heq1 : Alive u = {l} := by
              obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard1
              rw [hx] at hlu
              simp only [Finset.mem_singleton] at hlu
              rw [hx, hlu]
            exact ⟨k, hklt, hwkS, ⟨g, hg, hor, u, hu_mem, hu_lt, hu_S, heq1⟩,
              hwk ▸ hcard, hwk ▸ hadj⟩
        rcases hl_ab with hla | hlb
        · exact step_child a (by rw [hinp]; simp) ha_lt ha_S hla (by rw [hAeq]; exact Finset.subset_union_left)
        · exact step_child b (by rw [hinp]; simp) hb_lt hb_S hlb (by rw [hAeq]; exact Finset.subset_union_right)

set_option maxHeartbeats 2000000 in
lemma main_lb {n : ℕ} (G : SimpleGraph (Fin n)) (L : Finset (Fin n)) (τ : ℕ)
    (hBip : ∀ u v : Fin n, G.Adj u v → (u ∈ L ↔ v ∉ L))
    (hNoC4 : ∀ u v w1 w2 : Fin n, u ≠ v → w1 ≠ w2 →
      G.Adj u w1 → G.Adj u w2 → G.Adj v w1 → ¬ G.Adj v w2)
    (hEdgeNE : ∃ u v : Fin n, G.Adj u v)
    (hTau : ∀ K : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ K ∨ v ∈ K) → τ ≤ K.card) :
    ∀ s : ℕ, ∀ m : ℕ, ∀ C : Circuit, C.size = s → bigInputCount n C = m →
      Monotone2 C → (∃ S : Set ℕ, ValidS L C S) →
      (∀ x : Fin n → Bool, val C n x C.output = true ↔
        ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) →
      ((L ×ˢ (Finset.univ \ L)).filter (fun p => G.Adj p.1 p.2)).card + τ ≤ s + 1 := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih_s =>
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih_m =>
      intro C hCsize hCbig hmono ⟨S0, hS0⟩ hfun
      by_contra hlt_goal
      have hnot_smaller : ∀ C' : Circuit, Monotone2 C' → C'.size < s →
          (∃ S', ValidS L C' S') →
          (∀ x : Fin n → Bool, val C' n x C'.output = true ↔
            ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → False := by
        intro C' hm' hsz' hS' hf'
        have := ih_s C'.size hsz' (bigInputCount n C') C' rfl rfl hm' hS' hf'
        omega
      have hnot_less_big : ∀ C' : Circuit, Monotone2 C' → C'.size = s → bigInputCount n C' < m →
          (∃ S', ValidS L C' S') →
          (∀ x : Fin n → Bool, val C' n x C'.output = true ↔
            ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → False := by
        intro C' hm' hsz' hbig' hS' hf'
        have := ih_m (bigInputCount n C') hbig' C' hsz' rfl hm' hS' hf'
        omega
      set S : Set ℕ := { w : ℕ | wireInS L C.gates w = true }
      have hS : ValidS L C S := validS_wireInS L C S0 hS0
      have hS_in : ∀ w (hw : w < n), w ∈ S ↔ (⟨w, hw⟩ : Fin n) ∈ L := by
        intro w hw; change wireInS L C.gates w = true ↔ _; rw [wireInS_input L _ w hw]; simp
      have hS_gate : ∀ j g, C.gates[j]? = some g → (n + j ∈ S ↔ ∃ i ∈ g.inputs, i < n + j ∧ i ∈ S) := by
        intro j g hg; change wireInS L C.gates (n + j) = true ↔ _; exact wireInS_gate L C.gates j g hg
      have hY0_out : val C n (y0 L) C.output = false := by
        cases hv : val C n (y0 L) C.output with
        | false => rfl
        | true =>
          exfalso
          obtain ⟨u, v, hadj, hu, hv'⟩ := (hfun _).mp hv
          simp only [y0, decide_eq_true_eq] at hu hv'
          exact hu ((hBip u v hadj).mpr hv')
      have hYl_out : ∀ l ∈ L, val C n (yl G L l) C.output = false := by
        intro l hl
        cases hv : val C n (yl G L l) C.output with
        | false => rfl
        | true =>
          exfalso
          obtain ⟨u, v, hadj, hu, hv'⟩ := (hfun _).mp hv
          simp only [yl, decide_eq_true_eq] at hu hv'
          rcases hu with rfl | ⟨huL, huna⟩ <;> rcases hv' with rfl | ⟨hvL, hvna⟩
          · exact G.loopless.irrefl _ hadj
          · exact hvna hadj.symm
          · exact huna hadj
          · exact huL ((hBip u v hadj).mpr hvL)
      have hEdge_out : ∀ u v : Fin n, G.Adj u v → val C n (e2 u v) C.output = true := by
        intro u v hadj
        exact (hfun _).mpr ⟨u, v, hadj, by simp [e2], by simp [e2]⟩
      have hCglen : C.gates.length = s := hCsize
      obtain ⟨u0, v0, huv0⟩ := hEdgeNE
      have hout_lt : C.output < n + s := by
        by_contra hge
        have ht := hEdge_out u0 v0 huv0
        rw [val_oob C _ C.output (by omega)] at ht; cases ht
      have hout_ge : n ≤ C.output := by
        by_contra hlt
        have ht : val C n (e1 ⟨C.output, by omega⟩) C.output = true := by
          rw [val_input C _ C.output (by omega)]; simp [e1]
        obtain ⟨u, v, hadj, hu, hv⟩ := (hfun _).mp ht
        simp only [e1, decide_eq_true_eq] at hu hv
        exact hadj.ne (hu.trans hv.symm)
      set o := C.output - n
      have ho_eq : C.output = n + o := by omega
      have ho_lt : o < s := by omega
      have ho_last : o + 1 = s := by
        by_contra hne
        have hlt : o + 1 < s := by omega
        set C' : Circuit := ⟨C.gates.take (o + 1), C.output⟩
        have hsz' : C'.size < s := by
          change (C.gates.take (o + 1)).length < s
          rw [List.length_take, hCglen, Nat.min_eq_left (by omega)]; exact hlt
        have hm' : Monotone2 C' := fun g hg => hmono g (List.mem_of_mem_take hg)
        have hS' : ValidS L C' S := by
          refine ⟨hS.1, ?_, ?_⟩
          · intro j g hg i hi hilt hiS
            have hjlt : j < o + 1 := by
              by_contra hge; rw [List.getElem?_eq_none (by rw [List.length_take]; omega)] at hg; cases hg
            rw [List.getElem?_take_of_lt hjlt] at hg
            exact hS.2.1 j g hg i hi hilt hiS
          · intro j g hg hop a b hab ha hb
            have hjlt : j < o + 1 := by
              by_contra hge; rw [List.getElem?_eq_none (by rw [List.length_take]; omega)] at hg; cases hg
            rw [List.getElem?_take_of_lt hjlt] at hg
            exact hS.2.2 j g hg hop a b hab ha hb
        have hf' : ∀ x, val C' n x C'.output = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
          intro x; rw [val_take C (o + 1) x C.output (by omega)]; exact hfun x
        exact hnot_smaller C' hm' hsz' ⟨S, hS'⟩ hf'
      have hno_const_copy : ∀ j0 < s,
          (¬ ∀ x, val C n x (n + j0) = false) ∧
          (¬ ∀ x, val C n x (n + j0) = true) ∧
          (∀ w0 < n + j0, (w0 ∈ S → n + j0 ∈ S) → ¬ ∀ x, val C n x (n + j0) = val C n x w0) := by
        intro j0 hj0
        have hj0len : j0 < C.gates.length := by omega
        refine ⟨?_, ?_, ?_⟩
        · intro hf
          obtain ⟨C', hm', hsz', hS', heq'⟩ := elim_smaller G L C S hmono hS ⟨u0, v0, huv0⟩ hfun j0 hj0len
            (fun _ => Sum.inl false) false (fun _ _ _ => trivial) (fun _ _ _ _ h _ => by cases h)
            (fun _ x _ _ _ _ => (hf x).symm) (by intro h; cases h)
          exact hnot_smaller C' hm' (by omega) hS' (fun x => by rw [heq' x]; exact hfun x)
        · intro ht
          obtain ⟨C', hm', hsz', hS', heq'⟩ := elim_smaller G L C S hmono hS ⟨u0, v0, huv0⟩ hfun j0 hj0len
            (fun _ => Sum.inl true) false (fun _ _ _ => trivial) (fun _ _ _ _ h _ => by cases h)
            (fun _ x _ _ _ _ => (ht x).symm) (by intro h; cases h)
          exact hnot_smaller C' hm' (by omega) hS' (fun x => by rw [heq' x]; exact hfun x)
        · intro w0 hw0 hwS heqw
          obtain ⟨C', hm', hsz', hS', heq'⟩ := elim_smaller G L C S hmono hS ⟨u0, v0, huv0⟩ hfun j0 hj0len
            (fun tbl => tbl.getD w0 (Sum.inl false)) false
            (fun tbl _ hv => hv w0 hw0)
            (fun tbl _ hinv m hm hwm => hwS (hinv w0 hw0 m hm hwm))
            (fun _ x tbl w' _ hvals => (hvals w0 hw0).trans (heqw x).symm)
            (by intro h; cases h)
          exact hnot_smaller C' hm' (by omega) hS' (fun x => by rw [heq' x]; exact hfun x)
      have hused : ∀ j0 < s, j0 ≠ o → ∃ j < s, ∃ g : Gate, C.gates[j]? = some g ∧ j0 < j ∧ n + j0 ∈ g.inputs := by
        intro j0 hj0 hne
        by_contra hno
        push Not at hno
        have hj0len : j0 < C.gates.length := by omega
        obtain ⟨C', hm', hsz', hS', heq'⟩ := elim_smaller G L C S hmono hS ⟨u0, v0, huv0⟩ hfun j0 hj0len
          (fun _ => Sum.inl false) true (fun _ _ _ => trivial) (fun _ _ _ _ h _ => by cases h)
          (by intro h; cases h)
          (fun _ => ⟨by omega, fun j g hg hjlt => hno j (by have := (List.getElem?_eq_some_iff.mp hg).1; omega) g hg hjlt⟩)
        exact hnot_smaller C' hm' (by omega) hS' (fun x => by rw [heq' x]; exact hfun x)
      have hshape : ∀ j < s, ∀ g, C.gates[j]? = some g →
          ∃ a b : ℕ, g.inputs = [a, b] ∧ a < n + j ∧ b < n + j ∧ a ≠ b := by
        intro j hj g hg
        have hgop : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using (hmono g (List.mem_of_getElem? hg)).1
        have hglen : g.inputs.length ≤ 2 := (hmono g (List.mem_of_getElem? hg)).2
        obtain ⟨hnc0, hnc1, hncw⟩ := hno_const_copy j hj
        rcases hinp : g.inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
        · rcases hgop with hand | hor
          · exfalso; apply hnc1; intro x; rw [val_gate C x j g hg, hand, hinp]; rfl
          · exfalso; apply hnc0; intro x; rw [val_gate C x j g hg, hor, hinp]; rfl
        · by_cases ha : a < n + j
          · exfalso; apply hncw a ha (hS.2.1 j g hg a (by rw [hinp]; simp) ha); intro x
            rw [val_gate C x j g hg, hinp]; rcases hgop with hand | hor
            · simp [hand, GateOp.eval, ha]
            · simp [hor, GateOp.eval, ha]
          · exfalso; apply hnc0; intro x
            rw [val_gate C x j g hg, hinp]; rcases hgop with hand | hor
            · simp [hand, GateOp.eval, ha]
            · simp [hor, GateOp.eval, ha]
        · by_cases ha : a < n + j
          · by_cases hb : b < n + j
            · by_cases hab : a = b
              · subst hab; exfalso; apply hncw a ha (hS.2.1 j g hg a (by rw [hinp]; simp) ha); intro x
                rw [val_gate C x j g hg, hinp]; rcases hgop with hand | hor
                · simp [hand, GateOp.eval, ha]
                · simp [hor, GateOp.eval, ha]
              · exact ⟨a, b, rfl, ha, hb, hab⟩
            · rcases hgop with hand | hor
              · exfalso; apply hnc0; intro x; rw [val_gate C x j g hg, hand, hinp]; simp [GateOp.eval, hb]
              · exfalso; apply hncw a ha (hS.2.1 j g hg a (by rw [hinp]; simp) ha); intro x
                rw [val_gate C x j g hg, hor, hinp]; simp [GateOp.eval, ha, hb]
          · rcases hgop with hand | hor
            · exfalso; apply hnc0; intro x; rw [val_gate C x j g hg, hand, hinp]; simp [GateOp.eval, ha]
            · by_cases hb : b < n + j
              · exfalso; apply hncw b hb (hS.2.1 j g hg b (by rw [hinp]; simp) hb); intro x
                rw [val_gate C x j g hg, hor, hinp]; simp [GateOp.eval, ha, hb]
              · exfalso; apply hnc0; intro x; rw [val_gate C x j g hg, hor, hinp]; simp [GateOp.eval, ha, hb]
        · rw [hinp] at hglen; simp at hglen
      set T : ℕ → Finset (Fin n) := fun w => (Finset.univ \ L).filter (fun r => val C n (e1 r) w = true)
      have hT_mem : ∀ w r, r ∈ T w ↔ r ∉ L ∧ val C n (e1 r) w = true := by
        intro w r; simp [T]
      have hR_y0_of_true : ∀ w, w ∉ S → ∀ x, val C n x w = true → val C n (y0 L) w = true := by
        intro w hwS x hxw
        have h1 : val C n (fun i => if i ∈ L then false else x i) w = true := by
          rw [val_indep_of_not_inS L C S hS _ x (fun r hr => by simp [hr]) w hwS]; exact hxw
        refine val_mono C hmono _ (y0 L) ?_ w h1
        intro i hi
        by_cases hiL : i ∈ L
        · simp [hiL] at hi
        · simp [y0, hiL]
      have hR_y0 : ∀ w < n + s, w ∉ S → val C n (y0 L) w = true := by
        intro w hwlt hwS
        by_cases hwn : w < n
        · rw [val_input C _ w hwn]; simp only [y0, decide_eq_true_eq]
          intro hL; exact hwS ((hS_in w hwn).mpr hL)
        · have hjlt : w - n < s := by omega
          have hnw := (hno_const_copy (w - n) hjlt).1
          push Not at hnw
          obtain ⟨x, hx⟩ := hnw
          have hxt : val C n x w = true := by
            have heq : n + (w - n) = w := by omega
            rw [heq] at hx; cases hv : val C n x w <;> simp [hv] at hx ⊢
          exact hR_y0_of_true w hwS x hxt
      have hR_or : ∀ j < s, n + j ∉ S → ∀ g, C.gates[j]? = some g → g.op = GateOp.or := by
        intro j hj hwS g hg
        have hgop : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using (hmono g (List.mem_of_getElem? hg)).1
        rcases hgop with hand | hor
        · exfalso
          obtain ⟨a, b, hinp, ha_lt, hb_lt, _⟩ := hshape j hj g hg
          have ha_notS : a ∉ S := fun haS => hwS (hS.2.1 j g hg a (by rw [hinp]; simp) ha_lt haS)
          have hb_notS : b ∉ S := fun hbS => hwS (hS.2.1 j g hg b (by rw [hinp]; simp) hb_lt hbS)
          have hj_y0 : val C n (y0 L) (n + j) = true := hR_y0 (n + j) (by omega) hwS
          have ha_y0 : val C n (y0 L) a = true := hR_y0 a (by omega) ha_notS
          have hb_y0 : val C n (y0 L) b = true := hR_y0 b (by omega) hb_notS
          have h_kill_side : ∀ c d, (g.inputs = [c, d] ∨ g.inputs = [d, c]) →
              c < n + j → d < n + j → c ∉ S → d ∉ S →
              ∃ l ∈ L, val C n (yl G L l) c = true ∧ val C n (yl G L l) d = false := by
            intro c d hcd hc_lt hd_lt hc_notS hd_notS
            have hcmem : c ∈ g.inputs := by rcases hcd with h | h <;> rw [h] <;> simp
            have hdmem : d ∈ g.inputs := by rcases hcd with h | h <;> rw [h] <;> simp
            have hj_le_c : ∀ x, val C n x (n + j) = true → val C n x c = true := by
              intro x hx; exact ((val_and C x j g hg hand).mp hx c hcmem).2
            by_contra hno
            push Not at hno
            have hYl_c : ∀ l ∈ L, valRepl C n j (fun x => val C n x c) (yl G L l) C.output = false := by
              intro l hl
              cases hvc : val C n (yl G L l) c with
              | false =>
                have hvj : val C n (yl G L l) (n + j) = false := by
                  cases hvj' : val C n (yl G L l) (n + j) with
                  | false => rfl
                  | true => have := hj_le_c _ hvj'; rw [hvc] at this; cases this
                rw [valRepl_eq_val_of_eq C n j _ (yl G L l) (by rw [hvc, hvj]) C.output]
                exact hYl_out l hl
              | true =>
                have hvd : val C n (yl G L l) d = true := by
                  cases hvd' : val C n (yl G L l) d with
                  | true => rfl
                  | false => exact absurd hvd' (hno l hl hvc)
                have hvj : val C n (yl G L l) (n + j) = true := by
                  refine (val_and C _ j g hg hand).mpr ?_
                  intro u hu
                  rcases hcd with h | h <;> rw [h] at hu <;> simp at hu <;> rcases hu with rfl | rfl
                  · exact ⟨hc_lt, hvc⟩
                  · exact ⟨hd_lt, hvd⟩
                  · exact ⟨hd_lt, hvd⟩
                  · exact ⟨hc_lt, hvc⟩
                rw [valRepl_eq_val_of_eq C n j _ (yl G L l) (by rw [hvc, hvj]) C.output]
                exact hYl_out l hl
            obtain ⟨C', hm', hsz', hS', hf'⟩ := elim_smaller_by_valRepl G L C S hmono hS
              ⟨u0, v0, huv0⟩ (by omega) j (by omega)
              (fun tbl => tbl.getD c (Sum.inl false)) (fun x => val C n x c)
              (fun tbl _ hv => hv c hc_lt)
              (fun tbl _ hinv m hm hwm => absurd (hinv c hc_lt m hm hwm) hc_notS)
              (fun x tbl w' _ hvals => hvals c hc_lt)
              (fun u v hadj => val_le_valRepl C n j hmono _ (e2 u v) (hj_le_c _) C.output (hEdge_out u v hadj))
              (by
                rw [valRepl_eq_val_of_eq C n j _ (y0 L) (by rw [hR_y0 c (by omega) hc_notS, hj_y0]) C.output]
                exact hY0_out)
              hYl_c
            exact hnot_smaller C' hm' (by omega) hS' hf'
          obtain ⟨l1, hl1, ha1, hb1⟩ := h_kill_side a b (Or.inl hinp) ha_lt hb_lt ha_notS hb_notS
          obtain ⟨l2, hl2, hb2, ha2⟩ := h_kill_side b a (Or.inr hinp) hb_lt ha_lt hb_notS ha_notS
          have hl12 : l1 ≠ l2 := fun heq => by rw [heq, ha2] at ha1; cases ha1
          have hT_sub : ∀ r ∈ T (n + j), G.Adj l1 r ∧ G.Adj l2 r := by
            intro r hr
            obtain ⟨hrL, hrv⟩ := (hT_mem (n + j) r).mp hr
            have hall := (val_and C (e1 r) j g hg hand).mp hrv
            have hra : val C n (e1 r) a = true := (hall a (by rw [hinp]; simp)).2
            have hrb : val C n (e1 r) b = true := (hall b (by rw [hinp]; simp)).2
            constructor
            · by_contra hna
              have hle : ∀ i, e1 r i = true → yl G L l1 i = true := by
                intro i hi; simp only [e1, decide_eq_true_eq] at hi; subst hi
                simp only [yl, decide_eq_true_eq]; exact Or.inr ⟨hrL, fun h => hna h.symm⟩
              have := val_mono C hmono (e1 r) (yl G L l1) hle b hrb
              rw [hb1] at this; cases this
            · by_contra hna
              have hle : ∀ i, e1 r i = true → yl G L l2 i = true := by
                intro i hi; simp only [e1, decide_eq_true_eq] at hi; subst hi
                simp only [yl, decide_eq_true_eq]; exact Or.inr ⟨hrL, fun h => hna h.symm⟩
              have := val_mono C hmono (e1 r) (yl G L l2) hle a hra
              rw [ha2] at this; cases this
          have hT_le1 : (T (n + j)).card ≤ 1 := by
            refine Finset.card_le_one.mpr ?_
            intro r1 hr1 r2 hr2
            by_contra hne
            have h1 := hT_sub r1 hr1
            have h2 := hT_sub r2 hr2
            exact hNoC4 l1 l2 r1 r2 hl12 hne h1.1 h2.1 h1.2 h2.2
          have hedge_val : ∀ u v : Fin n, G.Adj u v →
              ∃ r : Fin n, r ∉ L ∧ val C n (e2 u v) (n + j) = val C n (e1 r) (n + j) ∧ (u = r ∨ v = r) := by
            intro u v hadj
            by_cases huL : u ∈ L
            · have hvL : v ∉ L := (hBip u v hadj).mp huL
              refine ⟨v, hvL, ?_, Or.inr rfl⟩
              exact val_indep_of_not_inS L C S hS (e2 u v) (e1 v)
                (fun w hw => by have hwu : w ≠ u := fun h => hw (h ▸ huL); simp [e2, e1, hwu]) (n + j) hwS
            · have hvL : v ∈ L := by by_contra h; exact huL ((hBip u v hadj).mpr h)
              refine ⟨u, huL, ?_, Or.inl rfl⟩
              exact val_indep_of_not_inS L C S hS (e2 u v) (e1 u)
                (fun w hw => by have hwv : w ≠ v := fun h => hw (h ▸ hvL); simp [e2, e1, hwv]) (n + j) hwS
          by_cases hemp : (T (n + j)).Nonempty
          · obtain ⟨r0, hr0⟩ := hemp
            have hTeq : T (n + j) = {r0} := by
              have h1 : (T (n + j)).card = 1 := le_antisymm hT_le1 (Finset.card_pos.mpr ⟨r0, hr0⟩)
              obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h1
              rw [hx] at hr0; simp only [Finset.mem_singleton] at hr0; rw [hx, hr0]
            obtain ⟨hr0L, hr0v⟩ := (hT_mem (n + j) r0).mp hr0
            have hr0_notS : r0.val ∉ S := fun h => hr0L ((hS_in r0.val r0.isLt).mp h)
            have hr0_le : ∀ x, x r0 = true → val C n x (n + j) = true := by
              intro x hxr
              refine val_mono C hmono (e1 r0) x ?_ (n + j) hr0v
              intro i hi; simp only [e1, decide_eq_true_eq] at hi; subst hi; exact hxr
            obtain ⟨C', hm', hsz', hS', hf'⟩ := elim_smaller_by_valRepl G L C S hmono hS
              ⟨u0, v0, huv0⟩ (by omega) j (by omega)
              (fun tbl => tbl.getD r0.val (Sum.inl false)) (fun x => x r0)
              (fun tbl _ hv => hv r0.val (by omega))
              (fun tbl _ hinv m hm hwm => absurd (hinv r0.val (by omega) m hm hwm) hr0_notS)
              (fun x tbl w' _ hvals => (hvals r0.val (by omega)).trans (val_input C x r0.val r0.isLt))
              (fun u v hadj => by
                obtain ⟨r, hrL, heq, huvr⟩ := hedge_val u v hadj
                have hfeq : e2 u v r0 = val C n (e2 u v) (n + j) := by
                  rw [heq]
                  by_cases hrr0 : r = r0
                  · subst hrr0; rw [hr0v]; rcases huvr with rfl | rfl <;> simp [e2]
                  · have hrf : val C n (e1 r) (n + j) = false := by
                      cases hv : val C n (e1 r) (n + j) with
                      | false => rfl
                      | true =>
                        have hmem : r ∈ T (n + j) := (hT_mem (n + j) r).mpr ⟨hrL, hv⟩
                        rw [hTeq, Finset.mem_singleton] at hmem; exact absurd hmem hrr0
                    rw [hrf]
                    have hu_ne : r0 ≠ u := by
                      intro h; subst h
                      rcases huvr with h1 | h1
                      · exact hrr0 h1.symm
                      · have : r0 ∈ L := (hBip r0 v hadj).mpr (h1 ▸ hrL)
                        exact hr0L this
                    have hv_ne : r0 ≠ v := by
                      intro h; subst h
                      rcases huvr with h1 | h1
                      · have : r0 ∈ L := (hBip r0 u hadj.symm).mpr (h1 ▸ hrL)
                        exact hr0L this
                      · exact hrr0 h1.symm
                    simp [e2, hu_ne, hv_ne]
                rw [valRepl_eq_val_of_eq C n j _ (e2 u v) hfeq C.output]
                exact hEdge_out u v hadj)
              (by
                cases h : valRepl C n j (fun x => x r0) (y0 L) C.output with
                | false => rfl
                | true =>
                  have := valRepl_le_val C n j hmono _ (y0 L) (hr0_le _) C.output h
                  rw [hY0_out] at this; cases this)
              (fun l hl => by
                cases h : valRepl C n j (fun x => x r0) (yl G L l) C.output with
                | false => rfl
                | true =>
                  have := valRepl_le_val C n j hmono _ (yl G L l) (hr0_le _) C.output h
                  rw [hYl_out l hl] at this; cases this)
            exact hnot_smaller C' hm' (by omega) hS' hf'
          · rw [Finset.not_nonempty_iff_eq_empty] at hemp
            obtain ⟨C', hm', hsz', hS', hf'⟩ := elim_smaller_by_valRepl G L C S hmono hS
              ⟨u0, v0, huv0⟩ (by omega) j (by omega)
              (fun _ => Sum.inl false) (fun _ => false)
              (fun _ _ _ => trivial) (fun _ _ _ _ h _ => by cases h) (fun _ _ _ _ _ => rfl)
              (fun u v hadj => by
                obtain ⟨r, hrL, heq, _⟩ := hedge_val u v hadj
                have hrf : val C n (e1 r) (n + j) = false := by
                  cases hv : val C n (e1 r) (n + j) with
                  | false => rfl
                  | true =>
                    have hmem : r ∈ T (n + j) := (hT_mem (n + j) r).mpr ⟨hrL, hv⟩
                    rw [hemp] at hmem; exact absurd hmem (Finset.notMem_empty _)
                rw [valRepl_eq_val_of_eq C n j _ (e2 u v) (by rw [heq, hrf]) C.output]
                exact hEdge_out u v hadj)
              (by
                cases h : valRepl C n j (fun _ => false) (y0 L) C.output with
                | false => rfl
                | true =>
                  have := valRepl_le_val C n j hmono _ (y0 L) (by intro h'; cases h') C.output h
                  rw [hY0_out] at this; cases this)
              (fun l hl => by
                cases h : valRepl C n j (fun _ => false) (yl G L l) C.output with
                | false => rfl
                | true =>
                  have := valRepl_le_val C n j hmono _ (yl G L l) (by intro h'; cases h') C.output h
                  rw [hYl_out l hl] at this; cases this)
            exact hnot_smaller C' hm' (by omega) hS' hf'
        · exact hor
      have hR_disj : ∀ w < n + s, w ∉ S → ∀ x : Fin n → Bool,
          val C n x w = true ↔ ∃ r ∈ T w, x r = true := by
        intro w
        induction w using Nat.strong_induction_on with
        | ind w ih =>
          intro hwlt hwS x
          by_cases hwn : w < n
          · have hnotL : (⟨w, hwn⟩ : Fin n) ∉ L := fun hL => hwS ((hS_in w hwn).mpr hL)
            rw [val_input C x w hwn]
            constructor
            · intro hx
              exact ⟨⟨w, hwn⟩, (hT_mem w ⟨w, hwn⟩).mpr ⟨hnotL, by rw [val_input C _ w hwn]; simp [e1]⟩, hx⟩
            · rintro ⟨r, hrT, hxr⟩
              obtain ⟨_, hrv⟩ := (hT_mem w r).mp hrT
              rw [val_input C _ w hwn] at hrv
              simp only [e1, decide_eq_true_eq] at hrv
              rw [hrv]; exact hxr
          · set j := w - n
            have hwj : w = n + j := by omega
            have hjlt : j < s := by omega
            have hg : C.gates[j]? = some (C.gates[j]' (by omega)) := List.getElem?_eq_getElem (by omega)
            set g := C.gates[j]' (by omega)
            have hwjS : n + j ∉ S := hwj ▸ hwS
            have hor := hR_or j hjlt hwjS g hg
            rw [hwj, val_or C x j g hg hor]
            constructor
            · rintro ⟨u, hu_mem, hu_lt, hux⟩
              have huS : u ∉ S := fun huin => hwjS (hS.2.1 j g hg u hu_mem hu_lt huin)
              obtain ⟨r, hrT, hxr⟩ := (ih u (by omega) (by omega) huS x).mp hux
              obtain ⟨hrL, hrv⟩ := (hT_mem u r).mp hrT
              exact ⟨r, (hT_mem (n + j) r).mpr ⟨hrL, (val_or C (e1 r) j g hg hor).mpr ⟨u, hu_mem, hu_lt, hrv⟩⟩, hxr⟩
            · rintro ⟨r, hrT, hxr⟩
              obtain ⟨hrL, hrv⟩ := (hT_mem (n + j) r).mp hrT
              obtain ⟨u, hu_mem, hu_lt, huv⟩ := (val_or C (e1 r) j g hg hor).mp hrv
              have huS : u ∉ S := fun huin => hwjS (hS.2.1 j g hg u hu_mem hu_lt huin)
              exact ⟨u, hu_mem, hu_lt, (ih u (by omega) (by omega) huS x).mpr ⟨r, (hT_mem u r).mpr ⟨hrL, huv⟩, hxr⟩⟩
      have hR_yl_iff : ∀ w < n + s, w ∉ S → ∀ l ∈ L,
          val C n (yl G L l) w = false ↔ ∀ r ∈ T w, G.Adj l r := by
        intro w hwlt hwS l hl
        rw [← Bool.not_eq_true, hR_disj w hwlt hwS (yl G L l)]
        push Not
        constructor
        · intro hall r hrT
          have hrL := ((hT_mem w r).mp hrT).1
          have hrf := hall r hrT
          by_contra hna
          have : yl G L l r = true := by simp only [yl, decide_eq_true_eq]; exact Or.inr ⟨hrL, fun h => hna h.symm⟩
          exact hrf this
        · intro hall r hrT hyl
          have hrL := ((hT_mem w r).mp hrT).1
          simp only [yl, decide_eq_true_eq] at hyl
          rcases hyl with rfl | ⟨_, hna⟩
          · exact hrL hl
          · exact hna (hall r hrT).symm
      have hR_ge2 : ∀ j < s, n + j ∉ S → 2 ≤ (T (n + j)).card := by
        intro j hj hwS
        have hne : (T (n + j)).Nonempty := by
          by_contra h
          rw [Finset.not_nonempty_iff_eq_empty] at h
          apply (hno_const_copy j hj).1
          intro x
          cases hv : val C n x (n + j) with
          | false => rfl
          | true =>
            obtain ⟨r, hr, _⟩ := (hR_disj (n + j) (by omega) hwS x).mp hv
            rw [h] at hr; exact absurd hr (Finset.notMem_empty _)
        by_contra hlt2
        have hcard1 : (T (n + j)).card = 1 := by
          have hpos := Finset.card_pos.mpr hne; omega
        obtain ⟨r0, hr0eq⟩ := Finset.card_eq_one.mp hcard1
        have hr0L : r0 ∉ L := ((hT_mem (n + j) r0).mp (hr0eq ▸ Finset.mem_singleton_self r0)).1
        have hr0_notS : r0.val ∉ S := fun h => hr0L ((hS_in r0.val r0.isLt).mp h)
        apply (hno_const_copy j hj).2.2 r0.val (by omega) (fun h => absurd h hr0_notS)
        intro x
        rw [val_input C x r0.val r0.isLt, Bool.eq_iff_iff, hR_disj (n + j) (by omega) hwS x]
        simp [hr0eq]
      have hS_y0 : ∀ w < n + s, w ∈ S → val C n (y0 L) w = false := by
        intro w hwlt hwS
        by_contra hne
        have hwt : val C n (y0 L) w = true := by cases h : val C n (y0 L) w <;> simp [h] at hne ⊢
        have hstep_up : ∀ d : ℕ, ∀ w0 < n + s, n + s - w0 ≤ d → w0 ∈ S → val C n (y0 L) w0 = true → False := by
          intro d
          induction d with
          | zero => intro w0 hw0 hd; omega
          | succ d ih =>
            intro w0 hw0 hd hw0S hw0t
            by_cases hwn : w0 < n
            · rw [val_input C _ w0 hwn] at hw0t
              simp only [y0, decide_eq_true_eq] at hw0t
              exact hw0t ((hS_in w0 hwn).mp hw0S)
            · set k := w0 - n
              have hwk : w0 = n + k := by omega
              by_cases hko : k = o
              · rw [hwk, hko, ← ho_eq, hY0_out] at hw0t; cases hw0t
              · obtain ⟨j, hjlt, g, hg, hkj, hmem⟩ := hused k (by omega) hko
                have hjS : n + j ∈ S := hS.2.1 j g hg (n + k) hmem (by omega) (hwk ▸ hw0S)
                have hgop : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using (hmono g (List.mem_of_getElem? hg)).1
                have hjt : val C n (y0 L) (n + j) = true := by
                  rcases hgop with hand | hor
                  · obtain ⟨a, b, hinp, ha_lt, hb_lt, hab⟩ := hshape j hjlt g hg
                    refine (val_and C _ j g hg hand).mpr ?_
                    intro u hu
                    rw [hinp] at hu hmem
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hmem
                    rcases hmem with h1 | h1
                    · rcases hu with hu1 | hu2
                      · rw [hu1]; exact ⟨ha_lt, h1 ▸ hwk ▸ hw0t⟩
                      · rw [hu2]
                        have hb_notS : b ∉ S := fun hbS =>
                          hS.2.2 j g hg hand a b hinp ha_lt hb_lt ⟨h1 ▸ hwk ▸ hw0S, hbS⟩
                        exact ⟨hb_lt, hR_y0 b (by omega) hb_notS⟩
                    · rcases hu with hu1 | hu2
                      · rw [hu1]
                        have ha_notS : a ∉ S := fun haS =>
                          hS.2.2 j g hg hand a b hinp ha_lt hb_lt ⟨haS, h1 ▸ hwk ▸ hw0S⟩
                        exact ⟨ha_lt, hR_y0 a (by omega) ha_notS⟩
                      · rw [hu2]; exact ⟨hb_lt, h1 ▸ hwk ▸ hw0t⟩
                  · exact (val_or C _ j g hg hor).mpr ⟨n + k, hmem, by omega, hwk ▸ hw0t⟩
                exact ih (n + j) (by omega) (by omega) hjS hjt
        exact hstep_up (n + s) w hwlt (by omega) hwS hwt
      have hout_S : n + o ∈ S := by
        by_contra hnot
        have := hR_y0 (n + o) (by omega) hnot
        rw [← ho_eq, hY0_out] at this; cases this
      have hSOR_both : ∀ j < s, n + j ∈ S → ∀ g, C.gates[j]? = some g → g.op = GateOp.or →
          ∀ i ∈ g.inputs, i ∈ S := by
        intro j hj hjS g hg hor i hi
        obtain ⟨a, b, hinp, ha_lt, hb_lt, _⟩ := hshape j hj g hg
        have hilt : i < n + j := by rw [hinp] at hi; simp at hi; rcases hi with rfl | rfl <;> omega
        by_contra hi_notS
        have hit : val C n (y0 L) i = true := hR_y0 i (by omega) hi_notS
        have hjt : val C n (y0 L) (n + j) = true := (val_or C _ j g hg hor).mpr ⟨i, hi, hilt, hit⟩
        rw [hS_y0 (n + j) (by omega) hjS] at hjt; cases hjt
      have hSAND_split : ∀ j < s, n + j ∈ S → ∀ g, C.gates[j]? = some g → g.op = GateOp.and →
          ∃ sW rW, (g.inputs = [sW, rW] ∨ g.inputs = [rW, sW]) ∧ sW < n + j ∧ rW < n + j ∧ sW ∈ S ∧ rW ∉ S := by
        intro j hj hjS g hg hand
        obtain ⟨a, b, hinp, ha_lt, hb_lt, _⟩ := hshape j hj g hg
        obtain ⟨i, hi, _, hiS⟩ := (hS_gate j g hg).mp hjS
        rw [hinp] at hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with hi1 | hi2
        · rw [hi1] at hiS
          have hb_notS : b ∉ S := fun hbS => hS.2.2 j g hg hand a b hinp ha_lt hb_lt ⟨hiS, hbS⟩
          exact ⟨a, b, Or.inl hinp, ha_lt, hb_lt, hiS, hb_notS⟩
        · rw [hi2] at hiS
          have ha_notS : a ∉ S := fun haS => hS.2.2 j g hg hand a b hinp ha_lt hb_lt ⟨haS, hiS⟩
          exact ⟨b, a, Or.inr hinp, hb_lt, ha_lt, hiS, ha_notS⟩
      set Alive : ℕ → Finset (Fin n) := fun w => L.filter (fun l => val C n (yl G L l) w = true)
      have hAlive_mem : ∀ w l, l ∈ Alive w ↔ l ∈ L ∧ val C n (yl G L l) w = true := by
        intro w l; simp [Alive]
      have hAlive_in_eq : ∀ w (hw : w < n), w ∈ S → Alive w = {⟨w, hw⟩} := by
        intro w hw hwS
        have hwL : (⟨w, hw⟩ : Fin n) ∈ L := (hS_in w hw).mp hwS
        ext l; rw [hAlive_mem, Finset.mem_singleton, val_input C _ w hw]
        simp only [yl, decide_eq_true_eq]
        constructor
        · rintro ⟨_, h1 | ⟨hnotL, _⟩⟩
          · exact h1.symm
          · exact absurd hwL hnotL
        · rintro rfl; exact ⟨hwL, Or.inl rfl⟩
      have hAlive_out : Alive (n + o) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro l hl
        obtain ⟨hlL, hlt⟩ := (hAlive_mem (n + o) l).mp hl
        rw [← ho_eq, hYl_out l hlL] at hlt; cases hlt
      have hAlive_or : ∀ j < s, n + j ∈ S → ∀ g, C.gates[j]? = some g → g.op = GateOp.or →
          ∃ a b, g.inputs = [a, b] ∧ a < n + j ∧ b < n + j ∧ a ∈ S ∧ b ∈ S ∧ Alive (n + j) = Alive a ∪ Alive b := by
        intro j hj hjS g hg hor
        obtain ⟨a, b, hinp, ha_lt, hb_lt, _⟩ := hshape j hj g hg
        have haS : a ∈ S := hSOR_both j hj hjS g hg hor a (by rw [hinp]; simp)
        have hbS : b ∈ S := hSOR_both j hj hjS g hg hor b (by rw [hinp]; simp)
        refine ⟨a, b, hinp, ha_lt, hb_lt, haS, hbS, ?_⟩
        ext l; rw [hAlive_mem, Finset.mem_union, hAlive_mem, hAlive_mem, val_or C _ j g hg hor]
        rw [hinp]
        constructor
        · rintro ⟨hlL, u, hu, _, huv⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
          rcases hu with rfl | rfl
          · exact Or.inl ⟨hlL, huv⟩
          · exact Or.inr ⟨hlL, huv⟩
        · rintro (⟨hlL, ha⟩ | ⟨hlL, hb⟩)
          · exact ⟨hlL, a, by simp, ha_lt, ha⟩
          · exact ⟨hlL, b, by simp, hb_lt, hb⟩
      have hAlive_and_sub : ∀ j < s, n + j ∈ S → ∀ g, C.gates[j]? = some g → g.op = GateOp.and →
          ∀ sW rW, (g.inputs = [sW, rW] ∨ g.inputs = [rW, sW]) → sW < n + j → rW < n + j →
          sW ∈ S → rW ∉ S →
          ∀ l, l ∈ Alive (n + j) ↔ l ∈ Alive sW ∧ ¬ (∀ r ∈ T rW, G.Adj l r) := by
        intro j hj hjS g hg hand sW rW hinp hsW_lt hrW_lt hsW_S hrW_notS l
        rw [hAlive_mem, hAlive_mem, val_and C _ j g hg hand]
        constructor
        · rintro ⟨hlL, hall⟩
          have hsW_t : val C n (yl G L l) sW = true := (hall sW (by rcases hinp with h | h <;> rw [h] <;> simp)).2
          have hrW_t : val C n (yl G L l) rW = true := (hall rW (by rcases hinp with h | h <;> rw [h] <;> simp)).2
          refine ⟨⟨hlL, hsW_t⟩, ?_⟩
          intro hall_adj
          have := (hR_yl_iff rW (by omega) hrW_notS l hlL).mpr hall_adj
          rw [hrW_t] at this; cases this
        · rintro ⟨⟨hlL, hsW_t⟩, hnot_adj⟩
          have hrW_t : val C n (yl G L l) rW = true := by
            cases hv : val C n (yl G L l) rW with
            | true => rfl
            | false => exact absurd ((hR_yl_iff rW (by omega) hrW_notS l hlL).mp hv) hnot_adj
          refine ⟨hlL, ?_⟩
          intro u hu
          rcases hinp with h | h <;> rw [h] at hu <;> simp at hu <;> rcases hu with rfl | rfl
          · exact ⟨hsW_lt, hsW_t⟩
          · exact ⟨hrW_lt, hrW_t⟩
          · exact ⟨hrW_lt, hrW_t⟩
          · exact ⟨hsW_lt, hsW_t⟩
      have hSAND_multi : ∀ j < s, n + j ∈ S → ∀ g, C.gates[j]? = some g → g.op = GateOp.and →
          ∀ sW rW, (g.inputs = [sW, rW] ∨ g.inputs = [rW, sW]) → sW < n + j → rW < n + j →
          sW ∈ S → rW ∉ S → 2 ≤ (Alive sW).card →
          ∃ r0 : Fin n, r0 ∉ L ∧ rW = r0.val ∧ (∀ l' ∈ Alive sW, G.Adj l' r0) := by
        intro j hj hjS g hg hand sW rW hinp hsW_lt hrW_lt hsW_S hrW_notS hcard2
        have hneed : ∃ l r : Fin n, l ∈ L ∧ r ∉ L ∧ G.Adj l r ∧
            valRepl C n j (fun _ => false) (e2 l r) C.output = false := by
          by_contra hno
          push Not at hno
          have hEdge_k : ∀ u v : Fin n, G.Adj u v → valRepl C n j (fun _ => false) (e2 u v) C.output = true := by
            intro u v hadj
            by_cases huL : u ∈ L
            · have hvL := (hBip u v hadj).mp huL
              cases hv : valRepl C n j (fun _ => false) (e2 u v) C.output with
              | true => rfl
              | false => exact absurd hv (hno u v huL hvL hadj)
            · have hvL : v ∈ L := by by_contra h; exact huL ((hBip u v hadj).mpr h)
              have hsw : e2 u v = e2 v u := by funext i; simp [e2, or_comm]
              rw [hsw]
              cases hv : valRepl C n j (fun _ => false) (e2 v u) C.output with
              | true => rfl
              | false => exact absurd hv (hno v u hvL huL hadj.symm)
          obtain ⟨C', hm', hsz', hS', hf'⟩ := elim_smaller_by_valRepl G L C S hmono hS
            ⟨u0, v0, huv0⟩ (by omega) j (by omega)
            (fun _ => Sum.inl false) (fun _ => false)
            (fun _ _ _ => trivial) (fun _ _ _ _ h _ => by cases h) (fun _ _ _ _ _ => rfl)
            hEdge_k
            (by
              cases h : valRepl C n j (fun _ => false) (y0 L) C.output with
              | false => rfl
              | true =>
                have := valRepl_le_val C n j hmono _ (y0 L) (by intro h'; cases h') C.output h
                rw [hY0_out] at this; cases this)
            (fun l hl => by
              cases h : valRepl C n j (fun _ => false) (yl G L l) C.output with
              | false => rfl
              | true =>
                have := valRepl_le_val C n j hmono _ (yl G L l) (by intro h'; cases h') C.output h
                rw [hYl_out l hl] at this; cases this)
          exact hnot_smaller C' hm' (by omega) hS' hf'
        have hall_adj : ∀ l r : Fin n, l ∈ L → r ∉ L → G.Adj l r →
            valRepl C n j (fun _ => false) (e2 l r) C.output = false →
            ∀ l' ∈ Alive sW, G.Adj l' r := by
          intro l r hl hr hadj hkf l' hl'
          obtain ⟨hl'L, hl'v⟩ := (hAlive_mem sW l').mp hl'
          by_contra hna
          have hsW_mem : sW ∈ g.inputs := by rcases hinp with h | h <;> rw [h] <;> simp
          have hrW_mem : rW ∈ g.inputs := by rcases hinp with h | h <;> rw [h] <;> simp
          have hylt := super_killer G L C S hmono hS j hjS g hg hand sW rW
            hsW_mem hrW_mem hsW_lt hrW_lt hsW_S hrW_notS l l' r hl hr hna hl'v
            C.output (hEdge_out l r hadj) hkf
          rw [hYl_out l' hl'L] at hylt; cases hylt
        obtain ⟨l0, r0, hl0, hr0, hadj0, hkf0⟩ := hneed
        have hadj_r0 : ∀ l' ∈ Alive sW, G.Adj l' r0 := hall_adj l0 r0 hl0 hr0 hadj0 hkf0
        obtain ⟨l1, hl1, l2, hl2, hl12⟩ := Finset.one_lt_card.mp (by omega : 1 < (Alive sW).card)
        have huniq_r : ∀ l r : Fin n, l ∈ L → r ∉ L → G.Adj l r →
            valRepl C n j (fun _ => false) (e2 l r) C.output = false → r = r0 := by
          intro l r hl hr hadj hkf
          by_contra hne
          exact hNoC4 l1 l2 r r0 hl12 hne
            (hall_adj l r hl hr hadj hkf l1 hl1) (hadj_r0 l1 hl1)
            (hall_adj l r hl hr hadj hkf l2 hl2) (hadj_r0 l2 hl2)
        have hj_true0 : val C n (e2 l0 r0) (n + j) = true := by
          cases hv : val C n (e2 l0 r0) (n + j) with
          | true => rfl
          | false =>
            have := valRepl_eq_val_of_eq C n j (fun _ => false) (e2 l0 r0) hv.symm C.output
            rw [hkf0, hEdge_out l0 r0 hadj0] at this; cases this
        have hr0_in_T : r0 ∈ T rW := by
          have hrW_mem : rW ∈ g.inputs := by rcases hinp with h | h <;> rw [h] <;> simp
          have hrW_t : val C n (e2 l0 r0) rW = true := ((val_and C _ j g hg hand).mp hj_true0 rW hrW_mem).2
          have hrW_e1 : val C n (e1 r0) rW = true := by
            rw [← val_indep_of_not_inS L C S hS (e2 l0 r0) (e1 r0)
              (fun v hv => by have hvl : v ≠ l0 := fun h => hv (h ▸ hl0); simp [e2, e1, hvl]) rW hrW_notS]
            exact hrW_t
          exact (hT_mem rW r0).mpr ⟨hr0, hrW_e1⟩
        by_cases hrW_lt_n : rW < n
        · have hrW_eq : rW = r0.val := by
            have hr0_v := ((hT_mem rW r0).mp hr0_in_T).2
            rw [val_input C _ rW hrW_lt_n] at hr0_v
            simp only [e1, decide_eq_true_eq] at hr0_v
            exact congrArg Fin.val hr0_v
          exact ⟨r0, hr0, hrW_eq, hadj_r0⟩
        · exfalso
          set g' : Gate := ⟨GateOp.and, [sW, r0.val]⟩
          set C' : Circuit := ⟨C.gates.set j g', C.output⟩
          have hC'sz : C'.size = s := by change (C.gates.set j g').length = s; simp [hCglen]
          have hC'big : bigInputCount n C' < m := by
            rw [← hCbig]
            apply bigInputCount_set_lt n C j (by omega) g'
            have hgetj : C.gates[j]'(by omega) = g := by
              have h1 := List.getElem?_eq_getElem (by omega : j < C.gates.length)
              rw [h1] at hg; exact Option.some.inj hg
            rw [hgetj]
            have hr0_lt_n : ¬ n ≤ r0.val := by omega
            have hrW_ge_n : n ≤ rW := by omega
            rcases hinp with h | h <;> rw [h]
            · simp only [g', List.countP_cons, List.countP_nil, hr0_lt_n, hrW_ge_n, decide_false, decide_true]
              by_cases hsn : n ≤ sW <;> simp [hsn]
            · simp only [g', List.countP_cons, List.countP_nil, hr0_lt_n, hrW_ge_n, decide_false, decide_true]
              by_cases hsn : n ≤ sW <;> simp [hsn]
          have hC'mono : Monotone2 C' := by
            intro g1 hg1
            obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hg1
            have hidxC : idx < C.gates.length := by simpa [C'] using hidx
            by_cases hidxj : idx = j
            · subst hidxj
              have : (C.gates.set idx g')[idx]'hidx = g' := List.getElem_set_self _
              rw [this]; exact ⟨by simp [g'], by simp [g']⟩
            · have : (C.gates.set j g')[idx]'hidx = C.gates[idx]'hidxC := List.getElem_set_ne (Ne.symm hidxj) _
              rw [this]; exact hmono _ (List.getElem_mem _)
          have hr0_notS : r0.val ∉ S := fun h => hr0 ((hS_in r0.val r0.isLt).mp h)
          have hC'S : ValidS L C' S := by
            refine ⟨hS.1, ?_, ?_⟩
            · intro j1 g1 hg1 i hi hilt hiS
              by_cases hj1 : j1 = j
              · subst hj1
                have : g1 = g' := by
                  have h1 : (C.gates.set j1 g')[j1]? = some g' := by simp [List.getElem?_set_self (by omega : j1 < C.gates.length)]
                  change (C.gates.set j1 g')[j1]? = some g1 at hg1
                  rw [h1] at hg1; exact (Option.some.inj hg1).symm
                subst this; exact hjS
              · change (C.gates.set j g')[j1]? = some g1 at hg1
                rw [List.getElem?_set_ne (Ne.symm hj1)] at hg1
                exact hS.2.1 j1 g1 hg1 i hi hilt hiS
            · intro j1 g1 hg1 hop1 a1 b1 hab1 ha1 hb1 hboth
              by_cases hj1 : j1 = j
              · subst hj1
                have : g1 = g' := by
                  have h1 : (C.gates.set j1 g')[j1]? = some g' := by simp [List.getElem?_set_self (by omega : j1 < C.gates.length)]
                  change (C.gates.set j1 g')[j1]? = some g1 at hg1
                  rw [h1] at hg1; exact (Option.some.inj hg1).symm
                subst this
                simp only [g', List.cons.injEq, and_true] at hab1
                obtain ⟨rfl, rfl⟩ := hab1
                exact hr0_notS hboth.2
              · change (C.gates.set j g')[j1]? = some g1 at hg1
                rw [List.getElem?_set_ne (Ne.symm hj1)] at hg1
                exact hS.2.2 j1 g1 hg1 hop1 a1 b1 hab1 ha1 hb1 hboth
          have hf_eq : ∀ x, g'.op.eval (g'.inputs.map fun i => if i < n + j then val C n x i else false) =
              (val C n x sW && x r0) := by
            intro x
            have hr0_ltj : r0.val < n + j := by omega
            simp [g', GateOp.eval, hsW_lt, hr0_ltj, val_input C x r0.val r0.isLt]
          have hf_le : ∀ x, (val C n x sW && x r0) = true → val C n x (n + j) = true := by
            intro x hx
            rw [Bool.and_eq_true] at hx
            have hrW_t : val C n x rW = true := (hR_disj rW (by omega) hrW_notS x).mpr ⟨r0, hr0_in_T, hx.2⟩
            refine (val_and C x j g hg hand).mpr ?_
            intro u hu
            rcases hinp with h | h <;> rw [h] at hu <;> simp at hu <;> rcases hu with rfl | rfl
            · exact ⟨hsW_lt, hx.1⟩
            · exact ⟨hrW_lt, hrW_t⟩
            · exact ⟨hrW_lt, hrW_t⟩
            · exact ⟨hsW_lt, hx.1⟩
          have hC'val : ∀ x, val C' n x C'.output = valRepl C n j (fun z => val C n z sW && z r0) x C.output := by
            intro x
            have h1 := set_gate_val C j (by omega) g' C' rfl x C.output
            convert h1 using 2
            funext z; exact (hf_eq z).symm
          have hC'fun := bipartite_test_iff G L C' S hC'mono hC'S
            (fun u v hadj => by
              rw [hC'val]
              by_cases huL : u ∈ L
              · have hvL := (hBip u v hadj).mp huL
                by_cases hvr0 : v = r0
                · rw [hvr0]
                  have hfeq : (val C n (e2 u r0) sW && e2 u r0 r0) = val C n (e2 u r0) (n + j) := by
                    rw [Bool.eq_iff_iff, Bool.and_eq_true]
                    constructor
                    · exact fun h => hf_le _ ((Bool.and_eq_true _ _).mpr h)
                    · intro h
                      have hsW_mem : sW ∈ g.inputs := by rcases hinp with h' | h' <;> rw [h'] <;> simp
                      exact ⟨((val_and C _ j g hg hand).mp h sW hsW_mem).2, by simp [e2]⟩
                  rw [valRepl_eq_val_of_eq C n j _ (e2 u r0) hfeq C.output]
                  exact hEdge_out u r0 (hvr0 ▸ hadj)
                · have hkt : valRepl C n j (fun _ => false) (e2 u v) C.output = true := by
                    cases hk : valRepl C n j (fun _ => false) (e2 u v) C.output with
                    | true => rfl
                    | false => exact absurd (huniq_r u v huL hvL hadj hk) hvr0
                  have hmon : ∀ w, valRepl C n j (fun _ => false) (e2 u v) w = true →
                      valRepl C n j (fun z => val C n z sW && z r0) (e2 u v) w = true := by
                    intro w
                    induction w using Nat.strong_induction_on with
                    | ind w ih =>
                      intro hw
                      by_cases hwn : w < n
                      · rw [valRepl_input _ _ _ _ _ w hwn] at hw ⊢; exact hw
                      · set k := w - n
                        have hwk : w = n + k := by omega
                        rw [hwk] at hw ⊢
                        by_cases hkj : k = j
                        · subst hkj; rw [valRepl_j0] at hw; cases hw
                        · cases hgk : C.gates[k]? with
                          | none => rw [valRepl_none_ne _ _ _ _ _ k hkj hgk] at hw; cases hw
                          | some gk =>
                            rw [valRepl_gate_ne _ _ _ _ _ k hkj gk hgk] at hw ⊢
                            have hkop : gk.op = GateOp.and ∨ gk.op = GateOp.or := by
                              simpa using (hmono gk (List.mem_of_getElem? hgk)).1
                            apply gateOp_mono gk.op hkop _ _ _ ?_ hw
                            intro i _ hi
                            by_cases hilt : i < n + k
                            · simp only [hilt, ↓reduceIte] at hi ⊢; exact ih i (by omega) hi
                            · simp only [hilt, ↓reduceIte] at hi; cases hi
                  exact hmon C.output hkt
              · have hvL : v ∈ L := by by_contra h; exact huL ((hBip u v hadj).mpr h)
                have hsw : e2 u v = e2 v u := by funext i; simp [e2, or_comm]
                rw [hsw]
                by_cases hur0 : u = r0
                · rw [hur0]
                  have hfeq : (val C n (e2 v r0) sW && e2 v r0 r0) = val C n (e2 v r0) (n + j) := by
                    rw [Bool.eq_iff_iff, Bool.and_eq_true]
                    constructor
                    · exact fun h => hf_le _ ((Bool.and_eq_true _ _).mpr h)
                    · intro h
                      have hsW_mem : sW ∈ g.inputs := by rcases hinp with h' | h' <;> rw [h'] <;> simp
                      exact ⟨((val_and C _ j g hg hand).mp h sW hsW_mem).2, by simp [e2]⟩
                  rw [valRepl_eq_val_of_eq C n j _ (e2 v r0) hfeq C.output]
                  exact hEdge_out v r0 (hur0 ▸ hadj.symm)
                · have hkt : valRepl C n j (fun _ => false) (e2 v u) C.output = true := by
                    cases hk : valRepl C n j (fun _ => false) (e2 v u) C.output with
                    | true => rfl
                    | false => exact absurd (huniq_r v u hvL huL hadj.symm hk) hur0
                  have hmon : ∀ w, valRepl C n j (fun _ => false) (e2 v u) w = true →
                      valRepl C n j (fun z => val C n z sW && z r0) (e2 v u) w = true := by
                    intro w
                    induction w using Nat.strong_induction_on with
                    | ind w ih =>
                      intro hw
                      by_cases hwn : w < n
                      · rw [valRepl_input _ _ _ _ _ w hwn] at hw ⊢; exact hw
                      · set k := w - n
                        have hwk : w = n + k := by omega
                        rw [hwk] at hw ⊢
                        by_cases hkj : k = j
                        · subst hkj; rw [valRepl_j0] at hw; cases hw
                        · cases hgk : C.gates[k]? with
                          | none => rw [valRepl_none_ne _ _ _ _ _ k hkj hgk] at hw; cases hw
                          | some gk =>
                            rw [valRepl_gate_ne _ _ _ _ _ k hkj gk hgk] at hw ⊢
                            have hkop : gk.op = GateOp.and ∨ gk.op = GateOp.or := by
                              simpa using (hmono gk (List.mem_of_getElem? hgk)).1
                            apply gateOp_mono gk.op hkop _ _ _ ?_ hw
                            intro i _ hi
                            by_cases hilt : i < n + k
                            · simp only [hilt, ↓reduceIte] at hi ⊢; exact ih i (by omega) hi
                            · simp only [hilt, ↓reduceIte] at hi; cases hi
                  exact hmon C.output hkt)
            (by
              rw [hC'val]
              cases h : valRepl C n j (fun z => val C n z sW && z r0) (y0 L) C.output with
              | false => rfl
              | true =>
                have := valRepl_le_val C n j hmono _ (y0 L) (hf_le _) C.output h
                rw [hY0_out] at this; cases this)
            (fun l hl => by
              rw [hC'val]
              cases h : valRepl C n j (fun z => val C n z sW && z r0) (yl G L l) C.output with
              | false => rfl
              | true =>
                have := valRepl_le_val C n j hmono _ (yl G L l) (hf_le _) C.output h
                rw [hYl_out l hl] at this; cases this)
          exact hnot_less_big C' hC'mono hC'sz hC'big ⟨S, hC'S⟩ hC'fun
      have hAlive_and_lt2 : ∀ j < s, n + j ∈ S → ∀ g, C.gates[j]? = some g → g.op = GateOp.and →
          (Alive (n + j)).card < 2 := by
        intro j hj hjS g hg hand
        obtain ⟨sW, rW, hinp, hsW_lt, hrW_lt, hsW_S, hrW_notS⟩ := hSAND_split j hj hjS g hg hand
        by_cases h2 : 2 ≤ (Alive sW).card
        · obtain ⟨r0, hr0L, rfl, hadj_r0⟩ := hSAND_multi j hj hjS g hg hand sW rW hinp hsW_lt hrW_lt hsW_S hrW_notS h2
          have hemp : Alive (n + j) = ∅ := by
            apply Finset.eq_empty_of_forall_notMem
            intro l hl
            obtain ⟨hlA, hna⟩ := (hAlive_and_sub j hj hjS g hg hand sW r0.val hinp hsW_lt hrW_lt hsW_S hrW_notS l).mp hl
            apply hna
            intro r hrT
            have hrv := ((hT_mem r0.val r).mp hrT).2
            rw [val_input C _ r0.val r0.isLt] at hrv
            simp only [e1, decide_eq_true_eq] at hrv
            rw [← hrv]; exact hadj_r0 l hlA
          rw [hemp]; simp
        · have hsub : Alive (n + j) ⊆ Alive sW := by
            intro l hl
            exact ((hAlive_and_sub j hj hjS g hg hand sW rW hinp hsW_lt hrW_lt hsW_S hrW_notS l).mp hl).1
          have := Finset.card_le_card hsub; omega
      set UR : Finset ℕ := (Finset.range s).filter (fun j => n + j ∉ S)
      set US : Finset ℕ := (Finset.range s).filter (fun j => n + j ∈ S)
      set USAnd : Finset ℕ := US.filter (fun j => ∃ g, C.gates[j]? = some g ∧ g.op = GateOp.and)
      set USOr : Finset ℕ := US.filter (fun j => ∃ g, C.gates[j]? = some g ∧ g.op = GateOp.or)
      have hUS_split : USAnd.card + USOr.card = US.card := by
        have heq : USOr = US.filter (fun j => ¬ ∃ g, C.gates[j]? = some g ∧ g.op = GateOp.and) := by
          ext j; simp only [USOr, US, Finset.mem_filter, Finset.mem_range]
          constructor
          · rintro ⟨⟨hj, hjS⟩, g, hg, hor⟩
            refine ⟨⟨hj, hjS⟩, ?_⟩
            rintro ⟨g', hg', hand⟩
            rw [hg] at hg'; cases Option.some.inj hg'; rw [hor] at hand; cases hand
          · rintro ⟨⟨hj, hjS⟩, hnot⟩
            have hg : C.gates[j]? = some (C.gates[j]'(by omega)) := List.getElem?_eq_getElem (by omega)
            have hgop : (C.gates[j]'(by omega)).op = GateOp.and ∨ (C.gates[j]'(by omega)).op = GateOp.or := by
              simpa using (hmono _ (List.mem_of_getElem? hg)).1
            rcases hgop with hand | hor
            · exact absurd ⟨_, hg, hand⟩ hnot
            · exact ⟨⟨hj, hjS⟩, _, hg, hor⟩
        rw [heq]
        exact Finset.card_filter_add_card_filter_not (s := US) _
      have hU_total : UR.card + US.card = s := by
        have h := Finset.card_filter_add_card_filter_not (s := Finset.range s) (fun j => n + j ∈ S)
        rw [Finset.card_range] at h
        change US.card + UR.card = s at h
        omega
      have hoUS : o ∈ US := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ho_lt, hout_S⟩
      set E : Finset (Fin n × Fin n) := (L ×ˢ (Finset.univ \ L)).filter (fun p => G.Adj p.1 p.2)
      set EL : Finset (Fin n × Fin n) := E.filter (fun p =>
        ∃ j ∈ USAnd, ∃ g, C.gates[j]? = some g ∧ g.op = GateOp.and ∧
          ∃ sW rW, (g.inputs = [sW, rW] ∨ g.inputs = [rW, sW]) ∧ sW < n + j ∧ rW < n + j ∧
            sW ∈ S ∧ rW ∉ S ∧ n ≤ rW ∧ p.2 ∈ T rW ∧ (∀ r ∈ T rW, G.Adj p.1 r) ∧ p.1 ∈ Alive sW)
      set ER : Finset (Fin n × Fin n) := E \ EL
      have hE_split : EL.card + ER.card = E.card := by
        have hsub : EL ⊆ E := Finset.filter_subset _ _
        have h := Finset.card_sdiff_add_card_eq_card hsub
        change ER.card + EL.card = E.card at h
        omega
      set CL : Finset (Fin n) := EL.image Prod.fst
      set CR : Finset (Fin n) := ER.image Prod.snd
      have hVC : τ ≤ CL.card + CR.card := by
        have hdisj : Disjoint CL CR := by
          rw [Finset.disjoint_left]
          intro x hxL hxR
          obtain ⟨p1, hp1, rfl⟩ := Finset.mem_image.mp hxL
          obtain ⟨p2, hp2, hp2eq⟩ := Finset.mem_image.mp hxR
          have h1 : p1.1 ∈ L := (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.filter_subset _ _ hp1)).1).1
          have h2 : p2.2 ∉ L := (Finset.mem_sdiff.mp (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.sdiff_subset hp2)).1).2).2
          exact h2 (hp2eq ▸ h1)
        rw [← Finset.card_union_of_disjoint hdisj]
        apply hTau
        intro u v hadj
        by_cases huL : u ∈ L
        · have hvL := (hBip u v hadj).mp huL
          have hpE : (u, v) ∈ E := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨huL, Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hvL⟩⟩, hadj⟩
          by_cases hpEL : (u, v) ∈ EL
          · exact Or.inl (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(u, v), hpEL, rfl⟩))
          · exact Or.inr (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(u, v), Finset.mem_sdiff.mpr ⟨hpE, hpEL⟩, rfl⟩))
        · have hvL : v ∈ L := by by_contra h; exact huL ((hBip u v hadj).mpr h)
          have hpE : (v, u) ∈ E := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hvL, Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, huL⟩⟩, hadj.symm⟩
          by_cases hpEL : (v, u) ∈ EL
          · exact Or.inr (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(v, u), hpEL, rfl⟩))
          · exact Or.inl (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(v, u), Finset.mem_sdiff.mpr ⟨hpE, hpEL⟩, rfl⟩))
      have hER_crit : ∀ p ∈ ER, ∃ j ∈ USAnd, ∃ g, C.gates[j]? = some g ∧ g.op = GateOp.and ∧
          ∃ sW, (g.inputs = [sW, p.2.val] ∨ g.inputs = [p.2.val, sW]) ∧ sW < n + j ∧ sW ∈ S ∧ p.1 ∈ Alive sW := by
        intro p hpER
        have hpE := Finset.sdiff_subset hpER
        have hpNotEL := (Finset.mem_sdiff.mp hpER).2
        have hp1L : p.1 ∈ L := (Finset.mem_product.mp (Finset.mem_filter.mp hpE).1).1
        have hp2L : p.2 ∉ L := (Finset.mem_sdiff.mp (Finset.mem_product.mp (Finset.mem_filter.mp hpE).1).2).2
        have hadj : G.Adj p.1 p.2 := (Finset.mem_filter.mp hpE).2
        obtain ⟨j, hjlt, hjS, g, hg, hand, sW, rW, hinp, hsW_lt, hrW_lt, hsW_S, hrW_notS, _, hrW_e, hsW_y, hrW_y⟩ :=
          er_crit_trace G L C S hmono hS_in
            (fun j hj => hSOR_both j (by omega))
            (fun j hj => hSAND_split j (by omega))
            p.1 p.2 hp2L (n + o) (by omega) hout_S
            (by rw [← ho_eq]; exact hEdge_out p.1 p.2 hadj)
            (by rw [← ho_eq]; exact hYl_out p.1 hp1L)
        have hjUSAnd : j ∈ USAnd := Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hjS⟩, g, hg, hand⟩
        have hrW_adj : ∀ r ∈ T rW, G.Adj p.1 r := (hR_yl_iff rW (by omega) hrW_notS p.1 hp1L).mp hrW_y
        have hp2_in_T : p.2 ∈ T rW := by
          have he1 : val C n (e1 p.2) rW = true := by
            rw [← val_indep_of_not_inS L C S hS (e2 p.1 p.2) (e1 p.2)
              (fun v hv => by have hvp : v ≠ p.1 := fun h => hv (h ▸ hp1L); simp [e2, e1, hvp]) rW hrW_notS]
            exact hrW_e
          exact (hT_mem rW p.2).mpr ⟨hp2L, he1⟩
        have hp1_Alive : p.1 ∈ Alive sW := (hAlive_mem sW p.1).mpr ⟨hp1L, hsW_y⟩
        have hrW_lt_n : rW < n := by
          by_contra hge
          exact hpNotEL (Finset.mem_filter.mpr ⟨hpE, j, hjUSAnd, g, hg, hand, sW, rW, hinp, hsW_lt, hrW_lt, hsW_S, hrW_notS, by omega, hp2_in_T, hrW_adj, hp1_Alive⟩)
        have hrW_eq : rW = p.2.val := by
          have hrv := ((hT_mem rW p.2).mp hp2_in_T).2
          rw [val_input C _ rW hrW_lt_n] at hrv
          simp only [e1, decide_eq_true_eq] at hrv
          exact congrArg Fin.val hrv
        subst hrW_eq
        exact ⟨j, hjUSAnd, g, hg, hand, sW, hinp, hsW_lt, hsW_S, hp1_Alive⟩
      set ZR : Finset (ℕ × ℕ) := (UR ∪ USAnd).biUnion (fun j =>
        ((Finset.range (n + j)).filter (fun w => (∃ g, C.gates[j]? = some g ∧ w ∈ g.inputs) ∧ w ∉ S)).image (fun w => (j, w)))
      have hZR_card : ZR.card ≤ 2 * UR.card + USAnd.card := by
        have hdisj : Disjoint UR USAnd := by
          rw [Finset.disjoint_left]; intro j hj1 hj2
          exact (Finset.mem_filter.mp hj1).2 (Finset.mem_filter.mp (Finset.mem_filter.mp hj2).1).2
        have h1 : ZR.card ≤ ∑ j ∈ UR ∪ USAnd,
            (((Finset.range (n + j)).filter (fun w => (∃ g, C.gates[j]? = some g ∧ w ∈ g.inputs) ∧ w ∉ S)).image (fun w => (j, w))).card :=
          Finset.card_biUnion_le
        rw [Finset.sum_union hdisj] at h1
        have hUR_sum : ∑ j ∈ UR,
            (((Finset.range (n + j)).filter (fun w => (∃ g, C.gates[j]? = some g ∧ w ∈ g.inputs) ∧ w ∉ S)).image (fun w => (j, w))).card ≤ 2 * UR.card := by
          calc _ ≤ ∑ j ∈ UR, 2 := Finset.sum_le_sum (fun j hj => by
                have hjlt : j < s := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
                have hg : C.gates[j]? = some (C.gates[j]'(by omega)) := List.getElem?_eq_getElem (by omega)
                obtain ⟨a, b, hinp, _, _, _⟩ := hshape j hjlt _ hg
                refine Finset.card_image_le.trans ?_
                have hsub : (Finset.range (n + j)).filter (fun w => (∃ g, C.gates[j]? = some g ∧ w ∈ g.inputs) ∧ w ∉ S) ⊆ {a, b} := by
                  intro w hw
                  obtain ⟨_, ⟨g', hg', hw'⟩, _⟩ := Finset.mem_filter.mp hw
                  rw [hg] at hg'; cases Option.some.inj hg'; rw [hinp] at hw'
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
                  simp [hw']
                exact (Finset.card_le_card hsub).trans Finset.card_le_two)
            _ = 2 * UR.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        have hUSAnd_sum : ∑ j ∈ USAnd,
            (((Finset.range (n + j)).filter (fun w => (∃ g, C.gates[j]? = some g ∧ w ∈ g.inputs) ∧ w ∉ S)).image (fun w => (j, w))).card ≤ USAnd.card := by
          calc _ ≤ ∑ j ∈ USAnd, 1 := Finset.sum_le_sum (fun j hj => by
                have hjlt : j < s := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1
                have hjS : n + j ∈ S := (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
                obtain ⟨g, hg, hand⟩ := (Finset.mem_filter.mp hj).2
                obtain ⟨sW, rW, hinp, _, _, hsW_S, _⟩ := hSAND_split j hjlt hjS g hg hand
                refine Finset.card_image_le.trans ?_
                have hsub : (Finset.range (n + j)).filter (fun w => (∃ g, C.gates[j]? = some g ∧ w ∈ g.inputs) ∧ w ∉ S) ⊆ {rW} := by
                  intro w hw
                  obtain ⟨_, ⟨g', hg', hw'⟩, hw_notS⟩ := Finset.mem_filter.mp hw
                  rw [hg] at hg'; cases Option.some.inj hg'
                  rcases hinp with h | h <;> rw [h] at hw' <;> simp at hw' <;> rcases hw' with rfl | rfl
                  · exact absurd hsW_S hw_notS
                  · exact Finset.mem_singleton_self _
                  · exact Finset.mem_singleton_self _
                  · exact absurd hsW_S hw_notS
                exact (Finset.card_le_card hsub).trans (by simp))
            _ = USAnd.card := by simp
        omega
      have hZR_mem : ∀ j w, j ∈ UR ∪ USAnd → w < n + j → (∃ g, C.gates[j]? = some g ∧ w ∈ g.inputs) → w ∉ S → (j, w) ∈ ZR := by
        intro j w hj hwlt hread hwS
        exact Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_image.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hwlt, hread, hwS⟩, rfl⟩⟩
      set ZR1 : Finset (ℕ × ℕ) := ZR.filter (fun z => n ≤ z.2)
      set ZR_in : Finset (ℕ × ℕ) := ZR.filter (fun z => ¬ n ≤ z.2)
      set ZR2 : Finset (ℕ × ℕ) := ZR_in.filter (fun z => z.1 ∈ UR)
      set ZR3 : Finset (ℕ × ℕ) := ZR_in.filter (fun z => z.1 ∉ UR)
      have hZR_sp1 : ZR1.card + ZR_in.card = ZR.card := Finset.card_filter_add_card_filter_not (s := ZR) _
      have hZR_sp2 : ZR2.card + ZR3.card = ZR_in.card := Finset.card_filter_add_card_filter_not (s := ZR_in) _
      have hZR1_lb : UR.card ≤ ZR1.card := by
        apply card_le_of_rel UR ZR1 (fun k z => z.2 = n + k)
        · intro k hk
          have hklt : k < s := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
          have hk_notS : n + k ∉ S := (Finset.mem_filter.mp hk).2
          have hkne : k ≠ o := fun h => hk_notS (h ▸ hout_S)
          obtain ⟨j, hjlt, g, hg, hkj, hmem⟩ := hused k hklt hkne
          have hj_in : j ∈ UR ∪ USAnd := by
            by_cases hjS : n + j ∈ S
            · have hgop : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using (hmono g (List.mem_of_getElem? hg)).1
              rcases hgop with hand | hor
              · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjlt, hjS⟩, g, hg, hand⟩)
              · exact absurd (hSOR_both j hjlt hjS g hg hor (n + k) hmem) hk_notS
            · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjlt, hjS⟩)
          exact ⟨(j, n + k), Finset.mem_filter.mpr ⟨hZR_mem j (n + k) hj_in (by omega) ⟨g, hg, hmem⟩ hk_notS, by omega⟩, rfl⟩
        · intro k1 _ k2 _ z h1 h2; omega
      have hZR2_lb : EL.card ≤ ZR2.card := by
        apply card_le_of_rel EL ZR2 (fun p z => z.2 = p.2.val ∧ 2 ≤ (T (n + z.1)).card ∧ ∀ r' ∈ T (n + z.1), G.Adj p.1 r')
        · intro p hp
          have hpE := Finset.filter_subset _ _ hp
          have hp2L : p.2 ∉ L := (Finset.mem_sdiff.mp (Finset.mem_product.mp (Finset.mem_filter.mp hpE).1).2).2
          obtain ⟨_, j, hjUSAnd, g, hg, hand, sW, rW, hinp, hsW_lt, hrW_lt, hsW_S, hrW_notS, hrW_ge, hp2T, hadj_rW, _⟩ :=
            Finset.mem_filter.mp hp
          have hjlt : j < s := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hjUSAnd).1).1
          obtain ⟨gR, hgR_lt, hgR_notS, hread, hge2, hadj_gR⟩ := r_leaf_trace G L C S hS T
            (fun w _ _ r => hT_mem w r)
            (fun j hj => hR_or j (by omega))
            (fun j hj g hg => let ⟨a, b, h1, h2, h3, _⟩ := hshape j (by omega) g hg; ⟨a, b, h1, h2, h3⟩)
            (fun j hj => hR_ge2 j (by omega))
            p.1 p.2 hp2L rW (by omega) hrW_notS hrW_ge hp2T hadj_rW
          have hgR_UR : gR ∈ UR := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hgR_notS⟩
          have hp2_notS : p.2.val ∉ S := fun h => hp2L ((hS_in p.2.val p.2.isLt).mp h)
          refine ⟨(gR, p.2.val), Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hZR_mem gR p.2.val (Finset.mem_union_left _ hgR_UR) (by omega) hread hp2_notS, by omega⟩, hgR_UR⟩, rfl, hge2, hadj_gR⟩
        · intro p1 _ p2 _ z h1 h2
          have hsnd : p1.2 = p2.2 := Fin.ext (h1.1.symm.trans h2.1)
          have hfst : p1.1 = p2.1 := by
            by_contra hne
            obtain ⟨r1, hr1, r2, hr2, hr12⟩ := Finset.one_lt_card.mp (by omega : 1 < (T (n + z.1)).card)
            exact hNoC4 p1.1 p2.1 r1 r2 hne hr12 (h1.2.2 r1 hr1) (h1.2.2 r2 hr2) (h2.2.2 r1 hr1) (h2.2.2 r2 hr2)
          exact Prod.ext hfst hsnd
      have hZR3_lb : CR.card ≤ ZR3.card := by
        apply card_le_of_rel CR ZR3 (fun r z => z.2 = r.val)
        · intro r hrCR
          obtain ⟨p, hpER, rfl⟩ := Finset.mem_image.mp hrCR
          have hpE := Finset.sdiff_subset hpER
          have hp2L : p.2 ∉ L := (Finset.mem_sdiff.mp (Finset.mem_product.mp (Finset.mem_filter.mp hpE).1).2).2
          obtain ⟨j, hjUSAnd, g, hg, hand, sW, hinp, _, _, _⟩ := hER_crit p hpER
          have hj_notUR : j ∉ UR := fun h => (Finset.mem_filter.mp h).2 (Finset.mem_filter.mp (Finset.mem_filter.mp hjUSAnd).1).2
          have hp2_notS : p.2.val ∉ S := fun h => hp2L ((hS_in p.2.val p.2.isLt).mp h)
          have hmem_g : p.2.val ∈ g.inputs := by rcases hinp with h | h <;> rw [h] <;> simp
          exact ⟨(j, p.2.val), Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hZR_mem j p.2.val (Finset.mem_union_right _ hjUSAnd) (by omega) ⟨g, hg, hmem_g⟩ hp2_notS, by omega⟩, hj_notUR⟩, rfl⟩
        · intro r1 _ r2 _ z h1 h2; exact Fin.ext (h1.symm.trans h2)
      have hIneq1 : EL.card + CR.card ≤ UR.card + USAnd.card := by omega
      set ZS : Finset (ℕ × ℕ) := US.biUnion (fun j =>
        ((Finset.range (n + j)).filter (fun w => (∃ g, C.gates[j]? = some g ∧ w ∈ g.inputs) ∧ w ∈ S)).image (fun w => (j, w)))
      have hZS_card : ZS.card ≤ US.card + USOr.card := by
        have hdisj : Disjoint USAnd USOr := by
          rw [Finset.disjoint_left]; intro j h1 h2
          obtain ⟨g1, hg1, hand⟩ := (Finset.mem_filter.mp h1).2
          obtain ⟨g2, hg2, hor⟩ := (Finset.mem_filter.mp h2).2
          rw [hg1] at hg2; cases Option.some.inj hg2; rw [hand] at hor; cases hor
        have hUS_eq : US = USAnd ∪ USOr := by
          ext j; simp only [Finset.mem_union, USAnd, USOr, Finset.mem_filter]
          constructor
          · intro hj
            have hjlt : j < s := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
            have hg : C.gates[j]? = some (C.gates[j]'(by omega)) := List.getElem?_eq_getElem (by omega)
            have hgop : (C.gates[j]'(by omega)).op = GateOp.and ∨ (C.gates[j]'(by omega)).op = GateOp.or := by
              simpa using (hmono _ (List.mem_of_getElem? hg)).1
            rcases hgop with hand | hor
            · exact Or.inl ⟨hj, _, hg, hand⟩
            · exact Or.inr ⟨hj, _, hg, hor⟩
          · rintro (⟨hj, _⟩ | ⟨hj, _⟩) <;> exact hj
        have h1 : ZS.card ≤ ∑ j ∈ US,
            (((Finset.range (n + j)).filter (fun w => (∃ g, C.gates[j]? = some g ∧ w ∈ g.inputs) ∧ w ∈ S)).image (fun w => (j, w))).card :=
          Finset.card_biUnion_le
        rw [hUS_eq, Finset.sum_union hdisj] at h1
        have hAnd_sum : ∑ j ∈ USAnd,
            (((Finset.range (n + j)).filter (fun w => (∃ g, C.gates[j]? = some g ∧ w ∈ g.inputs) ∧ w ∈ S)).image (fun w => (j, w))).card ≤ USAnd.card := by
          calc _ ≤ ∑ j ∈ USAnd, 1 := Finset.sum_le_sum (fun j hj => by
                have hjlt : j < s := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1
                have hjS : n + j ∈ S := (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
                obtain ⟨g, hg, hand⟩ := (Finset.mem_filter.mp hj).2
                obtain ⟨sW, rW, hinp, _, _, _, hrW_notS⟩ := hSAND_split j hjlt hjS g hg hand
                refine Finset.card_image_le.trans ?_
                have hsub : (Finset.range (n + j)).filter (fun w => (∃ g, C.gates[j]? = some g ∧ w ∈ g.inputs) ∧ w ∈ S) ⊆ {sW} := by
                  intro w hw
                  obtain ⟨_, ⟨g', hg', hw'⟩, hwS⟩ := Finset.mem_filter.mp hw
                  rw [hg] at hg'; cases Option.some.inj hg'
                  rcases hinp with h | h <;> rw [h] at hw' <;> simp at hw' <;> rcases hw' with rfl | rfl
                  · exact Finset.mem_singleton_self _
                  · exact absurd hwS hrW_notS
                  · exact absurd hwS hrW_notS
                  · exact Finset.mem_singleton_self _
                exact (Finset.card_le_card hsub).trans (by simp))
            _ = USAnd.card := by simp
        have hOr_sum : ∑ j ∈ USOr,
            (((Finset.range (n + j)).filter (fun w => (∃ g, C.gates[j]? = some g ∧ w ∈ g.inputs) ∧ w ∈ S)).image (fun w => (j, w))).card ≤ 2 * USOr.card := by
          calc _ ≤ ∑ j ∈ USOr, 2 := Finset.sum_le_sum (fun j hj => by
                have hjlt : j < s := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1
                have hg : C.gates[j]? = some (C.gates[j]'(by omega)) := List.getElem?_eq_getElem (by omega)
                obtain ⟨a, b, hinp, _, _, _⟩ := hshape j hjlt _ hg
                refine Finset.card_image_le.trans ?_
                have hsub : (Finset.range (n + j)).filter (fun w => (∃ g, C.gates[j]? = some g ∧ w ∈ g.inputs) ∧ w ∈ S) ⊆ {a, b} := by
                  intro w hw
                  obtain ⟨_, ⟨g', hg', hw'⟩, _⟩ := Finset.mem_filter.mp hw
                  rw [hg] at hg'; cases Option.some.inj hg'; rw [hinp] at hw'
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
                  simp [hw']
                exact (Finset.card_le_card hsub).trans Finset.card_le_two)
            _ = 2 * USOr.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        omega
      have hZS_mem : ∀ j w, j ∈ US → w < n + j → (∃ g, C.gates[j]? = some g ∧ w ∈ g.inputs) → w ∈ S → (j, w) ∈ ZS := by
        intro j w hj hwlt hread hwS
        exact Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_image.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hwlt, hread, hwS⟩, rfl⟩⟩
      set ZS_int1 : Finset (ℕ × ℕ) := ZS.filter (fun z => (Alive z.2).card ≠ 1)
      set ZS_a1 : Finset (ℕ × ℕ) := ZS.filter (fun z => ¬ (Alive z.2).card ≠ 1)
      set ZS_int2 : Finset (ℕ × ℕ) := ZS_a1.filter (fun z => Alive (n + z.1) = Alive z.2)
      set ZS_exit : Finset (ℕ × ℕ) := ZS_a1.filter (fun z => Alive (n + z.1) ≠ Alive z.2)
      have hZS_sp1 : ZS_int1.card + ZS_a1.card = ZS.card := Finset.card_filter_add_card_filter_not (s := ZS) _
      have hZS_sp2 : ZS_int2.card + ZS_exit.card = ZS_a1.card := Finset.card_filter_add_card_filter_not (s := ZS_a1) _
      set Kne1 : Finset ℕ := (US.erase o).filter (fun k => (Alive (n + k)).card ≠ 1)
      set K1 : Finset ℕ := (US.erase o).filter (fun k => ¬ (Alive (n + k)).card ≠ 1)
      have hK_sp : Kne1.card + K1.card = US.card - 1 := by
        have h := Finset.card_filter_add_card_filter_not (s := US.erase o) (fun k => (Alive (n + k)).card ≠ 1)
        rw [Finset.card_erase_of_mem hoUS] at h; exact h
      have hKne1_lb : Kne1.card ≤ ZS_int1.card := by
        apply card_le_of_rel Kne1 ZS_int1 (fun k z => z.2 = n + k)
        · intro k hk
          have hk_er := (Finset.mem_filter.mp hk).1
          have hk_ne1 := (Finset.mem_filter.mp hk).2
          have hkne : k ≠ o := (Finset.mem_erase.mp hk_er).1
          have hkUS := (Finset.mem_erase.mp hk_er).2
          have hklt : k < s := Finset.mem_range.mp (Finset.mem_filter.mp hkUS).1
          have hkS : n + k ∈ S := (Finset.mem_filter.mp hkUS).2
          obtain ⟨j, hjlt, g, hg, hkj, hmem⟩ := hused k hklt hkne
          have hjS : n + j ∈ S := hS.2.1 j g hg (n + k) hmem (by omega) hkS
          have hjUS : j ∈ US := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjlt, hjS⟩
          exact ⟨(j, n + k), Finset.mem_filter.mpr ⟨hZS_mem j (n + k) hjUS (by omega) ⟨g, hg, hmem⟩ hkS, hk_ne1⟩, rfl⟩
        · intro k1 _ k2 _ z h1 h2; omega
      have hK1_lb : K1.card ≤ ZS_int2.card := by
        apply card_le_of_rel K1 ZS_int2 (fun k z => z.1 = k)
        · intro k hk
          have hk_er := (Finset.mem_filter.mp hk).1
          have hk_eq1 : (Alive (n + k)).card = 1 := not_not.mp (Finset.mem_filter.mp hk).2
          have hkUS := (Finset.mem_erase.mp hk_er).2
          have hklt : k < s := Finset.mem_range.mp (Finset.mem_filter.mp hkUS).1
          have hkS : n + k ∈ S := (Finset.mem_filter.mp hkUS).2
          obtain ⟨l, hl_eq⟩ := Finset.card_eq_one.mp hk_eq1
          have hg : C.gates[k]? = some (C.gates[k]'(by omega)) := List.getElem?_eq_getElem (by omega)
          set g := C.gates[k]'(by omega)
          have hgop : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using (hmono g (List.mem_of_getElem? hg)).1
          rcases hgop with hand | hor
          · obtain ⟨sW, rW, hinp, hsW_lt, hrW_lt, hsW_S, hrW_notS⟩ := hSAND_split k hklt hkS g hg hand
            have hsW_le1 : (Alive sW).card ≤ 1 := by
              by_contra hgt
              obtain ⟨r0, _, rfl, hadj_r0⟩ := hSAND_multi k hklt hkS g hg hand sW rW hinp hsW_lt hrW_lt hsW_S hrW_notS (by omega)
              have hlin : l ∈ Alive (n + k) := hl_eq ▸ Finset.mem_singleton_self l
              obtain ⟨hlA, hna⟩ := (hAlive_and_sub k hklt hkS g hg hand sW r0.val hinp hsW_lt hrW_lt hsW_S hrW_notS l).mp hlin
              apply hna; intro r hrT
              have hrv := ((hT_mem r0.val r).mp hrT).2
              rw [val_input C _ r0.val r0.isLt] at hrv; simp only [e1, decide_eq_true_eq] at hrv
              rw [← hrv]; exact hadj_r0 l hlA
            have hsub : Alive (n + k) ⊆ Alive sW := fun x hx =>
              ((hAlive_and_sub k hklt hkS g hg hand sW rW hinp hsW_lt hrW_lt hsW_S hrW_notS x).mp hx).1
            have hAeq : Alive (n + k) = Alive sW := Finset.eq_of_subset_of_card_le hsub (by omega)
            have hsW_mem : sW ∈ g.inputs := by rcases hinp with h | h <;> rw [h] <;> simp
            exact ⟨(k, sW), Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hZS_mem k sW hkUS hsW_lt ⟨g, hg, hsW_mem⟩ hsW_S, by rw [← hAeq, hk_eq1]; simp⟩, hAeq⟩, rfl⟩
          · obtain ⟨a, b, hinp, ha_lt, hb_lt, ha_S, hb_S, hAeq⟩ := hAlive_or k hklt hkS g hg hor
            have hlin : l ∈ Alive a ∨ l ∈ Alive b := by
              have : l ∈ Alive (n + k) := hl_eq ▸ Finset.mem_singleton_self l
              rw [hAeq, Finset.mem_union] at this; exact this
            rcases hlin with hla | hlb
            · have ha_eq : Alive (n + k) = Alive a := by
                apply Finset.Subset.antisymm
                · rw [hl_eq]; exact Finset.singleton_subset_iff.mpr hla
                · rw [hAeq]; exact Finset.subset_union_left
              exact ⟨(k, a), Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hZS_mem k a hkUS ha_lt ⟨g, hg, by rw [hinp]; simp⟩ ha_S, by rw [← ha_eq, hk_eq1]; simp⟩, ha_eq⟩, rfl⟩
            · have hb_eq : Alive (n + k) = Alive b := by
                apply Finset.Subset.antisymm
                · rw [hl_eq]; exact Finset.singleton_subset_iff.mpr hlb
                · rw [hAeq]; exact Finset.subset_union_right
              exact ⟨(k, b), Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hZS_mem k b hkUS hb_lt ⟨g, hg, by rw [hinp]; simp⟩ hb_S, by rw [← hb_eq, hk_eq1]; simp⟩, hb_eq⟩, rfl⟩
        · intro k1 _ k2 _ z h1 h2; exact h1.symm.trans h2
      set ZS_exit_L : Finset (ℕ × ℕ) := ZS_exit.filter (fun z => z.1 ∈ USAnd ∧
        ∃ g, C.gates[z.1]? = some g ∧ ∃ rW ∈ g.inputs, rW < n + z.1 ∧ rW ∉ S ∧ n ≤ rW)
      set ZS_exit_R : Finset (ℕ × ℕ) := ZS_exit.filter (fun z => ¬ (z.1 ∈ USAnd ∧
        ∃ g, C.gates[z.1]? = some g ∧ ∃ rW ∈ g.inputs, rW < n + z.1 ∧ rW ∉ S ∧ n ≤ rW))
      have hZS_ex_sp : ZS_exit_L.card + ZS_exit_R.card = ZS_exit.card :=
        Finset.card_filter_add_card_filter_not (s := ZS_exit) _
      have hCL_lb : CL.card ≤ ZS_exit_L.card := by
        apply card_le_of_rel CL ZS_exit_L (fun l z => Alive z.2 = {l})
        · intro l hlCL
          obtain ⟨p, hpEL, rfl⟩ := Finset.mem_image.mp hlCL
          obtain ⟨_, j, hjUSAnd, g, hg, hand, sW, rW, hinp, hsW_lt, hrW_lt, hsW_S, hrW_notS, hrW_ge, _, hadj_rW, hp1_A⟩ :=
            Finset.mem_filter.mp hpEL
          have hjUS := (Finset.mem_filter.mp hjUSAnd).1
          have hjlt : j < s := Finset.mem_range.mp (Finset.mem_filter.mp hjUS).1
          have hjS : n + j ∈ S := (Finset.mem_filter.mp hjUS).2
          have hsW_card1 : (Alive sW).card = 1 := by
            by_contra hne1
            have hpos : 0 < (Alive sW).card := Finset.card_pos.mpr ⟨p.1, hp1_A⟩
            have hge2 : 2 ≤ (Alive sW).card := by omega
            obtain ⟨r0, _, hrW_eq, _⟩ := hSAND_multi j hjlt hjS g hg hand sW rW hinp hsW_lt hrW_lt hsW_S hrW_notS hge2
            omega
          have hsW_eq : Alive sW = {p.1} := by
            obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hsW_card1
            rw [hx] at hp1_A; simp only [Finset.mem_singleton] at hp1_A; rw [hx, hp1_A]
          have hj_not_p1 : p.1 ∉ Alive (n + j) := fun h =>
            ((hAlive_and_sub j hjlt hjS g hg hand sW rW hinp hsW_lt hrW_lt hsW_S hrW_notS p.1).mp h).2 hadj_rW
          have hne_A : Alive (n + j) ≠ Alive sW := fun heq => hj_not_p1 (heq.symm ▸ hp1_A)
          have hsW_mem : sW ∈ g.inputs := by rcases hinp with h | h <;> rw [h] <;> simp
          have hrW_mem : rW ∈ g.inputs := by rcases hinp with h | h <;> rw [h] <;> simp
          refine ⟨(j, sW), Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hZS_mem j sW hjUS hsW_lt ⟨g, hg, hsW_mem⟩ hsW_S, by rw [hsW_card1]; simp⟩, hne_A⟩, hjUSAnd, g, hg, rW, hrW_mem, hrW_lt, hrW_notS, hrW_ge⟩, hsW_eq⟩
        · intro l1 _ l2 _ z h1 h2
          have := h1.symm.trans h2
          exact Finset.singleton_injective this
      have hER_lb : ER.card ≤ ZS_exit_R.card := by
        apply card_le_of_rel ER ZS_exit_R (fun p z => Alive z.2 = {p.1} ∧
          ((z.1 ∈ USAnd ∧ ∃ g, C.gates[z.1]? = some g ∧ p.2.val ∈ g.inputs) ∨
           (z.1 ∈ USOr ∧ 2 ≤ (Alive (n + z.1)).card ∧ ∀ l' ∈ Alive (n + z.1), G.Adj l' p.2)))
        · intro p hpER
          have hpE := Finset.sdiff_subset hpER
          have hp2L : p.2 ∉ L := (Finset.mem_sdiff.mp (Finset.mem_product.mp (Finset.mem_filter.mp hpE).1).2).2
          have hadj : G.Adj p.1 p.2 := (Finset.mem_filter.mp hpE).2
          obtain ⟨j, hjUSAnd, g, hg, hand, sW, hinp, hsW_lt, hsW_S, hp1_A⟩ := hER_crit p hpER
          have hjUS := (Finset.mem_filter.mp hjUSAnd).1
          have hjlt : j < s := Finset.mem_range.mp (Finset.mem_filter.mp hjUS).1
          have hjS : n + j ∈ S := (Finset.mem_filter.mp hjUS).2
          have hp2_notS : p.2.val ∉ S := fun h => hp2L ((hS_in p.2.val p.2.isLt).mp h)
          have hnot_bigR : ¬ (j ∈ USAnd ∧ ∃ g', C.gates[j]? = some g' ∧ ∃ rW ∈ g'.inputs, rW < n + j ∧ rW ∉ S ∧ n ≤ rW) := by
            rintro ⟨_, g', hg', rW, hrW_mem, _, hrW_notS, hrW_ge⟩
            rw [hg] at hg'; cases Option.some.inj hg'
            rcases hinp with h | h <;> rw [h] at hrW_mem <;> simp at hrW_mem <;> rcases hrW_mem with rfl | rfl
            · exact hrW_notS hsW_S
            · omega
            · omega
            · exact hrW_notS hsW_S
          by_cases h2 : 2 ≤ (Alive sW).card
          · obtain ⟨r0, _, hr0eq, hadj_r0⟩ := hSAND_multi j hjlt hjS g hg hand sW p.2.val hinp hsW_lt (by omega) hsW_S hp2_notS h2
            have hr0_is_p2 : r0 = p.2 := Fin.ext hr0eq.symm
            subst hr0_is_p2
            obtain ⟨k, hklt, hkS, ⟨gk, hgk, hgor, w', hw'_mem, hw'_lt, hw'_S, hw'_A⟩, hk2, hk_adj⟩ :=
              s_multi_trace G L C S hmono Alive
                (fun w hw hwS => by rw [hAlive_in_eq w hw hwS]; simp)
                (fun j' hj' => hAlive_or j' (by omega))
                (fun j' hj' => hAlive_and_lt2 j' (by omega))
                p.1 p.2 sW (by omega) hsW_S hp1_A h2 hadj_r0
            have hkUS : k ∈ US := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hkS⟩
            have hkUSOr : k ∈ USOr := Finset.mem_filter.mpr ⟨hkUS, gk, hgk, hgor⟩
            have hk_notAnd : k ∉ USAnd := by
              intro h; obtain ⟨g', hg', hand'⟩ := (Finset.mem_filter.mp h).2
              rw [hgk] at hg'; cases Option.some.inj hg'; rw [hgor] at hand'; cases hand'
            have hne_A : Alive (n + k) ≠ Alive w' := fun heq => by rw [heq, hw'_A] at hk2; simp at hk2
            refine ⟨(k, w'), Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hZS_mem k w' hkUS hw'_lt ⟨gk, hgk, hw'_mem⟩ hw'_S, by rw [hw'_A]; simp⟩, hne_A⟩, fun h => hk_notAnd h.1⟩, hw'_A, Or.inr ⟨hkUSOr, hk2, hk_adj⟩⟩
          · have hsW_card1 : (Alive sW).card = 1 := by
              have hpos := Finset.card_pos.mpr ⟨p.1, hp1_A⟩; omega
            have hsW_eq : Alive sW = {p.1} := by
              obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hsW_card1
              rw [hx] at hp1_A; simp only [Finset.mem_singleton] at hp1_A; rw [hx, hp1_A]
            have hj_not_p1 : p.1 ∉ Alive (n + j) := by
              intro h
              apply ((hAlive_and_sub j hjlt hjS g hg hand sW p.2.val hinp hsW_lt (by omega) hsW_S hp2_notS p.1).mp h).2
              intro r hrT
              have hrv := ((hT_mem p.2.val r).mp hrT).2
              rw [val_input C _ p.2.val p.2.isLt] at hrv; simp only [e1, decide_eq_true_eq] at hrv
              rw [← hrv]; exact hadj
            have hne_A : Alive (n + j) ≠ Alive sW := fun heq => hj_not_p1 (heq.symm ▸ hp1_A)
            have hsW_mem : sW ∈ g.inputs := by rcases hinp with h | h <;> rw [h] <;> simp
            have hp2_mem : p.2.val ∈ g.inputs := by rcases hinp with h | h <;> rw [h] <;> simp
            refine ⟨(j, sW), Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hZS_mem j sW hjUS hsW_lt ⟨g, hg, hsW_mem⟩ hsW_S, by rw [hsW_card1]; simp⟩, hne_A⟩, hnot_bigR⟩, hsW_eq, Or.inl ⟨hjUSAnd, g, hg, hp2_mem⟩⟩
        · intro p1 hp1 p2 hp2 z h1 h2
          have hfst : p1.1 = p2.1 := Finset.singleton_injective (h1.1.symm.trans h2.1)
          have hsnd : p1.2 = p2.2 := by
            rcases h1.2 with ⟨hzA, g1, hg1, hp1m⟩ | ⟨hzO, hk2, hadj1⟩
            · rcases h2.2 with ⟨_, g2, hg2, hp2m⟩ | ⟨hzO, _, _⟩
              · rw [hg1] at hg2; cases Option.some.inj hg2
                have hzUS := (Finset.mem_filter.mp hzA).1
                have hzlt : z.1 < s := Finset.mem_range.mp (Finset.mem_filter.mp hzUS).1
                have hzS : n + z.1 ∈ S := (Finset.mem_filter.mp hzUS).2
                obtain ⟨g', hg', hand⟩ := (Finset.mem_filter.mp hzA).2
                rw [hg1] at hg'; cases Option.some.inj hg'
                obtain ⟨sW, rW, hinp, _, _, hsW_S, _⟩ := hSAND_split z.1 hzlt hzS g1 hg1 hand
                have hp1L : p1.2 ∉ L := (Finset.mem_sdiff.mp (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.sdiff_subset hp1)).1).2).2
                have hp2L : p2.2 ∉ L := (Finset.mem_sdiff.mp (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.sdiff_subset hp2)).1).2).2
                have hp1_notS : p1.2.val ∉ S := fun h => hp1L ((hS_in p1.2.val p1.2.isLt).mp h)
                have hp2_notS : p2.2.val ∉ S := fun h => hp2L ((hS_in p2.2.val p2.2.isLt).mp h)
                have h1r : p1.2.val = rW := by
                  rcases hinp with h | h <;> rw [h] at hp1m <;> simp at hp1m <;> rcases hp1m with h' | h'
                  · exact absurd (h' ▸ hsW_S) hp1_notS
                  · exact h'
                  · exact h'
                  · exact absurd (h' ▸ hsW_S) hp1_notS
                have h2r : p2.2.val = rW := by
                  rcases hinp with h | h <;> rw [h] at hp2m <;> simp at hp2m <;> rcases hp2m with h' | h'
                  · exact absurd (h' ▸ hsW_S) hp2_notS
                  · exact h'
                  · exact h'
                  · exact absurd (h' ▸ hsW_S) hp2_notS
                exact Fin.ext (h1r.trans h2r.symm)
              · exfalso
                obtain ⟨g', hg', hand⟩ := (Finset.mem_filter.mp hzA).2
                obtain ⟨g2, hg2, hor⟩ := (Finset.mem_filter.mp hzO).2
                rw [hg'] at hg2; cases Option.some.inj hg2; rw [hand] at hor; cases hor
            · rcases h2.2 with ⟨hzA, _, _, _⟩ | ⟨_, _, hadj2⟩
              · exfalso
                obtain ⟨g', hg', hand⟩ := (Finset.mem_filter.mp hzA).2
                obtain ⟨g2, hg2, hor⟩ := (Finset.mem_filter.mp hzO).2
                rw [hg'] at hg2; cases Option.some.inj hg2; rw [hand] at hor; cases hor
              · by_contra hne
                obtain ⟨l1, hl1, l2, hl2, hl12⟩ := Finset.one_lt_card.mp (by omega : 1 < (Alive (n + z.1)).card)
                exact hNoC4 l1 l2 p1.2 p2.2 hl12 hne (hadj1 l1 hl1) (hadj2 l1 hl1) (hadj1 l2 hl2) (hadj2 l2 hl2)
          exact Prod.ext hfst hsnd
      have hUS_pos : 1 ≤ US.card := Finset.card_pos.mpr ⟨o, hoUS⟩
      have hIneq2 : CL.card + ER.card ≤ USOr.card + 1 := by omega
      omega

end ClassicalProof

end PEqualNP.Outside.L_meta_655_aux

theorem PEqualNP.Outside.L_meta_655 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 14 ∧ (∃ S : Set ℕ, ((∀ i : ℕ, i < 4 → i ∈ S) ∨ (∀ i : ℕ, 4 ≤ i → i < 10 → i ∈ S)) ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → ∀ i ∈ g.inputs, i < 10 + j → i ∈ S → 10 + j ∈ S) ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ a b : ℕ, g.inputs = [a, b] → a < 10 + j → b < 10 + j → ¬ (a ∈ S ∧ b ∈ S))) ∧ (∀ x : Fin 10 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 10, (u.val, v.val) ∈ ([(0, 4), (4, 1), (0, 5), (5, 2), (0, 6), (6, 3), (1, 7), (7, 2), (1, 8), (8, 3), (2, 9), (9, 3)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) := by
  rintro ⟨C, hmono, hsz, ⟨S, hSide, hSUp, hSAnd⟩, hEval⟩
  have hfun : ∀ x : Fin 10 → Bool, PEqualNP.Outside.L_meta_655_aux.val C 10 x C.output = true ↔
      ∃ u v : Fin 10, PEqualNP.Outside.L_meta_655_aux.G10.Adj u v ∧ x u = true ∧ x v = true := by
    intro x
    change C.eval (List.ofFn x) = true ↔ _
    rw [hEval x]
    constructor
    · rintro ⟨u, v, huv, hxu, hxv⟩
      refine ⟨u, v, ?_, hxu, hxv⟩
      simp only [PEqualNP.Outside.L_meta_655_aux.adj10b, decide_eq_true_eq]
      exact Or.inl huv
    · rintro ⟨u, v, hadj, hxu, hxv⟩
      simp only [PEqualNP.Outside.L_meta_655_aux.adj10b, decide_eq_true_eq] at hadj
      rcases hadj with huv | hvu
      · exact ⟨u, v, huv, hxu, hxv⟩
      · exact ⟨v, u, hvu, hxv, hxu⟩
  rcases hSide with hA | hB
  · have hValid : PEqualNP.Outside.L_meta_655_aux.ValidS PEqualNP.Outside.L_meta_655_aux.LA C S :=
      ⟨fun l hl => hA l.val (Finset.mem_filter.mp hl).2, hSUp, hSAnd⟩
    have hlb := PEqualNP.Outside.L_meta_655_aux.main_lb
      PEqualNP.Outside.L_meta_655_aux.G10 PEqualNP.Outside.L_meta_655_aux.LA 4
      PEqualNP.Outside.L_meta_655_aux.G10_bip_A
      PEqualNP.Outside.L_meta_655_aux.G10_noC4
      ⟨0, 4, PEqualNP.Outside.L_meta_655_aux.G10_edge04⟩
      PEqualNP.Outside.L_meta_655_aux.G10_vc
      C.size (PEqualNP.Outside.L_meta_655_aux.bigInputCount 10 C) C rfl rfl hmono ⟨S, hValid⟩ hfun
    rw [PEqualNP.Outside.L_meta_655_aux.G10_edges_A _] at hlb
    omega
  · have hValid : PEqualNP.Outside.L_meta_655_aux.ValidS PEqualNP.Outside.L_meta_655_aux.LB C S :=
      ⟨fun l hl => hB l.val (Finset.mem_filter.mp hl).2 l.isLt, hSUp, hSAnd⟩
    have hlb := PEqualNP.Outside.L_meta_655_aux.main_lb
      PEqualNP.Outside.L_meta_655_aux.G10 PEqualNP.Outside.L_meta_655_aux.LB 4
      PEqualNP.Outside.L_meta_655_aux.G10_bip_B
      PEqualNP.Outside.L_meta_655_aux.G10_noC4
      ⟨0, 4, PEqualNP.Outside.L_meta_655_aux.G10_edge04⟩
      PEqualNP.Outside.L_meta_655_aux.G10_vc
      C.size (PEqualNP.Outside.L_meta_655_aux.bigInputCount 10 C) C rfl rfl hmono ⟨S, hValid⟩ hfun
    rw [PEqualNP.Outside.L_meta_655_aux.G10_edges_B _] at hlb
    omega
