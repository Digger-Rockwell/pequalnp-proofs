import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_616_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl step x := rfl

lemma foldl_step_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_append_left_lt (w t : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_self (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl w.length)]
  simp

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
    exact getD_append_left_lt w _ i hi

lemma foldl_step_getD_ge (gs : List Gate) (w : List Bool) (i : ℕ) (hi : w.length + gs.length ≤ i) :
    (gs.foldl step w).getD i false = false := by
  apply getD_ge_len
  rw [foldl_step_len]
  exact hi

lemma foldl_step_gate (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate) (hj : gs[j]? = some g) :
    (gs.foldl step w).getD (w.length + j) false =
      g.op.eval (g.inputs.map fun i => if i < w.length + j then (gs.foldl step w).getD i false else false) := by
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
      rw [show (step w g0).getD w.length false = g0.op.eval (g0.inputs.map fun i => w.getD i false) from getD_append_self w _]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · have hilt : i < (step w g0).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]
          omega
        simp only [hi, ↓reduceIte, foldl_step_getD_lt gs (step w g0) i hilt]
        exact (getD_append_left_lt w _ i hi).symm
      · simp only [hi, ↓reduceIte]
        exact getD_ge_len w i (Nat.le_of_not_lt hi)
    | succ j' =>
      simp only [List.getElem?_cons_succ] at hj
      have hlen : (step w g0).length + j' = w.length + (j' + 1) := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [List.foldl_cons, ← hlen]
      exact ih (step w g0) j' hj

lemma val_lt_n {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val C x w = x ⟨w, hw⟩ := by
  unfold val
  rw [wires_eq_foldl, foldl_step_getD_lt C.gates (List.ofFn x) w (by simp [hw])]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, ↓reduceDIte, Option.getD_some]

lemma val_ge_len {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    val C x w = false := by
  unfold val
  rw [wires_eq_foldl]
  exact foldl_step_getD_ge C.gates (List.ofFn x) w (by simp [hw])

lemma val_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hj : C.gates[j]? = some g) :
    val C x (n + j) =
      g.op.eval (g.inputs.map fun i => if i < n + j then val C x i else false) := by
  unfold val
  have h := foldl_step_gate C.gates (List.ofFn x) j g hj
  simpa only [List.length_ofFn, ← wires_eq_foldl] using h

lemma val_mono {n : ℕ} (C : Circuit) (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true) :
    ∀ w, val C x w = true → val C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hx
    by_cases h1 : w < n
    · rw [val_lt_n C x w h1] at hx
      rw [val_lt_n C y w h1]
      exact hxy ⟨w, h1⟩ hx
    · by_cases h2 : n + C.gates.length ≤ w
      · rw [val_ge_len C x w h2] at hx
        exact absurd hx (by decide)
      · have hjlt : w - n < C.gates.length := by omega
        set j := w - n
        have hwj : w = n + j := by omega
        set g := C.gates[j]'hjlt
        have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hjlt
        have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by
          have := (hmono g (List.mem_of_getElem? hg)).1
          simpa using this
        rw [hwj, val_gate C x j g hg] at hx
        rw [hwj, val_gate C y j g hg]
        rcases hop with hand | hor
        · rw [hand] at hx ⊢
          simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index,
            and_imp, forall_apply_eq_imp_iff₂] at hx ⊢
          intro i hi
          have hxi := hx i hi
          by_cases hilt : i < n + j
          · simp only [hilt, ↓reduceIte] at hxi ⊢
            exact ih i (by omega) hxi
          · simp only [hilt, ↓reduceIte] at hxi
            exact absurd hxi (by decide)
        · rw [hor] at hx ⊢
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hx ⊢
          obtain ⟨_, ⟨i, hi, rfl⟩, hxi⟩ := hx
          by_cases hilt : i < n + j
          · simp only [hilt, ↓reduceIte] at hxi
            refine ⟨val C y i, ⟨i, hi, by simp [hilt]⟩, ih i (by omega) hxi⟩
          · simp only [hilt, ↓reduceIte] at hxi
            exact absurd hxi (by decide)

def statVal {n : ℕ} (C : Circuit) (x : Fin n → Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl b => b
  | Sum.inr w => val C x w

def evalStatGate (op : GateOp) (ins : List (Bool ⊕ ℕ)) (nextWire : ℕ) :
    Option Gate × (Bool ⊕ ℕ) :=
  match op with
  | GateOp.and =>
    if ins.any (fun s => s == Sum.inl false) then (none, Sum.inl false)
    else
      let wires := ins.filterMap (fun s => match s with | Sum.inr w => some w | Sum.inl _ => none)
      match wires with
      | [] => (none, Sum.inl true)
      | [a] => (none, Sum.inr a)
      | a :: b :: _ => (some ⟨GateOp.and, [a, b]⟩, Sum.inr nextWire)
  | GateOp.or =>
    if ins.any (fun s => s == Sum.inl true) then (none, Sum.inl true)
    else
      let wires := ins.filterMap (fun s => match s with | Sum.inr w => some w | Sum.inl _ => none)
      match wires with
      | [] => (none, Sum.inl false)
      | [a] => (none, Sum.inr a)
      | a :: b :: _ => (some ⟨GateOp.or, [a, b]⟩, Sum.inr nextWire)
  | _ => (none, Sum.inl false)

def simpLoop (n skip : ℕ) (repl : Bool ⊕ ℕ) :
    List Gate → ℕ → List Gate → (ℕ → Bool ⊕ ℕ) → List Gate × (ℕ → Bool ⊕ ℕ)
  | [], _, acc, env => (acc, env)
  | g :: rest, j, acc, env =>
    if j = skip then
      simpLoop n skip repl rest (j + 1) acc (fun k => if k = n + j then repl else env k)
    else
      let ins := g.inputs.map (fun i => if i < n + j then env i else Sum.inl false)
      let res := evalStatGate g.op ins (n + acc.length)
      let acc' := match res.1 with | none => acc | some g' => acc ++ [g']
      let env' := fun k => if k = n + j then res.2 else env k
      simpLoop n skip repl rest (j + 1) acc' env'

lemma evalStatGate_mono (op : GateOp) (ins : List (Bool ⊕ ℕ)) (nw : ℕ) (g' : Gate)
    (h : (evalStatGate op ins nw).1 = some g') :
    g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 := by
  cases op <;> simp only [evalStatGate] at h
  · by_cases hany : ins.any (fun s => s == Sum.inl false) = true
    · simp [hany] at h
    · simp only [hany] at h
      rcases hfm : ins.filterMap (fun s => match s with | Sum.inr w => some w | Sum.inl _ => none)
        with _ | ⟨a, _ | ⟨b, t⟩⟩ <;> simp only [hfm] at h
      · cases h
      · cases h
      · injection h with h'; subst h'; simp
  · by_cases hany : ins.any (fun s => s == Sum.inl true) = true
    · simp [hany] at h
    · simp only [hany] at h
      rcases hfm : ins.filterMap (fun s => match s with | Sum.inr w => some w | Sum.inl _ => none)
        with _ | ⟨a, _ | ⟨b, t⟩⟩ <;> simp only [hfm] at h
      · cases h
      · cases h
      · injection h with h'; subst h'; simp
  · cases h
  · cases h
  · cases h

lemma evalStatGate_val {n : ℕ} (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (ins : List (Bool ⊕ ℕ)) (hins : ins.length ≤ 2)
    (acc : List Gate) (hbound : ∀ w, Sum.inr w ∈ ins → w < n + acc.length)
    (x : Fin n → Bool) :
    let res := evalStatGate op ins (n + acc.length)
    let acc' := match res.1 with | none => acc | some g' => acc ++ [g']
    statVal ⟨acc', 0⟩ x res.2 = op.eval (ins.map (statVal ⟨acc, 0⟩ x)) := by
  have hlen : (acc.foldl step (List.ofFn x)).length = n + acc.length := by
    rw [foldl_step_len, List.length_ofFn]
  have hkeep : ∀ (g' : Gate) (w : ℕ), w < n + acc.length →
      val ⟨acc ++ [g'], 0⟩ x w = val ⟨acc, 0⟩ x w := by
    intro g' w hw
    unfold val
    simp only [wires_eq_foldl, List.foldl_append, List.foldl_cons, List.foldl_nil, step]
    exact getD_append_left_lt _ _ w (by rw [hlen]; exact hw)
  have hnew : ∀ (g' : Gate),
      val ⟨acc ++ [g'], 0⟩ x (n + acc.length) =
        g'.op.eval (g'.inputs.map fun i => val ⟨acc, 0⟩ x i) := by
    intro g'
    unfold val
    simp only [wires_eq_foldl, List.foldl_append, List.foldl_cons, List.foldl_nil, step]
    rw [← hlen, getD_append_self]
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨s1, _ | ⟨s2, _ | ⟨s3, t⟩⟩⟩
    · simp [evalStatGate, statVal, GateOp.eval]
    · cases s1 with
      | inl b => cases b <;> simp [evalStatGate, statVal, GateOp.eval]
      | inr a => simp [evalStatGate, statVal, GateOp.eval]
    · cases s1 with
      | inl b1 =>
        cases s2 with
        | inl b2 => cases b1 <;> cases b2 <;> simp [evalStatGate, statVal, GateOp.eval]
        | inr b => cases b1 <;> simp [evalStatGate, statVal, GateOp.eval]
      | inr a =>
        cases s2 with
        | inl b2 => cases b2 <;> simp [evalStatGate, statVal, GateOp.eval]
        | inr b =>
          change val ⟨acc ++ [⟨GateOp.and, [a, b]⟩], 0⟩ x (n + acc.length) =
            GateOp.and.eval [statVal ⟨acc, 0⟩ x (Sum.inr a), statVal ⟨acc, 0⟩ x (Sum.inr b)]
          rw [hnew]
          simp [GateOp.eval, statVal]
    · simp at hins
  · rcases ins with _ | ⟨s1, _ | ⟨s2, _ | ⟨s3, t⟩⟩⟩
    · simp [evalStatGate, statVal, GateOp.eval]
    · cases s1 with
      | inl b => cases b <;> simp [evalStatGate, statVal, GateOp.eval]
      | inr a => simp [evalStatGate, statVal, GateOp.eval]
    · cases s1 with
      | inl b1 =>
        cases s2 with
        | inl b2 => cases b1 <;> cases b2 <;> simp [evalStatGate, statVal, GateOp.eval]
        | inr b => cases b1 <;> simp [evalStatGate, statVal, GateOp.eval]
      | inr a =>
        cases s2 with
        | inl b2 => cases b2 <;> simp [evalStatGate, statVal, GateOp.eval]
        | inr b =>
          change val ⟨acc ++ [⟨GateOp.or, [a, b]⟩], 0⟩ x (n + acc.length) =
            GateOp.or.eval [statVal ⟨acc, 0⟩ x (Sum.inr a), statVal ⟨acc, 0⟩ x (Sum.inr b)]
          rw [hnew]
          simp [GateOp.eval, statVal]
    · simp at hins

lemma evalStatGate_bound (op : GateOp) (ins : List (Bool ⊕ ℕ)) (n len : ℕ)
    (hbound : ∀ w, Sum.inr w ∈ ins → w < n + len) :
    ∀ w, (evalStatGate op ins (n + len)).2 = Sum.inr w →
      w < n + (match (evalStatGate op ins (n + len)).1 with | none => len | some _ => len + 1) := by
  cases op <;> simp only [evalStatGate]
  · split_ifs
    · intro w hw; cases hw
    · rcases hfm : ins.filterMap (fun s => match s with | Sum.inr w => some w | Sum.inl _ => none)
        with _ | ⟨a, _ | ⟨b, t⟩⟩ <;> simp only [hfm]
      · intro w hw; cases hw
      · intro w hw
        injection hw with hw'
        subst hw'
        have ha : a ∈ ins.filterMap (fun s => match s with | Sum.inr w => some w | Sum.inl _ => none) := by
          rw [hfm]; simp
        obtain ⟨s, hs, hms⟩ := List.mem_filterMap.mp ha
        cases s with
        | inl _ => simp at hms
        | inr a' =>
          simp at hms
          subst hms
          exact hbound a' hs
      · intro w hw
        injection hw with hw'
        subst hw'
        simp
  · split_ifs
    · intro w hw; cases hw
    · rcases hfm : ins.filterMap (fun s => match s with | Sum.inr w => some w | Sum.inl _ => none)
        with _ | ⟨a, _ | ⟨b, t⟩⟩ <;> simp only [hfm]
      · intro w hw; cases hw
      · intro w hw
        injection hw with hw'
        subst hw'
        have ha : a ∈ ins.filterMap (fun s => match s with | Sum.inr w => some w | Sum.inl _ => none) := by
          rw [hfm]; simp
        obtain ⟨s, hs, hms⟩ := List.mem_filterMap.mp ha
        cases s with
        | inl _ => simp at hms
        | inr a' =>
          simp at hms
          subst hms
          exact hbound a' hs
      · intro w hw
        injection hw with hw'
        subst hw'
        simp
  · intro w hw; cases hw
  · intro w hw; cases hw
  · intro w hw; cases hw

lemma val_append_lt {n : ℕ} (gs1 gs2 : List Gate) (x : Fin n → Bool) (w : ℕ)
    (hw : w < n + gs1.length) :
    val ⟨gs1 ++ gs2, 0⟩ x w = val ⟨gs1, 0⟩ x w := by
  unfold val
  simp only [wires_eq_foldl, List.foldl_append]
  have hlen : (gs1.foldl step (List.ofFn x)).length = n + gs1.length := by
    rw [foldl_step_len, List.length_ofFn]
  exact foldl_step_getD_lt gs2 _ w (by rw [hlen]; exact hw)

lemma statVal_append_lt {n : ℕ} (gs1 gs2 : List Gate) (x : Fin n → Bool) (s : Bool ⊕ ℕ)
    (hs : ∀ w, s = Sum.inr w → w < n + gs1.length) :
    statVal ⟨gs1 ++ gs2, 0⟩ x s = statVal ⟨gs1, 0⟩ x s := by
  cases s with
  | inl b => rfl
  | inr w => exact val_append_lt gs1 gs2 x w (hs w rfl)

lemma simpLoop_props (n skip : ℕ) (repl : Bool ⊕ ℕ) (C : Circuit)
    (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (rest : List Gate) (j : ℕ) (hrest : C.gates.drop j = rest)
    (acc : List Gate) (env : ℕ → Bool ⊕ ℕ)
    (hacc_mono : ∀ g ∈ acc, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (henv_bound : ∀ k < n + j, ∀ w, env k = Sum.inr w → w < n + acc.length)
    (hrepl_bound : ∀ w, repl = Sum.inr w → w < n + acc.length)
    (bad : ℕ → Prop)
    (hbad_keep : ∀ k < n + j, ¬ bad k → ∀ x : Fin n → Bool, statVal ⟨acc, 0⟩ x (env k) = val C x k)
    (hrepl_ok : j ≤ skip → (¬ bad (n + skip) → ∀ x : Fin n → Bool, statVal ⟨acc, 0⟩ x repl = val C x (n + skip)))
    (hbad_unused : ∀ (j' : ℕ) (g : Gate), j ≤ j' → C.gates[j']? = some g → j' ≠ skip →
      ¬ bad (n + j') → ∀ i ∈ g.inputs, i < n + j' → ¬ bad i) :
    let res := simpLoop n skip repl rest j acc env
    (∃ tail, res.1 = acc ++ tail) ∧
    (∀ g ∈ res.1, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
    res.1.length ≤ acc.length + rest.length - (if j ≤ skip ∧ skip < j + rest.length then 1 else 0) ∧
    (∀ k < n + j + rest.length, ∀ w, res.2 k = Sum.inr w → w < n + res.1.length) ∧
    (∀ k < n + j + rest.length, ¬ bad k → ∀ x : Fin n → Bool, statVal ⟨res.1, 0⟩ x (res.2 k) = val C x k) := by
  induction rest generalizing j acc env with
  | nil =>
    have hfalse : ¬ (j ≤ skip ∧ skip < j) := by omega
    simp only [simpLoop, List.length_nil, add_zero, hfalse, ↓reduceIte, Nat.sub_zero]
    exact ⟨⟨[], by simp⟩, hacc_mono, le_refl _, henv_bound, hbad_keep⟩
  | cons g rest ih =>
    have hjlt : j < C.gates.length := by
      have hne : C.gates.drop j ≠ [] := by rw [hrest]; simp
      by_contra hge
      exact hne (List.drop_eq_nil_of_le (Nat.le_of_not_lt hge))
    have hgj : C.gates[j]? = some g := by
      have h0 : (C.gates.drop j)[0]? = some g := by rw [hrest]; rfl
      rw [List.getElem?_drop, Nat.add_zero] at h0
      exact h0
    have hrest' : C.gates.drop (j + 1) = rest := by
      have h1 : (C.gates.drop j).drop 1 = rest := by rw [hrest]; rfl
      rw [List.drop_drop] at h1
      exact h1
    have hgmem : g ∈ C.gates := List.mem_of_getElem? hgj
    have hgmono := hmono g hgmem
    have hgop : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using hgmono.1
    by_cases hjeq : j = skip
    · subst hjeq
      simp only [simpLoop, ↓reduceIte]
      let env' : ℕ → Bool ⊕ ℕ := fun k => if k = n + j then repl else env k
      have henv'_bound : ∀ k < n + (j + 1), ∀ w, env' k = Sum.inr w → w < n + acc.length := by
        intro k hk w hw
        dsimp only [env'] at hw
        split_ifs at hw with hkeq
        · exact hrepl_bound w hw
        · exact henv_bound k (by omega) w hw
      have hbad'_keep : ∀ k < n + (j + 1), ¬ bad k → ∀ x : Fin n → Bool,
          statVal ⟨acc, 0⟩ x (env' k) = val C x k := by
        intro k hk hnb x
        dsimp only [env']
        split_ifs with hkeq
        · subst hkeq
          exact hrepl_ok (le_refl _) hnb x
        · exact hbad_keep k (by omega) hnb x
      obtain ⟨⟨tail, htail⟩, hm, hlen, hb, hval⟩ :=
        ih (j + 1) hrest' acc env' hacc_mono henv'_bound hrepl_bound
          hbad'_keep (fun h => by omega)
          (fun j' g' hj' hg' hne hnb i hi hilt => hbad_unused j' g' (by omega) hg' hne hnb i hi hilt)
      refine ⟨⟨tail, htail⟩, hm, ?_, ?_, ?_⟩
      · have h1 : (if j + 1 ≤ j ∧ j < j + 1 + rest.length then 1 else 0) = 0 :=
          ite_eq_right_iff.mpr (fun h => by omega)
        have h2 : (if j ≤ j ∧ j < j + (rest.length + 1) then 1 else 0) = 1 :=
          ite_eq_left_iff.mpr (fun h => absurd (by omega) h)
        rw [h1] at hlen
        rw [List.length_cons, h2]
        exact hlen.trans (by omega)
      · intro k hk w hw
        exact hb k (by simp only [List.length_cons] at hk; omega) w hw
      · intro k hk hnb x
        exact hval k (by simp only [List.length_cons] at hk; omega) hnb x
    · simp only [simpLoop, hjeq, ↓reduceIte]
      set ins := g.inputs.map (fun i => if i < n + j then env i else Sum.inl false)
      set res0 := evalStatGate g.op ins (n + acc.length)
      set acc' := match res0.1 with | none => acc | some g' => acc ++ [g']
      set env' : ℕ → Bool ⊕ ℕ := fun k => if k = n + j then res0.2 else env k
      have hstep_tail : ∃ t0, acc' = acc ++ t0 ∧ t0.length ≤ 1 := by
        cases h1 : res0.1 with
        | none => exact ⟨[], by simp [acc', h1], by simp⟩
        | some g' => exact ⟨[g'], by simp [acc', h1], by simp⟩
      obtain ⟨t0, ht0, ht0len⟩ := hstep_tail
      have hacc'_mono : ∀ g' ∈ acc', g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 := by
        intro g' hg'
        cases h1 : res0.1 with
        | none =>
          simp only [acc', h1] at hg'
          exact hacc_mono g' hg'
        | some g0 =>
          simp only [acc', h1, List.mem_append, List.mem_singleton] at hg'
          rcases hg' with hg' | rfl
          · exact hacc_mono g' hg'
          · exact evalStatGate_mono g.op ins (n + acc.length) g' h1
      have hins_bound : ∀ w, Sum.inr w ∈ ins → w < n + acc.length := by
        intro w hw
        obtain ⟨i, _, hi⟩ := List.mem_map.mp hw
        by_cases hilt : i < n + j
        · simp only [hilt, ↓reduceIte] at hi
          exact henv_bound i hilt w hi
        · simp only [hilt, ↓reduceIte] at hi
          cases hi
      have hres_bound : ∀ w, res0.2 = Sum.inr w → w < n + acc'.length := by
        intro w hw
        have h := evalStatGate_bound g.op ins n acc.length hins_bound w hw
        cases h1 : res0.1 with
        | none =>
          have h1' : (evalStatGate g.op ins (n + acc.length)).1 = none := h1
          simp only [h1'] at h
          simp only [acc', h1]
          exact h
        | some g0 =>
          have h1' : (evalStatGate g.op ins (n + acc.length)).1 = some g0 := h1
          simp only [h1'] at h
          simp only [acc', h1, List.length_append, List.length_cons, List.length_nil]
          exact h
      have hacc_le : acc.length ≤ acc'.length := by rw [ht0, List.length_append]; omega
      have henv'_bound : ∀ k < n + (j + 1), ∀ w, env' k = Sum.inr w → w < n + acc'.length := by
        intro k hk w hw
        dsimp only [env'] at hw
        split_ifs at hw with hkeq
        · exact hres_bound w hw
        · exact lt_of_lt_of_le (henv_bound k (by omega) w hw) (by omega)
      have hrepl'_bound : ∀ w, repl = Sum.inr w → w < n + acc'.length :=
        fun w hw => lt_of_lt_of_le (hrepl_bound w hw) (by omega)
      have hbad'_keep : ∀ k < n + (j + 1), ¬ bad k → ∀ x : Fin n → Bool,
          statVal ⟨acc', 0⟩ x (env' k) = val C x k := by
        intro k hk hnb x
        dsimp only [env']
        split_ifs with hkeq
        · subst hkeq
          have hev := evalStatGate_val g.op hgop ins (by simp [ins, hgmono.2]) acc hins_bound x
          change statVal ⟨acc', 0⟩ x res0.2 = g.op.eval (ins.map (statVal ⟨acc, 0⟩ x)) at hev
          rw [hev, val_gate C x j g hgj]
          congr 1
          rw [List.map_map]
          apply List.map_congr_left
          intro i hi
          simp only [Function.comp_apply]
          split_ifs with hilt
          · exact hbad_keep i hilt (hbad_unused j g (le_refl _) hgj hjeq hnb i hi hilt) x
          · rfl
        · rw [ht0, statVal_append_lt acc t0 x (env k) (henv_bound k (by omega))]
          exact hbad_keep k (by omega) hnb x
      have hrepl'_ok : j + 1 ≤ skip → (¬ bad (n + skip) → ∀ x : Fin n → Bool,
          statVal ⟨acc', 0⟩ x repl = val C x (n + skip)) := by
        intro hle hnb x
        rw [ht0, statVal_append_lt acc t0 x repl hrepl_bound]
        exact hrepl_ok (by omega) hnb x
      obtain ⟨⟨tail, htail⟩, hm, hlen, hb, hval⟩ :=
        ih (j + 1) hrest' acc' env' hacc'_mono henv'_bound hrepl'_bound
          hbad'_keep hrepl'_ok
          (fun j' g' hj' hg' hne hnb i hi hilt => hbad_unused j' g' (by omega) hg' hne hnb i hi hilt)
      refine ⟨⟨t0 ++ tail, by rw [htail, ht0, List.append_assoc]⟩, hm, ?_, ?_, ?_⟩
      · have hacclen : acc'.length ≤ acc.length + 1 := by rw [ht0, List.length_append]; omega
        simp only [List.length_cons] at hlen ⊢
        split_ifs at hlen ⊢ <;> omega
      · intro k hk w hw
        exact hb k (by simp only [List.length_cons] at hk; omega) w hw
      · intro k hk hnb x
        exact hval k (by simp only [List.length_cons] at hk; omega) hnb x

lemma elim_wire_equiv {n : ℕ} (C : Circuit) (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (hnc : ∃ x y : Fin n → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn y))
    (skip : ℕ) (hskip : skip < C.gates.length)
    (repl : Bool ⊕ ℕ) (hrepl : ∀ w, repl = Sum.inr w → w < n)
    (hrepl_val : ∀ x : Fin n → Bool, statVal ⟨[], 0⟩ x repl = val C x (n + skip)) :
    ∃ C' : Circuit, PEqualNP.MetaComplexity.Monotone2 C' ∧ C'.size < C.size ∧
      ∀ x : Fin n → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  let env0 : ℕ → Bool ⊕ ℕ := fun k => if k < n then Sum.inr k else Sum.inl false
  have hres := simpLoop_props n skip repl C hmono C.gates 0 (by simp) [] env0
    (by simp)
    (fun k hk w hw => by
      dsimp only [env0] at hw
      by_cases hkn : k < n
      · simp only [hkn, ↓reduceIte] at hw; injection hw with hw'; omega
      · simp only [hkn, ↓reduceIte] at hw; cases hw)
    (fun w hw => by simp [hrepl w hw])
    (fun _ => False)
    (fun k hk _ x => by
      dsimp only [env0]
      have hkn : k < n := by omega
      simp only [hkn, ↓reduceIte, statVal]
      rw [val_lt_n ⟨[], 0⟩ x k hkn, val_lt_n C x k hkn])
    (fun _ _ x => hrepl_val x)
    (fun _ _ _ _ _ _ _ _ _ => id)
  obtain ⟨_, hm, hlen, hb, hval⟩ := hres
  set res := simpLoop n skip repl C.gates 0 [] env0
  have hlt : res.1.length < C.gates.length := by
    simp only [List.length_nil, zero_add, Nat.zero_le, true_and, hskip, ↓reduceIte] at hlen
    omega
  by_cases hout : C.output < n + C.gates.length
  · cases hro : res.2 C.output with
    | inl b =>
      exfalso
      obtain ⟨x, y, hxy⟩ := hnc
      have hx := hval C.output (by omega) id x
      have hy := hval C.output (by omega) id y
      rw [hro] at hx hy
      exact hxy (hx.symm.trans hy)
    | inr o =>
      refine ⟨⟨res.1, o⟩, hm, hlt, fun x => ?_⟩
      have hx := hval C.output (by omega) id x
      rw [hro] at hx
      exact hx
  · exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    have hx : C.eval (List.ofFn x) = false := val_ge_len C x C.output (by omega)
    have hy : C.eval (List.ofFn y) = false := val_ge_len C y C.output (by omega)
    exact hxy (hx.trans hy.symm)

lemma elim_wire_copy {n : ℕ} (C : Circuit) (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (hnc : ∃ x y : Fin n → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn y))
    (skip : ℕ) (hskip : skip < C.gates.length)
    (w0 : ℕ) (hw0 : w0 < n + skip)
    (hcopy : ∀ x : Fin n → Bool, val C x w0 = val C x (n + skip)) :
    ∃ C' : Circuit, PEqualNP.MetaComplexity.Monotone2 C' ∧ C'.size < C.size ∧
      ∀ x : Fin n → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  let env0 : ℕ → Bool ⊕ ℕ := fun k => if k < n then Sum.inr k else Sum.inl false
  let p1 := simpLoop n (C.gates.length + 1) (Sum.inl false) (C.gates.take skip) 0 [] env0
  have htake_len : (C.gates.take skip).length = skip := List.length_take_of_le (le_of_lt hskip)
  have h1_aux : ∀ (gs : List Gate) (j : ℕ) (acc : List Gate) (env : ℕ → Bool ⊕ ℕ),
      C.gates.drop j = gs ++ C.gates.drop (j + gs.length) →
      (∀ g ∈ acc, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      (∀ k < n + j, ∀ w, env k = Sum.inr w → w < n + acc.length) →
      (∀ k < n + j, ∀ x : Fin n → Bool, statVal ⟨acc, 0⟩ x (env k) = val C x k) →
      let r := simpLoop n (C.gates.length + 1) (Sum.inl false) gs j acc env
      (∀ g ∈ r.1, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
      r.1.length ≤ acc.length + gs.length ∧
      (∀ k < n + j + gs.length, ∀ w, r.2 k = Sum.inr w → w < n + r.1.length) ∧
      (∀ k < n + j + gs.length, ∀ x : Fin n → Bool, statVal ⟨r.1, 0⟩ x (r.2 k) = val C x k) := by
    intro gs
    induction gs with
    | nil =>
      intro j acc env _ hm hb hv
      simp only [simpLoop, List.length_nil, add_zero]
      exact ⟨hm, le_refl _, hb, hv⟩
    | cons g gs ih =>
      intro j acc env hdrop hm hb hv
      have hgj : C.gates[j]? = some g := by
        have h0 : (C.gates.drop j)[0]? = some g := by rw [hdrop]; rfl
        rw [List.getElem?_drop, Nat.add_zero] at h0
        exact h0
      have hjlt : j < C.gates.length := (List.getElem?_eq_some_iff.mp hgj).1
      have hne : j ≠ C.gates.length + 1 := by omega
      have hdrop' : C.gates.drop (j + 1) = gs ++ C.gates.drop (j + 1 + gs.length) := by
        have h1 : (C.gates.drop j).drop 1 = gs ++ C.gates.drop (j + (g :: gs).length) := by
          rw [hdrop]; rfl
        rw [List.drop_drop] at h1
        simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1 gs.length] using h1
      have hgmono := hmono g (List.mem_of_getElem? hgj)
      have hgop : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using hgmono.1
      simp only [simpLoop, hne, ↓reduceIte]
      set ins := g.inputs.map (fun i => if i < n + j then env i else Sum.inl false)
      set res0 := evalStatGate g.op ins (n + acc.length)
      set acc' := match res0.1 with | none => acc | some g' => acc ++ [g']
      set env' : ℕ → Bool ⊕ ℕ := fun k => if k = n + j then res0.2 else env k
      have hstep_tail : ∃ t0, acc' = acc ++ t0 ∧ t0.length ≤ 1 := by
        cases h1 : res0.1 with
        | none => exact ⟨[], by simp [acc', h1], by simp⟩
        | some g' => exact ⟨[g'], by simp [acc', h1], by simp⟩
      obtain ⟨t0, ht0, ht0len⟩ := hstep_tail
      have hacc'_mono : ∀ g' ∈ acc', g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 := by
        intro g' hg'
        cases h1 : res0.1 with
        | none => simp only [acc', h1] at hg'; exact hm g' hg'
        | some g0 =>
          simp only [acc', h1, List.mem_append, List.mem_singleton] at hg'
          rcases hg' with hg' | rfl
          · exact hm g' hg'
          · exact evalStatGate_mono g.op ins (n + acc.length) g' h1
      have hins_bound : ∀ w, Sum.inr w ∈ ins → w < n + acc.length := by
        intro w hw
        obtain ⟨i, _, hi⟩ := List.mem_map.mp hw
        by_cases hilt : i < n + j
        · simp only [hilt, ↓reduceIte] at hi
          exact hb i hilt w hi
        · simp only [hilt, ↓reduceIte] at hi
          cases hi
      have hres_bound : ∀ w, res0.2 = Sum.inr w → w < n + acc'.length := by
        intro w hw
        have h := evalStatGate_bound g.op ins n acc.length hins_bound w hw
        cases h1 : res0.1 with
        | none =>
          have h1' : (evalStatGate g.op ins (n + acc.length)).1 = none := h1
          simp only [h1'] at h
          simp only [acc', h1]
          exact h
        | some g0 =>
          have h1' : (evalStatGate g.op ins (n + acc.length)).1 = some g0 := h1
          simp only [h1'] at h
          simp only [acc', h1, List.length_append, List.length_cons, List.length_nil]
          exact h
      have hacc_le : acc.length ≤ acc'.length := by rw [ht0, List.length_append]; omega
      have henv'_bound : ∀ k < n + (j + 1), ∀ w, env' k = Sum.inr w → w < n + acc'.length := by
        intro k hk w hw
        dsimp only [env'] at hw
        split_ifs at hw with hkeq
        · exact hres_bound w hw
        · exact lt_of_lt_of_le (hb k (by omega) w hw) (by omega)
      have hv' : ∀ k < n + (j + 1), ∀ x : Fin n → Bool, statVal ⟨acc', 0⟩ x (env' k) = val C x k := by
        intro k hk x
        dsimp only [env']
        split_ifs with hkeq
        · subst hkeq
          have hev := evalStatGate_val g.op hgop ins (by simp [ins, hgmono.2]) acc hins_bound x
          change statVal ⟨acc', 0⟩ x res0.2 = g.op.eval (ins.map (statVal ⟨acc, 0⟩ x)) at hev
          rw [hev, val_gate C x j g hgj]
          congr 1
          rw [List.map_map]
          apply List.map_congr_left
          intro i _
          simp only [Function.comp_apply]
          split_ifs with hilt
          · exact hv i hilt x
          · rfl
        · rw [ht0, statVal_append_lt acc t0 x (env k) (hb k (by omega))]
          exact hv k (by omega) x
      obtain ⟨hm', hlen', hb', hv''⟩ := ih (j + 1) acc' env' hdrop' hacc'_mono henv'_bound hv'
      refine ⟨hm', ?_, ?_, ?_⟩
      · have : acc'.length ≤ acc.length + 1 := by rw [ht0, List.length_append]; omega
        simp only [List.length_cons]; omega
      · intro k hk w hw; exact hb' k (by simp only [List.length_cons] at hk; omega) w hw
      · intro k hk x; exact hv'' k (by simp only [List.length_cons] at hk; omega) x
  obtain ⟨hm1, hlen1, hb1, hv1⟩ := h1_aux (C.gates.take skip) 0 [] env0
    (by simp [htake_len, List.take_append_drop])
    (by simp)
    (fun k hk w hw => by
      dsimp only [env0] at hw
      by_cases hkn : k < n
      · simp only [hkn, ↓reduceIte] at hw; injection hw with hw'; omega
      · simp only [hkn, ↓reduceIte] at hw; cases hw)
    (fun k hk x => by
      dsimp only [env0]
      have hkn : k < n := by omega
      simp only [hkn, ↓reduceIte, statVal]
      rw [val_lt_n ⟨[], 0⟩ x k hkn, val_lt_n C x k hkn])
  have h2 := simpLoop_props n skip (p1.2 w0) C hmono (C.gates.drop skip) skip rfl p1.1 p1.2
    hm1
    (fun k hk w hw => hb1 k (by omega) w hw)
    (fun w hw => hb1 w0 (by omega) w hw)
    (fun _ => False)
    (fun k hk _ x => hv1 k (by omega) x)
    (fun _ _ x => (hv1 w0 (by omega) x).trans (hcopy x))
    (fun _ _ _ _ _ _ _ _ _ => id)
  obtain ⟨_, hm2, hlen2, _, hv2⟩ := h2
  set res := simpLoop n skip (p1.2 w0) (C.gates.drop skip) skip p1.1 p1.2
  have hdrop_len : (C.gates.drop skip).length = C.gates.length - skip := List.length_drop
  have hlt : res.1.length < C.gates.length := by
    have hlen1' : p1.1.length ≤ skip := by
      have : p1.1.length ≤ ([] : List Gate).length + (C.gates.take skip).length := hlen1
      rw [List.length_nil, zero_add, htake_len] at this
      exact this
    have hcond : skip ≤ skip ∧ skip < skip + (C.gates.drop skip).length := by omega
    have hif : (if skip ≤ skip ∧ skip < skip + (C.gates.drop skip).length then 1 else 0) = 1 :=
      ite_eq_left_iff.mpr (fun h => absurd hcond h)
    have hlen2' : res.1.length ≤ p1.1.length + (C.gates.drop skip).length - 1 := by
      rw [hif] at hlen2
      exact hlen2
    omega
  by_cases hout : C.output < n + C.gates.length
  · cases hro : res.2 C.output with
    | inl b =>
      exfalso
      obtain ⟨x, y, hxy⟩ := hnc
      have hx := hv2 C.output (by omega) id x
      have hy := hv2 C.output (by omega) id y
      rw [hro] at hx hy
      exact hxy (hx.symm.trans hy)
    | inr o =>
      refine ⟨⟨res.1, o⟩, hm2, hlt, fun x => ?_⟩
      have hx := hv2 C.output (by omega) id x
      rw [hro] at hx
      exact hx
  · exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    have hx : C.eval (List.ofFn x) = false := val_ge_len C x C.output (by omega)
    have hy : C.eval (List.ofFn y) = false := val_ge_len C y C.output (by omega)
    exact hxy (hx.trans hy.symm)

lemma elim_wire_unused {n : ℕ} (C : Circuit) (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (hnc : ∃ x y : Fin n → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn y))
    (skip : ℕ) (hskip : skip < C.gates.length)
    (hne_out : C.output ≠ n + skip)
    (hunused : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → skip < j → n + skip ∉ g.inputs) :
    ∃ C' : Circuit, PEqualNP.MetaComplexity.Monotone2 C' ∧ C'.size < C.size ∧
      ∀ x : Fin n → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  let env0 : ℕ → Bool ⊕ ℕ := fun k => if k < n then Sum.inr k else Sum.inl false
  have hres := simpLoop_props n skip (Sum.inl false) C hmono C.gates 0 (by simp) [] env0
    (by simp)
    (fun k hk w hw => by
      dsimp only [env0] at hw
      by_cases hkn : k < n
      · simp only [hkn, ↓reduceIte] at hw; injection hw with hw'; omega
      · simp only [hkn, ↓reduceIte] at hw; cases hw)
    (fun _ hw => by cases hw)
    (fun k => k = n + skip)
    (fun k hk _ x => by
      dsimp only [env0]
      have hkn : k < n := by omega
      simp only [hkn, ↓reduceIte, statVal]
      rw [val_lt_n ⟨[], 0⟩ x k hkn, val_lt_n C x k hkn])
    (fun _ hnb => absurd rfl hnb)
    (fun j' g' _ hg' hne _ i hi hilt => by
      intro heq
      subst heq
      exact hunused j' g' hg' (by omega) hi)
  obtain ⟨_, hm, hlen, _, hval⟩ := hres
  set res := simpLoop n skip (Sum.inl false) C.gates 0 [] env0
  have hlt : res.1.length < C.gates.length := by
    simp only [List.length_nil, zero_add, Nat.zero_le, true_and, hskip, ↓reduceIte] at hlen
    omega
  by_cases hout : C.output < n + C.gates.length
  · cases hro : res.2 C.output with
    | inl b =>
      exfalso
      obtain ⟨x, y, hxy⟩ := hnc
      have hx := hval C.output (by omega) hne_out x
      have hy := hval C.output (by omega) hne_out y
      rw [hro] at hx hy
      exact hxy (hx.symm.trans hy)
    | inr o =>
      refine ⟨⟨res.1, o⟩, hm, hlt, fun x => ?_⟩
      have hx := hval C.output (by omega) hne_out x
      rw [hro] at hx
      exact hx
  · exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    have hx : C.eval (List.ofFn x) = false := val_ge_len C x C.output (by omega)
    have hy : C.eval (List.ofFn y) = false := val_ge_len C y C.output (by omega)
    exact hxy (hx.trans hy.symm)

def eof {n : ℕ} (u : Fin n) : Fin n → Bool := fun v => decide (v = u)

def pair {n : ℕ} (u v : Fin n) : Fin n → Bool := fun z => decide (z = u ∨ z = v)

def triple {n : ℕ} (a b c : Fin n) : Fin n → Bool := fun z => decide (z = a ∨ z = b ∨ z = c)

open Classical in
noncomputable def readers (C : Circuit) (w : ℕ) : Finset ℕ :=
  (Finset.range C.gates.length).filter (fun j =>
    match C.gates[j]? with
    | some g => w ∈ g.inputs
    | none => False)

def CleanMin (n : ℕ) (C : Circuit) : Prop :=
  PEqualNP.MetaComplexity.Monotone2 C ∧
  0 < C.gates.length ∧
  C.output = n + C.gates.length - 1 ∧
  (∀ j (g : Gate), C.gates[j]? = some g →
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
    ∃ p q, g.inputs = [p, q] ∧ p < n + j ∧ q < n + j ∧ p ≠ q) ∧
  (∀ j < C.gates.length, (∃ x : Fin n → Bool, val C x (n + j) = false) ∧
    (∃ x : Fin n → Bool, val C x (n + j) = true) ∧
    ∀ w < n + j, ∃ x : Fin n → Bool, val C x (n + j) ≠ val C x w) ∧
  (∀ w < n + C.gates.length - 1, 1 ≤ (readers C w).card)

lemma exists_clean_min {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
    (hdeg : ∀ v : Fin n, (G.neighborSet v).ncard = 3)
    (C0 : Circuit) (hmono0 : PEqualNP.MetaComplexity.Monotone2 C0)
    (heval0 : ∀ x : Fin n → Bool, C0.eval (List.ofFn x) = true ↔
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) :
    ∃ C : Circuit, CleanMin n C ∧ C.size ≤ C0.size ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  classical
  let P : ℕ → Prop := fun s => ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = s ∧
    ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true
  have hex : ∃ s, P s := ⟨C0.size, C0, hmono0, rfl, heval0⟩
  let smin := Nat.find hex
  obtain ⟨C, hmono, hsz, heval⟩ := Nat.find_spec hex
  have hmin : ∀ C' : Circuit, PEqualNP.MetaComplexity.Monotone2 C' →
      (∀ x : Fin n → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x)) →
      C.size ≤ C'.size := by
    intro C' hm' heq'
    have hP' : P C'.size := ⟨C', hm', rfl, fun x => by rw [heq' x]; exact heval x⟩
    have := Nat.find_min' hex hP'
    omega
  have hadj_ex : ∀ v : Fin n, ∃ u : Fin n, G.Adj v u := by
    intro v
    have hpos : 0 < (G.neighborSet v).ncard := by rw [hdeg v]; omega
    obtain ⟨u, hu⟩ := Set.nonempty_of_ncard_ne_zero (by omega : (G.neighborSet v).ncard ≠ 0)
    exact ⟨u, hu⟩
  have hnc : ∃ x y : Fin n → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn y) := by
    obtain ⟨u, hu⟩ := hadj_ex ⟨0, hn⟩
    refine ⟨fun _ => false, pair ⟨0, hn⟩ u, ?_⟩
    have h0 : C.eval (List.ofFn (fun _ : Fin n => false)) = false := by
      cases h : C.eval (List.ofFn (fun _ : Fin n => false))
      · rfl
      · exfalso; obtain ⟨a, b, _, ha, _⟩ := (heval _).mp h; exact absurd ha (by decide)
    have h1 : C.eval (List.ofFn (pair ⟨0, hn⟩ u)) = true :=
      (heval _).mpr ⟨⟨0, hn⟩, u, hu, by simp [pair], by simp [pair]⟩
    rw [h0, h1]; decide
  have hpos_len : 0 < C.gates.length := by
    by_contra h0
    have hnil : C.gates = [] := List.eq_nil_of_length_eq_zero (by omega)
    by_cases ho : C.output < n
    · have h1 : C.eval (List.ofFn (eof ⟨C.output, ho⟩)) = true := by
        change val C (eof ⟨C.output, ho⟩) C.output = true
        rw [val_lt_n C _ C.output ho]
        simp [eof]
      obtain ⟨a, b, hab, ha, hb⟩ := (heval _).mp h1
      simp only [eof, decide_eq_true_eq] at ha hb
      subst ha; subst hb
      exact G.irrefl hab
    · obtain ⟨x, y, hxy⟩ := hnc
      have hx : C.eval (List.ofFn x) = false := val_ge_len C x C.output (by rw [hnil]; simp; omega)
      have hy : C.eval (List.ofFn y) = false := val_ge_len C y C.output (by rw [hnil]; simp; omega)
      exact hxy (hx.trans hy.symm)
  have hnot_const_false : ∀ j < C.gates.length, ∃ x : Fin n → Bool, val C x (n + j) = true := by
    intro j hj
    by_contra hall
    push Not at hall
    have hf : ∀ x : Fin n → Bool, val C x (n + j) = false := fun x =>
      Bool.eq_false_iff.mpr (hall x)
    obtain ⟨C', hm', hlt', heq'⟩ := elim_wire_equiv C hmono hnc j hj (Sum.inl false)
      (fun _ h => by cases h) (fun x => (hf x).symm)
    have := hmin C' hm' heq'
    omega
  have hnot_const_true : ∀ j < C.gates.length, ∃ x : Fin n → Bool, val C x (n + j) = false := by
    intro j hj
    by_contra hall
    push Not at hall
    have ht : ∀ x : Fin n → Bool, val C x (n + j) = true := fun x =>
      Bool.eq_true_of_not_eq_false (hall x)
    obtain ⟨C', hm', hlt', heq'⟩ := elim_wire_equiv C hmono hnc j hj (Sum.inl true)
      (fun _ h => by cases h) (fun x => (ht x).symm)
    have := hmin C' hm' heq'
    omega
  have hnot_copy : ∀ j < C.gates.length, ∀ w < n + j, ∃ x : Fin n → Bool, val C x (n + j) ≠ val C x w := by
    intro j hj w hw
    by_contra hall
    push Not at hall
    have hc : ∀ x : Fin n → Bool, val C x w = val C x (n + j) := fun x => (hall x).symm
    obtain ⟨C', hm', hlt', heq'⟩ := elim_wire_copy C hmono hnc j hj w hw hc
    have := hmin C' hm' heq'
    omega
  have hgates : ∀ j (g : Gate), C.gates[j]? = some g →
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ p q, g.inputs = [p, q] ∧ p < n + j ∧ q < n + j ∧ p ≠ q := by
    intro j g hj
    have hjlt : j < C.gates.length := (List.getElem?_eq_some_iff.mp hj).1
    have hgmono := hmono g (List.mem_of_getElem? hj)
    have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using hgmono.1
    refine ⟨hop, ?_⟩
    rcases hins : g.inputs with _ | ⟨p, _ | ⟨q, _ | ⟨r, t⟩⟩⟩
    · exfalso
      rcases hop with hand | hor
      · obtain ⟨x, hx⟩ := hnot_const_true j hjlt
        rw [val_gate C x j g hj, hand, hins] at hx
        simp [GateOp.eval] at hx
      · obtain ⟨x, hx⟩ := hnot_const_false j hjlt
        rw [val_gate C x j g hj, hor, hins] at hx
        simp [GateOp.eval] at hx
    · exfalso
      by_cases hp : p < n + j
      · obtain ⟨x, hx⟩ := hnot_copy j hjlt p hp
        rw [val_gate C x j g hj, hins] at hx
        rcases hop with hand | hor
        · rw [hand] at hx; simp [GateOp.eval, hp] at hx
        · rw [hor] at hx; simp [GateOp.eval, hp] at hx
      · obtain ⟨x, hx⟩ := hnot_const_false j hjlt
        rw [val_gate C x j g hj, hins] at hx
        rcases hop with hand | hor
        · rw [hand] at hx; simp [GateOp.eval, hp] at hx
        · rw [hor] at hx; simp [GateOp.eval, hp] at hx
    · refine ⟨p, q, rfl, ?_, ?_, ?_⟩
      · by_contra hge
        rcases hop with hand | hor
        · obtain ⟨x, hx⟩ := hnot_const_false j hjlt
          rw [val_gate C x j g hj, hand, hins] at hx
          simp [GateOp.eval, hge] at hx
        · by_cases hq : q < n + j
          · obtain ⟨x, hx⟩ := hnot_copy j hjlt q hq
            rw [val_gate C x j g hj, hor, hins] at hx
            simp [GateOp.eval, hge, hq] at hx
          · obtain ⟨x, hx⟩ := hnot_const_false j hjlt
            rw [val_gate C x j g hj, hor, hins] at hx
            simp [GateOp.eval, hge, hq] at hx
      · by_contra hge
        rcases hop with hand | hor
        · obtain ⟨x, hx⟩ := hnot_const_false j hjlt
          rw [val_gate C x j g hj, hand, hins] at hx
          simp [GateOp.eval, hge] at hx
        · by_cases hp : p < n + j
          · obtain ⟨x, hx⟩ := hnot_copy j hjlt p hp
            rw [val_gate C x j g hj, hor, hins] at hx
            simp [GateOp.eval, hge, hp] at hx
          · obtain ⟨x, hx⟩ := hnot_const_false j hjlt
            rw [val_gate C x j g hj, hor, hins] at hx
            simp [GateOp.eval, hge, hp] at hx
      · intro hpq
        subst hpq
        by_cases hp : p < n + j
        · obtain ⟨x, hx⟩ := hnot_copy j hjlt p hp
          rw [val_gate C x j g hj, hins] at hx
          rcases hop with hand | hor
          · rw [hand] at hx; simp [GateOp.eval, hp] at hx
          · rw [hor] at hx; simp [GateOp.eval, hp] at hx
        · obtain ⟨x, hx⟩ := hnot_const_false j hjlt
          rw [val_gate C x j g hj, hins] at hx
          rcases hop with hand | hor
          · rw [hand] at hx; simp [GateOp.eval, hp] at hx
          · rw [hor] at hx; simp [GateOp.eval, hp] at hx
    · have := hgmono.2
      rw [hins] at this
      simp at this
  have hgate_used : ∀ j < C.gates.length, C.output ≠ n + j → 1 ≤ (readers C (n + j)).card := by
    intro j hj hne
    by_contra hlt
    have hempty : readers C (n + j) = ∅ := Finset.card_eq_zero.mp (by omega)
    have hunused : ∀ (j' : ℕ) (g' : Gate), C.gates[j']? = some g' → j < j' → n + j ∉ g'.inputs := by
      intro j' g' hg' hjj' hmem
      have hj'lt : j' < C.gates.length := (List.getElem?_eq_some_iff.mp hg').1
      have : j' ∈ readers C (n + j) := by
        simp only [readers, Finset.mem_filter, Finset.mem_range, hg']
        exact ⟨hj'lt, hmem⟩
      rw [hempty] at this
      exact Finset.notMem_empty _ this
    obtain ⟨C', hm', hlt', heq'⟩ := elim_wire_unused C hmono hnc j hj hne hunused
    have := hmin C' hm' heq'
    omega
  have hout : C.output = n + C.gates.length - 1 := by
    by_contra hne
    have hlast_lt : C.gates.length - 1 < C.gates.length := by omega
    have hne' : C.output ≠ n + (C.gates.length - 1) := by omega
    have hpos := hgate_used (C.gates.length - 1) hlast_lt hne'
    obtain ⟨j', hj'⟩ := Finset.card_pos.mp hpos
    simp only [readers, Finset.mem_filter, Finset.mem_range] at hj'
    obtain ⟨hj'lt, hmem⟩ := hj'
    have hg' : C.gates[j']? = some (C.gates[j']'hj'lt) := List.getElem?_eq_getElem hj'lt
    rw [hg'] at hmem
    dsimp only at hmem
    obtain ⟨_, p, q, hin, hp, hq, _⟩ := hgates j' _ hg'
    rw [hin] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with hmem | hmem <;> omega
  have hinp_used : ∀ v : Fin n, 1 ≤ (readers C v.val).card := by
    intro v
    by_contra hlt
    have hempty : readers C v.val = ∅ := Finset.card_eq_zero.mp (by omega)
    have hindep : ∀ (x y : Fin n → Bool), (∀ z ≠ v, x z = y z) →
        ∀ k, k ≠ v.val → val C x k = val C y k := by
      intro x y hxy k
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        intro hkv
        by_cases h1 : k < n
        · rw [val_lt_n C x k h1, val_lt_n C y k h1]
          exact hxy ⟨k, h1⟩ (fun h => hkv (congrArg Fin.val h))
        · by_cases h2 : n + C.gates.length ≤ k
          · rw [val_ge_len C x k h2, val_ge_len C y k h2]
          · have hjlt : k - n < C.gates.length := by omega
            set j := k - n
            have hkj : k = n + j := by omega
            have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
            obtain ⟨_, p, q, hin, hp, hq, _⟩ := hgates j _ hg
            have hnv : v.val ∉ (C.gates[j]'hjlt).inputs := by
              intro hmem
              have : j ∈ readers C v.val := by
                simp only [readers, Finset.mem_filter, Finset.mem_range, hg]
                exact ⟨hjlt, hmem⟩
              rw [hempty] at this
              exact Finset.notMem_empty _ this
            rw [hin] at hnv
            have hpne : p ≠ v.val := fun h => hnv (by simp [h])
            have hqne : q ≠ v.val := fun h => hnv (by simp [h])
            rw [hkj, val_gate C x j _ hg, val_gate C y j _ hg, hin]
            simp only [List.map_cons, List.map_nil, hp, hq, ↓reduceIte]
            rw [ih p (by omega) hpne, ih q (by omega) hqne]
    obtain ⟨u, hu⟩ := hadj_ex v
    have hvu : v ≠ u := G.ne_of_adj hu
    have h0 : C.eval (List.ofFn (eof u)) = false := by
      cases h : C.eval (List.ofFn (eof u))
      · rfl
      · exfalso
        obtain ⟨a, b, hab, ha, hb⟩ := (heval _).mp h
        simp only [eof, decide_eq_true_eq] at ha hb
        subst ha; subst hb
        exact G.irrefl hab
    have h1 : C.eval (List.ofFn (pair v u)) = true :=
      (heval _).mpr ⟨v, u, hu, by simp [pair], by simp [pair]⟩
    have heq : val C (eof u) C.output = val C (pair v u) C.output :=
      hindep (eof u) (pair v u) (fun z hz => by simp [eof, pair, hz]) C.output (by omega)
    change C.eval (List.ofFn (eof u)) = C.eval (List.ofFn (pair v u)) at heq
    rw [h0, h1] at heq
    exact absurd heq (by decide)
  refine ⟨C, ⟨hmono, hpos_len, hout, hgates, ?_, ?_⟩, ?_, heval⟩
  · intro j hj
    exact ⟨hnot_const_true j hj, hnot_const_false j hj, hnot_copy j hj⟩
  · intro w hw
    by_cases hwn : w < n
    · exact hinp_used ⟨w, hwn⟩
    · have hjlt : w - n < C.gates.length := by omega
      have hwj : w = n + (w - n) := by omega
      rw [hwj]
      exact hgate_used (w - n) hjlt (by omega)
  · have := Nat.find_min' hex ⟨C0, hmono0, rfl, heval0⟩
    omega

lemma clean_readers_out_empty {n : ℕ} {C : Circuit} (hC : CleanMin n C) :
    readers C (n + C.gates.length - 1) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro j hj
  simp only [readers, Finset.mem_filter, Finset.mem_range] at hj
  obtain ⟨hjlt, hmem⟩ := hj
  have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
  rw [hg] at hmem
  dsimp only at hmem
  obtain ⟨_, p, q, hin, hp, hq, _⟩ := hC.2.2.2.1 j _ hg
  rw [hin] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with hmem | hmem <;> omega

lemma double_count_excess {n : ℕ} (hn : 0 < n) {C : Circuit} (hC : CleanMin n C) :
    (n - 1) + ∑ w ∈ Finset.range (n + C.gates.length - 1), ((readers C w).card - 1) =
      C.gates.length := by
  classical
  have hpos := hC.2.1
  have hsum_all : ∑ w ∈ Finset.range (n + C.gates.length), (readers C w).card =
      2 * C.gates.length := by
    have h1 : ∀ w, (readers C w).card =
        ∑ j ∈ Finset.range C.gates.length,
          if (match C.gates[j]? with | some g => w ∈ g.inputs | none => False) then 1 else 0 := by
      intro w
      simp only [readers, Finset.card_filter]
    simp_rw [h1]
    rw [Finset.sum_comm]
    have h2 : ∀ j ∈ Finset.range C.gates.length,
        (∑ w ∈ Finset.range (n + C.gates.length),
          if (match C.gates[j]? with | some g => w ∈ g.inputs | none => False) then 1 else 0) = 2 := by
      intro j hj
      have hjlt : j < C.gates.length := Finset.mem_range.mp hj
      have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
      obtain ⟨_, p, q, hin, hp, hq, hpq⟩ := hC.2.2.2.1 j _ hg
      simp only [hg, hin, List.mem_cons, List.not_mem_nil, or_false]
      rw [← Finset.card_filter]
      have heq : (Finset.range (n + C.gates.length)).filter (fun w => w = p ∨ w = q) = {p, q} := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro h; exact h.2
        · intro h; refine ⟨?_, h⟩; rcases h with rfl | rfl <;> omega
      rw [heq, Finset.card_pair hpq]
    rw [Finset.sum_congr rfl h2, Finset.sum_const, Finset.card_range, smul_eq_mul]
    omega
  have hsplit : ∑ w ∈ Finset.range (n + C.gates.length), (readers C w).card =
      ∑ w ∈ Finset.range (n + C.gates.length - 1), (readers C w).card := by
    have hlen : n + C.gates.length = (n + C.gates.length - 1) + 1 := by omega
    conv_lhs => rw [hlen]
    rw [Finset.sum_range_succ, clean_readers_out_empty hC, Finset.card_empty, add_zero]
  have hsum_ge : ∑ w ∈ Finset.range (n + C.gates.length - 1), (readers C w).card =
      (∑ w ∈ Finset.range (n + C.gates.length - 1), ((readers C w).card - 1)) +
        (n + C.gates.length - 1) := by
    have h3 : ∀ w ∈ Finset.range (n + C.gates.length - 1),
        (readers C w).card = ((readers C w).card - 1) + 1 := by
      intro w hw
      have := hC.2.2.2.2.2 w (Finset.mem_range.mp hw)
      omega
    rw [Finset.sum_congr rfl h3, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      smul_eq_mul, mul_one]
  omega

noncomputable def stepChain (n : ℕ) (C : Circuit) (w : ℕ) : Option ℕ :=
  open Classical in
  if h : (readers C w).card = 1 then
    let j := (Finset.card_eq_one.mp h).choose
    match C.gates[j]? with
    | some g => if g.op = GateOp.or then some (n + j) else none
    | none => none
  else none

noncomputable def followChain (n : ℕ) (C : Circuit) : ℕ → ℕ → List ℕ
  | 0, w => [w]
  | fuel + 1, w =>
    match stepChain n C w with
    | none => [w]
    | some w' => w :: followChain n C fuel w'

lemma followChain_ne_nil (n : ℕ) (C : Circuit) (fuel w : ℕ) :
    followChain n C fuel w ≠ [] := by
  cases fuel with
  | zero => simp [followChain]
  | succ f =>
    simp only [followChain]
    cases stepChain n C w <;> simp

lemma followChain_cons_getLast (n : ℕ) (C : Circuit) (f w w' : ℕ)
    (hst : stepChain n C w = some w') :
    (followChain n C (f + 1) w).getLast (followChain_ne_nil n C (f + 1) w) =
      (followChain n C f w').getLast (followChain_ne_nil n C f w') := by
  simp only [followChain, hst, List.getLast_cons (followChain_ne_nil n C f w')]

lemma mem_followChain_self (n : ℕ) (C : Circuit) (fuel w : ℕ) :
    w ∈ followChain n C fuel w := by
  cases fuel with
  | zero => simp [followChain]
  | succ f =>
    simp only [followChain]
    cases stepChain n C w <;> simp

lemma stepChain_some_props {n : ℕ} {C : Circuit} (hC : CleanMin n C) {w w' : ℕ}
    (hs : stepChain n C w = some w') :
    ∃ j < C.gates.length, ∃ g : Gate,
      C.gates[j]? = some g ∧ g.op = GateOp.or ∧ readers C w = {j} ∧
      w' = n + j ∧ w < w' ∧ w ∈ g.inputs := by
  classical
  simp only [stepChain] at hs
  by_cases h1 : (readers C w).card = 1
  · simp only [h1, ↓reduceDIte] at hs
    set j := (Finset.card_eq_one.mp h1).choose
    have hj_eq : readers C w = {j} := (Finset.card_eq_one.mp h1).choose_spec
    have hj_mem : j ∈ readers C w := by rw [hj_eq]; simp
    simp only [readers, Finset.mem_filter, Finset.mem_range] at hj_mem
    obtain ⟨hjlt, hmem⟩ := hj_mem
    have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
    rw [hg] at hs hmem
    dsimp only at hs hmem
    by_cases hor : (C.gates[j]'hjlt).op = GateOp.or
    · simp only [hor, ↓reduceIte] at hs
      injection hs with hw'
      obtain ⟨_, p, q, hin, hp, hq, _⟩ := hC.2.2.2.1 j _ hg
      have hwlt : w < n + j := by
        rw [hin] at hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl <;> omega
      exact ⟨j, hjlt, C.gates[j]'hjlt, hg, hor, hj_eq, hw'.symm, by omega, hmem⟩
    · simp only [hor, ↓reduceIte] at hs
      cases hs
  · simp only [h1, ↓reduceDIte] at hs
    cases hs

lemma followChain_props {n : ℕ} {C : Circuit} (hC : CleanMin n C) :
    ∀ (fuel w : ℕ), w < n + C.gates.length → n + C.gates.length - w ≤ fuel →
      let L := followChain n C fuel w
      let e := L.getLast (followChain_ne_nil n C fuel w)
      stepChain n C e = none ∧
      e ∈ L ∧
      (∀ c ∈ L, w ≤ c ∧ c < n + C.gates.length) ∧
      (∀ c ∈ L, ∀ x : Fin n → Bool, val C x w = true → val C x c = true) ∧
      (∀ c ∈ L, c ≠ e → ∃ j < C.gates.length, readers C c = {j} ∧ n + j ∈ L) := by
  intro fuel
  induction fuel with
  | zero =>
    intro w hw hfuel
    omega
  | succ f ih =>
    intro w hw hfuel
    cases hst : stepChain n C w with
    | none =>
      dsimp only
      have hL : followChain n C (f + 1) w = [w] := by simp [followChain, hst]
      have hlast : (followChain n C (f + 1) w).getLast (followChain_ne_nil n C (f + 1) w) = w := by
        simp [followChain, hst]
      rw [hlast, hL]
      refine ⟨hst, List.mem_singleton_self w,
        fun c hc => by rw [List.mem_singleton.mp hc]; exact ⟨le_refl _, hw⟩,
        fun c hc x hx => by rw [List.mem_singleton.mp hc]; exact hx,
        fun c hc hne => absurd (List.mem_singleton.mp hc) hne⟩
    | some w' =>
      obtain ⟨j, hjlt, g, hg, hor, hread, hw'eq, hwlt, hwmem⟩ := stepChain_some_props hC hst
      have hw'lt : w' < n + C.gates.length := by omega
      obtain ⟨hend, hemem, hbounds, hmono_w', hstep_w'⟩ := ih w' hw'lt (by omega)
      have hL : followChain n C (f + 1) w = w :: followChain n C f w' := by
        simp [followChain, hst]
      have hlast := followChain_cons_getLast n C f w w' hst
      have hval_step : ∀ x : Fin n → Bool, val C x w = true → val C x w' = true := by
        intro x hx
        rw [hw'eq, val_gate C x j g hg, hor]
        simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
        exact ⟨true, ⟨w, hwmem, by simp [show w < n + j by omega, hx]⟩, rfl⟩
      dsimp only
      rw [hlast, hL]
      refine ⟨hend, List.mem_cons_of_mem _ hemem, ?_, ?_, ?_⟩
      · intro c hc
        rcases List.mem_cons.mp hc with rfl | hc'
        · exact ⟨le_refl _, hw⟩
        · have := hbounds c hc'
          exact ⟨by omega, this.2⟩
      · intro c hc x hx
        rcases List.mem_cons.mp hc with rfl | hc'
        · exact hx
        · exact hmono_w' c hc' x (hval_step x hx)
      · intro c hc hne
        rcases List.mem_cons.mp hc with rfl | hc'
        · exact ⟨j, hjlt, hread, List.mem_cons_of_mem _ (hw'eq ▸ mem_followChain_self n C f w')⟩
        · obtain ⟨j', hj'lt, hr', hmem'⟩ := hstep_w' c hc' hne
          exact ⟨j', hj'lt, hr', List.mem_cons_of_mem _ hmem'⟩

noncomputable def chainL {n : ℕ} (C : Circuit) (u : Fin n) : List ℕ :=
  followChain n C (n + C.gates.length) u.val

noncomputable def endW {n : ℕ} (C : Circuit) (u : Fin n) : ℕ :=
  (chainL C u).getLast (followChain_ne_nil n C (n + C.gates.length) u.val)

lemma chain_props {n : ℕ} {C : Circuit} (hC : CleanMin n C) (u : Fin n) :
    stepChain n C (endW C u) = none ∧
    endW C u ∈ chainL C u ∧
    u.val ∈ chainL C u ∧
    (∀ c ∈ chainL C u, u.val ≤ c ∧ c < n + C.gates.length) ∧
    (∀ c ∈ chainL C u, ∀ x : Fin n → Bool, x u = true → val C x c = true) ∧
    (∀ c ∈ chainL C u, c ≠ endW C u → ∃ j < C.gates.length, readers C c = {j} ∧ n + j ∈ chainL C u) := by
  have h := followChain_props hC (n + C.gates.length) u.val (by omega) (by omega)
  refine ⟨h.1, h.2.1, mem_followChain_self n C (n + C.gates.length) u.val, h.2.2.1, ?_, h.2.2.2.2⟩
  intro c hc x hxu
  exact h.2.2.2.1 c hc x (by rw [val_lt_n C x u.val u.isLt]; exact hxu)

lemma no_leakage {n : ℕ} {C : Circuit} (hC : CleanMin n C) (u : Fin n)
    (x y : Fin n → Bool) (hxy : ∀ z ≠ u, x z = y z)
    (hend : val C x (endW C u) = val C y (endW C u)) :
    ∀ k, k ∉ chainL C u → val C x k = val C y k := by
  have hp := chain_props hC u
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk
    by_cases h1 : k < n
    · rw [val_lt_n C x k h1, val_lt_n C y k h1]
      apply hxy
      intro heq
      apply hk
      have : k = u.val := congrArg Fin.val heq
      rw [this]
      exact hp.2.2.1
    · by_cases h2 : n + C.gates.length ≤ k
      · rw [val_ge_len C x k h2, val_ge_len C y k h2]
      · have hjlt : k - n < C.gates.length := by omega
        set j := k - n
        have hkj : k = n + j := by omega
        have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
        obtain ⟨_, p, q, hin, hp_lt, hq_lt, _⟩ := hC.2.2.2.1 j _ hg
        have hin_eq : ∀ i, i < n + j → i ∈ (C.gates[j]'hjlt).inputs → val C x i = val C y i := by
          intro i hilt himem
          by_cases hic : i ∈ chainL C u
          · by_cases hie : i = endW C u
            · rw [hie]; exact hend
            · exfalso
              obtain ⟨j', _, hr', hj'mem⟩ := hp.2.2.2.2.2 i hic hie
              have hjmem : j ∈ readers C i := by
                simp only [readers, Finset.mem_filter, Finset.mem_range, hg]
                exact ⟨hjlt, himem⟩
              rw [hr', Finset.mem_singleton] at hjmem
              subst hjmem
              exact hk (hkj ▸ hj'mem)
          · exact ih i (by omega) hic
        rw [hkj, val_gate C x j _ hg, val_gate C y j _ hg, hin]
        simp only [List.map_cons, List.map_nil, hp_lt, hq_lt, ↓reduceIte]
        rw [hin_eq p hp_lt (by rw [hin]; simp), hin_eq q hq_lt (by rw [hin]; simp)]

lemma chain_singleton_iff {n : ℕ} (G : SimpleGraph (Fin n))
    (hdeg : ∀ v : Fin n, (G.neighborSet v).ncard = 3)
    (hc4 : ∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a)
    {C : Circuit} (hC : CleanMin n C)
    (heval : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)
    (u : Fin n) :
    ∀ c ∈ chainL C u, ∀ z : Fin n, val C (eof z) c = true ↔ z = u := by
  have hp := chain_props hC u
  have hout_not_mem : C.output ∉ chainL C u := by
    intro hmem
    have h1 := hp.2.2.2.2.1 C.output hmem (eof u) (by simp [eof])
    obtain ⟨a, b, hab, ha, hb⟩ := (heval (eof u)).mp h1
    simp only [eof, decide_eq_true_eq] at ha hb
    subst ha; subst hb
    exact G.irrefl hab
  have hend_only : ∀ z : Fin n, val C (eof z) (endW C u) = true → z = u := by
    intro z hz
    by_contra hzu
    have hadj_all : ∀ y : Fin n, G.Adj u y → G.Adj z y := by
      intro y huy
      have hv0 : val C (pair z y) (endW C u) = true :=
        val_mono C hC.1 (eof z) (pair z y) (fun w hw => by simp only [eof, decide_eq_true_eq] at hw; simp [pair, hw]) _ hz
      have hv1 : val C (triple z y u) (endW C u) = true :=
        val_mono C hC.1 (pair z y) (triple z y u) (fun w hw => by
          simp only [pair, decide_eq_true_eq] at hw
          rcases hw with rfl | rfl <;> simp [triple]) _ hv0
      have heq_out := no_leakage hC u (pair z y) (triple z y u)
        (fun w hw => by simp [pair, triple, hw]) (hv0.trans hv1.symm) C.output hout_not_mem
      have htri : C.eval (List.ofFn (triple z y u)) = true :=
        (heval _).mpr ⟨u, y, huy, by simp [triple], by simp [triple]⟩
      change C.eval (List.ofFn (pair z y)) = C.eval (List.ofFn (triple z y u)) at heq_out
      rw [htri] at heq_out
      obtain ⟨a, b, hab, ha, hb⟩ := (heval _).mp heq_out
      simp only [pair, decide_eq_true_eq] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact absurd hab (G.irrefl)
      · exact hab
      · exact hab.symm
      · exact absurd hab (G.irrefl)
    have hcard : (G.neighborSet u).ncard = 3 := hdeg u
    have hfin : (G.neighborSet u).Finite := Set.toFinite _
    have hcard_f : hfin.toFinset.card = 3 := by
      rw [← Set.ncard_eq_toFinset_card (G.neighborSet u) hfin]; exact hcard
    have hgt1 : 1 < hfin.toFinset.card := by omega
    obtain ⟨y1, hy1, y2, hy2, hy12⟩ := Finset.one_lt_card.mp hgt1
    have huy1 : G.Adj u y1 := (hfin.mem_toFinset).mp hy1
    have huy2 : G.Adj u y2 := (hfin.mem_toFinset).mp hy2
    have hzy1 : G.Adj z y1 := hadj_all y1 huy1
    have hzy2 : G.Adj z y2 := hadj_all y2 huy2
    exact hc4 u y1 z y2 (G.ne_of_adj huy1) (Ne.symm hzu) (G.ne_of_adj huy2)
      (G.ne_of_adj hzy1.symm) hy12 (G.ne_of_adj hzy2)
      huy1 hzy1.symm hzy2 huy2.symm
  have hle_end : ∀ c ∈ chainL C u, ∀ x : Fin n → Bool, val C x c = true → val C x (endW C u) = true := by
    have hrec : ∀ (fuel w : ℕ), w < n + C.gates.length → n + C.gates.length - w ≤ fuel →
        ∀ c ∈ followChain n C fuel w, ∀ x : Fin n → Bool,
          val C x c = true → val C x ((followChain n C fuel w).getLast (followChain_ne_nil n C fuel w)) = true := by
      intro fuel
      induction fuel with
      | zero => intro w hw hfuel; omega
      | succ f ih =>
        intro w hw hfuel c hc x hxc
        cases hst : stepChain n C w with
        | none =>
          have hL : followChain n C (f + 1) w = [w] := by simp [followChain, hst]
          have hlast : (followChain n C (f + 1) w).getLast (followChain_ne_nil n C (f + 1) w) = w := by
            simp [followChain, hst]
          rw [hlast]
          rw [hL, List.mem_singleton] at hc
          subst hc; exact hxc
        | some w' =>
          obtain ⟨j, hjlt, g, hg, hor, _, hw'eq, hwlt, hwmem⟩ := stepChain_some_props hC hst
          have hL : followChain n C (f + 1) w = w :: followChain n C f w' := by simp [followChain, hst]
          rw [followChain_cons_getLast n C f w w' hst]
          rw [hL] at hc
          rcases List.mem_cons.mp hc with rfl | hc'
          · have hw't : val C x w' = true := by
              rw [hw'eq, val_gate C x j g hg, hor]
              simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
              exact ⟨true, ⟨c, hwmem, by simp [show c < n + j by omega, hxc]⟩, rfl⟩
            exact ih w' (by omega) (by omega) w' (mem_followChain_self n C f w') x hw't
          · exact ih w' (by omega) (by omega) c hc' x hxc
    exact hrec (n + C.gates.length) u.val (by omega) (by omega)
  intro c hc z
  constructor
  · intro hcz
    exact hend_only z (hle_end c hc (eof z) hcz)
  · rintro rfl
    exact hp.2.2.2.2.1 c hc (eof z) (by simp [eof])

lemma endW_lt_out {n : ℕ} (G : SimpleGraph (Fin n))
    {C : Circuit} (hC : CleanMin n C)
    (heval : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)
    (u : Fin n) : endW C u < n + C.gates.length - 1 := by
  have hp := chain_props hC u
  have hlt := (hp.2.2.2.1 (endW C u) hp.2.1).2
  have hne : endW C u ≠ C.output := by
    intro heq
    have h1 := hp.2.2.2.2.1 (endW C u) hp.2.1 (eof u) (by simp [eof])
    rw [heq] at h1
    obtain ⟨a, b, hab, ha, hb⟩ := (heval (eof u)).mp h1
    simp only [eof, decide_eq_true_eq] at ha hb
    subst ha; subst hb
    exact G.irrefl hab
  have hout := hC.2.2.1
  omega

lemma type2_and_gate {n : ℕ} (G : SimpleGraph (Fin n))
    {C : Circuit} (hC : CleanMin n C)
    (heval : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)
    (u : Fin n) (hcard1 : ¬ 2 ≤ (readers C (endW C u)).card) :
    ∃ j < C.gates.length, ∃ g : Gate, ∃ h : ℕ,
      C.gates[j]? = some g ∧ g.op = GateOp.and ∧
      readers C (endW C u) = {j} ∧
      (g.inputs = [endW C u, h] ∨ g.inputs = [h, endW C u]) ∧
      h < n + j ∧ h ≠ endW C u := by
  have hlt := endW_lt_out G hC heval u
  have hge1 := hC.2.2.2.2.2 (endW C u) hlt
  have hcard : (readers C (endW C u)).card = 1 := by omega
  obtain ⟨j, hj_eq⟩ := Finset.card_eq_one.mp hcard
  have hj_mem : j ∈ readers C (endW C u) := by rw [hj_eq]; simp
  simp only [readers, Finset.mem_filter, Finset.mem_range] at hj_mem
  obtain ⟨hjlt, hmem⟩ := hj_mem
  have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
  rw [hg] at hmem
  dsimp only at hmem
  obtain ⟨hop, p, q, hin, hp, hq, hpq⟩ := hC.2.2.2.1 j _ hg
  have hand : (C.gates[j]'hjlt).op = GateOp.and := by
    rcases hop with hand | hor
    · exact hand
    · exfalso
      have hst := (chain_props hC u).1
      classical
      simp only [stepChain, hcard, ↓reduceDIte] at hst
      have hch : (Finset.card_eq_one.mp hcard).choose = j := by
        have hspec : readers C (endW C u) = {(Finset.card_eq_one.mp hcard).choose} :=
          (Finset.card_eq_one.mp hcard).choose_spec
        exact (Finset.singleton_injective (hj_eq.symm.trans hspec)).symm
      rw [hch, hg] at hst
      dsimp only at hst
      rw [hor] at hst
      simp at hst
  rw [hin] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · exact ⟨j, hjlt, C.gates[j]'hjlt, q, hg, hand, hj_eq, Or.inl hin, hq, hpq.symm⟩
  · exact ⟨j, hjlt, C.gates[j]'hjlt, p, hg, hand, hj_eq, Or.inr hin, hp, hpq⟩

lemma and_no_leakage {n : ℕ} {C : Circuit} (hC : CleanMin n C) (u : Fin n)
    (j : ℕ) (hread : readers C (endW C u) = {j})
    (x y : Fin n → Bool) (hxy : ∀ z ≠ u, x z = y z)
    (hgj : val C x (n + j) = val C y (n + j)) :
    ∀ k, k ∉ chainL C u → val C x k = val C y k := by
  have hp := chain_props hC u
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk
    by_cases hkj_eq : k = n + j
    · rw [hkj_eq]; exact hgj
    · by_cases h1 : k < n
      · rw [val_lt_n C x k h1, val_lt_n C y k h1]
        apply hxy
        intro heq
        apply hk
        have hku : k = u.val := congrArg Fin.val heq
        rw [hku]
        exact hp.2.2.1
      · by_cases h2 : n + C.gates.length ≤ k
        · rw [val_ge_len C x k h2, val_ge_len C y k h2]
        · have hj'lt : k - n < C.gates.length := by omega
          set j' := k - n
          have hkj' : k = n + j' := by omega
          have hg' : C.gates[j']? = some (C.gates[j']'hj'lt) := List.getElem?_eq_getElem hj'lt
          obtain ⟨_, p, q, hin, hp_lt, hq_lt, _⟩ := hC.2.2.2.1 j' _ hg'
          have hin_eq : ∀ i, i < n + j' → i ∈ (C.gates[j']'hj'lt).inputs → val C x i = val C y i := by
            intro i hilt himem
            by_cases hic : i ∈ chainL C u
            · exfalso
              by_cases hie : i = endW C u
              · have hj'mem : j' ∈ readers C (endW C u) := by
                  simp only [readers, Finset.mem_filter, Finset.mem_range, hg']
                  exact ⟨hj'lt, hie ▸ himem⟩
                rw [hread, Finset.mem_singleton] at hj'mem
                exact hkj_eq (by omega)
              · obtain ⟨j2, _, hr2, hj2mem⟩ := hp.2.2.2.2.2 i hic hie
                have hj'mem : j' ∈ readers C i := by
                  simp only [readers, Finset.mem_filter, Finset.mem_range, hg']
                  exact ⟨hj'lt, himem⟩
                rw [hr2, Finset.mem_singleton] at hj'mem
                subst hj'mem
                exact hk (hkj' ▸ hj2mem)
            · exact ih i (by omega) hic
          rw [hkj', val_gate C x j' _ hg', val_gate C y j' _ hg', hin]
          simp only [List.map_cons, List.map_nil, hp_lt, hq_lt, ↓reduceIte]
          rw [hin_eq p hp_lt (by rw [hin]; simp), hin_eq q hq_lt (by rw [hin]; simp)]

lemma indep_lt_gStar {n : ℕ} {C : Circuit} (hC : CleanMin n C) (u : Fin n)
    (j : ℕ) (hread : readers C (endW C u) = {j})
    (x y : Fin n → Bool) (hxy : ∀ z ≠ u, x z = y z) :
    ∀ k, k < n + j → k ∉ chainL C u → val C x k = val C y k := by
  have hp := chain_props hC u
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hklt hk
    by_cases h1 : k < n
    · rw [val_lt_n C x k h1, val_lt_n C y k h1]
      apply hxy
      intro heq
      apply hk
      have hku : k = u.val := congrArg Fin.val heq
      rw [hku]
      exact hp.2.2.1
    · have hj'lt : k - n < C.gates.length := by
        have : j < C.gates.length := by
          have : j ∈ readers C (endW C u) := by rw [hread]; simp
          simp only [readers, Finset.mem_filter, Finset.mem_range] at this
          exact this.1
        omega
      set j' := k - n
      have hkj' : k = n + j' := by omega
      have hg' : C.gates[j']? = some (C.gates[j']'hj'lt) := List.getElem?_eq_getElem hj'lt
      obtain ⟨_, p, q, hin, hp_lt, hq_lt, _⟩ := hC.2.2.2.1 j' _ hg'
      have hin_eq : ∀ i, i < n + j' → i ∈ (C.gates[j']'hj'lt).inputs → val C x i = val C y i := by
        intro i hilt himem
        by_cases hic : i ∈ chainL C u
        · exfalso
          by_cases hie : i = endW C u
          · have hj'mem : j' ∈ readers C (endW C u) := by
              simp only [readers, Finset.mem_filter, Finset.mem_range, hg']
              exact ⟨hj'lt, hie ▸ himem⟩
            rw [hread, Finset.mem_singleton] at hj'mem
            omega
          · obtain ⟨j2, _, hr2, hj2mem⟩ := hp.2.2.2.2.2 i hic hie
            have hj'mem : j' ∈ readers C i := by
              simp only [readers, Finset.mem_filter, Finset.mem_range, hg']
              exact ⟨hj'lt, himem⟩
            rw [hr2, Finset.mem_singleton] at hj'mem
            subst hj'mem
            exact hk (hkj' ▸ hj2mem)
        · exact ih i (by omega) (by omega) hic
      rw [hkj', val_gate C x j' _ hg', val_gate C y j' _ hg', hin]
      simp only [List.map_cons, List.map_nil, hp_lt, hq_lt, ↓reduceIte]
      rw [hin_eq p hp_lt (by rw [hin]; simp), hin_eq q hq_lt (by rw [hin]; simp)]

lemma hWire_not_in_chain {n : ℕ} {C : Circuit} (hC : CleanMin n C) (u : Fin n)
    (j : ℕ) (g : Gate) (h : ℕ) (hg : C.gates[j]? = some g) (hand : g.op = GateOp.and)
    (hin : g.inputs = [endW C u, h] ∨ g.inputs = [h, endW C u]) (hne : h ≠ endW C u) :
    h ∉ chainL C u := by
  intro hc
  obtain ⟨j2, _, hr2, _⟩ := (chain_props hC u).2.2.2.2.2 h hc hne
  have hjlt : j < C.gates.length := (List.getElem?_eq_some_iff.mp hg).1
  have hjmem : j ∈ readers C h := by
    simp only [readers, Finset.mem_filter, Finset.mem_range, hg]
    exact ⟨hjlt, by rcases hin with hin | hin <;> rw [hin] <;> simp⟩
  rw [hr2, Finset.mem_singleton] at hjmem
  subst hjmem
  have hrec : ∀ (fuel w : ℕ), w < n + C.gates.length → n + C.gates.length - w ≤ fuel →
      ∀ c ∈ followChain n C fuel w, c ≠ (followChain n C fuel w).getLast (followChain_ne_nil n C fuel w) →
        ∃ j0, readers C c = {j0} ∧ ∃ g0, C.gates[j0]? = some g0 ∧ g0.op = GateOp.or := by
    intro fuel
    induction fuel with
    | zero => intro w hw hfuel; omega
    | succ f ih =>
      intro w hw hfuel c hc' hne'
      cases hst0 : stepChain n C w with
      | none =>
        have hL : followChain n C (f + 1) w = [w] := by simp [followChain, hst0]
        have hlast : (followChain n C (f + 1) w).getLast (followChain_ne_nil n C (f + 1) w) = w := by
          simp [followChain, hst0]
        rw [hL, List.mem_singleton] at hc'
        rw [hlast] at hne'
        exact absurd hc' hne'
      | some w' =>
        obtain ⟨j0, _, g0, hg0, hor0, hr0, _, _, _⟩ := stepChain_some_props hC hst0
        have hL : followChain n C (f + 1) w = w :: followChain n C f w' := by simp [followChain, hst0]
        rw [hL] at hc'
        rw [followChain_cons_getLast n C f w w' hst0] at hne'
        rcases List.mem_cons.mp hc' with rfl | hc''
        · exact ⟨j0, hr0, g0, hg0, hor0⟩
        · exact ih w' (by omega) (by omega) c hc'' hne'
  obtain ⟨j0, hr0, g0, hg0, hor0⟩ := hrec (n + C.gates.length) u.val (by omega) (by omega) h hc hne
  rw [hr2] at hr0
  have := Finset.singleton_injective hr0
  subst this
  rw [hg] at hg0
  injection hg0 with hg''
  subst hg''
  rw [hand] at hor0
  cases hor0

lemma and_gate_eval {n : ℕ} {C : Circuit} (j : ℕ) (g : Gate) (a b : ℕ)
    (hg : C.gates[j]? = some g) (hand : g.op = GateOp.and)
    (hin : g.inputs = [a, b] ∨ g.inputs = [b, a]) (ha : a < n + j) (hb : b < n + j)
    (x : Fin n → Bool) :
    val C x (n + j) = (val C x a && val C x b) := by
  rw [val_gate C x j g hg, hand]
  rcases hin with hin | hin
  · rw [hin]; simp [GateOp.eval, ha, hb]
  · rw [hin]; simp [GateOp.eval, ha, hb, Bool.and_comm]

lemma hWire_neighbor {n : ℕ} (G : SimpleGraph (Fin n))
    {C : Circuit} (hC : CleanMin n C)
    (heval : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)
    (u b : Fin n) (hub : G.Adj u b)
    (j : ℕ) (g : Gate) (h : ℕ) (hg : C.gates[j]? = some g) (hand : g.op = GateOp.and)
    (hread : readers C (endW C u) = {j})
    (hin : g.inputs = [endW C u, h] ∨ g.inputs = [h, endW C u]) (hh : h < n + j) (hne : h ≠ endW C u) :
    val C (eof b) h = true := by
  have hjlt : j < C.gates.length := (List.getElem?_eq_some_iff.mp hg).1
  have hend_lt : endW C u < n + j := by
    obtain ⟨_, p, q, hin', hp, hq, _⟩ := hC.2.2.2.1 j _ hg
    rcases hin with hin | hin <;> rw [hin] at hin' <;> simp at hin' <;> omega
  have hout_not_mem : C.output ∉ chainL C u := by
    intro hmem
    have h1 := (chain_props hC u).2.2.2.2.1 C.output hmem (eof u) (by simp [eof])
    obtain ⟨a, c, hac, ha, hc⟩ := (heval (eof u)).mp h1
    simp only [eof, decide_eq_true_eq] at ha hc
    subst ha; subst hc
    exact G.irrefl hac
  have h0 : C.eval (List.ofFn (eof b)) = false := by
    cases hval : C.eval (List.ofFn (eof b))
    · rfl
    · exfalso
      obtain ⟨a, c, hac, ha, hc⟩ := (heval _).mp hval
      simp only [eof, decide_eq_true_eq] at ha hc
      subst ha; subst hc
      exact G.irrefl hac
  have h1 : C.eval (List.ofFn (pair u b)) = true :=
    (heval _).mpr ⟨u, b, hub, by simp [pair], by simp [pair]⟩
  have hne_g : val C (eof b) (n + j) ≠ val C (pair u b) (n + j) := by
    intro heq_g
    have heq_out := and_no_leakage hC u j hread (eof b) (pair u b)
      (fun z hz => by simp [eof, pair, hz]) heq_g C.output hout_not_mem
    change C.eval (List.ofFn (eof b)) = C.eval (List.ofFn (pair u b)) at heq_out
    rw [h0, h1] at heq_out
    exact absurd heq_out (by decide)
  have htrue_g : val C (pair u b) (n + j) = true := by
    cases hv : val C (pair u b) (n + j)
    · exfalso
      have h0g : val C (eof b) (n + j) = false := by
        cases h0v : val C (eof b) (n + j)
        · rfl
        · have := val_mono C hC.1 (eof b) (pair u b)
            (fun z hz => by simp only [eof, decide_eq_true_eq] at hz; simp [pair, hz]) (n + j) h0v
          rw [hv] at this
          exact absurd this (by decide)
      exact hne_g (h0g.trans hv.symm)
    · rfl
  rw [and_gate_eval j g (endW C u) h hg hand hin hend_lt hh] at htrue_g
  have hh_pair : val C (pair u b) h = true := (Bool.and_eq_true _ _).mp htrue_g |>.2
  have hh_not : h ∉ chainL C u := hWire_not_in_chain hC u j g h hg hand hin hne
  have heq_h := indep_lt_gStar hC u j hread (eof b) (pair u b)
    (fun z hz => by simp [eof, pair, hz]) h hh hh_not
  rw [heq_h]
  exact hh_pair

lemma hWire_not_in_other_chain {n : ℕ} {C : Circuit} (hC : CleanMin n C) (u v : Fin n)
    (ju jv : ℕ) (gu : Gate) (hu : ℕ) (hgu : C.gates[ju]? = some gu) (handu : gu.op = GateOp.and)
    (hreadv : readers C (endW C v) = {jv})
    (hinu : gu.inputs = [endW C u, hu] ∨ gu.inputs = [hu, endW C u])
    (hjlt : ju < jv) :
    hu ∉ chainL C v := by
  intro hc
  have hjult : ju < C.gates.length := (List.getElem?_eq_some_iff.mp hgu).1
  have hjmem : ju ∈ readers C hu := by
    simp only [readers, Finset.mem_filter, Finset.mem_range, hgu]
    exact ⟨hjult, by rcases hinu with h | h <;> rw [h] <;> simp⟩
  by_cases he : hu = endW C v
  · rw [he, hreadv, Finset.mem_singleton] at hjmem
    omega
  · obtain ⟨j2, _, hr2, _⟩ := (chain_props hC v).2.2.2.2.2 hu hc he
    rw [hr2, Finset.mem_singleton] at hjmem
    subst hjmem
    have hrec : ∀ (fuel w : ℕ), w < n + C.gates.length → n + C.gates.length - w ≤ fuel →
        ∀ c ∈ followChain n C fuel w, c ≠ (followChain n C fuel w).getLast (followChain_ne_nil n C fuel w) →
          ∃ j0, readers C c = {j0} ∧ ∃ g0, C.gates[j0]? = some g0 ∧ g0.op = GateOp.or := by
      intro fuel
      induction fuel with
      | zero => intro w hw hfuel; omega
      | succ f ih =>
        intro w hw hfuel c hc' hne'
        cases hst0 : stepChain n C w with
        | none =>
          have hL : followChain n C (f + 1) w = [w] := by simp [followChain, hst0]
          have hlast : (followChain n C (f + 1) w).getLast (followChain_ne_nil n C (f + 1) w) = w := by
            simp [followChain, hst0]
          rw [hL, List.mem_singleton] at hc'
          rw [hlast] at hne'
          exact absurd hc' hne'
        | some w' =>
          obtain ⟨j0, _, g0, hg0, hor0, hr0, _, _, _⟩ := stepChain_some_props hC hst0
          have hL : followChain n C (f + 1) w = w :: followChain n C f w' := by simp [followChain, hst0]
          rw [hL] at hc'
          rw [followChain_cons_getLast n C f w w' hst0] at hne'
          rcases List.mem_cons.mp hc' with rfl | hc''
          · exact ⟨j0, hr0, g0, hg0, hor0⟩
          · exact ih w' (by omega) (by omega) c hc'' hne'
    obtain ⟨j0, hr0, g0, hg0, hor0⟩ := hrec (n + C.gates.length) v.val (by omega) (by omega) hu hc he
    rw [hr2] at hr0
    have := Finset.singleton_injective hr0
    subst this
    rw [hgu] at hg0
    injection hg0 with hg''
    subst hg''
    rw [handu] at hor0
    cases hor0

lemma type2_indep {n : ℕ} (G : SimpleGraph (Fin n))
    (hdeg : ∀ v : Fin n, (G.neighborSet v).ncard = 3)
    (hc4 : ∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a)
    {C : Circuit} (hC : CleanMin n C)
    (heval : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)
    (u v : Fin n) (hu : ¬ 2 ≤ (readers C (endW C u)).card) (hv : ¬ 2 ≤ (readers C (endW C v)).card) :
    ¬ G.Adj u v := by
  intro huv
  obtain ⟨ju, hjult, gu, huw, hgu, handu, hreadu, hinu, hhult, hhune⟩ := type2_and_gate G hC heval u hu
  obtain ⟨jv, hjvlt, gv, hvw, hgv, handv, hreadv, hinv, hhvlt, hhvne⟩ := type2_and_gate G hC heval v hv
  have hsing := chain_singleton_iff G hdeg hc4 hC heval
  have hne_uv : u ≠ v := G.ne_of_adj huv
  rcases lt_trichotomy ju jv with hlt | heq | hgt
  · have hh_v : val C (eof v) huw = true :=
      hWire_neighbor G hC heval u v huv ju gu huw hgu handu hreadu hinu hhult hhune
    have hh_not_v : huw ∉ chainL C v :=
      hWire_not_in_other_chain hC u v ju jv gu huw hgu handu hreadv hinu hlt
    have hh_zero : val C (fun _ : Fin n => false) huw = true := by
      rw [indep_lt_gStar hC v jv hreadv (fun _ : Fin n => false) (eof v)
        (fun z hz => by simp [eof, hz]) huw (by omega) hh_not_v]
      exact hh_v
    have hh_all : ∀ x : Fin n → Bool, val C x huw = true := fun x =>
      val_mono C hC.1 (fun _ : Fin n => false) x (fun _ h => absurd h (by decide)) huw hh_zero
    have hend_lt : endW C u < n + ju := by
      obtain ⟨_, p, q, hin', hp, hq, _⟩ := hC.2.2.2.1 ju _ hgu
      rcases hinu with h | h <;> rw [h] at hin' <;> simp at hin' <;> omega
    obtain ⟨x, hx⟩ := (hC.2.2.2.2.1 ju hjult).2.2 (endW C u) hend_lt
    rw [and_gate_eval ju gu (endW C u) huw hgu handu hinu hend_lt hhult, hh_all x, Bool.and_true] at hx
    exact hx rfl
  · subst heq
    have hgu_eq : gu = gv := by rw [hgu] at hgv; exact Option.some.inj hgv
    subst hgu_eq
    have hfin : (G.neighborSet u).Finite := Set.toFinite _
    have hcard_f : hfin.toFinset.card = 3 := by
      rw [← Set.ncard_eq_toFinset_card (G.neighborSet u) hfin]; exact hdeg u
    have hlt2 : 1 < hfin.toFinset.card := by omega
    obtain ⟨y1, hy1, y2, hy2, hy12⟩ := Finset.one_lt_card.mp hlt2
    have ⟨y, huy, hyv⟩ : ∃ y : Fin n, G.Adj u y ∧ y ≠ v := by
      by_cases h1 : y1 = v
      · exact ⟨y2, (hfin.mem_toFinset).mp hy2, fun h2 => hy12 (h1.trans h2.symm)⟩
      · exact ⟨y1, (hfin.mem_toFinset).mp hy1, h1⟩
    have hh_y : val C (eof y) huw = true :=
      hWire_neighbor G hC heval u y huy ju gu huw hgu handu hreadu hinu hhult hhune
    have hweq : huw = endW C v := by
      have hend_ne : endW C u ≠ endW C v := by
        intro he
        have := (hsing u (endW C u) (chain_props hC u).2.1 v).mp (by rw [he]; exact (hsing v (endW C v) (chain_props hC v).2.1 v).mpr rfl)
        exact hne_uv this.symm
      rcases hinu with h1 | h1 <;> rcases hinv with h2 | h2 <;> rw [h1] at h2 <;> simp at h2
      · exact absurd h2.1 hend_ne
      · exact h2.2
      · exact h2.1
      · exact absurd h2.2 hend_ne
    rw [hweq] at hh_y
    exact hyv ((hsing v (endW C v) (chain_props hC v).2.1 y).mp hh_y)
  · have hh_u : val C (eof u) hvw = true :=
      hWire_neighbor G hC heval v u huv.symm jv gv hvw hgv handv hreadv hinv hhvlt hhvne
    have hh_not_u : hvw ∉ chainL C u :=
      hWire_not_in_other_chain hC v u jv ju gv hvw hgv handv hreadu hinv hgt
    have hh_zero : val C (fun _ : Fin n => false) hvw = true := by
      rw [indep_lt_gStar hC u ju hreadu (fun _ : Fin n => false) (eof u)
        (fun z hz => by simp [eof, hz]) hvw (by omega) hh_not_u]
      exact hh_u
    have hh_all : ∀ x : Fin n → Bool, val C x hvw = true := fun x =>
      val_mono C hC.1 (fun _ : Fin n => false) x (fun _ h => absurd h (by decide)) hvw hh_zero
    have hend_lt : endW C v < n + jv := by
      obtain ⟨_, p, q, hin', hp, hq, _⟩ := hC.2.2.2.1 jv _ hgv
      rcases hinv with h | h <;> rw [h] at hin' <;> simp at hin' <;> omega
    obtain ⟨x, hx⟩ := (hC.2.2.2.2.1 jv hjvlt).2.2 (endW C v) hend_lt
    rw [and_gate_eval jv gv (endW C v) hvw hgv handv hinv hend_lt hhvlt, hh_all x, Bool.and_true] at hx
    exact hx rfl

noncomputable def targetAux (n : ℕ) (C : Circuit) (stopSet : Finset ℕ) : ℕ → ℕ → ℕ
  | 0, k => k
  | fuel + 1, k =>
    open Classical in
    if k ∈ stopSet ∨ n + C.gates.length - 1 ≤ k then k
    else if h : (readers C k).card = 1 then
      let j := (Finset.card_eq_one.mp h).choose
      targetAux n C stopSet fuel (n + j)
    else k

lemma targetAux_stop (n : ℕ) (C : Circuit) (stopSet : Finset ℕ) (fuel k : ℕ)
    (hk : k ∈ stopSet ∨ n + C.gates.length - 1 ≤ k) :
    targetAux n C stopSet fuel k = k := by
  classical
  cases fuel with
  | zero => rfl
  | succ f => simp only [targetAux, hk, ↓reduceIte]

lemma targetAux_indep_fuel {n : ℕ} {C : Circuit} (hC : CleanMin n C) (stopSet : Finset ℕ) :
    ∀ (m k f1 f2 : ℕ), n + C.gates.length - k ≤ m → m ≤ f1 → m ≤ f2 →
      targetAux n C stopSet f1 k = targetAux n C stopSet f2 k := by
  intro m
  induction m with
  | zero =>
    intro k f1 f2 hm _ _
    have hk : n + C.gates.length - 1 ≤ k := by omega
    rw [targetAux_stop n C stopSet f1 k (Or.inr hk), targetAux_stop n C stopSet f2 k (Or.inr hk)]
  | succ m ih =>
    intro k f1 f2 hm hf1 hf2
    obtain ⟨f1', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f1 ≠ 0)
    obtain ⟨f2', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f2 ≠ 0)
    classical
    simp only [targetAux]
    split_ifs with hs h1
    · rfl
    · set j := (Finset.card_eq_one.mp h1).choose
      have hj_eq : readers C k = {j} := (Finset.card_eq_one.mp h1).choose_spec
      have hj_mem : j ∈ readers C k := by rw [hj_eq]; simp
      simp only [readers, Finset.mem_filter, Finset.mem_range] at hj_mem
      obtain ⟨hjlt, hmem⟩ := hj_mem
      have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
      rw [hg] at hmem
      dsimp only at hmem
      obtain ⟨_, p, q, hin, hp, hq, _⟩ := hC.2.2.2.1 j _ hg
      have hklt : k < n + j := by
        rw [hin] at hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl <;> omega
      exact ih (n + j) f1' f2' (by omega) (by omega) (by omega)
    · rfl

lemma targetAux_step {n : ℕ} {C : Circuit} (hC : CleanMin n C) (stopSet : Finset ℕ)
    (k j : ℕ) (hnot : k ∉ stopSet) (hklt : k < n + C.gates.length - 1)
    (hread : readers C k = {j}) :
    targetAux n C stopSet (n + C.gates.length) k =
      targetAux n C stopSet (n + C.gates.length) (n + j) := by
  classical
  have hpos : 0 < n + C.gates.length := by have := hC.2.1; omega
  obtain ⟨f, hf⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n + C.gates.length ≠ 0)
  have hcard : (readers C k).card = 1 := by rw [hread]; simp
  have hch : (Finset.card_eq_one.mp hcard).choose = j := by
    have hspec : readers C k = {(Finset.card_eq_one.mp hcard).choose} :=
      (Finset.card_eq_one.mp hcard).choose_spec
    exact (Finset.singleton_injective (hread.symm.trans hspec)).symm
  have hhjlt : j < C.gates.length := by
    have : j ∈ readers C k := by rw [hread]; simp
    simp only [readers, Finset.mem_filter, Finset.mem_range] at this
    exact this.1
  have hg : C.gates[j]? = some (C.gates[j]'hhjlt) := List.getElem?_eq_getElem hhjlt
  have hmem : k ∈ (C.gates[j]'hhjlt).inputs := by
    have : j ∈ readers C k := by rw [hread]; simp
    simp only [readers, Finset.mem_filter, Finset.mem_range, hg] at this
    exact this.2
  obtain ⟨_, p, q, hin, hp, hq, _⟩ := hC.2.2.2.1 j _ hg
  have hk_lt_nj : k < n + j := by
    rw [hin] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl <;> omega
  have hstep : targetAux n C stopSet (f + 1) k = targetAux n C stopSet f (n + j) := by
    simp only [targetAux, hnot, show ¬ n + C.gates.length - 1 ≤ k by omega, or_self, ↓reduceIte,
      hcard, ↓reduceDIte, hch]
  rw [hf, hstep]
  exact targetAux_indep_fuel hC stopSet (n + C.gates.length - (n + j)) (n + j) f (f + 1)
    (le_refl _) (by omega) (by omega)

lemma main_proof (n t : ℕ) (G : SimpleGraph (Fin n)) (C0 : Circuit)
    (hdeg : ∀ v : Fin n, (G.neighborSet v).ncard = 3)
    (hc4 : ∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a)
    (hvc_ex : ∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t)
    (hvc_min : ∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card)
    (hmono0 : PEqualNP.MetaComplexity.Monotone2 C0)
    (heval0 : ∀ x : Fin n → Bool, C0.eval (List.ofFn x) = true ↔
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) :
    n + t ≤ C0.size := by
  classical
  by_cases hn : n = 0
  · subst hn
    have ht0 : t ≤ 0 := by
      have := hvc_min ∅ (fun u _ _ => Fin.elim0 u)
      simpa using this
    omega
  have hn_pos : 0 < n := by omega
  obtain ⟨C, hC, hsz_le, heval⟩ := exists_clean_min hn_pos G hdeg C0 hmono0 heval0
  suffices hmain : n + t ≤ C.gates.length by
    change C.gates.length ≤ C0.gates.length at hsz_le
    change n + t ≤ C0.gates.length
    omega
  let B : Finset (Fin n) := Finset.univ.filter (fun v => 2 ≤ (readers C (endW C v)).card)
  let A : Finset (Fin n) := Finset.univ.filter (fun v => ¬ 2 ≤ (readers C (endW C v)).card)
  have hsing := chain_singleton_iff G hdeg hc4 hC heval
  have hend_inj : Function.Injective (endW (n := n) C) := by
    intro u v heq
    have h1 := (hsing u (endW C u) (chain_props hC u).2.1 u).mpr rfl
    rw [heq] at h1
    exact ((hsing v (endW C v) (chain_props hC v).2.1 u).mp h1)
  have hB_vc : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G B := by
    intro u v huv
    by_contra hnot
    push Not at hnot
    have huA : ¬ 2 ≤ (readers C (endW C u)).card := by
      intro h; exact hnot.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ u, h⟩)
    have hvA : ¬ 2 ≤ (readers C (endW C v)).card := by
      intro h; exact hnot.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ v, h⟩)
    exact type2_indep G hdeg hc4 hC heval u v huA hvA huv
  have ht_le_B : t ≤ B.card := hvc_min B hB_vc
  have hB_img_sub : B.image (endW C) ⊆ Finset.range (n + C.gates.length - 1) := by
    intro w hw
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hw
    exact Finset.mem_range.mpr (endW_lt_out G hC heval b)
  have hexcess := double_count_excess hn_pos hC
  have hsum_ge_B : B.card ≤ ∑ w ∈ Finset.range (n + C.gates.length - 1), ((readers C w).card - 1) := by
    calc B.card
        = (B.image (endW C)).card := (Finset.card_image_of_injective B hend_inj).symm
      _ = ∑ w ∈ B.image (endW C), 1 := by simp
      _ ≤ ∑ w ∈ B.image (endW C), ((readers C w).card - 1) := by
          apply Finset.sum_le_sum
          intro w hw
          obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hw
          have := (Finset.mem_filter.mp hb).2
          omega
      _ ≤ ∑ w ∈ Finset.range (n + C.gates.length - 1), ((readers C w).card - 1) :=
          Finset.sum_le_sum_of_subset hB_img_sub
  by_contra hlt_nt
  have hlen_eq : C.gates.length = n + t - 1 := by omega
  have hB_eq_t : B.card = t := by omega
  have hsum_eq_B : ∑ w ∈ Finset.range (n + C.gates.length - 1), ((readers C w).card - 1) = B.card := by
    omega
  have hB_read2 : ∀ b ∈ B, (readers C (endW C b)).card = 2 := by
    intro b hb
    have hge2 : 2 ≤ (readers C (endW C b)).card := (Finset.mem_filter.mp hb).2
    by_contra hne2
    have hge3 : 2 ≤ (readers C (endW C b)).card - 1 := by omega
    have hlt_s : ∑ w ∈ B.image (endW C), 1 < ∑ w ∈ B.image (endW C), ((readers C w).card - 1) := by
      apply Finset.sum_lt_sum
      · intro w hw
        obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hw
        have := (Finset.mem_filter.mp hb').2
        omega
      · exact ⟨endW C b, Finset.mem_image_of_mem _ hb, by omega⟩
    have hle_all := Finset.sum_le_sum_of_subset (f := fun w => (readers C w).card - 1) hB_img_sub
    have hcard_img : (B.image (endW C)).card = B.card := Finset.card_image_of_injective B hend_inj
    simp only [Finset.sum_const, smul_eq_mul, mul_one, hcard_img] at hlt_s
    omega
  have hother_read1 : ∀ w < n + C.gates.length - 1, w ∉ B.image (endW C) →
      (readers C w).card = 1 := by
    intro w hw hnotB
    have hge1 := hC.2.2.2.2.2 w hw
    by_contra hne1
    have hpos_w : 1 ≤ (readers C w).card - 1 := by omega
    have hsub_ins : insert w (B.image (endW C)) ⊆ Finset.range (n + C.gates.length - 1) := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxB
      · exact Finset.mem_range.mpr hw
      · exact hB_img_sub hxB
    have hsum_ins := Finset.sum_le_sum_of_subset (f := fun x => (readers C x).card - 1) hsub_ins
    rw [Finset.sum_insert hnotB] at hsum_ins
    have hsum_B : B.card ≤ ∑ x ∈ B.image (endW C), ((readers C x).card - 1) := by
      calc B.card = (B.image (endW C)).card := (Finset.card_image_of_injective B hend_inj).symm
        _ = ∑ _ ∈ B.image (endW C), 1 := by simp
        _ ≤ ∑ x ∈ B.image (endW C), ((readers C x).card - 1) := by
            apply Finset.sum_le_sum
            intro x hx
            obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hx
            have := (Finset.mem_filter.mp hb').2
            omega
    omega
  have hA_spec : ∀ u : Fin n, u ∈ A →
      ∃ j < C.gates.length, ∃ g : Gate, ∃ h : ℕ,
        C.gates[j]? = some g ∧ g.op = GateOp.and ∧
        readers C (endW C u) = {j} ∧
        (g.inputs = [endW C u, h] ∨ g.inputs = [h, endW C u]) ∧
        h < n + j ∧ h ≠ endW C u := fun u hu =>
    type2_and_gate G hC heval u (Finset.mem_filter.mp hu).2
  let gStar : Fin n → ℕ := fun u =>
    if h : u ∈ A then (hA_spec u h).choose else 0
  let hWire : Fin n → ℕ := fun u =>
    if h : u ∈ A then (hA_spec u h).choose_spec.2.choose_spec.choose else 0
  have hgStar_props : ∀ u ∈ A,
      gStar u < C.gates.length ∧
      ∃ g : Gate, C.gates[gStar u]? = some g ∧ g.op = GateOp.and ∧
        readers C (endW C u) = {gStar u} ∧
        (g.inputs = [endW C u, hWire u] ∨ g.inputs = [hWire u, endW C u]) ∧
        hWire u < n + gStar u ∧ hWire u ≠ endW C u := by
    intro u hu
    simp only [gStar, hWire, hu, ↓reduceDIte]
    exact ⟨(hA_spec u hu).choose_spec.1, (hA_spec u hu).choose_spec.2.choose,
      (hA_spec u hu).choose_spec.2.choose_spec.choose_spec⟩
  have hgStar_sing_false : ∀ u ∈ A, ∀ z : Fin n, val C (eof z) (n + gStar u) = false := by
    intro u hu z
    obtain ⟨hjlt, g, hg, hand, hread, hin, hhlt, hhne⟩ := hgStar_props u hu
    have hend_lt : endW C u < n + gStar u := by
      obtain ⟨_, p, q, hin', hp, hq, _⟩ := hC.2.2.2.1 (gStar u) _ hg
      rcases hin with h | h <;> rw [h] at hin' <;> simp at hin' <;> omega
    rw [and_gate_eval (gStar u) g (endW C u) (hWire u) hg hand hin hend_lt hhlt]
    by_cases hzu : z = u
    · subst hzu
      have hh_not : hWire z ∉ chainL C z := hWire_not_in_chain hC z (gStar z) g (hWire z) hg hand hin hhne
      have heq0 := indep_lt_gStar hC z (gStar z) hread (eof z) (fun _ : Fin n => false)
        (fun w hw => by simp [eof, hw]) (hWire z) hhlt hh_not
      have hzero : val C (fun _ : Fin n => false) (hWire z) = false := by
        cases hv0 : val C (fun _ : Fin n => false) (hWire z)
        · rfl
        · exfalso
          have hall : ∀ x : Fin n → Bool, val C x (hWire z) = true := fun x =>
            val_mono C hC.1 (fun _ : Fin n => false) x (fun _ h => absurd h (by decide)) _ hv0
          obtain ⟨x, hx⟩ := (hC.2.2.2.2.1 (gStar z) hjlt).2.2 (endW C z) hend_lt
          rw [and_gate_eval (gStar z) g (endW C z) (hWire z) hg hand hin hend_lt hhlt, hall x,
            Bool.and_true] at hx
          exact hx rfl
      rw [heq0, hzero, Bool.and_false]
    · have hfalse : val C (eof z) (endW C u) = false := by
        cases hv : val C (eof z) (endW C u)
        · rfl
        · exfalso; exact hzu ((hsing u (endW C u) (chain_props hC u).2.1 z).mp hv)
      rw [hfalse, Bool.false_and]
  have hWire_nb : ∀ u ∈ A, ∀ b : Fin n, G.Adj u b → val C (eof b) (hWire u) = true := by
    intro u hu b hub
    obtain ⟨_, g, hg, hand, hread, hin, hhlt, hhne⟩ := hgStar_props u hu
    exact hWire_neighbor G hC heval u b hub (gStar u) g (hWire u) hg hand hread hin hhlt hhne
  have hgStar_inj : ∀ u ∈ A, ∀ v ∈ A, gStar u = gStar v → u = v := by
    intro u hu v hv heq
    by_contra huv
    obtain ⟨_, gu, hgu, handu, hreadu, hinu, hhult, _⟩ := hgStar_props u hu
    obtain ⟨_, gv, hgv, handv, hreadv, hinv, hhvlt, _⟩ := hgStar_props v hv
    rw [heq] at hgu
    have hg_eq : gu = gv := by rw [hgu] at hgv; exact Option.some.inj hgv
    subst hg_eq
    have hweq : hWire u = endW C v := by
      have hend_ne : endW C u ≠ endW C v := fun h => huv (hend_inj h)
      rcases hinu with h1 | h1 <;> rcases hinv with h2 | h2 <;> rw [h1] at h2 <;> simp at h2
      · exact absurd h2.1 hend_ne
      · exact h2.2
      · exact h2.1
      · exact absurd h2.2 hend_ne
    have hfin : (G.neighborSet u).Finite := Set.toFinite _
    have hcard_f : hfin.toFinset.card = 3 := by
      rw [← Set.ncard_eq_toFinset_card (G.neighborSet u) hfin]; exact hdeg u
    obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega : 0 < hfin.toFinset.card)
    have hub : G.Adj u b := (hfin.mem_toFinset).mp hb
    have hbv : b ≠ v := by
      intro hbv
      subst hbv
      exact type2_indep G hdeg hc4 hC heval u b (Finset.mem_filter.mp hu).2 (Finset.mem_filter.mp hv).2 hub
    have htrue := hWire_nb u hu b hub
    rw [hweq] at htrue
    exact hbv ((hsing v (endW C v) (chain_props hC v).2.1 b).mp htrue)
  let gStarSet : Finset ℕ := A.image (fun u => n + gStar u)
  let stopSet : Finset ℕ := ((Finset.univ : Finset (Fin n)).image (endW (n := n) C)) ∪ gStarSet
  let tgt : ℕ → ℕ := targetAux n C stopSet (n + C.gates.length)
  have hWire_not_stop : ∀ u ∈ A, hWire u ∉ stopSet := by
    intro u hu hmem
    simp only [stopSet, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
      gStarSet] at hmem
    have hfin : (G.neighborSet u).Finite := Set.toFinite _
    have hcard_f : hfin.toFinset.card = 3 := by
      rw [← Set.ncard_eq_toFinset_card (G.neighborSet u) hfin]; exact hdeg u
    obtain ⟨b1, hb1, b2, hb2, hb12⟩ := Finset.one_lt_card.mp (by omega : 1 < hfin.toFinset.card)
    have hub1 : G.Adj u b1 := (hfin.mem_toFinset).mp hb1
    have hub2 : G.Adj u b2 := (hfin.mem_toFinset).mp hb2
    rcases hmem with ⟨v, hv⟩ | ⟨u', hu', hu'eq⟩
    · have h1 := hWire_nb u hu b1 hub1
      have h2 := hWire_nb u hu b2 hub2
      rw [← hv] at h1 h2
      have eq1 := (hsing v (endW C v) (chain_props hC v).2.1 b1).mp h1
      have eq2 := (hsing v (endW C v) (chain_props hC v).2.1 b2).mp h2
      exact hb12 (eq1.trans eq2.symm)
    · have h1 := hWire_nb u hu b1 hub1
      rw [← hu'eq] at h1
      rw [hgStar_sing_false u' hu' b1] at h1
      exact absurd h1 (by decide)
  have htarget_chain : ∀ v : Fin n, ∀ c ∈ chainL C v, tgt c = endW C v := by
    intro v c hc
    have hrec2 : ∀ (m : ℕ), ∀ c ∈ chainL C v, n + C.gates.length - c ≤ m → tgt c = endW C v := by
      intro m
      induction m with
      | zero =>
        intro c hc' hm
        have := (chain_props hC v).2.2.2.1 c hc'
        omega
      | succ m ih =>
        intro c hc' hm
        by_cases hce : c = endW C v
        · subst hce
          apply targetAux_stop
          left
          exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ v))
        · obtain ⟨j, hjlt, hread, hjmem⟩ := (chain_props hC v).2.2.2.2.2 c hc' hce
          have hc_lt_out : c < n + C.gates.length - 1 := by
            have := endW_lt_out G hC heval v
            have hrec_le : c < n + j := by
              have : j ∈ readers C c := by rw [hread]; simp
              simp only [readers, Finset.mem_filter, Finset.mem_range] at this
              have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
              rw [hg] at this
              dsimp only at this
              obtain ⟨_, p, q, hin, hp, hq, _⟩ := hC.2.2.2.1 j _ hg
              rw [hin] at this
              simp only [List.mem_cons, List.not_mem_nil, or_false] at this
              rcases this.2 with rfl | rfl <;> omega
            omega
          have hc_not_stop : c ∉ stopSet := by
            intro hs
            simp only [stopSet, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
              gStarSet] at hs
            rcases hs with ⟨v', hv'⟩ | ⟨u', hu', hu'eq⟩
            · have hv_eq : v = v' := by
                have h1 := (hsing v c hc' v).mpr rfl
                rw [← hv'] at h1
                exact (hsing v' (endW C v') (chain_props hC v').2.1 v).mp h1
              subst hv_eq
              exact hce hv'.symm
            · have h1 := (hsing v c hc' v).mpr rfl
              rw [← hu'eq, hgStar_sing_false u' hu' v] at h1
              exact absurd h1 (by decide)
          have hstep := targetAux_step hC stopSet c j hc_not_stop hc_lt_out hread
          have hc_lt_nj : c < n + j := by
            have : j ∈ readers C c := by rw [hread]; simp
            simp only [readers, Finset.mem_filter, Finset.mem_range] at this
            have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
            rw [hg] at this
            dsimp only at this
            obtain ⟨_, p, q, hin, hp, hq, _⟩ := hC.2.2.2.1 j _ hg
            rw [hin] at this
            simp only [List.mem_cons, List.not_mem_nil, or_false] at this
            rcases this.2 with rfl | rfl <;> omega
          rw [show tgt c = tgt (n + j) from hstep]
          exact ih (n + j) hjmem (by omega)
    exact hrec2 (n + C.gates.length) c hc (by omega)
  have hpath_to_gStar : ∀ u ∈ A, ∀ b : Fin n, G.Adj u b →
      ∃ j ∈ readers C (endW C b), tgt (n + j) = n + gStar u := by
    intro u hu b hub
    have haux : ∀ k, k < n + C.gates.length → k ∉ stopSet → tgt k = n + gStar u →
        val C (eof b) k = true →
        ∃ j ∈ readers C (endW C b), tgt (n + j) = n + gStar u := by
      intro k
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        intro hklt hk_not htgt hval
        by_cases hkn : k < n
        · exfalso
          have hck := htarget_chain ⟨k, hkn⟩ k (chain_props hC ⟨k, hkn⟩).2.2.1
          rw [htgt] at hck
          have h1 := (hsing ⟨k, hkn⟩ (endW C ⟨k, hkn⟩) (chain_props hC ⟨k, hkn⟩).2.1 ⟨k, hkn⟩).mpr rfl
          rw [← hck, hgStar_sing_false u hu ⟨k, hkn⟩] at h1
          exact absurd h1 (by decide)
        · have hjlt : k - n < C.gates.length := by omega
          set j := k - n
          have hkj : k = n + j := by omega
          have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
          obtain ⟨hop, p, q, hin, hp_lt, hq_lt, _⟩ := hC.2.2.2.1 j _ hg
          rw [hkj, val_gate C (eof b) j _ hg, hin] at hval
          have hex_in : ∃ i, (i = p ∨ i = q) ∧ i < n + j ∧ val C (eof b) i = true := by
            rcases hop with hand | hor
            · rw [hand] at hval
              simp only [GateOp.eval, List.map_cons, List.map_nil, hp_lt, hq_lt, ↓reduceIte,
                List.all_cons, List.all_nil, Bool.and_true, id_eq, Bool.and_eq_true] at hval
              exact ⟨p, Or.inl rfl, hp_lt, hval.1⟩
            · rw [hor] at hval
              simp only [GateOp.eval, List.map_cons, List.map_nil, hp_lt, hq_lt, ↓reduceIte,
                List.any_cons, List.any_nil, Bool.or_false, id_eq, Bool.or_eq_true] at hval
              rcases hval with h | h
              · exact ⟨p, Or.inl rfl, hp_lt, h⟩
              · exact ⟨q, Or.inr rfl, hq_lt, h⟩
          obtain ⟨i, hi_pq, hi_lt, hi_val⟩ := hex_in
          have hi_mem_in : i ∈ (C.gates[j]'hjlt).inputs := by
            rw [hin]; rcases hi_pq with rfl | rfl <;> simp
          by_cases histop : i ∈ stopSet
          · simp only [stopSet, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
              gStarSet] at histop
            rcases histop with ⟨v, hv⟩ | ⟨u', hu', hu'eq⟩
            · rw [← hv] at hi_val
              have hbv : b = v := (hsing v (endW C v) (chain_props hC v).2.1 b).mp hi_val
              subst hbv
              refine ⟨j, ?_, hkj ▸ htgt⟩
              simp only [readers, Finset.mem_filter, Finset.mem_range, hg]
              exact ⟨hjlt, hv.symm ▸ hi_mem_in⟩
            · rw [← hu'eq, hgStar_sing_false u' hu' b] at hi_val
              exact absurd hi_val (by decide)
          · have hi_lt_out : i < n + C.gates.length - 1 := by omega
            have hi_notB : i ∉ B.image (endW C) := fun h =>
              histop (Finset.mem_union_left _ (Finset.image_subset_image (Finset.subset_univ B) h))
            have hi_card1 : (readers C i).card = 1 := hother_read1 i hi_lt_out hi_notB
            have hj_mem_r : j ∈ readers C i := by
              simp only [readers, Finset.mem_filter, Finset.mem_range, hg]
              exact ⟨hjlt, hi_mem_in⟩
            have hi_read : readers C i = {j} := by
              obtain ⟨j0, hj0⟩ := Finset.card_eq_one.mp hi_card1
              rw [hj0, Finset.mem_singleton] at hj_mem_r
              subst hj_mem_r
              exact hj0
            have htgt_i : tgt i = tgt (n + j) :=
              targetAux_step hC stopSet i j histop hi_lt_out hi_read
            exact ih i (by omega) (by omega) histop (htgt_i.trans (hkj ▸ htgt)) hi_val
    obtain ⟨hjlt, g, hg, hand, hread, hin, hhlt, hhne⟩ := hgStar_props u hu
    have hh_not := hWire_not_stop u hu
    have hh_lt_out : hWire u < n + C.gates.length - 1 := by omega
    have hh_notB : hWire u ∉ B.image (endW C) := fun h =>
      hh_not (Finset.mem_union_left _ (Finset.image_subset_image (Finset.subset_univ B) h))
    have hh_card1 := hother_read1 (hWire u) hh_lt_out hh_notB
    have hgu_mem : gStar u ∈ readers C (hWire u) := by
      simp only [readers, Finset.mem_filter, Finset.mem_range, hg]
      exact ⟨hjlt, by rcases hin with h | h <;> rw [h] <;> simp⟩
    have hh_read : readers C (hWire u) = {gStar u} := by
      obtain ⟨j0, hj0⟩ := Finset.card_eq_one.mp hh_card1
      rw [hj0, Finset.mem_singleton] at hgu_mem
      subst hgu_mem
      exact hj0
    have htgt_h : tgt (hWire u) = n + gStar u := by
      dsimp only [tgt]
      rw [targetAux_step hC stopSet (hWire u) (gStar u) hh_not hh_lt_out hh_read]
      exact targetAux_stop n C stopSet (n + C.gates.length) (n + gStar u)
        (Or.inl (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hu)))
    exact haux (hWire u) (by omega) hh_not htgt_h (hWire_nb u hu b hub)
  have hB0_no_B_nb : ∀ b ∈ B, (∀ j ∈ readers C (endW C b), tgt (n + j) ∈ gStarSet) →
      ∀ b' ∈ B, ¬ G.Adj b b' := by
    intro b hb hall b' hb' hbb'
    have hstep_ind : ∀ k, k < n + C.gates.length → k ∉ chainL C b →
        (tgt k ∉ gStarSet ∨ k ∈ gStarSet) →
        val C (pair b b') k = val C (eof b') k := by
      intro k
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        intro hklt hk_not_cb hk_cond
        by_cases hkg : k ∈ gStarSet
        · obtain ⟨u, huA, rfl⟩ := Finset.mem_image.mp hkg
          obtain ⟨hjlt, g, hg, hand, _, hin, hhlt, _⟩ := hgStar_props u huA
          have hend_lt : endW C u < n + gStar u := by
            obtain ⟨_, p, q, hin', hp, hq, _⟩ := hC.2.2.2.1 (gStar u) _ hg
            rcases hin with h | h <;> rw [h] at hin' <;> simp at hin' <;> omega
          have hu_not_cb : endW C u ∉ chainL C b := by
            intro hmem
            have hbu : u = b := (hsing b (endW C u) hmem u).mp ((hsing u (endW C u) (chain_props hC u).2.1 u).mpr rfl)
            subst hbu
            exact (Finset.mem_filter.mp huA).2 (Finset.mem_filter.mp hb).2
          have hu_tgt : tgt (endW C u) = endW C u :=
            targetAux_stop n C stopSet (n + C.gates.length) (endW C u)
              (Or.inl (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ u))))
          have hu_not_g : endW C u ∉ gStarSet := by
            intro hm
            obtain ⟨u', hu', heq⟩ := Finset.mem_image.mp hm
            have h1 := (hsing u (endW C u) (chain_props hC u).2.1 u).mpr rfl
            rw [← heq, hgStar_sing_false u' hu' u] at h1
            exact absurd h1 (by decide)
          have hwu_eq := ih (endW C u) hend_lt (by omega) hu_not_cb (Or.inl (by rw [hu_tgt]; exact hu_not_g))
          have hub' : u ≠ b' := by
            intro h; subst h; exact (Finset.mem_filter.mp huA).2 (Finset.mem_filter.mp hb').2
          have hwu_f : val C (eof b') (endW C u) = false := by
            cases hv : val C (eof b') (endW C u)
            · rfl
            · exfalso; exact hub' ((hsing u (endW C u) (chain_props hC u).2.1 b').mp hv).symm
          rw [and_gate_eval (gStar u) g (endW C u) (hWire u) hg hand hin hend_lt hhlt,
            and_gate_eval (gStar u) g (endW C u) (hWire u) hg hand hin hend_lt hhlt,
            hwu_eq, hwu_f, Bool.false_and, Bool.false_and]
        · have hktgt_not : tgt k ∉ gStarSet := hk_cond.resolve_right hkg
          by_cases hkn : k < n
          · rw [val_lt_n C (pair b b') k hkn, val_lt_n C (eof b') k hkn]
            have hkb : (⟨k, hkn⟩ : Fin n) ≠ b := fun h => by
              have hkb' : k = b.val := congrArg Fin.val h
              exact hk_not_cb (by rw [hkb']; exact (chain_props hC b).2.2.1)
            simp [pair, eof, hkb]
          · have hjlt : k - n < C.gates.length := by omega
            set j := k - n
            have hkj : k = n + j := by omega
            have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
            obtain ⟨_, p, q, hin, hp_lt, hq_lt, _⟩ := hC.2.2.2.1 j _ hg
            have hin_eq : ∀ i, i < n + j → i ∈ (C.gates[j]'hjlt).inputs →
                val C (pair b b') i = val C (eof b') i := by
              intro i hilt himem
              have hi_not_cb : i ∉ chainL C b := by
                intro hmem
                by_cases hie : i = endW C b
                · have hj_mem : j ∈ readers C (endW C b) := by
                    simp only [readers, Finset.mem_filter, Finset.mem_range, hg]
                    exact ⟨hjlt, hie ▸ himem⟩
                  exact hktgt_not (hkj ▸ hall j hj_mem)
                · obtain ⟨j2, _, hr2, hj2mem⟩ := (chain_props hC b).2.2.2.2.2 i hmem hie
                  have hj_mem : j ∈ readers C i := by
                    simp only [readers, Finset.mem_filter, Finset.mem_range, hg]
                    exact ⟨hjlt, himem⟩
                  rw [hr2, Finset.mem_singleton] at hj_mem
                  subst hj_mem
                  exact hk_not_cb (hkj ▸ hj2mem)
              have hi_cond : tgt i ∉ gStarSet ∨ i ∈ gStarSet := by
                by_cases histop : i ∈ stopSet
                · dsimp only [tgt]
                  rw [targetAux_stop n C stopSet (n + C.gates.length) i (Or.inl histop)]
                  exact Classical.em (i ∈ gStarSet) |>.symm
                · left
                  have hi_lt_out : i < n + C.gates.length - 1 := by omega
                  have hi_notB : i ∉ B.image (endW C) := fun h =>
                    histop (Finset.mem_union_left _ (Finset.image_subset_image (Finset.subset_univ B) h))
                  have hi_card1 := hother_read1 i hi_lt_out hi_notB
                  have hj_mem : j ∈ readers C i := by
                    simp only [readers, Finset.mem_filter, Finset.mem_range, hg]
                    exact ⟨hjlt, himem⟩
                  have hi_read : readers C i = {j} := by
                    obtain ⟨j0, hj0⟩ := Finset.card_eq_one.mp hi_card1
                    rw [hj0, Finset.mem_singleton] at hj_mem
                    subst hj_mem
                    exact hj0
                  dsimp only [tgt]
                  rw [targetAux_step hC stopSet i j histop hi_lt_out hi_read]
                  exact hkj ▸ hktgt_not
              exact ih i (by omega) (by omega) hi_not_cb hi_cond
            rw [hkj, val_gate C (pair b b') j _ hg, val_gate C (eof b') j _ hg, hin]
            simp only [List.map_cons, List.map_nil, hp_lt, hq_lt, ↓reduceIte]
            rw [hin_eq p hp_lt (by rw [hin]; simp), hin_eq q hq_lt (by rw [hin]; simp)]
    have hout_not_cb : C.output ∉ chainL C b := by
      intro hmem
      have h1 := (chain_props hC b).2.2.2.2.1 C.output hmem (eof b) (by simp [eof])
      obtain ⟨a, c, hac, ha, hc⟩ := (heval (eof b)).mp h1
      simp only [eof, decide_eq_true_eq] at ha hc
      subst ha; subst hc
      exact G.irrefl hac
    have hout_cond : tgt C.output ∉ gStarSet ∨ C.output ∈ gStarSet := by
      dsimp only [tgt]
      rw [targetAux_stop n C stopSet (n + C.gates.length) C.output (Or.inr (by rw [hC.2.2.1]))]
      exact (Classical.em (C.output ∈ gStarSet)).symm
    have heq_out := hstep_ind C.output (by rw [hC.2.2.1]; have := hC.2.1; omega) hout_not_cb hout_cond
    have h1 : C.eval (List.ofFn (pair b b')) = true :=
      (heval _).mpr ⟨b, b', hbb', by simp [pair], by simp [pair]⟩
    have h0 : C.eval (List.ofFn (eof b')) = false := by
      cases hv : C.eval (List.ofFn (eof b'))
      · rfl
      · exfalso
        obtain ⟨a, c, hac, ha, hc⟩ := (heval _).mp hv
        simp only [eof, decide_eq_true_eq] at ha hc
        subst ha; subst hc
        exact G.irrefl hac
    change C.eval (List.ofFn (pair b b')) = C.eval (List.ofFn (eof b')) at heq_out
    rw [h1, h0] at heq_out
    exact absurd heq_out (by decide)
  have hdA_le_1 : ∀ b ∈ B, (A.filter (fun u => G.Adj u b)).card ≤ 1 := by
    intro b hb
    set NA := A.filter (fun u => G.Adj u b)
    have hex_j : ∀ u ∈ NA, ∃ j ∈ readers C (endW C b), tgt (n + j) = n + gStar u := fun u hu =>
      hpath_to_gStar u (Finset.mem_filter.mp hu).1 b (Finset.mem_filter.mp hu).2
    let f : Fin n → ℕ := fun u => if h : u ∈ NA then (hex_j u h).choose else 0
    have hf_mem : ∀ u ∈ NA, f u ∈ (readers C (endW C b)).filter (fun j => tgt (n + j) ∈ gStarSet) := by
      intro u hu
      simp only [f, hu, ↓reduceDIte, Finset.mem_filter]
      have hspec := (hex_j u hu).choose_spec
      refine ⟨hspec.1, ?_⟩
      rw [hspec.2]
      exact Finset.mem_image_of_mem _ (Finset.mem_filter.mp hu).1
    have hf_inj : Set.InjOn f NA := by
      intro u1 hu1 u2 hu2 heq
      have hu1' : u1 ∈ NA := hu1
      have hu2' : u2 ∈ NA := hu2
      simp only [f, hu1', hu2', ↓reduceDIte] at heq
      have h1 := (hex_j u1 hu1').choose_spec.2
      have h2 := (hex_j u2 hu2').choose_spec.2
      rw [heq] at h1
      have hge : gStar u1 = gStar u2 := by omega
      exact hgStar_inj u1 (Finset.mem_filter.mp hu1').1 u2 (Finset.mem_filter.mp hu2').1 hge
    have hcard_le : NA.card ≤ ((readers C (endW C b)).filter (fun j => tgt (n + j) ∈ gStarSet)).card := by
      calc NA.card = (NA.image f).card := (Finset.card_image_of_injOn hf_inj).symm
        _ ≤ _ := Finset.card_le_card (fun j hj => by
            obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hj
            exact hf_mem u hu)
    have hread2 := hB_read2 b hb
    have hfilt_le : ((readers C (endW C b)).filter (fun j => tgt (n + j) ∈ gStarSet)).card ≤ 2 := by
      calc _ ≤ (readers C (endW C b)).card := Finset.card_filter_le _ _
        _ = 2 := hread2
    by_contra hgt1
    have hNA_eq2 : NA.card = 2 := by omega
    have hfilt_eq2 : ((readers C (endW C b)).filter (fun j => tgt (n + j) ∈ gStarSet)).card = 2 := by
      omega
    have hfilt_eq : (readers C (endW C b)).filter (fun j => tgt (n + j) ∈ gStarSet) =
        readers C (endW C b) :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
    have hall : ∀ j ∈ readers C (endW C b), tgt (n + j) ∈ gStarSet := by
      intro j hj
      rw [← hfilt_eq] at hj
      exact (Finset.mem_filter.mp hj).2
    have hfin : (G.neighborSet b).Finite := Set.toFinite _
    have hcard_nb : hfin.toFinset.card = 3 := by
      rw [← Set.ncard_eq_toFinset_card (G.neighborSet b) hfin]; exact hdeg b
    have hsub_NA : NA ⊆ hfin.toFinset := by
      intro u hu
      exact (hfin.mem_toFinset).mpr ((Finset.mem_filter.mp hu).2.symm)
    have hsdiff_pos : 0 < (hfin.toFinset \ NA).card := by
      have := Finset.card_sdiff_add_card_eq_card hsub_NA
      omega
    obtain ⟨b', hb'⟩ := Finset.card_pos.mp hsdiff_pos
    obtain ⟨hb'nb, hb'not⟩ := Finset.mem_sdiff.mp hb'
    have hbb' : G.Adj b b' := (hfin.mem_toFinset).mp hb'nb
    have hb'B : b' ∈ B := by
      by_contra hb'notB
      have hb'A : b' ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ b', fun h =>
        hb'notB (Finset.mem_filter.mpr ⟨Finset.mem_univ b', h⟩)⟩
      exact hb'not (Finset.mem_filter.mpr ⟨hb'A, hbb'.symm⟩)
    exact hB0_no_B_nb b hb hall b' hb'B hbb'
  have ht_lt_n : t < n := by
    let S0 : Finset (Fin n) := Finset.univ.erase ⟨0, hn_pos⟩
    have hS0 : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S0 := by
      intro u v huv
      by_cases hu0 : u = ⟨0, hn_pos⟩
      · right
        exact Finset.mem_erase.mpr ⟨fun hv0 => G.irrefl (hu0 ▸ hv0 ▸ huv), Finset.mem_univ v⟩
      · left
        exact Finset.mem_erase.mpr ⟨hu0, Finset.mem_univ u⟩
    have h1 := hvc_min S0 hS0
    have h2 : S0.card = n - 1 := by
      simp [S0, Finset.card_erase_of_mem (Finset.mem_univ _)]
    omega
  have hA_nonempty : A.Nonempty := by
    have hpart : B.card + A.card = n := by
      have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
        (p := fun v => 2 ≤ (readers C (endW C v)).card)
      simpa [B, A] using this
    exact Finset.card_pos.mp (by omega)
  obtain ⟨u0, hu0A⟩ := hA_nonempty
  have hfin0 : (G.neighborSet u0).Finite := Set.toFinite _
  have hcard0 : hfin0.toFinset.card = 3 := by
    rw [← Set.ncard_eq_toFinset_card (G.neighborSet u0) hfin0]; exact hdeg u0
  obtain ⟨b1, b2, b3, hb1, hb2, hb3, h12, h13, h23⟩ :
      ∃ b1 b2 b3 : Fin n, b1 ∈ hfin0.toFinset ∧ b2 ∈ hfin0.toFinset ∧ b3 ∈ hfin0.toFinset ∧
        b1 ≠ b2 ∧ b1 ≠ b3 ∧ b2 ≠ b3 := by
    obtain ⟨b1, hb1⟩ := Finset.card_pos.mp (by omega : 0 < hfin0.toFinset.card)
    have hc1 : (hfin0.toFinset.erase b1).card = 2 := by
      rw [Finset.card_erase_of_mem hb1]; omega
    obtain ⟨b2, hb2'⟩ := Finset.card_pos.mp (by omega : 0 < (hfin0.toFinset.erase b1).card)
    obtain ⟨h21, hb2⟩ := Finset.mem_erase.mp hb2'
    have hc2 : ((hfin0.toFinset.erase b1).erase b2).card = 1 := by
      rw [Finset.card_erase_of_mem hb2']; omega
    obtain ⟨b3, hb3'⟩ := Finset.card_pos.mp (by omega : 0 < ((hfin0.toFinset.erase b1).erase b2).card)
    obtain ⟨h32, hb3''⟩ := Finset.mem_erase.mp hb3'
    obtain ⟨h31, hb3⟩ := Finset.mem_erase.mp hb3''
    exact ⟨b1, b2, b3, hb1, hb2, hb3, h21.symm, h31.symm, h32.symm⟩
  have hu0b1 : G.Adj u0 b1 := (hfin0.mem_toFinset).mp hb1
  have hu0b2 : G.Adj u0 b2 := (hfin0.mem_toFinset).mp hb2
  have hu0b3 : G.Adj u0 b3 := (hfin0.mem_toFinset).mp hb3
  have hb_in_B : ∀ b : Fin n, G.Adj u0 b → b ∈ B := by
    intro b hub
    by_contra hnot
    have hbA : b ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ b, fun h =>
      hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ b, h⟩)⟩
    exact type2_indep G hdeg hc4 hC heval u0 b (Finset.mem_filter.mp hu0A).2 (Finset.mem_filter.mp hbA).2 hub
  have hnonadj : ∃ x y : Fin n, x ∈ B ∧ y ∈ B ∧ G.Adj u0 x ∧ G.Adj u0 y ∧ x ≠ y ∧ ¬ G.Adj x y := by
    by_cases h1 : G.Adj b1 b2
    · by_cases h2 : G.Adj b2 b3
      · exfalso
        exact hc4 u0 b1 b2 b3 (G.ne_of_adj hu0b1) (G.ne_of_adj hu0b2) (G.ne_of_adj hu0b3)
          h12 h13 h23 hu0b1 h1 h2 hu0b3.symm
      · exact ⟨b2, b3, hb_in_B b2 hu0b2, hb_in_B b3 hu0b3, hu0b2, hu0b3, h23, h2⟩
    · exact ⟨b1, b2, hb_in_B b1 hu0b1, hb_in_B b2 hu0b2, hu0b1, hu0b2, h12, h1⟩
  obtain ⟨x, y, hxB, hyB, hu0x, hu0y, hxy, hnotadj⟩ := hnonadj
  let S' : Finset (Fin n) := insert u0 ((B.erase x).erase y)
  have hS'_vc : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S' := by
    intro p q hpq
    by_contra hnot
    push Not at hnot
    have hpu0 : p ≠ u0 := fun h => hnot.1 (Finset.mem_insert.mpr (Or.inl h))
    have hqu0 : q ≠ u0 := fun h => hnot.2 (Finset.mem_insert.mpr (Or.inl h))
    have hmem_elim : ∀ z ∈ B, z ∉ S' → z = x ∨ z = y := by
      intro z hzB hznot
      by_contra hne
      push Not at hne
      exact hznot (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne.2, Finset.mem_erase.mpr ⟨hne.1, hzB⟩⟩))
    have hno_other_A : ∀ z ∈ ({x, y} : Finset (Fin n)), ∀ w ∈ A, G.Adj w z → w = u0 := by
      intro z hz w hwA hwz
      have hzB : z ∈ B := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl <;> assumption
      have hu0z : G.Adj u0 z := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl <;> assumption
      have hcard_le1 := hdA_le_1 z hzB
      have h1 : u0 ∈ A.filter (fun u => G.Adj u z) := Finset.mem_filter.mpr ⟨hu0A, hu0z⟩
      have h2 : w ∈ A.filter (fun u => G.Adj u z) := Finset.mem_filter.mpr ⟨hwA, hwz⟩
      exact Finset.card_le_one.mp hcard_le1 w h2 u0 h1
    rcases hB_vc p q hpq with hpB | hqB
    · have hpxy := hmem_elim p hpB hnot.1
      by_cases hqB' : q ∈ B
      · have hqxy := hmem_elim q hqB' hnot.2
        rcases hpxy with rfl | rfl <;> rcases hqxy with rfl | rfl
        · exact G.irrefl hpq
        · exact hnotadj hpq
        · exact hnotadj hpq.symm
        · exact G.irrefl hpq
      · have hqA : q ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ q, fun h =>
          hqB' (Finset.mem_filter.mpr ⟨Finset.mem_univ q, h⟩)⟩
        have hpin : p ∈ ({x, y} : Finset (Fin n)) := by
          rcases hpxy with rfl | rfl <;> simp
        exact hqu0 (hno_other_A p hpin q hqA hpq.symm)
    · have hqxy := hmem_elim q hqB hnot.2
      by_cases hpB' : p ∈ B
      · have hpxy := hmem_elim p hpB' hnot.1
        rcases hpxy with rfl | rfl <;> rcases hqxy with rfl | rfl
        · exact G.irrefl hpq
        · exact hnotadj hpq
        · exact hnotadj hpq.symm
        · exact G.irrefl hpq
      · have hpA : p ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ p, fun h =>
          hpB' (Finset.mem_filter.mpr ⟨Finset.mem_univ p, h⟩)⟩
        have hqin : q ∈ ({x, y} : Finset (Fin n)) := by
          rcases hqxy with rfl | rfl <;> simp
        exact hpu0 (hno_other_A q hqin p hpA hpq)
  have hu0_notB : u0 ∉ B := fun h => (Finset.mem_filter.mp hu0A).2 (Finset.mem_filter.mp h).2
  have hu0_not_er : u0 ∉ (B.erase x).erase y := fun h =>
    hu0_notB (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
  have hy_in_er : y ∈ B.erase x := Finset.mem_erase.mpr ⟨hxy.symm, hyB⟩
  have hS'_card : S'.card = t - 1 := by
    rw [Finset.card_insert_of_notMem hu0_not_er, Finset.card_erase_of_mem hy_in_er,
      Finset.card_erase_of_mem hxB, hB_eq_t]
    have hB_ge2 : 2 ≤ B.card := by
      have hsub : ({x, y} : Finset (Fin n)) ⊆ B := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl <;> assumption
      have := Finset.card_le_card hsub
      rw [Finset.card_pair hxy] at this
      exact this
    omega
  have hmin_S' := hvc_min S' hS'_vc
  have hB_ge2 : 2 ≤ t := by
    have hsub : ({x, y} : Finset (Fin n)) ⊆ B := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    have := Finset.card_le_card hsub
    rw [Finset.card_pair hxy] at this
    omega
  omega

end PEqualNP.Outside.L_meta_616_aux

theorem PEqualNP.Outside.L_meta_616 : ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ v : Fin n, (G.neighborSet v).ncard = 3) → (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) → (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) → (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → n + t ≤ C.size :=
  PEqualNP.Outside.L_meta_616_aux.main_proof
