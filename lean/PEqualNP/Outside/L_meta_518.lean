import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L518

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    rw [wiresFrom_cons, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem wiresFrom_getD_gate (gs : List Gate) (w : List Bool) (t : ℕ) (ht : t < gs.length) :
    (wiresFrom gs w).getD (w.length + t) false =
      (gs[t]).op.eval ((gs[t]).inputs.map fun i => (wiresFrom (gs.take t) w).getD i false) := by
  have hsplit : gs = gs.take t ++ gs[t] :: gs.drop (t + 1) := by
    simp [List.take_append_drop]
  conv_lhs => rw [hsplit, wiresFrom_append, wiresFrom_cons]
  have hlen : (wiresFrom (gs.take t) w).length = w.length + t := by
    rw [length_wiresFrom, List.length_take, Nat.min_eq_left ht.le]
  rw [getD_wiresFrom _ _ _ (by simp [hlen])]
  rw [show w.length + t = (wiresFrom (gs.take t) w).length by omega, getD_snoc_eq]

theorem wiresFrom_take_getD (gs : List Gate) (w : List Bool) (t i : ℕ)
    (hi : i < (wiresFrom (gs.take t) w).length) :
    (wiresFrom gs w).getD i false = (wiresFrom (gs.take t) w).getD i false := by
  conv_lhs => rw [← List.take_append_drop t gs, wiresFrom_append]
  exact getD_wiresFrom _ _ _ hi

theorem gate_value (gs : List Gate) (w : List Bool) (t : ℕ) (ht : t < gs.length) :
    (wiresFrom gs w).getD (w.length + t) false =
      (gs[t]).op.eval ((gs[t]).inputs.map fun i =>
        if i < w.length + t then (wiresFrom gs w).getD i false else false) := by
  rw [wiresFrom_getD_gate gs w t ht]
  congr 1
  apply List.map_congr_left
  intro i _
  have hlen : (wiresFrom (gs.take t) w).length = w.length + t := by
    rw [length_wiresFrom, List.length_take, Nat.min_eq_left ht.le]
  split_ifs with h
  · exact (wiresFrom_take_getD gs w t i (by rw [hlen]; exact h)).symm
  · exact List.getD_eq_default _ _ (by rw [hlen]; omega)

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate]

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    rw [List.map_cons, wiresFrom_cons, wiresFrom_cons, normGate_eval, ih]

def gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union {n : ℕ} (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom {n : ℕ} (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

theorem suppsFrom_append {n : ℕ} (gs gs' : List Gate) (L : List (Finset (Fin n))) :
    suppsFrom (gs ++ gs') L = suppsFrom gs' (suppsFrom gs L) := by
  simp [suppsFrom, List.foldl_append]

theorem suppsFrom_cons {n : ℕ} (g : Gate) (gs : List Gate) (L : List (Finset (Fin n))) :
    suppsFrom (g :: gs) L = suppsFrom gs (L ++ [gateSupp L g]) := rfl

theorem suppsFrom_prefix {n : ℕ} (gs : List Gate) : ∀ L : List (Finset (Fin n)),
    ∃ t : List (Finset (Fin n)), suppsFrom gs L = L ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro L; exact ⟨[], by simp [suppsFrom], rfl⟩
  | cons g gs ih =>
    intro L
    obtain ⟨t, ht, hl⟩ := ih (L ++ [gateSupp L g])
    refine ⟨gateSupp L g :: t, ?_, by simp [hl]⟩
    rw [suppsFrom_cons, ht]; simp

theorem length_suppsFrom {n : ℕ} (gs : List Gate) (L : List (Finset (Fin n))) :
    (suppsFrom gs L).length = L.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := suppsFrom_prefix gs L
  rw [ht]; simp [hl]

theorem getD_suppsFrom {n : ℕ} (gs : List Gate) (L : List (Finset (Fin n))) (i : ℕ)
    (h : i < L.length) :
    (suppsFrom gs L).getD i ∅ = L.getD i ∅ := by
  obtain ⟨t, ht, _⟩ := suppsFrom_prefix gs L
  rw [ht, List.getD_append _ _ _ _ h]

theorem suppsFrom_getD_gate {n : ℕ} (gs : List Gate) (L : List (Finset (Fin n))) (t : ℕ)
    (ht : t < gs.length) :
    (suppsFrom gs L).getD (L.length + t) ∅ =
      gateSupp (suppsFrom (gs.take t) L) (gs[t]) := by
  have hsplit : gs = gs.take t ++ gs[t] :: gs.drop (t + 1) := by
    simp [List.take_append_drop]
  conv_lhs => rw [hsplit, suppsFrom_append, suppsFrom_cons]
  have hlen : (suppsFrom (gs.take t) L).length = L.length + t := by
    rw [length_suppsFrom, List.length_take, Nat.min_eq_left ht.le]
  rw [getD_suppsFrom _ _ _ (by simp [hlen])]
  rw [show L.length + t = (suppsFrom (gs.take t) L).length by omega, getD_snoc_eq]

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree {n : ℕ} (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom {n : ℕ} (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs {n : ℕ} (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Cnt {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs (n : ℕ) : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom {n : ℕ} (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

theorem dep_lower_finset {n : ℕ} (D : Finset (Fin n)) (f : (Fin n → Bool) → Bool)
    (hdep : ∀ i ∈ D, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : D.card ≤ s + 1 := by
  obtain ⟨C, hfan, hsize, heval⟩ := h
  set L := suppsFrom C.gates (inputSupps n) with hL
  have hsub : D ⊆ L.getD C.output ∅ := by
    intro i hi
    by_contra hni
    obtain ⟨x, hx⟩ := hdep i hi
    have hagr := agree_wiresFrom (Function.update x i (!x i)) x C.gates (inputSupps n)
      (List.ofFn (Function.update x i (!x i))) (List.ofFn x) (agree_inputs _ _)
    have heq := hagr.2.2 C.output (fun j hj => by
      have hji : j ≠ i := fun h => hni (h ▸ hj)
      simp [Function.update_of_ne hji])
    have e1 := heval (Function.update x i (!x i))
    have e2 := heval x
    simp only [Circuit.eval, wires_eq] at e1 e2
    rw [e1, e2] at heq
    exact hx heq
  have hcnt := cnt_suppsFrom C.gates 0 (inputSupps n) hfan (cnt_inputs n) {C.output}
  rw [← hL, zero_add, Finset.singleton_biUnion, Finset.card_singleton] at hcnt
  have hcard := Finset.card_le_card hsub
  simp only [Circuit.size] at hsize
  omega

abbrev Stat := Sum Bool ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨e, l⟩⟩⟩
    · simp at hc
    · rcases a with a | a <;> simp [simplify, simpAnd] at hc ⊢
    · rcases a with a | a <;> rcases b with b | b <;> simp [simplify, simpAnd] at hc ⊢
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨e, l⟩⟩⟩
    · simp at hc
    · rcases a with a | a <;> simp [simplify, simpOr] at hc ⊢
    · rcases a with a | a <;> rcases b with b | b <;> simp [simplify, simpOr] at hc ⊢
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp at hc
    · have hl : l = [] := by
        have := hnot rfl; simp only [List.length_cons] at this
        exact List.eq_nil_of_length_eq_zero (by omega)
      subst hl
      rcases a with a | a <;> simp [simplify, simpNot] at hc ⊢

theorem simplify_valid (op : GateOp) (m : ℕ) (ins : List Stat)
    (hv : ∀ s ∈ ins, Stat.Valid m s) :
    Stat.Valid (m + ((simplify op m ins).1.toList).length) (simplify op m ins).2 := by
  cases op <;> simp only [simplify]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp [simpAnd, Stat.Valid]
    · rcases a with a | a
      · simp [simpAnd, Stat.Valid]
      · have := hv (Sum.inr a) (by simp); simp [simpAnd, Stat.Valid] at this ⊢; exact this
    · rcases a with a | a <;> rcases b with b | b
      · simp [simpAnd, Stat.Valid]
      · have := hv (Sum.inr b) (by simp); cases a <;> simp [simpAnd, Stat.Valid] at this ⊢; exact this
      · have := hv (Sum.inr a) (by simp); cases b <;> simp [simpAnd, Stat.Valid] at this ⊢; exact this
      · simp [simpAnd, Stat.Valid]
    · simp [simpAnd, Stat.Valid]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp [simpOr, Stat.Valid]
    · rcases a with a | a
      · simp [simpOr, Stat.Valid]
      · have := hv (Sum.inr a) (by simp); simp [simpOr, Stat.Valid] at this ⊢; exact this
    · rcases a with a | a <;> rcases b with b | b
      · simp [simpOr, Stat.Valid]
      · have := hv (Sum.inr b) (by simp); cases a <;> simp [simpOr, Stat.Valid] at this ⊢; exact this
      · have := hv (Sum.inr a) (by simp); cases b <;> simp [simpOr, Stat.Valid] at this ⊢; exact this
      · simp [simpOr, Stat.Valid]
    · simp [simpOr, Stat.Valid]
  · rcases ins with _ | ⟨a, l⟩
    · simp [simpNot, Stat.Valid]
    · rcases a with a | a <;> simp [simpNot, Stat.Valid]
  · simp [Stat.Valid]
  · simp [Stat.Valid]

theorem simplify_eval (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (ins : List Stat) (hlen : ins.length ≤ 2) (w : List Bool) :
    Stat.val (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2 =
      op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp [simplify, simpAnd, wiresFrom, Stat.val, GateOp.eval]
    · rcases a with a | a <;> simp [simplify, simpAnd, wiresFrom, Stat.val, GateOp.eval]
    · rcases a with a | a <;> rcases b with b | b
      · simp [simplify, simpAnd, wiresFrom, Stat.val, GateOp.eval]
      · cases a <;> simp [simplify, simpAnd, wiresFrom, Stat.val, GateOp.eval]
      · cases b <;> simp [simplify, simpAnd, wiresFrom, Stat.val, GateOp.eval]
      · simp [simplify, simpAnd, wiresFrom, Stat.val, GateOp.eval]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp [simplify, simpOr, wiresFrom, Stat.val, GateOp.eval]
    · rcases a with a | a <;> simp [simplify, simpOr, wiresFrom, Stat.val, GateOp.eval]
    · rcases a with a | a <;> rcases b with b | b
      · simp [simplify, simpOr, wiresFrom, Stat.val, GateOp.eval]
      · cases a <;> simp [simplify, simpOr, wiresFrom, Stat.val, GateOp.eval]
      · cases b <;> simp [simplify, simpOr, wiresFrom, Stat.val, GateOp.eval]
      · simp [simplify, simpOr, wiresFrom, Stat.val, GateOp.eval]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, wiresFrom, Stat.val, GateOp.eval]
    · rcases a with a | a <;> simp [simplify, simpNot, wiresFrom, Stat.val, GateOp.eval]

def elimStep (m : ℕ) (st : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  let ins := g.inputs.map fun i => st.1.getD i (Sum.inl false)
  let r := simplify g.op (m + st.2.length) ins
  (st.1 ++ [r.2], st.2 ++ r.1.toList)

def elim (m : ℕ) (gs : List Gate) (st : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep m) st

theorem elim_cons (m : ℕ) (g : Gate) (gs : List Gate) (st : List Stat × List Gate) :
    elim m (g :: gs) st = elim m gs (elimStep m st g) := rfl

theorem elim_append (m : ℕ) (gs1 gs2 : List Gate) (st : List Stat × List Gate) :
    elim m (gs1 ++ gs2) st = elim m gs2 (elim m gs1 st) := by
  simp [elim, List.foldl_append]

theorem elim_prefix (m : ℕ) (gs : List Gate) : ∀ st : List Stat × List Gate,
    ∃ (t1 : List Stat) (t2 : List Gate),
      (elim m gs st).1 = st.1 ++ t1 ∧ (elim m gs st).2 = st.2 ++ t2 ∧
      t1.length = gs.length ∧ t2.length ≤ gs.length := by
  induction gs with
  | nil => intro st; exact ⟨[], [], by simp [elim], by simp [elim], rfl, le_rfl⟩
  | cons g gs ih =>
    intro st
    obtain ⟨t1, t2, h1, h2, hl1, hl2⟩ := ih (elimStep m st g)
    set ins := g.inputs.map fun i => st.1.getD i (Sum.inl false)
    set r := simplify g.op (m + st.2.length) ins
    refine ⟨r.2 :: t1, r.1.toList ++ t2, ?_, ?_, ?_, ?_⟩
    · rw [elim_cons, h1]; simp [elimStep, r, ins]
    · rw [elim_cons, h2]; simp [elimStep, r, ins]
    · simp [hl1]
    · have hlen : r.1.toList.length ≤ 1 := by cases r.1 <;> simp
      simp; omega

theorem elim_ok (m : ℕ) (gs : List Gate) : ∀ st : List Stat × List Gate,
    (∀ g ∈ st.2, Ok g) → ∀ g ∈ (elim m gs st).2, Ok g := by
  induction gs with
  | nil => intro st h; exact h
  | cons g gs ih =>
    intro st h
    apply ih (elimStep m st g)
    intro g' hg'
    simp only [elimStep, List.mem_append, Option.mem_toList] at hg'
    rcases hg' with hg' | hg'
    · exact h g' hg'
    · exact simplify_ok _ _ _ g' hg'

def Inv (m : ℕ) (wOld wNew : List Bool) (st : List Stat × List Gate) : Prop :=
  st.1.length = wOld.length ∧
  wNew.length = m ∧
  (∀ i, Stat.Valid (m + st.2.length) (st.1.getD i (Sum.inl false)) ∧
    Stat.val (wiresFrom st.2 wNew) (st.1.getD i (Sum.inl false)) = wOld.getD i false)

theorem inv_step (m : ℕ) (wOld wNew : List Bool) (st : List Stat × List Gate) (g : Gate)
    (hg : Ok g) (hinv : Inv m wOld wNew st) :
    Inv m (wOld ++ [g.op.eval (g.inputs.map fun i => wOld.getD i false)]) wNew (elimStep m st g) := by
  obtain ⟨hlen1, hlen2, hval⟩ := hinv
  set ins := g.inputs.map fun i => st.1.getD i (Sum.inl false) with hins
  set r := simplify g.op (m + st.2.length) ins with hr
  have hcur : (wiresFrom st.2 wNew).length = m + st.2.length := by
    rw [length_wiresFrom, hlen2]
  have hrlen : (wiresFrom (st.2 ++ r.1.toList) wNew).length =
      m + (st.2 ++ r.1.toList).length := by
    rw [length_wiresFrom, hlen2]
  have hvalid_r : Stat.Valid (m + (st.2 ++ r.1.toList).length) r.2 := by
    have := simplify_valid g.op (m + st.2.length) ins (fun s hs => by
      obtain ⟨i, _, rfl⟩ := List.mem_map.1 hs
      exact (hval i).1)
    simpa [hr, List.length_append, Nat.add_assoc] using this
  have hhop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
    simpa [Ok, Set.mem_insert_iff, Set.mem_singleton_iff] using hg.1
  have heval_r : Stat.val (wiresFrom (st.2 ++ r.1.toList) wNew) r.2 =
      g.op.eval (g.inputs.map fun i => wOld.getD i false) := by
    rw [wiresFrom_append]
    have h1 := simplify_eval g.op hhop ins (by simpa [hins] using hg.2) (wiresFrom st.2 wNew)
    rw [hcur] at h1
    rw [← hr] at h1
    rw [h1, hins, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    exact (hval i).2
  refine ⟨by simp [elimStep, hlen1], hlen2, ?_⟩
  intro i
  by_cases hi : i = st.1.length
  · subst hi
    simp only [elimStep]
    rw [getD_snoc_eq, hlen1, getD_snoc_eq]
    exact ⟨hvalid_r, heval_r⟩
  · simp only [elimStep]
    rw [getD_snoc_ne _ _ _ _ hi, getD_snoc_ne _ _ _ _ (by omega)]
    obtain ⟨hv, he⟩ := hval i
    cases hst : st.1.getD i (Sum.inl false) with
    | inl c =>
      rw [hst] at hv he
      exact ⟨trivial, by simpa [Stat.val] using he⟩
    | inr j =>
      rw [hst] at hv he
      simp only [Stat.Valid] at hv
      refine ⟨by simp [Stat.Valid, List.length_append]; omega, ?_⟩
      rw [wiresFrom_append]
      simp only [Stat.val] at he ⊢
      rw [getD_wiresFrom _ _ _ (by rw [hcur]; exact hv), he]

theorem inv_elim (m : ℕ) (gs : List Gate) (hok : ∀ g ∈ gs, Ok g) :
    ∀ (wOld wNew : List Bool) (st : List Stat × List Gate),
      Inv m wOld wNew st → Inv m (wiresFrom gs wOld) wNew (elim m gs st) := by
  induction gs with
  | nil => intro wOld wNew st h; exact h
  | cons g gs ih =>
    intro wOld wNew st h
    rw [wiresFrom_cons, elim_cons]
    exact ih (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) _ _ _
      (inv_step m wOld wNew st g (hok g List.mem_cons_self) h)

def del (G : List Gate) (t p r : ℕ) : List Gate :=
  G.take t ++ (G.drop (t + 1)).map (fun g => ⟨g.op, g.inputs.map (fun i =>
    if i < p then i else if i = p then r else i - 1)⟩)

def ren (p r i : ℕ) : ℕ := if i < p then i else if i = p then r else i - 1

def renG (p r : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (ren p r)⟩

theorem getD_eraseIdx_lt (l : List Bool) (p i : ℕ) (hi : i < p) :
    (l.eraseIdx p).getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx_of_lt hi]

theorem getD_eraseIdx_ge (l : List Bool) (p i : ℕ) (hi : p ≤ i) :
    (l.eraseIdx p).getD i false = l.getD (i + 1) false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx_of_ge hi]

theorem del_wiresFrom_aux (W : List Bool) (p r : ℕ) (hr : r < p ∨ W.length ≤ r) :
    ∀ (L : List Gate) (v : List Bool), wiresFrom L v = W → p < v.length →
      (∀ g ∈ L, p ∈ g.inputs → W.getD p false = W.getD r false) →
      wiresFrom (L.map (renG p r)) (v.eraseIdx p) = W.eraseIdx p := by
  intro L
  induction L with
  | nil =>
    intro v hW _ _
    simp only [wiresFrom, List.foldl_nil] at hW
    subst hW
    rfl
  | cons g L ih =>
    intro v hW hp hv
    rw [wiresFrom_cons] at hW
    rw [List.map_cons, wiresFrom_cons]
    have hvW : ∀ i, i < v.length → v.getD i false = W.getD i false := fun i hi => by
      rw [← hW, getD_wiresFrom _ _ _ (by simp; omega)]
      exact (List.getD_append _ _ _ _ hi).symm
    have hWlen : v.length + 1 + L.length = W.length := by
      have := congrArg List.length hW
      rw [length_wiresFrom] at this
      simp at this
      omega
    have hstep : (v.eraseIdx p) ++ [(renG p r g).op.eval ((renG p r g).inputs.map fun i =>
        (v.eraseIdx p).getD i false)] =
        (v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]).eraseIdx p := by
      rw [List.eraseIdx_append_of_lt_length hp]
      congr 2
      simp only [renG, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi
      simp only [Function.comp, ren]
      split_ifs with h1 h2
      · exact getD_eraseIdx_lt _ _ _ h1
      · subst h2
        rcases hr with hr | hr
        · rw [getD_eraseIdx_lt _ _ _ hr, hvW _ (by omega), hvW _ hp]
          exact (hv g List.mem_cons_self hi).symm
        · rw [List.getD_eq_default _ _ (by rw [List.length_eraseIdx_of_lt hp]; omega), hvW _ hp,
            hv g List.mem_cons_self hi, List.getD_eq_default _ _ hr]
      · rw [getD_eraseIdx_ge _ _ _ (by omega), Nat.sub_add_cancel (by omega)]
    rw [hstep]
    exact ih _ hW (by simp; omega) (fun g' hg' => hv g' (List.mem_cons_of_mem _ hg'))

theorem del_eval (G : List Gate) (o : ℕ) (x : List Bool) (t r : ℕ) (ht : t < G.length)
    (hr : r < x.length + t ∨ x.length + G.length ≤ r)
    (hv : ∀ g ∈ G.drop (t + 1), x.length + t ∈ g.inputs →
      (wiresFrom G x).getD (x.length + t) false = (wiresFrom G x).getD r false)
    (ho : o = x.length + t →
      (wiresFrom G x).getD (x.length + t) false = (wiresFrom G x).getD r false) :
    Circuit.eval ⟨del G t (x.length + t) r, ren (x.length + t) r o⟩ x = Circuit.eval ⟨G, o⟩ x := by
  have hsplit : G = G.take t ++ G[t] :: G.drop (t + 1) := by simp
  have hWlen : (wiresFrom G x).length = x.length + G.length := length_wiresFrom _ _
  have hW' : wiresFrom (G.drop (t + 1)) (wiresFrom (G.take t) x ++
      [G[t].op.eval (G[t].inputs.map fun i => (wiresFrom (G.take t) x).getD i false)]) =
      wiresFrom G x := by
    conv_rhs => rw [hsplit]
    rw [wiresFrom_append, wiresFrom_cons]
  have hlen : (wiresFrom (G.take t) x).length = x.length + t := by
    rw [length_wiresFrom, List.length_take, Nat.min_eq_left ht.le]
  have hv0 : wiresFrom (G.take t) x =
      (wiresFrom (G.take t) x ++ [G[t].op.eval (G[t].inputs.map fun i =>
        (wiresFrom (G.take t) x).getD i false)]).eraseIdx (x.length + t) := by
    rw [List.eraseIdx_append_of_length_le (by omega)]
    simp [hlen]
  have hdel : wiresFrom (del G t (x.length + t) r) x =
      (wiresFrom G x).eraseIdx (x.length + t) := by
    change wiresFrom (G.take t ++ (G.drop (t + 1)).map (renG (x.length + t) r)) x = _
    rw [wiresFrom_append, hv0]
    exact del_wiresFrom_aux _ (x.length + t) r (by rwa [hWlen]) _ _ hW' (by simp [hlen]) hv
  simp only [Circuit.eval, wires_eq, hdel]
  unfold ren
  split_ifs with h1 h2
  · exact getD_eraseIdx_lt _ _ _ h1
  · subst h2
    rcases hr with hr | hr
    · rw [getD_eraseIdx_lt _ _ _ hr]
      exact (ho rfl).symm
    · rw [List.getD_eq_default _ _ (by rw [List.length_eraseIdx_of_lt (by rw [hWlen]; omega), hWlen]; omega),
        ho rfl, List.getD_eq_default _ _ (by rw [hWlen]; exact hr)]
  · rw [getD_eraseIdx_ge _ _ _ (by omega), Nat.sub_add_cancel (by omega)]

theorem del_length (G : List Gate) (t p r : ℕ) (ht : t < G.length) :
    (del G t p r).length = G.length - 1 := by
  simp only [del, List.length_append, List.length_take, List.length_map, List.length_drop]
  omega

theorem fanInTwo_del (G : List Gate) (o t p r o' : ℕ) (h : FanInTwo ⟨G, o⟩) :
    FanInTwo ⟨del G t p r, o'⟩ := by
  simp only [FanInTwo] at h ⊢
  intro g hg
  simp only [del, List.mem_append, List.mem_map] at hg
  rcases hg with hg | ⟨g', hg', rfl⟩
  · exact h g (List.mem_of_mem_take hg)
  · obtain ⟨h1, h2⟩ := h g' (List.mem_of_mem_drop hg')
    exact ⟨h1, by simpa using h2⟩

def seedInput (n : ℕ) (p : Fin n) (b : Bool) : List Stat :=
  List.ofFn fun i : Fin n => if i = p then Sum.inl b else Sum.inr i.val

theorem seedInput_inv {n : ℕ} (p : Fin n) (b : Bool) (x : Fin n → Bool) :
    Inv n (List.ofFn (Function.update x p b)) (List.ofFn x) (seedInput n p b, []) := by
  refine ⟨by simp [seedInput], by simp, ?_⟩
  intro i
  by_cases hi : i < n
  · simp only [seedInput, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte,
      Option.getD_some, wiresFrom, List.foldl_nil]
    by_cases hp : (⟨i, hi⟩ : Fin n) = p
    · subst hp
      simp [Stat.Valid, Stat.val]
    · simp [hp, Stat.Valid, Stat.val, hi]
  · simp [seedInput, List.getD_eq_getElem?_getD, hi, Stat.Valid, Stat.val]

theorem elim_skips_count (m : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) :
    ∀ (st : List Stat × List Gate) (S : Finset ℕ),
      (∀ t ∈ S, ∃ ht : t < gs.length, ∃ i ∈ (gs[t]).inputs, ∃ c,
        (elim m (gs.take t) st).1.getD i (Sum.inl false) = Sum.inl c) →
      (elim m gs st).2.length + S.card ≤ st.2.length + gs.length := by
  induction gs with
  | nil =>
    intro st S hS
    have hSe : S = ∅ := by
      ext t; simp only [Finset.notMem_empty, iff_false]
      intro ht; obtain ⟨h, _⟩ := hS t ht; simp at h
    subst hSe; simp [elim]
  | cons g gs ih =>
    intro st S hS
    set st' := elimStep m st g with hst'
    set S' := (S.erase 0).image (fun t => t - 1) with hS'
    have hS'prop : ∀ t ∈ S', ∃ ht : t < gs.length, ∃ i ∈ (gs[t]).inputs, ∃ c,
        (elim m (gs.take t) st').1.getD i (Sum.inl false) = Sum.inl c := by
      intro t ht
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 ht
      obtain ⟨hu0, huS⟩ := Finset.mem_erase.1 hu
      obtain ⟨hult, i, hi, c, hc⟩ := hS u huS
      obtain ⟨u', rfl⟩ : ∃ u', u = u' + 1 := ⟨u - 1, by omega⟩
      refine ⟨by simpa using hult, i, by simpa using hi, c, ?_⟩
      simpa [elim_cons, hst'] using hc
    have hrec := ih (fun g' hg' => hnok g' (List.mem_cons_of_mem _ hg')) st' S' hS'prop
    have hcardS' : S'.card = (S.erase 0).card := by
      apply Finset.card_image_of_injOn
      intro a ha b hb hab
      have ha0 := (Finset.mem_erase.1 ha).1
      have hb0 := (Finset.mem_erase.1 hb).1
      dsimp only at hab
      omega
    rw [hcardS'] at hrec
    rw [elim_cons, ← hst']
    by_cases h0 : 0 ∈ S
    · obtain ⟨_, i, hi, c, hc⟩ := hS 0 h0
      simp only [List.take_zero, elim, List.foldl_nil] at hc
      have hnokg := hnok g List.mem_cons_self
      have hhop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
        simpa [NOk, Ok, Set.mem_insert_iff, Set.mem_singleton_iff] using hnokg.1.1
      have hnone := simplify_count g.op (m + st.2.length)
        (g.inputs.map fun a => st.1.getD a (Sum.inl false)) hhop
        (by simpa using hnokg.1.2) (fun h => by simpa using hnokg.2 h)
        ⟨c, List.mem_map.2 ⟨i, hi, hc⟩⟩
      have hlen_st' : st'.2.length = st.2.length := by
        simp only [hst', elimStep, hnone, Option.toList_none, List.append_nil]
      have hcard0 := Finset.card_erase_add_one h0
      simp only [List.length_cons]
      omega
    · have hlen_st' : st'.2.length ≤ st.2.length + 1 := by
        simp only [hst', elimStep, List.length_append]
        cases (simplify g.op (m + st.2.length) (g.inputs.map fun a => st.1.getD a (Sum.inl false))).1 <;> simp
      have hcard0 : (S.erase 0).card = S.card := by
        rw [Finset.erase_eq_of_notMem h0]
      simp only [List.length_cons]
      omega

theorem elim_getD_take (m : ℕ) (gs : List Gate) (st : List Stat × List Gate) (t i : ℕ)
    (hi : i < st.1.length + t) :
    (elim m gs st).1.getD i (Sum.inl false) = (elim m (gs.take t) st).1.getD i (Sum.inl false) := by
  by_cases ht : t ≤ gs.length
  · conv_lhs => rw [← List.take_append_drop t gs, elim_append]
    obtain ⟨t1, _, h1, _, _, _⟩ := elim_prefix m (gs.drop t) (elim m (gs.take t) st)
    obtain ⟨t0, _, h0, _, hl0, _⟩ := elim_prefix m (gs.take t) st
    rw [h1, List.getD_append _ _ _ _ (by rw [h0, List.length_append, hl0, List.length_take, Nat.min_eq_left ht]; omega)]
  · rw [List.take_of_length_le (by omega)]

theorem elim_const_of_input_mem {n : ℕ} (C : Circuit) (hfan : FanInTwo C) (p : Fin n) (b : Bool)
    (hnc : ∃ x y : Fin n → Bool,
      C.eval (List.ofFn (Function.update x p b)) ≠ C.eval (List.ofFn (Function.update y p b)))
    (S : Finset ℕ)
    (hS : ∀ t ∈ S, ∃ ht : t < C.gates.length, ∃ i ∈ ((C.gates.map normGate)[t]'(by simp [ht])).inputs,
      ∃ c, (elim n ((C.gates.map normGate).take t) (seedInput n p b, [])).1.getD i (Sum.inl false) = Sum.inl c) :
    HasCircuitSize n (fun x => C.eval (List.ofFn (Function.update x p b))) (C.size - S.card) := by
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g' (hfan g' hg')
  have hok : ∀ g ∈ gs, Ok g := fun g hg => (hnok g hg).1
  set res := elim n gs (seedInput n p b, []) with hres
  have hcnt := elim_skips_count n gs hnok (seedInput n p b, []) S (by
    intro t ht
    obtain ⟨hlt, i, hi, c, hc⟩ := hS t ht
    exact ⟨by simpa [hgs] using hlt, i, hi, c, hc⟩)
  have hinv : ∀ x : Fin n → Bool,
      Inv n (wiresFrom gs (List.ofFn (Function.update x p b))) (List.ofFn x) res := fun x =>
    inv_elim n gs hok _ _ _ (seedInput_inv p b x)
  cases hout : res.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    have hx := (hinv x).2.2 C.output
    have hy := (hinv y).2.2 C.output
    rw [hout] at hx hy
    simp only [Stat.val, hgs, wiresFrom_norm] at hx hy
    apply hxy
    simp only [Circuit.eval, wires_eq, ← hx.2, ← hy.2]
  | inr o' =>
    refine ⟨⟨res.2, o'⟩, elim_ok n gs (seedInput n p b, []) (by simp), ?_, ?_⟩
    · simp only [Circuit.size] at hcnt ⊢
      simp only [List.length_nil, zero_add, hgs, List.length_map] at hcnt
      rw [hres, hgs]
      omega
    · intro x
      have hx := (hinv x).2.2 C.output
      rw [hout] at hx
      simp only [Circuit.eval, wires_eq, Stat.val, hgs, wiresFrom_norm] at hx ⊢
      exact hx.2

theorem has_reader_of_dep {n : ℕ} (C : Circuit) (p : Fin n)
    (hdep : ∃ x : Fin n → Bool,
      C.eval (List.ofFn (Function.update x p (!x p))) ≠ C.eval (List.ofFn x)) :
    C.output = p.val ∨ ∃ t, ∃ ht : t < C.gates.length,
      p.val ∈ ((C.gates.map normGate)[t]'(by simp [ht])).inputs := by
  by_contra h
  push_neg at h
  obtain ⟨ho, hnr⟩ := h
  set gs := C.gates.map normGate with hgs
  have hns : ∀ (L : List Gate), (∀ g ∈ L, p.val ∉ g.inputs) →
      ∀ (S : List (Finset (Fin n))), (∀ j, j ≠ p.val → p ∉ S.getD j ∅) →
      ∀ j, j ≠ p.val → p ∉ (suppsFrom L S).getD j ∅ := by
    intro L
    induction L with
    | nil => intro _ S hS j hj; exact hS j hj
    | cons g L ih =>
      intro hL S hS
      apply ih (fun g' hg' => hL g' (List.mem_cons_of_mem _ hg'))
      intro j hj
      by_cases hjl : j = S.length
      · subst hjl
        rw [getD_snoc_eq, mem_gateSupp]
        rintro ⟨a, ha, hpa⟩
        have hap : a ≠ p.val := fun e => hL g List.mem_cons_self (e ▸ ha)
        exact hS a hap hpa
      · rw [getD_snoc_ne _ _ _ _ hjl]
        exact hS j hj
  have hmem : ∀ g ∈ gs, p.val ∉ g.inputs := by
    intro g hg
    obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 hg
    exact hnr t (by simpa [hgs] using ht)
  have hp_not : p ∉ (suppsFrom gs (inputSupps n)).getD C.output ∅ := by
    apply hns gs hmem (inputSupps n) _ C.output ho
    intro j hj
    by_cases hjn : j < n
    · simp only [inputSupps, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hjn, ↓reduceDIte,
        Option.getD_some, Finset.mem_singleton]
      intro e; exact hj (congrArg Fin.val e.symm)
    · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp
  obtain ⟨x, hx⟩ := hdep
  have hagr := agree_wiresFrom (Function.update x p (!x p)) x gs (inputSupps n)
    (List.ofFn (Function.update x p (!x p))) (List.ofFn x) (agree_inputs _ _)
  have heq := hagr.2.2 C.output (fun j hj => by
    have hjp : j ≠ p := fun e => hp_not (e ▸ hj)
    simp [Function.update_of_ne hjp])
  simp only [Circuit.eval, wires_eq, ← wiresFrom_norm C.gates] at hx
  exact hx heq

theorem one_gate_elim {n : ℕ} (f : (Fin n → Bool) → Bool) (p : Fin n) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin n → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∃ x y : Fin n → Bool, f (Function.update x p b) ≠ f (Function.update y p b))
    (hs : HasCircuitSize n f s) :
    1 ≤ s ∧ HasCircuitSize n (fun x => f (Function.update x p b)) (s - 1) := by
  obtain ⟨C, hfan, hsize, heval⟩ := hs
  have hdepC : ∃ x : Fin n → Bool,
      C.eval (List.ofFn (Function.update x p (!x p))) ≠ C.eval (List.ofFn x) := by
    obtain ⟨x, hx⟩ := hdep; exact ⟨x, by rwa [heval, heval]⟩
  have hncC : ∃ x y : Fin n → Bool,
      C.eval (List.ofFn (Function.update x p b)) ≠ C.eval (List.ofFn (Function.update y p b)) := by
    obtain ⟨x, y, hxy⟩ := hnc; exact ⟨x, y, by rwa [heval, heval]⟩
  rcases has_reader_of_dep C p hdepC with ho | ⟨t, ht, hmem⟩
  · exfalso
    obtain ⟨x, y, hxy⟩ := hncC
    apply hxy
    simp only [Circuit.eval, wires_eq, ho]
    rw [getD_wiresFrom _ _ _ (by simp), getD_wiresFrom _ _ _ (by simp)]
    simp
  · have hpos : 1 ≤ C.size := by simp [Circuit.size]; omega
    have hres := elim_const_of_input_mem C hfan p b hncC {t} (by
      intro t' ht'
      rw [Finset.mem_singleton] at ht'
      subst t'
      refine ⟨ht, p.val, hmem, b, ?_⟩
      obtain ⟨t1, _, h1, _, _, _⟩ := elim_prefix n ((C.gates.map normGate).take t) (seedInput n p b, [])
      rw [h1, List.getD_append _ _ _ _ (by simp [seedInput])]
      simp [seedInput, p.isLt])
    simp only [Finset.card_singleton] at hres
    refine ⟨by omega, ?_⟩
    obtain ⟨D, hDf, hDs, hDe⟩ := hres
    exact ⟨D, hDf, by omega, fun x => by dsimp only; rw [hDe x]; exact heval _⟩

theorem hasCircuitSize_mono {n : ℕ} {f : (Fin n → Bool) → Bool} {s s' : ℕ} (h : s ≤ s')
    (hc : HasCircuitSize n f s) : HasCircuitSize n f s' := by
  obtain ⟨C, h1, h2, h3⟩ := hc
  exact ⟨C, h1, h2.trans h, h3⟩

theorem exists_min_circuit {n : ℕ} {f : (Fin n → Bool) → Bool} {s : ℕ}
    (hc : HasCircuitSize n f s) :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ s ∧ (∀ x, C.eval (List.ofFn x) = f x) ∧
      (∀ g ∈ C.gates, NOk g) ∧
      (∀ D : Circuit, FanInTwo D → (∀ x, D.eval (List.ofFn x) = f x) → C.size ≤ D.size) := by
  classical
  have hex : ∃ m, HasCircuitSize n f m := ⟨s, hc⟩
  set m := Nat.find hex with hm
  have hm_le : m ≤ s := Nat.find_min' hex hc
  have hspec : HasCircuitSize n f m := Nat.find_spec hex
  obtain ⟨C0, hfan0, hsize0, heval0⟩ := hspec
  let C : Circuit := ⟨C0.gates.map normGate, C0.output⟩
  have hnok : ∀ g ∈ C.gates, NOk g := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g' (hfan0 g' hg')
  have hfan : FanInTwo C := fun g hg => (hnok g hg).1
  have hsize : C.size ≤ m := by
    simp only [C, Circuit.size, List.length_map]
    exact hsize0
  have heval : ∀ x, C.eval (List.ofFn x) = f x := by
    intro x
    simp only [C, Circuit.eval, wires_eq, wiresFrom_norm]
    exact heval0 x
  refine ⟨C, hfan, hsize.trans hm_le, heval, hnok, ?_⟩
  intro D hDf hDe
  have hDm : m ≤ D.size := Nat.find_min' hex ⟨D, hDf, le_rfl, hDe⟩
  omega

theorem min_no_dead {n : ℕ} {f : (Fin n → Bool) → Bool} {C : Circuit}
    (hfan : FanInTwo C) (heval : ∀ x, C.eval (List.ofFn x) = f x)
    (hmin : ∀ D : Circuit, FanInTwo D → (∀ x, D.eval (List.ofFn x) = f x) → C.size ≤ D.size)
    (t : ℕ) (ht : t < C.gates.length) :
    C.output = n + t ∨ ∃ t', ∃ ht' : t' < C.gates.length, t < t' ∧ n + t ∈ (C.gates[t']).inputs := by
  by_contra h
  push_neg at h
  obtain ⟨ho, hnr⟩ := h
  let D : Circuit := ⟨del C.gates t (n + t) (n + C.gates.length), ren (n + t) (n + C.gates.length) C.output⟩
  have hDf : FanInTwo D := fanInTwo_del C.gates C.output t (n + t) (n + C.gates.length) _ hfan
  have hDe : ∀ x : Fin n → Bool, D.eval (List.ofFn x) = f x := by
    intro x
    rw [← heval x]
    have hlen : (List.ofFn x).length = n := by simp
    have h1 := del_eval C.gates C.output (List.ofFn x) t (n + C.gates.length) ht
      (Or.inr (by rw [hlen]))
      (fun g hg hmem => by
        obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hg
        rw [List.getElem_drop] at hmem
        rw [hlen] at hmem
        exact absurd hmem (hnr (t + 1 + k) (by simp at hk; omega) (by omega)))
      (fun h => absurd h (by rw [hlen]; exact ho))
    simpa [D, hlen] using h1
  have hle := hmin D hDf hDe
  have hlenD : D.size = C.size - 1 := del_length C.gates t (n + t) (n + C.gates.length) ht
  simp only [Circuit.size] at hle hlenD
  omega

theorem min_no_copy {n : ℕ} {f : (Fin n → Bool) → Bool} {C : Circuit}
    (hfan : FanInTwo C) (heval : ∀ x, C.eval (List.ofFn x) = f x)
    (hmin : ∀ D : Circuit, FanInTwo D → (∀ x, D.eval (List.ofFn x) = f x) → C.size ≤ D.size)
    (t : ℕ) (ht : t < C.gates.length) (r : ℕ) (hr : r < n + t ∨ n + C.gates.length ≤ r)
    (hcopy : ∀ x : Fin n → Bool,
      (wiresFrom C.gates (List.ofFn x)).getD (n + t) false =
        (wiresFrom C.gates (List.ofFn x)).getD r false) : False := by
  let D : Circuit := ⟨del C.gates t (n + t) r, ren (n + t) r C.output⟩
  have hDf : FanInTwo D := fanInTwo_del C.gates C.output t (n + t) r _ hfan
  have hDe : ∀ x : Fin n → Bool, D.eval (List.ofFn x) = f x := by
    intro x
    rw [← heval x]
    have hlen : (List.ofFn x).length = n := by simp
    have h1 := del_eval C.gates C.output (List.ofFn x) t r ht
      (by rw [hlen]; exact hr) (fun _ _ _ => by rw [hlen]; exact hcopy x)
      (fun _ => by rw [hlen]; exact hcopy x)
    simpa [D, hlen] using h1
  have hle := hmin D hDf hDe
  have hlenD : D.size = C.size - 1 := del_length C.gates t (n + t) r ht
  simp only [Circuit.size] at hle hlenD
  omega

theorem min_gate_shape {n : ℕ} {f : (Fin n → Bool) → Bool} {C : Circuit}
    (hfan : FanInTwo C) (heval : ∀ x, C.eval (List.ofFn x) = f x)
    (hnok : ∀ g ∈ C.gates, NOk g)
    (hmin : ∀ D : Circuit, FanInTwo D → (∀ x, D.eval (List.ofFn x) = f x) → C.size ≤ D.size)
    (hnc : ∃ x y : Fin n → Bool, f x ≠ f y)
    (t : ℕ) (ht : t < C.gates.length) :
    ((C.gates[t]).op = GateOp.not ∧ ∃ a, (C.gates[t]).inputs = [a] ∧ a < n + t) ∨
    (((C.gates[t]).op = GateOp.and ∨ (C.gates[t]).op = GateOp.or) ∧
      ∃ a b, (C.gates[t]).inputs = [a, b] ∧ a < n + t ∧ b < n + t ∧ a ≠ b) := by
  have hg := hnok _ (List.getElem_mem ht)
  have hhop : (C.gates[t]).op = GateOp.and ∨ (C.gates[t]).op = GateOp.or ∨ (C.gates[t]).op = GateOp.not := by
    simpa [NOk, Ok, Set.mem_insert_iff, Set.mem_singleton_iff] using hg.1.1
  have hgv : ∀ x : Fin n → Bool,
      (wiresFrom C.gates (List.ofFn x)).getD (n + t) false =
        (C.gates[t]).op.eval ((C.gates[t]).inputs.map fun i =>
          if i < n + t then (wiresFrom C.gates (List.ofFn x)).getD i false else false) := by
    intro x
    have := gate_value C.gates (List.ofFn x) t ht
    simpa using this
  have hbig : ∀ x : Fin n → Bool,
      (wiresFrom C.gates (List.ofFn x)).getD (n + C.gates.length) false = false := fun x =>
    List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp)
  have hconst_true : ¬ (∀ x : Fin n → Bool,
      (wiresFrom C.gates (List.ofFn x)).getD (n + t) false = true) := by
    intro htrue
    let pre := C.gates.take t
    let rest := C.gates.drop (t + 1)
    let m := n + t
    let seed : List Stat := List.ofFn (fun i : Fin m => Sum.inr i.val) ++ [Sum.inl true]
    let res := elim m rest (seed, [])
    have hinv : ∀ x : Fin n → Bool,
        Inv m (wiresFrom C.gates (List.ofFn x)) (wiresFrom pre (List.ofFn x)) res := by
      intro x
      have hsplit : C.gates = pre ++ C.gates[t] :: rest := by simp [pre, rest]
      have hpre_len : (wiresFrom pre (List.ofFn x)).length = m := by
        rw [length_wiresFrom]; simp [pre, m, Nat.min_eq_left ht.le]
      have hinit : Inv m (wiresFrom (pre ++ [C.gates[t]]) (List.ofFn x))
          (wiresFrom pre (List.ofFn x)) (seed, []) := by
        have hlen_pre1 : (wiresFrom (pre ++ [C.gates[t]]) (List.ofFn x)).length = m + 1 := by
          rw [length_wiresFrom, List.length_append, List.length_ofFn, List.length_singleton]
          simp [pre, m, Nat.min_eq_left ht.le]; omega
        refine ⟨by rw [hlen_pre1]; simp [seed], hpre_len, ?_⟩
        intro i
        have hnil : wiresFrom ([] : List Gate) (wiresFrom pre (List.ofFn x)) =
            wiresFrom pre (List.ofFn x) := rfl
        rw [hnil]
        by_cases him : i < m
        · have hget : seed.getD i (Sum.inl false) = Sum.inr i := by
            simp only [seed]
            rw [List.getD_append _ _ _ _ (by simp; exact him)]
            simp [List.getD_eq_getElem?_getD, him]
          rw [hget]
          refine ⟨by simp [Stat.Valid]; exact him, ?_⟩
          simp only [Stat.val]
          rw [wiresFrom_append]
          exact (getD_wiresFrom [C.gates[t]] (wiresFrom pre (List.ofFn x)) i (by omega)).symm
        · by_cases hieq : i = m
          · subst hieq
            have hget : seed.getD m (Sum.inl false) = Sum.inl true := by
              simp [seed]
            rw [hget]
            refine ⟨trivial, ?_⟩
            simp only [Stat.val]
            have h1 := htrue x
            have h2 : (wiresFrom C.gates (List.ofFn x)).getD m false =
                (wiresFrom (pre ++ [C.gates[t]]) (List.ofFn x)).getD m false := by
              conv_lhs => rw [hsplit, show pre ++ C.gates[t] :: rest = (pre ++ [C.gates[t]]) ++ rest by simp]
              rw [wiresFrom_append, getD_wiresFrom _ _ _ (by rw [hlen_pre1]; omega)]
            rw [← h2, h1]
          · have hget : seed.getD i (Sum.inl false) = Sum.inl false := by
              rw [List.getD_eq_default _ _ (by simp [seed]; omega)]
            rw [hget, List.getD_eq_default _ _ (by rw [hlen_pre1]; omega)]
            exact ⟨trivial, rfl⟩
      have hrest_ok : ∀ g ∈ rest, Ok g := fun g hg => hfan g (List.mem_of_mem_drop hg)
      have := inv_elim m rest hrest_ok _ _ _ hinit
      have hcat : wiresFrom rest (wiresFrom (pre ++ [C.gates[t]]) (List.ofFn x)) =
          wiresFrom C.gates (List.ofFn x) := by
        rw [← wiresFrom_append]
        congr 1
        simp [pre, rest]
      rwa [hcat] at this
    cases hout : res.1.getD C.output (Sum.inl false) with
    | inl c =>
      obtain ⟨x, y, hxy⟩ := hnc
      have hx := (hinv x).2.2 C.output
      have hy := (hinv y).2.2 C.output
      rw [hout] at hx hy
      simp only [Stat.val] at hx hy
      apply hxy
      rw [← heval x, ← heval y]
      simp only [Circuit.eval, wires_eq, ← hx.2, ← hy.2]
    | inr o' =>
      let D : Circuit := ⟨pre ++ res.2, o'⟩
      have hDf : FanInTwo D := by
        intro g hg
        simp only [D, List.mem_append] at hg
        rcases hg with hg | hg
        · exact hfan g (List.mem_of_mem_take hg)
        · exact elim_ok m rest (seed, []) (by simp) g hg
      have hDe : ∀ x, D.eval (List.ofFn x) = f x := by
        intro x
        rw [← heval x]
        have hx := (hinv x).2.2 C.output
        rw [hout] at hx
        simp only [D, Circuit.eval, wires_eq, wiresFrom_append, Stat.val] at hx ⊢
        exact hx.2
      have hle := hmin D hDf hDe
      obtain ⟨_, t2, _, h2, _, hl2⟩ := elim_prefix m rest (seed, [])
      have hlenD : D.size ≤ C.size - 1 := by
        have hDsz : D.size = pre.length + res.2.length := by
          simp [D, Circuit.size]
        have hres2 : res.2.length = t2.length := by
          change (elim m rest (seed, [])).2.length = t2.length
          rw [h2]; simp
        have hpre_l : pre.length = t := by simp [pre, Nat.min_eq_left ht.le]
        have hrest_l : rest.length = C.gates.length - (t + 1) := by simp [rest]
        have hCsz : C.size = C.gates.length := rfl
        omega
      simp only [Circuit.size] at hle hlenD
      omega
  rcases hhop with hop | hop | hop
  · rcases hl : (C.gates[t]).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · exfalso; apply hconst_true; intro x; rw [hgv x, hl, hop]; rfl
    · exfalso
      by_cases ha : a < n + t
      · exact min_no_copy hfan heval hmin t ht a (Or.inl ha) (fun x => by
          rw [hgv x, hl, hop]; simp [GateOp.eval, ha])
      · exact min_no_copy hfan heval hmin t ht (n + C.gates.length) (Or.inr le_rfl) (fun x => by
          rw [hgv x, hl, hop, hbig x]; simp [GateOp.eval, ha])
    · by_cases ha : a < n + t
      · by_cases hb : b < n + t
        · by_cases hab : a = b
          · subst hab
            exfalso
            exact min_no_copy hfan heval hmin t ht a (Or.inl ha) (fun x => by
              rw [hgv x, hl, hop]; simp [GateOp.eval, ha])
          · exact Or.inr ⟨Or.inl hop, a, b, rfl, ha, hb, hab⟩
        · exfalso
          exact min_no_copy hfan heval hmin t ht (n + C.gates.length) (Or.inr le_rfl) (fun x => by
            rw [hgv x, hl, hop, hbig x]; simp [GateOp.eval, hb])
      · exfalso
        exact min_no_copy hfan heval hmin t ht (n + C.gates.length) (Or.inr le_rfl) (fun x => by
          rw [hgv x, hl, hop, hbig x]; simp [GateOp.eval, ha])
    · have := hg.1.2; rw [hl] at this; simp at this
  · rcases hl : (C.gates[t]).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · exfalso
      exact min_no_copy hfan heval hmin t ht (n + C.gates.length) (Or.inr le_rfl) (fun x => by
        rw [hgv x, hl, hop, hbig x]; rfl)
    · exfalso
      by_cases ha : a < n + t
      · exact min_no_copy hfan heval hmin t ht a (Or.inl ha) (fun x => by
          rw [hgv x, hl, hop]; simp [GateOp.eval, ha])
      · exact min_no_copy hfan heval hmin t ht (n + C.gates.length) (Or.inr le_rfl) (fun x => by
          rw [hgv x, hl, hop, hbig x]; simp [GateOp.eval, ha])
    · by_cases ha : a < n + t
      · by_cases hb : b < n + t
        · by_cases hab : a = b
          · subst hab
            exfalso
            exact min_no_copy hfan heval hmin t ht a (Or.inl ha) (fun x => by
              rw [hgv x, hl, hop]; simp [GateOp.eval, ha])
          · exact Or.inr ⟨Or.inr hop, a, b, rfl, ha, hb, hab⟩
        · exfalso
          exact min_no_copy hfan heval hmin t ht a (Or.inl ha) (fun x => by
            rw [hgv x, hl, hop]; simp [GateOp.eval, ha, hb])
      · by_cases hb : b < n + t
        · exfalso
          exact min_no_copy hfan heval hmin t ht b (Or.inl hb) (fun x => by
            rw [hgv x, hl, hop]; simp [GateOp.eval, ha, hb])
        · exfalso
          exact min_no_copy hfan heval hmin t ht (n + C.gates.length) (Or.inr le_rfl) (fun x => by
            rw [hgv x, hl, hop, hbig x]; simp [GateOp.eval, ha, hb])
    · have := hg.1.2; rw [hl] at this; simp at this
  · rcases hl : (C.gates[t]).inputs with _ | ⟨a, l⟩
    · exfalso; apply hconst_true; intro x; rw [hgv x, hl, hop]; rfl
    · have hl0 : l = [] := by
        have := hg.2 hop; rw [hl] at this; simp only [List.length_cons] at this
        exact List.eq_nil_of_length_eq_zero (by omega)
      subst hl0
      by_cases ha : a < n + t
      · exact Or.inl ⟨hop, a, rfl, ha⟩
      · exfalso; apply hconst_true; intro x; rw [hgv x, hl, hop]; simp [GateOp.eval, ha]

theorem two_gate_elim {n : ℕ} (f : (Fin n → Bool) → Bool) (p : Fin n) (s : ℕ)
    (hdep : ∃ x : Fin n → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc0 : ∃ x y : Fin n → Bool, f (Function.update x p false) ≠ f (Function.update y p false))
    (hnc1 : ∃ x y : Fin n → Bool, f (Function.update x p true) ≠ f (Function.update y p true))
    (hs : HasCircuitSize n f s) :
    2 ≤ s ∧ (HasCircuitSize n (fun x => f (Function.update x p false)) (s - 2) ∨
      HasCircuitSize n (fun x => f (Function.update x p true)) (s - 2)) := by
  obtain ⟨C, hfan, hsize, heval, hnok, hmin⟩ := exists_min_circuit hs
  have hncf : ∃ x y, f x ≠ f y := by
    obtain ⟨x, hx⟩ := hdep; exact ⟨_, _, hx⟩
  have hdepC : ∃ x, C.eval (List.ofFn (Function.update x p (!x p))) ≠ C.eval (List.ofFn x) := by
    obtain ⟨x, hx⟩ := hdep; exact ⟨x, by rwa [heval, heval]⟩
  have hnc0C : ∃ x y, C.eval (List.ofFn (Function.update x p false)) ≠
      C.eval (List.ofFn (Function.update y p false)) := by
    obtain ⟨x, y, hxy⟩ := hnc0; exact ⟨x, y, by rwa [heval, heval]⟩
  have hnc1C : ∃ x y, C.eval (List.ofFn (Function.update x p true)) ≠
      C.eval (List.ofFn (Function.update y p true)) := by
    obtain ⟨x, y, hxy⟩ := hnc1; exact ⟨x, y, by rwa [heval, heval]⟩
  have hmap : C.gates.map normGate = C.gates := by
    apply List.ext_getElem (by simp)
    intro i hi _
    rw [List.getElem_map]
    have hg := hnok C.gates[i] (List.getElem_mem (by simpa using hi))
    cases hgi : C.gates[i] with
    | mk op ins =>
      cases op <;> simp [normGate]
      have hlen := hg.2 (by simp [hgi])
      simp [hgi] at hlen
      exact hlen
  rcases has_reader_of_dep C p hdepC with ho | ⟨t1, ht1, hmem1⟩
  · exfalso
    obtain ⟨x, y, hxy⟩ := hnc0C
    apply hxy
    simp only [Circuit.eval, wires_eq, ho]
    rw [getD_wiresFrom _ _ _ (by simp), getD_wiresFrom _ _ _ (by simp)]
    simp
  have hmem1 : p.val ∈ (C.gates[t1]).inputs := by
    simpa [hmap] using hmem1
  have hseed : ∀ (b : Bool) (t : ℕ),
      (elim n (C.gates.take t) (seedInput n p b, [])).1.getD p.val (Sum.inl false) = Sum.inl b := by
    intro b t
    obtain ⟨t1, _, h1, _, _, _⟩ := elim_prefix n (C.gates.take t) (seedInput n p b, [])
    rw [h1, List.getD_append _ _ _ _ (by simp [seedInput])]
    simp [seedInput, p.isLt]
  by_cases h2 : ∃ t2, ∃ ht2 : t2 < C.gates.length, t2 ≠ t1 ∧ p.val ∈ (C.gates[t2]).inputs
  · obtain ⟨t2, ht2, hne, hmem2⟩ := h2
    have hcard : ({t1, t2} : Finset ℕ).card = 2 := Finset.card_pair hne.symm
    have h2le : 2 ≤ C.size := by
      simp only [Circuit.size]
      have hsub : ({t1, t2} : Finset ℕ) ⊆ Finset.range C.gates.length := by
        intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl <;> exact Finset.mem_range.2 (by assumption)
      have := Finset.card_le_card hsub
      rw [hcard, Finset.card_range] at this
      exact this
    have hres := elim_const_of_input_mem C hfan p false hnc0C {t1, t2} (by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact ⟨ht1, p.val, by simpa [hmap] using hmem1, false, by simpa [hmap] using hseed false t⟩
      · exact ⟨ht2, p.val, by simpa [hmap] using hmem2, false, by simpa [hmap] using hseed false t⟩)
    rw [hcard] at hres
    refine ⟨by omega, Or.inl ?_⟩
    obtain ⟨D, hDf, hDs, hDe⟩ := hres
    exact ⟨D, hDf, by omega, fun x => by dsimp only; rw [hDe x]; exact heval _⟩
  · have hshape := min_gate_shape hfan heval hnok hmin hncf t1 ht1
    have hconst_elim : ∀ (b c : Bool),
        (elim n (C.gates.take (t1 + 1)) (seedInput n p b, [])).1.getD (n + t1) (Sum.inl false) =
          Sum.inl c →
        (∃ x y, C.eval (List.ofFn (Function.update x p b)) ≠
          C.eval (List.ofFn (Function.update y p b))) →
        2 ≤ s ∧ HasCircuitSize n (fun x => f (Function.update x p b)) (s - 2) := by
      intro b c hc hncb
      have hst_all : ∀ t' > t1,
          (elim n (C.gates.take t') (seedInput n p b, [])).1.getD (n + t1) (Sum.inl false) =
            Sum.inl c := by
        intro t' ht'
        have hlen : (elim n (C.gates.take (t1 + 1)) (seedInput n p b, [])).1.length = n + (t1 + 1) := by
          obtain ⟨l1, _, h1, _, hl1, _⟩ := elim_prefix n (C.gates.take (t1 + 1)) (seedInput n p b, [])
          rw [h1, List.length_append, hl1, List.length_take, Nat.min_eq_left (by omega)]
          simp [seedInput]
        have htake : C.gates.take t' = C.gates.take (t1 + 1) ++ (C.gates.take t').drop (t1 + 1) := by
          conv_lhs => rw [← List.take_append_drop (t1 + 1) (C.gates.take t'), List.take_take, Nat.min_eq_left (by omega)]
        rw [htake, elim_append]
        obtain ⟨l2, _, h2, _, _, _⟩ := elim_prefix n ((C.gates.take t').drop (t1 + 1)) _
        rw [h2, List.getD_append _ _ _ _ (by omega), hc]
      rcases min_no_dead hfan heval hmin t1 ht1 with ho | ⟨t2, ht2, hlt, hmem2⟩
      · exfalso
        obtain ⟨x, y, hxy⟩ := hncb
        have hx := inv_elim n C.gates (fun g hg => (hnok g hg).1) _ _ _ (seedInput_inv p b x)
        have hy := inv_elim n C.gates (fun g hg => (hnok g hg).1) _ _ _ (seedInput_inv p b y)
        have hce : (elim n C.gates (seedInput n p b, [])).1.getD (n + t1) (Sum.inl false) = Sum.inl c := by
          have h1 := hst_all C.gates.length ht1
          rwa [List.take_of_length_le le_rfl] at h1
        have hx1 := (hx.2.2 (n + t1)).2
        have hy1 := (hy.2.2 (n + t1)).2
        rw [hce] at hx1 hy1
        apply hxy
        simp only [Circuit.eval, wires_eq, ho, ← hx1, ← hy1, Stat.val]
      · have hne : t1 ≠ t2 := by omega
        have hcard : ({t1, t2} : Finset ℕ).card = 2 := Finset.card_pair hne
        have h2le : 2 ≤ C.size := by simp [Circuit.size]; omega
        have hres := elim_const_of_input_mem C hfan p b hncb {t1, t2} (by
          intro t ht
          simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl
          · exact ⟨ht1, p.val, by simpa [hmap] using hmem1, b, by simpa [hmap] using hseed b t⟩
          · exact ⟨ht2, n + t1, by simpa [hmap] using hmem2, c, by simpa [hmap] using hst_all t hlt⟩)
        rw [hcard] at hres
        refine ⟨by omega, ?_⟩
        obtain ⟨D, hDf, hDs, hDe⟩ := hres
        exact ⟨D, hDf, by omega, fun x => by dsimp only; rw [hDe x]; exact heval _⟩
    have hstep_eq : ∀ (b : Bool),
        (elim n (C.gates.take (t1 + 1)) (seedInput n p b, [])).1.getD (n + t1) (Sum.inl false) =
          (simplify (C.gates[t1]).op (n + (elim n (C.gates.take t1) (seedInput n p b, [])).2.length)
            ((C.gates[t1]).inputs.map fun i =>
              (elim n (C.gates.take t1) (seedInput n p b, [])).1.getD i (Sum.inl false))).2 := by
      intro b
      rw [List.take_succ_eq_append_getElem ht1, elim_append]
      set st0 := elim n (C.gates.take t1) (seedInput n p b, []) with hst0
      have hlen : st0.1.length = n + t1 := by
        obtain ⟨l1, _, h1, _, hl1, _⟩ := elim_prefix n (C.gates.take t1) (seedInput n p b, [])
        rw [hst0, h1, List.length_append, hl1, List.length_take, Nat.min_eq_left ht1.le]
        simp [seedInput]
      change (st0.1 ++ [(simplify (C.gates[t1]).op (n + st0.2.length)
        ((C.gates[t1]).inputs.map fun i => st0.1.getD i (Sum.inl false))).2]).getD (n + t1) (Sum.inl false) = _
      rw [← hlen, getD_snoc_eq]
    rcases hshape with ⟨hop, a, hl, ha⟩ | ⟨hop | hop, a, b, hl, ha, hb, hab⟩
    · have hap : a = p.val := by rw [hl] at hmem1; simpa [eq_comm] using hmem1
      subst hap
      have ⟨h2s, hc0⟩ := hconst_elim false true (by
        rw [hstep_eq, hop, hl]
        simp only [List.map_cons, List.map_nil, hseed, simplify, simpNot]; rfl) hnc0C
      exact ⟨h2s, Or.inl hc0⟩
    · rw [hl] at hmem1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem1
      rcases hmem1 with rfl | rfl
      · have ⟨h2s, hc0⟩ := hconst_elim false false (by
          rw [hstep_eq, hop, hl]
          simp only [List.map_cons, List.map_nil, hseed, simplify]
          cases (elim n (C.gates.take t1) (seedInput n p false, [])).1.getD b (Sum.inl false) <;>
            simp [simpAnd]) hnc0C
        exact ⟨h2s, Or.inl hc0⟩
      · have ⟨h2s, hc0⟩ := hconst_elim false false (by
          rw [hstep_eq, hop, hl]
          simp only [List.map_cons, List.map_nil, hseed, simplify]
          cases (elim n (C.gates.take t1) (seedInput n p false, [])).1.getD a (Sum.inl false) <;>
            simp [simpAnd]) hnc0C
        exact ⟨h2s, Or.inl hc0⟩
    · rw [hl] at hmem1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem1
      rcases hmem1 with rfl | rfl
      · have ⟨h2s, hc1⟩ := hconst_elim true true (by
          rw [hstep_eq, hop, hl]
          simp only [List.map_cons, List.map_nil, hseed, simplify]
          cases (elim n (C.gates.take t1) (seedInput n p true, [])).1.getD b (Sum.inl false) <;>
            simp [simpOr]) hnc1C
        exact ⟨h2s, Or.inr hc1⟩
      · have ⟨h2s, hc1⟩ := hconst_elim true true (by
          rw [hstep_eq, hop, hl]
          simp only [List.map_cons, List.map_nil, hseed, simplify]
          cases (elim n (C.gates.take t1) (seedInput n p true, [])).1.getD a (Sum.inl false) <;>
            simp [simpOr]) hnc1C
        exact ⟨h2s, Or.inr hc1⟩

noncomputable def graphFun {n : ℕ} (A : Finset (Fin n)) (E : SimpleGraph (Fin n))
    (x : Fin n → Bool) : Bool := by
  classical
  exact decide ((∃ a ∈ A, x a = true) ∨ (∃ u v : Fin n, E.Adj u v ∧ x u = true ∧ x v = true))

theorem graphFun_eq_true {n : ℕ} (A : Finset (Fin n)) (E : SimpleGraph (Fin n)) (x : Fin n → Bool) :
    graphFun A E x = true ↔
      (∃ a ∈ A, x a = true) ∨ (∃ u v : Fin n, E.Adj u v ∧ x u = true ∧ x v = true) := by
  classical
  simp [graphFun]

def IsMatching {n : ℕ} (E : SimpleGraph (Fin n)) (M : Finset (Sym2 (Fin n))) : Prop :=
  (∀ e ∈ M, e ∈ E.edgeSet) ∧
  (∀ e1 ∈ M, ∀ e2 ∈ M, e1 ≠ e2 → ∀ v : Fin n, ¬ (v ∈ e1 ∧ v ∈ e2))

def isAdjPath {n : ℕ} (E : SimpleGraph (Fin n)) : List (Fin n) → Prop
  | [] => True
  | [_] => True
  | u :: v :: rest => E.Adj u v ∧ isAdjPath E (v :: rest)

theorem walkOfPath {n : ℕ} (E : SimpleGraph (Fin n)) :
    ∀ (L : List (Fin n)) (u w : Fin n),
      L.head? = some u → L.getLast? = some w → isAdjPath E L →
      ∃ p : E.Walk u w, p.support = L := by
  intro L
  induction L with
  | nil => intro u w h; simp at h
  | cons a t ih =>
    intro u w hh hl hp
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    cases t with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hl
      subst hl
      exact ⟨SimpleGraph.Walk.nil, rfl⟩
    | cons b t' =>
      obtain ⟨hab, hpt⟩ := hp
      have hl' : (b :: t').getLast? = some w := by
        simpa [List.getLast?_cons_cons] using hl
      obtain ⟨p, hp_supp⟩ := ih b w rfl hl' hpt
      exact ⟨SimpleGraph.Walk.cons hab p, by simp [hp_supp]⟩

theorem prefix_to_mem {α : Type} [DecidableEq α] :
    ∀ (L : List α) (w : α), w ∈ L →
      ∃ p : List α, (∃ s : List α, L = p ++ s) ∧ p.getLast? = some w ∧ p.head? = L.head? := by
  intro L
  induction L with
  | nil => intro w hw; simp at hw
  | cons a t ih =>
    intro w hw
    by_cases hwa : w = a
    · subst hwa
      exact ⟨[w], ⟨t, rfl⟩, rfl, rfl⟩
    · have hwt : w ∈ t := by
        simp only [List.mem_cons] at hw
        exact hw.resolve_left hwa
      obtain ⟨p, ⟨s, hts⟩, hlast, hhead⟩ := ih w hwt
      refine ⟨a :: p, ⟨s, by simp [hts]⟩, ?_, rfl⟩
      cases p with
      | nil => simp at hlast
      | cons b p' => simpa [List.getLast?_cons_cons] using hlast

theorem isAdjPath_of_prefix {n : ℕ} (E : SimpleGraph (Fin n)) :
    ∀ (p s : List (Fin n)), isAdjPath E (p ++ s) → isAdjPath E p := by
  intro p
  induction p with
  | nil => intro _ _; trivial
  | cons a t ih =>
    intro s h
    cases t with
    | nil => trivial
    | cons b t' =>
      simp only [List.cons_append] at h
      exact ⟨h.1, ih s h.2⟩

theorem acyclic_no_chord {n : ℕ} (E : SimpleGraph (Fin n)) (hacyc : E.IsAcyclic)
    (u v : Fin n) (rest : List (Fin n)) (hnodup : (u :: v :: rest).Nodup)
    (hpath : isAdjPath E (u :: v :: rest)) (w : Fin n) (hw : w ∈ rest) (huw : E.Adj u w) :
    False := by
  obtain ⟨p, ⟨s, hps⟩, hlast, hhead⟩ := prefix_to_mem (v :: rest) w (List.mem_cons_of_mem _ hw)
  have hup_nodup : (u :: p).Nodup := by
    have h1 : (u :: (p ++ s)).Nodup := hps ▸ hnodup
    exact h1.sublist (List.Sublist.cons₂ u (List.sublist_append_left p s))
  have hup_path : isAdjPath E (u :: p) := by
    have h1 : isAdjPath E ((u :: p) ++ s) := by simpa [hps] using hpath
    exact isAdjPath_of_prefix E (u :: p) s h1
  have hne_vw : v ≠ w := by
    have hvn : v ∉ rest := (List.nodup_cons.1 (List.nodup_cons.1 hnodup).2).1
    intro e; subst e; exact hvn hw
  obtain ⟨q, hq_supp⟩ := walkOfPath E (u :: p) u w rfl (by
    cases p with
    | nil => simp at hlast
    | cons b p' => simpa [List.getLast?_cons_cons] using hlast) hup_path
  have hq_path : q.IsPath := by
    rw [SimpleGraph.Walk.isPath_def, hq_supp]
    exact hup_nodup
  have hp_len : 2 ≤ p.length := by
    cases p with
    | nil => simp at hlast
    | cons b p' =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      cases p' with
      | nil =>
        simp only [List.getLast?_singleton, Option.some.injEq] at hlast
        exact absurd hlast hne_vw
      | cons c p'' => simp
  have hq_len : 2 ≤ q.length := by
    have hlen := q.length_support
    rw [hq_supp] at hlen
    simp only [List.length_cons] at hlen
    omega
  have hnotmem : s(w, u) ∉ q.edges := by
    cases q with
    | nil => simp at hq_len
    | cons h1 q1 =>
      rename_i x
      simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]
      rintro (he | he)
      · rw [Sym2.eq_iff] at he
        rcases he with ⟨hwu, _⟩ | ⟨hww, _⟩
        · exact E.ne_of_adj h1 (by subst hwu; exact (E.ne_of_adj huw rfl).elim)
        · subst hww
          simp only [SimpleGraph.Walk.support_cons, List.cons.injEq] at hq_supp
          cases p with
          | nil => simp at hp_len
          | cons b p' =>
            simp only [List.head?_cons, Option.some.injEq] at hhead
            subst hhead
            have hbx : b = w := by
              have hhead_q1 : q1.support.head? = some w := by cases q1 <;> rfl
              rw [hq_supp.2] at hhead_q1
              simp at hhead_q1
              exact hhead_q1
            exact hne_vw hbx
      · have hu_in : u ∈ q1.support := SimpleGraph.Walk.snd_mem_support_of_mem_edges q1 he
        simp only [SimpleGraph.Walk.support_cons] at hq_supp
        rw [← hq_supp] at hup_nodup
        exact (List.nodup_cons.1 hup_nodup).1 hu_in
  have hcyc : (SimpleGraph.Walk.cons huw.symm q).IsCycle := by
    rw [SimpleGraph.Walk.isCycle_def]
    refine ⟨⟨?_⟩, by simp, ?_⟩
    · rw [SimpleGraph.Walk.edges_cons, List.nodup_cons]
      exact ⟨hnotmem, hq_path.edges_nodup⟩
    · simpa [SimpleGraph.Walk.support_cons, hq_supp] using hup_nodup
  exact hacyc _ hcyc

theorem exists_longest_path {n : ℕ} (E : SimpleGraph (Fin n)) (u0 v0 : Fin n) (h0 : E.Adj u0 v0) :
    ∃ L : List (Fin n), L.Nodup ∧ isAdjPath E L ∧ 2 ≤ L.length ∧
      ∀ L' : List (Fin n), L'.Nodup → isAdjPath E L' → L'.length ≤ L.length := by
  classical
  let P (k : ℕ) : Prop := ∃ L : List (Fin n), L.Nodup ∧ isAdjPath E L ∧ L.length = k
  have hbound : ∀ k, P k → k ≤ n := by
    rintro k ⟨L, hnd, _, rfl⟩
    have h1 := L.toFinset_card_of_nodup hnd
    have h2 : L.toFinset.card ≤ Fintype.card (Fin n) := Finset.card_le_univ _
    rw [Fintype.card_fin] at h2
    omega
  have h2 : P 2 := ⟨[u0, v0], by simp [E.ne_of_adj h0], ⟨h0, trivial⟩, rfl⟩
  let S := (Finset.range (n + 1)).filter P
  have hne : S.Nonempty := ⟨2, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by have := hbound 2 h2; omega), h2⟩⟩
  obtain ⟨k, hkS, hkmax⟩ := Finset.exists_max_image S id hne
  obtain ⟨_, L, hnd, hp, hlen⟩ := Finset.mem_filter.1 hkS
  have hk2 : 2 ≤ k := hkmax 2 (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by have := hbound 2 h2; omega), h2⟩)
  refine ⟨L, hnd, hp, by omega, ?_⟩
  intro L' hnd' hp'
  have hle : L'.length ≤ n := hbound L'.length ⟨L', hnd', hp', rfl⟩
  have hmem : L'.length ∈ S := Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), ⟨L', hnd', hp', rfl⟩⟩
  have := hkmax L'.length hmem
  dsimp only [id] at this
  omega

theorem matching_card_erase {n : ℕ} (M : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) :
    M.card ≤ (M.erase e).card + 1 := by
  by_cases he : e ∈ M
  · have := Finset.card_erase_add_one he; omega
  · rw [Finset.erase_eq_of_notMem he]; omega

theorem matching_card_erase_two_incident {n : ℕ} (E : SimpleGraph (Fin n))
    (M : Finset (Sym2 (Fin n))) (hM : IsMatching E M) (v a b : Fin n) :
    M.card ≤ ((M.erase s(v, a)).erase s(v, b)).card + 1 := by
  by_cases ha : s(v, a) ∈ M
  · by_cases hb : s(v, b) ∈ M
    · by_cases hab : s(v, a) = s(v, b)
      · rw [hab, Finset.erase_idem]
        have := Finset.card_erase_add_one hb; omega
      · exfalso
        exact hM.2 s(v, a) ha s(v, b) hb hab v ⟨Sym2.mem_mk_left v a, Sym2.mem_mk_left v b⟩
    · rw [Finset.erase_eq_of_notMem (fun h => hb (Finset.mem_of_mem_erase h))]
      have := Finset.card_erase_add_one ha; omega
  · rw [Finset.erase_eq_of_notMem ha]
    exact matching_card_erase M s(v, b)

noncomputable def edgesOf {n : ℕ} (E : SimpleGraph (Fin n)) : Finset (Sym2 (Fin n)) := by
  classical
  exact E.edgeFinset

theorem mem_edgesOf {n : ℕ} (E : SimpleGraph (Fin n)) (e : Sym2 (Fin n)) :
    e ∈ edgesOf E ↔ e ∈ E.edgeSet := by
  classical
  simp [edgesOf]

theorem forest_bound {n : ℕ} :
    ∀ (K : ℕ) (A : Finset (Fin n)) (E : SimpleGraph (Fin n)) (M : Finset (Sym2 (Fin n))) (s : ℕ),
      A.card + 2 * (edgesOf E).card = K →
      E.IsAcyclic →
      (∀ a ∈ A, ∀ v, ¬ E.Adj a v) →
      IsMatching E M →
      1 ≤ A.card + (edgesOf E).card →
      HasCircuitSize n (graphFun A E) s →
      A.card + (edgesOf E).card + M.card - 1 ≤ s := by
  intro K
  induction K using Nat.strong_induction_on with
  | ind K ih =>
    intro A E M s hK hacyc hdisj hM hne hs
    by_cases hE0 : (edgesOf E).card = 0
    · have hEempty : edgesOf E = ∅ := Finset.card_eq_zero.1 hE0
      have hM0 : M.card = 0 := by
        apply Finset.card_eq_zero.2
        ext e; simp only [Finset.notMem_empty, iff_false]
        intro he
        have : e ∈ edgesOf E := (mem_edgesOf E e).2 (hM.1 e he)
        rw [hEempty] at this; exact Finset.notMem_empty _ this
      have hdep : ∀ a ∈ A, ∃ x : Fin n → Bool,
          graphFun A E (Function.update x a (!x a)) ≠ graphFun A E x := by
        intro a ha
        refine ⟨fun _ => false, ?_⟩
        intro heq
        have h1 : graphFun A E (Function.update (fun _ => false) a true) = true := by
          rw [graphFun_eq_true]; exact Or.inl ⟨a, ha, by simp⟩
        have h2 : graphFun A E (fun _ => false) = false := by
          cases hf : graphFun A E (fun _ => false)
          · rfl
          · rw [graphFun_eq_true] at hf
            rcases hf with ⟨_, _, h⟩ | ⟨_, _, _, h, _⟩ <;> simp at h
        simp [h1, h2] at heq
      have hdl := dep_lower_finset A (graphFun A E) hdep s hs
      omega
    · by_cases hA : A.Nonempty
      · obtain ⟨a, ha⟩ := hA
        have hdep : ∃ x : Fin n → Bool,
            graphFun A E (Function.update x a (!x a)) ≠ graphFun A E x := by
          refine ⟨fun _ => false, ?_⟩
          intro heq
          have h1 : graphFun A E (Function.update (fun _ => false) a true) = true := by
            rw [graphFun_eq_true]; exact Or.inl ⟨a, ha, by simp⟩
          have h2 : graphFun A E (fun _ => false) = false := by
            cases hf : graphFun A E (fun _ => false)
            · rfl
            · rw [graphFun_eq_true] at hf
              rcases hf with ⟨_, _, h⟩ | ⟨_, _, _, h, _⟩ <;> simp at h
          simp [h1, h2] at heq
        have hupd : (fun x => graphFun A E (Function.update x a false)) =
            graphFun (A.erase a) E := by
          funext x
          apply Bool.eq_iff_iff.2
          rw [graphFun_eq_true, graphFun_eq_true]
          constructor
          · rintro (⟨b, hb, hxb⟩ | ⟨u, v, huv, hxu, hxv⟩)
            · by_cases hba : b = a
              · subst hba; simp at hxb
              · exact Or.inl ⟨b, Finset.mem_erase.2 ⟨hba, hb⟩, by rwa [Function.update_of_ne hba] at hxb⟩
            · have hua : u ≠ a := fun e => hdisj a ha v (e ▸ huv)
              have hva : v ≠ a := fun e => hdisj a ha u (e ▸ huv.symm)
              rw [Function.update_of_ne hua] at hxu
              rw [Function.update_of_ne hva] at hxv
              exact Or.inr ⟨u, v, huv, hxu, hxv⟩
          · rintro (⟨b, hb, hxb⟩ | ⟨u, v, huv, hxu, hxv⟩)
            · obtain ⟨hba, hbA⟩ := Finset.mem_erase.1 hb
              exact Or.inl ⟨b, hbA, by rwa [Function.update_of_ne hba]⟩
            · have hua : u ≠ a := fun e => hdisj a ha v (e ▸ huv)
              have hva : v ≠ a := fun e => hdisj a ha u (e ▸ huv.symm)
              exact Or.inr ⟨u, v, huv, by rwa [Function.update_of_ne hua], by rwa [Function.update_of_ne hva]⟩
        obtain ⟨e0, he0⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero hE0)
        induction e0 using Sym2.ind with
        | _ u0 v0 =>
          have huv0 : E.Adj u0 v0 := (mem_edgesOf E _).1 he0
          have hnc : ∃ x y : Fin n → Bool,
              graphFun A E (Function.update x a false) ≠ graphFun A E (Function.update y a false) := by
            refine ⟨fun _ => false, fun i => decide (i = u0 ∨ i = v0), ?_⟩
            have hupd' := congrFun hupd
            rw [hupd', hupd']
            have h0 : graphFun (A.erase a) E (fun _ => false) = false := by
              cases hf : graphFun (A.erase a) E (fun _ => false)
              · rfl
              · rw [graphFun_eq_true] at hf
                rcases hf with ⟨_, _, h⟩ | ⟨_, _, _, h, _⟩ <;> simp at h
            have h1 : graphFun (A.erase a) E (fun i => decide (i = u0 ∨ i = v0)) = true := by
              rw [graphFun_eq_true]
              exact Or.inr ⟨u0, v0, huv0, by simp, by simp⟩
            rw [h0, h1]; decide
          obtain ⟨hs1, hred⟩ := one_gate_elim (graphFun A E) a false s hdep hnc hs
          rw [hupd] at hred
          have hca : (A.erase a).card + 1 = A.card := Finset.card_erase_add_one ha
          have hrec := ih ((A.erase a).card + 2 * (edgesOf E).card) (by omega)
            (A.erase a) E M (s - 1) rfl hacyc
            (fun b hb => hdisj b (Finset.mem_of_mem_erase hb)) hM (by omega) hred
          omega
      · have hAempty : A = ∅ := Finset.not_nonempty_iff_eq_empty.1 hA
        subst hAempty
        have hEpos : 1 ≤ (edgesOf E).card := by omega
        have hdel_v : ∀ (v : Fin n),
            (fun x => graphFun ∅ E (Function.update x v false)) =
              graphFun ∅ (E.deleteEdges {e | v ∈ e}) := by
          intro v; funext x
          apply Bool.eq_iff_iff.2
          rw [graphFun_eq_true, graphFun_eq_true]
          simp only [Finset.notMem_empty, false_and, exists_false, false_or,
            SimpleGraph.deleteEdges_adj, Set.mem_setOf_eq, Sym2.mem_iff, not_or]
          constructor
          · rintro ⟨a, b, hab, ha, hb⟩
            have hav : a ≠ v := by intro e; subst e; simp at ha
            have hbv : b ≠ v := by intro e; subst e; simp at hb
            rw [Function.update_of_ne hav] at ha
            rw [Function.update_of_ne hbv] at hb
            exact ⟨a, b, ⟨hab, hav.symm, hbv.symm⟩, ha, hb⟩
          · rintro ⟨a, b, ⟨hab, hav, hbv⟩, ha, hb⟩
            exact ⟨a, b, hab, by rwa [Function.update_of_ne (Ne.symm hav)], by rwa [Function.update_of_ne (Ne.symm hbv)]⟩
        by_cases hleaf_free : ∃ v u : Fin n, E.Adj u v ∧ (∀ w, E.Adj v w → w = u) ∧ s(u, v) ∉ M
        · obtain ⟨v, u, huv, huniq, hnotM⟩ := hleaf_free
          by_cases hE1 : (edgesOf E).card = 1
          · have hM0 : M.card = 0 := by
              apply Finset.card_eq_zero.2
              ext e; simp only [Finset.notMem_empty, iff_false]
              intro he
              have heE : e ∈ edgesOf E := (mem_edgesOf E e).2 (hM.1 e he)
              have huvE : s(u, v) ∈ edgesOf E := (mem_edgesOf E _).2 huv
              have heq : e = s(u, v) := Finset.card_le_one.1 (by omega) e heE s(u, v) huvE
              exact hnotM (heq ▸ he)
            simp [hE1, hM0]
          · let E' := E.deleteEdges {e | v ∈ e}
            have hE'sub : E' ≤ E := SimpleGraph.deleteEdges_le _
            have hE'acyc : E'.IsAcyclic := fun x c hc => hacyc _ (hc.map (f := SimpleGraph.Hom.ofLE hE'sub) Function.injective_id)
            have hE'edges : edgesOf E' = (edgesOf E).erase s(u, v) := by
              ext e
              induction e using Sym2.ind with
              | _ a b =>
                simp only [mem_edgesOf, E', SimpleGraph.edgeSet_deleteEdges,
                  Set.mem_diff, Set.mem_setOf_eq, Finset.mem_erase, SimpleGraph.mem_edgeSet]
                constructor
                · rintro ⟨hab, hvnot⟩
                  refine ⟨?_, hab⟩
                  intro heq
                  rw [heq] at hvnot
                  exact hvnot (Sym2.mem_mk_right u v)
                · rintro ⟨hne', hab⟩
                  refine ⟨hab, ?_⟩
                  intro hvab
                  rw [Sym2.mem_iff] at hvab
                  rcases hvab with rfl | rfl
                  · have hbu := huniq b hab
                    subst hbu
                    exact hne' (Sym2.eq_swap)
                  · have hau := huniq a hab.symm
                    subst hau
                    exact hne' rfl
            have hE'card : (edgesOf E').card + 1 = (edgesOf E).card := by
              rw [hE'edges]
              exact Finset.card_erase_add_one ((mem_edgesOf E _).2 huv)
            have hM' : IsMatching E' M := by
              refine ⟨fun e he => ?_, hM.2⟩
              have heE : e ∈ edgesOf E := (mem_edgesOf E e).2 (hM.1 e he)
              have hne' : e ≠ s(u, v) := fun h => hnotM (h ▸ he)
              exact (mem_edgesOf E' e).1 (hE'edges ▸ Finset.mem_erase.2 ⟨hne', heE⟩)
            have hdep : ∃ x : Fin n → Bool,
                graphFun ∅ E (Function.update x v (!x v)) ≠ graphFun ∅ E x := by
              refine ⟨fun i => decide (i = u), ?_⟩
              have hvu : v ≠ u := (E.ne_of_adj huv).symm
              have h0 : graphFun ∅ E (fun i => decide (i = u)) = false := by
                cases hf : graphFun ∅ E (fun i => decide (i = u))
                · rfl
                · rw [graphFun_eq_true] at hf
                  rcases hf with ⟨_, h, _⟩ | ⟨a, b, hab, ha, hb⟩
                  · exact (Finset.notMem_empty _ h).elim
                  · simp only [decide_eq_true_eq] at ha hb
                    subst ha; subst hb
                    exact (E.ne_of_adj hab rfl).elim
              have h1 : graphFun ∅ E (Function.update (fun i => decide (i = u)) v (!decide (v = u))) = true := by
                rw [graphFun_eq_true]
                refine Or.inr ⟨u, v, huv, ?_, ?_⟩
                · simp [Function.update_of_ne hvu.symm]
                · simp [hvu]
              simp [h0, h1]
            obtain ⟨e1, he1⟩ := Finset.card_pos.1 (show 0 < (edgesOf E').card by omega)
            induction e1 using Sym2.ind with
            | _ a1 b1 =>
              have hab1 : E'.Adj a1 b1 := (mem_edgesOf E' _).1 he1
              have hnc : ∃ x y : Fin n → Bool,
                  graphFun ∅ E (Function.update x v false) ≠ graphFun ∅ E (Function.update y v false) := by
                refine ⟨fun _ => false, fun i => decide (i = a1 ∨ i = b1), ?_⟩
                have hdv := congrFun (hdel_v v)
                rw [hdv, hdv]
                have h0 : graphFun ∅ E' (fun _ => false) = false := by
                  cases hf : graphFun ∅ E' (fun _ => false)
                  · rfl
                  · rw [graphFun_eq_true] at hf
                    rcases hf with ⟨_, h, _⟩ | ⟨_, _, _, h, _⟩ <;> simp at h
                have h1 : graphFun ∅ E' (fun i => decide (i = a1 ∨ i = b1)) = true := by
                  rw [graphFun_eq_true]
                  exact Or.inr ⟨a1, b1, hab1, by simp, by simp⟩
                rw [h0, h1]; decide
              obtain ⟨hs1, hred⟩ := one_gate_elim (graphFun ∅ E) v false s hdep hnc hs
              rw [hdel_v v] at hred
              have hrec := ih (0 + 2 * (edgesOf E').card) (by simp only [Finset.card_empty, zero_add] at hK; omega)
                ∅ E' M (s - 1) (by simp) hE'acyc (by simp) hM' (by simp only [Finset.card_empty, zero_add]; omega) hred
              simp only [Finset.card_empty, zero_add] at hrec ⊢
              omega
        · obtain ⟨e0, he0⟩ := Finset.card_pos.1 hEpos
          induction e0 using Sym2.ind with
          | _ u0 v0 =>
            have huv0 : E.Adj u0 v0 := (mem_edgesOf E _).1 he0
            obtain ⟨L, hnd, hlp, hlen2, hmax⟩ := exists_longest_path E u0 v0 huv0
            rcases L with _ | ⟨a, _ | ⟨b, rest⟩⟩
            · simp at hlen2
            · simp at hlen2
            · have hab : E.Adj a b := hlp.1
              have ha_uniq : ∀ w, E.Adj a w → w = b := by
                intro w haw
                by_cases hwb : w = b
                · exact hwb
                · by_cases hwL : w ∈ a :: b :: rest
                  · simp only [List.mem_cons] at hwL
                    rcases hwL with rfl | rfl | hwr
                    · exact absurd rfl (E.ne_of_adj haw)
                    · exact absurd rfl hwb
                    · exact (acyclic_no_chord E hacyc a b rest hnd hlp w hwr haw).elim
                  · exfalso
                    have hlonger := hmax (w :: a :: b :: rest)
                      (List.nodup_cons.2 ⟨hwL, hnd⟩) ⟨haw.symm, hlp⟩
                    simp at hlonger
              cases rest with
              | nil =>
                have hb_uniq : ∀ w, E.Adj b w → w = a := by
                  intro w hbw
                  by_cases hwa : w = a
                  · exact hwa
                  · by_cases hwL : w ∈ [b, a]
                    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hwL
                      rcases hwL with rfl | rfl
                      · exact absurd rfl (E.ne_of_adj hbw)
                      · exact absurd rfl hwa
                    · exfalso
                      have hba_nd : ([b, a] : List (Fin n)).Nodup := by
                        simp [E.ne_of_adj hab.symm]
                      have hlonger := hmax (w :: b :: [a])
                        (List.nodup_cons.2 ⟨hwL, hba_nd⟩) ⟨hbw.symm, hab.symm, trivial⟩
                      simp at hlonger
                by_cases hE1 : (edgesOf E).card = 1
                · have hM1 : M.card ≤ 1 := by
                    have hsub : M ⊆ edgesOf E := fun e he => (mem_edgesOf E e).2 (hM.1 e he)
                    have := Finset.card_le_card hsub
                    omega
                  have hdep2 : ∀ i ∈ ({a, b} : Finset (Fin n)), ∃ x : Fin n → Bool,
                      graphFun ∅ E (Function.update x i (!x i)) ≠ graphFun ∅ E x := by
                    intro i hi
                    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                    rcases hi with rfl | rfl
                    · refine ⟨fun j => decide (j = b), ?_⟩
                      have h0 : graphFun ∅ E (fun j => decide (j = b)) = false := by
                        cases hf : graphFun ∅ E (fun j => decide (j = b))
                        · rfl
                        · rw [graphFun_eq_true] at hf
                          rcases hf with ⟨_, h, _⟩ | ⟨x1, x2, hx, h1, h2⟩
                          · exact (Finset.notMem_empty _ h).elim
                          · simp only [decide_eq_true_eq] at h1 h2; subst h1; subst h2; exact (E.ne_of_adj hx rfl).elim
                      have h1 : graphFun ∅ E (Function.update (fun j => decide (j = b)) i (!decide (i = b))) = true := by
                        rw [graphFun_eq_true]
                        exact Or.inr ⟨i, b, hab, by simp [E.ne_of_adj hab], by simp [Function.update_of_ne (E.ne_of_adj hab).symm]⟩
                      simp [h0, h1]
                    · refine ⟨fun j => decide (j = a), ?_⟩
                      have h0 : graphFun ∅ E (fun j => decide (j = a)) = false := by
                        cases hf : graphFun ∅ E (fun j => decide (j = a))
                        · rfl
                        · rw [graphFun_eq_true] at hf
                          rcases hf with ⟨_, h, _⟩ | ⟨x1, x2, hx, h1, h2⟩
                          · exact (Finset.notMem_empty _ h).elim
                          · simp only [decide_eq_true_eq] at h1 h2; subst h1; subst h2; exact (E.ne_of_adj hx rfl).elim
                      have h1 : graphFun ∅ E (Function.update (fun j => decide (j = a)) i (!decide (i = a))) = true := by
                        rw [graphFun_eq_true]
                        exact Or.inr ⟨a, i, hab, by simp [Function.update_of_ne (E.ne_of_adj hab)], by simp [(E.ne_of_adj hab).symm]⟩
                      simp [h0, h1]
                  have hdl := dep_lower_finset {a, b} (graphFun ∅ E) hdep2 s hs
                  rw [Finset.card_pair (E.ne_of_adj hab)] at hdl
                  simp at hK ⊢
                  omega
                · let E' := E.deleteEdges {e | a ∈ e}
                  have hE'sub : E' ≤ E := SimpleGraph.deleteEdges_le _
                  have hE'acyc : E'.IsAcyclic := fun x c hc => hacyc _ (hc.map (f := SimpleGraph.Hom.ofLE hE'sub) Function.injective_id)
                  have hE'edges : edgesOf E' = (edgesOf E).erase s(a, b) := by
                    ext e
                    induction e using Sym2.ind with
                    | _ x1 x2 =>
                      simp only [mem_edgesOf, E', SimpleGraph.edgeSet_deleteEdges,
                        Set.mem_diff, Set.mem_setOf_eq, Finset.mem_erase, SimpleGraph.mem_edgeSet]
                      constructor
                      · rintro ⟨hx, han⟩
                        refine ⟨fun heq => han (heq ▸ Sym2.mem_mk_left a b), hx⟩
                      · rintro ⟨hne', hx⟩
                        refine ⟨hx, fun ha12 => ?_⟩
                        rw [Sym2.mem_iff] at ha12
                        rcases ha12 with rfl | rfl
                        · exact hne' (by rw [ha_uniq x2 hx])
                        · exact hne' (by rw [ha_uniq x1 hx.symm, Sym2.eq_swap])
                  have hE'card : (edgesOf E').card + 1 = (edgesOf E).card := by
                    rw [hE'edges]
                    exact Finset.card_erase_add_one ((mem_edgesOf E _).2 hab)
                  have hE'no_b : ∀ v, ¬ E'.Adj b v := by
                    intro v hbv
                    rw [SimpleGraph.deleteEdges_adj] at hbv
                    have hva := hb_uniq v hbv.1
                    exact hbv.2 (show a ∈ s(b, v) by rw [hva]; exact Sym2.mem_mk_right b a)
                  have hupd1 : (fun x => graphFun ∅ E (Function.update x a true)) =
                      graphFun {b} E' := by
                    funext x
                    apply Bool.eq_iff_iff.2
                    rw [graphFun_eq_true, graphFun_eq_true]
                    simp only [Finset.notMem_empty, false_and, exists_false, false_or,
                      Finset.mem_singleton, exists_eq_left]
                    constructor
                    · rintro ⟨u, v, huv, hxu, hxv⟩
                      by_cases hua : u = a
                      · subst hua
                        have hvb := ha_uniq v huv
                        subst hvb
                        rw [Function.update_of_ne (E.ne_of_adj huv).symm] at hxv
                        exact Or.inl hxv
                      · by_cases hva : v = a
                        · subst hva
                          have hub := ha_uniq u huv.symm
                          subst hub
                          rw [Function.update_of_ne (E.ne_of_adj huv)] at hxu
                          exact Or.inl hxu
                        · rw [Function.update_of_ne hua] at hxu
                          rw [Function.update_of_ne hva] at hxv
                          refine Or.inr ⟨u, v, SimpleGraph.deleteEdges_adj.2 ⟨huv, ?_⟩, hxu, hxv⟩
                          intro hmem
                          change a ∈ s(u, v) at hmem
                          rw [Sym2.mem_iff] at hmem
                          rcases hmem with h1 | h1
                          · exact hua h1.symm
                          · exact hva h1.symm
                    · rintro (hxb | ⟨u, v, huv, hxu, hxv⟩)
                      · exact ⟨a, b, hab, by simp, by simp [Function.update_of_ne (E.ne_of_adj hab).symm, hxb]⟩
                      · rw [SimpleGraph.deleteEdges_adj] at huv
                        have hua : u ≠ a := fun e => huv.2 (show a ∈ s(u, v) by rw [e]; exact Sym2.mem_mk_left a v)
                        have hva : v ≠ a := fun e => huv.2 (show a ∈ s(u, v) by rw [e]; exact Sym2.mem_mk_right u a)
                        exact ⟨u, v, huv.1, by rwa [Function.update_of_ne hua], by rwa [Function.update_of_ne hva]⟩
                  have hM' : IsMatching E' (M.erase s(a, b)) := by
                    refine ⟨fun e he => ?_, fun e1 he1 e2 he2 =>
                      hM.2 e1 (Finset.mem_of_mem_erase he1) e2 (Finset.mem_of_mem_erase he2)⟩
                    obtain ⟨hne', heM⟩ := Finset.mem_erase.1 he
                    exact (mem_edgesOf E' e).1 (hE'edges ▸ Finset.mem_erase.2 ⟨hne', (mem_edgesOf E e).2 (hM.1 e heM)⟩)
                  have hdep : ∃ x : Fin n → Bool,
                      graphFun ∅ E (Function.update x a (!x a)) ≠ graphFun ∅ E x := by
                    refine ⟨fun j => decide (j = b), ?_⟩
                    have h0 : graphFun ∅ E (fun j => decide (j = b)) = false := by
                      cases hf : graphFun ∅ E (fun j => decide (j = b))
                      · rfl
                      · rw [graphFun_eq_true] at hf
                        rcases hf with ⟨_, h, _⟩ | ⟨x1, x2, hx, h1, h2⟩
                        · exact (Finset.notMem_empty _ h).elim
                        · simp only [decide_eq_true_eq] at h1 h2; subst h1; subst h2; exact (E.ne_of_adj hx rfl).elim
                    have h1 : graphFun ∅ E (Function.update (fun j => decide (j = b)) a (!decide (a = b))) = true := by
                      rw [graphFun_eq_true]
                      exact Or.inr ⟨a, b, hab, by simp [E.ne_of_adj hab], by simp [Function.update_of_ne (E.ne_of_adj hab).symm]⟩
                    simp [h0, h1]
                  obtain ⟨e1, he1⟩ := Finset.card_pos.1 (show 0 < (edgesOf E').card by omega)
                  induction e1 using Sym2.ind with
                  | _ a1 b1 =>
                    have hab1 : E'.Adj a1 b1 := (mem_edgesOf E' _).1 he1
                    have hnc0 : ∃ x y : Fin n → Bool,
                        graphFun ∅ E (Function.update x a false) ≠ graphFun ∅ E (Function.update y a false) := by
                      refine ⟨fun _ => false, fun i => decide (i = a1 ∨ i = b1), ?_⟩
                      have hdv := congrFun (hdel_v a)
                      rw [hdv, hdv]
                      have h0 : graphFun ∅ E' (fun _ => false) = false := by
                        cases hf : graphFun ∅ E' (fun _ => false)
                        · rfl
                        · rw [graphFun_eq_true] at hf
                          rcases hf with ⟨_, h, _⟩ | ⟨_, _, _, h, _⟩ <;> simp at h
                      have h1 : graphFun ∅ E' (fun i => decide (i = a1 ∨ i = b1)) = true := by
                        rw [graphFun_eq_true]
                        exact Or.inr ⟨a1, b1, hab1, by simp, by simp⟩
                      rw [h0, h1]; decide
                    have hnc1 : ∃ x y : Fin n → Bool,
                        graphFun ∅ E (Function.update x a true) ≠ graphFun ∅ E (Function.update y a true) := by
                      refine ⟨fun _ => false, fun i => decide (i = b), ?_⟩
                      have hu1 := congrFun hupd1
                      rw [hu1, hu1]
                      have h0 : graphFun {b} E' (fun _ => false) = false := by
                        cases hf : graphFun {b} E' (fun _ => false)
                        · rfl
                        · rw [graphFun_eq_true] at hf
                          rcases hf with ⟨_, _, h⟩ | ⟨_, _, _, h, _⟩ <;> simp at h
                      have h1 : graphFun {b} E' (fun i => decide (i = b)) = true := by
                        rw [graphFun_eq_true]
                        exact Or.inl ⟨b, Finset.mem_singleton_self b, by simp⟩
                      rw [h0, h1]; decide
                    obtain ⟨hs2, hred0 | hred1⟩ := two_gate_elim (graphFun ∅ E) a s hdep hnc0 hnc1 hs
                    · rw [hdel_v a] at hred0
                      have hrec := ih (0 + 2 * (edgesOf E').card) (by simp only [Finset.card_empty, zero_add] at hK; omega)
                        ∅ E' (M.erase s(a, b)) (s - 2) (by simp) hE'acyc (by simp) hM' (by simp only [Finset.card_empty, zero_add]; omega) hred0
                      have hm := matching_card_erase M s(a, b)
                      simp only [Finset.card_empty, zero_add] at hrec ⊢
                      omega
                    · rw [hupd1] at hred1
                      have hrec := ih (1 + 2 * (edgesOf E').card) (by simp only [Finset.card_empty, zero_add] at hK; omega)
                        {b} E' (M.erase s(a, b)) (s - 2) (by simp) hE'acyc
                        (fun x hx => by rw [Finset.mem_singleton.1 hx]; exact hE'no_b) hM' (by simp) hred1
                      have hm := matching_card_erase M s(a, b)
                      simp only [Finset.card_empty, Finset.card_singleton, zero_add] at hrec ⊢
                      omega
              | cons c rest' =>
                have hbc : E.Adj b c := hlp.2.1
                have haM : s(b, a) ∈ M := by
                  by_contra hn
                  exact hleaf_free ⟨a, b, hab.symm, ha_uniq, hn⟩
                have hb_uniq : ∀ w, E.Adj b w → w = a ∨ w = c := by
                  intro w hbw
                  by_cases hwa : w = a
                  · exact Or.inl hwa
                  · by_cases hwc : w = c
                    · exact Or.inr hwc
                    · exfalso
                      by_cases hwL : w ∈ a :: b :: c :: rest'
                      · simp only [List.mem_cons] at hwL
                        rcases hwL with rfl | rfl | rfl | hwr
                        · exact hwa rfl
                        · exact E.ne_of_adj hbw rfl
                        · exact hwc rfl
                        · exact acyclic_no_chord E hacyc b c rest' (List.nodup_cons.1 hnd).2 hlp.2 w hwr hbw
                      · have hw_uniq : ∀ z, E.Adj w z → z = b := by
                          intro z hwz
                          by_cases hzb : z = b
                          · exact hzb
                          · by_cases hzL : z ∈ a :: b :: c :: rest'
                            · simp only [List.mem_cons] at hzL
                              rcases hzL with hza | hzb' | hzc | hzr
                              · subst z
                                have hnd' : (w :: b :: [a]).Nodup := by
                                  have hne_wa : w ≠ a := fun e => hwL (e ▸ List.mem_cons_self)
                                  have hne_wb : w ≠ b := (E.ne_of_adj hbw).symm
                                  have hne_ba : b ≠ a := (E.ne_of_adj hab).symm
                                  simp [hne_wa, hne_wb, hne_ba]
                                exact (acyclic_no_chord E hacyc w b [a] hnd' ⟨hbw.symm, hab.symm, trivial⟩ a
                                  List.mem_cons_self hwz).elim
                              · exact (hzb hzb').elim
                              · subst z
                                have hnd' : (w :: b :: [c]).Nodup := by
                                  have hne_wc : w ≠ c := fun e => hwL (e ▸ List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
                                  have hne_wb : w ≠ b := (E.ne_of_adj hbw).symm
                                  have hne_bc : b ≠ c := E.ne_of_adj hbc
                                  simp [hne_wc, hne_wb, hne_bc]
                                exact (acyclic_no_chord E hacyc w b [c] hnd' ⟨hbw.symm, hbc, trivial⟩ c
                                  List.mem_cons_self hwz).elim
                              · have hnd' : (w :: b :: c :: rest').Nodup :=
                                  List.nodup_cons.2 ⟨fun h => hwL (List.mem_cons_of_mem _ h), (List.nodup_cons.1 hnd).2⟩
                                exact (acyclic_no_chord E hacyc w b (c :: rest') hnd' ⟨hbw.symm, hlp.2⟩ z
                                  (List.mem_cons_of_mem _ hzr) hwz).elim
                            · exfalso
                              have hnd' : (z :: w :: b :: c :: rest').Nodup := by
                                refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨fun h => hwL (List.mem_cons_of_mem _ h), (List.nodup_cons.1 hnd).2⟩⟩
                                intro hz'
                                rw [List.mem_cons] at hz'
                                rcases hz' with rfl | h
                                · exact E.ne_of_adj hwz rfl
                                · exact hzL (List.mem_cons_of_mem _ h)
                              have hlonger := hmax (z :: w :: b :: c :: rest') hnd' ⟨hwz.symm, hbw.symm, hlp.2⟩
                              simp at hlonger
                        have hwM : s(b, w) ∈ M := by
                          by_contra hn
                          exact hleaf_free ⟨w, b, hbw, hw_uniq, hn⟩
                        have hne_aw : s(b, a) ≠ s(b, w) := by
                          intro heq
                          rw [Sym2.eq_iff] at heq
                          rcases heq with ⟨_, h1⟩ | ⟨h1, _⟩
                          · exact hwa h1.symm
                          · exact E.ne_of_adj hbw h1
                        exact hM.2 s(b, a) haM s(b, w) hwM hne_aw b ⟨Sym2.mem_mk_left b a, Sym2.mem_mk_left b w⟩
                have hne_ab : a ≠ b := E.ne_of_adj hab
                have hne_bc : b ≠ c := E.ne_of_adj hbc
                have hne_ac : a ≠ c := by
                  intro e; subst e
                  have := (List.nodup_cons.1 hnd).1
                  exact this (List.mem_cons_of_mem _ List.mem_cons_self)
                by_cases hE2 : (edgesOf E).card ≤ 2
                · have hEeq2 : edgesOf E = {s(a, b), s(b, c)} := by
                    have hsub : ({s(a, b), s(b, c)} : Finset (Sym2 (Fin n))) ⊆ edgesOf E := by
                      intro e he; simp only [Finset.mem_insert, Finset.mem_singleton] at he
                      rcases he with rfl | rfl
                      · exact (mem_edgesOf E _).2 hab
                      · exact (mem_edgesOf E _).2 hbc
                    have hne_e : s(a, b) ≠ s(b, c) := by
                      intro heq; rw [Sym2.eq_iff] at heq
                      rcases heq with ⟨rfl, _⟩ | ⟨rfl, _⟩
                      · exact hne_ab rfl
                      · exact hne_ac rfl
                    have hcard2 : ({s(a, b), s(b, c)} : Finset (Sym2 (Fin n))).card = 2 := Finset.card_pair hne_e
                    exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
                  have hM1 : M.card ≤ 1 := by
                    by_contra hM2
                    have hgt : 1 < M.card := by omega
                    obtain ⟨e1, he1, e2, he2, hne12⟩ := Finset.one_lt_card.1 hgt
                    have he1' : e1 ∈ ({s(a, b), s(b, c)} : Finset (Sym2 (Fin n))) :=
                      hEeq2 ▸ (mem_edgesOf E e1).2 (hM.1 e1 he1)
                    have he2' : e2 ∈ ({s(a, b), s(b, c)} : Finset (Sym2 (Fin n))) :=
                      hEeq2 ▸ (mem_edgesOf E e2).2 (hM.1 e2 he2)
                    have hb1 : b ∈ e1 := by
                      simp only [Finset.mem_insert, Finset.mem_singleton] at he1'
                      rcases he1' with rfl | rfl <;> simp
                    have hb2 : b ∈ e2 := by
                      simp only [Finset.mem_insert, Finset.mem_singleton] at he2'
                      rcases he2' with rfl | rfl <;> simp
                    exact hM.2 e1 he1 e2 he2 hne12 b ⟨hb1, hb2⟩
                  have hdep3 : ∀ i ∈ ({a, b, c} : Finset (Fin n)), ∃ x : Fin n → Bool,
                      graphFun ∅ E (Function.update x i (!x i)) ≠ graphFun ∅ E x := by
                    intro i hi
                    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                    rcases hi with rfl | rfl | rfl
                    · refine ⟨fun j => decide (j = b), ?_⟩
                      have h0 : graphFun ∅ E (fun j => decide (j = b)) = false := by
                        cases hf : graphFun ∅ E (fun j => decide (j = b))
                        · rfl
                        · rw [graphFun_eq_true] at hf
                          rcases hf with ⟨_, h, _⟩ | ⟨x1, x2, hx, h1, h2⟩
                          · exact (Finset.notMem_empty _ h).elim
                          · simp only [decide_eq_true_eq] at h1 h2; subst h1; subst h2; exact (E.ne_of_adj hx rfl).elim
                      have h1 : graphFun ∅ E (Function.update (fun j => decide (j = b)) i (!decide (i = b))) = true := by
                        rw [graphFun_eq_true]
                        exact Or.inr ⟨i, b, hab, by simp [hne_ab], by simp [Function.update_of_ne hne_ab.symm]⟩
                      simp [h0, h1]
                    · refine ⟨fun j => decide (j = a), ?_⟩
                      have h0 : graphFun ∅ E (fun j => decide (j = a)) = false := by
                        cases hf : graphFun ∅ E (fun j => decide (j = a))
                        · rfl
                        · rw [graphFun_eq_true] at hf
                          rcases hf with ⟨_, h, _⟩ | ⟨x1, x2, hx, h1, h2⟩
                          · exact (Finset.notMem_empty _ h).elim
                          · simp only [decide_eq_true_eq] at h1 h2; subst h1; subst h2; exact (E.ne_of_adj hx rfl).elim
                      have h1 : graphFun ∅ E (Function.update (fun j => decide (j = a)) i (!decide (i = a))) = true := by
                        rw [graphFun_eq_true]
                        exact Or.inr ⟨a, i, hab, by simp [Function.update_of_ne hne_ab], by simp [hne_ab.symm]⟩
                      simp [h0, h1]
                    · refine ⟨fun j => decide (j = b), ?_⟩
                      have h0 : graphFun ∅ E (fun j => decide (j = b)) = false := by
                        cases hf : graphFun ∅ E (fun j => decide (j = b))
                        · rfl
                        · rw [graphFun_eq_true] at hf
                          rcases hf with ⟨_, h, _⟩ | ⟨x1, x2, hx, h1, h2⟩
                          · exact (Finset.notMem_empty _ h).elim
                          · simp only [decide_eq_true_eq] at h1 h2; subst h1; subst h2; exact (E.ne_of_adj hx rfl).elim
                      have h1 : graphFun ∅ E (Function.update (fun j => decide (j = b)) i (!decide (i = b))) = true := by
                        rw [graphFun_eq_true]
                        exact Or.inr ⟨b, i, hbc, by simp [Function.update_of_ne hne_bc], by simp [hne_bc.symm]⟩
                      simp [h0, h1]
                  have hdl := dep_lower_finset {a, b, c} (graphFun ∅ E) hdep3 s hs
                  have hcard3 : ({a, b, c} : Finset (Fin n)).card = 3 := by
                    rw [Finset.card_insert_of_notMem (by simp [hne_ab, hne_ac]), Finset.card_pair hne_bc]
                  rw [hcard3] at hdl
                  simp at hK ⊢
                  omega
                · let E0 := E.deleteEdges {e | a ∈ e}
                  let E1 := E.deleteEdges {e | a ∈ e ∨ b ∈ e}
                  have hE0sub : E0 ≤ E := SimpleGraph.deleteEdges_le _
                  have hE1sub : E1 ≤ E := SimpleGraph.deleteEdges_le _
                  have hE0acyc : E0.IsAcyclic := fun x p hp => hacyc _ (hp.map (f := SimpleGraph.Hom.ofLE hE0sub) Function.injective_id)
                  have hE1acyc : E1.IsAcyclic := fun x p hp => hacyc _ (hp.map (f := SimpleGraph.Hom.ofLE hE1sub) Function.injective_id)
                  have hE0edges : edgesOf E0 = (edgesOf E).erase s(a, b) := by
                    ext e
                    induction e using Sym2.ind with
                    | _ x1 x2 =>
                      simp only [mem_edgesOf, E0, SimpleGraph.edgeSet_deleteEdges,
                        Set.mem_diff, Set.mem_setOf_eq, Finset.mem_erase, SimpleGraph.mem_edgeSet]
                      constructor
                      · rintro ⟨hx, han⟩
                        exact ⟨fun heq => han (heq ▸ Sym2.mem_mk_left a b), hx⟩
                      · rintro ⟨hne', hx⟩
                        refine ⟨hx, fun ha12 => ?_⟩
                        rw [Sym2.mem_iff] at ha12
                        rcases ha12 with rfl | rfl
                        · exact hne' (by rw [ha_uniq x2 hx])
                        · exact hne' (by rw [ha_uniq x1 hx.symm, Sym2.eq_swap])
                  have hE1edges : edgesOf E1 = ((edgesOf E).erase s(a, b)).erase s(b, c) := by
                    ext e
                    induction e using Sym2.ind with
                    | _ x1 x2 =>
                      simp only [mem_edgesOf, E1, SimpleGraph.edgeSet_deleteEdges,
                        Set.mem_diff, Set.mem_setOf_eq, Finset.mem_erase, SimpleGraph.mem_edgeSet, not_or]
                      constructor
                      · rintro ⟨hx, han, hbn⟩
                        exact ⟨fun heq => hbn (heq ▸ Sym2.mem_mk_left b c),
                          fun heq => han (heq ▸ Sym2.mem_mk_left a b), hx⟩
                      · rintro ⟨hne2, hne1, hx⟩
                        refine ⟨hx, fun ha12 => ?_, fun hb12 => ?_⟩
                        · rw [Sym2.mem_iff] at ha12
                          rcases ha12 with rfl | rfl
                          · exact hne1 (by rw [ha_uniq x2 hx])
                          · exact hne1 (by rw [ha_uniq x1 hx.symm, Sym2.eq_swap])
                        · rw [Sym2.mem_iff] at hb12
                          rcases hb12 with rfl | rfl
                          · rcases hb_uniq x2 hx with rfl | rfl
                            · exact hne1 Sym2.eq_swap
                            · exact hne2 rfl
                          · rcases hb_uniq x1 hx.symm with rfl | rfl
                            · exact hne1 rfl
                            · exact hne2 Sym2.eq_swap
                  have hne_e : s(b, c) ≠ s(a, b) := by
                    intro heq; rw [Sym2.eq_iff] at heq
                    rcases heq with ⟨rfl, _⟩ | ⟨_, rfl⟩
                    · exact hne_ab rfl
                    · exact hne_ac rfl
                  have hE0card : (edgesOf E0).card + 1 = (edgesOf E).card := by
                    rw [hE0edges]; exact Finset.card_erase_add_one ((mem_edgesOf E s(a, b)).2 hab)
                  have hE1card : (edgesOf E1).card + 2 = (edgesOf E).card := by
                    rw [hE1edges]
                    have h1 := Finset.card_erase_add_one
                      (Finset.mem_erase.2 ⟨hne_e, (mem_edgesOf E s(b, c)).2 hbc⟩)
                    have h2 := Finset.card_erase_add_one ((mem_edgesOf E s(a, b)).2 hab)
                    omega
                  have hE1no_b : ∀ v, ¬ E1.Adj b v := fun v hbv =>
                    (SimpleGraph.deleteEdges_adj.1 hbv).2 (show a ∈ s(b, v) ∨ b ∈ s(b, v) from Or.inr (Sym2.mem_mk_left b v))
                  have hupd1 : (fun x => graphFun ∅ E (Function.update x a true)) =
                      graphFun {b} E1 := by
                    funext x
                    apply Bool.eq_iff_iff.2
                    rw [graphFun_eq_true, graphFun_eq_true]
                    simp only [Finset.notMem_empty, false_and, exists_false, false_or,
                      Finset.mem_singleton, exists_eq_left]
                    constructor
                    · rintro ⟨u, v, huv, hxu, hxv⟩
                      by_cases hua : u = a
                      · subst hua
                        have hvb := ha_uniq v huv
                        subst hvb
                        rw [Function.update_of_ne hne_ab.symm] at hxv
                        exact Or.inl hxv
                      · by_cases hva : v = a
                        · subst hva
                          have hub := ha_uniq u huv.symm
                          subst hub
                          rw [Function.update_of_ne hne_ab.symm] at hxu
                          exact Or.inl hxu
                        · rw [Function.update_of_ne hua] at hxu
                          rw [Function.update_of_ne hva] at hxv
                          by_cases hub : u = b
                          · subst hub; exact Or.inl hxu
                          · by_cases hvb : v = b
                            · subst hvb; exact Or.inl hxv
                            · refine Or.inr ⟨u, v, SimpleGraph.deleteEdges_adj.2 ⟨huv, ?_⟩, hxu, hxv⟩
                              intro hmem
                              change a ∈ s(u, v) ∨ b ∈ s(u, v) at hmem
                              rcases hmem with h1 | h1 <;> rw [Sym2.mem_iff] at h1
                              · rcases h1 with h1 | h1
                                · exact hua h1.symm
                                · exact hva h1.symm
                              · rcases h1 with h1 | h1
                                · exact hub h1.symm
                                · exact hvb h1.symm
                    · rintro (hxb | ⟨u, v, huv, hxu, hxv⟩)
                      · exact ⟨a, b, hab, by simp, by simp [Function.update_of_ne hne_ab.symm, hxb]⟩
                      · rw [SimpleGraph.deleteEdges_adj] at huv
                        have hua : u ≠ a := fun e => huv.2 (show a ∈ s(u, v) ∨ b ∈ s(u, v) from Or.inl (by rw [e]; exact Sym2.mem_mk_left a v))
                        have hva : v ≠ a := fun e => huv.2 (show a ∈ s(u, v) ∨ b ∈ s(u, v) from Or.inl (by rw [e]; exact Sym2.mem_mk_right u a))
                        exact ⟨u, v, huv.1, by rwa [Function.update_of_ne hua], by rwa [Function.update_of_ne hva]⟩
                  have hM0 : IsMatching E0 (M.erase s(a, b)) := by
                    refine ⟨fun e he => ?_, fun e1 he1 e2 he2 =>
                      hM.2 e1 (Finset.mem_of_mem_erase he1) e2 (Finset.mem_of_mem_erase he2)⟩
                    obtain ⟨hne', heM⟩ := Finset.mem_erase.1 he
                    exact (mem_edgesOf E0 e).1 (hE0edges ▸ Finset.mem_erase.2 ⟨hne', (mem_edgesOf E e).2 (hM.1 e heM)⟩)
                  have hM1 : IsMatching E1 ((M.erase s(b, a)).erase s(b, c)) := by
                    refine ⟨fun e he => ?_, fun e1 he1 e2 he2 =>
                      hM.2 e1 (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase he1))
                        e2 (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase he2))⟩
                    obtain ⟨hne2, he'⟩ := Finset.mem_erase.1 he
                    obtain ⟨hne1, heM⟩ := Finset.mem_erase.1 he'
                    have hne1' : e ≠ s(a, b) := fun h => hne1 (h.trans Sym2.eq_swap)
                    exact (mem_edgesOf E1 e).1 (hE1edges ▸ Finset.mem_erase.2
                      ⟨hne2, Finset.mem_erase.2 ⟨hne1', (mem_edgesOf E e).2 (hM.1 e heM)⟩⟩)
                  have hdep : ∃ x : Fin n → Bool,
                      graphFun ∅ E (Function.update x a (!x a)) ≠ graphFun ∅ E x := by
                    refine ⟨fun j => decide (j = b), ?_⟩
                    have h0 : graphFun ∅ E (fun j => decide (j = b)) = false := by
                      cases hf : graphFun ∅ E (fun j => decide (j = b))
                      · rfl
                      · rw [graphFun_eq_true] at hf
                        rcases hf with ⟨_, h, _⟩ | ⟨x1, x2, hx, h1, h2⟩
                        · exact (Finset.notMem_empty _ h).elim
                        · simp only [decide_eq_true_eq] at h1 h2; subst h1; subst h2; exact (E.ne_of_adj hx rfl).elim
                    have h1 : graphFun ∅ E (Function.update (fun j => decide (j = b)) a (!decide (a = b))) = true := by
                      rw [graphFun_eq_true]
                      exact Or.inr ⟨a, b, hab, by simp [hne_ab], by simp [Function.update_of_ne hne_ab.symm]⟩
                    simp [h0, h1]
                  have hnc0 : ∃ x y : Fin n → Bool,
                      graphFun ∅ E (Function.update x a false) ≠ graphFun ∅ E (Function.update y a false) := by
                    refine ⟨fun _ => false, fun i => decide (i = b ∨ i = c), ?_⟩
                    have hdv := congrFun (hdel_v a)
                    rw [hdv, hdv]
                    have hbc0 : E0.Adj b c := ⟨hbc, by simp [Sym2.mem_iff, hne_ab, hne_ac]⟩
                    have h0 : graphFun ∅ E0 (fun _ => false) = false := by
                      cases hf : graphFun ∅ E0 (fun _ => false)
                      · rfl
                      · rw [graphFun_eq_true] at hf
                        rcases hf with ⟨_, h, _⟩ | ⟨_, _, _, h, _⟩ <;> simp at h
                    have h1 : graphFun ∅ E0 (fun i => decide (i = b ∨ i = c)) = true := by
                      rw [graphFun_eq_true]
                      exact Or.inr ⟨b, c, hbc0, by simp, by simp⟩
                    rw [h0, h1]; decide
                  have hnc1 : ∃ x y : Fin n → Bool,
                      graphFun ∅ E (Function.update x a true) ≠ graphFun ∅ E (Function.update y a true) := by
                    refine ⟨fun _ => false, fun i => decide (i = b), ?_⟩
                    have hu1 := congrFun hupd1
                    rw [hu1, hu1]
                    have h0 : graphFun {b} E1 (fun _ => false) = false := by
                      cases hf : graphFun {b} E1 (fun _ => false)
                      · rfl
                      · rw [graphFun_eq_true] at hf
                        rcases hf with ⟨_, _, h⟩ | ⟨_, _, _, h, _⟩ <;> simp at h
                    have h1 : graphFun {b} E1 (fun i => decide (i = b)) = true := by
                      rw [graphFun_eq_true]
                      exact Or.inl ⟨b, Finset.mem_singleton_self b, by simp⟩
                    rw [h0, h1]; decide
                  obtain ⟨hs2, hred0 | hred1⟩ := two_gate_elim (graphFun ∅ E) a s hdep hnc0 hnc1 hs
                  · rw [hdel_v a] at hred0
                    have hrec := ih (0 + 2 * (edgesOf E0).card) (by simp only [Finset.card_empty, zero_add] at hK; omega)
                      ∅ E0 (M.erase s(a, b)) (s - 2) (by simp) hE0acyc (by simp) hM0 (by simp only [Finset.card_empty, zero_add]; omega) hred0
                    have hm := matching_card_erase M s(a, b)
                    simp only [Finset.card_empty, zero_add] at hrec ⊢
                    omega
                  · rw [hupd1] at hred1
                    have hrec := ih (1 + 2 * (edgesOf E1).card) (by simp only [Finset.card_empty, zero_add] at hK; omega)
                      {b} E1 ((M.erase s(b, a)).erase s(b, c)) (s - 2) (by simp) hE1acyc
                      (fun x hx => by rw [Finset.mem_singleton.1 hx]; exact hE1no_b) hM1 (by simp) hred1
                    have hm := matching_card_erase_two_incident E M hM b a c
                    simp only [Finset.card_empty, Finset.card_singleton, zero_add] at hrec ⊢
                    omega

theorem isAcyclic_of_parent {n : ℕ} (E : SimpleGraph (Fin n))
    (par : Fin n → Option (Fin n)) (dep : Fin n → ℕ)
    (h : ∀ u v, E.Adj u v → (par u = some v ∧ dep v < dep u) ∨ (par v = some u ∧ dep u < dep v)) :
    E.IsAcyclic := by
  classical
  intro u c hc
  have hne : c.support.toFinset.Nonempty := ⟨u, List.mem_toFinset.2 (SimpleGraph.Walk.start_mem_support c)⟩
  obtain ⟨w, hw, hmax⟩ := Finset.exists_max_image c.support.toFinset dep hne
  have hws : w ∈ c.support := List.mem_toFinset.1 hw
  let c' := c.rotate w hws
  have hc' : c'.IsCycle := hc.rotate hws
  have hlen3 : 3 ≤ c'.length := hc'.three_le_length
  have hsub : ∀ z ∈ c'.support, dep z ≤ dep w := by
    intro z hz
    have hzc : z ∈ c.support := (SimpleGraph.Walk.mem_support_rotate_iff c w hws).1 hz
    exact hmax z (List.mem_toFinset.2 hzc)
  cases hc'eq : c' with
  | nil => rw [hc'eq] at hlen3; simp at hlen3
  | cons hadj1 p =>
    rename_i a
    have ha_mem : a ∈ c'.support := by rw [hc'eq]; simp
    have hda : dep a ≤ dep w := hsub a ha_mem
    have hpar_a : par w = some a := by
      rcases h w a hadj1 with ⟨hp, _⟩ | ⟨_, hlt⟩
      · exact hp
      · omega
    cases hrev : p.reverse with
    | nil =>
      have : p.length = 0 := by
        have h1 := congrArg SimpleGraph.Walk.length hrev
        simp only [SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.length_nil] at h1
        exact h1
      rw [hc'eq] at hlen3
      simp only [SimpleGraph.Walk.length_cons] at hlen3
      omega
    | cons hadj2 q =>
      rename_i b
      have hb_mem : b ∈ c'.support := by
        rw [hc'eq]
        have : b ∈ p.reverse.support := by rw [hrev]; simp
        rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at this
        exact List.mem_cons_of_mem _ this
      have hdb : dep b ≤ dep w := hsub b hb_mem
      have hpar_b : par w = some b := by
        rcases h w b hadj2 with ⟨hp, _⟩ | ⟨_, hlt⟩
        · exact hp
        · omega
      have hab : a = b := Option.some.inj (hpar_a.symm.trans hpar_b)
      subst hab
      have hnd : c'.edges.Nodup := hc'.edges_nodup
      rw [hc'eq] at hnd
      simp only [SimpleGraph.Walk.edges_cons, List.nodup_cons] at hnd
      have hmem_e : s(w, a) ∈ p.edges := by
        have : s(w, a) ∈ p.reverse.edges := by rw [hrev]; simp
        rwa [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at this
      exact hnd.1 hmem_e

def fG (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 1) ||
  (x 0 && x 8) || (x 1 && x 9)

def mkGraph (es : List (Fin 10 × Fin 10)) : SimpleGraph (Fin 10) :=
  SimpleGraph.fromRel (fun a b => (a, b) ∈ es)

theorem mkGraph_adj (es : List (Fin 10 × Fin 10)) (a b : Fin 10) :
    (mkGraph es).Adj a b ↔ a ≠ b ∧ ((a, b) ∈ es ∨ (b, a) ∈ es) := by
  simp [mkGraph, SimpleGraph.fromRel_adj]

theorem mkGraph_edgesOf_card_ge (es : List (Fin 10 × Fin 10)) (k : ℕ)
    (h : (es.map (fun p => s(p.1, p.2))).toFinset.card = k)
    (hloopless : ∀ p ∈ es, p.1 ≠ p.2) :
    k ≤ (edgesOf (mkGraph es)).card := by
  rw [← h]
  apply Finset.card_le_card
  intro e he
  rw [List.mem_toFinset, List.mem_map] at he
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := he
  rw [mem_edgesOf, SimpleGraph.mem_edgeSet, mkGraph_adj]
  exact ⟨hloopless (a, b) hab, Or.inl hab⟩

theorem fG_forest_lower (A : Finset (Fin 10)) (es : List (Fin 10 × Fin 10))
    (M : Finset (Sym2 (Fin 10))) (par : Fin 10 → Option (Fin 10)) (dep : Fin 10 → ℕ)
    (v : Fin 10) (b : Bool) (B s : ℕ)
    (hpar : ∀ p ∈ es, (par p.1 = some p.2 ∧ dep p.2 < dep p.1) ∨ (par p.2 = some p.1 ∧ dep p.1 < dep p.2))
    (hdisj : ∀ a ∈ A, ∀ p ∈ es, a ≠ p.1 ∧ a ≠ p.2)
    (hloopless : ∀ p ∈ es, p.1 ≠ p.2)
    (hM1 : ∀ e ∈ M, ∃ p ∈ es, e = s(p.1, p.2))
    (hM2 : ∀ e1 ∈ M, ∀ e2 ∈ M, e1 ≠ e2 → ∀ u : Fin 10, ¬ (u ∈ e1 ∧ u ∈ e2))
    (hbound : B ≤ A.card + (es.map (fun p => s(p.1, p.2))).toFinset.card + M.card - 1)
    (hpos : 1 ≤ A.card + (es.map (fun p => s(p.1, p.2))).toFinset.card)
    (heq : ∀ x : Fin 10 → Bool,
      ((∃ a ∈ A, x a = true) ∨ (∃ p ∈ es, x p.1 = true ∧ x p.2 = true)) ↔
      fG (Function.update x v b) = true)
    (hs : HasCircuitSize 10 (fun x => fG (Function.update x v b)) s) :
    B ≤ s := by
  let E := mkGraph es
  have hacyc : E.IsAcyclic := by
    apply isAcyclic_of_parent E par dep
    intro u w huw
    rw [mkGraph_adj] at huw
    rcases huw.2 with h | h
    · exact hpar (u, w) h
    · exact (hpar (w, u) h).symm
  have hdisj' : ∀ a ∈ A, ∀ w, ¬ E.Adj a w := by
    intro a ha w haw
    rw [mkGraph_adj] at haw
    rcases haw.2 with h | h
    · exact (hdisj a ha (a, w) h).1 rfl
    · exact (hdisj a ha (w, a) h).2 rfl
  have hM : IsMatching E M := by
    refine ⟨fun e he => ?_, hM2⟩
    obtain ⟨⟨a, c⟩, hac, rfl⟩ := hM1 e he
    rw [SimpleGraph.mem_edgeSet, mkGraph_adj]
    exact ⟨hloopless (a, c) hac, Or.inl hac⟩
  have hEcard : (es.map (fun p => s(p.1, p.2))).toFinset.card ≤ (edgesOf E).card :=
    mkGraph_edgesOf_card_ge es _ rfl hloopless
  have hfun : (fun x => fG (Function.update x v b)) = graphFun A E := by
    funext x
    apply Bool.eq_iff_iff.2
    rw [graphFun_eq_true, ← heq x]
    constructor
    · rintro (h | ⟨⟨a, c⟩, hac, ha, hc⟩)
      · exact Or.inl h
      · exact Or.inr ⟨a, c, (mkGraph_adj es a c).2 ⟨hloopless _ hac, Or.inl hac⟩, ha, hc⟩
    · rintro (h | ⟨a, c, hac, ha, hc⟩)
      · exact Or.inl h
      · rw [mkGraph_adj] at hac
        rcases hac.2 with h | h
        · exact Or.inr ⟨(a, c), h, ha, hc⟩
        · exact Or.inr ⟨(c, a), h, hc, ha⟩
  rw [hfun] at hs
  have hfb := forest_bound (A.card + 2 * (edgesOf E).card) A E M s rfl hacyc hdisj' hM (by omega) hs
  omega

def par3 : Fin 10 → Option (Fin 10)
  | 0 => none | 8 => some 0 | 2 => some 0 | 1 => some 0
  | 9 => some 1 | 7 => some 1 | 6 => some 7 | 5 => some 6 | 4 => some 5 | 3 => none

def dep3 : Fin 10 → ℕ
  | 0 => 0 | 8 => 1 | 2 => 1 | 1 => 1 | 9 => 2 | 7 => 2 | 6 => 3 | 5 => 4 | 4 => 5 | 3 => 0

def par4 : Fin 10 → Option (Fin 10)
  | 0 => none | 8 => some 0 | 2 => some 0 | 3 => some 2 | 1 => some 0
  | 9 => some 1 | 7 => some 1 | 6 => some 7 | 5 => some 6 | 4 => none

def dep4 : Fin 10 → ℕ
  | 0 => 0 | 8 => 1 | 2 => 1 | 3 => 2 | 1 => 1 | 9 => 2 | 7 => 2 | 6 => 3 | 5 => 4 | 4 => 0

def par5 : Fin 10 → Option (Fin 10)
  | 0 => none | 8 => some 0 | 2 => some 0 | 3 => some 2 | 4 => some 3 | 1 => some 0
  | 9 => some 1 | 7 => some 1 | 6 => some 7 | 5 => none

def dep5 : Fin 10 → ℕ
  | 0 => 0 | 8 => 1 | 2 => 1 | 3 => 2 | 4 => 3 | 1 => 1 | 9 => 2 | 7 => 2 | 6 => 3 | 5 => 0

def par6 : Fin 10 → Option (Fin 10)
  | 0 => none | 8 => some 0 | 2 => some 0 | 3 => some 2 | 4 => some 3 | 5 => some 4
  | 1 => some 0 | 9 => some 1 | 7 => some 1 | 6 => none

def dep6 : Fin 10 → ℕ
  | 0 => 0 | 8 => 1 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 4 | 1 => 1 | 9 => 2 | 7 => 2 | 6 => 0

theorem fG_false_3 (s : ℕ) (hs : HasCircuitSize 10 (fun x => fG (Function.update x 3 false)) s) : 11 ≤ s :=
  fG_forest_lower ∅ [(0, 1), (0, 2), (4, 5), (5, 6), (6, 7), (7, 1), (0, 8), (1, 9)]
    {s(0, 8), s(1, 9), s(6, 7), s(4, 5)} par3 dep3 3 false 11 s
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun x => by simp [fG, Function.update]; tauto) hs

theorem fG_true_3 (s : ℕ) (hs : HasCircuitSize 10 (fun x => fG (Function.update x 3 true)) s) : 10 ≤ s :=
  fG_forest_lower {2, 4} [(0, 1), (5, 6), (6, 7), (7, 1), (0, 8), (1, 9)]
    {s(0, 8), s(1, 9), s(5, 6)} par3 dep3 3 true 10 s
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun x => by simp [fG, Function.update]; tauto) hs

theorem fG_false_4 (s : ℕ) (hs : HasCircuitSize 10 (fun x => fG (Function.update x 4 false)) s) : 11 ≤ s :=
  fG_forest_lower ∅ [(0, 1), (0, 2), (2, 3), (5, 6), (6, 7), (7, 1), (0, 8), (1, 9)]
    {s(0, 8), s(2, 3), s(1, 9), s(5, 6)} par4 dep4 4 false 11 s
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun x => by simp [fG, Function.update]; tauto) hs

theorem fG_true_4 (s : ℕ) (hs : HasCircuitSize 10 (fun x => fG (Function.update x 4 true)) s) : 10 ≤ s :=
  fG_forest_lower {3, 5} [(0, 1), (0, 2), (6, 7), (7, 1), (0, 8), (1, 9)]
    {s(0, 8), s(1, 9), s(6, 7)} par4 dep4 4 true 10 s
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun x => by simp [fG, Function.update]; tauto) hs

theorem fG_false_5 (s : ℕ) (hs : HasCircuitSize 10 (fun x => fG (Function.update x 5 false)) s) : 11 ≤ s :=
  fG_forest_lower ∅ [(0, 1), (0, 2), (2, 3), (3, 4), (6, 7), (7, 1), (0, 8), (1, 9)]
    {s(0, 8), s(3, 4), s(1, 9), s(6, 7)} par5 dep5 5 false 11 s
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun x => by simp [fG, Function.update]; tauto) hs

theorem fG_true_5 (s : ℕ) (hs : HasCircuitSize 10 (fun x => fG (Function.update x 5 true)) s) : 10 ≤ s :=
  fG_forest_lower {4, 6} [(0, 1), (0, 2), (2, 3), (7, 1), (0, 8), (1, 9)]
    {s(0, 8), s(2, 3), s(1, 9)} par5 dep5 5 true 10 s
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun x => by simp [fG, Function.update]; tauto) hs

theorem fG_false_6 (s : ℕ) (hs : HasCircuitSize 10 (fun x => fG (Function.update x 6 false)) s) : 11 ≤ s :=
  fG_forest_lower ∅ [(0, 1), (0, 2), (2, 3), (3, 4), (4, 5), (7, 1), (0, 8), (1, 9)]
    {s(0, 8), s(2, 3), s(4, 5), s(1, 9)} par6 dep6 6 false 11 s
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun x => by simp [fG, Function.update]; tauto) hs

theorem fG_true_6 (s : ℕ) (hs : HasCircuitSize 10 (fun x => fG (Function.update x 6 true)) s) : 10 ≤ s :=
  fG_forest_lower {5, 7} [(0, 1), (0, 2), (2, 3), (3, 4), (0, 8), (1, 9)]
    {s(0, 8), s(3, 4), s(1, 9)} par6 dep6 6 true 10 s
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun x => by simp [fG, Function.update]; tauto) hs

def Sset : Finset (Fin 10) := {3, 4, 5, 6}
def Tset : Finset (Fin 10) := {0, 1, 2, 7, 8, 9}

theorem mem_Tset_iff (i : Fin 10) : i ∈ Tset ↔ i ∉ Sset := by
  fin_cases i <;> decide

theorem fG_false_lower (v : Fin 10) (hv : v ∈ Sset) (s : ℕ)
    (hs : HasCircuitSize 10 (fun x => fG (Function.update x v false)) s) : 11 ≤ s := by
  fin_cases v <;> simp [Sset] at hv
  · exact fG_false_3 s hs
  · exact fG_false_4 s hs
  · exact fG_false_5 s hs
  · exact fG_false_6 s hs

theorem fG_true_lower (v : Fin 10) (hv : v ∈ Sset) (s : ℕ)
    (hs : HasCircuitSize 10 (fun x => fG (Function.update x v true)) s) : 10 ≤ s := by
  fin_cases v <;> simp [Sset] at hv
  · exact fG_true_3 s hs
  · exact fG_true_4 s hs
  · exact fG_true_5 s hs
  · exact fG_true_6 s hs

theorem fG_nc_fix (v : Fin 10) (hv : v ∈ Sset) (b : Bool) :
    ∃ x y : Fin 10 → Bool, fG (Function.update x v b) ≠ fG (Function.update y v b) := by
  refine ⟨fun _ => false, fun i => decide (i = 0 ∨ i = 8), ?_⟩
  fin_cases v <;> simp [Sset] at hv <;> cases b <;> decide

theorem fG_dep_S (v : Fin 10) (hv : v ∈ Sset) :
    ∃ x : Fin 10 → Bool, fG (Function.update x v (!x v)) ≠ fG x := by
  fin_cases v <;> simp [Sset] at hv
  · exact ⟨fun i => decide (i = 2), by decide⟩
  · exact ⟨fun i => decide (i = 3), by decide⟩
  · exact ⟨fun i => decide (i = 4), by decide⟩
  · exact ⟨fun i => decide (i = 5), by decide⟩

theorem fG_dep_after_fix (u v : Fin 10) (hu : u ∈ Sset) (hv : v ∈ Sset) (huv : u ≠ v) (bu : Bool) :
    ∃ x : Fin 10 → Bool, x u = bu ∧ fG (Function.update x v false) ≠ fG (Function.update x v true) := by
  fin_cases u <;> simp [Sset] at hu <;> fin_cases v <;> simp [Sset] at hv
  all_goals first
    | exact (huv rfl).elim
    | (cases bu
       · first
         | exact ⟨fun i => decide (i = 2), by decide, by decide⟩
         | exact ⟨fun i => decide (i = 3), by decide, by decide⟩
         | exact ⟨fun i => decide (i = 4), by decide, by decide⟩
         | exact ⟨fun i => decide (i = 5), by decide, by decide⟩
         | exact ⟨fun i => decide (i = 6), by decide, by decide⟩
         | exact ⟨fun i => decide (i = 7), by decide, by decide⟩
       · first
         | exact ⟨fun i => decide (i = 3), by decide, by decide⟩
         | exact ⟨fun i => decide (i = 4), by decide, by decide⟩
         | exact ⟨fun i => decide (i = 5), by decide, by decide⟩
         | exact ⟨fun i => decide (i = 6), by decide, by decide⟩
         | exact ⟨fun i => decide (i = 3 ∨ i = 6), by decide, by decide⟩
         | exact ⟨fun i => decide (i = 3 ∨ i = 7), by decide, by decide⟩
         | exact ⟨fun i => decide (i = 4 ∨ i = 7), by decide, by decide⟩
         | exact ⟨fun i => decide (i = 5 ∨ i = 2), by decide, by decide⟩
         | exact ⟨fun i => decide (i = 6 ∨ i = 2), by decide, by decide⟩
         | exact ⟨fun i => decide (i = 6 ∨ i = 3), by decide, by decide⟩)

def fGT (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 7 && x 1) || (x 0 && x 8) || (x 1 && x 9)

theorem fG_of_fGT (x : Fin 10 → Bool) (h : fGT x = true) : fG x = true := by
  simp only [fGT, fG, Bool.or_eq_true] at h ⊢
  tauto

theorem fG_extend_aux (v : Fin 10) (hv : v ∈ Sset) (b0 b1 b2 b7 b8 b9 : Bool)
    (h0 : ((b0 && b1) || (b0 && b2) || (b7 && b1) || (b0 && b8) || (b1 && b9)) = false) :
    let u : Fin 10 := if v = 3 ∨ v = 5 then 4 else 5
    let y : Fin 10 → Bool := fun i =>
      if i = 0 then b0 else if i = 1 then b1 else if i = 2 then b2 else
      if i = 7 then b7 else if i = 8 then b8 else if i = 9 then b9 else decide (i = u)
    fG (Function.update y v false) = false ∧ fG (Function.update y v true) = true := by
  revert v hv b0 b1 b2 b7 b8 b9 h0
  decide

theorem fG_extend_S (x : Fin 10 → Bool) (h0 : fGT x = false) (v : Fin 10) (hv : v ∈ Sset) :
    ∃ y : Fin 10 → Bool, (∀ i ∈ Tset, y i = x i) ∧
      fG (Function.update y v false) = false ∧ fG (Function.update y v true) = true := by
  let u : Fin 10 := if v = 3 ∨ v = 5 then 4 else 5
  let y : Fin 10 → Bool := fun i =>
    if i = 0 then x 0 else if i = 1 then x 1 else if i = 2 then x 2 else
    if i = 7 then x 7 else if i = 8 then x 8 else if i = 9 then x 9 else decide (i = u)
  have haux := fG_extend_aux v hv (x 0) (x 1) (x 2) (x 7) (x 8) (x 9) h0
  refine ⟨y, ?_, haux.1, haux.2⟩
  intro i hi
  fin_cases i <;> simp [Tset] at hi <;> rfl

theorem fG_nc_on_fGT_false :
    ∃ x y : Fin 10 → Bool, fGT x = false ∧ fGT y = false ∧ fG x ≠ fG y :=
  ⟨fun _ => false, fun i => decide (i = 3 ∨ i = 4), by decide, by decide, by decide⟩

def HasTopOrs (C : Circuit) (k : ℕ) : Prop :=
  k ≤ C.gates.length ∧
  (k = 0 ∨ (C.output = 10 + C.gates.length - 1 ∧
    ∃ o0 < 10 + (C.gates.length - k),
      ∀ i (hi : i < (C.gates.drop (C.gates.length - k)).length),
        ∃ h < 10 + (C.gates.take (C.gates.length - k)).length,
          (suppsFrom (C.gates.take (C.gates.length - k)) (inputSupps 10)).getD h ∅ ⊆ Tset ∧
          (C.gates.drop (C.gates.length - k))[i] =
            ⟨GateOp.or, [h, if i = 0 then o0 else 10 + (C.gates.take (C.gates.length - k)).length + i - 1]⟩))

theorem elim_take_step_eq (n : ℕ) (gs : List Gate) (st0 : List Stat × List Gate) (t : ℕ)
    (ht : t < gs.length) :
    (elim n (gs.take (t + 1)) st0).1.getD (st0.1.length + t) (Sum.inl false) =
      (simplify (gs[t]).op (n + (elim n (gs.take t) st0).2.length)
        ((gs[t]).inputs.map fun i => (elim n (gs.take t) st0).1.getD i (Sum.inl false))).2 := by
  rw [List.take_succ_eq_append_getElem ht, elim_append]
  set st := elim n (gs.take t) st0 with hst
  have hlen : st.1.length = st0.1.length + t := by
    obtain ⟨l1, _, h1, _, hl1, _⟩ := elim_prefix n (gs.take t) st0
    rw [hst, h1, List.length_append, hl1, List.length_take, Nat.min_eq_left ht.le]
  change (st.1 ++ [(simplify (gs[t]).op (n + st.2.length)
    ((gs[t]).inputs.map fun i => st.1.getD i (Sum.inl false))).2]).getD (st0.1.length + t) (Sum.inl false) = _
  rw [← hlen, getD_snoc_eq]

theorem elim_take_const_persist (n : ℕ) (gs : List Gate) (st0 : List Stat × List Gate)
    (t t' : ℕ) (c : Bool) (htt : t < t')
    (hc : (elim n (gs.take (t + 1)) st0).1.getD (st0.1.length + t) (Sum.inl false) = Sum.inl c) :
    (elim n (gs.take t') st0).1.getD (st0.1.length + t) (Sum.inl false) = Sum.inl c := by
  have htake : gs.take t' = gs.take (t + 1) ++ (gs.take t').drop (t + 1) := by
    conv_lhs => rw [← List.take_append_drop (t + 1) (gs.take t'), List.take_take, Nat.min_eq_left (by omega)]
  by_cases ht : t < gs.length
  · have hlen : (elim n (gs.take (t + 1)) st0).1.length = st0.1.length + (t + 1) := by
      obtain ⟨l1, _, h1, _, hl1, _⟩ := elim_prefix n (gs.take (t + 1)) st0
      rw [h1, List.length_append, hl1, List.length_take, Nat.min_eq_left (by omega)]
    rw [htake, elim_append]
    obtain ⟨l2, _, h2, _, _, _⟩ := elim_prefix n ((gs.take t').drop (t + 1)) _
    rw [h2, List.getD_append _ _ _ _ (by omega), hc]
  · have h1 : gs.take t' = gs.take (t + 1) := by
      rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
    rw [h1, hc]

theorem getD_ofFn_fin {α : Type} {n : ℕ} (f : Fin n → α) (i : Fin n) (d : α) :
    (List.ofFn f).getD i.val d = f i := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt]

theorem fanout_S_eq_one (C : Circuit) (hfan : FanInTwo C) (hnok : ∀ g ∈ C.gates, NOk g)
    (heval : ∀ x, C.eval (List.ofFn x) = fG x)
    (hmin : ∀ D : Circuit, FanInTwo D → (∀ x, D.eval (List.ofFn x) = fG x) → C.size ≤ D.size)
    (hs13 : C.size ≤ 13) (v : Fin 10) (hv : v ∈ Sset) :
    ∃ t1, ∃ ht1 : t1 < C.gates.length,
      v.val ∈ (C.gates[t1]).inputs ∧
      (∀ t, (ht : t < C.gates.length) → v.val ∈ (C.gates[t]).inputs → t = t1) ∧
      ((C.gates[t1]).op = GateOp.not →
        ∃ t2, ∃ ht2 : t2 < C.gates.length,
          10 + t1 ∈ (C.gates[t2]).inputs ∧
          (∀ t, (ht : t < C.gates.length) → 10 + t1 ∈ (C.gates[t]).inputs → t = t2) ∧
          ((C.gates[t2]).op = GateOp.and ∨ (C.gates[t2]).op = GateOp.or)) := by
  have hmap : C.gates.map normGate = C.gates := by
    apply List.ext_getElem (by simp)
    intro i hi _
    rw [List.getElem_map]
    have hg := hnok C.gates[i] (List.getElem_mem (by simpa using hi))
    cases hgi : C.gates[i] with
    | mk op ins =>
      cases op <;> simp [normGate]
      have hlen := hg.2 (by simp [hgi])
      simp [hgi] at hlen
      exact hlen
  have hncf : ∃ x y, fG x ≠ fG y := by
    obtain ⟨x, hx⟩ := fG_dep_S v hv; exact ⟨_, _, hx⟩
  have hdepC : ∃ x, C.eval (List.ofFn (Function.update x v (!x v))) ≠ C.eval (List.ofFn x) := by
    obtain ⟨x, hx⟩ := fG_dep_S v hv; exact ⟨x, by rwa [heval, heval]⟩
  have hncC : ∀ b : Bool, ∃ x y,
      C.eval (List.ofFn (Function.update x v b)) ≠ C.eval (List.ofFn (Function.update y v b)) := by
    intro b; obtain ⟨x, y, hxy⟩ := fG_nc_fix v hv b; exact ⟨x, y, by rwa [heval, heval]⟩
  have hseed : ∀ (b : Bool) (t : ℕ),
      (elim 10 (C.gates.take t) (seedInput 10 v b, [])).1.getD v.val (Sum.inl false) = Sum.inl b := by
    intro b t
    obtain ⟨l1, _, h1, _, _, _⟩ := elim_prefix 10 (C.gates.take t) (seedInput 10 v b, [])
    rw [h1, List.getD_append _ _ _ _ (by simp [seedInput, v.isLt])]
    rw [seedInput, getD_ofFn_fin]; simp
  have hlen_seed : ∀ (b : Bool), (seedInput 10 v b).length = 10 := fun b => by simp [seedInput]
  have hkill : ∀ (b : Bool) (K : Finset ℕ),
      (∀ t ∈ K, ∃ ht : t < C.gates.length, ∃ i ∈ (C.gates[t]).inputs, ∃ c,
        (elim 10 (C.gates.take t) (seedInput 10 v b, [])).1.getD i (Sum.inl false) = Sum.inl c) →
      (b = false → 3 ≤ K.card → False) ∧ (b = true → 4 ≤ K.card → False) := by
    intro b K hK
    have hres := elim_const_of_input_mem C hfan v b (hncC b) K (by
      intro t ht; obtain ⟨hlt, i, hi, c, hc⟩ := hK t ht
      exact ⟨hlt, i, by simpa [hmap] using hi, c, by simpa [hmap] using hc⟩)
    have hres' : HasCircuitSize 10 (fun x => fG (Function.update x v b)) (C.size - K.card) := by
      obtain ⟨D, hDf, hDs, hDe⟩ := hres
      exact ⟨D, hDf, hDs, fun x => by dsimp only; rw [hDe x]; exact heval _⟩
    constructor
    · rintro rfl h3
      have h11 := fG_false_lower v hv _ hres'
      omega
    · rintro rfl h4
      have h10 := fG_true_lower v hv _ hres'
      omega
  have hhas_reader : ∀ (t : ℕ) (ht : t < C.gates.length) (b c : Bool),
      (elim 10 (C.gates.take (t + 1)) (seedInput 10 v b, [])).1.getD (10 + t) (Sum.inl false) = Sum.inl c →
      ∃ t', ∃ ht' : t' < C.gates.length, t < t' ∧ 10 + t ∈ (C.gates[t']).inputs := by
    intro t ht b c hc
    rcases min_no_dead hfan heval hmin t ht with ho | ⟨t', ht', hlt, hmem⟩
    · exfalso
      obtain ⟨x, y, hxy⟩ := hncC b
      have hx := inv_elim 10 C.gates (fun g hg => (hnok g hg).1) _ _ _ (seedInput_inv v b x)
      have hy := inv_elim 10 C.gates (fun g hg => (hnok g hg).1) _ _ _ (seedInput_inv v b y)
      have hce : (elim 10 C.gates (seedInput 10 v b, [])).1.getD (10 + t) (Sum.inl false) = Sum.inl c := by
        have h1 := elim_take_const_persist 10 C.gates (seedInput 10 v b, []) t C.gates.length c ht
          (by simpa [seedInput] using hc)
        rw [List.take_of_length_le le_rfl] at h1
        simpa [seedInput] using h1
      have hx1 := (hx.2.2 (10 + t)).2
      have hy1 := (hy.2.2 (10 + t)).2
      rw [hce] at hx1 hy1
      apply hxy
      simp only [Circuit.eval, wires_eq, ho, ← hx1, ← hy1, Stat.val]
    · exact ⟨t', ht', hlt, hmem⟩
  have hconst_of_read : ∀ (t : ℕ) (ht : t < C.gates.length) (i : ℕ) (b c : Bool),
      i ∈ (C.gates[t]).inputs →
      (elim 10 (C.gates.take t) (seedInput 10 v b, [])).1.getD i (Sum.inl false) = Sum.inl c →
      ((C.gates[t]).op = GateOp.not →
        (elim 10 (C.gates.take (t + 1)) (seedInput 10 v b, [])).1.getD (10 + t) (Sum.inl false) = Sum.inl (!c)) ∧
      ((C.gates[t]).op = GateOp.and → c = false →
        (elim 10 (C.gates.take (t + 1)) (seedInput 10 v b, [])).1.getD (10 + t) (Sum.inl false) = Sum.inl false) ∧
      ((C.gates[t]).op = GateOp.or → c = true →
        (elim 10 (C.gates.take (t + 1)) (seedInput 10 v b, [])).1.getD (10 + t) (Sum.inl false) = Sum.inl true) := by
    intro t ht i b c hi hst
    have hshape := min_gate_shape hfan heval hnok hmin hncf t ht
    have hstep := elim_take_step_eq 10 C.gates (seedInput 10 v b, []) t ht
    rw [hlen_seed b] at hstep
    refine ⟨?_, ?_, ?_⟩
    · intro hop
      rcases hshape with ⟨_, a, hl, _⟩ | ⟨h | h, _⟩
      · have : a = i := by rw [hl] at hi; simpa [eq_comm] using hi
        subst this
        rw [hstep, hop, hl]; simp only [List.map_cons, List.map_nil, hst, simplify, simpNot]
      · rw [hop] at h; cases h
      · rw [hop] at h; cases h
    · intro hop hc
      subst hc
      rcases hshape with ⟨h, _⟩ | ⟨_, a, d, hl, _, _, _⟩
      · rw [hop] at h; cases h
      · rw [hl] at hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · rw [hstep, hop, hl]; simp only [List.map_cons, List.map_nil, hst, simplify]
          cases (elim 10 (C.gates.take t) (seedInput 10 v b, [])).1.getD d (Sum.inl false) <;> simp [simpAnd]
        · rw [hstep, hop, hl]; simp only [List.map_cons, List.map_nil, hst, simplify]
          cases (elim 10 (C.gates.take t) (seedInput 10 v b, [])).1.getD a (Sum.inl false) <;> simp [simpAnd]
    · intro hop hc
      subst hc
      rcases hshape with ⟨h, _⟩ | ⟨_, a, d, hl, _, _, _⟩
      · rw [hop] at h; cases h
      · rw [hl] at hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · rw [hstep, hop, hl]; simp only [List.map_cons, List.map_nil, hst, simplify]
          cases (elim 10 (C.gates.take t) (seedInput 10 v b, [])).1.getD d (Sum.inl false) <;> simp [simpOr]
        · rw [hstep, hop, hl]; simp only [List.map_cons, List.map_nil, hst, simplify]
          cases (elim 10 (C.gates.take t) (seedInput 10 v b, [])).1.getD a (Sum.inl false) <;> simp [simpOr]
  rcases has_reader_of_dep C v hdepC with ho | ⟨t1, ht1, hmem1_raw⟩
  · exfalso
    obtain ⟨x, y, hxy⟩ := hncC false
    apply hxy
    simp only [Circuit.eval, wires_eq, ho]
    rw [getD_wiresFrom _ _ _ (by simp [v.isLt]), getD_wiresFrom _ _ _ (by simp [v.isLt])]
    rw [getD_ofFn_fin, getD_ofFn_fin]; simp
  have hmem1 : v.val ∈ (C.gates[t1]).inputs := by simpa [hmap] using hmem1_raw
  clear hmem1_raw
  have huniq1 : ∀ t, (ht : t < C.gates.length) → v.val ∈ (C.gates[t]).inputs → t = t1 := by
    intro t2 ht2 hmem2
    by_contra hne
    wlog hlt : t1 < t2 generalizing t1 t2 ht1 hmem1 ht2 hmem2
    · exact this t2 ht2 hmem2 t1 ht1 hmem1 (Ne.symm hne) (by omega)
    have hnot_const0 : ∀ (t : ℕ) (ht : t < C.gates.length), v.val ∈ (C.gates[t]).inputs →
        ∀ c, (elim 10 (C.gates.take (t + 1)) (seedInput 10 v false, [])).1.getD (10 + t) (Sum.inl false) ≠ Sum.inl c := by
      intro t ht hmt c hc
      obtain ⟨t3, ht3, hlt3, hmem3⟩ := hhas_reader t ht false c hc
      have hpers : ∀ u > t, (elim 10 (C.gates.take u) (seedInput 10 v false, [])).1.getD (10 + t) (Sum.inl false) = Sum.inl c :=
        fun u hu => by
          have := elim_take_const_persist 10 C.gates (seedInput 10 v false, []) t u c hu (by rw [hlen_seed]; exact hc)
          rwa [hlen_seed] at this
      by_cases ht_eq : t = t1
      · subst t
        by_cases h32 : t3 = t2
        · subst t3
          have hshape2 := min_gate_shape hfan heval hnok hmin hncf t2 ht2
          have hstep2 := elim_take_step_eq 10 C.gates (seedInput 10 v false, []) t2 ht2
          rw [hlen_seed false] at hstep2
          have hc2 : ∃ c2, (elim 10 (C.gates.take (t2 + 1)) (seedInput 10 v false, [])).1.getD (10 + t2) (Sum.inl false) = Sum.inl c2 := by
            rcases hshape2 with ⟨hop2, a, hl2, _⟩ | ⟨hop2 | hop2, a, d, hl2, _, _, _⟩
            · rw [hl2] at hmem2 hmem3
              simp only [List.mem_singleton] at hmem2 hmem3
              omega
            · rw [hl2] at hmem2 hmem3
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem2 hmem3
              rcases hmem2 with rfl | rfl <;> rcases hmem3 with h3a | h3b
              · omega
              · subst h3b; refine ⟨false && c, ?_⟩; rw [hstep2, hop2, hl2]; simp only [List.map_cons, List.map_nil, hseed, hpers t2 hlt, simplify, simpAnd]
              · subst h3a; refine ⟨c && false, ?_⟩; rw [hstep2, hop2, hl2]; simp only [List.map_cons, List.map_nil, hseed, hpers t2 hlt, simplify, simpAnd]
              · omega
            · rw [hl2] at hmem2 hmem3
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem2 hmem3
              rcases hmem2 with rfl | rfl <;> rcases hmem3 with h3a | h3b
              · omega
              · subst h3b; refine ⟨false || c, ?_⟩; rw [hstep2, hop2, hl2]; simp only [List.map_cons, List.map_nil, hseed, hpers t2 hlt, simplify, simpOr]
              · subst h3a; refine ⟨c || false, ?_⟩; rw [hstep2, hop2, hl2]; simp only [List.map_cons, List.map_nil, hseed, hpers t2 hlt, simplify, simpOr]
              · omega
          obtain ⟨c2, hc2⟩ := hc2
          obtain ⟨t4, ht4, hlt4, hmem4⟩ := hhas_reader t2 ht2 false c2 hc2
          have hcard3 : ({t1, t2, t4} : Finset ℕ).card = 3 := by
            rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_pair (by omega)]
          exact (hkill false {t1, t2, t4} (by
            intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
            rcases hu with hu | hu | hu <;> subst u
            · exact ⟨ht1, v.val, hmem1, false, hseed false t1⟩
            · exact ⟨ht2, v.val, hmem2, false, hseed false t2⟩
            · exact ⟨ht4, 10 + t2, hmem4, c2, by
                have := elim_take_const_persist 10 C.gates (seedInput 10 v false, []) t2 t4 c2 hlt4 (by rw [hlen_seed]; exact hc2)
                rwa [hlen_seed] at this⟩)).1 rfl (by omega)
        · have hcard3 : ({t1, t2, t3} : Finset ℕ).card = 3 := by
            rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_pair (by omega)]
          exact (hkill false {t1, t2, t3} (by
            intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
            rcases hu with hu | hu | hu <;> subst u
            · exact ⟨ht1, v.val, hmem1, false, hseed false t1⟩
            · exact ⟨ht2, v.val, hmem2, false, hseed false t2⟩
            · exact ⟨ht3, 10 + t1, hmem3, c, hpers t3 hlt3⟩)).1 rfl (by omega)
      · have ht_eq2 : t = t2 := by
          by_contra hnt2
          have hcard3 : ({t1, t2, t} : Finset ℕ).card = 3 := by
            rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_pair (by omega)]
          exact (hkill false {t1, t2, t} (by
            intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
            rcases hu with hu | hu | hu <;> subst u
            · exact ⟨ht1, v.val, hmem1, false, hseed false t1⟩
            · exact ⟨ht2, v.val, hmem2, false, hseed false t2⟩
            · exact ⟨ht, v.val, hmt, false, hseed false t⟩)).1 rfl (by omega)
        subst t
        have hcard3 : ({t1, t2, t3} : Finset ℕ).card = 3 := by
          rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_pair (by omega)]
        exact (hkill false {t1, t2, t3} (by
          intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with hu | hu | hu <;> subst u
          · exact ⟨ht1, v.val, hmem1, false, hseed false t1⟩
          · exact ⟨ht2, v.val, hmem2, false, hseed false t2⟩
          · exact ⟨ht3, 10 + t2, hmem3, c, hpers t3 hlt3⟩)).1 rfl (by omega)
    have hor1 : (C.gates[t1]).op = GateOp.or := by
      rcases min_gate_shape hfan heval hnok hmin hncf t1 ht1 with ⟨hop, _⟩ | ⟨hop | hop, _⟩
      · exact (hnot_const0 t1 ht1 hmem1 true ((hconst_of_read t1 ht1 v.val false false hmem1 (hseed false t1)).1 hop)).elim
      · exact (hnot_const0 t1 ht1 hmem1 false ((hconst_of_read t1 ht1 v.val false false hmem1 (hseed false t1)).2.1 hop rfl)).elim
      · exact hop
    have hor2 : (C.gates[t2]).op = GateOp.or := by
      rcases min_gate_shape hfan heval hnok hmin hncf t2 ht2 with ⟨hop, _⟩ | ⟨hop | hop, _⟩
      · exact (hnot_const0 t2 ht2 hmem2 true ((hconst_of_read t2 ht2 v.val false false hmem2 (hseed false t2)).1 hop)).elim
      · exact (hnot_const0 t2 ht2 hmem2 false ((hconst_of_read t2 ht2 v.val false false hmem2 (hseed false t2)).2.1 hop rfl)).elim
      · exact hop
    have hc1 : (elim 10 (C.gates.take (t1 + 1)) (seedInput 10 v true, [])).1.getD (10 + t1) (Sum.inl false) = Sum.inl true :=
      (hconst_of_read t1 ht1 v.val true true hmem1 (hseed true t1)).2.2 hor1 rfl
    have hc2 : (elim 10 (C.gates.take (t2 + 1)) (seedInput 10 v true, [])).1.getD (10 + t2) (Sum.inl false) = Sum.inl true :=
      (hconst_of_read t2 ht2 v.val true true hmem2 (hseed true t2)).2.2 hor2 rfl
    have hpers1 : ∀ u > t1, (elim 10 (C.gates.take u) (seedInput 10 v true, [])).1.getD (10 + t1) (Sum.inl false) = Sum.inl true :=
      fun u hu => by
        have := elim_take_const_persist 10 C.gates (seedInput 10 v true, []) t1 u true hu (by rw [hlen_seed]; exact hc1)
        rwa [hlen_seed] at this
    have hpers2 : ∀ u > t2, (elim 10 (C.gates.take u) (seedInput 10 v true, [])).1.getD (10 + t2) (Sum.inl false) = Sum.inl true :=
      fun u hu => by
        have := elim_take_const_persist 10 C.gates (seedInput 10 v true, []) t2 u true hu (by rw [hlen_seed]; exact hc2)
        rwa [hlen_seed] at this
    obtain ⟨h1, hh1, hlt1, hmem_h1⟩ := hhas_reader t1 ht1 true true hc1
    obtain ⟨h2, hh2, hlt2, hmem_h2⟩ := hhas_reader t2 ht2 true true hc2
    by_cases h12 : h1 = t2
    · subst h1
      rcases min_gate_shape hfan heval hnok hmin hncf t1 ht1 with ⟨hop, _⟩ | ⟨_, a1, b1, hl1, ha1, hb1, hab1⟩
      · rw [hor1] at hop; cases hop
      rcases min_gate_shape hfan heval hnok hmin hncf t2 ht2 with ⟨hop, _⟩ | ⟨_, a2, b2, hl2, ha2, hb2, hab2⟩
      · rw [hor2] at hop; cases hop
      exfalso
      apply min_no_copy hfan heval hmin t2 ht2 (10 + t1) (Or.inl (by omega))
      intro x
      have hv1 := gate_value C.gates (List.ofFn x) t1 ht1
      have hv2 := gate_value C.gates (List.ofFn x) t2 ht2
      simp only [List.length_ofFn] at hv1 hv2
      rw [hv2, hor2, hl2]
      rw [hl2] at hmem2 hmem_h1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem2 hmem_h1
      rw [hl1] at hmem1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem1
      have hv1' : (wiresFrom C.gates (List.ofFn x)).getD (10 + t1) false =
          ((wiresFrom C.gates (List.ofFn x)).getD a1 false || (wiresFrom C.gates (List.ofFn x)).getD b1 false) := by
        rw [hv1, hor1, hl1]; simp [GateOp.eval, ha1, hb1]
      rcases hmem2 with rfl | rfl <;> rcases hmem_h1 with h_eq | h_eq
      · omega
      · subst h_eq; simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
          Bool.or_false, ha2, hb2, ↓reduceIte, hv1']
        rcases hmem1 with rfl | rfl <;> cases (wiresFrom C.gates (List.ofFn x)).getD v.val false <;>
          simp
      · subst h_eq; simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
          Bool.or_false, ha2, hb2, ↓reduceIte, hv1']
        rcases hmem1 with rfl | rfl <;> cases (wiresFrom C.gates (List.ofFn x)).getD v.val false <;>
          simp
      · omega
    · by_cases hh12 : h1 = h2
      · subst h2
        have hshape_h1 := min_gate_shape hfan heval hnok hmin hncf h1 hh1
        have hstep_h1 := elim_take_step_eq 10 C.gates (seedInput 10 v true, []) h1 hh1
        rw [hlen_seed true] at hstep_h1
        have hch1 : ∃ c3, (elim 10 (C.gates.take (h1 + 1)) (seedInput 10 v true, [])).1.getD (10 + h1) (Sum.inl false) = Sum.inl c3 := by
          rcases hshape_h1 with ⟨hop, a, hl, _⟩ | ⟨hop | hop, a, d, hl, _, _, _⟩
          · rw [hl] at hmem_h1 hmem_h2; simp only [List.mem_singleton] at hmem_h1 hmem_h2; omega
          · rw [hl] at hmem_h1 hmem_h2; simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem_h1 hmem_h2
            rcases hmem_h1 with rfl | rfl <;> rcases hmem_h2 with h2a | h2b
            · omega
            · subst h2b; refine ⟨true, ?_⟩; rw [hstep_h1, hop, hl]; simp only [List.map_cons, List.map_nil, hpers1 h1 hlt1, hpers2 h1 hlt2, simplify, simpAnd]; rfl
            · subst h2a; refine ⟨true, ?_⟩; rw [hstep_h1, hop, hl]; simp only [List.map_cons, List.map_nil, hpers1 h1 hlt1, hpers2 h1 hlt2, simplify, simpAnd]; rfl
            · omega
          · rw [hl] at hmem_h1 hmem_h2; simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem_h1 hmem_h2
            rcases hmem_h1 with rfl | rfl <;> rcases hmem_h2 with h2a | h2b
            · omega
            · subst h2b; refine ⟨true, ?_⟩; rw [hstep_h1, hop, hl]; simp only [List.map_cons, List.map_nil, hpers1 h1 hlt1, hpers2 h1 hlt2, simplify, simpOr]; rfl
            · subst h2a; refine ⟨true, ?_⟩; rw [hstep_h1, hop, hl]; simp only [List.map_cons, List.map_nil, hpers1 h1 hlt1, hpers2 h1 hlt2, simplify, simpOr]; rfl
            · omega
        obtain ⟨c3, hch1⟩ := hch1
        obtain ⟨k, hk, hltk, hmem_k⟩ := hhas_reader h1 hh1 true c3 hch1
        have hcard4 : ({t1, t2, h1, k} : Finset ℕ).card = 4 := by
          rw [Finset.card_insert_of_notMem (by simp; omega),
            Finset.card_insert_of_notMem (by simp; omega), Finset.card_pair (by omega)]
        exact (hkill true {t1, t2, h1, k} (by
          intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with hu | hu | hu | hu <;> subst u
          · exact ⟨ht1, v.val, hmem1, true, hseed true t1⟩
          · exact ⟨ht2, v.val, hmem2, true, hseed true t2⟩
          · exact ⟨hh1, 10 + t1, hmem_h1, true, hpers1 h1 hlt1⟩
          · exact ⟨hk, 10 + h1, hmem_k, c3, by
              have := elim_take_const_persist 10 C.gates (seedInput 10 v true, []) h1 k c3 hltk (by rw [hlen_seed]; exact hch1)
              rwa [hlen_seed] at this⟩)).2 rfl (by omega)
      · have hcard4 : ({t1, t2, h1, h2} : Finset ℕ).card = 4 := by
          rw [Finset.card_insert_of_notMem (by simp; omega),
            Finset.card_insert_of_notMem (by simp; omega), Finset.card_pair hh12]
        exact (hkill true {t1, t2, h1, h2} (by
          intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with hu | hu | hu | hu <;> subst u
          · exact ⟨ht1, v.val, hmem1, true, hseed true t1⟩
          · exact ⟨ht2, v.val, hmem2, true, hseed true t2⟩
          · exact ⟨hh1, 10 + t1, hmem_h1, true, hpers1 h1 hlt1⟩
          · exact ⟨hh2, 10 + t2, hmem_h2, true, hpers2 h2 hlt2⟩)).2 rfl (by omega)
  refine ⟨t1, ht1, hmem1, huniq1, ?_⟩
  intro hnot1
  have hc1 : (elim 10 (C.gates.take (t1 + 1)) (seedInput 10 v false, [])).1.getD (10 + t1) (Sum.inl false) = Sum.inl true :=
    (hconst_of_read t1 ht1 v.val false false hmem1 (hseed false t1)).1 hnot1
  have hpers1 : ∀ u > t1, (elim 10 (C.gates.take u) (seedInput 10 v false, [])).1.getD (10 + t1) (Sum.inl false) = Sum.inl true :=
    fun u hu => by
      have := elim_take_const_persist 10 C.gates (seedInput 10 v false, []) t1 u true hu (by rw [hlen_seed]; exact hc1)
      rwa [hlen_seed] at this
  obtain ⟨t2, ht2, hlt12, hmem2⟩ := hhas_reader t1 ht1 false true hc1
  have huniq2 : ∀ t, (ht : t < C.gates.length) → 10 + t1 ∈ (C.gates[t]).inputs → t = t2 := by
    intro t3 ht3 hmem3
    by_contra hne
    have hlt13 : t1 < t3 := by
      rcases min_gate_shape hfan heval hnok hmin hncf t3 ht3 with ⟨_, a, hl, ha⟩ | ⟨_, a, d, hl, ha, hd, _⟩
      · rw [hl] at hmem3; simp only [List.mem_singleton] at hmem3; omega
      · rw [hl] at hmem3; simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem3
        rcases hmem3 with h | h <;> omega
    have hcard3 : ({t1, t2, t3} : Finset ℕ).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_pair (Ne.symm hne)]
    exact (hkill false {t1, t2, t3} (by
      intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with hu | hu | hu <;> subst u
      · exact ⟨ht1, v.val, hmem1, false, hseed false t1⟩
      · exact ⟨ht2, 10 + t1, hmem2, true, hpers1 t2 hlt12⟩
      · exact ⟨ht3, 10 + t1, hmem3, true, hpers1 t3 hlt13⟩)).1 rfl (by omega)
  refine ⟨t2, ht2, hmem2, huniq2, ?_⟩
  rcases min_gate_shape hfan heval hnok hmin hncf t2 ht2 with ⟨hnot2, a2, hl2, ha2⟩ | ⟨hop2, _⟩
  · exfalso
    have ha2' : a2 = 10 + t1 := by rw [hl2] at hmem2; simpa [eq_comm] using hmem2
    subst ha2'
    rcases min_gate_shape hfan heval hnok hmin hncf t1 ht1 with ⟨_, a1, hl1, _⟩ | ⟨h | h, _⟩
    · have ha1' : a1 = v.val := by rw [hl1] at hmem1; simpa [eq_comm] using hmem1
      subst ha1'
      apply min_no_copy hfan heval hmin t2 ht2 v.val (Or.inl (by have := v.isLt; omega))
      intro x
      have hv1 := gate_value C.gates (List.ofFn x) t1 ht1
      have hv2 := gate_value C.gates (List.ofFn x) t2 ht2
      simp only [List.length_ofFn] at hv1 hv2
      rw [hv2, hnot2, hl2]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons, ha2, ↓reduceIte]
      rw [hv1, hnot1, hl1]
      simp [GateOp.eval, show v.val < 10 + t1 by have := v.isLt; omega]
    · rw [hnot1] at h; cases h
    · rw [hnot1] at h; cases h
  · exact hop2

theorem simplify_nok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, NOk g := by
  intro g hg
  have hok := simplify_ok op m ins g hg
  refine ⟨hok, ?_⟩
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp [simpAnd] at hg
    · rcases a with a | a <;> simp [simpAnd] at hg
    · rcases a with a | a <;> rcases b with b | b
      · simp [simpAnd] at hg
      · cases a <;> simp [simpAnd] at hg
      · cases b <;> simp [simpAnd] at hg
      · simp [simpAnd] at hg; subst hg; simp
    · simp [simpAnd] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp [simpOr] at hg
    · rcases a with a | a <;> simp [simpOr] at hg
    · rcases a with a | a <;> rcases b with b | b
      · simp [simpOr] at hg
      · cases a <;> simp [simpOr] at hg
      · cases b <;> simp [simpOr] at hg
      · simp [simpOr] at hg; subst hg; simp
    · simp [simpOr] at hg
  · rcases ins with _ | ⟨a, l⟩
    · simp [simpNot] at hg
    · rcases a with a | a <;> simp [simpNot] at hg
      subst hg; simp
  · simp at hg
  · simp at hg

theorem elim_nok (m : ℕ) (gs : List Gate) : ∀ st : List Stat × List Gate,
    (∀ g ∈ st.2, NOk g) → ∀ g ∈ (elim m gs st).2, NOk g := by
  induction gs with
  | nil => intro st h; exact h
  | cons g gs ih =>
    intro st h
    apply ih (elimStep m st g)
    intro g' hg'
    simp only [elimStep, List.mem_append, Option.mem_toList] at hg'
    rcases hg' with hg' | hg'
    · exact h g' hg'
    · exact simplify_nok _ _ _ g' hg'

theorem elim_valid (m : ℕ) (gs : List Gate) : ∀ st : List Stat × List Gate,
    (∀ i, Stat.Valid (m + st.2.length) (st.1.getD i (Sum.inl false))) →
    ∀ i, Stat.Valid (m + (elim m gs st).2.length) ((elim m gs st).1.getD i (Sum.inl false)) := by
  induction gs with
  | nil => intro st h; exact h
  | cons g gs ih =>
    intro st h
    apply ih (elimStep m st g)
    intro i
    simp only [elimStep]
    by_cases hi : i = st.1.length
    · subst hi
      rw [getD_snoc_eq]
      have hv := simplify_valid g.op (m + st.2.length)
        (g.inputs.map fun a => st.1.getD a (Sum.inl false)) (fun s hs => by
          obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
          exact h a)
      simpa [List.length_append, Nat.add_assoc] using hv
    · rw [getD_snoc_ne _ _ _ _ hi]
      have hvi := h i
      cases hst : st.1.getD i (Sum.inl false) with
      | inl _ => trivial
      | inr j =>
        rw [hst] at hvi
        simp only [Stat.Valid, List.length_append] at hvi ⊢
        omega

theorem supp_elim_T (m : ℕ) (pre' : List Gate) (hm : 10 + pre'.length = m) :
    ∀ (gs : List Gate) (st : List Stat × List Gate) (S0 : List (Finset (Fin 10))),
      st.1.length = S0.length →
      (∀ i, Stat.Valid (m + st.2.length) (st.1.getD i (Sum.inl false))) →
      (∀ i, S0.getD i ∅ ⊆ Tset → match st.1.getD i (Sum.inl false) with
        | Sum.inl _ => True
        | Sum.inr j => (suppsFrom (pre' ++ st.2) (inputSupps 10)).getD j ∅ ⊆ Tset) →
      (∀ i, (suppsFrom gs S0).getD i ∅ ⊆ Tset → match (elim m gs st).1.getD i (Sum.inl false) with
        | Sum.inl _ => True
        | Sum.inr j => (suppsFrom (pre' ++ (elim m gs st).2) (inputSupps 10)).getD j ∅ ⊆ Tset) := by
  intro gs
  induction gs with
  | nil => intro st S0 _ _ h; exact h
  | cons g gs ih =>
    intro st S0 hlen hval hT
    rw [suppsFrom_cons, elim_cons]
    have hval' : ∀ i, Stat.Valid (m + (elimStep m st g).2.length)
        ((elimStep m st g).1.getD i (Sum.inl false)) := by
      simpa [elim_cons, elim] using elim_valid m [g] st hval
    apply ih (elimStep m st g) (S0 ++ [gateSupp S0 g]) (by simp [elimStep, hlen]) hval'
    intro i hi
    have hpre_len : (suppsFrom (pre' ++ st.2) (inputSupps 10)).length = m + st.2.length := by
      rw [length_suppsFrom, List.length_append]; simp [inputSupps, hm]; omega
    by_cases hil : i = S0.length
    · subst hil
      rw [getD_snoc_eq] at hi
      simp only [elimStep]
      rw [← hlen, getD_snoc_eq]
      set ins := g.inputs.map fun a => st.1.getD a (Sum.inl false) with hins
      set r := simplify g.op (m + st.2.length) ins with hr
      have hins_T : ∀ a ∈ g.inputs, match st.1.getD a (Sum.inl false) with
          | Sum.inl _ => True
          | Sum.inr j => (suppsFrom (pre' ++ st.2) (inputSupps 10)).getD j ∅ ⊆ Tset := by
        intro a ha
        apply hT a
        intro x hx
        exact hi ((mem_gateSupp S0 g x).2 ⟨a, ha, hx⟩)
      have hall : ∀ s ∈ ins, match s with
          | Sum.inl _ => True
          | Sum.inr j => (suppsFrom (pre' ++ st.2) (inputSupps 10)).getD j ∅ ⊆ Tset := by
        intro s hs
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hs
        exact hins_T a ha
      have hnew_T : ∀ (g' : Gate), r.1 = some g' → r.2 = Sum.inr (m + st.2.length) →
          (∀ j ∈ g'.inputs, (suppsFrom (pre' ++ st.2) (inputSupps 10)).getD j ∅ ⊆ Tset) →
          (suppsFrom (pre' ++ (st.2 ++ r.1.toList)) (inputSupps 10)).getD (m + st.2.length) ∅ ⊆ Tset := by
        intro g' hg' _ hgj
        rw [hg', Option.toList_some, ← List.append_assoc, suppsFrom_append, suppsFrom_cons]
        rw [show m + st.2.length = (suppsFrom (pre' ++ st.2) (inputSupps 10)).length by omega]
        change (suppsFrom [] _).getD _ ∅ ⊆ Tset
        simp only [suppsFrom, List.foldl_nil, getD_snoc_eq]
        intro x hx
        obtain ⟨j, hj, hxj⟩ := (mem_gateSupp _ g' x).1 hx
        exact hgj j hj hxj
      cases hop : g.op <;> simp only [hr, simplify, hop] at *
      · rcases hins' : ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
        · simp [simpAnd]
        · rcases a with a | a
          · simp [simpAnd]
          · have ha := hall (Sum.inr a) (by simp [hins'])
            simp only [simpAnd, Option.toList_none, List.append_nil]; exact ha
        · rcases a with a | a <;> rcases b with b | b
          · simp [simpAnd]
          · have hb := hall (Sum.inr b) (by simp [hins'])
            dsimp only at hb
            cases a
            · simp [simpAnd]
            · simp only [simpAnd, Bool.cond_true, Option.toList_none, List.append_nil]; exact hb
          · have ha := hall (Sum.inr a) (by simp [hins'])
            dsimp only at ha
            cases b
            · simp [simpAnd]
            · simp only [simpAnd, Bool.cond_true, Option.toList_none, List.append_nil]; exact ha
          · have ha := hall (Sum.inr a) (by simp [hins'])
            have hb := hall (Sum.inr b) (by simp [hins'])
            simp only [simpAnd]
            have := hnew_T ⟨GateOp.and, [a, b]⟩ (by simp [hr, hop, simplify, hins', simpAnd])
              (by simp [hr, hop, simplify, hins', simpAnd]) (by intro j hj; simp at hj; rcases hj with rfl | rfl <;> assumption)
            simpa [hr, hop, simplify, hins', simpAnd] using this
        · simp [simpAnd]
      · rcases hins' : ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
        · simp [simpOr]
        · rcases a with a | a
          · simp [simpOr]
          · have ha := hall (Sum.inr a) (by simp [hins'])
            simp only [simpOr, Option.toList_none, List.append_nil]; exact ha
        · rcases a with a | a <;> rcases b with b | b
          · simp [simpOr]
          · have hb := hall (Sum.inr b) (by simp [hins'])
            dsimp only at hb
            cases a
            · simp only [simpOr, Bool.cond_false, Option.toList_none, List.append_nil]; exact hb
            · simp [simpOr]
          · have ha := hall (Sum.inr a) (by simp [hins'])
            dsimp only at ha
            cases b
            · simp only [simpOr, Bool.cond_false, Option.toList_none, List.append_nil]; exact ha
            · simp [simpOr]
          · have ha := hall (Sum.inr a) (by simp [hins'])
            have hb := hall (Sum.inr b) (by simp [hins'])
            simp only [simpOr]
            have := hnew_T ⟨GateOp.or, [a, b]⟩ (by simp [hr, hop, simplify, hins', simpOr])
              (by simp [hr, hop, simplify, hins', simpOr]) (by intro j hj; simp at hj; rcases hj with rfl | rfl <;> assumption)
            simpa [hr, hop, simplify, hins', simpOr] using this
        · simp [simpOr]
      · rcases hins' : ins with _ | ⟨a, l⟩
        · simp [simpNot]
        · rcases a with a | a
          · simp [simpNot]
          · have ha := hall (Sum.inr a) (by simp [hins'])
            simp only [simpNot]
            have := hnew_T ⟨GateOp.not, [a]⟩ (by simp [hr, hop, simplify, hins', simpNot])
              (by simp [hr, hop, simplify, hins', simpNot]) (by intro j hj; simp at hj; subst hj; exact ha)
            simpa [hr, hop, simplify, hins', simpNot] using this
      all_goals trivial
    · rw [getD_snoc_ne _ _ _ _ hil] at hi
      simp only [elimStep]
      rw [getD_snoc_ne _ _ _ _ (by omega)]
      have hold := hT i hi
      have hvi := hval i
      cases hst : st.1.getD i (Sum.inl false) with
      | inl c => trivial
      | inr j =>
        rw [hst] at hold hvi
        simp only [Stat.Valid] at hvi
        dsimp only
        rw [← List.append_assoc, suppsFrom_append, getD_suppsFrom _ _ _ (by rw [hpre_len]; exact hvi)]
        exact hold

theorem elim_full_emit_step (m : ℕ) (gs : List Gate) (st : List Stat × List Gate)
    (hfull : (elim m gs st).2.length = st.2.length + gs.length) :
    ∀ t (ht : t < gs.length),
      (elim m (gs.take t) st).2.length = st.2.length + t ∧
      ∃ g', (simplify (gs[t]).op (m + (st.2.length + t))
        ((gs[t]).inputs.map fun i => (elim m (gs.take t) st).1.getD i (Sum.inl false))).1 = some g' ∧
        (elim m gs st).2[st.2.length + t]'(by omega) = g' := by
  have hlen_le : ∀ t, t ≤ gs.length → (elim m (gs.take t) st).2.length = st.2.length + t := by
    intro t ht
    have hsplit : gs = gs.take t ++ gs.drop t := (List.take_append_drop t gs).symm
    obtain ⟨_, t1, _, h21, _, hl1⟩ := elim_prefix m (gs.take t) st
    obtain ⟨_, t2, _, h22, _, hl2⟩ := elim_prefix m (gs.drop t) (elim m (gs.take t) st)
    have heq : (elim m gs st).2 = (elim m (gs.take t) st).2 ++ t2 := by
      conv_lhs => rw [hsplit, elim_append]
      exact h22
    have h1 : (elim m (gs.take t) st).2.length ≤ st.2.length + t := by
      rw [h21, List.length_append]; simp only [List.length_take] at hl1; omega
    have h2 : (elim m gs st).2.length ≤ (elim m (gs.take t) st).2.length + (gs.length - t) := by
      rw [heq, List.length_append]; simp only [List.length_drop] at hl2; omega
    omega
  intro t ht
  have hlt := hlen_le t ht.le
  have hlt1 := hlen_le (t + 1) ht
  refine ⟨hlt, ?_⟩
  have hstep : (elim m (gs.take (t + 1)) st).2 =
      (elim m (gs.take t) st).2 ++
        (simplify (gs[t]).op (m + (elim m (gs.take t) st).2.length)
          ((gs[t]).inputs.map fun i => (elim m (gs.take t) st).1.getD i (Sum.inl false))).1.toList := by
    rw [List.take_succ_eq_append_getElem ht, elim_append]; rfl
  rw [hlt] at hstep
  set r := simplify (gs[t]).op (m + (st.2.length + t))
    ((gs[t]).inputs.map fun i => (elim m (gs.take t) st).1.getD i (Sum.inl false)) with hr
  cases hr1 : r.1 with
  | none =>
    rw [hr1] at hstep
    have := congrArg List.length hstep
    simp [hlt, hlt1] at this
  | some g' =>
    refine ⟨g', rfl, ?_⟩
    have hsplit : gs = gs.take (t + 1) ++ gs.drop (t + 1) := (List.take_append_drop (t + 1) gs).symm
    obtain ⟨_, rest, _, hrest, _, _⟩ := elim_prefix m (gs.drop (t + 1)) (elim m (gs.take (t + 1)) st)
    have hall : (elim m gs st).2 = (elim m (gs.take t) st).2 ++ [g'] ++ rest := by
      conv_lhs => rw [hsplit, elim_append, hrest, hstep, hr1]
      simp
    simp only [hall]
    rw [List.getElem_append_left (by simp [hlt])]
    rw [List.getElem_append_right (by omega)]
    simp [hlt]

theorem peel_wire (C : Circuit) (hfan : FanInTwo C) (hnok : ∀ g ∈ C.gates, NOk g)
    (heval : ∀ x, C.eval (List.ofFn x) = fG x)
    (hmin : ∀ D : Circuit, FanInTwo D → (∀ x, D.eval (List.ofFn x) = fG x) → C.size ≤ D.size)
    (k : ℕ) (htop : HasTopOrs C k)
    (w : ℕ) (hw10 : 10 ≤ w) (hwB : w < 10 + (C.gates.length - k))
    (hwT : (suppsFrom (C.gates.take (C.gates.length - k)) (inputSupps 10)).getD w ∅ ⊆ Tset)
    (c : Bool)
    (habsorb : ∀ x, (wiresFrom C.gates (List.ofFn x)).getD w false = c → fG x = true)
    (hnc_notc : ∃ x y, (wiresFrom C.gates (List.ofFn x)).getD w false = !c ∧
      (wiresFrom C.gates (List.ofFn y)).getD w false = !c ∧ fG x ≠ fG y)
    (Sskip : Finset ℕ) (hcard : Sskip.card = if c then 1 else 2)
    (hskip : ∀ t ∈ Sskip, ∃ ht : t < ((C.gates.take (C.gates.length - k)).drop (w - 9)).length,
      w ∈ (((C.gates.take (C.gates.length - k)).drop (w - 9))[t]).inputs) :
    ∃ D : Circuit, FanInTwo D ∧ (∀ g ∈ D.gates, NOk g) ∧ D.size = C.size ∧
      (∀ x, D.eval (List.ofFn x) = fG x) ∧ HasTopOrs D (k + 1) := by
  have hkC : k ≤ C.gates.length := htop.1
  set body := C.gates.take (C.gates.length - k) with hbody
  set top := C.gates.drop (C.gates.length - k) with htop_def
  have hbody_len : body.length = C.gates.length - k := by
    rw [hbody, List.length_take, Nat.min_eq_left (by omega)]
  have htop_len : top.length = k := by
    rw [htop_def, List.length_drop]; omega
  have hCsplit : C.gates = body ++ top := (List.take_append_drop (C.gates.length - k) C.gates).symm
  set pre := body.take (w - 9) with hpre
  set body2 := body.drop (w - 9) with hbody2
  have hpre_len : pre.length = w - 9 := by
    rw [hpre, List.length_take, Nat.min_eq_left (by omega)]
  have hbody2_len : body2.length = body.length - (w - 9) := by
    rw [hbody2, List.length_drop]
  have hbodysplit : body = pre ++ body2 := (List.take_append_drop (w - 9) body).symm
  set m := 10 + pre.length with hm_def
  have hm_eq : m = w + 1 := by omega
  set st0 : List Stat × List Gate :=
    (List.ofFn fun i : Fin m => if i.val = w then Sum.inl (!c) else Sum.inr i.val, []) with hst0
  have hst0_len : st0.1.length = m := by simp [hst0]
  have hst0_val : ∀ i, Stat.Valid (m + st0.2.length) (st0.1.getD i (Sum.inl false)) := by
    intro i
    by_cases hi : i < m
    · simp only [hst0, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte,
        Option.getD_some, List.length_nil, add_zero]
      split_ifs <;> simp [Stat.Valid, hi]
    · simp [hst0, List.getD_eq_getElem?_getD, hi, Stat.Valid]
  have hst0_w : st0.1.getD w (Sum.inl false) = Sum.inl (!c) := by
    simp [hst0, List.getD_eq_getElem?_getD, show w < m by omega]
  have hst0_inv : ∀ x : Fin 10 → Bool,
      (wiresFrom C.gates (List.ofFn x)).getD w false = !c →
      Inv m (wiresFrom pre (List.ofFn x)) (wiresFrom pre (List.ofFn x)) st0 := by
    intro x hwx
    have hpre_w : (wiresFrom pre (List.ofFn x)).getD w false = !c := by
      have h1 : C.gates = pre ++ (body2 ++ top) := by rw [hCsplit, hbodysplit, List.append_assoc]
      rw [h1, wiresFrom_append, getD_wiresFrom _ _ _ (by rw [length_wiresFrom]; simp; omega)] at hwx
      exact hwx
    refine ⟨by rw [hst0_len, length_wiresFrom]; simp [hm_def],
      by rw [length_wiresFrom]; simp [hm_def], ?_⟩
    intro i
    by_cases hi : i < m
    · simp only [hst0, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte,
        Option.getD_some, List.length_nil, add_zero, wiresFrom, List.foldl_nil]
      split_ifs with hiw
      · subst hiw; exact ⟨trivial, hpre_w.symm⟩
      · exact ⟨hi, rfl⟩
    · simp only [hst0, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte,
        Option.getD_none, List.length_nil, add_zero, Stat.val, Stat.Valid]
      refine ⟨trivial, ?_⟩
      symm
      exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp [hm_def]; omega)
  have hnok_pre : ∀ g ∈ pre, NOk g := fun g hg =>
    hnok g (by rw [hCsplit, hbodysplit]; simp [hg])
  have hnok_body2 : ∀ g ∈ body2, NOk g := fun g hg =>
    hnok g (by rw [hCsplit, hbodysplit]; simp [hg])
  have hnok_top : ∀ g ∈ top, NOk g := fun g hg =>
    hnok g (by rw [hCsplit]; simp [hg])
  set resBody := elim m body2 st0 with hresBody
  have hresBody_cnt : resBody.2.length + Sskip.card ≤ body2.length := by
    have h := elim_skips_count m body2 hnok_body2 st0 Sskip (by
      intro t ht
      obtain ⟨hlt, hmem⟩ := hskip t ht
      refine ⟨hlt, w, hmem, !c, ?_⟩
      obtain ⟨l1, _, h1, _, _, _⟩ := elim_prefix m (body2.take t) st0
      rw [h1, List.getD_append _ _ _ _ (by omega), hst0_w])
    simpa [hst0] using h
  have hresBody_val : ∀ i, Stat.Valid (m + resBody.2.length) (resBody.1.getD i (Sum.inl false)) :=
    elim_valid m body2 st0 hst0_val
  have hresBody_len1 : resBody.1.length = 10 + body.length := by
    obtain ⟨l1, _, h1, _, hl1, _⟩ := elim_prefix m body2 st0
    rw [hresBody, h1, List.length_append, hst0_len, hl1, hm_def, hbody2_len, hpre_len]
    omega
  set st1 : List Stat × List Gate :=
    (resBody.1, if c then resBody.2 else resBody.2 ++ [⟨GateOp.not, [w]⟩]) with hst1
  have hst1_len2 : st1.2.length = resBody.2.length + (if c then 0 else 1) := by
    cases c <;> simp [hst1]
  have hst1_val : ∀ i, Stat.Valid (m + st1.2.length) (st1.1.getD i (Sum.inl false)) := by
    intro i
    have hvi := hresBody_val i
    cases hst : resBody.1.getD i (Sum.inl false) with
    | inl _ => simp [hst1, hst, Stat.Valid]
    | inr j =>
      rw [hst] at hvi
      simp only [hst1, hst, Stat.Valid] at hvi ⊢
      cases c <;> simp at hvi ⊢ <;> omega
  have hst1_nok : ∀ g ∈ st1.2, NOk g := by
    have hrb : ∀ g ∈ resBody.2, NOk g := elim_nok m body2 st0 (by simp [hst0])
    intro g hg
    cases c <;> simp only [hst1, ↓reduceIte, Bool.false_eq_true, List.mem_append, List.mem_singleton] at hg
    · rcases hg with hg | rfl
      · exact hrb g hg
      · exact ⟨⟨Or.inr (Or.inr rfl), by simp⟩, by simp⟩
    · exact hrb g hg
  have hst1_inv : ∀ x : Fin 10 → Bool,
      (wiresFrom C.gates (List.ofFn x)).getD w false = !c →
      Inv m (wiresFrom body (List.ofFn x)) (wiresFrom pre (List.ofFn x)) st1 := by
    intro x hwx
    have hrb := inv_elim m body2 (fun g hg => (hnok_body2 g hg).1)
      (wiresFrom pre (List.ofFn x)) (wiresFrom pre (List.ofFn x)) st0 (hst0_inv x hwx)
    rw [← wiresFrom_append, ← hbodysplit] at hrb
    obtain ⟨hl1, hl2, hvv⟩ := hrb
    refine ⟨hl1, hl2, ?_⟩
    intro i
    obtain ⟨hvi, hei⟩ := hvv i
    refine ⟨hst1_val i, ?_⟩
    cases hst : resBody.1.getD i (Sum.inl false) with
    | inl b =>
      rw [hst] at hei
      simp only [hst1, hst, Stat.val] at hei ⊢; exact hei
    | inr j =>
      rw [hst] at hvi hei
      simp only [hst1, hst, Stat.val, Stat.Valid] at hvi hei ⊢
      cases c
      · simp only [Bool.false_eq_true, ↓reduceIte, wiresFrom_append]
        rw [getD_wiresFrom _ _ _ (by rw [length_wiresFrom, hl2]; exact hvi)]
        exact hei
      · simpa using hei
  set res := elim m top st1 with hres
  have hres_inv : ∀ x : Fin 10 → Bool,
      (wiresFrom C.gates (List.ofFn x)).getD w false = !c →
      Inv m (wiresFrom C.gates (List.ofFn x)) (wiresFrom pre (List.ofFn x)) res := by
    intro x hwx
    have h := inv_elim m top (fun g hg => (hnok_top g hg).1)
      (wiresFrom body (List.ofFn x)) (wiresFrom pre (List.ofFn x)) st1 (hst1_inv x hwx)
    rw [← wiresFrom_append, ← hCsplit] at h
    exact h
  have hout_inr : ∃ out', res.1.getD C.output (Sum.inl false) = Sum.inr out' := by
    cases hout : res.1.getD C.output (Sum.inl false) with
    | inl b =>
      exfalso
      obtain ⟨x, y, hwx, hwy, hxy⟩ := hnc_notc
      have hx := (hres_inv x hwx).2.2 C.output
      have hy := (hres_inv y hwy).2.2 C.output
      rw [hout] at hx hy
      apply hxy
      rw [← heval x, ← heval y]
      simp only [Circuit.eval, wires_eq, ← hx.2, ← hy.2, Stat.val]
    | inr out' => exact ⟨out', rfl⟩
  obtain ⟨out', hout'⟩ := hout_inr
  set w' := if c then w else m + resBody.2.length with hw'
  set D : Circuit := ⟨pre ++ res.2 ++ [⟨GateOp.or, [w', out']⟩], 10 + pre.length + res.2.length⟩ with hD
  have hD_nok : ∀ g ∈ D.gates, NOk g := by
    have hres_nok : ∀ g ∈ res.2, NOk g := elim_nok m top st1 hst1_nok
    intro g hg
    simp only [hD, List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | rfl
    · exact hnok_pre g hg
    · exact hres_nok g hg
    · exact ⟨⟨Or.inr (Or.inl rfl), by simp⟩, by simp⟩
  have hD_fan : FanInTwo D := fun g hg => (hD_nok g hg).1
  have hD_eval : ∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = fG x := by
    intro x
    have hlen_pr : (wiresFrom (pre ++ res.2) (List.ofFn x)).length = 10 + pre.length + res.2.length := by
      rw [length_wiresFrom, List.length_append]; simp; omega
    have hD_val : D.eval (List.ofFn x) =
        ((wiresFrom (pre ++ res.2) (List.ofFn x)).getD w' false ||
          (wiresFrom (pre ++ res.2) (List.ofFn x)).getD out' false) := by
      simp only [Circuit.eval, wires_eq, hD]
      rw [wiresFrom_append (pre ++ res.2), wiresFrom_cons]
      rw [show 10 + pre.length + res.2.length = (wiresFrom (pre ++ res.2) (List.ofFn x)).length by omega]
      rw [show wiresFrom [] (wiresFrom (pre ++ res.2) (List.ofFn x) ++
        [(GateOp.or).eval ([w', out'].map fun i => (wiresFrom (pre ++ res.2) (List.ofFn x)).getD i false)]) =
        wiresFrom (pre ++ res.2) (List.ofFn x) ++
        [(GateOp.or).eval ([w', out'].map fun i => (wiresFrom (pre ++ res.2) (List.ofFn x)).getD i false)] from rfl]
      rw [getD_snoc_eq]
      simp [GateOp.eval]
    have hw'_val : (wiresFrom (pre ++ res.2) (List.ofFn x)).getD w' false =
        decide ((wiresFrom C.gates (List.ofFn x)).getD w false = c) := by
      have hpre_w : (wiresFrom pre (List.ofFn x)).getD w false =
          (wiresFrom C.gates (List.ofFn x)).getD w false := by
        have h1 : C.gates = pre ++ (body2 ++ top) := by rw [hCsplit, hbodysplit, List.append_assoc]
        symm
        rw [h1, wiresFrom_append pre, getD_wiresFrom _ _ _ (by rw [length_wiresFrom]; simp; omega)]
      obtain ⟨_, rest, _, hrest, _, _⟩ := elim_prefix m top st1
      cases hc : c
      · simp only [hw', hc, Bool.false_eq_true, ↓reduceIte]
        have hres2 : pre ++ res.2 = ((pre ++ resBody.2) ++ [⟨GateOp.not, [w]⟩]) ++ rest := by
          rw [hres, hrest, hst1]; simp [hc, List.append_assoc]
        rw [hres2, wiresFrom_append ((pre ++ resBody.2) ++ [_]), wiresFrom_append (pre ++ resBody.2), wiresFrom_cons]
        have hlen_pb : (wiresFrom (pre ++ resBody.2) (List.ofFn x)).length = m + resBody.2.length := by
          rw [length_wiresFrom, List.length_append]; simp [hm_def]; omega
        rw [show wiresFrom [] (wiresFrom (pre ++ resBody.2) (List.ofFn x) ++
          [(GateOp.not).eval ([w].map fun i => (wiresFrom (pre ++ resBody.2) (List.ofFn x)).getD i false)]) =
          wiresFrom (pre ++ resBody.2) (List.ofFn x) ++
          [(GateOp.not).eval ([w].map fun i => (wiresFrom (pre ++ resBody.2) (List.ofFn x)).getD i false)] from rfl]
        rw [getD_wiresFrom _ _ _ (by rw [List.length_append, hlen_pb]; simp)]
        rw [show m + resBody.2.length = (wiresFrom (pre ++ resBody.2) (List.ofFn x)).length by omega, getD_snoc_eq]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons]
        rw [wiresFrom_append pre, getD_wiresFrom _ _ _ (by rw [length_wiresFrom]; simp; omega), hpre_w]
        cases (wiresFrom C.gates (List.ofFn x)).getD w false <;> rfl
      · simp only [hw', hc, ↓reduceIte]
        rw [wiresFrom_append pre, getD_wiresFrom _ _ _ (by rw [length_wiresFrom]; simp; omega), hpre_w]
        cases (wiresFrom C.gates (List.ofFn x)).getD w false <;> rfl
    rw [hD_val, hw'_val]
    by_cases hwc : (wiresFrom C.gates (List.ofFn x)).getD w false = c
    · simp only [hwc, decide_true, Bool.true_or]
      exact (habsorb x hwc).symm
    · have hwn : (wiresFrom C.gates (List.ofFn x)).getD w false = !c := by
        cases h : (wiresFrom C.gates (List.ofFn x)).getD w false <;> cases c <;>
          first | rfl | exact (hwc (by rw [h])).elim
      simp only [hwc, decide_false, Bool.false_or]
      have hx := (hres_inv x hwn).2.2 C.output
      rw [hout'] at hx
      rw [wiresFrom_append pre, ← heval x]
      simp only [Circuit.eval, wires_eq]
      exact hx.2
  have hD_ge : C.size ≤ D.size := hmin D hD_fan hD_eval
  obtain ⟨_, top', _, htop'_eq, _, htop'_len⟩ := elim_prefix m top st1
  have hD_size : D.size = C.size := by
    simp only [Circuit.size, hD, List.length_append, List.length_singleton] at hD_ge ⊢
    have hres_le : res.2.length ≤ st1.2.length + top.length := by
      rw [hres, htop'_eq, List.length_append]; omega
    cases c <;> simp only [↓reduceIte, Bool.false_eq_true] at hcard hst1_len2 <;> omega
  have hfull : res.2.length = st1.2.length + top.length := by
    simp only [Circuit.size, hD, List.length_append, List.length_singleton] at hD_size
    have hres_le : res.2.length ≤ st1.2.length + top.length := by
      rw [hres, htop'_eq, List.length_append]; omega
    cases c <;> simp only [↓reduceIte, Bool.false_eq_true] at hcard hst1_len2 <;> omega
  have htop'_len_eq : top'.length = k := by
    rw [hres, htop'_eq, List.length_append] at hfull; omega
  have hD_gates_len : D.gates.length = pre.length + st1.2.length + k + 1 := by
    simp only [hD, List.length_append, List.length_singleton, hfull, htop_len]; omega
  have hD_body : D.gates.take (D.gates.length - (k + 1)) = pre ++ st1.2 := by
    have h1 : D.gates = (pre ++ st1.2) ++ (top' ++ [⟨GateOp.or, [w', out']⟩]) := by
      simp only [hD, hres, htop'_eq, List.append_assoc]
    rw [show D.gates.length - (k + 1) = (pre ++ st1.2).length by simp [hD_gates_len], h1]
    exact List.take_left
  have hD_top : D.gates.drop (D.gates.length - (k + 1)) = top' ++ [⟨GateOp.or, [w', out']⟩] := by
    have h1 : D.gates = (pre ++ st1.2) ++ (top' ++ [⟨GateOp.or, [w', out']⟩]) := by
      simp only [hD, hres, htop'_eq, List.append_assoc]
    rw [show D.gates.length - (k + 1) = (pre ++ st1.2).length by simp [hD_gates_len], h1]
    exact List.drop_left
  set B' := 10 + (pre ++ st1.2).length with hB'
  have hB'_eq : B' = m + st1.2.length := by simp [hB', hm_def]; omega
  have hsupp_pre_w : (suppsFrom pre (inputSupps 10)).getD w ∅ ⊆ Tset := by
    have h1 : (suppsFrom body (inputSupps 10)).getD w ∅ = (suppsFrom pre (inputSupps 10)).getD w ∅ := by
      rw [hbodysplit, suppsFrom_append, getD_suppsFrom _ _ _ (by rw [length_suppsFrom]; simp [inputSupps, hpre_len]; omega)]
    rwa [← h1]
  have hw'_lt : w' < B' := by
    cases c <;> simp [hw', hB'_eq, hst1_len2] <;> omega
  have hw'_T : (suppsFrom (pre ++ st1.2) (inputSupps 10)).getD w' ∅ ⊆ Tset := by
    have hlen_pb : (suppsFrom (pre ++ resBody.2) (inputSupps 10)).length = m + resBody.2.length := by
      rw [length_suppsFrom, List.length_append]; simp [inputSupps, hm_def]; omega
    cases hc : c
    · simp only [hw', hc, Bool.false_eq_true, ↓reduceIte, hst1]
      rw [← List.append_assoc, suppsFrom_append (pre ++ resBody.2), suppsFrom_cons]
      rw [show m + resBody.2.length = (suppsFrom (pre ++ resBody.2) (inputSupps 10)).length by omega]
      rw [show suppsFrom [] (suppsFrom (pre ++ resBody.2) (inputSupps 10) ++
        [gateSupp (suppsFrom (pre ++ resBody.2) (inputSupps 10)) ⟨GateOp.not, [w]⟩]) =
        suppsFrom (pre ++ resBody.2) (inputSupps 10) ++
        [gateSupp (suppsFrom (pre ++ resBody.2) (inputSupps 10)) ⟨GateOp.not, [w]⟩] from rfl]
      rw [getD_snoc_eq]
      intro x hx
      obtain ⟨j, hj, hxj⟩ := (mem_gateSupp _ _ x).1 hx
      simp only [List.mem_singleton] at hj
      subst hj
      rw [suppsFrom_append pre, getD_suppsFrom _ _ _ (by rw [length_suppsFrom]; simp [inputSupps, hpre_len]; omega)] at hxj
      exact hsupp_pre_w hxj
    · simp only [hw', hc, ↓reduceIte, hst1]
      rw [suppsFrom_append pre, getD_suppsFrom _ _ _ (by rw [length_suppsFrom]; simp [inputSupps, hpre_len]; omega)]
      exact hsupp_pre_w
  have hsupp_st1 : ∀ i, (suppsFrom body (inputSupps 10)).getD i ∅ ⊆ Tset →
      match st1.1.getD i (Sum.inl false) with
      | Sum.inl _ => True
      | Sum.inr j => (suppsFrom (pre ++ st1.2) (inputSupps 10)).getD j ∅ ⊆ Tset := by
    have hrb_T := supp_elim_T m pre rfl body2 st0 (suppsFrom pre (inputSupps 10))
      (by rw [hst0_len, length_suppsFrom]; simp [inputSupps, hm_def]) hst0_val (by
        intro i hi
        by_cases him : i < m
        · simp only [hst0, List.getD_eq_getElem?_getD, List.getElem?_ofFn, him, ↓reduceDIte,
            Option.getD_some, List.append_nil]
          split_ifs
          · trivial
          · exact hi
        · simp [hst0, List.getD_eq_getElem?_getD, him])
    rw [← suppsFrom_append, ← hbodysplit] at hrb_T
    intro i hi
    have h1 := hrb_T i hi
    have hvi := hresBody_val i
    cases hst : resBody.1.getD i (Sum.inl false) with
    | inl _ => simp [hst1, hst]
    | inr j =>
      rw [hst] at h1 hvi
      simp only [hst1, hst, Stat.Valid] at hvi ⊢
      dsimp only at h1 ⊢
      cases hc : c
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [← List.append_assoc, suppsFrom_append (pre ++ resBody.2)]
        rw [getD_suppsFrom _ _ _ (by rw [length_suppsFrom, List.length_append]; simp [inputSupps, hm_def]; omega)]
        exact h1
      · simpa using h1
  refine ⟨D, hD_fan, hD_nok, hD_size, hD_eval, ?_⟩
  refine ⟨by omega, Or.inr ⟨by simp [hD, hD_gates_len]; omega, ?_⟩⟩
  rcases htop.2 with hk0 | ⟨hCout, o0, ho0, htop_spec⟩
  · subst hk0
    have htop_nil : top = [] := List.eq_nil_of_length_eq_zero htop_len
    have htop'_nil : top' = [] := List.eq_nil_of_length_eq_zero htop'_len_eq
    have hout'_lt : out' < B' := by
      have hv := hst1_val C.output
      have hres_st1 : res = st1 := by simp [hres, htop_nil, elim]
      rw [hres_st1] at hout'
      rw [hout'] at hv
      simpa [Stat.Valid, hB'_eq] using hv
    refine ⟨out', by rw [hD_body] at *; simp [hB'] at hout'_lt; omega, ?_⟩
    intro i hi
    have hD_top_len : (D.gates.drop (D.gates.length - (0 + 1))).length = 1 := by
      rw [hD_top, htop'_nil]; simp
    have hi0 : i = 0 := by omega
    subst hi0
    refine ⟨w', by rw [hD_body]; exact hw'_lt, by rw [hD_body]; exact hw'_T, ?_⟩
    simp [hD_top, htop'_nil]
  · by_cases hk0 : k = 0
    · subst hk0
      have htop_nil : top = [] := List.eq_nil_of_length_eq_zero htop_len
      have htop'_nil : top' = [] := List.eq_nil_of_length_eq_zero htop'_len_eq
      have hout'_lt : out' < B' := by
        have hv := hst1_val C.output
        have hres_st1 : res = st1 := by simp [hres, htop_nil, elim]
        rw [hres_st1] at hout'
        rw [hout'] at hv
        simpa [Stat.Valid, hB'_eq] using hv
      refine ⟨out', by rw [hD_body] at *; simp [hB'] at hout'_lt; omega, ?_⟩
      intro i hi
      have hD_top_len : (D.gates.drop (D.gates.length - (0 + 1))).length = 1 := by
        rw [hD_top, htop'_nil]; simp
      have hi0 : i = 0 := by omega
      subst hi0
      refine ⟨w', by rw [hD_body]; exact hw'_lt, by rw [hD_body]; exact hw'_T, ?_⟩
      simp [hD_top, htop'_nil]
    have hkpos : 1 ≤ k := by omega
    have hstep_full := elim_full_emit_step m top st1 hfull
    have hchain : ∀ i, (hi : i < k) →
        ∃ (hi_w : ℕ), hi_w < B' ∧
          (suppsFrom (pre ++ st1.2) (inputSupps 10)).getD hi_w ∅ ⊆ Tset ∧
          ∃ (o0' : ℕ), o0' < B' ∧ st1.1.getD o0 (Sum.inl false) = Sum.inr o0' ∧
          top'[i]'(by omega) = ⟨GateOp.or, [hi_w, if i = 0 then o0' else B' + i - 1]⟩ ∧
          (elim m (top.take (i + 1)) st1).1.getD (10 + body.length + i) (Sum.inl false) = Sum.inr (B' + i) := by
      intro i
      induction i with
      | zero =>
        intro hi
        obtain ⟨h0, h0_lt, h0_T, h0_eq_raw⟩ := htop_spec 0 (by rw [← htop_def]; omega)
        have h0_eq : top[0]'(by omega) = ⟨GateOp.or, [h0, o0]⟩ := by
          simpa only [← htop_def, ← hbody, ↓reduceIte] using h0_eq_raw
        rw [← hbody] at h0_lt h0_T
        obtain ⟨hlen0, g', hg'_eq, hg'_at⟩ := hstep_full 0 (by omega)
        have hg'_top' : top'[0]'(by omega) = g' := by
          have : res.2[st1.2.length + 0]'(by omega) = top'[0]'(by omega) := by
            simp only [hres, htop'_eq, add_zero]
            rw [List.getElem_append_right le_rfl]
            simp
          rw [← this, hg'_at]
        simp only [List.take_zero, elim, List.foldl_nil, h0_eq, List.map_cons,
          List.map_nil, simplify] at hg'_eq
        cases hh0 : st1.1.getD h0 (Sum.inl false) with
        | inl b =>
          rw [hh0] at hg'_eq
          cases ho0'' : st1.1.getD o0 (Sum.inl false) with
          | inl b2 => rw [ho0''] at hg'_eq; cases b <;> cases b2 <;> simp [simpOr] at hg'_eq
          | inr j2 => rw [ho0''] at hg'_eq; cases b <;> simp [simpOr] at hg'_eq
        | inr h0' =>
          cases ho0' : st1.1.getD o0 (Sum.inl false) with
          | inl b2 =>
            rw [hh0, ho0'] at hg'_eq
            cases b2 <;> simp [simpOr] at hg'_eq
          | inr o0' =>
            rw [hh0, ho0'] at hg'_eq
            simp only [simpOr, Option.some.injEq] at hg'_eq
            have hh0'_lt : h0' < B' := by
              have hv := hst1_val h0; rw [hh0] at hv; simpa [Stat.Valid, hB'_eq] using hv
            have ho0'_lt : o0' < B' := by
              have hv := hst1_val o0; rw [ho0'] at hv; simpa [Stat.Valid, hB'_eq] using hv
            have hh0'_T : (suppsFrom (pre ++ st1.2) (inputSupps 10)).getD h0' ∅ ⊆ Tset := by
              have hT := hsupp_st1 h0 h0_T; rw [hh0] at hT; exact hT
            have hstat0 : (elim m (top.take 1) st1).1.getD (10 + body.length + 0) (Sum.inl false) =
                Sum.inr (B' + 0) := by
              have hs := elim_take_step_eq m top st1 0 (by omega)
              rw [show st1.1.length = 10 + body.length from hresBody_len1] at hs
              simp only [List.take_zero, elim, List.foldl_nil, h0_eq, List.map_cons,
                List.map_nil, hh0, ho0', simplify, simpOr] at hs
              exact hs.trans (by rw [hB'_eq]; simp)
            exact ⟨h0', hh0'_lt, hh0'_T, o0', ho0'_lt, rfl, by rw [hg'_top', ← hg'_eq]; simp, hstat0⟩
      | succ i ih =>
        intro hi
        obtain ⟨_, _, _, o0', ho0'_lt, ho0'_eq, _, hprev⟩ := ih (by omega)
        obtain ⟨hi_in, hi_lt, hi_T, hi_eq_raw⟩ := htop_spec (i + 1) (by rw [← htop_def]; omega)
        have hi_eq : top[i + 1]'(by omega) = ⟨GateOp.or, [hi_in, 10 + body.length + i]⟩ := by
          have h1 : top[i + 1]'(by omega) =
              ⟨GateOp.or, [hi_in, 10 + body.length + (i + 1) - 1]⟩ := by
            simpa only [← htop_def, ← hbody, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte] using hi_eq_raw
          rw [h1]; simp [Nat.add_sub_cancel]
        rw [← hbody] at hi_lt hi_T
        obtain ⟨hlen_i, g', hg'_eq, hg'_at⟩ := hstep_full (i + 1) (by omega)
        have hg'_top' : top'[i + 1]'(by omega) = g' := by
          have : res.2[st1.2.length + (i + 1)]'(by omega) = top'[i + 1]'(by omega) := by
            simp only [hres, htop'_eq]
            rw [List.getElem_append_right (by omega)]
            simp
          rw [← this, hg'_at]
        have hhi_st : (elim m (top.take (i + 1)) st1).1.getD hi_in (Sum.inl false) =
            st1.1.getD hi_in (Sum.inl false) := by
          obtain ⟨l1, _, h1, _, _, _⟩ := elim_prefix m (top.take (i + 1)) st1
          rw [h1, List.getD_append _ _ _ _ (by rw [show st1.1.length = 10 + body.length from hresBody_len1]; exact hi_lt)]
        simp only [hi_eq, List.map_cons, List.map_nil, hhi_st, hprev, simplify] at hg'_eq
        cases hhi' : st1.1.getD hi_in (Sum.inl false) with
        | inl b =>
          rw [hhi'] at hg'_eq
          cases b <;> simp [simpOr, Bool.cond_false, Bool.cond_true] at hg'_eq
        | inr hi_w =>
          rw [hhi'] at hg'_eq
          simp only [simpOr, Option.some.injEq] at hg'_eq
          have hhi_w_lt : hi_w < B' := by
            have hv := hst1_val hi_in; rw [hhi'] at hv; simpa [Stat.Valid, hB'_eq] using hv
          have hhi_w_T : (suppsFrom (pre ++ st1.2) (inputSupps 10)).getD hi_w ∅ ⊆ Tset := by
            have hT := hsupp_st1 hi_in hi_T; rw [hhi'] at hT; exact hT
          have hstat_i : (elim m (top.take (i + 1 + 1)) st1).1.getD (10 + body.length + (i + 1)) (Sum.inl false) =
              Sum.inr (B' + (i + 1)) := by
            have hs := elim_take_step_eq m top st1 (i + 1) (by omega)
            rw [show st1.1.length = 10 + body.length from hresBody_len1] at hs
            rw [hlen_i] at hs
            simp only [hi_eq, List.map_cons, List.map_nil, hhi_st, hhi', hprev, simplify, simpOr] at hs
            rw [hs, hB'_eq]; congr 1; omega
          refine ⟨hi_w, hhi_w_lt, hhi_w_T, o0', ho0'_lt, ho0'_eq, ?_, hstat_i⟩
          rw [hg'_top', ← hg'_eq]
          simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
          rw [show B' + (i + 1) - 1 = B' + i by omega]
    obtain ⟨_, _, _, o0', ho0'_lt, ho0'_eq, _, hlast⟩ := hchain (k - 1) (by omega)
    have hout'_eq : out' = B' + k - 1 := by
      have htk : top.take (k - 1 + 1) = top := List.take_of_length_le (by omega)
      rw [htk] at hlast
      have hCout' : C.output = 10 + body.length + (k - 1) := by omega
      rw [hCout'] at hout'
      rw [← hres, hout'] at hlast
      have := Sum.inr.inj hlast
      omega
    refine ⟨o0', by rw [hD_body] at *; simp [hB'] at ho0'_lt; omega, ?_⟩
    intro i hi
    have hD_top_len : (D.gates.drop (D.gates.length - (k + 1))).length = k + 1 := by
      rw [hD_top]; simp [htop'_len_eq]
    by_cases hik : i < k
    · obtain ⟨hi_w, hi_lt, hi_T, o0'', _, ho0''_eq, hti, _⟩ := hchain i hik
      have ho0_same : o0'' = o0' := Sum.inr.inj (ho0''_eq.symm.trans ho0'_eq)
      subst ho0_same
      refine ⟨hi_w, by rw [hD_body]; exact hi_lt, by rw [hD_body]; exact hi_T, ?_⟩
      simp only [hD_top]
      rw [List.getElem_append_left (by omega)]
      simpa only [hD_body] using hti
    · have hik_eq : i = k := by omega
      subst i
      refine ⟨w', by rw [hD_body]; exact hw'_lt, by rw [hD_body]; exact hw'_T, ?_⟩
      simp only [hD_top]
      rw [List.getElem_append_right (by omega)]
      simp only [htop'_len_eq, Nat.sub_self, List.getElem_singleton, hD_body]
      have hk0' : k ≠ 0 := by omega
      simp [hk0', hout'_eq, hB']

theorem elim_not_in_supp_inr_lt (gs : List Gate) (m : ℕ)
    (hshape : ∀ t (ht : t < gs.length),
      ((gs[t]).op = GateOp.not ∧ (gs[t]).inputs.length = 1 ∧ ∀ a ∈ (gs[t]).inputs, a < m + t) ∨
      (((gs[t]).op = GateOp.and ∨ (gs[t]).op = GateOp.or) ∧ (gs[t]).inputs.length = 2 ∧
        ∀ a ∈ (gs[t]).inputs, a < m + t))
    (v : Fin 10) :
    ∀ (st : List Stat × List Gate) (S0 : List (Finset (Fin 10))),
      st.1.length = S0.length → S0.length = m →
      (∀ i, i < S0.length → v ∉ S0.getD i ∅ → ∃ r, st.1.getD i (Sum.inl false) = Sum.inr r) →
      ∀ i, i < (suppsFrom gs S0).length → v ∉ (suppsFrom gs S0).getD i ∅ →
        ∃ r, (elim 10 gs st).1.getD i (Sum.inl false) = Sum.inr r := by
  induction gs generalizing m with
  | nil => intro st S0 _ _ h; exact h
  | cons g gs ih =>
    intro st S0 hlen hSm hst
    rw [suppsFrom_cons, elim_cons]
    have hshape_tail : ∀ t (ht : t < gs.length),
        ((gs[t]).op = GateOp.not ∧ (gs[t]).inputs.length = 1 ∧ ∀ a ∈ (gs[t]).inputs, a < (m + 1) + t) ∨
        (((gs[t]).op = GateOp.and ∨ (gs[t]).op = GateOp.or) ∧ (gs[t]).inputs.length = 2 ∧
          ∀ a ∈ (gs[t]).inputs, a < (m + 1) + t) := by
      intro t ht
      have h := hshape (t + 1) (by simp [ht])
      simpa [Nat.add_assoc, Nat.add_comm 1 t] using h
    apply ih (m + 1) hshape_tail (elimStep 10 st g) (S0 ++ [gateSupp S0 g])
      (by simp [elimStep, hlen]) (by simp [hSm])
    intro i hi hvi
    by_cases hil : i = S0.length
    · subst hil
      rw [getD_snoc_eq] at hvi
      simp only [elimStep]
      rw [← hlen, getD_snoc_eq]
      have h0 := hshape 0 (by simp)
      simp only [List.getElem_cons_zero, add_zero] at h0
      have harg : ∀ a ∈ g.inputs, a < S0.length → ∃ r, st.1.getD a (Sum.inl false) = Sum.inr r := by
        intro a ha hal
        exact hst a hal (fun hv => hvi ((mem_gateSupp S0 g v).2 ⟨a, ha, hv⟩))
      rcases h0 with ⟨hop, hlen_g, hlt_g⟩ | ⟨hop | hop, hlen_g, hlt_g⟩
      · rcases hg_in : g.inputs with _ | ⟨a, _ | ⟨b, l⟩⟩
        · simp [hg_in] at hlen_g
        · obtain ⟨ra, hra⟩ := harg a (by simp [hg_in]) (by rw [hSm]; exact hlt_g a (by simp [hg_in]))
          exact ⟨10 + st.2.length, by rw [hop]; simp only [List.map_cons, List.map_nil, hra, simplify, simpNot]⟩
        · simp [hg_in] at hlen_g
      · rcases hg_in : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
        · simp [hg_in] at hlen_g
        · simp [hg_in] at hlen_g
        · obtain ⟨ra, hra⟩ := harg a (by simp [hg_in]) (by rw [hSm]; exact hlt_g a (by simp [hg_in]))
          obtain ⟨rb, hrb⟩ := harg b (by simp [hg_in]) (by rw [hSm]; exact hlt_g b (by simp [hg_in]))
          exact ⟨10 + st.2.length, by rw [hop]; simp only [List.map_cons, List.map_nil, hra, hrb, simplify, simpAnd]⟩
        · simp [hg_in] at hlen_g
      · rcases hg_in : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
        · simp [hg_in] at hlen_g
        · simp [hg_in] at hlen_g
        · obtain ⟨ra, hra⟩ := harg a (by simp [hg_in]) (by rw [hSm]; exact hlt_g a (by simp [hg_in]))
          obtain ⟨rb, hrb⟩ := harg b (by simp [hg_in]) (by rw [hSm]; exact hlt_g b (by simp [hg_in]))
          exact ⟨10 + st.2.length, by rw [hop]; simp only [List.map_cons, List.map_nil, hra, hrb, simplify, simpOr]⟩
        · simp [hg_in] at hlen_g
    · rw [getD_snoc_ne _ _ _ _ hil] at hvi
      simp only [elimStep]
      rw [getD_snoc_ne _ _ _ _ (by omega)]
      exact hst i (by simp at hi; omega) hvi

theorem elim_unused_wire (w p : ℕ) :
    ∀ (gs : List Gate) (st : List Stat × List Gate),
      p < 10 + st.2.length →
      (∀ i, i ≠ w → st.1.getD i (Sum.inl false) ≠ Sum.inr p) →
      (∀ t (ht : t < gs.length), w ∈ (gs[t]).inputs →
        simplify (gs[t]).op (10 + (elim 10 (gs.take t) st).2.length)
          ((gs[t]).inputs.map fun i => (elim 10 (gs.take t) st).1.getD i (Sum.inl false)) =
          (none, Sum.inl false)) →
      (∀ i, i ≠ w → (elim 10 gs st).1.getD i (Sum.inl false) ≠ Sum.inr p) ∧
      (∀ g ∈ (elim 10 gs st).2.drop st.2.length, p ∉ g.inputs) := by
  intro gs
  induction gs with
  | nil =>
    intro st _ hneq _
    exact ⟨hneq, by simp [elim]⟩
  | cons g gs ih =>
    intro st hp hneq hzero
    rw [elim_cons]
    set st' := elimStep 10 st g with hst'
    have hzero' : ∀ t (ht : t < gs.length), w ∈ (gs[t]).inputs →
        simplify (gs[t]).op (10 + (elim 10 (gs.take t) st').2.length)
          ((gs[t]).inputs.map fun i => (elim 10 (gs.take t) st').1.getD i (Sum.inl false)) =
          (none, Sum.inl false) := by
      intro t ht hmem
      have h := hzero (t + 1) (by simp [ht]) (by simpa using hmem)
      simpa [elim_cons, hst'] using h
    by_cases hw : w ∈ g.inputs
    · have hr0 : simplify g.op (10 + st.2.length) (g.inputs.map fun i => st.1.getD i (Sum.inl false)) =
          (none, Sum.inl false) := by
        have h := hzero 0 (by simp) hw
        simpa only [List.take_zero, elim, List.foldl_nil, List.getElem_cons_zero] using h
      have hst'_eq : st' = (st.1 ++ [Sum.inl false], st.2) := by
        simp only [hst', elimStep, hr0, Option.toList_none, List.append_nil]
      have hneq' : ∀ i, i ≠ w → st'.1.getD i (Sum.inl false) ≠ Sum.inr p := by
        intro i hi
        rw [hst'_eq]
        by_cases hil : i = st.1.length
        · subst hil; simp
        · rw [getD_snoc_ne _ _ _ _ hil]; exact hneq i hi
      have hrec := ih st' (by rw [hst'_eq]; exact hp) hneq' hzero'
      refine ⟨hrec.1, ?_⟩
      simpa [hst'_eq] using hrec.2
    · set ins := g.inputs.map fun i => st.1.getD i (Sum.inl false) with hins
      set r := simplify g.op (10 + st.2.length) ins with hr
      have hp_not_ins : Sum.inr p ∉ ins := by
        intro hmem
        obtain ⟨a, ha, hea⟩ := List.mem_map.1 hmem
        have haw : a ≠ w := fun e => hw (e ▸ ha)
        exact hneq a haw hea
      have hr_prop : r.2 ≠ Sum.inr p ∧ ∀ g' ∈ r.1, p ∉ g'.inputs := by
        cases hop : g.op <;> simp only [hr, hop, simplify]
        · rcases hins' : ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
          · simp [simpAnd]
          · rcases a with a | a
            · simp [simpAnd]
            · simp only [simpAnd, Option.mem_def, reduceCtorEq, false_implies, implies_true, and_true]
              intro h; exact hp_not_ins (by simp [hins', h])
          · rcases a with a | a <;> rcases b with b | b
            · simp [simpAnd]
            · cases a <;> simp only [simpAnd, cond_true, cond_false, Option.mem_def, reduceCtorEq,
                false_implies, implies_true, and_true]
              · simp
              · intro h; exact hp_not_ins (by simp [hins', h])
            · cases b <;> simp only [simpAnd, cond_true, cond_false, Option.mem_def, reduceCtorEq,
                false_implies, implies_true, and_true]
              · simp
              · intro h; exact hp_not_ins (by simp [hins', h])
            · refine ⟨by simp [simpAnd]; omega, ?_⟩
              intro g' hg' hpg'
              simp only [simpAnd, Option.mem_def, Option.some.injEq] at hg'
              subst hg'
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hpg'
              rcases hpg' with rfl | rfl <;> exact hp_not_ins (by simp [hins'])
          · simp [simpAnd]
        · rcases hins' : ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
          · simp [simpOr]
          · rcases a with a | a
            · simp [simpOr]
            · simp only [simpOr, Option.mem_def, reduceCtorEq, false_implies, implies_true, and_true]
              intro h; exact hp_not_ins (by simp [hins', h])
          · rcases a with a | a <;> rcases b with b | b
            · simp [simpOr]
            · cases a <;> simp only [simpOr, cond_true, cond_false, Option.mem_def, reduceCtorEq,
                false_implies, implies_true, and_true]
              · intro h; exact hp_not_ins (by simp [hins', h])
              · simp
            · cases b <;> simp only [simpOr, cond_true, cond_false, Option.mem_def, reduceCtorEq,
                false_implies, implies_true, and_true]
              · intro h; exact hp_not_ins (by simp [hins', h])
              · simp
            · refine ⟨by simp [simpOr]; omega, ?_⟩
              intro g' hg' hpg'
              simp only [simpOr, Option.mem_def, Option.some.injEq] at hg'
              subst hg'
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hpg'
              rcases hpg' with rfl | rfl <;> exact hp_not_ins (by simp [hins'])
          · simp [simpOr]
        · rcases hins' : ins with _ | ⟨a, l⟩
          · simp [simpNot]
          · rcases a with a | a
            · simp [simpNot]
            · refine ⟨by simp [simpNot]; omega, ?_⟩
              intro g' hg' hpg'
              simp only [simpNot, Option.mem_def, Option.some.injEq] at hg'
              subst hg'
              simp only [List.mem_singleton] at hpg'
              subst hpg'
              exact hp_not_ins (by simp [hins'])
        · simp
        · simp
      have hneq' : ∀ i, i ≠ w → st'.1.getD i (Sum.inl false) ≠ Sum.inr p := by
        intro i hi
        simp only [hst', elimStep]
        by_cases hil : i = st.1.length
        · subst hil; rw [getD_snoc_eq]; exact hr_prop.1
        · rw [getD_snoc_ne _ _ _ _ hil]; exact hneq i hi
      have hrec := ih st' (by simp only [hst', elimStep, List.length_append]; omega) hneq' hzero'
      refine ⟨hrec.1, ?_⟩
      obtain ⟨_, t2, _, h2, _, _⟩ := elim_prefix 10 gs st'
      have hdrop : (elim 10 gs st').2.drop st.2.length = r.1.toList ++ t2 := by
        rw [h2]
        simp only [hst', elimStep, List.append_assoc]
        exact List.drop_left
      have hdrop' : (elim 10 gs st').2.drop st'.2.length = t2 := by
        rw [h2]; exact List.drop_left
      rw [hdrop]
      intro g' hg'
      rw [List.mem_append] at hg'
      rcases hg' with hg' | hg'
      · exact hr_prop.2 g' (Option.mem_toList.1 hg')
      · exact hrec.2 g' (by rwa [hdrop'])

theorem L_meta_518_aux : ∀ s : ℕ, HasCircuitSize 10 fG s → 14 ≤ s := by
  intro s hs
  by_contra hlt
  have hs13 : s ≤ 13 := by omega
  obtain ⟨C0, hfan0, hsize0, heval0, hnok0, hmin0⟩ := exists_min_circuit hs
  set s0 := C0.size with hs0_def
  have hs0_13 : s0 ≤ 13 := le_trans hsize0 hs13
  have hex_k : ∃ k ≤ s0, ∃ C : Circuit, FanInTwo C ∧ (∀ g ∈ C.gates, NOk g) ∧
      C.size = s0 ∧ (∀ x, C.eval (List.ofFn x) = fG x) ∧ HasTopOrs C k :=
    ⟨0, Nat.zero_le _, C0, hfan0, hnok0, rfl, heval0, Nat.zero_le _, Or.inl rfl⟩
  let P : ℕ → Prop := fun k => k ≤ s0 ∧ ∃ C : Circuit, FanInTwo C ∧ (∀ g ∈ C.gates, NOk g) ∧
    C.size = s0 ∧ (∀ x, C.eval (List.ofFn x) = fG x) ∧ HasTopOrs C k
  have hmax : ∃ k, P k ∧ ∀ k', P k' → k' ≤ k := by
    classical
    have hfin : (Finset.filter (fun k => P k) (Finset.range (s0 + 1))).Nonempty := by
      obtain ⟨k, hk, hC⟩ := hex_k
      exact ⟨k, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hk, hC⟩⟩
    obtain ⟨k, hk_mem, hk_max⟩ := Finset.exists_max_image _ id hfin
    refine ⟨k, (Finset.mem_filter.1 hk_mem).2, fun k' hk' => ?_⟩
    exact hk_max k' (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by have := hk'.1; omega), hk'⟩)
  obtain ⟨k, ⟨hk_le, C, hfan, hnok, hsize, heval, htop⟩, hk_max⟩ := hmax
  have hmin : ∀ D : Circuit, FanInTwo D → (∀ x, D.eval (List.ofFn x) = fG x) → C.size ≤ D.size := by
    intro D hDf hDe
    rw [hsize, hs0_def]
    exact hmin0 D hDf hDe
  have hncf : ∃ x y, fG x ≠ fG y := ⟨fun _ => false, fun i => decide (i = 0 ∨ i = 8), by decide⟩
  have hC13 : C.size ≤ 13 := by omega
  have hfo : ∀ u ∈ Sset, ∃ (lit : ℕ) (bin : ℕ) (hbin : bin < C.gates.length),
      ((lit = u.val ∧ (∀ t (ht : t < C.gates.length), u.val ∈ (C.gates[t]).inputs → t = bin)) ∨
        (∃ jn, ∃ hjn : jn < C.gates.length, lit = 10 + jn ∧ (C.gates[jn]).op = GateOp.not ∧
          (C.gates[jn]).inputs = [u.val] ∧
          (∀ t (ht : t < C.gates.length), u.val ∈ (C.gates[t]).inputs → t = jn) ∧
          (∀ t (ht : t < C.gates.length), 10 + jn ∈ (C.gates[t]).inputs → t = bin))) ∧
      lit ∈ (C.gates[bin]).inputs ∧
      ((C.gates[bin]).op = GateOp.and ∨ (C.gates[bin]).op = GateOp.or) := by
    intro u hu
    obtain ⟨t1, ht1, hmem1, huniq1, hnot1⟩ := fanout_S_eq_one C hfan hnok heval hmin hC13 u hu
    rcases min_gate_shape hfan heval hnok hmin hncf t1 ht1 with ⟨hop1, a1, hl1, _⟩ | ⟨hop1, _⟩
    · obtain ⟨t2, ht2, hmem2, huniq2, hop2⟩ := hnot1 hop1
      have ha1 : a1 = u.val := by rw [hl1] at hmem1; simpa [eq_comm] using hmem1
      subst ha1
      exact ⟨10 + t1, t2, ht2, Or.inr ⟨t1, ht1, rfl, hop1, hl1, huniq1, huniq2⟩, hmem2, hop2⟩
    · exact ⟨u.val, t1, ht1, Or.inl ⟨rfl, huniq1⟩, hmem1, hop1⟩
  classical
  let litOf : Fin 10 → ℕ := fun u =>
    if hu : u ∈ Sset then (hfo u hu).choose else 0
  let binOf : Fin 10 → ℕ := fun u =>
    if hu : u ∈ Sset then (hfo u hu).choose_spec.choose else 0
  have hS_ne : Sset.Nonempty := ⟨3, by decide⟩
  obtain ⟨v, hvS, hv_min⟩ := Finset.exists_min_image Sset binOf hS_ne
  set j := binOf v with hj_def
  set lv := litOf v with hlv_def
  have hfo_spec : ∀ u (hu : u ∈ Sset),
      ∃ hbin : binOf u < C.gates.length,
        ((litOf u = u.val ∧ (∀ t (ht : t < C.gates.length), u.val ∈ (C.gates[t]).inputs → t = binOf u)) ∨
          (∃ jn, ∃ hjn : jn < C.gates.length, litOf u = 10 + jn ∧ (C.gates[jn]).op = GateOp.not ∧
            (C.gates[jn]).inputs = [u.val] ∧
            (∀ t (ht : t < C.gates.length), u.val ∈ (C.gates[t]).inputs → t = jn) ∧
            (∀ t (ht : t < C.gates.length), 10 + jn ∈ (C.gates[t]).inputs → t = binOf u))) ∧
        litOf u ∈ (C.gates[binOf u]).inputs ∧
        ((C.gates[binOf u]).op = GateOp.and ∨ (C.gates[binOf u]).op = GateOp.or) := by
    intro u hu
    simpa only [litOf, binOf, hu, ↓reduceDIte] using (hfo u hu).choose_spec.choose_spec
  obtain ⟨hj_lt, hlv_cases, hlv_mem, hj_op⟩ := hfo_spec v hvS
  simp only [← hj_def] at hj_lt hlv_cases hlv_mem hj_op
  simp only [← hlv_def] at hlv_cases hlv_mem
  have hlit_val : ∀ u (hu : u ∈ Sset) (x : Fin 10 → Bool),
      (wiresFrom C.gates (List.ofFn x)).getD (litOf u) false =
        if litOf u = u.val then x u else !(x u) := by
    intro u hu x
    obtain ⟨_, hcases, _, _⟩ := hfo_spec u hu
    rcases hcases with ⟨heq, _⟩ | ⟨jn, hjn, heq, hopn, hln, _, _⟩
    · simp only [heq, ↓reduceIte]
      rw [getD_wiresFrom _ _ _ (by simp [u.isLt]), getD_ofFn_fin]
    · have hne : litOf u ≠ u.val := by have := u.isLt; omega
      rw [if_neg hne, heq]
      have hgv := gate_value C.gates (List.ofFn x) jn hjn
      simp only [List.length_ofFn] at hgv
      rw [hgv, hopn, hln]
      have hlt : u.val < 10 + jn := by have := u.isLt; omega
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons, hlt, ↓reduceIte]
      rw [getD_wiresFrom _ _ _ (by simp [u.isLt]), getD_ofFn_fin]
  have hv_only_j : ∀ (y : Fin 10 → Bool),
      (wiresFrom C.gates (List.ofFn (Function.update y v false))).getD (10 + j) false =
      (wiresFrom C.gates (List.ofFn (Function.update y v true))).getD (10 + j) false →
      fG (Function.update y v false) = fG (Function.update y v true) := by
    intro y hjeq
    set x1 := Function.update y v false
    set x2 := Function.update y v true
    have hwire_eq : ∀ p, p < 10 + C.gates.length → p ≠ v.val → p ≠ lv →
        (wiresFrom C.gates (List.ofFn x1)).getD p false =
        (wiresFrom C.gates (List.ofFn x2)).getD p false := by
      intro p
      induction p using Nat.strong_induction_on with
      | ind p ih =>
        intro hp hpv hplv
        by_cases hp10 : p < 10
        · rw [getD_wiresFrom _ _ _ (by simp [hp10]), getD_wiresFrom _ _ _ (by simp [hp10])]
          simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hp10, ↓reduceDIte, Option.getD_some]
          have hne : (⟨p, hp10⟩ : Fin 10) ≠ v := fun e => hpv (congrArg Fin.val e)
          simp [x1, x2, Function.update_of_ne hne]
        · set t := p - 10 with ht_def
          have hp_eq : p = 10 + t := by omega
          have ht_lt : t < C.gates.length := by omega
          by_cases htj : t = j
          · rw [hp_eq, htj]; exact hjeq
          · rw [hp_eq]
            have hgv1 := gate_value C.gates (List.ofFn x1) t ht_lt
            have hgv2 := gate_value C.gates (List.ofFn x2) t ht_lt
            simp only [List.length_ofFn] at hgv1 hgv2
            rw [hgv1, hgv2]
            congr 1
            apply List.map_congr_left
            intro r hr
            split_ifs with hrt
            · have hrv : r ≠ v.val := by
                intro e
                subst e
                rcases hlv_cases with ⟨_, huniq⟩ | ⟨jn, _, heq, _, _, huniq, _⟩
                · exact htj (huniq t ht_lt hr)
                · exact hplv (by rw [hp_eq, heq, huniq t ht_lt hr])
              have hrlv : r ≠ lv := by
                intro e
                subst e
                rcases hlv_cases with ⟨heq, huniq⟩ | ⟨jn, _, heq, _, _, _, huniq⟩
                · exact htj (huniq t ht_lt (heq ▸ hr))
                · exact htj (huniq t ht_lt (heq ▸ hr))
              exact ih r (by omega) (by omega) hrv hrlv
            · rfl
    rw [← heval x1, ← heval x2]
    simp only [Circuit.eval, wires_eq]
    by_cases ho_lt : C.output < 10 + C.gates.length
    · have ho_nv : C.output ≠ v.val := by
        intro e
        have h1 := heval (fun i => decide (i = 0 ∨ i = 8))
        simp only [Circuit.eval, wires_eq, e] at h1
        rw [getD_wiresFrom _ _ _ (by simp [v.isLt])] at h1
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, v.isLt, ↓reduceDIte, Option.getD_some] at h1
        have hfalse : decide (v = 0 ∨ v = 8) = false := by fin_cases v <;> simp [Sset] at hvS ⊢
        have htrue : fG (fun i => decide (i = 0 ∨ i = 8)) = true := by decide
        rw [hfalse, htrue] at h1; exact Bool.false_ne_true h1
      have ho_nlv : C.output ≠ lv := by
        intro e
        have h1 := heval (fun _ => false)
        have h2 := hlit_val v hvS (fun _ => false)
        simp only [Circuit.eval, wires_eq, e] at h1
        rw [h1] at h2
        have hf0 : fG (fun _ => false) = false := by decide
        rw [hf0] at h2
        split_ifs at h2 with hif
        · exact ho_nv (e.trans hif)
        · simp at h2
      exact hwire_eq C.output ho_lt ho_nv ho_nlv
    · rw [List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega),
        List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)]
  have hshape_j := min_gate_shape hfan heval hnok hmin hncf j hj_lt
  obtain ⟨a, d, hj_ins, ha_lt, hd_lt, had_ne⟩ : ∃ a d, (C.gates[j]).inputs = [a, d] ∧
      a < 10 + j ∧ d < 10 + j ∧ a ≠ d := by
    rcases hshape_j with ⟨hnot, _⟩ | ⟨_, a, d, hl, ha, hd, hne⟩
    · rcases hj_op with h | h <;> (rw [hnot] at h; cases h)
    · exact ⟨a, d, hl, ha, hd, hne⟩
  obtain ⟨w, hw_lt, hw_ne, hw_mem, hj_pair⟩ :
      ∃ w, w < 10 + j ∧ w ≠ lv ∧ w ∈ (C.gates[j]).inputs ∧
        ((C.gates[j]).inputs = [lv, w] ∨ (C.gates[j]).inputs = [w, lv]) := by
    rw [hj_ins] at hlv_mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlv_mem
    rcases hlv_mem with rfl | rfl
    · exact ⟨d, hd_lt, had_ne.symm, by simp [hj_ins], Or.inl hj_ins⟩
    · exact ⟨a, ha_lt, had_ne, by simp [hj_ins], Or.inr hj_ins⟩
  have hsupp_before_j : ∀ p, p < 10 + j →
      (suppsFrom C.gates (inputSupps 10)).getD p ∅ ⊆ Tset ∨
      ∃ u, ∃ _ : u ∈ Sset, p = u.val ∨ p = litOf u := by
    intro p
    induction p using Nat.strong_induction_on with
    | ind p ih =>
      intro hp
      by_cases hp10 : p < 10
      · by_cases hmemS : (⟨p, hp10⟩ : Fin 10) ∈ Sset
        · exact Or.inr ⟨⟨p, hp10⟩, hmemS, Or.inl rfl⟩
        · left
          rw [getD_suppsFrom _ _ _ (by simp [inputSupps, hp10])]
          simp only [inputSupps, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hp10, ↓reduceDIte,
            Option.getD_some, Finset.singleton_subset_iff]
          exact (mem_Tset_iff _).2 hmemS
      · set q := p - 10 with hq_def
        have hp_eq : p = 10 + q := by omega
        have hq_lt : q < j := by omega
        have hq_C : q < C.gates.length := by omega
        by_cases hex_lit : ∃ u, ∃ _ : u ∈ Sset, p = litOf u
        · obtain ⟨u, hu, heq⟩ := hex_lit
          exact Or.inr ⟨u, hu, Or.inr heq⟩
        · left
          have hsupp_q : (suppsFrom C.gates (inputSupps 10)).getD p ∅ =
              gateSupp (suppsFrom (C.gates.take q) (inputSupps 10)) (C.gates[q]) := by
            have hsplit : C.gates = C.gates.take q ++ C.gates[q] :: C.gates.drop (q + 1) := by simp
            conv_lhs => rw [hsplit, suppsFrom_append, suppsFrom_cons]
            have hlen_tq : (suppsFrom (C.gates.take q) (inputSupps 10)).length = p := by
              rw [length_suppsFrom, List.length_take, Nat.min_eq_left hq_C.le]
              simp [inputSupps, hp_eq]
            rw [getD_suppsFrom _ _ _ (by simp [hlen_tq])]
            rw [show p = (suppsFrom (C.gates.take q) (inputSupps 10)).length by omega, getD_snoc_eq]
          rw [hsupp_q]
          intro x hx
          obtain ⟨r, hr_mem, hxr⟩ := (mem_gateSupp _ _ x).1 hx
          have hr_lt : r < p := by
            rcases min_gate_shape hfan heval hnok hmin hncf q hq_C with ⟨_, a', hl', ha'⟩ | ⟨_, a', d', hl', ha', hd', _⟩
            · rw [hl'] at hr_mem; simp only [List.mem_singleton] at hr_mem; omega
            · rw [hl'] at hr_mem; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_mem
              rcases hr_mem with rfl | rfl <;> omega
          have hxr' : x ∈ (suppsFrom C.gates (inputSupps 10)).getD r ∅ := by
            have hlen_tq : (suppsFrom (C.gates.take q) (inputSupps 10)).length = p := by
              rw [length_suppsFrom, List.length_take, Nat.min_eq_left hq_C.le]
              simp [inputSupps, hp_eq]
            have h1 : (suppsFrom C.gates (inputSupps 10)).getD r ∅ =
                (suppsFrom (C.gates.take q) (inputSupps 10)).getD r ∅ := by
              conv_lhs => rw [← List.take_append_drop q C.gates, suppsFrom_append]
              exact getD_suppsFrom _ _ _ (by omega)
            rwa [h1]
          rcases ih r hr_lt (by omega) with hrT | ⟨u, huS, hr_u | hr_lu⟩
          · exact hrT hxr'
          · exfalso
            have hju : j ≤ binOf u := hv_min u huS
            obtain ⟨_, hucases, _, _⟩ := hfo_spec u huS
            rcases hucases with ⟨_, huniq⟩ | ⟨jn, _, hlitu, _, _, huniq, _⟩
            · have := huniq q hq_C (hr_u ▸ hr_mem); omega
            · have hq_jn : q = jn := huniq q hq_C (hr_u ▸ hr_mem)
              exact hex_lit ⟨u, huS, by omega⟩
          · exfalso
            have hju : j ≤ binOf u := hv_min u huS
            obtain ⟨_, hucases, _, _⟩ := hfo_spec u huS
            rcases hucases with ⟨hlitu, huniq⟩ | ⟨jn, _, hlitu, _, _, _, huniq⟩
            · have := huniq q hq_C (hlitu ▸ hr_lu ▸ hr_mem); omega
            · have := huniq q hq_C (hlitu ▸ hr_lu ▸ hr_mem); omega
  set c := decide ((C.gates[j]).op = GateOp.or) with hc_def
  have hlv_lt : lv < 10 + j := by
    rcases hj_pair with h | h <;> rw [h] at hj_ins <;>
      (simp only [List.cons.injEq, and_true] at hj_ins; omega)
  have hgate_j_ctrl : ∀ y : Fin 10 → Bool,
      (wiresFrom C.gates (List.ofFn (Function.update y v false))).getD w false = c →
      (wiresFrom C.gates (List.ofFn (Function.update y v true))).getD w false = c →
      fG (Function.update y v false) = fG (Function.update y v true) := by
    intro y hw1 hw2
    apply hv_only_j y
    have hgv1 := gate_value C.gates (List.ofFn (Function.update y v false)) j hj_lt
    have hgv2 := gate_value C.gates (List.ofFn (Function.update y v true)) j hj_lt
    simp only [List.length_ofFn] at hgv1 hgv2
    rw [hgv1, hgv2]
    rcases hj_op with hop | hop
    · have hc_f : c = false := by simp [hc_def, hop]
      rw [hc_f] at hw1 hw2
      rcases hj_pair with hpair | hpair <;>
        (rw [hop, hpair]; simp only [GateOp.eval, List.map_cons, List.map_nil, hw_lt, hlv_lt, ↓reduceIte, hw1, hw2]; simp)
    · have hc_t : c = true := by simp [hc_def, hop]
      rw [hc_t] at hw1 hw2
      rcases hj_pair with hpair | hpair <;>
        (rw [hop, hpair]; simp only [GateOp.eval, List.map_cons, List.map_nil, hw_lt, hlv_lt, ↓reduceIte, hw1, hw2]; simp)
  have hw_T_all : (suppsFrom C.gates (inputSupps 10)).getD w ∅ ⊆ Tset := by
    rcases hsupp_before_j w hw_lt with hT | ⟨u, huS, hw_u | hw_lu⟩
    · exact hT
    · exfalso
      obtain ⟨_, hucases, _, _⟩ := hfo_spec u huS
      rcases hucases with ⟨hlitu, huniq⟩ | ⟨jn, hjn, hlitu, hopn, _, huniq, _⟩
      · have huv : u ≠ v := fun e => hw_ne (by rw [hw_u, ← hlitu, e, hlv_def])
        obtain ⟨y, hyu, hydep⟩ := fG_dep_after_fix u v huS hvS huv c
        apply hydep
        apply hgate_j_ctrl y
        · rw [hw_u, getD_wiresFrom _ _ _ (by simp [u.isLt]), getD_ofFn_fin, Function.update_of_ne huv, hyu]
        · rw [hw_u, getD_wiresFrom _ _ _ (by simp [u.isLt]), getD_ofFn_fin, Function.update_of_ne huv, hyu]
      · have hj_jn : j = jn := huniq j hj_lt (hw_u ▸ hw_mem)
        simp only [hj_jn, hopn] at hj_op
        rcases hj_op with h | h <;> cases h
    · exfalso
      have huv : u ≠ v := fun e => hw_ne (by rw [hw_lu, e])
      let bu := if litOf u = u.val then c else !c
      obtain ⟨y, hyu, hydep⟩ := fG_dep_after_fix u v huS hvS huv bu
      apply hydep
      apply hgate_j_ctrl y
      · rw [hw_lu, hlit_val u huS]
        simp only [Function.update_of_ne huv, hyu, bu]
        split_ifs <;> simp
      · rw [hw_lu, hlit_val u huS]
        simp only [Function.update_of_ne huv, hyu, bu]
        split_ifs <;> simp
  have hw_fGT : ∀ x : Fin 10 → Bool,
      (wiresFrom C.gates (List.ofFn x)).getD w false = c → fGT x = true := by
    intro x hwx
    by_contra hnt
    have hf0 : fGT x = false := by cases h : fGT x <;> first | rfl | exact (hnt h).elim
    obtain ⟨y, hyT, hy0, hy1⟩ := fG_extend_S x hf0 v hvS
    have hagr_w : ∀ z : Fin 10 → Bool, (∀ i ∈ Tset, z i = x i) →
        (wiresFrom C.gates (List.ofFn z)).getD w false = c := by
      intro z hzT
      have hagr := agree_wiresFrom z x C.gates (inputSupps 10) (List.ofFn z) (List.ofFn x) (agree_inputs z x)
      rw [hagr.2.2 w (fun i hi => hzT i (hw_T_all hi)), hwx]
    have hw1 : (wiresFrom C.gates (List.ofFn (Function.update y v false))).getD w false = c :=
      hagr_w _ (fun i hi => by
        have hiv : i ≠ v := fun e => by rw [e] at hi; exact (mem_Tset_iff v).1 hi hvS
        rw [Function.update_of_ne hiv, hyT i hi])
    have hw2 : (wiresFrom C.gates (List.ofFn (Function.update y v true))).getD w false = c :=
      hagr_w _ (fun i hi => by
        have hiv : i ≠ v := fun e => by rw [e] at hi; exact (mem_Tset_iff v).1 hi hvS
        rw [Function.update_of_ne hiv, hyT i hi])
    have heq : fG (Function.update y v false) = fG (Function.update y v true) :=
      hgate_j_ctrl y hw1 hw2
    rw [hy0, hy1] at heq; exact Bool.false_ne_true heq
  have habsorb : ∀ x, (wiresFrom C.gates (List.ofFn x)).getD w false = c → fG x = true :=
    fun x h => fG_of_fGT x (hw_fGT x h)
  have hnc_notc : ∃ x y, (wiresFrom C.gates (List.ofFn x)).getD w false = !c ∧
      (wiresFrom C.gates (List.ofFn y)).getD w false = !c ∧ fG x ≠ fG y := by
    obtain ⟨x, y, hfx, hfy, hxy⟩ := fG_nc_on_fGT_false
    refine ⟨x, y, ?_, ?_, hxy⟩
    · by_contra h
      have heq : (wiresFrom C.gates (List.ofFn x)).getD w false = c := by
        cases h1 : (wiresFrom C.gates (List.ofFn x)).getD w false <;> cases h2 : c <;>
          first | rfl | exact (h (by rw [h1, h2]; rfl)).elim
      have := hw_fGT x heq; rw [hfx] at this; exact Bool.false_ne_true this
    · by_contra h
      have heq : (wiresFrom C.gates (List.ofFn y)).getD w false = c := by
        cases h1 : (wiresFrom C.gates (List.ofFn y)).getD w false <;> cases h2 : c <;>
          first | rfl | exact (h (by rw [h1, h2]; rfl)).elim
      have := hw_fGT y heq; rw [hfy] at this; exact Bool.false_ne_true this
  have hw10 : 10 ≤ w := by
    by_contra hlt10
    have hw_fin : w < 10 := by omega
    let i0 : Fin 10 := ⟨w, hw_fin⟩
    cases hc : c
    · have h1 : (wiresFrom C.gates (List.ofFn (fun _ : Fin 10 => false))).getD w false = false := by
        rw [getD_wiresFrom _ _ _ (by simp [hw_fin])]
        exact getD_ofFn_fin (fun _ : Fin 10 => false) i0 false
      have h2 := habsorb (fun _ => false) (by rw [hc]; exact h1)
      exact Bool.false_ne_true ((by decide : fG (fun _ => false) = false).symm.trans h2)
    · have h1 : (wiresFrom C.gates (List.ofFn (fun t : Fin 10 => decide (t = i0)))).getD w false = true := by
        rw [getD_wiresFrom _ _ _ (by simp [hw_fin])]
        have := getD_ofFn_fin (fun t : Fin 10 => decide (t = i0)) i0 false
        simpa [i0] using this
      have h2 := habsorb (fun t => decide (t = i0)) (by rw [hc]; exact h1)
      have h3 : ∀ i : Fin 10, fG (fun t => decide (t = i)) = false := by decide
      rw [h3 i0] at h2; exact Bool.false_ne_true h2
  have hbody_len : (C.gates.take (C.gates.length - k)).length = C.gates.length - k := by
    rw [List.length_take, Nat.min_eq_left (by have := htop.1; omega)]
  have hj_body : j < C.gates.length - k := by
    by_contra hj_ge
    rcases htop.2 with hk0 | ⟨hCout, o0, ho0, htop_spec⟩
    · omega
    · set i0 := j - (C.gates.length - k) with hi0_def
      have hi0_lt : i0 < k := by omega
      obtain ⟨h_i, h_lt, h_T, h_eq⟩ := htop_spec i0 (by simp; omega)
      have hgj : C.gates[j] = ⟨GateOp.or, [h_i, if i0 = 0 then o0 else 10 + (C.gates.take (C.gates.length - k)).length + i0 - 1]⟩ := by
        have : (C.gates.drop (C.gates.length - k))[i0]'(by simp; omega) = C.gates[j] := by
          simp [List.getElem_drop, show C.gates.length - k + i0 = j by omega]
        rw [← this, h_eq]
      have hlv_notin_T : ¬ (suppsFrom C.gates (inputSupps 10)).getD lv ∅ ⊆ Tset := by
        intro hsub
        have hv_in : v ∈ (suppsFrom C.gates (inputSupps 10)).getD lv ∅ := by
          rcases hlv_cases with ⟨heq, _⟩ | ⟨jn, hjn, heq, _, hln, _, _⟩
          · rw [heq, getD_suppsFrom _ _ _ (by simp [inputSupps, v.isLt]), inputSupps, getD_ofFn_fin]
            simp
          · rw [heq]
            have hsplit : C.gates = C.gates.take jn ++ C.gates[jn] :: C.gates.drop (jn + 1) := by simp
            conv_lhs => rw [hsplit, suppsFrom_append, suppsFrom_cons]
            have hlen_jn : (suppsFrom (C.gates.take jn) (inputSupps 10)).length = 10 + jn := by
              rw [length_suppsFrom, List.length_take, Nat.min_eq_left hjn.le]; simp [inputSupps]
            rw [getD_suppsFrom _ _ _ (by simp [hlen_jn]), ← hlen_jn, getD_snoc_eq, mem_gateSupp]
            refine ⟨v.val, by simp [hln], ?_⟩
            rw [getD_suppsFrom _ _ _ (by simp [inputSupps, v.isLt]), inputSupps, getD_ofFn_fin]
            simp
        exact (mem_Tset_iff v).1 (hsub hv_in) hvS
      have hh_T_all : (suppsFrom C.gates (inputSupps 10)).getD h_i ∅ ⊆ Tset := by
        conv_lhs => rw [← List.take_append_drop (C.gates.length - k) C.gates, suppsFrom_append]
        rw [getD_suppsFrom _ _ _ (by rw [length_suppsFrom]; simp [inputSupps]; omega)]
        exact h_T
      have hlv_eq_prev : lv = if i0 = 0 then o0 else 10 + (C.gates.take (C.gates.length - k)).length + i0 - 1 := by
        rw [hgj] at hlv_mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hlv_mem
        rcases hlv_mem with rfl | h2
        · exact (hlv_notin_T hh_T_all).elim
        · exact h2
      have hi0_zero : i0 = 0 := by
        by_contra hne0
        simp only [hne0, ↓reduceIte] at hlv_eq_prev
        have hlt_prev : 10 + (C.gates.take (C.gates.length - k)).length + i0 - 1 = 10 + (j - 1) := by omega
        rw [hlt_prev] at hlv_eq_prev
        rcases hlv_cases with ⟨heq, _⟩ | ⟨jn, hjn, heq, hopn, _, _, _⟩
        · have := v.isLt; omega
        · have hjn_eq : jn = j - 1 := by omega
          have hi1 : i0 - 1 < k := by omega
          obtain ⟨_, _, _, hprev_eq⟩ := htop_spec (i0 - 1) (by simp; omega)
          have hgjn : C.gates[jn] = (C.gates.drop (C.gates.length - k))[i0 - 1]'(by simp; omega) := by
            simp [List.getElem_drop, show C.gates.length - k + (i0 - 1) = jn by omega]
          rw [hgjn, hprev_eq] at hopn
          cases hopn
      rw [hi0_zero, if_pos rfl] at hlv_eq_prev hgj
      have hout_supp : ∀ m (hm : m < k),
          (suppsFrom C.gates (inputSupps 10)).getD (10 + (C.gates.length - k) + m) ∅ ⊆
            Tset ∪ {v} := by
        intro m
        induction m with
        | zero =>
          intro hm
          have hj_eq : j = C.gates.length - k := by omega
          have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by simp
          rw [add_zero, ← hj_eq]
          conv_lhs => rw [hsplit, suppsFrom_append, suppsFrom_cons]
          have hlen_j : (suppsFrom (C.gates.take j) (inputSupps 10)).length = 10 + j := by
            rw [length_suppsFrom, List.length_take, Nat.min_eq_left hj_lt.le]; simp [inputSupps]
          rw [getD_suppsFrom _ _ _ (by simp [hlen_j]), ← hlen_j, getD_snoc_eq]
          intro x hx
          obtain ⟨r, hr, hxr⟩ := (mem_gateSupp _ _ x).1 hx
          rw [hgj] at hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          have hxr' : x ∈ (suppsFrom C.gates (inputSupps 10)).getD r ∅ := by
            conv_lhs => rw [← List.take_append_drop j C.gates, suppsFrom_append]
            have hr_lt : r < 10 + j := by rcases hr with rfl | rfl <;> omega
            rwa [getD_suppsFrom _ _ _ (by omega)]
          rcases hr with rfl | rfl
          · exact Finset.mem_union_left _ (hh_T_all hxr')
          · rw [← hlv_eq_prev] at hxr'
            have hlv_supp : (suppsFrom C.gates (inputSupps 10)).getD lv ∅ = {v} := by
              rcases hlv_cases with ⟨heq, _⟩ | ⟨jn, hjn, heq, _, hln, _, _⟩
              · rw [heq, getD_suppsFrom _ _ _ (by simp [inputSupps, v.isLt]), inputSupps, getD_ofFn_fin]
              · rw [heq]
                have hs2 : C.gates = C.gates.take jn ++ C.gates[jn] :: C.gates.drop (jn + 1) := by simp
                conv_lhs => rw [hs2, suppsFrom_append, suppsFrom_cons]
                have hl2 : (suppsFrom (C.gates.take jn) (inputSupps 10)).length = 10 + jn := by
                  rw [length_suppsFrom, List.length_take, Nat.min_eq_left hjn.le]; simp [inputSupps]
                rw [getD_suppsFrom _ _ _ (by simp [hl2]), ← hl2, getD_snoc_eq]
                ext z
                simp only [mem_gateSupp, hln, List.mem_singleton, exists_eq_left]
                rw [getD_suppsFrom _ _ _ (by simp [inputSupps, v.isLt]), inputSupps, getD_ofFn_fin]
            rw [hlv_supp] at hxr'
            exact Finset.mem_union_right _ hxr'
        | succ m ih =>
          intro hm
          obtain ⟨hm_i, hm_lt, hm_T, hm_eq⟩ := htop_spec (m + 1) (by simp; omega)
          set idx := C.gates.length - k + (m + 1)
          have hidx_lt : idx < C.gates.length := by omega
          have hgidx : C.gates[idx] = ⟨GateOp.or, [hm_i, 10 + (C.gates.length - k) + m]⟩ := by
            have : (C.gates.drop (C.gates.length - k))[m + 1]'(by simp; omega) = C.gates[idx] := by
              simp [List.getElem_drop, idx]
            rw [← this, hm_eq]; simp [hbody_len]
          have hsplit : C.gates = C.gates.take idx ++ C.gates[idx] :: C.gates.drop (idx + 1) := by simp
          rw [show 10 + (C.gates.length - k) + (m + 1) = 10 + idx by omega]
          conv_lhs => rw [hsplit, suppsFrom_append, suppsFrom_cons]
          have hlen_idx : (suppsFrom (C.gates.take idx) (inputSupps 10)).length = 10 + idx := by
            rw [length_suppsFrom, List.length_take, Nat.min_eq_left hidx_lt.le]; simp [inputSupps]
          rw [getD_suppsFrom _ _ _ (by simp [hlen_idx]), ← hlen_idx, getD_snoc_eq]
          intro x hx
          obtain ⟨r, hr, hxr⟩ := (mem_gateSupp _ _ x).1 hx
          rw [hgidx] at hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          have hxr' : x ∈ (suppsFrom C.gates (inputSupps 10)).getD r ∅ := by
            conv_lhs => rw [← List.take_append_drop idx C.gates, suppsFrom_append]
            have hr_lt : r < 10 + idx := by rcases hr with rfl | rfl <;> omega
            rwa [getD_suppsFrom _ _ _ (by omega)]
          rcases hr with hr | hr <;> subst r
          · have h1 : (suppsFrom C.gates (inputSupps 10)).getD hm_i ∅ ⊆ Tset := by
              conv_lhs => rw [← List.take_append_drop (C.gates.length - k) C.gates, suppsFrom_append]
              rw [getD_suppsFrom _ _ _ (by rw [length_suppsFrom]; simp [inputSupps]; omega)]
              exact hm_T
            exact Finset.mem_union_left _ (h1 hxr')
          · exact ih (by omega) hxr'
      have hu_ex : ∃ u ∈ Sset, u ≠ v := by
        fin_cases v <;> simp [Sset] at hvS
        · exact ⟨4, by decide, by decide⟩
        · exact ⟨3, by decide, by decide⟩
        · exact ⟨3, by decide, by decide⟩
        · exact ⟨3, by decide, by decide⟩
      obtain ⟨u, huS, huv⟩ := hu_ex
      obtain ⟨x, hx⟩ := fG_dep_S u huS
      have hout_sub := hout_supp (k - 1) (by omega)
      rw [show 10 + (C.gates.length - k) + (k - 1) = C.output by omega] at hout_sub
      have hagr := agree_wiresFrom (Function.update x u (!x u)) x C.gates (inputSupps 10)
        (List.ofFn (Function.update x u (!x u))) (List.ofFn x) (agree_inputs _ _)
      have heq := hagr.2.2 C.output (fun z hz => by
        have hzu : z ≠ u := by
          intro e
          subst e
          have hmem := hout_sub hz
          simp only [Finset.mem_union, Finset.mem_singleton] at hmem
          rcases hmem with hT | rfl
          · exact (mem_Tset_iff z).1 hT huS
          · exact huv rfl
        simp [Function.update_of_ne hzu])
      apply hx
      rw [← heval _, ← heval _]
      exact heq
  have hwB : w < 10 + (C.gates.length - k) := by omega
  have hwT_body : (suppsFrom (C.gates.take (C.gates.length - k)) (inputSupps 10)).getD w ∅ ⊆ Tset := by
    have h1 : (suppsFrom C.gates (inputSupps 10)).getD w ∅ =
        (suppsFrom (C.gates.take (C.gates.length - k)) (inputSupps 10)).getD w ∅ := by
      conv_lhs => rw [← List.take_append_drop (C.gates.length - k) C.gates, suppsFrom_append]
      exact getD_suppsFrom _ _ _ (by rw [length_suppsFrom]; simp [inputSupps, hbody_len]; omega)
    rwa [← h1]
  rcases hj_op with hop_and | hop_or
  · have hc_false : c = false := by simp [hc_def, hop_and]
    by_cases hother : ∃ t', ∃ _ : t' < C.gates.length, t' ≠ j ∧ w ∈ (C.gates[t']).inputs
    · obtain ⟨t', ht', ht'_ne, ht'_mem⟩ := hother
      have ht'_gt : w < 10 + t' := by
        rcases min_gate_shape hfan heval hnok hmin hncf t' ht' with ⟨_, a', hl', ha'⟩ | ⟨_, a', d', hl', ha', hd', _⟩
        · rw [hl'] at ht'_mem; simp only [List.mem_singleton] at ht'_mem; omega
        · rw [hl'] at ht'_mem; simp only [List.mem_cons, List.not_mem_nil, or_false] at ht'_mem
          rcases ht'_mem with rfl | rfl <;> omega
      have ht'_body : t' < C.gates.length - k := by
        by_contra ht'_ge
        rcases htop.2 with hk0 | ⟨hCout, o0, ho0, htop_spec⟩
        · omega
        · set i0 := t' - (C.gates.length - k)
          have hi0_lt : i0 < k := by omega
          obtain ⟨h_i, h_lt, h_T, h_eq⟩ := htop_spec i0 (by simp; omega)
          have hgt' : C.gates[t'] = ⟨GateOp.or, [h_i, if i0 = 0 then o0 else 10 + (C.gates.take (C.gates.length - k)).length + i0 - 1]⟩ := by
            have : (C.gates.drop (C.gates.length - k))[i0]'(by simp; omega) = C.gates[t'] := by
              simp [List.getElem_drop, show C.gates.length - k + i0 = t' by omega]
            rw [← this, h_eq]
          rw [hgt'] at ht'_mem
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ht'_mem
          rcases ht'_mem with hw_hi | hw_prev
          · have htrue : ∀ x, (wiresFrom C.gates (List.ofFn x)).getD w false = true → fG x = true := by
              intro x hwx
              have hchain_true : ∀ m, i0 ≤ m → m < k →
                  (wiresFrom C.gates (List.ofFn x)).getD (10 + (C.gates.length - k) + m) false = true := by
                intro m
                induction m with
                | zero =>
                  intro h0m hm
                  have hi00 : i0 = 0 := by omega
                  have ht'_eq : t' = C.gates.length - k := by omega
                  rw [add_zero, ← ht'_eq]
                  have hgv := gate_value C.gates (List.ofFn x) t' ht'
                  simp only [List.length_ofFn] at hgv
                  rw [hgv, hgt', ← hw_hi]
                  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
                    Bool.or_false, show w < 10 + t' by omega, ↓reduceIte, hwx, Bool.true_or]
                | succ m ih =>
                  intro h0m hm
                  by_cases hm_eq : i0 = m + 1
                  · have ht'_eq : t' = C.gates.length - k + (m + 1) := by omega
                    rw [show 10 + (C.gates.length - k) + (m + 1) = 10 + t' by omega]
                    have hgv := gate_value C.gates (List.ofFn x) t' ht'
                    simp only [List.length_ofFn] at hgv
                    rw [hgv, hgt', ← hw_hi]
                    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
                      Bool.or_false, show w < 10 + t' by omega, ↓reduceIte, hwx, Bool.true_or]
                  · obtain ⟨hm_i, _, _, hm_eq2⟩ := htop_spec (m + 1) (by simp; omega)
                    set idx := C.gates.length - k + (m + 1)
                    have hidx_lt : idx < C.gates.length := by omega
                    have hgidx : C.gates[idx] = ⟨GateOp.or, [hm_i, 10 + (C.gates.length - k) + m]⟩ := by
                      have : (C.gates.drop (C.gates.length - k))[m + 1]'(by simp; omega) = C.gates[idx] := by
                        simp [List.getElem_drop, idx]
                      rw [← this, hm_eq2]; simp [hbody_len]
                    rw [show 10 + (C.gates.length - k) + (m + 1) = 10 + idx by omega]
                    have hgv := gate_value C.gates (List.ofFn x) idx hidx_lt
                    simp only [List.length_ofFn] at hgv
                    rw [hgv, hgidx]
                    have hprev := ih (by omega) (by omega)
                    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
                      Bool.or_false, show 10 + (C.gates.length - k) + m < 10 + idx by omega, ↓reduceIte,
                      hprev, Bool.or_true]
              rw [← heval x]
              simp only [Circuit.eval, wires_eq, show C.output = 10 + (C.gates.length - k) + (k - 1) by omega]
              exact hchain_true (k - 1) (by omega) (by omega)
            cases h0 : (wiresFrom C.gates (List.ofFn (fun _ : Fin 10 => false))).getD w false
            · have h1 := habsorb (fun _ => false) (by rw [hc_false]; exact h0)
              exact Bool.false_ne_true ((by decide : fG (fun _ => false) = false).symm.trans h1)
            · have h1 := htrue (fun _ => false) h0
              exact Bool.false_ne_true ((by decide : fG (fun _ => false) = false).symm.trans h1)
          · have hi00 : i0 = 0 := by
              by_contra hne0
              simp only [hne0, ↓reduceIte] at hw_prev
              omega
            rw [hi00, if_pos rfl] at hw_prev hgt'
            have hout_T : ∀ m (hm : m < k),
                (suppsFrom C.gates (inputSupps 10)).getD (10 + (C.gates.length - k) + m) ∅ ⊆ Tset := by
              intro m
              induction m with
              | zero =>
                intro hm
                have ht'_eq : t' = C.gates.length - k := by omega
                rw [add_zero, ← ht'_eq]
                have hsplit : C.gates = C.gates.take t' ++ C.gates[t'] :: C.gates.drop (t' + 1) := by simp
                conv_lhs => rw [hsplit, suppsFrom_append, suppsFrom_cons]
                have hlen_t' : (suppsFrom (C.gates.take t') (inputSupps 10)).length = 10 + t' := by
                  rw [length_suppsFrom, List.length_take, Nat.min_eq_left ht'.le]; simp [inputSupps]
                rw [getD_suppsFrom _ _ _ (by simp [hlen_t']), ← hlen_t', getD_snoc_eq]
                intro x hx
                obtain ⟨r, hr, hxr⟩ := (mem_gateSupp _ _ x).1 hx
                rw [hgt'] at hr
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
                have hxr' : x ∈ (suppsFrom C.gates (inputSupps 10)).getD r ∅ := by
                  conv_lhs => rw [← List.take_append_drop t' C.gates, suppsFrom_append]
                  have hr_lt : r < 10 + t' := by rcases hr with rfl | rfl <;> omega
                  rwa [getD_suppsFrom _ _ _ (by omega)]
                rcases hr with hr | hr <;> subst r
                · have h1 : (suppsFrom C.gates (inputSupps 10)).getD h_i ∅ ⊆ Tset := by
                    conv_lhs => rw [← List.take_append_drop (C.gates.length - k) C.gates, suppsFrom_append]
                    rw [getD_suppsFrom _ _ _ (by rw [length_suppsFrom]; simp [inputSupps]; omega)]
                    exact h_T
                  exact h1 hxr'
                · rw [← hw_prev] at hxr'; exact hw_T_all hxr'
              | succ m ih =>
                intro hm
                obtain ⟨hm_i, hm_lt, hm_T, hm_eq⟩ := htop_spec (m + 1) (by simp; omega)
                set idx := C.gates.length - k + (m + 1)
                have hidx_lt : idx < C.gates.length := by omega
                have hgidx : C.gates[idx] = ⟨GateOp.or, [hm_i, 10 + (C.gates.length - k) + m]⟩ := by
                  have : (C.gates.drop (C.gates.length - k))[m + 1]'(by simp; omega) = C.gates[idx] := by
                    simp [List.getElem_drop, idx]
                  rw [← this, hm_eq]; simp [hbody_len]
                have hsplit : C.gates = C.gates.take idx ++ C.gates[idx] :: C.gates.drop (idx + 1) := by simp
                rw [show 10 + (C.gates.length - k) + (m + 1) = 10 + idx by omega]
                conv_lhs => rw [hsplit, suppsFrom_append, suppsFrom_cons]
                have hlen_idx : (suppsFrom (C.gates.take idx) (inputSupps 10)).length = 10 + idx := by
                  rw [length_suppsFrom, List.length_take, Nat.min_eq_left hidx_lt.le]; simp [inputSupps]
                rw [getD_suppsFrom _ _ _ (by simp [hlen_idx]), ← hlen_idx, getD_snoc_eq]
                intro x hx
                obtain ⟨r, hr, hxr⟩ := (mem_gateSupp _ _ x).1 hx
                rw [hgidx] at hr
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
                have hxr' : x ∈ (suppsFrom C.gates (inputSupps 10)).getD r ∅ := by
                  conv_lhs => rw [← List.take_append_drop idx C.gates, suppsFrom_append]
                  have hr_lt : r < 10 + idx := by rcases hr with rfl | rfl <;> omega
                  rwa [getD_suppsFrom _ _ _ (by omega)]
                rcases hr with hr | hr <;> subst r
                · have h1 : (suppsFrom C.gates (inputSupps 10)).getD hm_i ∅ ⊆ Tset := by
                    conv_lhs => rw [← List.take_append_drop (C.gates.length - k) C.gates, suppsFrom_append]
                    rw [getD_suppsFrom _ _ _ (by rw [length_suppsFrom]; simp [inputSupps]; omega)]
                    exact hm_T
                  exact h1 hxr'
                · exact ih (by omega) hxr'
            obtain ⟨x, hx⟩ := fG_dep_S 3 (by decide)
            have hout_sub := hout_T (k - 1) (by omega)
            rw [show 10 + (C.gates.length - k) + (k - 1) = C.output by omega] at hout_sub
            have hagr := agree_wiresFrom (Function.update x 3 (!x 3)) x C.gates (inputSupps 10)
              (List.ofFn (Function.update x 3 (!x 3))) (List.ofFn x) (agree_inputs _ _)
            have heq := hagr.2.2 C.output (fun z hz => by
              have hz3 : z ≠ 3 := fun e => by rw [e] at hz; exact (mem_Tset_iff 3).1 (hout_sub hz) (by decide)
              simp [Function.update_of_ne hz3])
            apply hx; rw [← heval _, ← heval _]; exact heq
      set Sskip : Finset ℕ := {j - (w - 9), t' - (w - 9)}
      have hcard_S : Sskip.card = if c then 1 else 2 := by
        rw [hc_false, if_neg Bool.false_ne_true]
        exact Finset.card_pair (by omega)
      obtain ⟨D, hDf, hDnok, hDs, hDe, hDtop⟩ := peel_wire C hfan hnok heval hmin k htop w hw10 hwB
        hwT_body c habsorb hnc_notc Sskip hcard_S (by
          intro t ht
          simp only [Sskip, Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl
          · refine ⟨by simp [hbody_len]; omega, ?_⟩
            have : ((C.gates.take (C.gates.length - k)).drop (w - 9))[j - (w - 9)]'(by simp [hbody_len]; omega) = C.gates[j] := by
              rw [List.getElem_drop, List.getElem_take]; congr 1; omega
            rw [this]; exact hw_mem
          · refine ⟨by simp [hbody_len]; omega, ?_⟩
            have : ((C.gates.take (C.gates.length - k)).drop (w - 9))[t' - (w - 9)]'(by simp [hbody_len]; omega) = C.gates[t'] := by
              rw [List.getElem_drop, List.getElem_take]; congr 1; omega
            rw [this]; exact ht'_mem)
      have hle := hk_max (k + 1) ⟨by rw [← hsize, ← hDs]; exact hDtop.1, D, hDf, hDnok, by omega, hDe, hDtop⟩
      omega
    · push_neg at hother
      set q := w - 10 with hq_def
      have hw_eq : w = 10 + q := by omega
      have hq_lt : q < j := by omega
      have hq_C : q < C.gates.length := by omega
      have hCout_ne_w : C.output ≠ w := by
        intro e
        obtain ⟨x, hx⟩ := fG_dep_S 3 (by decide)
        have hagr := agree_wiresFrom (Function.update x 3 (!x 3)) x C.gates (inputSupps 10)
          (List.ofFn (Function.update x 3 (!x 3))) (List.ofFn x) (agree_inputs _ _)
        have heq := hagr.2.2 C.output (fun z hz => by
          rw [e] at hz
          have hz3 : z ≠ 3 := fun h => by rw [h] at hz; exact (mem_Tset_iff 3).1 (hw_T_all hz) (by decide)
          simp [Function.update_of_ne hz3])
        apply hx; rw [← heval _, ← heval _]; exact heq
      set bv : Bool := decide (lv ≠ v.val) with hbv_def
      set st0 : List Stat × List Gate := (seedInput 10 v bv, []) with hst0_def
      have hst0_len1 : st0.1.length = 10 := by simp [hst0_def, seedInput]
      have hlv_zero : (elim 10 (C.gates.take j) st0).1.getD lv (Sum.inl false) = Sum.inl false := by
        rcases hlv_cases with ⟨heq, _⟩ | ⟨jn, hjn, heq, hopn, hln, _, _⟩
        · have hbv_f : bv = false := by simp [hbv_def, heq]
          obtain ⟨l1, _, h1, _, _, _⟩ := elim_prefix 10 (C.gates.take j) st0
          rw [heq, h1, List.getD_append _ _ _ _ (by rw [hst0_len1]; exact v.isLt)]
          rw [hst0_def]; dsimp only; rw [seedInput, getD_ofFn_fin]; simp [hbv_f]
        · have hbv_t : bv = true := by
            have hne : lv ≠ v.val := by have := v.isLt; omega
            simp [hbv_def, hne]
          have hjn_lt : jn < j := by omega
          have hstep := elim_take_step_eq 10 C.gates st0 jn hjn
          rw [hst0_len1] at hstep
          have hv_at : (elim 10 (C.gates.take jn) st0).1.getD v.val (Sum.inl false) = Sum.inl true := by
            obtain ⟨l1, _, h1, _, _, _⟩ := elim_prefix 10 (C.gates.take jn) st0
            rw [h1, List.getD_append _ _ _ _ (by rw [hst0_len1]; exact v.isLt)]
            rw [hst0_def]; dsimp only; rw [seedInput, getD_ofFn_fin]; simp [hbv_t]
          have hjn_c : (elim 10 (C.gates.take (jn + 1)) st0).1.getD (10 + jn) (Sum.inl false) = Sum.inl false := by
            rw [hstep, hopn, hln]; simp only [List.map_cons, List.map_nil, hv_at, simplify, simpNot]; rfl
          have hpers := elim_take_const_persist 10 C.gates st0 jn j false hjn_lt
            (by rw [hst0_len1]; exact hjn_c)
          rw [heq]; rwa [hst0_len1] at hpers
      have hshape_all : ∀ t (ht : t < C.gates.length),
          ((C.gates[t]).op = GateOp.not ∧ (C.gates[t]).inputs.length = 1 ∧ ∀ a ∈ (C.gates[t]).inputs, a < 10 + t) ∨
          (((C.gates[t]).op = GateOp.and ∨ (C.gates[t]).op = GateOp.or) ∧ (C.gates[t]).inputs.length = 2 ∧
            ∀ a ∈ (C.gates[t]).inputs, a < 10 + t) := by
        intro t ht
        rcases min_gate_shape hfan heval hnok hmin hncf t ht with ⟨hop, a, hl, ha⟩ | ⟨hop, a, d, hl, ha, hd, _⟩
        · left; refine ⟨hop, by simp [hl], fun x hx => by rw [hl] at hx; simp at hx; omega⟩
        · right; refine ⟨hop, by simp [hl], fun x hx => by
            rw [hl] at hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl <;> omega⟩
      have hst_q_inr : ∀ i, i < (suppsFrom (C.gates.take q) (inputSupps 10)).length →
          v ∉ (suppsFrom (C.gates.take q) (inputSupps 10)).getD i ∅ →
          ∃ r, (elim 10 (C.gates.take q) st0).1.getD i (Sum.inl false) = Sum.inr r := by
        apply elim_not_in_supp_inr_lt (C.gates.take q) 10 (by
          intro t ht
          have htC : t < C.gates.length := by simp at ht; omega
          simpa [List.getElem_take] using hshape_all t htC) v st0 (inputSupps 10)
          (by simp [hst0_def, seedInput, inputSupps]) (by simp [inputSupps])
        intro i hi hvi
        simp only [inputSupps, List.length_ofFn] at hi
        simp only [inputSupps, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte,
          Option.getD_some, Finset.mem_singleton] at hvi
        have hne : (⟨i, hi⟩ : Fin 10) ≠ v := fun e => hvi e.symm
        refine ⟨i, ?_⟩
        rw [hst0_def]; dsimp only
        have h1 := getD_ofFn_fin (fun k : Fin 10 => if k = v then Sum.inl bv else Sum.inr k.val) ⟨i, hi⟩ (Sum.inl false)
        rw [seedInput]; simpa [hne] using h1
      set st_q := elim 10 (C.gates.take q) st0 with hst_q
      set q' := st_q.2.length with hq'_def
      have hq_nv : v ∉ (suppsFrom (C.gates.take (q + 1)) (inputSupps 10)).getD (10 + q) ∅ := by
        have h1 : (suppsFrom C.gates (inputSupps 10)).getD (10 + q) ∅ =
            (suppsFrom (C.gates.take (q + 1)) (inputSupps 10)).getD (10 + q) ∅ := by
          conv_lhs => rw [← List.take_append_drop (q + 1) C.gates, suppsFrom_append]
          exact getD_suppsFrom _ _ _ (by rw [length_suppsFrom, List.length_take, Nat.min_eq_left hq_C]; simp [inputSupps])
        rw [← h1, ← hw_eq]
        intro hv_in
        exact (mem_Tset_iff v).1 (hw_T_all hv_in) hvS
      have hq_emits : ∃ g', (simplify (C.gates[q]).op (10 + q')
          ((C.gates[q]).inputs.map fun i => st_q.1.getD i (Sum.inl false))) = (some g', Sum.inr (10 + q')) := by
        have hq_supp_eq : (suppsFrom (C.gates.take (q + 1)) (inputSupps 10)).getD (10 + q) ∅ =
            gateSupp (suppsFrom (C.gates.take q) (inputSupps 10)) (C.gates[q]) := by
          rw [List.take_succ_eq_append_getElem hq_C, suppsFrom_append, suppsFrom_cons]
          have hlen_tq : (suppsFrom (C.gates.take q) (inputSupps 10)).length = 10 + q := by
            rw [length_suppsFrom, List.length_take, Nat.min_eq_left hq_C.le]; simp [inputSupps]
          rw [← hlen_tq]
          change (suppsFrom [] _).getD _ ∅ = _
          simp [suppsFrom, getD_snoc_eq]
        rw [hq_supp_eq] at hq_nv
        have harg : ∀ a ∈ (C.gates[q]).inputs, a < 10 + q → ∃ r, st_q.1.getD a (Sum.inl false) = Sum.inr r := by
          intro a ha hal
          apply hst_q_inr a (by rw [length_suppsFrom, List.length_take, Nat.min_eq_left hq_C.le]; simp [inputSupps]; exact hal)
          intro hv_a
          exact hq_nv ((mem_gateSupp _ _ v).2 ⟨a, ha, hv_a⟩)
        rcases hshape_all q hq_C with ⟨hop, hlen_q, hlt_q⟩ | ⟨hop | hop, hlen_q, hlt_q⟩
        · rcases hq_in : (C.gates[q]).inputs with _ | ⟨a, _ | ⟨b, l⟩⟩
          · simp [hq_in] at hlen_q
          · obtain ⟨ra, hra⟩ := harg a (by simp [hq_in]) (hlt_q a (by simp [hq_in]))
            exact ⟨⟨GateOp.not, [ra]⟩, by rw [hop]; simp only [List.map_cons, List.map_nil, hra, simplify, simpNot]⟩
          · simp [hq_in] at hlen_q
        · rcases hq_in : (C.gates[q]).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
          · simp [hq_in] at hlen_q
          · simp [hq_in] at hlen_q
          · obtain ⟨ra, hra⟩ := harg a (by simp [hq_in]) (hlt_q a (by simp [hq_in]))
            obtain ⟨rb, hrb⟩ := harg b (by simp [hq_in]) (hlt_q b (by simp [hq_in]))
            exact ⟨⟨GateOp.and, [ra, rb]⟩, by rw [hop]; simp only [List.map_cons, List.map_nil, hra, hrb, simplify, simpAnd]⟩
          · simp [hq_in] at hlen_q
        · rcases hq_in : (C.gates[q]).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
          · simp [hq_in] at hlen_q
          · simp [hq_in] at hlen_q
          · obtain ⟨ra, hra⟩ := harg a (by simp [hq_in]) (hlt_q a (by simp [hq_in]))
            obtain ⟨rb, hrb⟩ := harg b (by simp [hq_in]) (hlt_q b (by simp [hq_in]))
            exact ⟨⟨GateOp.or, [ra, rb]⟩, by rw [hop]; simp only [List.map_cons, List.map_nil, hra, hrb, simplify, simpOr]⟩
          · simp [hq_in] at hlen_q
      obtain ⟨gq', hgq'⟩ := hq_emits
      set st_q1 := elim 10 (C.gates.take (q + 1)) st0 with hst_q1
      have hst_q1_eq : st_q1 = (st_q.1 ++ [Sum.inr (10 + q')], st_q.2 ++ [gq']) := by
        rw [hst_q1, List.take_succ_eq_append_getElem hq_C, elim_append, ← hst_q]
        change elimStep 10 st_q C.gates[q] = _
        simp only [elimStep, ← hq'_def, hgq', Option.toList_some]
      have hst_q_len1 : st_q.1.length = 10 + q := by
        obtain ⟨l1, _, h1, _, hl1, _⟩ := elim_prefix 10 (C.gates.take q) st0
        rw [hst_q, h1, List.length_append, hl1, List.length_take, Nat.min_eq_left hq_C.le]
        simp [hst0_def, seedInput]
      have hst_q_val : ∀ i, Stat.Valid (10 + q') (st_q.1.getD i (Sum.inl false)) := by
        apply elim_valid 10 (C.gates.take q) st0
        intro i
        by_cases hi : i < 10
        · simp only [hst0_def, seedInput, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte,
            Option.getD_some, List.length_nil, add_zero]
          split_ifs <;> simp [Stat.Valid, hi]
        · simp [hst0_def, seedInput, List.getD_eq_getElem?_getD, hi, Stat.Valid]
      have hst_q1_neq : ∀ i, i ≠ w → st_q1.1.getD i (Sum.inl false) ≠ Sum.inr (10 + q') := by
        intro i hi
        rw [hst_q1_eq]
        rw [getD_snoc_ne _ _ _ _ (by omega)]
        have hv := hst_q_val i
        cases hst : st_q.1.getD i (Sum.inl false) with
        | inl _ => simp
        | inr r =>
          rw [hst] at hv; simp only [Stat.Valid] at hv
          intro h; have := Sum.inr.inj h; omega
      have hst_q1_len2 : st_q1.2.length = q' + 1 := by rw [hst_q1_eq]; simp [hq'_def]
      set res := elim 10 C.gates st0 with hres_def
      have hres_split : res = elim 10 (C.gates.drop (q + 1)) st_q1 := by
        rw [hres_def, hst_q1, ← elim_append, List.take_append_drop]
      have hunused := elim_unused_wire w (10 + q') (C.gates.drop (q + 1)) st_q1
        (by rw [hst_q1_len2]; omega) hst_q1_neq (by
          intro t ht hmem
          have htC : q + 1 + t < C.gates.length := by simp at ht; omega
          have hmemC : w ∈ (C.gates[q + 1 + t]).inputs := by simpa [List.getElem_drop] using hmem
          have hteq : q + 1 + t = j := by
            by_contra hne
            exact hother (q + 1 + t) htC hne hmemC
          have htake_eq : C.gates.take (q + 1) ++ (C.gates.drop (q + 1)).take t = C.gates.take j :=
            (List.take_add (i := q + 1) (j := t) (l := C.gates)).symm.trans (by rw [hteq])
          have helim_eq : elim 10 ((C.gates.drop (q + 1)).take t) st_q1 = elim 10 (C.gates.take j) st0 := by
            rw [hst_q1, ← elim_append, htake_eq]
          rw [helim_eq]
          have hgt_eq : (C.gates.drop (q + 1))[t] = C.gates[j] := by
            simp [List.getElem_drop, hteq]
          rw [hgt_eq, hop_and]
          rcases hj_pair with hp | hp <;> rw [hp] <;> simp only [List.map_cons, List.map_nil, hlv_zero, simplify]
          · cases (elim 10 (C.gates.take j) st0).1.getD w (Sum.inl false) with
            | inl b => cases b <;> rfl
            | inr r => rfl
          · cases (elim 10 (C.gates.take j) st0).1.getD w (Sum.inl false) with
            | inl b => cases b <;> rfl
            | inr r => rfl)
      rw [← hres_split, hst_q1_len2] at hunused
      have hj_zero : (elim 10 (C.gates.take (j + 1)) st0).1.getD (10 + j) (Sum.inl false) = Sum.inl false := by
        have hstep := elim_take_step_eq 10 C.gates st0 j hj_lt
        rw [hst0_len1] at hstep
        rw [hstep, hop_and]
        rcases hj_pair with hp | hp <;> rw [hp] <;> simp only [List.map_cons, List.map_nil, hlv_zero, simplify]
        · cases (elim 10 (C.gates.take j) st0).1.getD w (Sum.inl false) with
          | inl b => cases b <;> rfl
          | inr r => rfl
        · cases (elim 10 (C.gates.take j) st0).1.getD w (Sum.inl false) with
          | inl b => cases b <;> rfl
          | inr r => rfl
      have hres_inv : ∀ x, Inv 10 (wiresFrom C.gates (List.ofFn (Function.update x v bv))) (List.ofFn x) res :=
        fun x => inv_elim 10 C.gates (fun g hg => (hnok g hg).1) _ _ _ (seedInput_inv v bv x)
      have hj_reader : ∃ t2, ∃ _ : t2 < C.gates.length, j < t2 ∧ 10 + j ∈ (C.gates[t2]).inputs := by
        rcases min_no_dead hfan heval hmin j hj_lt with ho | ⟨t2, ht2, hlt2, hmem2⟩
        · exfalso
          obtain ⟨x, y, hxy⟩ := fG_nc_fix v hvS bv
          have hpers := elim_take_const_persist 10 C.gates st0 j C.gates.length false hj_lt
            (by rw [hst0_len1]; exact hj_zero)
          rw [List.take_of_length_le le_rfl, hst0_len1, ← hres_def] at hpers
          have hx := (hres_inv x).2.2 C.output
          have hy := (hres_inv y).2.2 C.output
          rw [ho, hpers] at hx hy
          apply hxy
          rw [← heval _, ← heval _]
          simp only [Circuit.eval, wires_eq, ho, ← hx.2, ← hy.2, Stat.val]
        · exact ⟨t2, ht2, hlt2, hmem2⟩
      obtain ⟨t2, ht2, hlt2, hmem2⟩ := hj_reader
      have hres_out : ∃ o', res.1.getD C.output (Sum.inl false) = Sum.inr o' := by
        cases ho : res.1.getD C.output (Sum.inl false) with
        | inl b =>
          exfalso
          obtain ⟨x, y, hxy⟩ := fG_nc_fix v hvS bv
          have hx := (hres_inv x).2.2 C.output
          have hy := (hres_inv y).2.2 C.output
          rw [ho] at hx hy
          apply hxy
          rw [← heval _, ← heval _]
          simp only [Circuit.eval, wires_eq, ← hx.2, ← hy.2, Stat.val]
        | inr o' => exact ⟨o', rfl⟩
      obtain ⟨o', ho'⟩ := hres_out
      have ho'_ne : o' ≠ 10 + q' := by
        intro e
        have h1 := hunused.1 C.output hCout_ne_w
        rw [ho', e] at h1
        exact h1 rfl
      have hq'_lt_res : q' < res.2.length := by
        obtain ⟨_, t2_l, _, h2, _, _⟩ := elim_prefix 10 (C.gates.drop (q + 1)) st_q1
        rw [hres_split, h2, List.length_append, hst_q1_len2]; omega
      set D2 : Circuit := ⟨del res.2 q' (10 + q') 0, ren (10 + q') 0 o'⟩
      have hD2_fan : FanInTwo D2 := fanInTwo_del res.2 o' q' (10 + q') 0 _
        (elim_ok 10 C.gates st0 (by simp [hst0_def]))
      have hD2_eval : ∀ x : Fin 10 → Bool, D2.eval (List.ofFn x) = fG (Function.update x v bv) := by
        intro x
        have hdel := del_eval res.2 o' (List.ofFn x) q' 0 hq'_lt_res (Or.inl (by simp))
          (fun g hg hmem => (hunused.2 g hg (by simpa using hmem)).elim)
          (fun heq => (ho'_ne (by simpa using heq)).elim)
        simp only [List.length_ofFn] at hdel
        rw [hdel]
        have hx := (hres_inv x).2.2 C.output
        rw [ho'] at hx
        rw [← heval _]
        simpa [Circuit.eval, wires_eq, Stat.val] using hx.2
      have hD2_size : D2.size = res.2.length - 1 := del_length res.2 q' (10 + q') 0 hq'_lt_res
      rcases hlv_cases with ⟨heq, _⟩ | ⟨jn, hjn, heq, _, hln, _, _⟩
      · have hbv_f : bv = false := by simp [hbv_def, heq]
        have hcnt := elim_skips_count 10 C.gates hnok st0 {j, t2} (by
          intro t ht
          simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with ht | ht <;> subst t
          · exact ⟨hj_lt, lv, hlv_mem, false, hlv_zero⟩
          · exact ⟨ht2, 10 + j, hmem2, false, by
              have hpers := elim_take_const_persist 10 C.gates st0 j t2 false hlt2
                (by rw [hst0_len1]; exact hj_zero)
              rwa [hst0_len1] at hpers⟩)
        have hcard2 : ({j, t2} : Finset ℕ).card = 2 := Finset.card_pair (by omega)
        have hres_le : res.2.length ≤ 11 := by
          rw [← hres_def] at hcnt
          simp only [hst0_def, List.length_nil, zero_add, hcard2] at hcnt
          simp only [Circuit.size] at hC13
          omega
        have h11 := fG_false_lower v hvS D2.size ⟨D2, hD2_fan, le_rfl, by simpa [hbv_f] using hD2_eval⟩
        omega
      · have hbv_t : bv = true := by
          have hne : lv ≠ v.val := by have := v.isLt; omega
          simp [hbv_def, hne]
        have hjn_lt : jn < j := by omega
        have hcnt := elim_skips_count 10 C.gates hnok st0 {jn, j, t2} (by
          intro t ht
          simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with ht | ht | ht <;> subst t
          · refine ⟨hjn, v.val, by simp [hln], true, ?_⟩
            obtain ⟨l1, _, h1, _, _, _⟩ := elim_prefix 10 (C.gates.take jn) st0
            rw [h1, List.getD_append _ _ _ _ (by rw [hst0_len1]; exact v.isLt)]
            rw [hst0_def]; dsimp only; rw [seedInput, getD_ofFn_fin]; simp [hbv_t]
          · exact ⟨hj_lt, lv, hlv_mem, false, hlv_zero⟩
          · exact ⟨ht2, 10 + j, hmem2, false, by
              have hpers := elim_take_const_persist 10 C.gates st0 j t2 false hlt2
                (by rw [hst0_len1]; exact hj_zero)
              rwa [hst0_len1] at hpers⟩)
        have hcard3 : ({jn, j, t2} : Finset ℕ).card = 3 := by
          rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_pair (by omega)]
        have hres_le : res.2.length ≤ 10 := by
          rw [← hres_def] at hcnt
          simp only [hst0_def, List.length_nil, zero_add, hcard3] at hcnt
          simp only [Circuit.size] at hC13
          omega
        have h10 := fG_true_lower v hvS D2.size ⟨D2, hD2_fan, le_rfl, by simpa [hbv_t] using hD2_eval⟩
        omega
  · have hc_true : c = true := by simp [hc_def, hop_or]
    set Sskip : Finset ℕ := {j - (w - 9)}
    have hcard_S : Sskip.card = if c then 1 else 2 := by
      rw [hc_true, if_pos rfl, Finset.card_singleton]
    obtain ⟨D, hDf, hDnok, hDs, hDe, hDtop⟩ := peel_wire C hfan hnok heval hmin k htop w hw10 hwB
      hwT_body c habsorb hnc_notc Sskip hcard_S (by
        intro t ht
        simp only [Sskip, Finset.mem_singleton] at ht
        subst ht
        refine ⟨by simp [hbody_len]; omega, ?_⟩
        have : ((C.gates.take (C.gates.length - k)).drop (w - 9))[j - (w - 9)]'(by simp [hbody_len]; omega) = C.gates[j] := by
          rw [List.getElem_drop, List.getElem_take]; congr 1; omega
        rw [this]; exact hw_mem)
    have hle := hk_max (k + 1) ⟨by rw [← hsize, ← hDs]; exact hDtop.1, D, hDf, hDnok, by omega, hDe, hDtop⟩
    omega

end PEqualNP.Outside.L518

theorem PEqualNP.Outside.L_meta_518 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 10 (fun x : Fin 10 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 1) || (x 0 && x 8) || (x 1 && x 9)) s → 14 ≤ s :=
  PEqualNP.Outside.L518.L_meta_518_aux
