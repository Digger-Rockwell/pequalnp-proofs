import Mathlib
import PEqualNP.Defs

namespace L573

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

section
variable {n : ℕ}
theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
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

theorem agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
end

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def renum (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

theorem renum_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨renum n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [renum, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this

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
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

abbrev Stat : Type := Sum Bool ℕ

def statVal (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Stat → Prop
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
      simp [simpAnd] at hg; (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg; (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg; (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · rcases a with (_ | _) | j <;> rcases b with (_ | _) | k <;>
        simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · rcases a with (_ | _) | j <;> rcases b with (_ | _) | k <;>
        simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem statVal_append (w t : List Bool) : ∀ s : Stat, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => (Sum.inr i.val : Stat)) ++ [Sum.inl b]

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => (Sum.inr i.val : Stat))).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, statValid, statVal, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

theorem supp_noread (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, n ∉ g.inputs) → (∀ j : ℕ, j ≠ n → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, j ≠ n → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem inputSupps_getD (m j : ℕ) (h : j < m) :
    (inputSupps m).getD j ∅ = {⟨j, h⟩} := by
  simp [inputSupps, h]

theorem inputSupps_noread (n : ℕ) : ∀ j : ℕ, j ≠ n →
    Fin.last n ∉ (inputSupps (n + 1)).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n + 1
  · have e : (inputSupps (n + 1)).getD j ∅ = {⟨j, hlt⟩} := inputSupps_getD (n + 1) j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem gate_elim (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f (s + 1)) :
    HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s + 1 := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      statVal (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD C.output (Sum.inl false))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  have hvalid : statValid (n + acc.2.length) (acc.1.getD C.output (Sum.inl false)) := by
    obtain ⟨y, _, _⟩ := hnc
    exact ((hinv y).2 C.output).1
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | inr j =>
    have hlen : acc.2.length ≤ s := by
      by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
      · have := elim_len_lt n n gs (initStats n b, []) hnok (by simp [initStats])
          ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push Not at hread
        have hout : C.output ≠ n := by
          intro e
          rw [e, hacc, elim_getD n n _ gs _ (by simp [initStats])] at hst
          have hb : (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
            getD_snoc_len _ _ _ _ (by simp)
          rw [show ((initStats n b, ([] : List Gate))).1 = initStats n b from rfl, hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hns := supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) C.output hout
        have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
          (agree_inputs _ _)).2.2 C.output (by
            intro k hk
            have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
            simp [Function.update_of_ne this])
        rw [← hevg, ← hevg]
        exact hag
    refine ⟨⟨acc.2, j⟩, elim_ok n gs _ (by simp), hlen, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
  getD_snoc_len _ _ _ _ (by simp)

theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Sum.inl b ∈ ins) : ∃ c, (simplify op m ins).2 = Sum.inl c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Sum.inl false) = Sum.inl c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
  rw [hnone]; simp

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Sum.inl false) = Sum.inl (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Sum.inl false) = Sum.inl c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Sum.inl false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

theorem suppsFrom_append {n : ℕ} (pre post : List Gate) (L : List (Finset (Fin n))) :
    suppsFrom (pre ++ post) L = suppsFrom post (suppsFrom pre L) := by
  simp [suppsFrom, List.foldl_append]

theorem length_suppsFrom {n : ℕ} (gs : List Gate) : ∀ L : List (Finset (Fin n)),
    (suppsFrom gs L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; rfl
  | cons g gs ih =>
    intro L
    have h : suppsFrom (g :: gs) L = suppsFrom gs (L ++ [gateSupp L g]) := rfl
    rw [h, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g

theorem CleanGate.nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g := by
  rcases h with ⟨h1, j, _, h2⟩ | ⟨h1 | h1, j, k, _, _, h2⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inr rfl)
    · rw [h2]; simp
    · intro _; rw [h2]; simp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inl rfl
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inl rfl)
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h

theorem CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  intro a ha
  rcases h with ⟨_, j, hj, h2⟩ | ⟨_, j, k, hj, hk, h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha; exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk

theorem clean_nok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs, NOk g := by
  intro g hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hg
  exact (h p g hp).nok

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, statValid m s) :
    ∀ g ∈ (simplify op m ins).1, CleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    refine Or.inr ⟨Or.inl rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    refine Or.inr ⟨Or.inr rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    refine Or.inl ⟨rfl, _, ?_, rfl⟩
    exact hv _ List.mem_cons_self
  · simp at hg
  · simp at hg

theorem toList_getElem? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]? = some a) : k = 0 ∧ a ∈ o := by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h

theorem clean_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv hcl
    have hinv' : Inv n y (wiresFrom [g] w) (elimStep n acc g) :=
      inv_elim n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    refine ih _ (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
    intro p g' hp
    have hp' : (acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)[p]? = some g' := hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨h0, hmem⟩ := toList_getElem? _ _ _ hp'
      have hpl : p = acc.2.length := by omega
      rw [hpl]
      exact simplify_clean _ _ _ (fun s hs => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        exact (hinv.2 a).1) g' hmem

def HasClean (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ gs.length ≤ s ∧
    ∀ x : Fin n → Bool, (wiresFrom gs (List.ofFn x)).getD o false = f x

def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => (Sum.inr i.val : Stat))

theorem inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, statValid, statVal, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem clean_of (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasCircuitSize n f s) : HasClean n f s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  have hok : ∀ g ∈ C.gates, Ok g := ok
  set acc := elim n C.gates (idStats n, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n → Bool,
      statVal (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD C.output (Sum.inl false)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]; rfl
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | inr j =>
    refine ⟨acc.2, j, ?_, ?_, ?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · have := elim_len n C.gates (idStats n, [])
      rw [← hacc] at this
      simp only [List.length_nil, zero_add] at this
      omega
    · intro y
      have := hval y
      rw [hst] at this
      exact this

theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp

def statAt (n : ℕ) (i : Fin (n + 1)) (b : Bool) : List Stat :=
  List.ofFn (Fin.insertNth i (Sum.inl b) (fun k : Fin n => (Sum.inr k.val : Stat)) : Fin (n + 1) → Stat)

theorem statAt_length (n : ℕ) (i : Fin (n + 1)) (b : Bool) : (statAt n i b).length = n + 1 := by
  simp [statAt]

theorem statAt_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) :
    (statAt n i b).getD i (Sum.inl false) = Sum.inl b := by
  rw [statAt, getD_ofFn, Fin.insertNth_apply_same]

theorem statAt_above (n : ℕ) (i : Fin (n + 1)) (b : Bool) (k : Fin n) :
    (statAt n i b).getD (i.succAbove k) (Sum.inl false) = Sum.inr k.val := by
  rw [statAt, getD_ofFn, Fin.insertNth_apply_succAbove]

theorem inv_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool))
      (statAt n i b, []) := by
  refine ⟨by simp [statAt], ?_⟩
  have key : ∀ j : Fin (n + 1),
      statValid (n + 0) ((statAt n i b).getD j (Sum.inl false)) ∧
      statVal (List.ofFn y) ((statAt n i b).getD j (Sum.inl false))
        = (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)).getD j false := by
    intro j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
    · rw [statAt_at, getD_ofFn, Fin.insertNth_apply_same]
      exact ⟨trivial, rfl⟩
    · rw [statAt_above, getD_ofFn, Fin.insertNth_apply_succAbove]
      refine ⟨?_, ?_⟩
      · show (k : ℕ) < n + 0
        have := k.isLt
        omega
      · show (List.ofFn y).getD k false = y k
        exact getD_ofFn n y false k
  intro j
  by_cases hlt : j < n + 1
  · exact key ⟨j, hlt⟩
  · show statValid (n + 0) ((statAt n i b).getD j (Sum.inl false)) ∧
      statVal (List.ofFn y) ((statAt n i b).getD j (Sum.inl false))
        = (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)).getD j false
    rw [List.getD_eq_default _ _ (by rw [statAt_length]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

def stF (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Stat :=
  (elim n gs (statAt n i b, [])).1.getD a (Sum.inl false)

theorem stF_self (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) :
    stF n gs i b i = Sum.inl b := by
  show (elim n gs (statAt n i b, [])).1.getD i (Sum.inl false) = _
  rw [elim_getD n i _ gs _ (by
    show (i : ℕ) < (statAt n i b).length
    rw [statAt_length]; exact i.isLt)]
  exact statAt_at n i b

theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩

theorem elim_split_getD (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a ≤ acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elimStep n (elim n pre acc) g).1.getD a d := by
  rw [elim_append, elim_cons, elim_getD n a d post _ (by
    show a < ((elim n pre acc).1 ++ [_]).length
    rw [List.length_append, elim_fst_len, List.length_singleton]; omega)]

theorem elim_split_getD_lt (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a < acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elim n pre acc).1.getD a d := by
  rw [elim_split_getD n pre g post acc a d (le_of_lt h)]
  show ((elim n pre acc).1 ++ [_]).getD a d = _
  exact getD_snoc_ne _ _ _ _ (by rw [elim_fst_len]; omega)

theorem const_of_read (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (hg : NOk g) (a : ℕ) (ha : a ∈ g.inputs)
    (hlt : a < acc.1.length + p)
    (hc : (elim n gs acc).1.getD a (Sum.inl false) = Sum.inl (fixBit g)) :
    ∃ c, (elim n gs acc).1.getD (acc.1.length + p) (Sum.inl false) = Sum.inl c := by
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  rw [elim_split_getD_lt n pre g post acc a _ hlt] at hc
  obtain ⟨c, hc'⟩ := elimStep_const n (elim n pre acc) g hg a ha hc
  refine ⟨c, ?_⟩
  rw [elim_split_getD n pre g post acc _ _ (le_refl _)]
  rw [elim_fst_len] at hc'
  exact hc'

theorem elim_count (n : ℕ) (acc : List Stat × List Gate) : ∀ gs : List Gate,
    (∀ g ∈ gs, NOk g) → ∀ S : Finset ℕ,
    (∀ p ∈ S, ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, a < acc.1.length + p ∧
        ∃ c, (elim n gs acc).1.getD a (Sum.inl false) = Sum.inl c) →
      (elim n gs acc).2.length + S.card ≤ acc.2.length + gs.length := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ S hS
    have hE : S = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      obtain ⟨g, hg, _⟩ := hS p hp
      simp at hg
    subst hE
    simp [elim]
  | append_singleton gs g ih =>
    intro hok S hS
    have hstep : elim n (gs ++ [g]) acc = elimStep n (elim n gs acc) g := by
      rw [elim_append]; rfl
    have hpre : ∀ (a : ℕ) (d : Stat), a < acc.1.length + gs.length →
        (elim n (gs ++ [g]) acc).1.getD a d = (elim n gs acc).1.getD a d :=
      fun a d h => elim_split_getD_lt n gs g [] acc a d h
    have hok' : ∀ g' ∈ gs, NOk g' := fun g' h => hok g' (List.mem_append_left _ h)
    have ih' := ih hok' (S.erase gs.length) (by
      intro p hp
      obtain ⟨hne, hpS⟩ := Finset.mem_erase.1 hp
      obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS p hpS
      have hpl : p < gs.length := by
        obtain ⟨h1, _⟩ := List.getElem?_eq_some_iff.1 hg'
        rw [List.length_append, List.length_singleton] at h1
        omega
      rw [List.getElem?_append_left hpl] at hg'
      rw [hpre a _ (by omega)] at hc
      exact ⟨g', hg', a, ha, hlt, c, hc⟩)
    rw [hstep, List.length_append, List.length_singleton]
    by_cases hin : gs.length ∈ S
    · obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS _ hin
      have hgg : g' = g := by
        rw [List.getElem?_concat_length] at hg'
        exact (Option.some.inj hg').symm
      subst hgg
      rw [hpre a _ hlt] at hc
      have h2 := elimStep_none n (elim n gs acc) g' (hok g' (by simp)) a ha c hc
      have hcard := Finset.card_erase_of_mem hin
      have hpos : 1 ≤ S.card := Finset.card_pos.2 ⟨_, hin⟩
      omega
    · have h2 : (elimStep n (elim n gs acc) g).2.length ≤ (elim n gs acc).2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + (elim n gs acc).2.length)
          (g.inputs.map fun i => (elim n gs acc).1.getD i (Sum.inl false))).1
        omega
      rw [Finset.erase_eq_of_notMem hin] at ih'
      omega

theorem agree_except (k : ℕ) (gs : List Gate) : ∀ w w' : List Bool,
    (∀ g ∈ gs, k ∉ g.inputs) → w.length = w'.length →
    (∀ j, j ≠ k → w.getD j false = w'.getD j false) →
    ∀ j, j ≠ k → (wiresFrom gs w).getD j false = (wiresFrom gs w').getD j false := by
  induction gs with
  | nil => intro w w' _ _ h; exact h
  | cons g gs ih =>
    intro w w' hno hl h
    have hno' := hno g List.mem_cons_self
    have e : (g.inputs.map fun i => w.getD i false) = g.inputs.map fun i => w'.getD i false :=
      List.map_congr_left (fun a ha => h a (fun e => hno' (e ▸ ha)))
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
      (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) (by simp [hl])
    intro j hj
    by_cases hjl : j = w.length
    · rw [hjl, getD_snoc_eq, hl, getD_snoc_eq, e]
    · rw [getD_snoc_ne _ _ _ _ hjl, getD_snoc_ne _ _ _ _ (by omega)]
      exact h j hj

def RC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (p : ℕ) : Prop :=
  ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, ∃ c, stF n gs i b a = Sum.inl c

theorem elim_prefix (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    ∃ t : List Gate, (elim n gs acc).2 = acc.2 ++ t := by
  induction gs with
  | nil => intro acc; exact ⟨[], by simp [elim]⟩
  | cons g gs ih =>
    intro acc
    obtain ⟨t, ht⟩ := ih (elimStep n acc g)
    refine ⟨(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList ++ t, ?_⟩
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ht]
    simp [elimStep]

def startStats (m h : ℕ) : List Stat :=
  (List.range m).map fun i => if i = h then Sum.inl true else Sum.inr i

theorem startStats_getD (m h i : ℕ) :
    (startStats m h).getD i (Sum.inl false) =
      if i < m then (if i = h then Sum.inl true else Sum.inr i) else Sum.inl false := by
  unfold startStats
  by_cases hi : i < m
  · simp [hi]
  · rw [List.getD_eq_default _ _ (by simp; omega)]; simp [hi]

theorem inv_start (n h : ℕ) (pre : List Gate) (y : List Bool) (hy : y.length = n)
    (hh : (wiresFrom pre y).getD h false = true) :
    Inv n y (wiresFrom pre y) (startStats (n + pre.length) h, pre) := by
  have lw : (wiresFrom pre y).length = n + pre.length := by rw [length_wiresFrom, hy]
  refine ⟨by simp [startStats, lw], ?_⟩
  intro i
  rw [startStats_getD]
  by_cases hi : i < n + pre.length
  · by_cases hih : i = h
    · subst hih; simp only [hi, ite_true]; exact ⟨trivial, hh.symm⟩
    · simp only [hi, hih, ite_true, ite_false]; exact ⟨hi, rfl⟩
  · simp only [hi, ite_false]
    exact ⟨trivial, by rw [List.getD_eq_default _ _ (by omega)]; rfl⟩

def vl {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) : Bool :=
  (wiresFrom gs (List.ofFn u)).getD j false

theorem vl_input {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) (h : j < k) :
    vl gs u j = u ⟨j, h⟩ := by
  unfold vl
  rw [getD_wiresFrom gs _ j (by simpa using h)]
  exact getD_ofFn k u false ⟨j, h⟩

theorem vl_gate {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) :
    vl gs u (k + p) = g.op.eval (g.inputs.map (vl gs u)) := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hwl : (wiresFrom pre (List.ofFn u)).length = k + pre.length := by
    rw [length_wiresFrom]; simp
  have e : wiresFrom (pre ++ g :: post) (List.ofFn u)
      = wiresFrom post (wiresFrom pre (List.ofFn u) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have full : ∀ j, j < k + pre.length →
      (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false
        = (wiresFrom pre (List.ofFn u)).getD j false := by
    intro j hj
    rw [e, getD_wiresFrom _ _ j (by simp [hwl]; omega), getD_snoc_ne _ _ _ _ (by omega)]
  have top : (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false) := by
    rw [e, getD_wiresFrom _ _ _ (by simp [hwl]), getD_snoc_len _ _ _ _ hwl]
  show (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
    = g.op.eval (g.inputs.map fun j => (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false)
  rw [top]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact (full a (hlt a ha)).symm

theorem vl_congr {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) (h : ∀ a ∈ g.inputs, vl gs u a = vl gs u' a) :
    vl gs u (k + p) = vl gs u' (k + p) := by
  rw [vl_gate gs hcl u p g hp, vl_gate gs hcl u' p g hp]
  congr 1
  exact List.map_congr_left h

theorem vl_abs {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (w : ℕ)
    (hw : w ∈ g.inputs) (hv : vl gs u w = fixBit g) : vl gs u (k + p) = fixBit g := by
  rw [vl_gate gs hcl u p g hp]
  rcases hop with h | h
  · have hf : fixBit g = false := by simp [fixBit, h]
    rw [hf] at hv ⊢
    rw [h]
    show (g.inputs.map (vl gs u)).all id = false
    rw [List.all_eq_false]
    exact ⟨vl gs u w, List.mem_map.2 ⟨w, hw, rfl⟩, by simp [hv]⟩
  · have hf : fixBit g = true := by simp [fixBit, h]
    rw [hf] at hv ⊢
    rw [h]
    show (g.inputs.map (vl gs u)).any id = true
    rw [List.any_eq_true]
    exact ⟨vl gs u w, List.mem_map.2 ⟨w, hw, rfl⟩, by simp [hv]⟩

theorem agree_B {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool)
    (B : ℕ → Prop) (L : ℕ) (hin : ∀ j, j < k → ¬ B j → vl gs u j = vl gs u' j)
    (hstep : ∀ p g, gs[p]? = some g → k + p < L → ¬ B (k + p) → (∃ a ∈ g.inputs, B a) →
      (∀ j, j < k + p → ¬ B j → vl gs u j = vl gs u' j) → vl gs u (k + p) = vl gs u' (k + p)) :
    ∀ j, j < L → ¬ B j → vl gs u j = vl gs u' j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjL hB
    by_cases hjk : j < k
    · exact hin j hjk hB
    · obtain ⟨p, rfl⟩ : ∃ p, j = k + p := ⟨j - k, by omega⟩
      cases hp : gs[p]? with
      | none =>
        have hlen : gs.length ≤ p := List.getElem?_eq_none_iff.1 hp
        have h1 : ∀ v : Fin k → Bool, vl gs v (k + p) = false := by
          intro v
          unfold vl
          exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)
        rw [h1, h1]
      | some g =>
        by_cases hr : ∃ a ∈ g.inputs, B a
        · exact hstep p g hp hjL hB hr (fun j' hj' hB' => ih j' hj' (by omega) hB')
        · exact vl_congr gs hcl u u' p g hp (fun a ha =>
            ih a ((hcl p g hp).lt a ha) (by have := (hcl p g hp).lt a ha; omega)
              (fun hBa => hr ⟨a, ha, hBa⟩))

theorem takes {k : ℕ} (gs : List Gate)
    (hM1 : ∀ p g, gs[p]? = some g → ∀ c, ¬ ∀ u : Fin k → Bool, vl gs u (k + p) = c)
    (w : ℕ) (hw : w < k + gs.length) (c : Bool) : ∃ u : Fin k → Bool, vl gs u w = c := by
  by_cases hwk : w < k
  · exact ⟨fun _ => c, by rw [vl_input gs _ w hwk]⟩
  · obtain ⟨p, rfl⟩ : ∃ p, w = k + p := ⟨w - k, by omega⟩
    have hpl : p < gs.length := by omega
    by_contra hno
    apply hM1 p gs[p] (List.getElem?_eq_getElem hpl) (!c)
    intro u
    have h := fun h => hno ⟨u, h⟩
    revert h
    cases vl gs u (k + p) <;> cases c <;> simp

theorem gate_eq {gs : List Gate} {p q : ℕ} {g g' : Gate} (h : gs[p]? = some g)
    (h' : gs[q]? = some g') (e : p = q) : g = g' := by
  subst e
  rw [h] at h'
  exact Option.some.inj h'

theorem two_inputs {m : ℕ} {g : Gate} (hg : CleanGate m g) (a b w : ℕ) (ha : a ∈ g.inputs)
    (hb : b ∈ g.inputs) (hab : a ≠ b) (hw : w ∈ g.inputs) : w = a ∨ w = b := by
  rcases hg with ⟨_, j, _, hin⟩ | ⟨_, j, k, _, _, hin⟩ <;> rw [hin] at ha hb hw <;>
    simp at ha hb hw <;> omega

theorem drop_core (k : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (hcl : CleanL k (pre ++ g :: post)) (o : ℕ) (S : Stat)
    (hS : ∀ y : Fin k → Bool, statValid (k + (elim k pre (idStats k, [])).2.length) S ∧
      statVal (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y)) S
        = vl (pre ++ g :: post) y (k + pre.length))
    (hnc : ∃ y y' : Fin k → Bool, vl (pre ++ g :: post) y o ≠ vl (pre ++ g :: post) y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ (pre ++ g :: post).length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl (pre ++ g :: post) y o := by
  have hok : ∀ g' ∈ pre ++ g :: post, Ok g' := fun g' hg' => (clean_nok _ _ hcl g' hg').1
  have hokpre : ∀ g' ∈ pre, Ok g' := fun g' h => hok g' (List.mem_append_left _ h)
  have hokpost : ∀ g' ∈ post, Ok g' :=
    fun g' h => hok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have inv1 : ∀ y : Fin k → Bool, Inv k (List.ofFn y) (wiresFrom pre (List.ofFn y))
      (elim k pre (idStats k, [])) :=
    fun y => inv_elim k _ (by simp) pre _ _ hokpre (inv_id k y)
  have hwl : ∀ y : Fin k → Bool, (wiresFrom pre (List.ofFn y)).length = k + pre.length := by
    intro y; rw [length_wiresFrom]; simp
  have hfull : ∀ y : Fin k → Bool, wiresFrom (pre ++ g :: post) (List.ofFn y)
      = wiresFrom post (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)]) := by
    intro y; rw [wiresFrom_append]; rfl
  have hgv : ∀ y : Fin k → Bool, vl (pre ++ g :: post) y (k + pre.length)
      = g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false) := by
    intro y
    show (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD (k + pre.length) false = _
    rw [hfull, getD_wiresFrom _ _ _ (by simp [hwl y]), getD_snoc_len _ _ _ _ (hwl y)]
  have inv2 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)])
      ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2) := by
    intro y
    obtain ⟨hl, hi⟩ := inv1 y
    refine ⟨by simp [hl], ?_⟩
    intro a
    show statValid (k + (elim k pre (idStats k, [])).2.length) (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Sum.inl false)) ∧
      statVal (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y)) (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Sum.inl false)) = _
    by_cases hal : a = (elim k pre (idStats k, [])).1.length
    · rw [hal, getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨(hS y).1, by rw [(hS y).2, hgv]⟩
    · rw [getD_snoc_ne _ _ _ _ hal, getD_snoc_ne _ _ _ _ (by omega)]
      exact hi a
  have inv3 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom (pre ++ g :: post) (List.ofFn y))
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)) := by
    intro y
    rw [hfull]
    exact inv_elim k _ (by simp) post _ _ hokpost (inv2 y)
  have hc1 : CleanL k (elim k pre (idStats k, [])).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) pre _ _ hokpre (inv_id k _)
      (by intro p g' hp; simp at hp)
  have hc3 : CleanL k
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) post _ _ hokpost (inv2 _) hc1
  have hlen : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).2.length + 1 ≤ (pre ++ g :: post).length := by
    have h1 : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).2.length
        ≤ (elim k pre (idStats k, [])).2.length + post.length := elim_len k post _
    have h2 : (elim k pre (idStats k, [])).2.length ≤ 0 + pre.length :=
      elim_len k pre (idStats k, [])
    simp only [List.length_append, List.length_cons]
    omega
  have hval : ∀ y : Fin k → Bool,
      statVal (wiresFrom (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)).2 (List.ofFn y)) ((elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)).1.getD o (Sum.inl false))
      = vl (pre ++ g :: post) y o := fun y => ((inv3 y).2 o).2
  cases hst : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).1.getD o (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | inr j =>
    refine ⟨_, j, hc3, hlen, ?_⟩
    intro y
    have h := hval y
    rw [hst] at h
    exact h

theorem drop_alias (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p j : ℕ) (hp : p < gs.length)
    (hj : j < k + p) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = vl gs y j)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  apply drop_core k pre g post hcl o ((elim k pre (idStats k, [])).1.getD j (Sum.inl false))
    ?_ hnc
  intro y
  have hokpre : ∀ g' ∈ pre, Ok g' :=
    fun g' h => (clean_nok _ _ hcl g' (List.mem_append_left _ h)).1
  have inv1 := inv_elim k (List.ofFn y) (by simp) pre _ _ hokpre (inv_id k y)
  refine ⟨(inv1.2 j).1, ?_⟩
  rw [(inv1.2 j).2, heq y]
  show (wiresFrom pre (List.ofFn y)).getD j false
    = (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD j false
  rw [wiresFrom_append, getD_wiresFrom (g :: post) (wiresFrom pre (List.ofFn y)) j
    (by rw [length_wiresFrom]; simp; omega)]

theorem drop_const (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (c : Bool)
    (hp : p < gs.length) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = c)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  exact drop_core k pre g post hcl o (Sum.inl c) (fun y => ⟨trivial, (heq y).symm⟩) hnc

abbrev ins {n : ℕ} (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) : Fin (n + 1) → Bool :=
  Fin.insertNth i b y

def passG (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) : List Gate :=
  (elim n gs (statAt n i b, [])).2

def IsC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Prop :=
  ∃ c, stF n gs i b a = Sum.inl c

theorem inv_stF (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (y : Fin n → Bool) :
    Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (ins i b y))) (elim n gs (statAt n i b, [])) :=
  inv_elim n _ (by simp) gs _ _ (fun g hg => (clean_nok _ gs hcl g hg).1) (inv_at n i b y)

theorem st_val_const (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (j : ℕ) (c : Bool) (h : stF n gs i b j = Sum.inl c) (y : Fin n → Bool) :
    vl gs (ins i b y) j = c := by
  have h1 := ((inv_stF n gs hcl i b y).2 j).2
  rw [show (elim n gs (statAt n i b, [])).1.getD j (Sum.inl false) = Sum.inl c from h] at h1
  exact h1.symm

theorem st_val_wire (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (j q : ℕ) (h : stF n gs i b j = Sum.inr q) (y : Fin n → Bool) :
    vl gs (ins i b y) j = vl (passG n gs i b) y q := by
  have h1 := ((inv_stF n gs hcl i b y).2 j).2
  rw [show (elim n gs (statAt n i b, [])).1.getD j (Sum.inl false) = Sum.inr q from h] at h1
  exact h1.symm

theorem st_gate (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g) :
    ∃ t, stF n gs i b (n + 1 + p)
      = (simplify g.op (n + t) (g.inputs.map (stF n gs i b))).2 := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  refine ⟨(elim n pre (statAt n i b, [])).2.length, ?_⟩
  have e1 : stF n (pre ++ g :: post) i b (n + 1 + pre.length)
      = (elimStep n (elim n pre (statAt n i b, [])) g).1.getD (n + 1 + pre.length)
        (Sum.inl false) :=
    elim_split_getD n pre g post _ _ _ (by rw [hL])
  have e2 : (elimStep n (elim n pre (statAt n i b, [])) g).1.getD (n + 1 + pre.length)
        (Sum.inl false)
      = (simplify g.op (n + (elim n pre (statAt n i b, [])).2.length)
          (g.inputs.map fun a => (elim n pre (statAt n i b, [])).1.getD a (Sum.inl false))).2 :=
    getD_snoc_len _ _ _ _ (by rw [elim_fst_len, hL])
  have e3 : (g.inputs.map fun a => (elim n pre (statAt n i b, [])).1.getD a (Sum.inl false))
      = g.inputs.map (stF n (pre ++ g :: post) i b) :=
    List.map_congr_left (fun a ha =>
      (elim_split_getD_lt n pre g post _ a _ (by rw [hL]; exact hlt a ha)).symm)
  rw [e1, e2, e3]

theorem simp_allconst (op : GateOp) (t : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (h : ∀ s ∈ ins, ∃ c, s = Sum.inl c) : ∃ c, (simplify op t ins).2 = Sum.inl c := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      obtain ⟨c', rfl⟩ := h d (by simp)
      exact ⟨_, rfl⟩
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      obtain ⟨c', rfl⟩ := h d (by simp)
      exact ⟨_, rfl⟩
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩

theorem simp_fresh (g : Gate) (m : ℕ) (hg : CleanGate m g) (t : ℕ) (F : ℕ → Stat)
    (h : ∀ a ∈ g.inputs, ∀ c, F a ≠ Sum.inl c) :
    (simplify g.op t (g.inputs.map F)).2 = Sum.inr t := by
  rcases hg with ⟨hop, j, _, hin⟩ | ⟨hop | hop, j, k, _, _, hin⟩
  · have h1 := h j (by rw [hin]; simp)
    rw [hop, hin]
    cases hF : F j with
    | inl c => exact absurd hF (h1 c)
    | inr q => simp [simplify, simpNot, hF]
  · have h1 := h j (by rw [hin]; simp)
    have h2 := h k (by rw [hin]; simp)
    rw [hop, hin]
    cases hF : F j with
    | inl c => exact absurd hF (h1 c)
    | inr q =>
      cases hF' : F k with
      | inl c => exact absurd hF' (h2 c)
      | inr q' => simp [simplify, simpAnd, hF, hF']
  · have h1 := h j (by rw [hin]; simp)
    have h2 := h k (by rw [hin]; simp)
    rw [hop, hin]
    cases hF : F j with
    | inl c => exact absurd hF (h1 c)
    | inr q =>
      cases hF' : F k with
      | inl c => exact absurd hF' (h2 c)
      | inr q' => simp [simplify, simpOr, hF, hF']

theorem st_allconst (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (h : ∀ a ∈ g.inputs, IsC n gs i b a) : IsC n gs i b (n + 1 + p) := by
  obtain ⟨t, ht⟩ := st_gate n gs hcl i b p g hp
  have hn := (hcl p g hp).nok
  obtain ⟨c, hc⟩ := simp_allconst g.op (n + t) (g.inputs.map (stF n gs i b)) hn.1.1
    (by simpa using hn.1.2) (by
      intro s hs
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hs
      exact h a ha)
  exact ⟨c, by rw [ht]; exact hc⟩

theorem st_fresh (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (h : ∀ a ∈ g.inputs, ∀ c, stF n gs i b a ≠ Sum.inl c) :
    ∃ q, n ≤ q ∧ stF n gs i b (n + 1 + p) = Sum.inr q := by
  obtain ⟨t, ht⟩ := st_gate n gs hcl i b p g hp
  exact ⟨n + t, by omega, by rw [ht]; exact simp_fresh g _ (hcl p g hp) _ _ h⟩

theorem rc_of_const (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (hc : IsC n gs i b (n + 1 + p)) :
    RC n gs i b p := by
  by_contra hno
  obtain ⟨q, _, hq⟩ := st_fresh n gs hcl i b p g hp
    (fun a ha c' hc' => hno ⟨g, hp, a, ha, c', hc'⟩)
  obtain ⟨c, hc⟩ := hc
  rw [hq] at hc
  cases hc

theorem const_read (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (a : ℕ) (ha : a ∈ g.inputs)
    (hc : stF n gs i b a = Sum.inl (fixBit g)) : IsC n gs i b (n + 1 + p) := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have h := const_of_read n gs (statAt n i b, []) p g hp ((hcl p g hp).nok) a ha
    (by rw [hL]; exact (hcl p g hp).lt a ha) hc
  rw [hL] at h
  exact h

def Dep {m : ℕ} (f : (Fin m → Bool) → Bool) (p : Fin m) : Prop :=
  ∃ x : Fin m → Bool, f (Function.update x p (!x p)) ≠ f x

abbrev set2 {m : ℕ} (x : Fin m → Bool) (p : Fin m) (a : Bool) (q : Fin m) (b : Bool) :
    Fin m → Bool :=
  Function.update (Function.update x p a) q b

def PairFunnel {m : ℕ} (f : (Fin m → Bool) → Bool) (p q : Fin m) : Prop :=
  ∃ a b : Bool, ∀ x : Fin m → Bool,
    f (set2 x p (!a) q b) = f (set2 x p a q (!b)) ∧
    f (set2 x p a q (!b)) = f (set2 x p (!a) q (!b))

def Drop {m : ℕ} (f : (Fin m → Bool) → Bool) (y : Fin m) (b : Bool) (k s : ℕ) : Prop :=
  ∃ s' : ℕ, s' + k ≤ s ∧ HasCircuitSize m (fun x => f (Function.update x y b)) s'

def Pays {m : ℕ} (f : (Fin m → Bool) → Bool) (y : Fin m) (s : ℕ) : Prop :=
  (Drop f y false 3 s ∧ Drop f y true 3 s) ∨ (Drop f y false 4 s ∧ Drop f y true 2 s) ∨
    (Drop f y false 2 s ∧ Drop f y true 4 s)

def RestrNC {m : ℕ} (f : (Fin m → Bool) → Bool) : Prop :=
  ∀ p : Fin m, Dep f p → ∀ b : Bool, ∃ x y : Fin m → Bool,
    f (Function.update x p b) ≠ f (Function.update y p b)

def NoFunnel {m : ℕ} (f : (Fin m → Bool) → Bool) : Prop :=
  ∀ p q : Fin m, p ≠ q → Dep f p → Dep f q → ¬ PairFunnel f p q

def Least (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate) (o : ℕ) : Prop :=
  CleanL m gs ∧ (∀ x : Fin m → Bool, vl gs x o = f x) ∧
    ∀ (gs' : List Gate) (o' : ℕ), CleanL m gs' → (∀ x : Fin m → Bool, vl gs' x o' = f x) →
      gs.length ≤ gs'.length

theorem Least.hcl {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least m f gs o) : CleanL m gs := L.1

theorem Least.hev {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least m f gs o) : ∀ x : Fin m → Bool, vl gs x o = f x := L.2.1

theorem Least.hmin {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least m f gs o) :
    ∀ (gs' : List Gate) (o' : ℕ), CleanL m gs' → (∀ x : Fin m → Bool, vl gs' x o' = f x) →
      gs.length ≤ gs'.length := L.2.2

def Reads (gs : List Gate) (p w : ℕ) : Prop := ∃ g, gs[p]? = some g ∧ w ∈ g.inputs

theorem dep_nc {m : ℕ} {f : (Fin m → Bool) → Bool} {p : Fin m} (h : Dep f p) :
    ∃ x y : Fin m → Bool, f x ≠ f y := by
  obtain ⟨x, hx⟩ := h
  exact ⟨_, _, hx⟩

theorem Drop.mono {m : ℕ} {f : (Fin m → Bool) → Bool} {y : Fin m} {b : Bool} {k s k' s' : ℕ}
    (h : Drop f y b k s) (hk : k' ≤ k) (hs : s ≤ s') : Drop f y b k' s' := by
  obtain ⟨t, ht, hc⟩ := h
  exact ⟨t, by omega, hc⟩

theorem has_of_clean (k : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL k gs) :
    HasCircuitSize k (fun y => vl gs y o) gs.length := by
  refine ⟨⟨gs, o⟩, ?_, le_refl _, fun y => rfl⟩
  intro g hg
  exact (clean_nok k gs hcl g hg).1

theorem reads_lt {k : ℕ} {gs : List Gate} (hcl : CleanL k gs) {q w : ℕ} (h : Reads gs q w) :
    w < k + q := by
  obtain ⟨g, hg, hw⟩ := h
  exact (hcl q g hg).lt w hw

theorem reads_len {gs : List Gate} {q w : ℕ} (h : Reads gs q w) : q < gs.length := by
  obtain ⟨g, hg, _⟩ := h
  exact (List.getElem?_eq_some_iff.1 hg).1

theorem vl_beyond {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (w : ℕ) (h : k + gs.length ≤ w) :
    vl gs u w = false := by
  unfold vl
  exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)

theorem vl_not {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (q : ℕ) (g : Gate)
    (hq : gs[q]? = some g) (j : ℕ) (hop : g.op = GateOp.not) (hin : g.inputs = [j]) :
    vl gs u (k + q) = !vl gs u j := by
  rw [vl_gate gs hcl u q g hq, hop, hin]
  rfl

theorem exists_least (m : ℕ) (f : (Fin m → Bool) → Bool) (s : ℕ)
    (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (h : HasCircuitSize m f s) :
    ∃ (gs : List Gate) (o : ℕ), Least m f gs o ∧ gs.length ≤ s := by
  classical
  have hc := clean_of m f s hnc h
  have hex : ∃ t, HasClean m f t := ⟨s, hc⟩
  obtain ⟨gs, o, hcl, hsz, hev⟩ := Nat.find_spec hex
  have hfs : Nat.find hex ≤ s := Nat.find_min' hex hc
  refine ⟨gs, o, ⟨hcl, hev, ?_⟩, by omega⟩
  intro gs' o' hc' he'
  have := Nat.find_min' hex ⟨gs', o', hc', le_refl _, he'⟩
  omega

theorem drop_dead (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (hp : p < gs.length)
    (ho : o ≠ k + p) (hno : ∀ q, ¬ Reads gs q (k + p))
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  have hpos : 0 < k + p := by
    rcases hcl p g hg with ⟨_, j, hj, _⟩ | ⟨_, j, _, hj, _, _⟩ <;> omega
  let g0 : Gate := ⟨GateOp.and, [0, 0]⟩
  let gs' := gs.set p g0
  have hlen : gs'.length = gs.length := by simp [gs']
  have hget_p : gs'[p]? = some g0 := by simp [gs', hp]
  have hget_ne : ∀ r, r ≠ p → gs'[r]? = gs[r]? := by
    intro r hr
    simp [gs', Ne.symm hr]
  have hcl' : CleanL k gs' := by
    intro r g' hr'
    by_cases hrp : r = p
    · subst hrp
      rw [hget_p] at hr'
      cases hr'
      exact Or.inr ⟨Or.inl rfl, 0, 0, hpos, hpos, rfl⟩
    · rw [hget_ne r hrp] at hr'
      exact hcl r g' hr'
  have hagree : ∀ y : Fin k → Bool, ∀ w, w ≠ k + p → vl gs' y w = vl gs y w := by
    intro y w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases hwk : w < k
      · rw [vl_input gs' y w hwk, vl_input gs y w hwk]
      · obtain ⟨r, rfl⟩ : ∃ r, w = k + r := ⟨w - k, by omega⟩
        have hrp : r ≠ p := fun e => hw (by rw [e])
        cases hr : gs[r]? with
        | none =>
          have hl : gs.length ≤ r := List.getElem?_eq_none_iff.1 hr
          rw [vl_beyond gs' y _ (by omega), vl_beyond gs y _ (by omega)]
        | some g' =>
          have hr' : gs'[r]? = some g' := by rw [hget_ne r hrp]; exact hr
          rw [vl_gate gs' hcl' y r g' hr', vl_gate gs hcl y r g' hr]
          congr 1
          apply List.map_congr_left
          intro a ha
          have hlt := (hcl r g' hr).lt a ha
          exact ih a hlt (fun e => hno r ⟨g', hr, e ▸ ha⟩)
  have halias : ∀ y : Fin k → Bool, vl gs' y (k + p) = vl gs' y 0 := by
    intro y
    rw [vl_gate gs' hcl' y p g0 hget_p]
    simp [g0, GateOp.eval]
  have hnc' : ∃ y y' : Fin k → Bool, vl gs' y o ≠ vl gs' y' o := by
    obtain ⟨y, y', h⟩ := hnc
    exact ⟨y, y', by rw [hagree y o ho, hagree y' o ho]; exact h⟩
  obtain ⟨gs'', o'', hc'', hl'', he''⟩ :=
    drop_alias k gs' hcl' o p 0 (by omega) hpos halias hnc'
  exact ⟨gs'', o'', hc'', by omega, fun y => by rw [he'' y, hagree y o ho]⟩

section

variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}

theorem Least.ncv (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) :
    ∃ y y' : Fin m → Bool, vl gs y o ≠ vl gs y' o := by
  obtain ⟨x, y, h⟩ := hnc
  exact ⟨x, y, by rw [L.hev, L.hev]; exact h⟩

theorem Least.lower (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (s : ℕ)
    (h : HasCircuitSize m f s) : gs.length ≤ s := by
  obtain ⟨gs', o', hc', hl', he'⟩ := clean_of m f s hnc h
  have := L.hmin gs' o' hc' he'
  omega

theorem Least.no_const (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (c : Bool) : ¬ ∀ u : Fin m → Bool, vl gs u (m + p) = c := by
  intro hall
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_const m gs L.hcl o p c hp hall (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega

theorem Least.no_alias (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (j : ℕ) (hj : j < m + p) :
    ¬ ∀ u : Fin m → Bool, vl gs u (m + p) = vl gs u j := by
  intro hall
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_alias m gs L.hcl o p j hp hj hall (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega

theorem Least.live (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (ho : o ≠ m + p) : ∃ q, p < q ∧ Reads gs q (m + p) := by
  by_contra hno
  have hno' : ∀ q, ¬ Reads gs q (m + p) := by
    intro q hq
    by_cases hpq : p < q
    · exact hno ⟨q, hpq, hq⟩
    · have := reads_lt L.hcl hq
      omega
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_dead m gs L.hcl o p hp ho hno' (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega

theorem Least.dep_read (L : Least m f gs o) (i : Fin m) (hd : Dep f i)
    (hnc : ∀ b : Bool, ∃ x y : Fin m → Bool,
      f (Function.update x i b) ≠ f (Function.update y i b)) : ∃ q, Reads gs q i := by
  by_contra hno
  have hno' : ∀ g ∈ gs, (i : ℕ) ∉ g.inputs := by
    intro g hg hi
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg
    exact hno ⟨q, g, hq, hi⟩
  have hoi : o ≠ i := by
    intro e
    obtain ⟨x, y, hxy⟩ := hnc false
    apply hxy
    rw [← L.hev, ← L.hev, e, vl_input gs _ i i.isLt, vl_input gs _ i i.isLt]
    simp
  obtain ⟨x, hx⟩ := hd
  apply hx
  rw [← L.hev, ← L.hev]
  refine agree_except i gs _ _ hno' (by simp) ?_ o hoi
  intro j hj
  by_cases hjm : j < m
  · rw [show (List.ofFn (Function.update x i (!x i))).getD j false
        = Function.update x i (!x i) ⟨j, hjm⟩ from getD_ofFn m _ false ⟨j, hjm⟩,
      show (List.ofFn x).getD j false = x ⟨j, hjm⟩ from getD_ofFn m x false ⟨j, hjm⟩]
    exact Function.update_of_ne (fun e => hj (congrArg Fin.val e)) _ _
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

end

theorem upd_ins {n : ℕ} (i : Fin (n + 1)) (b : Bool) (x : Fin (n + 1) → Bool) :
    Function.update x i b = ins i b (Fin.removeNth i x) :=
  (Fin.insertNth_removeNth i b x).symm

theorem restr_const {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (hcl : CleanL (n + 1) gs) (hev : ∀ x : Fin (n + 1) → Bool, vl gs x o = f x)
    (i : Fin (n + 1)) (b c : Bool) (h : stF n gs i b o = Sum.inl c) (x : Fin (n + 1) → Bool) :
    f (Function.update x i b) = c := by
  rw [upd_ins, ← hev]
  exact st_val_const n gs hcl i b o c h _

theorem save (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (gs : List Gate) (o : ℕ)
    (hcl : CleanL (n + 1) gs) (hev : ∀ x : Fin (n + 1) → Bool, vl gs x o = f x)
    (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (S : Finset ℕ) (hS : ∀ p ∈ S, RC n gs i b p) : Drop f i b S.card gs.length := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have hcount := elim_count n (statAt n i b, []) gs (clean_nok _ gs hcl) S (by
    intro p hp
    obtain ⟨g, hg, a, ha, c, hc⟩ := hS p hp
    refine ⟨g, hg, a, ha, ?_, c, hc⟩
    rw [hL]
    exact (hcl p g hg).lt a ha)
  simp only [List.length_nil, zero_add] at hcount
  cases hst : stF n gs i b o with
  | inl c =>
    exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    exact hxy ((restr_const hcl hev i b c hst x).trans (restr_const hcl hev i b c hst y).symm)
  | inr j =>
    have hc : CleanL n (passG n gs i b) :=
      clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) gs _ _
        (fun g hg => (clean_nok _ gs hcl g hg).1) (inv_at n i b _) (by intro p g hp; simp at hp)
    have h2 := renum_size (Fin.succAbove i) _ _ (has_of_clean n (passG n gs i b) j hc)
    have e : (fun x : Fin (n + 1) → Bool => f (Function.update x i b))
        = fun x => vl (passG n gs i b) (x ∘ Fin.succAbove i) j := by
      funext x
      rw [upd_ins, ← hev, st_val_wire n gs hcl i b o j hst]
      rfl
    refine ⟨(passG n gs i b).length, hcount, ?_⟩
    rw [e]
    exact h2

section

variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}

theorem Least.save (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (S : Finset ℕ) (hS : ∀ p ∈ S, RC n gs i b p) : Drop f i b S.card gs.length :=
  L573.save n f gs o L.hcl L.hev i b hnc S hS

theorem Least.save2 (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p1 p2 : ℕ) (h12 : p1 ≠ p2) (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) :
    Drop f i b 2 gs.length := by
  have := L.save i b hnc {p1, p2} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> assumption)
  rwa [Finset.card_pair h12] at this

theorem Least.save3 (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p1 p2 p3 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) :
    Drop f i b 3 gs.length := by
  have := L.save i b hnc {p1, p2, p3} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> assumption)
  rwa [Finset.card_eq_three.2 ⟨p1, p2, p3, h12, h13, h23, rfl⟩] at this

theorem Least.save4 (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p1 p2 p3 p4 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) (h4 : RC n gs i b p4) :
    Drop f i b 4 gs.length := by
  have := L.save i b hnc {p1, p2, p3, p4} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> assumption)
  have hcard : ({p1, p2, p3, p4} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13, h14]),
      Finset.card_eq_three.2 ⟨p2, p3, p4, h23, h24, h34, rfl⟩]
  rwa [hcard] at this

theorem rc_input {gs : List Gate} {q : ℕ} {i : Fin (n + 1)} (b : Bool) (h : Reads gs q i) :
    RC n gs i b q := by
  obtain ⟨g, hg, hin⟩ := h
  exact ⟨g, hg, i, hin, b, stF_self n gs i b⟩

theorem rc_of_reads {gs : List Gate} {q w : ℕ} {i : Fin (n + 1)} {b : Bool} (h : Reads gs q w)
    (hc : IsC n gs i b w) : RC n gs i b q := by
  obtain ⟨g, hg, hin⟩ := h
  obtain ⟨c, hc⟩ := hc
  exact ⟨g, hg, w, hin, c, hc⟩

theorem Least.read_dep (L : Least (n + 1) f gs o) (hnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y)
    (i : Fin (n + 1)) (q : ℕ) (hq : Reads gs q i) : Dep f i := by
  by_contra hnd
  have hnd' : ∀ x : Fin (n + 1) → Bool, f (Function.update x i (!x i)) = f x := by
    intro x
    by_contra h
    exact hnd ⟨x, h⟩
  have hfix : ∀ x : Fin (n + 1) → Bool, f (Function.update x i false) = f x := by
    intro x
    by_cases hx : x i = false
    · have e : Function.update x i false = x := by
        rw [← hx]
        exact Function.update_eq_self i x
      rw [e]
    · have e : (!x i) = false := by simpa using hx
      have := hnd' x
      rwa [e] at this
  have hnc' : ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x i false) ≠ f (Function.update y i false) := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨x, y, by rw [hfix, hfix]; exact h⟩
  obtain ⟨s', hs', hc⟩ := L.save i false hnc' {q} (by
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    exact rc_input false hq)
  rw [Finset.card_singleton] at hs'
  have e : (fun x : Fin (n + 1) → Bool => f (Function.update x i false)) = f := funext hfix
  rw [e] at hc
  have := L.lower hnc s' hc
  omega

theorem Least.next (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p : ℕ) (hp : p < gs.length) (hc : IsC n gs i b (n + 1 + p)) :
    ∃ q, p < q ∧ Reads gs q (n + 1 + p) ∧ RC n gs i b q := by
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨_, _, h⟩
  have ho : o ≠ n + 1 + p := by
    intro e
    obtain ⟨c, hc'⟩ := hc
    obtain ⟨x, y, hxy⟩ := hnc
    rw [← e] at hc'
    exact hxy ((restr_const L.hcl L.hev i b c hc' x).trans (restr_const L.hcl L.hev i b c hc' y).symm)
  obtain ⟨q, hpq, hr⟩ := L.live hfnc p hp ho
  exact ⟨q, hpq, hr, rc_of_reads hr hc⟩

end

theorem gate_cases {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (q : ℕ) (g : Gate)
    (hq : gs[q]? = some g) (a : ℕ) (ha : a ∈ g.inputs) :
    (g.op = GateOp.not ∧ g.inputs = [a] ∧ ∀ u : Fin k → Bool, vl gs u (k + q) = !vl gs u a) ∨
    ∃ w, (g.inputs = [a, w] ∨ g.inputs = [w, a]) ∧
      ((g.op = GateOp.and ∧ ∀ u : Fin k → Bool, vl gs u (k + q) = (vl gs u a && vl gs u w)) ∨
       (g.op = GateOp.or ∧ ∀ u : Fin k → Bool, vl gs u (k + q) = (vl gs u a || vl gs u w))) := by
  rcases hcl q g hq with ⟨hop, j, _, hin⟩ | ⟨hop, j, j', _, _, hin⟩
  · left
    have e : a = j := by rw [hin] at ha; simpa using ha
    subst e
    exact ⟨hop, hin, fun u => vl_not gs hcl u q g hq a hop hin⟩
  · right
    have e : a = j ∨ a = j' := by rw [hin] at ha; simpa using ha
    rcases e with e | e
    · subst e
      refine ⟨j', Or.inl hin, ?_⟩
      rcases hop with hop | hop
      · exact Or.inl ⟨hop, fun u => by rw [vl_gate gs hcl u q g hq, hop, hin]; simp [GateOp.eval]⟩
      · exact Or.inr ⟨hop, fun u => by rw [vl_gate gs hcl u q g hq, hop, hin]; simp [GateOp.eval]⟩
    · subst e
      refine ⟨j, Or.inr hin, ?_⟩
      rcases hop with hop | hop
      · refine Or.inl ⟨hop, fun u => ?_⟩
        rw [vl_gate gs hcl u q g hq, hop, hin]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
          Bool.and_true]
        exact Bool.and_comm _ _
      · refine Or.inr ⟨hop, fun u => ?_⟩
        rw [vl_gate gs hcl u q g hq, hop, hin]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
          Bool.or_false]
        exact Bool.or_comm _ _

section

variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}

theorem Least.no_tri (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p q a : ℕ)
    (hpa : Reads gs p a) (hqa : Reads gs q a) (hqp : Reads gs q (m + p)) : False := by
  obtain ⟨gp, hgp, hap⟩ := hpa
  obtain ⟨gq, hgq, haq⟩ := hqa
  obtain ⟨gq', hgq', hpq⟩ := hqp
  have e : gq' = gq := by rw [hgq] at hgq'; exact (Option.some.inj hgq').symm
  subst e
  have hlt_a : a < m + p := (L.hcl p gp hgp).lt a hap
  have hlt_p : m + p < m + q := (L.hcl q gq' hgq).lt _ hpq
  have hqlen : q < gs.length := (List.getElem?_eq_some_iff.1 hgq).1
  rcases gate_cases gs L.hcl q gq' hgq a haq with ⟨_, hin, _⟩ | ⟨w, hin, hq⟩
  · rw [hin] at hpq
    simp at hpq
    omega
  · have hw : w = m + p := by
      rcases hin with hin | hin <;> rw [hin] at hpq <;> simp at hpq <;> omega
    subst hw
    rcases gate_cases gs L.hcl p gp hgp a hap with ⟨_, _, hp⟩ | ⟨w', _, hp⟩
    · rcases hq with ⟨_, hq⟩ | ⟨_, hq⟩
      · exact L.no_const hnc q hqlen false (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> rfl)
      · exact L.no_const hnc q hqlen true (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> rfl)
    · rcases hq with ⟨_, hq⟩ | ⟨_, hq⟩ <;> rcases hp with ⟨_, hp⟩ | ⟨_, hp⟩
      · exact L.no_alias hnc q hqlen (m + p) hlt_p (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)
      · exact L.no_alias hnc q hqlen a (by omega) (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)
      · exact L.no_alias hnc q hqlen a (by omega) (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)
      · exact L.no_alias hnc q hqlen (m + p) hlt_p (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)

end

section

variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}

theorem isC_reader (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (p : ℕ) (gp : Gate)
    (hgp : gs[p]? = some gp) (hip : (i : ℕ) ∈ gp.inputs) (b : Bool)
    (h : gp.op = GateOp.not ∨ b = fixBit gp) : IsC n gs i b (n + 1 + p) := by
  rcases h with h | rfl
  · apply st_allconst n gs hcl i b p gp hgp
    intro a ha
    rcases hcl p gp hgp with ⟨_, j, _, hin⟩ | ⟨hop, _⟩
    · rw [hin] at ha hip
      simp at ha hip
      rw [ha, ← hip]
      exact ⟨b, stF_self n gs i b⟩
    · rcases hop with hop | hop <;> rw [hop] at h <;> cases h
  · exact const_read n gs hcl i _ p gp hgp i hip (stF_self n gs i _)

theorem Least.third (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p i) (hq : Reads gs q i)
    (hc : IsC n gs i b (n + 1 + p)) : Drop f i b 3 gs.length := by
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨_, _, h⟩
  obtain ⟨J, hJp, hJr, hJrc⟩ := L.next i b hnc p (reads_len hp) hc
  have hJq : J ≠ q := by
    rintro rfl
    exact L.no_tri hfnc p J i hp hq hJr
  exact L.save3 i b hnc p q J hpq (by omega) (Ne.symm hJq) (rc_input b hp) (rc_input b hq) hJrc

theorem Least.fourth (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p i) (hq : Reads gs q i)
    (hcp : IsC n gs i b (n + 1 + p)) (hcq : IsC n gs i b (n + 1 + q)) :
    Drop f i b 4 gs.length := by
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨_, _, h⟩
  obtain ⟨J1, h1p, h1r, h1rc⟩ := L.next i b hnc p (reads_len hp) hcp
  obtain ⟨J2, h2q, h2r, h2rc⟩ := L.next i b hnc q (reads_len hq) hcq
  have h1q : J1 ≠ q := by
    rintro rfl
    exact L.no_tri hfnc p J1 i hp hq h1r
  have h2p : J2 ≠ p := by
    rintro rfl
    exact L.no_tri hfnc q J2 i hq hp h2r
  by_cases h12 : J1 = J2
  · have h2r' : Reads gs J1 (n + 1 + q) := by rw [h12]; exact h2r
    have h2q' : q < J1 := by rw [h12]; exact h2q
    obtain ⟨gJ, hgJ, hinp⟩ := h1r
    obtain ⟨gJ', hgJ', hinq⟩ := h2r'
    have e : gJ' = gJ := gate_eq hgJ' hgJ rfl
    subst e
    have hcJ : IsC n gs i b (n + 1 + J1) := st_allconst n gs L.hcl i b J1 gJ' hgJ (fun a ha => by
      rcases two_inputs (L.hcl J1 gJ' hgJ) (n + 1 + p) (n + 1 + q) a hinp hinq (by omega) ha
        with e | e
      · rw [e]; exact hcp
      · rw [e]; exact hcq)
    obtain ⟨K, hKJ, _, hKrc⟩ := L.next i b hnc J1 (List.getElem?_eq_some_iff.1 hgJ).1 hcJ
    exact L.save4 i b hnc p q J1 K hpq (by omega) (by omega) (Ne.symm h1q) (by omega) (by omega)
      (rc_input b hp) (rc_input b hq) h1rc hKrc
  · exact L.save4 i b hnc p q J1 J2 hpq (by omega) (Ne.symm h2p) (Ne.symm h1q) (by omega) h12
      (rc_input b hp) (rc_input b hq) h1rc h2rc

theorem Least.two_readers (L : Least (n + 1) f gs o) (i : Fin (n + 1))
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x i b) ≠ f (Function.update y i b))
    (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p i) (hq : Reads gs q i) : Pays f i gs.length := by
  obtain ⟨gp, hgp, hip⟩ := hp
  obtain ⟨gq, hgq, hiq⟩ := hq
  have hp : Reads gs p i := ⟨gp, hgp, hip⟩
  have hq : Reads gs q i := ⟨gq, hgq, hiq⟩
  have cp := isC_reader L.hcl i p gp hgp hip
  have cq := isC_reader L.hcl i q gq hgq hiq
  by_cases hnp : gp.op = GateOp.not
  · exact Or.inl ⟨L.third i false (hnc false) p q hpq hp hq (cp false (Or.inl hnp)),
      L.third i true (hnc true) p q hpq hp hq (cp true (Or.inl hnp))⟩
  by_cases hnq : gq.op = GateOp.not
  · exact Or.inl ⟨L.third i false (hnc false) q p (Ne.symm hpq) hq hp (cq false (Or.inl hnq)),
      L.third i true (hnc true) q p (Ne.symm hpq) hq hp (cq true (Or.inl hnq))⟩
  by_cases hfb : fixBit gp = fixBit gq
  · cases hc : fixBit gp
    · exact Or.inr (Or.inl ⟨L.fourth i false (hnc false) p q hpq hp hq
        (cp false (Or.inr hc.symm)) (cq false (Or.inr (by rw [← hfb, hc]))),
        L.save2 i true (hnc true) p q hpq (rc_input true hp) (rc_input true hq)⟩)
    · exact Or.inr (Or.inr ⟨L.save2 i false (hnc false) p q hpq (rc_input false hp)
        (rc_input false hq), L.fourth i true (hnc true) p q hpq hp hq
        (cp true (Or.inr hc.symm)) (cq true (Or.inr (by rw [← hfb, hc])))⟩)
  · have key : ∀ b, Drop f i b 3 gs.length := by
      intro b
      by_cases hb : b = fixBit gp
      · exact L.third i b (hnc b) p q hpq hp hq (cp b (Or.inr hb))
      · have hb' : b = fixBit gq := by
          revert hb hfb
          cases b <;> cases fixBit gp <;> cases fixBit gq <;> simp
        exact L.third i b (hnc b) q p (Ne.symm hpq) hq hp (cq b (Or.inr hb'))
    exact Or.inl ⟨key false, key true⟩

theorem Least.not_two_readers (L : Least (n + 1) f gs o) (i : Fin (n + 1))
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x i b) ≠ f (Function.update y i b))
    (r : ℕ) (g : Gate) (hr : gs[r]? = some g) (hop : g.op = GateOp.not)
    (hin : (i : ℕ) ∈ g.inputs) (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p (n + 1 + r))
    (hq : Reads gs q (n + 1 + r)) : Drop f i false 3 gs.length ∧ Drop f i true 3 gs.length := by
  have key : ∀ b, Drop f i b 3 gs.length := by
    intro b
    have hc := isC_reader L.hcl i r g hr hin b (Or.inl hop)
    have hpr := reads_lt L.hcl hp
    have hqr := reads_lt L.hcl hq
    exact L.save3 i b (hnc b) r p q (by omega) (by omega) hpq (rc_input b ⟨g, hr, hin⟩)
      (rc_of_reads hp hc) (rc_of_reads hq hc)
  exact ⟨key false, key true⟩

end

theorem set2_p {m : ℕ} (x : Fin m → Bool) {p q : Fin m} (h : p ≠ q) (a b : Bool) :
    set2 x p a q b p = a := by
  simp [set2, Function.update_of_ne h]

theorem set2_q {m : ℕ} (x : Fin m → Bool) (p q : Fin m) (a b : Bool) :
    set2 x p a q b q = b := by
  simp [set2]

theorem set2_o {m : ℕ} (x : Fin m → Bool) (p q : Fin m) (a b : Bool) (i : Fin m) (hp : i ≠ p)
    (hq : i ≠ q) : set2 x p a q b i = x i := by
  simp [set2, Function.update_of_ne hp, Function.update_of_ne hq]

def rd (N p a w : ℕ) : ℕ := if w < N + p then w else if w = N + p then a else w - 1

def rdel (N p a : ℕ) (gs : List Gate) : List Gate :=
  gs.take p ++ (gs.drop (p + 1)).map fun g => ⟨g.op, g.inputs.map (rd N p a)⟩

def StmtRD : Prop :=
  ∀ (N : ℕ) (gs : List Gate) (p a : ℕ), CleanL N gs → p < gs.length → a < N + p →
    CleanL N (rdel N p a gs) ∧ (rdel N p a gs).length + 1 = gs.length ∧
    (∀ (x : Fin N → Bool) (w : ℕ), w < N + p → vl (rdel N p a gs) x w = vl gs x w) ∧
    (∀ x : Fin N → Bool, vl gs x (N + p) = vl gs x a →
      ∀ w : ℕ, vl (rdel N p a gs) x (rd N p a w) = vl gs x w)

def TailOK (N : ℕ) (F : (Fin N → Bool) → Bool) (gs : List Gate) (j : ℕ) : Prop :=
  ∃ g, gs[j]? = some g ∧ (g.op = GateOp.not ∨
    (g.op = GateOp.or ∧ ∀ x : Fin N → Bool, vl gs x (N + j) = true → F x = true))

def TailGE (N : ℕ) (F : (Fin N → Bool) → Bool) (gs : List Gate) (t : ℕ) : Prop :=
  t ≤ gs.length ∧ ∀ j, gs.length ≤ j + t → j < gs.length → TailOK N F gs j

def StmtLift : Prop :=
  ∀ (N : ℕ) (F : (Fin N → Bool) → Bool) (gs : List Gate) (o p l h : ℕ) (g : Gate),
    Least N F gs o → (∃ x y : Fin N → Bool, F x ≠ F y) →
    gs[p]? = some g → g.op = GateOp.or → (g.inputs = [l, h] ∨ g.inputs = [h, l]) →
    (∀ x : Fin N → Bool, vl gs x h = true → F x = true) →
    Least N F (rdel N p l gs ++ [⟨GateOp.or, [rd N p l o, h]⟩]) (N + (gs.length - 1)) ∧
    (¬ TailOK N F gs p → ∀ t, TailGE N F gs t →
      TailGE N F (rdel N p l gs ++ [⟨GateOp.or, [rd N p l o, h]⟩]) (t + 1))

def StmtXMove : Prop :=
  ∀ (N : ℕ) (F : (Fin N → Bool) → Bool) (gs : List Gate) (o p p' l q h : ℕ) (g g' : Gate),
    Least N F gs o → (∃ x y : Fin N → Bool, F x ≠ F y) → p < p' →
    gs[p]? = some g → g.op = GateOp.and → (g.inputs = [l, h] ∨ g.inputs = [h, l]) →
    gs[p']? = some g' → g'.op = GateOp.and → (g'.inputs = [q, h] ∨ g'.inputs = [h, q]) →
    (∀ x : Fin N → Bool, vl gs x h = false → F x = true) →
    ∃ (gs' : List Gate) (o' : ℕ), Least N F gs' o' ∧
      ∀ t, TailGE N F gs t → TailGE N F gs' (t + 2)

def StmtExch : Prop :=
  ∀ (N : ℕ) (F : (Fin N → Bool) → Bool) (gs : List Gate) (o h : ℕ) (T : Finset ℕ),
    CleanL N gs → (∀ x : Fin N → Bool, vl gs x o = F x) → (∃ x y : Fin N → Bool, F x ≠ F y) →
    (∀ x : Fin N → Bool, vl gs x h = false → F x = true) →
    (∀ t ∈ T, Reads gs t h ∨ ∃ (r : ℕ) (g : Gate), gs[r]? = some g ∧
      (g.op = GateOp.or ∨ g.op = GateOp.not) ∧ Reads gs r h ∧ Reads gs t (N + r)) →
    ∃ (gs' : List Gate) (o' : ℕ), CleanL N gs' ∧ (∀ x : Fin N → Bool, vl gs' x o' = F x) ∧
      gs'.length + T.card ≤ gs.length + 2

def zeroOn {N : ℕ} (D : Finset (Fin N)) (x : Fin N → Bool) : Fin N → Bool :=
  fun i => if i ∈ D then false else x i

def DeepHyp {N : ℕ} (F : (Fin N → Bool) → Bool) (D : Finset (Fin N)) : Prop :=
  (∀ y ∈ D, ∀ b : Bool, ∃ x x' : Fin N → Bool,
    F (Function.update x y b) ≠ F (Function.update x' y b)) ∧
  (∀ y ∈ D, ∀ y' ∈ D, y ≠ y' → ¬ PairFunnel F y y') ∧
  (∀ y ∈ D, ∀ x : Fin N → Bool, F (zeroOn D x) = false →
    ∃ x' : Fin N → Bool, (∀ i, i ∉ D → x' i = x i) ∧ x' y = false ∧ F x' = false ∧
      F (Function.update x' y true) = true) ∧
  (∀ x : Fin N → Bool, F (zeroOn D x) = true → F x = true) ∧
  F (fun _ => false) = false

theorem DeepHyp.nc {N : ℕ} {F : (Fin N → Bool) → Bool} {D : Finset (Fin N)}
    (H : DeepHyp F D) : ∀ y ∈ D, ∀ b : Bool, ∃ x x' : Fin N → Bool,
    F (Function.update x y b) ≠ F (Function.update x' y b) := H.1

theorem DeepHyp.nf {N : ℕ} {F : (Fin N → Bool) → Bool} {D : Finset (Fin N)}
    (H : DeepHyp F D) : ∀ y ∈ D, ∀ y' ∈ D, y ≠ y' → ¬ PairFunnel F y y' := H.2.1

theorem DeepHyp.win {N : ℕ} {F : (Fin N → Bool) → Bool} {D : Finset (Fin N)}
    (H : DeepHyp F D) : ∀ y ∈ D, ∀ x : Fin N → Bool, F (zeroOn D x) = false →
    ∃ x' : Fin N → Bool, (∀ i, i ∉ D → x' i = x i) ∧ x' y = false ∧ F x' = false ∧
      F (Function.update x' y true) = true := H.2.2.1

theorem DeepHyp.mono {N : ℕ} {F : (Fin N → Bool) → Bool} {D : Finset (Fin N)}
    (H : DeepHyp F D) : ∀ x : Fin N → Bool, F (zeroOn D x) = true → F x = true := H.2.2.2.1

theorem DeepHyp.zero {N : ℕ} {F : (Fin N → Bool) → Bool} {D : Finset (Fin N)}
    (H : DeepHyp F D) : F (fun _ => false) = false := H.2.2.2.2

def IsLit (N : ℕ) (gs : List Gate) (y : Fin N) (l : ℕ) : Prop :=
  l = (y : ℕ) ∨ ∃ pn, l = N + pn ∧ gs[pn]? = some ⟨GateOp.not, [(y : ℕ)]⟩

def DFree {N : ℕ} (D : Finset (Fin N)) (gs : List Gate) (h : ℕ) : Prop :=
  ∀ y ∈ D, y ∉ (suppsFrom gs (inputSupps N)).getD h ∅

def OneReader {N : ℕ} (D : Finset (Fin N)) (gs : List Gate) : Prop :=
  (∀ y ∈ D, ∀ p q : ℕ, Reads gs p (y : ℕ) → Reads gs q (y : ℕ) → p = q) ∧
  (∀ y ∈ D, ∀ pn : ℕ, gs[pn]? = some ⟨GateOp.not, [(y : ℕ)]⟩ →
    ∀ p q : ℕ, Reads gs p (N + pn) → Reads gs q (N + pn) → p = q)

def Front {N : ℕ} (D : Finset (Fin N)) (gs : List Gate) (p : ℕ) (g : Gate) (y : Fin N)
    (l h : ℕ) : Prop :=
  gs[p]? = some g ∧ (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
    (g.inputs = [l, h] ∨ g.inputs = [h, l]) ∧ y ∈ D ∧ IsLit N gs y l ∧ DFree D gs h

def StmtFront : Prop :=
  ∀ (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (D : Finset (Fin (n + 1))) (gs : List Gate)
    (o : ℕ), DeepHyp F D → D.Nonempty → Least (n + 1) F gs o → OneReader D gs →
    ∃ (p : ℕ) (g : Gate) (y : Fin (n + 1)) (l h : ℕ), Front D gs p g y l h ∧ o ≠ n + 1 + p

def StmtWin : Prop :=
  ∀ (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (D : Finset (Fin (n + 1))) (gs : List Gate)
    (o p : ℕ) (g : Gate) (y : Fin (n + 1)) (l h : ℕ),
    DeepHyp F D → Least (n + 1) F gs o → OneReader D gs → Front D gs p g y l h →
    (g.op = GateOp.or → ∀ x : Fin (n + 1) → Bool, vl gs x h = true → F x = true) ∧
    (g.op = GateOp.and →
      (∀ x : Fin (n + 1) → Bool, vl gs x h = false → F x = true) ∧ n + 1 ≤ h)

def StmtTwo : Prop :=
  ∀ (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (D : Finset (Fin (n + 1))) (gs : List Gate)
    (o p : ℕ) (g : Gate) (y : Fin (n + 1)) (l h : ℕ),
    DeepHyp F D → Least (n + 1) F gs o → OneReader D gs → Front D gs p g y l h →
    g.op = GateOp.and → (∃ r, r ≠ p ∧ Reads gs r h) →
    ∃ (r : ℕ) (g' : Gate) (q : ℕ), r ≠ p ∧ gs[r]? = some g' ∧ g'.op = GateOp.and ∧
      (g'.inputs = [q, h] ∨ g'.inputs = [h, q]) ∧
      ∀ t, Reads gs t h → t = p ∨ t = r

def StmtAnd : Prop :=
  ∀ (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (gs : List Gate) (o p ph l : ℕ) (g : Gate)
    (y : Fin (n + 1)),
    Least (n + 1) F gs o →
    (∀ b : Bool, ∃ x x' : Fin (n + 1) → Bool,
      F (Function.update x y b) ≠ F (Function.update x' y b)) →
    Dep F y → gs[p]? = some g → g.op = GateOp.and →
    (g.inputs = [l, n + 1 + ph] ∨ g.inputs = [n + 1 + ph, l]) → IsLit (n + 1) gs y l →
    ph < gs.length → (∀ t, Reads gs t (n + 1 + ph) → t = p) →
    o ≠ n + 1 + p → o ≠ n + 1 + ph →
    (l = (y : ℕ) → Drop F y false 3 gs.length) ∧
    (l ≠ (y : ℕ) → Drop F y true 4 gs.length)

def StmtExt : Prop :=
  ∀ (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (D : Finset (Fin (n + 1))) (s : ℕ),
    DeepHyp F D → D.Nonempty → HasCircuitSize (n + 1) F s →
    ∃ (gs : List Gate) (o : ℕ), Least (n + 1) F gs o ∧ gs.length ≤ s ∧
      (¬ OneReader D gs ∨
        ∃ (p : ℕ) (g : Gate) (y : Fin (n + 1)) (l h : ℕ), Front D gs p g y l h ∧
          g.op = GateOp.and ∧ n + 1 ≤ h ∧ o ≠ n + 1 + p ∧ ∀ t, Reads gs t h → t = p)

def StmtML : Prop :=
  ∀ (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (D : Finset (Fin (n + 1))) (s : ℕ),
    DeepHyp F D → D.Nonempty → HasCircuitSize (n + 1) F s →
    ∃ y ∈ D,
      (∃ s' : ℕ, s' + 3 ≤ s ∧
        HasCircuitSize (n + 1) (fun x => F (Function.update x y false)) s') ∨
      (∃ s' : ℕ, s' + 4 ≤ s ∧
        HasCircuitSize (n + 1) (fun x => F (Function.update x y true)) s')

theorem rdel_length (N p a : ℕ) (gs : List Gate) (hp : p < gs.length) :
    (rdel N p a gs).length + 1 = gs.length := by
  simp [rdel]; omega

theorem rdel_get_lt (N p a : ℕ) (gs : List Gate) (hp : p < gs.length) (j : ℕ) (hj : j < p) :
    (rdel N p a gs)[j]? = gs[j]? := by
  unfold rdel
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt hj]

theorem rdel_get_ge (N p a : ℕ) (gs : List Gate) (hp : p < gs.length) (j : ℕ) (hj : p ≤ j) :
    (rdel N p a gs)[j]? =
      (gs[j + 1]?).map fun g => (⟨g.op, g.inputs.map (rd N p a)⟩ : Gate) := by
  unfold rdel
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_take, List.getElem?_map, List.getElem?_drop]
  congr 2
  omega

theorem vl_append_lt {N : ℕ} (gs gs' : List Gate) (x : Fin N → Bool) (w : ℕ)
    (hw : w < N + gs.length) : vl (gs ++ gs') x w = vl gs x w := by
  unfold vl
  rw [wiresFrom_append, getD_wiresFrom _ _ w (by rw [length_wiresFrom]; simp; omega)]

theorem rd_lt (N p a w : ℕ) (hw : w < N + p) : rd N p a w = w := by
  simp [rd, hw]

theorem rd_eq (N p a : ℕ) : rd N p a (N + p) = a := by
  simp [rd]

theorem rd_gt (N p a w : ℕ) (hw : N + p < w) : rd N p a w = w - 1 := by
  unfold rd
  split_ifs <;> omega

theorem rdel_clean (N p a : ℕ) (gs : List Gate) (hcl : CleanL N gs) (hp : p < gs.length)
    (ha : a < N + p) : CleanL N (rdel N p a gs) := by
  intro j g hj
  by_cases hjp : j < p
  · rw [rdel_get_lt N p a gs hp j hjp] at hj
    exact hcl j g hj
  · rw [rdel_get_ge N p a gs hp j (by omega)] at hj
    obtain ⟨g0, hg0, rfl⟩ := Option.map_eq_some_iff.1 hj
    have hc := hcl (j + 1) g0 hg0
    have hmap : ∀ i, i < N + (j + 1) → rd N p a i < N + j := by
      intro i hi
      unfold rd
      split_ifs <;> omega
    rcases hc with ⟨h1, i, hi, h2⟩ | ⟨h1, i, k, hi, hk, h2⟩
    · exact Or.inl ⟨h1, rd N p a i, hmap i hi, by simp [h2]⟩
    · exact Or.inr ⟨h1, rd N p a i, rd N p a k, hmap i hi, hmap k hk, by simp [h2]⟩

theorem rdel_prefix (N p a : ℕ) (gs : List Gate) (hcl : CleanL N gs) (hp : p < gs.length)
    (ha : a < N + p) (x : Fin N → Bool) :
    ∀ w : ℕ, w < N + p → vl (rdel N p a gs) x w = vl gs x w := by
  have hcl' := rdel_clean N p a gs hcl hp ha
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hwN : w < N
    · rw [vl_input _ x w hwN, vl_input _ x w hwN]
    · obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
      have hj : j < p := by omega
      obtain ⟨g, hg⟩ : ∃ g, gs[j]? = some g := ⟨gs[j], List.getElem?_eq_getElem (by omega)⟩
      have hg' : (rdel N p a gs)[j]? = some g := by rw [rdel_get_lt N p a gs hp j hj, hg]
      rw [vl_gate _ hcl' x j g hg', vl_gate _ hcl x j g hg]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact ih i ((hcl j g hg).lt i hi) (by have := (hcl j g hg).lt i hi; omega)

theorem rdel_all (N p a : ℕ) (gs : List Gate) (hcl : CleanL N gs) (hp : p < gs.length)
    (ha : a < N + p) (x : Fin N → Bool) (hx : vl gs x (N + p) = vl gs x a) :
    ∀ w : ℕ, vl (rdel N p a gs) x (rd N p a w) = vl gs x w := by
  have hcl' := rdel_clean N p a gs hcl hp ha
  have hlen := rdel_length N p a gs hp
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases lt_trichotomy w (N + p) with hw | rfl | hw
    · rw [rd_lt N p a w hw]
      exact rdel_prefix N p a gs hcl hp ha x w hw
    · rw [rd_eq, hx]
      exact rdel_prefix N p a gs hcl hp ha x a ha
    · rw [rd_gt N p a w hw]
      obtain ⟨j, rfl⟩ : ∃ j, w = N + (j + 1) := ⟨w - N - 1, by omega⟩
      have e : N + (j + 1) - 1 = N + j := by omega
      rw [e]
      by_cases hjl : j + 1 < gs.length
      · obtain ⟨g, hg⟩ : ∃ g, gs[j + 1]? = some g := ⟨gs[j + 1], List.getElem?_eq_getElem hjl⟩
        have hg' : (rdel N p a gs)[j]? = some ⟨g.op, g.inputs.map (rd N p a)⟩ := by
          rw [rdel_get_ge N p a gs hp j (by omega), hg]; rfl
        rw [vl_gate _ hcl' x j _ hg', vl_gate _ hcl x (j + 1) g hg]
        simp only [List.map_map]
        congr 1
        apply List.map_congr_left
        intro i hi
        exact ih i ((hcl (j + 1) g hg).lt i hi)
      · rw [vl_beyond _ x _ (by omega), vl_beyond _ x _ (by omega)]

theorem stmtRD : StmtRD := by
  intro N gs p a hcl hp ha
  exact ⟨rdel_clean N p a gs hcl hp ha, rdel_length N p a gs hp,
    fun x w hw => rdel_prefix N p a gs hcl hp ha x w hw,
    fun x hx w => rdel_all N p a gs hcl hp ha x hx w⟩

theorem TailGE.zero (N : ℕ) (F : (Fin N → Bool) → Bool) (gs : List Gate) : TailGE N F gs 0 :=
  ⟨Nat.zero_le _, fun j h1 h2 => absurd h2 (by omega)⟩

theorem TailGE.mono {N : ℕ} {F : (Fin N → Bool) → Bool} {gs : List Gate} {t t' : ℕ}
    (h : TailGE N F gs t) (ht : t' ≤ t) : TailGE N F gs t' :=
  ⟨le_trans ht h.1, fun j h1 h2 => h.2 j (by omega) h2⟩

theorem TailGE.le {N : ℕ} {F : (Fin N → Bool) → Bool} {gs : List Gate} {t : ℕ}
    (h : TailGE N F gs t) : t ≤ gs.length := h.1

theorem TailGE.lt_of_not {N : ℕ} {F : (Fin N → Bool) → Bool} {gs : List Gate} {t p : ℕ}
    (h : TailGE N F gs t) (hp : p < gs.length) (hn : ¬ TailOK N F gs p) : p + t < gs.length := by
  by_contra hc
  exact hn (h.2 p (by omega) hp)

theorem tailGE_rdel_app (N : ℕ) (F : (Fin N → Bool) → Bool) (gs new : List Gate) (p a t : ℕ)
    (S : (Fin N → Bool) → Prop) (hcl : CleanL N gs) (hp : p < gs.length) (ha : a < N + p)
    (ht : TailGE N F gs t) (hpt : p + t < gs.length)
    (hS : ∀ x, S x → vl gs x (N + p) = vl gs x a) (hF : ∀ x, ¬ S x → F x = true)
    (hnew : ∀ i, i < new.length → TailOK N F (rdel N p a gs ++ new) (gs.length - 1 + i)) :
    TailGE N F (rdel N p a gs ++ new) (t + new.length) := by
  have hlen := rdel_length N p a gs hp
  have hl' : (rdel N p a gs ++ new).length = gs.length - 1 + new.length := by
    simp; omega
  refine ⟨by rw [hl']; omega, ?_⟩
  intro j h1 h2
  rw [hl'] at h1 h2
  by_cases hj : gs.length - 1 ≤ j
  · have := hnew (j - (gs.length - 1)) (by omega)
    rwa [show gs.length - 1 + (j - (gs.length - 1)) = j by omega] at this
  · have hok := ht.2 (j + 1) (by omega) (by omega)
    obtain ⟨g, hg, hop⟩ := hok
    have hj' : (rdel N p a gs ++ new)[j]? = some ⟨g.op, g.inputs.map (rd N p a)⟩ := by
      rw [List.getElem?_append_left (by omega), rdel_get_ge N p a gs hp j (by omega), hg]; rfl
    refine ⟨_, hj', ?_⟩
    rcases hop with hop | ⟨hop, hbel⟩
    · exact Or.inl hop
    · refine Or.inr ⟨hop, fun x hx => ?_⟩
      by_cases hSx : S x
      · apply hbel x
        rw [← rdel_all N p a gs hcl hp ha x (hS x hSx) (N + (j + 1)),
          rd_gt N p a _ (by omega), show N + (j + 1) - 1 = N + j by omega,
          ← vl_append_lt (rdel N p a gs) new x (N + j) (by omega)]
        exact hx
      · exact hF x hSx

theorem least_of {N : ℕ} {F : (Fin N → Bool) → Bool} {gs gs0 : List Gate} {o o0 : ℕ}
    (h0 : Least N F gs0 o0) (hcl : CleanL N gs) (hev : ∀ x, vl gs x o = F x)
    (hle : gs.length ≤ gs0.length) : Least N F gs o :=
  ⟨hcl, hev, fun gs' o' hc he => le_trans hle (h0.hmin gs' o' hc he)⟩

theorem out_lt_of_nc {N : ℕ} {F : (Fin N → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (hev : ∀ x, vl gs x o = F x) (hnc : ∃ x y : Fin N → Bool, F x ≠ F y) :
    o < N + gs.length := by
  by_contra hc
  obtain ⟨x, y, hxy⟩ := hnc
  apply hxy
  rw [← hev x, ← hev y, vl_beyond _ x o (by omega), vl_beyond _ y o (by omega)]

theorem stmtLift : StmtLift := by
  intro N F gs o p l h g hle hnc hg hop hin hbel
  have hcl := hle.hcl
  have hp : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  have hlen := rdel_length N p l gs hp
  have ho := out_lt_of_nc hle.hev hnc

  have hlh : l < N + p ∧ h < N + p := by
    rcases hcl p g hg with ⟨h1, _⟩ | ⟨_, j, k, hj, hk, h2⟩
    · rw [hop] at h1; cases h1
    · rcases hin with e | e <;> rw [e] at h2 <;> simp at h2 <;> omega
  obtain ⟨hl, hh⟩ := hlh

  have hS : ∀ x : Fin N → Bool, vl gs x h = false → vl gs x (N + p) = vl gs x l := by
    intro x hx
    rw [vl_gate _ hcl x p g hg, hop]
    rcases hin with e | e <;> rw [e] <;> simp [hx, GateOp.eval]
  have hro : rd N p l o < N + (gs.length - 1) := by
    unfold rd; split_ifs <;> omega
  set gs2 := rdel N p l gs ++ [⟨GateOp.or, [rd N p l o, h]⟩] with hgs2
  have hcl' := rdel_clean N p l gs hcl hp hl
  have hcl2 : CleanL N gs2 := by
    intro j g' hj
    by_cases hj' : j < (rdel N p l gs).length
    · rw [hgs2, List.getElem?_append_left hj'] at hj
      exact hcl' j g' hj
    · rw [hgs2, List.getElem?_append_right (by omega)] at hj
      obtain ⟨e1, e2⟩ := List.getElem?_eq_some_iff.1 hj
      simp at e1
      have ej : j = (rdel N p l gs).length := by omega
      subst ej
      simp at e2
      subst e2
      exact Or.inr ⟨Or.inr rfl, rd N p l o, h, by omega, by omega, rfl⟩
  have hlast : (gs2)[gs.length - 1]? = some ⟨GateOp.or, [rd N p l o, h]⟩ := by
    rw [hgs2, List.getElem?_append_right (by omega)]
    rw [show gs.length - 1 - (rdel N p l gs).length = 0 by omega]; rfl
  have hval : ∀ x : Fin N → Bool, vl gs2 x (N + (gs.length - 1)) = F x := by
    intro x
    rw [vl_gate _ hcl2 x _ _ hlast]
    have e1 : vl gs2 x (rd N p l o) = vl (rdel N p l gs) x (rd N p l o) :=
      vl_append_lt _ _ x _ (by omega)
    have e2 : vl gs2 x h = vl gs x h := by
      rw [vl_append_lt _ _ x _ (by omega), rdel_prefix N p l gs hcl hp hl x h hh]
    simp only [List.map, GateOp.eval, e1, e2]
    cases hx : vl gs x h
    · rw [rdel_all N p l gs hcl hp hl x (hS x hx) o, hle.hev x]; simp
    · rw [hbel x hx]; simp
  refine ⟨least_of hle hcl2 hval (by simp [hgs2]; omega), ?_⟩
  intro hnt t ht
  have hpt := ht.lt_of_not hp hnt
  have := tailGE_rdel_app N F gs [⟨GateOp.or, [rd N p l o, h]⟩] p l t
    (fun x : Fin N → Bool => vl gs x h = false) hcl hp hl ht hpt hS
    (fun x hx => hbel x (by simpa using hx)) ?_
  · simpa using this
  · intro i hi
    simp at hi
    subst hi
    refine ⟨_, by simpa using hlast, Or.inr ⟨rfl, fun x hx => ?_⟩⟩
    rw [← hval x]; simpa using hx

theorem not_tailOK_and {N : ℕ} {F : (Fin N → Bool) → Bool} {gs : List Gate} {j : ℕ} {g : Gate}
    (hg : gs[j]? = some g) (hop : g.op = GateOp.and) : ¬ TailOK N F gs j := by
  rintro ⟨g0, hg0, h | ⟨h, _⟩⟩ <;>
  · rw [hg] at hg0
    cases hg0
    rw [hop] at h
    cases h

theorem vl_and_true {N : ℕ} (gs : List Gate) (hcl : CleanL N gs) (x : Fin N → Bool) (p l h : ℕ)
    (g : Gate) (hg : gs[p]? = some g) (hop : g.op = GateOp.and)
    (hin : g.inputs = [l, h] ∨ g.inputs = [h, l]) (hx : vl gs x h = true) :
    vl gs x (N + p) = vl gs x l := by
  rw [vl_gate gs hcl x p g hg, hop]
  rcases hin with hi | hi <;> rw [hi] <;> simp [GateOp.eval, hx]

theorem stmtXMove : StmtXMove := by
  intro N F gs o p p' l q h g g' hL hnc hpp hg hop hin hg' hop' hin' hbel
  have hcl := hL.hcl
  have hp's : p' < gs.length := (List.getElem?_eq_some_iff.1 hg').1
  have hl : l < N + p := (hcl p g hg).lt l (by rcases hin with hi | hi <;> simp [hi])
  have hh : h < N + p := (hcl p g hg).lt h (by rcases hin with hi | hi <;> simp [hi])
  have hq : q < N + p' := (hcl p' g' hg').lt q (by rcases hin' with hi | hi <;> simp [hi])
  have ho : o < N + gs.length := by
    by_contra hc
    obtain ⟨x, y, hxy⟩ := hnc
    apply hxy
    rw [← hL.hev x, ← hL.hev y, vl_beyond _ x o (by omega), vl_beyond _ y o (by omega)]

  have hcl1 := rdel_clean N p' q gs hcl hp's hq
  have hlen1 := rdel_length N p' q gs hp's
  have hp1 : p < (rdel N p' q gs).length := by omega
  have hg1 : (rdel N p' q gs)[p]? = some g := by rw [rdel_get_lt N p' q gs hp's p hpp, hg]

  have hcl2 := rdel_clean N p l (rdel N p' q gs) hcl1 hp1 hl
  have hlen2 := rdel_length N p l (rdel N p' q gs) hp1
  have ho2 : rd N p l (rd N p' q o) < N + (rdel N p l (rdel N p' q gs)).length := by
    unfold rd
    split_ifs <;> omega
  have hh2 : h < N + (rdel N p l (rdel N p' q gs)).length := by omega

  have hgood : ∀ x : Fin N → Bool, vl gs x h = true →
      vl (rdel N p l (rdel N p' q gs)) x (rd N p l (rd N p' q o)) = F x ∧
      vl (rdel N p l (rdel N p' q gs)) x h = true := by
    intro x hx
    have hx1 := vl_and_true gs hcl x p' q h g' hg' hop' hin' hx
    have hx2 : vl (rdel N p' q gs) x (N + p) = vl (rdel N p' q gs) x l := by
      rw [rdel_prefix N p' q gs hcl hp's hq x (N + p) (by omega),
        rdel_prefix N p' q gs hcl hp's hq x l (by omega)]
      exact vl_and_true gs hcl x p l h g hg hop hin hx
    refine ⟨?_, ?_⟩
    · rw [rdel_all N p l _ hcl1 hp1 hl x hx2, rdel_all N p' q gs hcl hp's hq x hx1, hL.hev x]
    · rw [rdel_prefix N p l _ hcl1 hp1 hl x h hh,
        rdel_prefix N p' q gs hcl hp's hq x h (by omega), hx]

  set gs2 := rdel N p l (rdel N p' q gs) with hgs2
  set o2 := rd N p l (rd N p' q o) with ho2def
  set new : List Gate := [⟨GateOp.not, [h]⟩, ⟨GateOp.or, [o2, N + gs2.length]⟩] with hnew
  have hget0 : (gs2 ++ new)[gs2.length]? = some ⟨GateOp.not, [h]⟩ := by simp [hnew]
  have hget1 : (gs2 ++ new)[gs2.length + 1]? = some ⟨GateOp.or, [o2, N + gs2.length]⟩ := by
    simp [hnew]
  have hclA : CleanL N (gs2 ++ new) := by
    intro j g0 hj
    by_cases hj2 : j < gs2.length
    · rw [List.getElem?_append_left hj2] at hj
      exact hcl2 j g0 hj
    · rw [List.getElem?_append_right (by omega)] at hj
      have hjl : j - gs2.length < 2 := by
        have := (List.getElem?_eq_some_iff.1 hj).1
        simpa [hnew] using this
      rcases (by omega : j - gs2.length = 0 ∨ j - gs2.length = 1) with e | e
      · rw [e] at hj
        simp [hnew] at hj
        subst hj
        exact Or.inl ⟨rfl, h, by omega, rfl⟩
      · rw [e] at hj
        simp [hnew] at hj
        subst hj
        exact Or.inr ⟨Or.inr rfl, o2, N + gs2.length, by omega, by omega, rfl⟩
  have hvtop : ∀ x : Fin N → Bool, vl (gs2 ++ new) x (N + (gs2.length + 1)) = F x := by
    intro x
    have h0 : vl (gs2 ++ new) x (N + gs2.length) = !vl gs2 x h := by
      rw [vl_gate _ hclA x _ _ hget0]
      simp [GateOp.eval, vl_append_lt gs2 new x h hh2]
    rw [vl_gate _ hclA x _ _ hget1]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
      Bool.or_false]
    rw [h0, vl_append_lt gs2 new x o2 ho2]
    by_cases hx : vl gs x h = true
    · obtain ⟨e1, e2⟩ := hgood x hx
      rw [e1, e2]
      simp
    · have hF := hbel x (by simpa using hx)
      have e2 : vl gs2 x h = vl gs x h := by
        rw [hgs2, rdel_prefix N p l _ hcl1 hp1 hl x h hh,
          rdel_prefix N p' q gs hcl hp's hq x h (by omega)]
      rw [hF, e2]
      simp [hx]
  have hlenA : (gs2 ++ new).length = gs.length := by simp [hnew]; omega
  refine ⟨gs2 ++ new, N + (gs2.length + 1),
    least_of hL hclA hvtop (le_of_eq hlenA), ?_⟩
  intro t ht
  have hpt' : p' + t < gs.length := ht.lt_of_not hp's (not_tailOK_and hg' hop')
  have hF : ∀ x : Fin N → Bool, ¬ (vl gs x h = true) → F x = true :=
    fun x hx => hbel x (by simpa using hx)
  have ht1 : TailGE N F (rdel N p' q gs) t := by
    have := tailGE_rdel_app N F gs [] p' q t (fun x => vl gs x h = true) hcl hp's hq ht hpt'
      (fun x hx => vl_and_true gs hcl x p' q h g' hg' hop' hin' hx) hF
      (fun i hi => absurd hi (by simp))
    simpa using this
  have hS2 : ∀ x : Fin N → Bool, vl gs x h = true →
      vl (rdel N p' q gs) x (N + p) = vl (rdel N p' q gs) x l := by
    intro x hx
    rw [rdel_prefix N p' q gs hcl hp's hq x (N + p) (by omega),
      rdel_prefix N p' q gs hcl hp's hq x l (by omega)]
    exact vl_and_true gs hcl x p l h g hg hop hin hx
  have hlen2' : gs2.length = (rdel N p' q gs).length - 1 := by omega
  have := tailGE_rdel_app N F (rdel N p' q gs) new p l t (fun x => vl gs x h = true) hcl1 hp1 hl
    ht1 (by omega) hS2 hF (by
      intro i hi
      have hi2 : i < 2 := by simpa [hnew] using hi
      rw [← hlen2']
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · exact ⟨_, by simpa using hget0, Or.inl rfl⟩
      · refine ⟨_, hget1, Or.inr ⟨rfl, fun x hx => ?_⟩⟩
        rw [show N + (gs2.length + 1) = N + (gs2.length + 1) from rfl, hvtop x] at hx
        exact hx)
  simpa [hnew] using this

theorem exch_startStats_length (m h : ℕ) : (startStats m h).length = m := by
  simp [startStats]

theorem exch_clean_take (N k : ℕ) (gs : List Gate) (hcl : CleanL N gs) :
    CleanL N (gs.take k) := by
  intro p g hp
  rw [List.getElem?_take] at hp
  by_cases hpk : p < k
  · simp [hpk] at hp; exact hcl p g hp
  · simp [hpk] at hp

theorem exch_const_reader (N : ℕ) (post : List Gate) (acc : List Stat × List Gate)
    (hok : ∀ g ∈ post, NOk g) (h q : ℕ) (g : Gate) (hq : post[q]? = some g)
    (hop : g.op = GateOp.or ∨ g.op = GateOp.not) (hh : h ∈ g.inputs) (hlt : h < acc.1.length)
    (hst : acc.1.getD h (Sum.inl false) = Sum.inl true) :
    ∃ c, (elim N post acc).1.getD (acc.1.length + q) (Sum.inl false) = Sum.inl c := by
  obtain ⟨pre, post', rfl, rfl⟩ := split_at post q g hq
  rw [elim_split_getD N pre g post' acc _ _ (le_refl _)]
  have hgok : NOk g := hok g (by simp)
  have hl : (elim N pre acc).1.length = acc.1.length + pre.length := elim_fst_len N pre acc
  simp only [elimStep]
  rw [getD_snoc_len _ _ _ _ hl]
  apply simplify_const _ _ _ hgok.1.1 (by simpa using hgok.1.2)
    (fun h' => by simpa using hgok.2 h') true
  · intro h'; rcases hop with h2 | h2 <;> rw [h2] at h' <;> cases h'
  · intro _; rfl
  · refine List.mem_map.2 ⟨h, hh, ?_⟩
    rw [elim_getD N h _ pre acc hlt]; exact hst

theorem stmtExch : StmtExch := by
  intro N F gs o h T hcl hev hnc hcov hT
  have hyl : ∀ x : Fin N → Bool, (List.ofFn x).length = N := by simp

  have hnotT : ¬ ∀ x : Fin N → Bool, F x = true := by
    intro hT'
    obtain ⟨x, y, hxy⟩ := hnc
    exact hxy (by rw [hT' x, hT' y])
  have hex : ∃ x0 : Fin N → Bool, vl gs x0 h = true := by
    by_contra hne
    push Not at hne
    exact hnotT fun x => hcov x (by simpa using hne x)
  obtain ⟨x0, hx0⟩ := hex
  have hhs : h < N + gs.length := by
    by_contra hlt
    rw [vl_beyond gs x0 h (by omega)] at hx0
    cases hx0
  set k := h + 1 - N with hk
  have hks : k ≤ gs.length := by omega
  have hhk : h < N + k := by omega
  set pre := gs.take k with hpre
  set post := gs.drop k with hpost
  have hlpre : pre.length = k := by simp [hpre]; omega
  have hlpost : post.length = gs.length - k := by simp [hpost]
  have hnok : ∀ g ∈ gs, NOk g := clean_nok N gs hcl
  have hnokpost : ∀ g ∈ post, NOk g := fun g hg => hnok g (List.mem_of_mem_drop hg)
  have hclpre : CleanL N pre := exch_clean_take N k gs hcl
  have hwg : ∀ y : List Bool, wiresFrom gs y = wiresFrom post (wiresFrom pre y) := by
    intro y
    rw [← wiresFrom_append, hpre, hpost, List.take_append_drop]
  have hwh : ∀ x : Fin N → Bool, vl gs x h = (wiresFrom pre (List.ofFn x)).getD h false := by
    intro x
    show (wiresFrom gs (List.ofFn x)).getD h false = _
    rw [hwg, getD_wiresFrom _ _ _ (by rw [length_wiresFrom, hyl, hlpre]; exact hhk)]

  set acc0 : List Stat × List Gate := (startStats (N + pre.length) h, pre) with hacc0
  have hl0 : acc0.1.length = N + k := by
    rw [hacc0, exch_startStats_length, hlpre]
  set acc := elim N post acc0 with hacc
  have hinv : ∀ x : Fin N → Bool, vl gs x h = true →
      Inv N (List.ofFn x) (wiresFrom gs (List.ofFn x)) acc := by
    intro x hx
    rw [hwg, hacc]
    exact inv_elim N _ (hyl x) post _ _ (fun g hg => (hnokpost g hg).1)
      (inv_start N h pre _ (hyl x) (by rw [← hwh]; exact hx))
  obtain ⟨tl, htl⟩ := elim_prefix N post acc0
  rw [← hacc] at htl
  have hLk : acc.2.length = k + tl.length := by rw [htl]; simp [hacc0, hlpre]
  have hclacc : CleanL N acc.2 :=
    clean_elim N (List.ofFn x0) (hyl x0) post _ _ (fun g hg => (hnokpost g hg).1)
      (inv_start N h pre _ (hyl x0) (by rw [← hwh]; exact hx0)) hclpre

  have hsth0 : acc0.1.getD h (Sum.inl false) = Sum.inl true := by
    rw [hacc0, startStats_getD]; simp [hlpre, hhk]
  have hsth : acc.1.getD h (Sum.inl false) = Sum.inl true := by
    rw [hacc, elim_getD N h _ post acc0 (by omega)]; exact hsth0

  have hTk : ∀ t ∈ T, k ≤ t := by
    intro t ht
    rcases hT t ht with hr | ⟨r, g, _, _, hrh, htr⟩
    · have := reads_lt hcl hr; omega
    · have := reads_lt hcl hrh; have := reads_lt hcl htr; omega

  have hcount := elim_count N acc0 post hnokpost (T.image fun t => t - k) (by
    intro p hp
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hp
    have htk := hTk t ht
    have hpt : post[t - k]? = gs[t]? := by
      rw [hpost, List.getElem?_drop]; congr 1; omega
    rcases hT t ht with ⟨g, hg, hhg⟩ | ⟨r, g', hg', hop, hrh, ⟨g, hg, hrg⟩⟩
    · refine ⟨g, by rw [hpt]; exact hg, h, hhg, ?_, true, ?_⟩
      · have := (hcl t g hg).lt h hhg; omega
      · rw [← hacc]; exact hsth
    · refine ⟨g, by rw [hpt]; exact hg, N + r, hrg, ?_, ?_⟩
      · have := (hcl t g hg).lt _ hrg; omega
      · have hrk : k ≤ r := by have := reads_lt hcl hrh; omega
        obtain ⟨g'', hg'', hhg''⟩ := hrh
        rw [hg'] at hg''
        cases hg''
        have hpr : post[r - k]? = some g' := by
          rw [hpost, List.getElem?_drop]
          have e : k + (r - k) = r := by omega
          rw [e]; exact hg'
        obtain ⟨c, hc⟩ := exch_const_reader N post acc0 hnokpost h (r - k) g' hpr hop hhg''
          (by omega) hsth0
        refine ⟨c, ?_⟩
        have e : acc0.1.length + (r - k) = N + r := by omega
        rw [e] at hc; exact hc)
  have hcard : (T.image fun t => t - k).card = T.card := by
    apply Finset.card_image_of_injOn
    intro a ha b hb hab
    have := hTk a ha; have := hTk b hb
    simp only at hab; omega
  rw [hcard, ← hacc] at hcount
  have hsize : acc.2.length + T.card ≤ gs.length := by
    have : acc0.2.length = k := by simp [hacc0, hlpre]
    omega

  have hwhA : ∀ x : Fin N → Bool, (wiresFrom acc.2 (List.ofFn x)).getD h false = vl gs x h := by
    intro x
    rw [htl, wiresFrom_append, hwh, getD_wiresFrom _ _ _ (by
      rw [length_wiresFrom, hyl]; simp [hacc0, hlpre]; exact hhk)]
  have hval : ∀ x : Fin N → Bool, vl gs x h = true →
      statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD o (Sum.inl false)) = F x := by
    intro x hx
    rw [((hinv x hx).2 o).2, ← hev x]; rfl
  have hvalid : statValid (N + acc.2.length) (acc.1.getD o (Sum.inl false)) :=
    ((hinv x0 hx0).2 o).1
  cases hst : acc.1.getD o (Sum.inl false) with
  | inl c =>
    cases c with
    | true =>
      exfalso
      apply hnotT
      intro x
      by_cases hx : vl gs x h = true
      · rw [← hval x hx, hst]; rfl
      · exact hcov x (by simpa using hx)
    | false =>

      refine ⟨pre ++ [⟨GateOp.not, [h]⟩], N + k, ?_, ?_, ?_⟩
      · intro p g hp
        by_cases hlt : p < pre.length
        · rw [List.getElem?_append_left hlt] at hp; exact hclpre p g hp
        · rw [List.getElem?_append_right (by omega)] at hp
          have hp0 : p - pre.length = 0 := by
            by_contra hne
            simp [hne] at hp
          simp [hp0] at hp
          cases hp
          have hpl : p = k := by omega
          rw [hpl]
          exact Or.inl ⟨rfl, h, by omega, rfl⟩
      · intro x
        show (wiresFrom (pre ++ [⟨GateOp.not, [h]⟩]) (List.ofFn x)).getD (N + k) false = _
        rw [wiresFrom_append]
        have hl : (wiresFrom pre (List.ofFn x)).length = N + k := by
          rw [length_wiresFrom, hyl, hlpre]
        show ((wiresFrom pre (List.ofFn x)) ++ [GateOp.not.eval
          ([h].map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]).getD (N + k) false = _
        rw [getD_snoc_len _ _ _ _ hl]
        simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
        rw [← hwh]
        by_cases hx : vl gs x h = true
        · rw [hx, ← hval x hx, hst]; rfl
        · rw [hcov x (by simpa using hx)]; simpa using hx
      · simp only [List.length_append, List.length_cons, List.length_nil, hlpre]
        omega
  | inr j =>
    rw [hst] at hvalid
    have hj : j < N + acc.2.length := hvalid
    set L := acc.2.length with hL
    refine ⟨acc.2 ++ [⟨GateOp.not, [h]⟩, ⟨GateOp.or, [j, N + L]⟩], N + L + 1, ?_, ?_, ?_⟩
    · intro p g hp
      by_cases hlt : p < L
      · rw [List.getElem?_append_left hlt] at hp; exact hclacc p g hp
      · rw [List.getElem?_append_right (by omega)] at hp
        by_cases h0 : p - L = 0
        · rw [h0] at hp
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hp
          subst hp
          have hpl : p = L := by omega
          rw [hpl]
          exact Or.inl ⟨rfl, h, by omega, rfl⟩
        · by_cases h1 : p - L = 1
          · rw [h1] at hp
            simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
              Option.some.injEq] at hp
            subst hp
            have hpl : p = L + 1 := by omega
            rw [hpl]
            exact Or.inr ⟨Or.inr rfl, j, N + L, by omega, by omega, rfl⟩
          · obtain ⟨d, hd⟩ : ∃ d, p - L = d + 2 := ⟨p - L - 2, by omega⟩
            rw [hd] at hp
            simp at hp
    · intro x
      show (wiresFrom (acc.2 ++ [⟨GateOp.not, [h]⟩, ⟨GateOp.or, [j, N + L]⟩])
        (List.ofFn x)).getD (N + L + 1) false = _
      rw [wiresFrom_append]
      set W := wiresFrom acc.2 (List.ofFn x) with hW
      have hl : W.length = N + L := by rw [hW, length_wiresFrom, hyl]
      set W' := W ++ [GateOp.not.eval ([h].map fun i => W.getD i false)] with hW'
      have hl' : W'.length = N + L + 1 := by simp [hW', hl]
      show (W' ++ [GateOp.or.eval ([j, N + L].map fun i => W'.getD i false)]).getD
        (N + L + 1) false = _
      rw [getD_snoc_len _ _ _ _ hl']
      have e1 : W'.getD j false = W.getD j false := List.getD_append _ _ _ _ (by omega)
      have e2 : W'.getD (N + L) false = !(W.getD h false) := by
        rw [hW', getD_snoc_len _ _ _ _ hl]; simp [GateOp.eval]
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
        id, Bool.or_false, e1, e2]
      rw [hW, hwhA]
      by_cases hx : vl gs x h = true
      · rw [hx, ← hval x hx, hst]; simp [statVal]
      · have hx' : vl gs x h = false := by simpa using hx
        rw [hcov x hx', hx']; simp
    · simp only [List.length_append, List.length_cons, List.length_nil]
      omega

def andSwap (gs : List Gate) (ph : ℕ) {N : ℕ} (y : Fin N) : List Gate :=
  gs.set ph ⟨GateOp.not, [(y : ℕ)]⟩

theorem andSwap_length (gs : List Gate) (ph : ℕ) {N : ℕ} (y : Fin N) :
    (andSwap gs ph y).length = gs.length := by
  simp [andSwap]

theorem andSwap_get_ne (gs : List Gate) (ph : ℕ) {N : ℕ} (y : Fin N) (r : ℕ) (hr : r ≠ ph) :
    (andSwap gs ph y)[r]? = gs[r]? := by
  simp [andSwap, Ne.symm hr]

theorem andSwap_get_eq (gs : List Gate) (ph : ℕ) {N : ℕ} (y : Fin N) (hph : ph < gs.length) :
    (andSwap gs ph y)[ph]? = some ⟨GateOp.not, [(y : ℕ)]⟩ := by
  simp [andSwap, hph]

theorem andSwap_clean {N : ℕ} (gs : List Gate) (ph : ℕ) (y : Fin N) (hcl : CleanL N gs)
    (hph : ph < gs.length) : CleanL N (andSwap gs ph y) := by
  intro r g' hr'
  by_cases hrp : r = ph
  · subst hrp
    rw [andSwap_get_eq gs r y hph] at hr'
    cases hr'
    exact Or.inl ⟨rfl, y, by omega, rfl⟩
  · rw [andSwap_get_ne gs ph y r hrp] at hr'
    exact hcl r g' hr'

theorem andSwap_agree {N : ℕ} (gs : List Gate) (hcl : CleanL N gs) (p ph l : ℕ) (g : Gate)
    (y : Fin N) (hph : ph < gs.length) (hgp : gs[p]? = some g) (hop : g.op = GateOp.and)
    (hin : g.inputs = [l, N + ph] ∨ g.inputs = [N + ph, l]) (hlne : l ≠ N + ph)
    (hone : ∀ t, Reads gs t (N + ph) → t = p) (x : Fin N → Bool) (hlx : vl gs x l = false) :
    ∀ w, w ≠ N + ph → vl (andSwap gs ph y) x w = vl gs x w := by
  have hcl' := andSwap_clean gs ph y hcl hph
  have hlen := andSwap_length gs ph y
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hwk : w < N
    · rw [vl_input _ x w hwk, vl_input gs x w hwk]
    · obtain ⟨r, rfl⟩ : ∃ r, w = N + r := ⟨w - N, by omega⟩
      have hrp : r ≠ ph := fun e => hw (by rw [e])
      cases hr : gs[r]? with
      | none =>
        have hl : gs.length ≤ r := List.getElem?_eq_none_iff.1 hr
        rw [vl_beyond _ x _ (by omega), vl_beyond gs x _ (by omega)]
      | some g' =>
        have hr' : (andSwap gs ph y)[r]? = some g' := by
          rw [andSwap_get_ne gs ph y r hrp]; exact hr
        rw [vl_gate _ hcl' x r g' hr', vl_gate gs hcl x r g' hr]
        by_cases hrp' : r = p
        · subst hrp'
          rw [hgp] at hr
          cases hr
          have hllt : l < N + r := (hcl r g hgp).lt l (by rcases hin with h | h <;> simp [h])
          have hl' : vl (andSwap gs ph y) x l = false := by rw [ih l hllt hlne]; exact hlx
          rw [hop]
          rcases hin with h | h <;> rw [h] <;> simp [GateOp.eval, hl', hlx]
        · congr 1
          apply List.map_congr_left
          intro a ha
          have hlt := (hcl r g' hr).lt a ha
          exact ih a hlt (fun e => hrp' (hone r ⟨g', hr, e ▸ ha⟩))

theorem andUpd_self {N : ℕ} (x : Fin N → Bool) (y : Fin N) (b : Bool) :
    Function.update x y b y = b := Function.update_self y b x

theorem and_core (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (gs : List Gate) (o p ph l : ℕ)
    (g : Gate) (y : Fin (n + 1)) (L : Least (n + 1) F gs o) (b : Bool)
    (hnc : ∃ x x' : Fin (n + 1) → Bool,
      F (Function.update x y b) ≠ F (Function.update x' y b))
    (hgp : gs[p]? = some g) (hop : g.op = GateOp.and)
    (hin : g.inputs = [l, n + 1 + ph] ∨ g.inputs = [n + 1 + ph, l]) (hlne : l ≠ n + 1 + ph)
    (hph : ph < gs.length) (hone : ∀ t, Reads gs t (n + 1 + ph) → t = p)
    (ho2 : o ≠ n + 1 + ph)
    (hlx : ∀ x : Fin (n + 1) → Bool, x y = b → vl gs x l = false)
    (S : Finset ℕ) (hS : ∀ q ∈ S, RC n (andSwap gs ph y) y b q) :
    Drop F y b S.card gs.length := by
  have hcl' := andSwap_clean gs ph y L.hcl hph
  have hag : ∀ x : Fin (n + 1) → Bool,
      vl (andSwap gs ph y) (Function.update x y b) o = F (Function.update x y b) := by
    intro x
    rw [andSwap_agree gs L.hcl p ph l g y hph hgp hop hin hlne hone _
      (hlx _ (andUpd_self x y b)) o ho2, L.hev]
  have hnc' : ∃ x x' : Fin (n + 1) → Bool,
      vl (andSwap gs ph y) (Function.update x y b) o
        ≠ vl (andSwap gs ph y) (Function.update x' y b) o := by
    obtain ⟨x, x', h⟩ := hnc
    exact ⟨x, x', by rw [hag, hag]; exact h⟩
  obtain ⟨s', hs', hc⟩ := save n (fun x => vl (andSwap gs ph y) x o) (andSwap gs ph y) o hcl'
    (fun _ => rfl) y b hnc' S hS
  refine ⟨s', by rw [andSwap_length] at hs'; exact hs', ?_⟩
  have e : (fun x : Fin (n + 1) → Bool => F (Function.update x y b))
      = fun x => (fun x => vl (andSwap gs ph y) x o) (Function.update x y b) := by
    funext x
    exact (hag x).symm
  rw [e]
  exact hc

theorem stmtAnd : StmtAnd := by
  intro n F gs o p ph l g y L hnc _hdep hgp hop hin hlit hph hone ho1 ho2
  have hfnc : ∃ x x' : Fin (n + 1) → Bool, F x ≠ F x' := by
    obtain ⟨x, x', h⟩ := hnc false
    exact ⟨_, _, h⟩
  have hlmem : l ∈ g.inputs := by rcases hin with h | h <;> simp [h]
  have hhmem : n + 1 + ph ∈ g.inputs := by rcases hin with h | h <;> simp [h]
  have hp : p < gs.length := (List.getElem?_eq_some_iff.1 hgp).1
  have hphp : n + 1 + ph < n + 1 + p := (L.hcl p g hgp).lt _ hhmem
  have hllt : l < n + 1 + p := (L.hcl p g hgp).lt _ hlmem
  have hlne : l ≠ n + 1 + ph := by
    intro e
    apply L.no_alias hfnc p hp (n + 1 + ph) hphp
    intro u
    rw [vl_gate gs L.hcl u p g hgp, hop]
    rcases hin with h | h <;> rw [h, ← e] <;> simp [GateOp.eval]
  have hcl' := andSwap_clean gs ph y L.hcl hph
  have hgp' : (andSwap gs ph y)[p]? = some g := by
    rw [andSwap_get_ne gs ph y p (by omega)]; exact hgp
  obtain ⟨S, hpS, hSr⟩ := L.live hfnc p hp ho1
  have hSr' : Reads (andSwap gs ph y) S (n + 1 + p) := by
    obtain ⟨g', hg', hm⟩ := hSr
    exact ⟨g', by rw [andSwap_get_ne gs ph y S (by omega)]; exact hg', hm⟩
  have hphR : Reads (andSwap gs ph y) ph y := ⟨_, andSwap_get_eq gs ph y hph, by simp⟩
  have hpR : Reads (andSwap gs ph y) p l := ⟨g, hgp', hlmem⟩
  refine ⟨fun hly => ?_, fun hly => ?_⟩
  ·
    subst hly
    have hlx : ∀ x : Fin (n + 1) → Bool, x y = false → vl gs x y = false := by
      intro x hx
      rw [vl_input gs x y y.isLt]
      exact hx
    have hcp : IsC n (andSwap gs ph y) y false (n + 1 + p) :=
      isC_reader hcl' y p g hgp' hlmem false (Or.inr (by simp [fixBit, hop]))
    have h3 := and_core n F gs o p ph y g y L false (hnc false) hgp hop hin hlne hph hone ho2 hlx
      {ph, p, S} (by
        intro q hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl
        · exact rc_input false hphR
        · exact rc_input false hpR
        · exact rc_of_reads hSr' hcp)
    rwa [Finset.card_eq_three.2 ⟨ph, p, S, by omega, by omega, by omega, rfl⟩] at h3
  ·
    rcases hlit with e | ⟨pn, rfl, hpn⟩
    · exact absurd e hly
    have hpnp : pn < p := by omega
    have hpnph : pn ≠ ph := fun e => hlne (by rw [e])
    have hpn' : (andSwap gs ph y)[pn]? = some ⟨GateOp.not, [(y : ℕ)]⟩ := by
      rw [andSwap_get_ne gs ph y pn hpnph]; exact hpn
    have hlx : ∀ x : Fin (n + 1) → Bool, x y = true → vl gs x (n + 1 + pn) = false := by
      intro x hx
      rw [vl_not gs L.hcl x pn _ hpn (y : ℕ) rfl rfl, vl_input gs x y y.isLt]
      simp [hx]
    have hpnR : Reads (andSwap gs ph y) pn y := ⟨_, hpn', by simp⟩
    obtain ⟨c, hc⟩ := isC_reader hcl' y pn _ hpn' (by simp) true (Or.inl rfl)
    have hc0 : c = false := by
      have h1 := st_val_const n _ hcl' y true _ c hc (fun _ => false)
      rw [vl_not _ hcl' _ pn _ hpn' (y : ℕ) rfl rfl, vl_input _ _ y y.isLt] at h1
      simp [ins] at h1
      exact h1
    subst hc0
    have hcp : IsC n (andSwap gs ph y) y true (n + 1 + p) :=
      const_read n _ hcl' y true p g hgp' (n + 1 + pn) hlmem (by simp [hc, fixBit, hop])
    have h4 := and_core n F gs o p ph (n + 1 + pn) g y L true (hnc true) hgp hop hin hlne hph
      hone ho2 hlx {ph, pn, p, S} (by
        intro q hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl
        · exact rc_input true hphR
        · exact rc_input true hpnR
        · exact rc_of_reads hpR ⟨false, hc⟩
        · exact rc_of_reads hSr' hcp)
    have hcard : ({ph, pn, p, S} : Finset ℕ).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp; omega),
        Finset.card_eq_three.2 ⟨pn, p, S, by omega, by omega, by omega, rfl⟩]
    rwa [hcard] at h4

theorem vl_dfree {N : ℕ} {D : Finset (Fin N)} {gs : List Gate} {h : ℕ} (hD : DFree D gs h)
    (u u' : Fin N → Bool) (hu : ∀ i, i ∉ D → u i = u' i) : vl gs u h = vl gs u' h := by
  unfold vl
  exact (agree_wiresFrom u u' gs _ _ _ (agree_inputs _ _)).2.2 h (fun i hi =>
    hu i (fun hiD => hD i hiD hi))

theorem out_ne_lit {N : ℕ} {F : (Fin N → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (hcl : CleanL N gs) (hev : ∀ x : Fin N → Bool, vl gs x o = F x) (y : Fin N)
    (hnc : ∀ b : Bool, ∃ x x' : Fin N → Bool,
      F (Function.update x y b) ≠ F (Function.update x' y b))
    (l : ℕ) (hl : IsLit N gs y l) : o ≠ l := by
  intro e
  subst e
  obtain ⟨x, x', hne⟩ := hnc false
  apply hne
  rw [← hev, ← hev]
  rcases hl with e | ⟨pn, e, hpn⟩
  · rw [e, vl_input _ _ _ y.isLt, vl_input _ _ _ y.isLt]
    simp
  · rw [e, vl_not gs hcl _ pn _ hpn (y : ℕ) rfl rfl, vl_not gs hcl _ pn _ hpn (y : ℕ) rfl rfl,
      vl_input _ _ _ y.isLt, vl_input _ _ _ y.isLt]
    simp

theorem win_core {N : ℕ} {F : (Fin N → Bool) → Bool} {D : Finset (Fin N)} {gs : List Gate}
    {o p : ℕ} {g : Gate} {y : Fin N} {l h : ℕ} (H : DeepHyp F D) (hcl : CleanL N gs)
    (hev : ∀ x : Fin N → Bool, vl gs x o = F x) (hO : OneReader D gs)
    (hF : Front D gs p g y l h) : ∀ x : Fin N → Bool, vl gs x h = fixBit g → F x = true := by
  obtain ⟨hp, hop, hin, hy, hl, hD⟩ := hF
  intro x hx
  cases hFx : F x with
  | true => rfl
  | false =>
  exfalso
  have hz : F (zeroOn D x) = false := by
    cases e : F (zeroOn D x) with
    | false => rfl
    | true => rw [H.mono x e] at hFx; cases hFx
  obtain ⟨x', hx'D, _, hF0, hF1⟩ := H.win y hy x hz
  have hagr : ∀ i, i ∉ D → x i = Function.update x' y true i := by
    intro i hi
    have hiy : i ≠ y := fun e => hi (e ▸ hy)
    rw [Function.update_of_ne hiy, hx'D i hi]
  have hagr' : ∀ i, i ∉ D → x i = x' i := fun i hi => (hx'D i hi).symm
  have hlmem : l ∈ g.inputs := by rcases hin with e | e <;> simp [e]
  have hhmem : h ∈ g.inputs := by rcases hin with e | e <;> simp [e]
  have hc1 : vl gs x' (N + p) = fixBit g :=
    vl_abs gs hcl x' p g hp hop h hhmem (by rw [← vl_dfree hD x x' hagr']; exact hx)
  have hc2 : vl gs (Function.update x' y true) (N + p) = fixBit g :=
    vl_abs gs hcl _ p g hp hop h hhmem (by rw [← vl_dfree hD x _ hagr]; exact hx)
  have hol : o ≠ l := out_ne_lit hcl hev y (H.nc y hy) l hl
  have hoy : o ≠ (y : ℕ) := out_ne_lit hcl hev y (H.nc y hy) y (Or.inl rfl)
  have key := agree_B gs hcl x' (Function.update x' y true) (fun j => j = (y : ℕ) ∨ j = l)
    (o + 1)
    (by
      intro j hj hB
      rw [vl_input _ _ _ hj, vl_input _ _ _ hj]
      have hne : (⟨j, hj⟩ : Fin N) ≠ y := fun e => hB (Or.inl (by rw [← e]))
      rw [Function.update_of_ne hne])
    (by
      intro q g' hq _ hBq hBa _
      obtain ⟨a, ha, hBa⟩ := hBa
      have hreads : Reads gs q a := ⟨g', hq, ha⟩
      have hqp : q = p := by
        rcases hl with el | ⟨pn, el, hpn⟩
        · have hay : a = (y : ℕ) := by
            rcases hBa with e | e
            · exact e
            · rw [e, el]
          exact hO.1 y hy q p (hay ▸ hreads) ⟨g, hp, el ▸ hlmem⟩
        · rcases hBa with e | e
          · exfalso
            have hq' := hO.1 y hy q pn (e ▸ hreads) ⟨_, hpn, by simp⟩
            apply hBq
            right
            rw [el, hq']
          · exact hO.2 y hy pn hpn q p (by rw [← el, ← e]; exact hreads)
              ⟨g, hp, el ▸ hlmem⟩
      rw [hqp, hc1, hc2])
    o (by omega) (by rintro (e | e) <;> contradiction)
  rw [hev, hev, hF0, hF1] at key
  cases key

theorem stmtWin : StmtWin := by
  intro n F D gs o p g y l h H L hO hF
  have core := win_core H L.hcl L.hev hO hF
  refine ⟨fun e x hx => core x (by simp [fixBit, e, hx]),
    fun e => ⟨fun x hx => core x (by simp [fixBit, e, hx]), ?_⟩⟩
  by_contra hge
  have hlt : h < n + 1 := by omega
  have h0 := core (fun _ => false) (by rw [vl_input _ _ _ hlt]; simp [fixBit, e])
  rw [H.zero] at h0
  cases h0

theorem vl_update_of_not_supp {N : ℕ} (gs : List Gate) (h : ℕ) (y : Fin N)
    (hy : y ∉ (suppsFrom gs (inputSupps N)).getD h ∅) (x : Fin N → Bool) (b : Bool) :
    vl gs (Function.update x y b) h = vl gs x h := by
  have A := agree_wiresFrom (Function.update x y b) x gs _ _ _
    (agree_inputs (Function.update x y b) x)
  refine A.2.2 h ?_
  intro i hi
  have hiy : i ≠ y := fun e => hy (e ▸ hi)
  exact Function.update_of_ne hiy b x

theorem stmtTwo : StmtExch → StmtWin → StmtTwo := by
  intro hEx hWin n F D gs o p g y l h hD L hOne hF hand hsec
  obtain ⟨hgp, _, hin, hyD, hlit, hfree⟩ := hF
  have hcl := L.hcl

  have hnc : ∃ x x' : Fin (n + 1) → Bool, F x ≠ F x' := by
    obtain ⟨x, x', hx⟩ := hD.nc y hyD false
    exact ⟨_, _, hx⟩
  obtain ⟨-, hW⟩ := hWin n F D gs o p g y l h hD L hOne ⟨hgp, Or.inl hand, hin, hyD, hlit, hfree⟩
  obtain ⟨hcov, hhN⟩ := hW hand

  have hT : ∀ T : Finset ℕ, (∀ t ∈ T, Reads gs t h ∨ ∃ (r : ℕ) (g : Gate), gs[r]? = some g ∧
      (g.op = GateOp.or ∨ g.op = GateOp.not) ∧ Reads gs r h ∧ Reads gs t (n + 1 + r)) →
      T.card ≤ 2 := by
    intro T hTm
    obtain ⟨gs', o', hc', he', hlen⟩ := hEx (n + 1) F gs o h T hcl L.hev hnc hcov hTm
    have := L.hmin gs' o' hc' he'
    omega
  have hpread : Reads gs p h := ⟨g, hgp, by rcases hin with e | e <;> rw [e] <;> simp⟩
  obtain ⟨r, hrp, hrr⟩ := hsec

  have hall : ∀ t, Reads gs t h → t = p ∨ t = r := by
    intro t ht
    by_contra hne
    push Not at hne
    have := hT {p, r, t} (by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl
      · exact Or.inl hpread
      · exact Or.inl hrr
      · exact Or.inl ht)
    rw [Finset.card_insert_of_notMem (by simp [hrp.symm, hne.1.symm]),
      Finset.card_insert_of_notMem (by simp [hne.2.symm]), Finset.card_singleton] at this
    omega
  obtain ⟨gr, hgr, hhr⟩ := hrr
  have hrlen : r < gs.length := (List.getElem?_eq_some_iff.1 hgr).1
  have hhlt : h < n + 1 + r := reads_lt hcl ⟨gr, hgr, hhr⟩
  rcases hcl r gr hgr with ⟨hnot, j, _, hjin⟩ | ⟨hop, j, k, _, _, hjk⟩
  ·
    exfalso
    have hj : j = h := by rw [hjin] at hhr; simp at hhr; exact hhr.symm
    rw [hj] at hjin
    by_cases ho : o = n + 1 + r
    ·
      have h0 : F (zeroOn D (fun _ => false)) = false := by
        have : zeroOn D (fun _ : Fin (n + 1) => false) = fun _ => false := by
          funext i; simp [zeroOn]
        rw [this]; exact hD.zero
      obtain ⟨x', _, hx'y, hFx', hFx''⟩ := hD.win y hyD _ h0
      have e1 := L.hev x'
      have e2 := L.hev (Function.update x' y true)
      rw [ho, vl_not gs hcl _ r gr hgr h hnot hjin] at e1 e2
      rw [vl_update_of_not_supp gs h y (hfree y hyD) x' true] at e2
      have : F x' = F (Function.update x' y true) := by rw [← e1, ← e2]
      rw [this, hFx''] at hFx'
      exact Bool.noConfusion hFx'
    · obtain ⟨t, hrt, htr⟩ := L.live hnc r hrlen ho
      have htp : t ≠ p := by
        rintro rfl
        obtain ⟨g2, hg2, hmem⟩ := htr
        have := gate_eq hgp hg2 rfl
        subst this
        have hm : n + 1 + r = l ∨ n + 1 + r = h := by
          rcases hin with e | e <;> rw [e] at hmem <;> simp at hmem <;> omega
        rcases hm with e | e
        · rcases hlit with e' | ⟨pn, e', hpn⟩
          · have := y.isLt; omega
          · have hrpn : r = pn := by omega
            subst hrpn
            have := gate_eq hgr hpn rfl
            rw [this] at hjin
            simp at hjin
            have := y.isLt; omega
        · omega
      have := hT {p, r, t} (by
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl | rfl
        · exact Or.inl hpread
        · exact Or.inl ⟨gr, hgr, hhr⟩
        · exact Or.inr ⟨r, gr, hgr, Or.inr hnot, ⟨gr, hgr, hhr⟩, htr⟩)
      rw [Finset.card_insert_of_notMem (by simp [hrp.symm, htp.symm]),
        Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton] at this
      omega
  · rcases hop with hop | hop
    ·
      refine ⟨r, gr, (if j = h then k else j), hrp, hgr, hop, ?_, hall⟩
      rw [hjk] at hhr ⊢
      by_cases hjh : j = h
      · subst hjh; right; simp
      · left
        simp at hhr ⊢
        omega
    ·
      exfalso
      by_cases ho : o = n + 1 + r
      ·
        apply hnc.elim
        intro x hx
        obtain ⟨x', hxx'⟩ := hx
        have key : ∀ z : Fin (n + 1) → Bool, F z = true := by
          intro z
          cases hz : vl gs z h
          · exact hcov z hz
          · rw [← L.hev z, ho, vl_gate gs hcl z r gr hgr, hop, hjk]
            rw [hjk] at hhr
            simp at hhr
            rcases hhr with e | e <;> subst e <;> simp [GateOp.eval, hz]
        exact hxx' (by rw [key x, key x'])
      · obtain ⟨t, hrt, htr⟩ := L.live hnc r hrlen ho
        have htp : t ≠ p := by
          rintro rfl
          obtain ⟨g2, hg2, hmem⟩ := htr
          have := gate_eq hgp hg2 rfl
          subst this
          have hm : n + 1 + r = l ∨ n + 1 + r = h := by
            rcases hin with e | e <;> rw [e] at hmem <;> simp at hmem <;> omega
          rcases hm with e | e
          · rcases hlit with e' | ⟨pn, e', hpn⟩
            · have := y.isLt; omega
            · have hrpn : r = pn := by omega
              subst hrpn
              have := gate_eq hgr hpn rfl
              rw [this] at hop
              exact GateOp.noConfusion hop
          · omega
        have := hT {p, r, t} (by
          intro u hu
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with rfl | rfl | rfl
          · exact Or.inl hpread
          · exact Or.inl ⟨gr, hgr, hhr⟩
          · exact Or.inr ⟨r, gr, hgr, Or.inl hop, ⟨gr, hgr, hhr⟩, htr⟩)
        rw [Finset.card_insert_of_notMem (by simp [hrp.symm, htp.symm]),
          Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton] at this
        omega

theorem front_suppsFrom_prefix {m : ℕ} (gs : List Gate) :
    ∀ L : List (Finset (Fin m)), ∃ T, suppsFrom gs L = L ++ T := by
  induction gs with
  | nil => intro L; exact ⟨[], by simp [suppsFrom]⟩
  | cons g gs ih =>
    intro L
    obtain ⟨T, hT⟩ := ih (L ++ [gateSupp L g])
    exact ⟨[gateSupp L g] ++ T, by
      show suppsFrom gs (L ++ [gateSupp L g]) = _
      rw [hT, List.append_assoc]⟩

theorem front_supp_input {m : ℕ} (gs : List Gate) (i : ℕ) (hi : i < m) :
    (suppsFrom gs (inputSupps m)).getD i ∅ = {(⟨i, hi⟩ : Fin m)} := by
  obtain ⟨T, hT⟩ := front_suppsFrom_prefix gs (inputSupps m)
  rw [hT, List.getD_append _ _ _ _ (by simp [inputSupps]; exact hi)]
  simp [inputSupps, hi]

theorem front_supp_beyond {m : ℕ} (gs : List Gate) (w : ℕ) (hw : m + gs.length ≤ w) :
    (suppsFrom gs (inputSupps m)).getD w ∅ = ∅ :=
  List.getD_eq_default _ _ (by rw [length_suppsFrom]; simp [inputSupps]; omega)

theorem front_supp_gate {m : ℕ} (gs : List Gate) (hcl : CleanL m gs) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (i : Fin m) :
    i ∈ (suppsFrom gs (inputSupps m)).getD (m + p) ∅ ↔
      ∃ a ∈ g.inputs, i ∈ (suppsFrom gs (inputSupps m)).getD a ∅ := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  set L0 := suppsFrom pre (inputSupps m) with hL0
  have hl0 : L0.length = m + pre.length := by rw [hL0, length_suppsFrom]; simp [inputSupps]
  have e : suppsFrom (pre ++ g :: post) (inputSupps m)
      = suppsFrom post (L0 ++ [gateSupp L0 g]) := by
    rw [suppsFrom_append]; rfl
  obtain ⟨T, hT⟩ := front_suppsFrom_prefix post (L0 ++ [gateSupp L0 g])
  have full : ∀ j, j < m + pre.length →
      (suppsFrom (pre ++ g :: post) (inputSupps m)).getD j ∅ = L0.getD j ∅ := by
    intro j hj
    rw [e, hT, List.getD_append _ _ _ _ (by simp [hl0]; omega), getD_snoc_ne _ _ _ _ (by omega)]
  have top : (suppsFrom (pre ++ g :: post) (inputSupps m)).getD (m + pre.length) ∅
      = gateSupp L0 g := by
    rw [e, hT, List.getD_append _ _ _ _ (by simp [hl0]), ← hl0, getD_snoc_eq]
  rw [top, mem_gateSupp]
  constructor
  · rintro ⟨a, ha, hia⟩
    exact ⟨a, ha, by rw [full a (hlt a ha)]; exact hia⟩
  · rintro ⟨a, ha, hia⟩
    exact ⟨a, ha, by rw [← full a (hlt a ha)]; exact hia⟩

section

variable {n : ℕ} {F : (Fin (n + 1) → Bool) → Bool} {D : Finset (Fin (n + 1))} {gs : List Gate}
  {o : ℕ}

theorem front_nlit (DH : DeepHyp F D) {y : Fin (n + 1)} (hy : y ∈ D) (c : Bool) :
    ¬ ∀ u, F u = xor (u y) c := by
  intro h
  obtain ⟨x, x', hx⟩ := DH.nc y hy false
  apply hx
  rw [h, h]
  simp

theorem front_fnc (DH : DeepHyp F D) {y : Fin (n + 1)} (hy : y ∈ D) :
    ∃ x x' : Fin (n + 1) → Bool, F x ≠ F x' := by
  obtain ⟨x, x', hx⟩ := DH.nc y hy false
  exact ⟨_, _, hx⟩

theorem front_dep (DH : DeepHyp F D) (L : Least (n + 1) F gs o) {y : Fin (n + 1)} (hy : y ∈ D) :
    y ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅ := by
  have hz : zeroOn D (fun _ : Fin (n + 1) => false) = fun _ => false := by
    funext i; simp [zeroOn]
  obtain ⟨x', -, -, hF0, hF1⟩ := DH.win y hy (fun _ => false) (by rw [hz]; exact DH.zero)
  by_contra hno
  have hag := (agree_wiresFrom (Function.update x' y true) x' gs _ _ _
    (agree_inputs _ _)).2.2 o (by
      intro k hk
      have : k ≠ y := fun e => hno (e ▸ hk)
      simp [Function.update_of_ne this])
  have e : F (Function.update x' y true) = F x' := by
    rw [← L.hev, ← L.hev]
    exact hag
  rw [hF0, hF1] at e
  cases e

theorem front_dlit (L : Least (n + 1) F gs o) (hfnc : ∃ x x' : Fin (n + 1) → Bool, F x ≠ F x')
    (p0 : ℕ) (hmin : ∀ r < p0, ∀ g, gs[r]? = some g → (g.op = GateOp.and ∨ g.op = GateOp.or) →
      ∀ i ∈ D, i ∉ (suppsFrom gs (inputSupps (n + 1))).getD (n + 1 + r) ∅) :
    ∀ w, w < n + 1 + p0 → (∃ i ∈ D, i ∈ (suppsFrom gs (inputSupps (n + 1))).getD w ∅) →
      ∃ y ∈ D, ∃ c : Bool, (∀ u, vl gs u w = xor (u y) c) ∧
        (w = y ∨ ∃ pn, pn < p0 ∧ w = n + 1 + pn ∧ gs[pn]? = some ⟨GateOp.not, [(y : ℕ)]⟩) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rintro hw ⟨i, hi, his⟩
    by_cases hwn : w < n + 1
    · rw [front_supp_input gs w hwn, Finset.mem_singleton] at his
      subst his
      exact ⟨⟨w, hwn⟩, hi, false, fun u => by rw [vl_input gs u w hwn]; simp, Or.inl rfl⟩
    · obtain ⟨r, rfl⟩ : ∃ r, w = n + 1 + r := ⟨w - (n + 1), by omega⟩
      cases hg : gs[r]? with
      | none =>
        have hlen : gs.length ≤ r := List.getElem?_eq_none_iff.1 hg
        rw [front_supp_beyond gs _ (by omega)] at his
        simp at his
      | some g =>
        have hrl : r < gs.length := (List.getElem?_eq_some_iff.1 hg).1
        rcases L.hcl r g hg with ⟨hop, j, hj, hin⟩ | ⟨hop, _⟩
        · obtain ⟨a, ha, hia⟩ := (front_supp_gate gs L.hcl r g hg i).1 his
          rw [hin, List.mem_singleton] at ha
          subst ha
          obtain ⟨y, hy, c, hv, hs⟩ := ih a (by omega) (by omega) ⟨i, hi, hia⟩
          rcases hs with e | ⟨pn, hpn, e, hgpn⟩
          · have hge : g = ⟨GateOp.not, [(y : ℕ)]⟩ := by
              cases g
              simp only at hop hin
              rw [hop, hin, e]
            refine ⟨y, hy, !c, fun u => ?_, Or.inr ⟨r, by omega, rfl, by rw [← hge]; exact hg⟩⟩
            rw [vl_not gs L.hcl u r g hg a hop hin, hv]
            cases u y <;> cases c <;> rfl
          · exfalso
            have hpl : pn < gs.length := (List.getElem?_eq_some_iff.1 hgpn).1
            refine L.no_alias hfnc r hrl y (by have := y.isLt; omega) (fun u => ?_)
            rw [vl_not gs L.hcl u r g hg a hop hin, e,
              vl_not gs L.hcl u pn _ hgpn (y : ℕ) rfl rfl, vl_input gs u y y.isLt]
            simp
        · exact absurd his (hmin r (by omega) g hg hop i hi)

theorem front_out (DH : DeepHyp F D) (L : Least (n + 1) F gs o) (p : ℕ) (g : Gate)
    (hg : gs[p]? = some g) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (l : ℕ)
    (hl : l ∈ g.inputs) {y : Fin (n + 1)} (hy : y ∈ D) (c : Bool)
    (hv : ∀ u, vl gs u l = xor (u y) c) : o ≠ n + 1 + p := by
  intro e
  obtain ⟨x, x', hx⟩ := DH.nc y hy (xor (fixBit g) c)
  have hc : ∀ z : Fin (n + 1) → Bool, F (Function.update z y (xor (fixBit g) c)) = fixBit g := by
    intro z
    rw [← L.hev, e]
    refine vl_abs gs L.hcl _ p g hg hop l hl ?_
    rw [hv]
    simp
  exact hx (by rw [hc, hc])

theorem front_two (DH : DeepHyp F D) (L : Least (n + 1) F gs o) (OR : OneReader D gs) (p : ℕ)
    (g : Gate) (hg : gs[p]? = some g) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (j k : ℕ)
    (hin : g.inputs = [j, k]) (hj : j < n + 1 + p) (hk : k < n + 1 + p)
    (yj : Fin (n + 1)) (hyj : yj ∈ D) (cj : Bool) (hvj : ∀ u, vl gs u j = xor (u yj) cj)
    (hsj : j = yj ∨ ∃ pn, pn < p ∧ j = n + 1 + pn ∧ gs[pn]? = some ⟨GateOp.not, [(yj : ℕ)]⟩)
    (yk : Fin (n + 1)) (hyk : yk ∈ D) (ck : Bool) (hvk : ∀ u, vl gs u k = xor (u yk) ck)
    (hsk : k = yk ∨ ∃ pn, pn < p ∧ k = n + 1 + pn ∧ gs[pn]? = some ⟨GateOp.not, [(yk : ℕ)]⟩) :
    False := by
  have hfnc := front_fnc DH hyj
  have htl : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  have hRj : Reads gs p j := ⟨g, hg, by rw [hin]; simp⟩
  have hRk : Reads gs p k := ⟨g, hg, by rw [hin]; simp⟩

  have hopnd : ∀ (w : ℕ) (v : Fin (n + 1)), v ∈ D → Reads gs p w →
      (w = v ∨ ∃ pn, pn < p ∧ w = n + 1 + pn ∧ gs[pn]? = some ⟨GateOp.not, [(v : ℕ)]⟩) →
      ∀ p' a, (a = (v : ℕ) ∨ a = w) → Reads gs p' a → n + 1 + p' ≠ w → p' = p := by
    intro w v hv hw hs p' a ha hr hne
    rcases hs with e | ⟨r, _, er, hg'⟩
    · have ha' : a = v := by
        rcases ha with ha | ha
        · exact ha
        · rw [ha, e]
      rw [ha'] at hr
      exact OR.1 v hv p' p hr (by rw [← e]; exact hw)
    · have hrv : Reads gs r v := ⟨_, hg', by simp⟩
      rcases ha with ha | ha
      · rw [ha] at hr
        have := OR.1 v hv p' r hr hrv
        exact (hne (by rw [this, er])).elim
      · rw [ha, er] at hr
        rw [er] at hw
        exact OR.2 v hv r hg' p' p hr hw

  have hvjk : yj ≠ yk := by
    intro e
    have hjk : j ≠ k := by
      intro e'
      subst e'
      exact L.no_alias hfnc p htl j hj (fun u => by
        rw [vl_gate gs L.hcl u p g hg, hin]
        rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval])
    rcases hsj with ej | ⟨r1, hr1, ej, hg1⟩ <;> rcases hsk with ek | ⟨r2, hr2, ek, hg2⟩
    · exact hjk (by rw [ej, ek, e])
    · have := OR.1 yj hyj p r2 (by rw [← ej]; exact hRj) ⟨_, hg2, by rw [← e]; simp⟩
      omega
    · have := OR.1 yk hyk p r1 (by rw [← ek]; exact hRk) ⟨_, hg1, by rw [e]; simp⟩
      omega
    · have := OR.1 yj hyj r1 r2 ⟨_, hg1, by simp⟩ ⟨_, hg2, by rw [← e]; simp⟩
      exact hjk (by rw [ej, ek, this])

  have KC : ∀ u u' : Fin (n + 1) → Bool, (∀ i, i ≠ yj → i ≠ yk → u i = u' i) →
      vl gs u (n + 1 + p) = vl gs u' (n + 1 + p) → F u = F u' := by
    intro u u' hagr hgv
    rw [← L.hev, ← L.hev]
    refine agree_B gs L.hcl u u' (fun a => a = (yj : ℕ) ∨ a = (yk : ℕ) ∨ a = j ∨ a = k) (o + 1)
      ?_ ?_ o (by omega) ?_
    · intro a ha hBa
      have hBa' : ¬ (a = (yj : ℕ) ∨ a = (yk : ℕ) ∨ a = j ∨ a = k) := hBa
      rw [vl_input gs u a ha, vl_input gs u' a ha]
      apply hagr
      · intro e
        exact hBa' (Or.inl (congrArg Fin.val e))
      · intro e
        exact hBa' (Or.inr (Or.inl (congrArg Fin.val e)))
    · intro p' g' hp' _ hB' hr _
      have hB'' : ¬ (n + 1 + p' = (yj : ℕ) ∨ n + 1 + p' = (yk : ℕ) ∨ n + 1 + p' = j ∨
          n + 1 + p' = k) := hB'
      obtain ⟨a, ha, hBa⟩ := hr
      have hBa' : a = (yj : ℕ) ∨ a = (yk : ℕ) ∨ a = j ∨ a = k := hBa
      have hR : Reads gs p' a := ⟨g', hp', ha⟩
      have hpt : p' = p := by
        rcases hBa' with e | e | e | e
        · exact hopnd j yj hyj hRj hsj p' a (Or.inl e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inl e'))))
        · exact hopnd k yk hyk hRk hsk p' a (Or.inl e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inr e'))))
        · exact hopnd j yj hyj hRj hsj p' a (Or.inr e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inl e'))))
        · exact hopnd k yk hyk hRk hsk p' a (Or.inr e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inr e'))))
      rw [hpt]
      exact hgv
    · intro hB
      have hB' : o = (yj : ℕ) ∨ o = (yk : ℕ) ∨ o = j ∨ o = k := hB
      rcases hB' with e | e | e | e
      · exact front_nlit DH hyj false (fun x => by
          rw [← L.hev, e, vl_input gs x yj yj.isLt]; simp)
      · exact front_nlit DH hyk false (fun x => by
          rw [← L.hev, e, vl_input gs x yk yk.isLt]; simp)
      · exact front_nlit DH hyj cj (fun x => by rw [← L.hev, e, hvj])
      · exact front_nlit DH hyk ck (fun x => by rw [← L.hev, e, hvk])
  have hag : ∀ (x : Fin (n + 1) → Bool) (a b a' b' : Bool), ∀ i, i ≠ yj → i ≠ yk →
      set2 x yj a yk b i = set2 x yj a' yk b' i := by
    intro x a b a' b' i e1 e2
    rw [set2_o x yj yk a b i e1 e2, set2_o x yj yk a' b' i e1 e2]
  have hval : ∀ (x : Fin (n + 1) → Bool) (a b : Bool),
      vl gs (set2 x yj a yk b) (n + 1 + p) = g.op.eval [xor a cj, xor b ck] := by
    intro x a b
    rw [vl_gate gs L.hcl _ p g hg, hin]
    simp only [List.map_cons, List.map_nil]
    rw [hvj, hvk, set2_p x hvjk, set2_q x]
  apply DH.nf yj hyj yk hyk hvjk
  rcases hop with hop | hop
  · refine ⟨!cj, !ck, fun x => ⟨KC _ _ (hag x _ _ _ _) ?_, KC _ _ (hag x _ _ _ _) ?_⟩⟩ <;>
      rw [hval, hval, hop] <;> cases cj <;> cases ck <;> rfl
  · refine ⟨cj, ck, fun x => ⟨KC _ _ (hag x _ _ _ _) ?_, KC _ _ (hag x _ _ _ _) ?_⟩⟩ <;>
      rw [hval, hval, hop] <;> cases cj <;> cases ck <;> rfl

end

theorem stmtFront : StmtFront := by
  intro n F D gs o DH hD L OR
  classical
  obtain ⟨y0, hy0⟩ := hD
  have hfnc := front_fnc DH hy0
  by_cases hex : ∃ p g, gs[p]? = some g ∧ (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ i ∈ D, i ∈ (suppsFrom gs (inputSupps (n + 1))).getD (n + 1 + p) ∅
  · obtain ⟨g, hg, hop, i, hi, his⟩ := Nat.find_spec hex
    set p := Nat.find hex with hpdef
    have hmin : ∀ r < p, ∀ g', gs[r]? = some g' → (g'.op = GateOp.and ∨ g'.op = GateOp.or) →
        ∀ i ∈ D, i ∉ (suppsFrom gs (inputSupps (n + 1))).getD (n + 1 + r) ∅ :=
      fun r hr g' hg' hop' i hi his => Nat.find_min hex hr ⟨g', hg', hop', i, hi, his⟩
    rcases L.hcl p g hg with ⟨hop2, _⟩ | ⟨_, j, k, hj, hk, hin⟩
    · rcases hop with h | h <;> rw [h] at hop2 <;> cases hop2
    obtain ⟨a, ha, hia⟩ := (front_supp_gate gs L.hcl p g hg i).1 his
    rw [hin] at ha
    have hlitof : ∀ (w : ℕ) (y : Fin (n + 1)),
        (w = y ∨ ∃ pn, pn < p ∧ w = n + 1 + pn ∧ gs[pn]? = some ⟨GateOp.not, [(y : ℕ)]⟩) →
        IsLit (n + 1) gs y w := by
      rintro w y (e | ⟨pn, _, e, hpn⟩)
      · exact Or.inl e
      · exact Or.inr ⟨pn, e, hpn⟩
    by_cases mj : ∃ i ∈ D, i ∈ (suppsFrom gs (inputSupps (n + 1))).getD j ∅ <;>
      by_cases mk : ∃ i ∈ D, i ∈ (suppsFrom gs (inputSupps (n + 1))).getD k ∅
    · exfalso
      obtain ⟨yj, hyj, cj, hvj, hsj⟩ := front_dlit L hfnc p hmin j hj mj
      obtain ⟨yk, hyk, ck, hvk, hsk⟩ := front_dlit L hfnc p hmin k hk mk
      exact front_two DH L OR p g hg hop j k hin hj hk yj hyj cj hvj hsj yk hyk ck hvk hsk
    · obtain ⟨y, hy, c, hv, hs⟩ := front_dlit L hfnc p hmin j hj mj
      refine ⟨p, g, y, j, k, ⟨hg, hop, Or.inl hin, hy, hlitof j y hs,
        fun y' hy' hm => mk ⟨y', hy', hm⟩⟩,
        front_out DH L p g hg hop j (by rw [hin]; simp) hy c hv⟩
    · obtain ⟨y, hy, c, hv, hs⟩ := front_dlit L hfnc p hmin k hk mk
      refine ⟨p, g, y, k, j, ⟨hg, hop, Or.inr hin, hy, hlitof k y hs,
        fun y' hy' hm => mj ⟨y', hy', hm⟩⟩,
        front_out DH L p g hg hop k (by rw [hin]; simp) hy c hv⟩
    · exfalso
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact mj ⟨i, hi, hia⟩
      · exact mk ⟨i, hi, hia⟩
  · exfalso
    have hmin : ∀ r < gs.length, ∀ g', gs[r]? = some g' →
        (g'.op = GateOp.and ∨ g'.op = GateOp.or) →
        ∀ i ∈ D, i ∉ (suppsFrom gs (inputSupps (n + 1))).getD (n + 1 + r) ∅ :=
      fun r _ g' hg' hop' i hi his => hex ⟨r, g', hg', hop', i, hi, his⟩
    by_cases hol : o < n + 1 + gs.length
    · obtain ⟨y, hy, c, hv, _⟩ := front_dlit L hfnc gs.length hmin o hol
        ⟨y0, hy0, front_dep DH L hy0⟩
      exact front_nlit DH hy c (fun u => by rw [← L.hev, hv])
    · obtain ⟨x, x', hxx⟩ := hfnc
      apply hxx
      rw [← L.hev, ← L.hev, vl_beyond gs x o (by omega), vl_beyond gs x' o (by omega)]

theorem deepHyp_nc {N : ℕ} {F : (Fin N → Bool) → Bool} {D : Finset (Fin N)}
    (hD : DeepHyp F D) (hne : D.Nonempty) : ∃ x y : Fin N → Bool, F x ≠ F y := by
  obtain ⟨y, hy⟩ := hne
  obtain ⟨x, x', h⟩ := hD.nc y hy false
  exact ⟨_, _, h⟩

theorem deepHyp_dep {N : ℕ} {F : (Fin N → Bool) → Bool} {D : Finset (Fin N)}
    (hD : DeepHyp F D) {y : Fin N} (hy : y ∈ D) : Dep F y := by
  have h0 : F (zeroOn D (fun _ => false)) = false := by
    have : zeroOn D (fun _ : Fin N => false) = fun _ => false := by
      funext i; simp [zeroOn]
    rw [this]; exact hD.zero
  obtain ⟨x', -, hx'y, hF, hF'⟩ := hD.win y hy _ h0
  refine ⟨x', ?_⟩
  rw [hx'y, hF, show (!false) = true from rfl, hF']
  simp

theorem least_len {N : ℕ} {F : (Fin N → Bool) → Bool} {gs gs' : List Gate} {o o' : ℕ}
    (L : Least N F gs o) (L' : Least N F gs' o') : gs.length = gs'.length :=
  le_antisymm (L.hmin gs' o' L'.hcl L'.hev) (L'.hmin gs o L.hcl L.hev)

theorem vl_bin {N : ℕ} (gs : List Gate) (hcl : CleanL N gs) (x : Fin N → Bool) (p l h : ℕ)
    (g : Gate) (hg : gs[p]? = some g) (hin : g.inputs = [l, h] ∨ g.inputs = [h, l]) :
    (g.op = GateOp.or → vl gs x (N + p) = (vl gs x l || vl gs x h)) ∧
    (g.op = GateOp.and → vl gs x (N + p) = (vl gs x l && vl gs x h)) := by
  rw [vl_gate gs hcl x p g hg]
  constructor <;> intro hop <;> rw [hop] <;>
    rcases hin with e | e <;> rw [e] <;> simp [GateOp.eval, Bool.or_comm, Bool.and_comm]

theorem not_tailOK_or {n : ℕ} {F : (Fin (n + 1) → Bool) → Bool} {D : Finset (Fin (n + 1))}
    {gs : List Gate} {o p : ℕ} {g : Gate} {y : Fin (n + 1)} {l h : ℕ}
    (hD : DeepHyp F D) (L : Least (n + 1) F gs o) (hf : Front D gs p g y l h)
    (hop : g.op = GateOp.or) : ¬ TailOK (n + 1) F gs p := by
  obtain ⟨hg, -, hin, hy, hlit, -⟩ := hf
  rintro ⟨g', hg', hop' | ⟨-, hbel⟩⟩
  · rw [hg] at hg'; cases hg'; rw [hop] at hop'; cases hop'
  · rw [hg] at hg'; cases hg'

    have key : ∀ b : Bool, (∀ x : Fin (n + 1) → Bool, x y = b → vl gs x l = true) → False := by
      intro b hb
      obtain ⟨x, x', hne⟩ := hD.nc y hy b
      have : ∀ z : Fin (n + 1) → Bool, F (Function.update z y b) = true := by
        intro z
        apply hbel
        rw [(vl_bin gs L.hcl _ p l h g hg hin).1 hop, hb _ (by simp)]
        rfl
      exact hne (by rw [this, this])
    rcases hlit with rfl | ⟨pn, rfl, hpn⟩
    · apply key true
      intro x hx
      rw [vl_input gs x y y.isLt]
      simpa using hx
    · apply key false
      intro x hx
      rw [vl_not gs L.hcl x pn _ hpn y rfl rfl, vl_input gs x y y.isLt]
      simpa using hx

theorem stmtExt (hLift : StmtLift) (hX : StmtXMove) (hFront : StmtFront) (hWin : StmtWin)
    (hTwo : StmtTwo) : StmtExt := by
  classical
  intro n F D s hD hne hs
  have hnc := deepHyp_nc hD hne
  obtain ⟨gs0, o0, L0, hl0⟩ := exists_least (n + 1) F s hnc hs
  let P : ℕ → Prop := fun t => ∃ (gs : List Gate) (o : ℕ), Least (n + 1) F gs o ∧
    TailGE (n + 1) F gs t
  have hP0 : P 0 := ⟨gs0, o0, L0, TailGE.zero _ _ _⟩

  have hbound : ∀ t, P t → t ≤ gs0.length := by
    rintro t ⟨gs, o, L, ht⟩
    exact (least_len L L0) ▸ ht.le
  set M := Nat.findGreatest P gs0.length with hM
  obtain ⟨gs, o, L, ht⟩ : P M := Nat.findGreatest_spec (Nat.zero_le _) hP0
  have hmax : ∀ t, P t → t ≤ M := fun t h => Nat.le_findGreatest (hbound t h) h
  refine ⟨gs, o, L, by rw [least_len L L0]; exact hl0, ?_⟩
  by_contra hstop
  push Not at hstop
  obtain ⟨hone, hnoand⟩ := hstop
  obtain ⟨p, g, y, l, h, hf, hop⟩ := hFront n F D gs o hD hne L hone
  have hw := hWin n F D gs o p g y l h hD L hone hf
  obtain ⟨hg, hor, hin, -, -, -⟩ := id hf
  rcases hor with hand | hor
  ·
    obtain ⟨hbel, hhN⟩ := hw.2 hand
    obtain ⟨t, htr, htp⟩ := hnoand p g y l h hf hand hhN hop
    obtain ⟨r, g', q, hrp, hg', hand', hin', -⟩ :=
      hTwo n F D gs o p g y l h hD L hone hf hand ⟨t, htp, htr⟩
    obtain ⟨gs', o', L', ht'⟩ : P (M + 2) := by
      rcases lt_or_gt_of_ne hrp with hlt | hlt
      · obtain ⟨gs', o', L', ht'⟩ :=
          hX (n + 1) F gs o r p q l h g' g L hnc hlt hg' hand' hin' hg hand hin hbel
        exact ⟨gs', o', L', ht' M ht⟩
      · obtain ⟨gs', o', L', ht'⟩ :=
          hX (n + 1) F gs o p r l q h g g' L hnc hlt hg hand hin hg' hand' hin' hbel
        exact ⟨gs', o', L', ht' M ht⟩
    have := hmax _ ⟨gs', o', L', ht'⟩
    omega
  ·
    have hbel := hw.1 hor
    obtain ⟨L', ht'⟩ := hLift (n + 1) F gs o p l h g L hnc hg hor hin hbel
    have := hmax _ ⟨_, _, L', ht' (not_tailOK_or hD L hf hor) M ht⟩
    omega

theorem stmtML (hAnd : StmtAnd) (hExt : StmtExt) : StmtML := by
  intro n F D s hD hne hs
  have hnc := deepHyp_nc hD hne
  obtain ⟨gs, o, L, hls, halt⟩ := hExt n F D s hD hne hs
  rcases halt with hone | ⟨p, g, y, l, h, hf, hand, hhN, hop, honly⟩
  · simp only [OneReader, not_and_or] at hone
    push Not at hone
    rcases hone with ⟨y, hy, p, q, hp, hq, hpq⟩ | ⟨y, hy, pn, hpn, p, q, hp, hq, hpq⟩
    · refine ⟨y, hy, ?_⟩
      rcases L.two_readers y (hD.nc y hy) p q hpq hp hq with
        ⟨h3, -⟩ | ⟨h4, -⟩ | ⟨-, h4⟩
      · exact Or.inl (h3.mono le_rfl hls)
      · exact Or.inl (h4.mono (by omega) hls)
      · exact Or.inr (h4.mono le_rfl hls)
    · refine ⟨y, hy, Or.inl ?_⟩
      exact (L.not_two_readers y (hD.nc y hy) pn _ hpn rfl (by simp) p q hpq hp hq).1.mono
        le_rfl hls
  · obtain ⟨hg, -, hin, hy, hlit, hfree⟩ := hf
    refine ⟨y, hy, ?_⟩
    have hrd : Reads gs p h := ⟨g, hg, by rcases hin with e | e <;> rw [e] <;> simp⟩
    have hhlt := reads_lt L.hcl hrd
    have hplt := reads_len hrd
    have hdep := deepHyp_dep hD hy

    have hoh : o ≠ h := by
      rintro rfl
      obtain ⟨x, hx⟩ := hdep
      apply hx
      rw [← L.hev, ← L.hev]
      exact (agree_wiresFrom (Function.update x y (!x y)) x gs _ _ _
        (agree_inputs _ _)).2.2 o (by
          intro k hk
          have : k ≠ y := fun e => hfree y hy (e ▸ hk)
          simp [Function.update_of_ne this])
    obtain ⟨ph, rfl⟩ : ∃ ph, h = n + 1 + ph := ⟨h - (n + 1), by omega⟩
    have hA := hAnd n F gs o p ph l g y L (hD.nc y hy) hdep hg hand hin hlit (by omega)
      honly hop hoh
    by_cases hl : l = (y : ℕ)
    · exact Or.inl ((hA.1 hl).mono le_rfl hls)
    · exact Or.inr ((hA.2 hl).mono le_rfl hls)

theorem stmtML_final : StmtML :=
  stmtML stmtAnd (stmtExt stmtLift stmtXMove stmtFront stmtWin (stmtTwo stmtExch stmtWin))

theorem stmtML_any (M : ℕ) (hM : 0 < M) (F : (Fin M → Bool) → Bool) (D : Finset (Fin M)) (s : ℕ)
    (hD : DeepHyp F D) (hne : D.Nonempty) (hc : HasCircuitSize M F s) :
    ∃ y ∈ D, Drop F y false 3 s ∨ Drop F y true 4 s := by
  cases M with
  | zero => omega
  | succ n => exact stmtML_final n F D s hD hne hc

theorem dep_of_ft {M : ℕ} {f : (Fin M → Bool) → Bool} {i : Fin M}
    (h : ∃ x : Fin M → Bool, f (Function.update x i false) ≠ f (Function.update x i true)) :
    Dep f i := by
  obtain ⟨x, hx⟩ := h
  refine ⟨Function.update x i false, ?_⟩
  simp only [Function.update_self, Bool.not_false, Function.update_idem]
  exact hx.symm

theorem drop1_var {M : ℕ} {f : (Fin M → Bool) → Bool} {s : ℕ} (i : Fin M) (b : Bool)
    (hd : Dep f i)
    (hnc : ∃ x y : Fin M → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (hc : HasCircuitSize M f s) : Drop f i b 1 s := by
  cases M with
  | zero => exact Fin.elim0 i
  | succ n =>
    have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
      obtain ⟨x, y, hxy⟩ := hnc
      exact ⟨_, _, hxy⟩
    obtain ⟨gs, o, L, hls⟩ := exists_least (n + 1) f s hfnc hc
    have hread : ∃ q, Reads gs q i := by
      by_contra hno
      have hno' : ∀ g ∈ gs, (i : ℕ) ∉ g.inputs := by
        intro g hg hi
        obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg
        exact hno ⟨q, g, hq, hi⟩
      have hoi : o ≠ i := by
        intro e
        obtain ⟨x, y, hxy⟩ := hnc
        apply hxy
        rw [← L.hev, ← L.hev, e, vl_input gs _ i i.isLt, vl_input gs _ i i.isLt]
        simp
      obtain ⟨x, hx⟩ := hd
      apply hx
      rw [← L.hev, ← L.hev]
      refine agree_except i gs _ _ hno' (by simp) ?_ o hoi
      intro j hj
      by_cases hjm : j < n + 1
      · rw [show (List.ofFn (Function.update x i (!x i))).getD j false
              = Function.update x i (!x i) ⟨j, hjm⟩ from getD_ofFn (n + 1) _ false ⟨j, hjm⟩,
            show (List.ofFn x).getD j false = x ⟨j, hjm⟩ from getD_ofFn (n + 1) x false ⟨j, hjm⟩]
        exact Function.update_of_ne (fun e => hj (congrArg Fin.val e)) _ _
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    obtain ⟨q, hq⟩ := hread
    have h1 := L.save i b hnc {q} (by
      intro p hp
      rw [Finset.mem_singleton] at hp
      subst hp
      exact rc_input b hq)
    rw [Finset.card_singleton] at h1
    exact h1.mono le_rfl hls

theorem drop2_var {M : ℕ} {f : (Fin M → Bool) → Bool} {s : ℕ} (i : Fin M)
    (hd : Dep f i)
    (hnc : ∀ b : Bool, ∃ x y : Fin M → Bool,
      f (Function.update x i b) ≠ f (Function.update y i b))
    (hc : HasCircuitSize M f s) : Drop f i false 2 s ∨ Drop f i true 2 s := by
  cases M with
  | zero => exact Fin.elim0 i
  | succ n =>
    have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
      obtain ⟨x, y, hxy⟩ := hnc false
      exact ⟨_, _, hxy⟩
    obtain ⟨gs, o, L, hls⟩ := exists_least (n + 1) f s hfnc hc
    obtain ⟨p, gp, hgp, hip⟩ := L.dep_read i hd hnc
    have hpr : Reads gs p i := ⟨gp, hgp, hip⟩
    let b : Bool := fixBit gp
    have hcp : IsC n gs i b (n + 1 + p) :=
      isC_reader L.hcl i p gp hgp hip b (Or.inr rfl)
    obtain ⟨q, hpq, _, hqrc⟩ := L.next i b (hnc b) p (reads_len hpr) hcp
    have hd2 : Drop f i b 2 s :=
      (L.save2 i b (hnc b) p q (by omega) (rc_input b hpr) hqrc).mono le_rfl hls
    cases hb : b with
    | false =>
      rw [hb] at hd2
      exact Or.inl hd2
    | true =>
      rw [hb] at hd2
      exact Or.inr hd2

theorem add_pendant {M s : ℕ} (H : (Fin M → Bool) → Bool) (r a : Fin M)
    (hT : ∃ x : Fin M → Bool, H x = true) (hc : HasCircuitSize M H s) :
    HasCircuitSize M (fun x => H x || (x r && x a)) (s + 2) := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  have hout : C.output < M + C.gates.length := by
    by_contra hge
    obtain ⟨y, hy⟩ := hT
    have hfalse : C.eval (List.ofFn y) = false := by
      show (wiresFrom C.gates (List.ofFn y)).getD C.output false = false
      exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)
    have e := hev y
    rw [hfalse, hy] at e
    cases e
  let K : ℕ := M + C.gates.length
  let g0 : Gate := ⟨GateOp.and, [r.val, a.val]⟩
  let g1 : Gate := ⟨GateOp.or, [C.output, K]⟩
  refine ⟨⟨C.gates ++ [g0, g1], K + 1⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | rfl | rfl
    · exact ok g hg
    · simp [g0]
    · simp [g1]
  · simp only [Circuit.size, List.length_append, List.length_cons, List.length_nil] at hsz ⊢
    omega
  · intro x
    show (wiresFrom (C.gates ++ [g0, g1]) (List.ofFn x)).getD (K + 1) false =
      (H x || (x r && x a))
    rw [wiresFrom_append]
    set W := wiresFrom C.gates (List.ofFn x) with hW
    have hlen : W.length = K := by rw [hW, length_wiresFrom]; simp [K]
    have hxr : W.getD r.val false = x r := by
      rw [hW, getD_wiresFrom _ _ r.val (by simp)]
      exact getD_ofFn M x false r
    have hxa : W.getD a.val false = x a := by
      rw [hW, getD_wiresFrom _ _ a.val (by simp)]
      exact getD_ofFn M x false a
    have hxo : W.getD C.output false = H x := hev x
    set W0 := W ++ [g0.op.eval (g0.inputs.map fun i => W.getD i false)] with hW0
    have hl0 : W0.length = K + 1 := by simp [hW0, hlen]
    have hv0 : W0.getD K false = (x r && x a) := by
      rw [hW0, getD_snoc_len _ _ _ _ hlen]
      simp only [g0, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id,
        Bool.and_true, hxr, hxa]
    have hstep : wiresFrom [g0, g1] W =
        W0 ++ [g1.op.eval (g1.inputs.map fun i => W0.getD i false)] := rfl
    rw [hstep, getD_snoc_len _ _ _ _ hl0]
    simp only [g1, List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id,
      Bool.or_false]
    rw [hW0, List.getD_append _ _ _ _ (by omega), hxo, ← hW0, hv0]

theorem eq_of_indep {M : ℕ} (H : (Fin M → Bool) → Bool) :
    ∀ {m : ℕ} (q : Fin m → Fin M),
      (∀ (i : Fin m) (x : Fin M → Bool) (b : Bool), H (Function.update x (q i) b) = H x) →
      ∀ (x y : Fin M → Bool), (∀ j : Fin M, (∀ i : Fin m, q i ≠ j) → x j = y j) →
      H x = H y
  | 0, q, _, x, y, hag => by
    have e : x = y := funext fun j => hag j (fun i => Fin.elim0 i)
    rw [e]
  | k + 1, q, hH, x, y, hag => by
    let x' := Function.update x (q (Fin.last k)) (y (q (Fin.last k)))
    have h1 : H x = H x' := (hH (Fin.last k) x _).symm
    rw [h1]
    apply eq_of_indep H (fun i : Fin k => q i.castSucc) (fun i => hH i.castSucc) x' y
    intro j hj
    by_cases hje : j = q (Fin.last k)
    · subst hje
      simp [x']
    · simp only [x', Function.update_of_ne hje]
      apply hag j
      intro i
      refine Fin.lastCases ?_ (fun i' => ?_) i
      · exact Ne.symm hje
      · exact hj i'

def pathPred {M m : ℕ} (r : Fin M) (q : Fin m → Fin M) (x : Fin M → Bool) : Bool :=
  decide (∃ i : Fin m, x (q i) = true ∧
    ((i.val = 0 ∧ x r = true) ∨
     ∃ j : Fin m, j.val = i.val + 1 ∧ x (q j) = true))

def pathOr {M m : ℕ} (H : (Fin M → Bool) → Bool) (r : Fin M) (q : Fin m → Fin M)
    (x : Fin M → Bool) : Bool :=
  H x || pathPred r q x

theorem pathPred_zero {M : ℕ} (r : Fin M) (q : Fin 0 → Fin M) (x : Fin M → Bool) :
    pathPred r q x = false := by
  simp [pathPred]

theorem pathPred_one {M : ℕ} (r : Fin M) (q : Fin 1 → Fin M) (x : Fin M → Bool) :
    pathPred r q x = (x r && x (q 0)) := by
  apply Bool.eq_iff_iff.2
  simp only [pathPred, decide_eq_true_eq, Bool.and_eq_true]
  constructor
  · rintro ⟨i, hi, ⟨_, hr⟩ | ⟨j, hj, _⟩⟩
    · have : i = 0 := Fin.ext (by omega)
      subst this
      exact ⟨hr, hi⟩
    · omega
  · rintro ⟨hr, hq⟩
    exact ⟨0, hq, Or.inl ⟨rfl, hr⟩⟩

theorem pathPred_all_false {M m : ℕ} (r : Fin M) (q : Fin m → Fin M) (x : Fin M → Bool)
    (hz : ∀ i : Fin m, x (q i) = false) : pathPred r q x = false := by
  simp only [pathPred, decide_eq_false_iff_not]
  rintro ⟨i, hi, _⟩
  rw [hz i] at hi
  cases hi

theorem pathPred_single_false {M m : ℕ} (r : Fin M) (q : Fin m → Fin M) (x : Fin M → Bool)
    (hr : x r = false) (k : Fin m) (honly : ∀ i : Fin m, x (q i) = true → i = k) :
    pathPred r q x = false := by
  simp only [pathPred, decide_eq_false_iff_not]
  rintro ⟨i, hi, ⟨_, hrt⟩ | ⟨j, hji, hj⟩⟩
  · rw [hr] at hrt; cases hrt
  · have e1 := honly i hi
    have e2 := honly j hj
    subst e1; subst e2
    omega

theorem pathPred_update_last_false {M k : ℕ} (r : Fin M) (q : Fin (k + 2) → Fin M)
    (hq_inj : Function.Injective q) (hq_ne : ∀ i, q i ≠ r) (x : Fin M → Bool) :
    pathPred r q (Function.update x (q (Fin.last (k + 1))) false) =
      pathPred r (fun i : Fin (k + 1) => q i.castSucc) x := by
  apply Bool.eq_iff_iff.2
  simp only [pathPred, decide_eq_true_eq]
  have hne_r : r ≠ q (Fin.last (k + 1)) := (hq_ne (Fin.last (k + 1))).symm
  constructor
  · rintro ⟨i, hi, hrest⟩
    have hi_ne : i ≠ Fin.last (k + 1) := by
      intro e; subst e; simp at hi
    have hi_lt : i.val < k + 1 := by
      have := i.isLt
      have : i.val ≠ k + 1 := fun h => hi_ne (Fin.ext h)
      omega
    let i' : Fin (k + 1) := ⟨i.val, hi_lt⟩
    have hi'_eq : i'.castSucc = i := Fin.ext rfl
    rw [Function.update_of_ne (hq_inj.ne hi_ne)] at hi
    refine ⟨i', by rwa [hi'_eq], ?_⟩
    rcases hrest with ⟨hi0, hr⟩ | ⟨j, hji, hj⟩
    · rw [Function.update_of_ne hne_r] at hr
      exact Or.inl ⟨hi0, hr⟩
    · have hj_ne : j ≠ Fin.last (k + 1) := by
        intro e; subst e; simp at hj
      have hj_lt : j.val < k + 1 := by
        have := j.isLt
        have : j.val ≠ k + 1 := fun h => hj_ne (Fin.ext h)
        omega
      let j' : Fin (k + 1) := ⟨j.val, hj_lt⟩
      have hj'_eq : j'.castSucc = j := Fin.ext rfl
      rw [Function.update_of_ne (hq_inj.ne hj_ne)] at hj
      exact Or.inr ⟨j', hji, by rwa [hj'_eq]⟩
  · rintro ⟨i, hi, hrest⟩
    have hi_ne : i.castSucc ≠ Fin.last (k + 1) := Fin.castSucc_ne_last i
    refine ⟨i.castSucc, by rw [Function.update_of_ne (hq_inj.ne hi_ne)]; exact hi, ?_⟩
    rcases hrest with ⟨hi0, hr⟩ | ⟨j, hji, hj⟩
    · exact Or.inl ⟨hi0, by rw [Function.update_of_ne hne_r]; exact hr⟩
    · have hj_ne : j.castSucc ≠ Fin.last (k + 1) := Fin.castSucc_ne_last j
      exact Or.inr ⟨j.castSucc, hji, by rw [Function.update_of_ne (hq_inj.ne hj_ne)]; exact hj⟩

theorem pathPred_update_last_true {M k : ℕ} (r : Fin M) (q : Fin (k + 2) → Fin M)
    (hq_inj : Function.Injective q) (hq_ne : ∀ i, q i ≠ r) (x : Fin M → Bool) :
    pathPred r q (Function.update x (q (Fin.last (k + 1))) true) =
      (pathPred r (fun i : Fin k => q i.castSucc.castSucc) x || x (q (Fin.last k).castSucc)) := by
  apply Bool.eq_iff_iff.2
  simp only [pathPred, Bool.or_eq_true, decide_eq_true_eq]
  have hne_r : r ≠ q (Fin.last (k + 1)) := (hq_ne (Fin.last (k + 1))).symm
  have hne_p : (Fin.last k).castSucc ≠ Fin.last (k + 1) := Fin.castSucc_ne_last _
  constructor
  · rintro ⟨i, hi, ⟨hi0, hr⟩ | ⟨j, hji, hj⟩⟩
    · have hi_lt : i.val < k + 1 := by omega
      have hi_ne : i ≠ Fin.last (k + 1) := by intro e; rw [e] at hi0; simp at hi0
      rw [Function.update_of_ne (hq_inj.ne hi_ne)] at hi
      rw [Function.update_of_ne hne_r] at hr
      by_cases hk : i.val = k
      · right
        have e : i = (Fin.last k).castSucc := Fin.ext (by simp [hk])
        rwa [e] at hi
      · left
        let i' : Fin k := ⟨i.val, by omega⟩
        have e : i'.castSucc.castSucc = i := Fin.ext rfl
        exact ⟨i', by rwa [e], Or.inl ⟨hi0, hr⟩⟩
    · have hi_lt : i.val < k + 1 := by have := j.isLt; omega
      have hi_ne : i ≠ Fin.last (k + 1) := fun e => by have := congrArg Fin.val e; simp at this; omega
      rw [Function.update_of_ne (hq_inj.ne hi_ne)] at hi
      by_cases hjk : j.val = k + 1
      · right
        have e : i = (Fin.last k).castSucc := Fin.ext (by simp; omega)
        rwa [e] at hi
      · have hj_ne : j ≠ Fin.last (k + 1) := fun e => hjk (congrArg Fin.val e)
        rw [Function.update_of_ne (hq_inj.ne hj_ne)] at hj
        by_cases hjk2 : j.val = k
        · right
          have e : j = (Fin.last k).castSucc := Fin.ext hjk2
          rwa [e] at hj
        · left
          let i' : Fin k := ⟨i.val, by omega⟩
          let j' : Fin k := ⟨j.val, by omega⟩
          have ei : i'.castSucc.castSucc = i := Fin.ext rfl
          have ej : j'.castSucc.castSucc = j := Fin.ext rfl
          exact ⟨i', by rwa [ei], Or.inr ⟨j', hji, by rwa [ej]⟩⟩
  · rintro (⟨i, hi, ⟨hi0, hr⟩ | ⟨j, hji, hj⟩⟩ | hp)
    · have hi_ne : i.castSucc.castSucc ≠ Fin.last (k + 1) := Fin.castSucc_ne_last _
      refine ⟨i.castSucc.castSucc, by rw [Function.update_of_ne (hq_inj.ne hi_ne)]; exact hi,
        Or.inl ⟨hi0, by rw [Function.update_of_ne hne_r]; exact hr⟩⟩
    · have hi_ne : i.castSucc.castSucc ≠ Fin.last (k + 1) := Fin.castSucc_ne_last _
      have hj_ne : j.castSucc.castSucc ≠ Fin.last (k + 1) := Fin.castSucc_ne_last _
      refine ⟨i.castSucc.castSucc, by rw [Function.update_of_ne (hq_inj.ne hi_ne)]; exact hi,
        Or.inr ⟨j.castSucc.castSucc, hji, by rw [Function.update_of_ne (hq_inj.ne hj_ne)]; exact hj⟩⟩
    · refine ⟨(Fin.last k).castSucc, by rw [Function.update_of_ne (hq_inj.ne hne_p)]; exact hp,
        Or.inr ⟨Fin.last (k + 1), by simp, by simp⟩⟩

theorem peel_step {M k s : ℕ} (H : (Fin M → Bool) → Bool) (r : Fin M) (q : Fin (k + 2) → Fin M)
    (hH_ind : ∀ (i : Fin (k + 2)) (x : Fin M → Bool) (b : Bool), H (Function.update x (q i) b) = H x)
    (hH_true : ∃ x : Fin M → Bool, H x = true)
    (hH_false_r0 : ∃ x : Fin M → Bool, H x = false ∧ x r = false)
    (hq_inj : Function.Injective q) (hq_ne : ∀ i, q i ≠ r)
    (hc : HasCircuitSize M (pathOr H r q) s) :
    (∃ s' : ℕ, s' + 2 ≤ s ∧ HasCircuitSize M (pathOr H r (fun i : Fin (k + 1) => q i.castSucc)) s') ∨
    (∃ s' : ℕ, s' + 3 ≤ s ∧ HasCircuitSize M (pathOr H r (fun i : Fin k => q i.castSucc.castSucc)) s') := by
  classical
  let ℓ := q (Fin.last (k + 1))
  let p := q (Fin.last k).castSucc
  let q1 : Fin (k + 1) → Fin M := fun i => q i.castSucc
  let q2 : Fin k → Fin M := fun i => q i.castSucc.castSucc
  have heq0 : (fun x => pathOr H r q (Function.update x ℓ false)) = pathOr H r q1 := by
    funext x
    simp only [pathOr, ℓ, q1, hH_ind, pathPred_update_last_false r q hq_inj hq_ne]
  have heq1 : (fun x => pathOr H r q (Function.update x ℓ true)) =
      fun x => pathOr H r q2 x || x p := by
    funext x
    simp only [pathOr, ℓ, p, q2, hH_ind, pathPred_update_last_true r q hq_inj hq_ne, Bool.or_assoc]
  obtain ⟨x0, hx0F, hx0r⟩ := hH_false_r0
  obtain ⟨yT, hyT⟩ := hH_true
  let z0 : Fin M → Bool := fun j => if ∃ i : Fin (k + 2), q i = j then false else x0 j
  have hz0H : H z0 = false := by
    rw [← hx0F]
    exact eq_of_indep H q hH_ind z0 x0 (fun j hj => by
      have : ¬ ∃ i : Fin (k + 2), q i = j := fun ⟨i, hi⟩ => hj i hi
      simp [z0, this])
  have hz0r : z0 r = false := by
    have : ¬ ∃ i : Fin (k + 2), q i = r := fun ⟨i, hi⟩ => hq_ne i hi
    simp [z0, this, hx0r]
  have hz0q : ∀ i : Fin (k + 2), z0 (q i) = false := by
    intro i; simp [z0]
  have hdep_l : Dep (pathOr H r q) ℓ := by
    apply dep_of_ft
    let w := Function.update z0 p true
    refine ⟨w, ?_⟩
    have hw0 : pathOr H r q (Function.update w ℓ false) = false := by
      have hne_lp : ℓ ≠ p := hq_inj.ne (Fin.castSucc_ne_last _).symm
      rw [pathOr, hH_ind, hH_ind, hz0H, Bool.false_or]
      apply pathPred_single_false r q _ (by
        simp only [w]
        rw [Function.update_of_ne (hq_ne _).symm, Function.update_of_ne (hq_ne _).symm, hz0r])
        (Fin.last k).castSucc
      intro i hi
      by_cases hil : i = Fin.last (k + 1)
      · subst hil; simp [ℓ] at hi
      · rw [Function.update_of_ne (hq_inj.ne hil)] at hi
        by_cases hip : i = (Fin.last k).castSucc
        · exact hip
        · simp only [w] at hi
          rw [Function.update_of_ne (hq_inj.ne hip), hz0q i] at hi
          cases hi
    have hw1 : pathOr H r q (Function.update w ℓ true) = true := by
      rw [congrFun heq1 w]
      simp [w]
    rw [hw0, hw1]; decide
  have hnc_l : ∀ b : Bool, ∃ x y : Fin M → Bool,
      pathOr H r q (Function.update x ℓ b) ≠ pathOr H r q (Function.update y ℓ b) := by
    intro b
    cases b
    · refine ⟨z0, yT, ?_⟩
      rw [congrFun heq0 z0, congrFun heq0 yT]
      have h1 : pathOr H r q1 z0 = false := by
        rw [pathOr, hz0H, pathPred_all_false r q1 z0 (fun i => hz0q i.castSucc)]; rfl
      have h2 : pathOr H r q1 yT = true := by rw [pathOr, hyT]; rfl
      rw [h1, h2]; decide
    · refine ⟨z0, yT, ?_⟩
      rw [congrFun heq1 z0, congrFun heq1 yT]
      have h1 : (pathOr H r q2 z0 || z0 p) = false := by
        rw [pathOr, hz0H, pathPred_all_false r q2 z0 (fun i => hz0q i.castSucc.castSucc),
          hz0q (Fin.last k).castSucc]; rfl
      have h2 : (pathOr H r q2 yT || yT p) = true := by rw [pathOr, hyT]; rfl
      rw [h1, h2]; decide
  rcases drop2_var ℓ hdep_l hnc_l hc with ⟨s1, hs1, hc1⟩ | ⟨s1, hs1, hc1⟩
  · rw [heq0] at hc1
    exact Or.inl ⟨s1, hs1, hc1⟩
  · rw [heq1] at hc1
    let F1 : (Fin M → Bool) → Bool := fun x => pathOr H r q2 x || x p
    have hF1_eq : (fun x => F1 (Function.update x p false)) = pathOr H r q2 := by
      funext x
      have hqp : ∀ i : Fin k, q2 i ≠ p := fun i =>
        hq_inj.ne (fun e => by have := congrArg Fin.val e; simp at this; omega)
      have hpr : r ≠ p := (hq_ne _).symm
      have hpred : pathPred r q2 (Function.update x p false) = pathPred r q2 x := by
        simp only [pathPred]
        congr 1
        apply propext
        constructor
        · rintro ⟨i, hi, ⟨hi0, hr⟩ | ⟨j, hji, hj⟩⟩
          · rw [Function.update_of_ne (hqp i)] at hi
            rw [Function.update_of_ne hpr] at hr
            exact ⟨i, hi, Or.inl ⟨hi0, hr⟩⟩
          · rw [Function.update_of_ne (hqp i)] at hi
            rw [Function.update_of_ne (hqp j)] at hj
            exact ⟨i, hi, Or.inr ⟨j, hji, hj⟩⟩
        · rintro ⟨i, hi, ⟨hi0, hr⟩ | ⟨j, hji, hj⟩⟩
          · exact ⟨i, by rw [Function.update_of_ne (hqp i)]; exact hi,
              Or.inl ⟨hi0, by rw [Function.update_of_ne hpr]; exact hr⟩⟩
          · exact ⟨i, by rw [Function.update_of_ne (hqp i)]; exact hi,
              Or.inr ⟨j, hji, by rw [Function.update_of_ne (hqp j)]; exact hj⟩⟩
      simp only [F1, pathOr, p, hH_ind, hpred, Function.update_self, Bool.or_false]
    have hdep_p : Dep F1 p := by
      apply dep_of_ft
      refine ⟨z0, ?_⟩
      rw [congrFun hF1_eq z0]
      have h0 : pathOr H r q2 z0 = false := by
        rw [pathOr, hz0H, pathPred_all_false r q2 z0 (fun i => hz0q i.castSucc.castSucc)]; rfl
      have h1 : F1 (Function.update z0 p true) = true := by simp [F1]
      rw [h0, h1]; decide
    have hnc_p : ∃ x y : Fin M → Bool,
        F1 (Function.update x p false) ≠ F1 (Function.update y p false) := by
      refine ⟨z0, yT, ?_⟩
      rw [congrFun hF1_eq z0, congrFun hF1_eq yT]
      have h0 : pathOr H r q2 z0 = false := by
        rw [pathOr, hz0H, pathPred_all_false r q2 z0 (fun i => hz0q i.castSucc.castSucc)]; rfl
      have h1 : pathOr H r q2 yT = true := by rw [pathOr, hyT]; rfl
      rw [h0, h1]; decide
    obtain ⟨s2, hs2, hc2⟩ := drop1_var p false hdep_p hnc_p hc1
    rw [hF1_eq] at hc2
    exact Or.inr ⟨s2, by omega, hc2⟩

theorem peel_to_zero {M : ℕ} (H : (Fin M → Bool) → Bool) (r : Fin M)
    (hH_true : ∃ x : Fin M → Bool, H x = true)
    (hH_false_r0 : ∃ x : Fin M → Bool, H x = false ∧ x r = false)
    (hH_false_r1 : ∃ x : Fin M → Bool, H x = false ∧ x r = true) :
    ∀ (m : ℕ) (q : Fin m → Fin M),
      (∀ (i : Fin m) (x : Fin M → Bool) (b : Bool), H (Function.update x (q i) b) = H x) →
      Function.Injective q → (∀ i, q i ≠ r) →
      ∀ s : ℕ, HasCircuitSize M (pathOr H r q) s →
        ∃ s' : ℕ, (3 * m) / 2 + s' ≤ s ∧ HasCircuitSize M H s' := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro q hH_ind hq_inj hq_ne s hc
    match m with
    | 0 =>
      have e : pathOr H r q = H := by
        funext x; simp [pathOr, pathPred_zero]
      rw [e] at hc
      exact ⟨s, by omega, hc⟩
    | 1 =>
      have e0 : (fun x => pathOr H r q (Function.update x (q 0) false)) = H := by
        funext x
        simp only [pathOr, pathPred_one, hH_ind, Function.update_self, Bool.and_false, Bool.or_false]
      obtain ⟨x1, hx1F, hx1r⟩ := hH_false_r1
      obtain ⟨yT, hyT⟩ := hH_true
      have hdep : Dep (pathOr H r q) (q 0) := by
        apply dep_of_ft
        refine ⟨x1, ?_⟩
        rw [congrFun e0 x1, hx1F]
        simp [pathOr, pathPred_one, Function.update_of_ne (hq_ne 0).symm, hx1r]
      have hnc : ∃ x y : Fin M → Bool,
          pathOr H r q (Function.update x (q 0) false) ≠
            pathOr H r q (Function.update y (q 0) false) := by
        refine ⟨x1, yT, ?_⟩
        rw [congrFun e0 x1, congrFun e0 yT, hx1F, hyT]; decide
      obtain ⟨s', hs', hc'⟩ := drop1_var (q 0) false hdep hnc hc
      rw [e0] at hc'
      exact ⟨s', by omega, hc'⟩
    | k + 2 =>
      rcases peel_step H r q hH_ind hH_true hH_false_r0 hq_inj hq_ne hc with
          ⟨s1, hs1, hc1⟩ | ⟨s1, hs1, hc1⟩
      · obtain ⟨s', hs', hc'⟩ := ih (k + 1) (by omega) (fun i => q i.castSucc)
          (fun i => hH_ind i.castSucc) (hq_inj.comp (Fin.castSucc_injective _))
          (fun i => hq_ne i.castSucc) s1 hc1
        exact ⟨s', by omega, hc'⟩
      · obtain ⟨s', hs', hc'⟩ := ih k (by omega) (fun i => q i.castSucc.castSucc)
          (fun i => hH_ind i.castSucc.castSucc)
          (hq_inj.comp ((Fin.castSucc_injective _).comp (Fin.castSucc_injective _)))
          (fun i => hq_ne i.castSucc.castSucc) s1 hc1
        exact ⟨s', by omega, hc'⟩

theorem peel_to_one {M : ℕ} (H : (Fin M → Bool) → Bool) (r : Fin M)
    (hH_true : ∃ x : Fin M → Bool, H x = true)
    (hH_false_r0 : ∃ x : Fin M → Bool, H x = false ∧ x r = false) :
    ∀ (m : ℕ) (hm : 1 ≤ m) (q : Fin m → Fin M),
      (∀ (i : Fin m) (x : Fin M → Bool) (b : Bool), H (Function.update x (q i) b) = H x) →
      Function.Injective q → (∀ i, q i ≠ r) →
      ∀ s : ℕ, HasCircuitSize M (pathOr H r q) s →
        ∃ s' : ℕ, (3 * (m - 1)) / 2 + s' ≤ s ∧
          HasCircuitSize M (fun x => H x || (x r && x (q ⟨0, by omega⟩))) s' := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm q hH_ind hq_inj hq_ne s hc
    match m with
    | 0 => omega
    | 1 =>
      have e : pathOr H r q = fun x => H x || (x r && x (q ⟨0, by omega⟩)) := by
        funext x; simp [pathOr, pathPred_one]
      rw [e] at hc
      exact ⟨s, by omega, hc⟩
    | 2 =>
      rcases peel_step H r q hH_ind hH_true hH_false_r0 hq_inj hq_ne hc with
          ⟨s1, hs1, hc1⟩ | ⟨s1, hs1, hc1⟩
      · have e : pathOr H r (fun i : Fin 1 => q i.castSucc) =
            fun x => H x || (x r && x (q ⟨0, by omega⟩)) := by
          funext x; simp [pathOr, pathPred_one]
        rw [e] at hc1
        exact ⟨s1, by omega, hc1⟩
      · have e : pathOr H r (fun i : Fin 0 => q i.castSucc.castSucc) = H := by
          funext x; simp [pathOr, pathPred_zero]
        rw [e] at hc1
        exact ⟨s1 + 2, by omega, add_pendant H r (q ⟨0, by omega⟩) hH_true hc1⟩
    | k + 3 =>
      rcases peel_step H r q hH_ind hH_true hH_false_r0 hq_inj hq_ne hc with
          ⟨s1, hs1, hc1⟩ | ⟨s1, hs1, hc1⟩
      · obtain ⟨s', hs', hc'⟩ := ih (k + 2) (by omega) (by omega) (fun i => q i.castSucc)
          (fun i => hH_ind i.castSucc) (hq_inj.comp (Fin.castSucc_injective _))
          (fun i => hq_ne i.castSucc) s1 hc1
        exact ⟨s', by omega, hc'⟩
      · obtain ⟨s', hs', hc'⟩ := ih (k + 1) (by omega) (by omega) (fun i => q i.castSucc.castSucc)
          (fun i => hH_ind i.castSucc.castSucc)
          (hq_inj.comp ((Fin.castSucc_injective _).comp (Fin.castSucc_injective _)))
          (fun i => hq_ne i.castSucc.castSucc) s1 hc1
        exact ⟨s', by omega, hc'⟩

def fullPath (N h : ℕ) (u v : Fin N) (g : (Fin N → Bool) → Bool)
    (x : Fin (N + 2 * h) → Bool) : Bool :=
  g (fun i : Fin N => x (Fin.castAdd (2 * h) i)) ||
    decide (∃ i : Fin (2 * h), x (Fin.natAdd N i) = true ∧
      ((i.val = 0 ∧ x (Fin.castAdd (2 * h) u) = true) ∨
       (i.val + 1 = 2 * h ∧ x (Fin.castAdd (2 * h) v) = true) ∨
       ∃ j : Fin (2 * h), j.val = i.val + 1 ∧ x (Fin.natAdd N j) = true))

def interiorD (N h : ℕ) : Finset (Fin (N + 2 * h)) :=
  Finset.univ.filter fun p => N + 1 ≤ p.val ∧ p.val + 1 < N + 2 * h

theorem mem_interiorD {N h : ℕ} {p : Fin (N + 2 * h)} :
    p ∈ interiorD N h ↔ ∃ i : Fin (2 * h), p = Fin.natAdd N i ∧ 1 ≤ i.val ∧ i.val + 1 < 2 * h := by
  simp only [interiorD, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro ⟨h1, h2⟩
    refine ⟨⟨p.val - N, by omega⟩, Fin.ext ?_, by simp; omega, by simp; omega⟩
    simp [Fin.natAdd]; omega
  · rintro ⟨i, rfl, h1, h2⟩
    simp [Fin.natAdd]; omega

theorem castAdd_not_mem_interiorD {N h : ℕ} (i : Fin N) :
    Fin.castAdd (2 * h) i ∉ interiorD N h := by
  simp only [interiorD, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castAdd]
  have := i.isLt
  omega

theorem natAdd_zero_not_mem_interiorD {N h : ℕ} (hh : 0 < 2 * h) :
    Fin.natAdd N ⟨0, hh⟩ ∉ interiorD N h := by
  simp [interiorD, Fin.natAdd]

theorem natAdd_last_not_mem_interiorD {N h : ℕ} (hh : 0 < 2 * h) :
    Fin.natAdd N ⟨2 * h - 1, by omega⟩ ∉ interiorD N h := by
  simp [interiorD, Fin.natAdd]; omega

theorem fullPath_false_single {N h : ℕ} {u v : Fin N} {g : (Fin N → Bool) → Bool}
    (hg0 : g (fun _ : Fin N => false) = false) (k : Fin (2 * h)) :
    fullPath N h u v g (fun p => decide (p = Fin.natAdd N k)) = false := by
  unfold fullPath
  have hbase : (fun i : Fin N => decide (Fin.castAdd (2 * h) i = Fin.natAdd N k)) =
      fun _ => false := by
    funext i
    simp only [decide_eq_false_iff_not]
    intro e
    have := congrArg Fin.val e
    simp [Fin.castAdd, Fin.natAdd] at this
    omega
  rw [hbase, hg0, Bool.false_or, decide_eq_false_iff_not]
  rintro ⟨i, hi, ⟨_, hu⟩ | ⟨_, hv⟩ | ⟨j, hji, hj⟩⟩
  · have := congrArg Fin.val (of_decide_eq_true hu)
    simp [Fin.castAdd, Fin.natAdd] at this
    omega
  · have := congrArg Fin.val (of_decide_eq_true hv)
    simp [Fin.castAdd, Fin.natAdd] at this
    omega
  · have ei := Fin.natAdd_injective (2 * h) N (of_decide_eq_true hi)
    have ej := Fin.natAdd_injective (2 * h) N (of_decide_eq_true hj)
    subst ei; subst ej
    omega

theorem fullPath_false_pair {N h : ℕ} {u v : Fin N} {g : (Fin N → Bool) → Bool}
    (hg0 : g (fun _ : Fin N => false) = false) (k1 k2 : Fin (2 * h))
    (h1 : k1.val + 1 ≠ k2.val) (h2 : k2.val + 1 ≠ k1.val) :
    fullPath N h u v g (fun p => decide (p = Fin.natAdd N k1 ∨ p = Fin.natAdd N k2)) = false := by
  unfold fullPath
  have hbase : (fun i : Fin N =>
      decide (Fin.castAdd (2 * h) i = Fin.natAdd N k1 ∨
        Fin.castAdd (2 * h) i = Fin.natAdd N k2)) = fun _ => false := by
    funext i
    simp only [decide_eq_false_iff_not, not_or]
    constructor <;> (intro e; have := congrArg Fin.val e; simp [Fin.castAdd, Fin.natAdd] at this; omega)
  rw [hbase, hg0, Bool.false_or, decide_eq_false_iff_not]
  rintro ⟨i, hi, ⟨_, hu⟩ | ⟨_, hv⟩ | ⟨j, hji, hj⟩⟩
  · rcases of_decide_eq_true hu with e | e <;>
      (have := congrArg Fin.val e; simp [Fin.castAdd, Fin.natAdd] at this; omega)
  · rcases of_decide_eq_true hv with e | e <;>
      (have := congrArg Fin.val e; simp [Fin.castAdd, Fin.natAdd] at this; omega)
  · rcases of_decide_eq_true hi with ei | ei <;> rcases of_decide_eq_true hj with ej | ej
    · have e1 := Fin.natAdd_injective (2 * h) N ei
      have e2 := Fin.natAdd_injective (2 * h) N ej
      subst e1; subst e2; omega
    · have e1 := Fin.natAdd_injective (2 * h) N ei
      have e2 := Fin.natAdd_injective (2 * h) N ej
      subst e1; subst e2; omega
    · have e1 := Fin.natAdd_injective (2 * h) N ei
      have e2 := Fin.natAdd_injective (2 * h) N ej
      subst e1; subst e2; omega
    · have e1 := Fin.natAdd_injective (2 * h) N ei
      have e2 := Fin.natAdd_injective (2 * h) N ej
      subst e1; subst e2; omega

theorem fullPath_edge_true {N h : ℕ} {u v : Fin N} {g : (Fin N → Bool) → Bool}
    (x : Fin (N + 2 * h) → Bool) (i j : Fin (2 * h)) (hji : j.val = i.val + 1)
    (hi : x (Fin.natAdd N i) = true) (hj : x (Fin.natAdd N j) = true) :
    fullPath N h u v g x = true := by
  unfold fullPath
  rw [Bool.or_eq_true, decide_eq_true_eq]
  exact Or.inr ⟨i, hi, Or.inr (Or.inr ⟨j, hji, hj⟩)⟩

theorem fullPath_deepHyp (N h : ℕ) (u v : Fin N) (g : (Fin N → Bool) → Bool)
    (hh : 3 ≤ h) (hnc : ∃ y y' : Fin N → Bool, g y ≠ g y')
    (hg0 : g (fun _ : Fin N => false) = false) :
    DeepHyp (fullPath N h u v g) (interiorD N h) := by
  have hzT : ∃ zT : Fin N → Bool, g zT = true := by
    obtain ⟨y, y', hne⟩ := hnc
    cases hy : g y
    · cases hy' : g y'
      · exact absurd (hy.trans hy'.symm) hne
      · exact ⟨y', hy'⟩
    · exact ⟨y, hy⟩
  obtain ⟨zT, hzT⟩ := hzT
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro y hy b
    obtain ⟨k, rfl, hk1, hk2⟩ := mem_interiorD.1 hy
    let xF : Fin (N + 2 * h) → Bool := fun _ => false
    let xT : Fin (N + 2 * h) → Bool := fun p =>
      if hlt : p.val < N then zT ⟨p.val, hlt⟩ else false
    refine ⟨xF, xT, ?_⟩
    have hT : fullPath N h u v g (Function.update xT (Fin.natAdd N k) b) = true := by
      unfold fullPath
      have hb : (fun i : Fin N =>
          Function.update xT (Fin.natAdd N k) b (Fin.castAdd (2 * h) i)) = zT := by
        funext i
        have hne : Fin.castAdd (2 * h) i ≠ Fin.natAdd N k := by
          intro e; have := congrArg Fin.val e; simp [Fin.castAdd, Fin.natAdd] at this; omega
        rw [Function.update_of_ne hne]
        simp [xT, i.isLt]
      rw [hb, hzT]; rfl
    have hF : fullPath N h u v g (Function.update xF (Fin.natAdd N k) b) = false := by
      cases b
      · have e : Function.update xF (Fin.natAdd N k) false = fun _ => false := by
          funext p; by_cases hp : p = Fin.natAdd N k <;> simp [xF, hp]
        rw [e]
        simp [fullPath, hg0]
      · have e : Function.update xF (Fin.natAdd N k) true =
            fun p => decide (p = Fin.natAdd N k) := by
          funext p; by_cases hp : p = Fin.natAdd N k <;> simp [xF, hp]
        rw [e]
        exact fullPath_false_single hg0 k
    rw [hF, hT]; decide
  · intro y hy y' hy' hne
    obtain ⟨k, rfl, hk1, hk2⟩ := mem_interiorD.1 hy
    obtain ⟨k', rfl, hk1', hk2'⟩ := mem_interiorD.1 hy'
    have hkne : k ≠ k' := fun e => hne (congrArg _ e)
    have hvalne : k.val ≠ k'.val := fun e => hkne (Fin.ext e)
    have sep0010 : ∀ (i j : Fin (2 * h)), 1 ≤ i.val → i.val + 1 < 2 * h → i.val ≠ j.val →
        ∃ x : Fin (N + 2 * h) → Bool,
          fullPath N h u v g (set2 x (Fin.natAdd N i) false (Fin.natAdd N j) false) = false ∧
          fullPath N h u v g (set2 x (Fin.natAdd N i) true (Fin.natAdd N j) false) = true := by
      intro i j hi1 hi2 hij
      let w : Fin (2 * h) :=
        if i.val + 1 = j.val then ⟨i.val - 1, by omega⟩ else ⟨i.val + 1, by omega⟩
      have hw_ne_i : w ≠ i := by
        intro e
        have := congrArg Fin.val e
        by_cases h1 : i.val + 1 = j.val
        · simp [w, h1] at this; omega
        · simp [w, h1] at this
      have hw_ne_j : w ≠ j := by
        intro e
        have := congrArg Fin.val e
        by_cases h1 : i.val + 1 = j.val
        · simp [w, h1] at this; omega
        · simp [w, h1] at this
      have hni : Fin.natAdd N i ≠ Fin.natAdd N j := fun e => hij (congrArg Fin.val (Fin.natAdd_injective (2 * h) N e))
      let x : Fin (N + 2 * h) → Bool := fun p => decide (p = Fin.natAdd N w)
      refine ⟨x, ?_, ?_⟩
      · have e : set2 x (Fin.natAdd N i) false (Fin.natAdd N j) false =
            fun p => decide (p = Fin.natAdd N w) := by
          funext p
          by_cases hp1 : p = Fin.natAdd N i
          · subst hp1
            rw [set2_p x hni]
            simp [hw_ne_i.symm]
          · by_cases hp2 : p = Fin.natAdd N j
            · subst hp2
              rw [set2_q]
              simp [hw_ne_j.symm]
            · rw [set2_o x _ _ _ _ p hp1 hp2]
        rw [e]
        exact fullPath_false_single hg0 w
      · have hti : set2 x (Fin.natAdd N i) true (Fin.natAdd N j) false (Fin.natAdd N i) = true :=
          set2_p x hni true false
        have htw : set2 x (Fin.natAdd N i) true (Fin.natAdd N j) false (Fin.natAdd N w) = true := by
          rw [set2_o x _ _ _ _ _ (fun e => hw_ne_i (Fin.natAdd_injective (2 * h) N e))
            (fun e => hw_ne_j (Fin.natAdd_injective (2 * h) N e))]
          simp [x]
        by_cases h1 : i.val + 1 = j.val
        · exact fullPath_edge_true _ w i (by simp [w, h1]; omega) htw hti
        · exact fullPath_edge_true _ i w (by simp [w, h1]) hti htw
    have sep1011 : ∃ x : Fin (N + 2 * h) → Bool,
        fullPath N h u v g (set2 x (Fin.natAdd N k) true (Fin.natAdd N k') false) = false ∧
        fullPath N h u v g (set2 x (Fin.natAdd N k) true (Fin.natAdd N k') true) = true := by
      by_cases hadj : k.val + 1 = k'.val ∨ k'.val + 1 = k.val
      · let x : Fin (N + 2 * h) → Bool := fun _ => false
        refine ⟨x, ?_, ?_⟩
        · have e : set2 x (Fin.natAdd N k) true (Fin.natAdd N k') false =
              fun p => decide (p = Fin.natAdd N k) := by
            funext p
            by_cases hp1 : p = Fin.natAdd N k
            · subst hp1; rw [set2_p x hne]; simp
            · by_cases hp2 : p = Fin.natAdd N k'
              · subst hp2; rw [set2_q]; simp [hne.symm]
              · rw [set2_o x _ _ _ _ p hp1 hp2]; simp [x, hp1]
          rw [e]
          exact fullPath_false_single hg0 k
        · rcases hadj with h1 | h1
          · exact fullPath_edge_true _ k k' h1.symm (set2_p x hne true true) (set2_q x _ _ true true)
          · exact fullPath_edge_true _ k' k h1.symm (set2_q x _ _ true true) (set2_p x hne true true)
      · push Not at hadj
        let w : Fin (2 * h) :=
          if k.val = k'.val + 2 then ⟨k'.val - 1, by omega⟩ else ⟨k'.val + 1, by omega⟩
        have hw_ne_k : w ≠ k := by
          intro e; have := congrArg Fin.val e
          by_cases h1 : k.val = k'.val + 2 <;> simp [w, h1] at this <;> omega
        have hw_ne_k' : w ≠ k' := by
          intro e; have := congrArg Fin.val e
          by_cases h1 : k.val = k'.val + 2
          · simp [w, h1] at this; omega
          · simp [w, h1] at this
        have hwa1 : k.val + 1 ≠ w.val := by
          by_cases h1 : k.val = k'.val + 2 <;> simp [w, h1] <;> omega
        have hwa2 : w.val + 1 ≠ k.val := by
          by_cases h1 : k.val = k'.val + 2
          · simp [w, h1]
          · simp [w, h1]; omega
        let x : Fin (N + 2 * h) → Bool := fun p => decide (p = Fin.natAdd N w)
        refine ⟨x, ?_, ?_⟩
        · have e : set2 x (Fin.natAdd N k) true (Fin.natAdd N k') false =
              fun p => decide (p = Fin.natAdd N k ∨ p = Fin.natAdd N w) := by
            funext p
            by_cases hp1 : p = Fin.natAdd N k
            · subst hp1; rw [set2_p x hne]; simp
            · by_cases hp2 : p = Fin.natAdd N k'
              · subst hp2; rw [set2_q]
                have h1 : Fin.natAdd N k' ≠ Fin.natAdd N k := hne.symm
                have h2 : Fin.natAdd N k' ≠ Fin.natAdd N w :=
                  fun e => hw_ne_k' (Fin.natAdd_injective (2 * h) N e).symm
                simp [h1, h2]
              · rw [set2_o x _ _ _ _ p hp1 hp2]
                simp [x, hp1]
          rw [e]
          exact fullPath_false_pair hg0 k w hwa1 hwa2
        · have htk' : set2 x (Fin.natAdd N k) true (Fin.natAdd N k') true (Fin.natAdd N k') = true :=
            set2_q x _ _ true true
          have htw : set2 x (Fin.natAdd N k) true (Fin.natAdd N k') true (Fin.natAdd N w) = true := by
            rw [set2_o x _ _ _ _ _ (fun e => hw_ne_k (Fin.natAdd_injective (2 * h) N e))
              (fun e => hw_ne_k' (Fin.natAdd_injective (2 * h) N e))]
            simp [x]
          by_cases h1 : k.val = k'.val + 2
          · exact fullPath_edge_true _ w k' (by simp [w, h1]; omega) htw htk'
          · exact fullPath_edge_true _ k' w (by simp [w, h1]) htk' htw
    rintro ⟨a, b, hab⟩
    cases a <;> cases b
    · obtain ⟨x, hx0, hx1⟩ := sep1011
      have h := (hab x).1.trans (hab x).2
      simp only [Bool.not_false] at h
      rw [hx0, hx1] at h
      cases h
    · obtain ⟨x, hx0, hx1⟩ := sep0010 k k' hk1 hk2 hvalne
      have h := (hab x).1
      simp only [Bool.not_false, Bool.not_true] at h
      have h2 := (hab x).2
      simp only [Bool.not_false, Bool.not_true] at h2
      rw [hx1, hx0] at h2
      cases h2
    · obtain ⟨x, hx0, hx1⟩ := sep0010 k' k hk1' hk2' (Ne.symm hvalne)
      have h1 := (hab x).1
      have h2 := (hab x).2
      simp only [Bool.not_false, Bool.not_true] at h1 h2
      have hsw0 : set2 x (Fin.natAdd N k) false (Fin.natAdd N k') false =
          set2 x (Fin.natAdd N k') false (Fin.natAdd N k) false := by
        funext p
        by_cases hp1 : p = Fin.natAdd N k
        · subst hp1; rw [set2_p x hne, set2_q]
        · by_cases hp2 : p = Fin.natAdd N k'
          · subst hp2; rw [set2_q, set2_p x hne.symm]
          · rw [set2_o x _ _ _ _ p hp1 hp2, set2_o x _ _ _ _ p hp2 hp1]
      have hsw1 : set2 x (Fin.natAdd N k) false (Fin.natAdd N k') true =
          set2 x (Fin.natAdd N k') true (Fin.natAdd N k) false := by
        funext p
        by_cases hp1 : p = Fin.natAdd N k
        · subst hp1; rw [set2_p x hne, set2_q]
        · by_cases hp2 : p = Fin.natAdd N k'
          · subst hp2; rw [set2_q, set2_p x hne.symm]
          · rw [set2_o x _ _ _ _ p hp1 hp2, set2_o x _ _ _ _ p hp2 hp1]
      have h12 : fullPath N h u v g (set2 x (Fin.natAdd N k) false (Fin.natAdd N k') false) =
          fullPath N h u v g (set2 x (Fin.natAdd N k) false (Fin.natAdd N k') true) :=
        h1.trans h2
      rw [hsw0, hsw1, hx0, hx1] at h12
      cases h12
    · obtain ⟨x, hx0, hx1⟩ := sep0010 k k' hk1 hk2 hvalne
      have h := (hab x).2
      simp only [Bool.not_true] at h
      rw [hx1, hx0] at h
      cases h
  · intro y hy x hz0
    obtain ⟨k, rfl, hk1, hk2⟩ := mem_interiorD.1 hy
    let w : Fin (2 * h) :=
      if k.val ≤ 2 then ⟨k.val + 1, by omega⟩ else ⟨k.val - 1, by omega⟩
    have hw_lo : 2 ≤ w.val := by by_cases h1 : k.val ≤ 2 <;> simp [w, h1] <;> omega
    have hw_hi : w.val + 2 < 2 * h := by by_cases h1 : k.val ≤ 2 <;> simp [w, h1] <;> omega
    have hw_mem : Fin.natAdd N w ∈ interiorD N h :=
      mem_interiorD.2 ⟨w, rfl, by omega, by omega⟩
    have hw_ne_k : w ≠ k := by
      intro e; have := congrArg Fin.val e
      by_cases h1 : k.val ≤ 2
      · simp [w, h1] at this
      · simp [w, h1] at this; omega
    let x' : Fin (N + 2 * h) → Bool := Function.update (zeroOn (interiorD N h) x) (Fin.natAdd N w) true
    refine ⟨x', ?_, ?_, ?_, ?_⟩
    · intro p hp
      have hne_w : p ≠ Fin.natAdd N w := fun e => hp (e ▸ hw_mem)
      simp [x', Function.update_of_ne hne_w, zeroOn, hp]
    · have hne_kw : Fin.natAdd N k ≠ Fin.natAdd N w := fun e => hw_ne_k (Fin.natAdd_injective (2 * h) N e).symm
      simp [x', Function.update_of_ne hne_kw, zeroOn, hy]
    · unfold fullPath at hz0 ⊢
      rw [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hz0 ⊢
      obtain ⟨hgx, hno⟩ := hz0
      have hbase : (fun i : Fin N => x' (Fin.castAdd (2 * h) i)) =
          fun i : Fin N => zeroOn (interiorD N h) x (Fin.castAdd (2 * h) i) := by
        funext i
        have hne_w : Fin.castAdd (2 * h) i ≠ Fin.natAdd N w := by
          intro e; have := congrArg Fin.val e; simp [Fin.castAdd, Fin.natAdd] at this; omega
        simp [x', Function.update_of_ne hne_w]
      refine ⟨by rw [hbase]; exact hgx, ?_⟩
      rintro ⟨i, hi, hrest⟩
      by_cases hiw : i = w
      · subst hiw
        rcases hrest with ⟨h0, _⟩ | ⟨hlast, _⟩ | ⟨j, hji, hj⟩
        · omega
        · omega
        · have hj_mem : Fin.natAdd N j ∈ interiorD N h :=
            mem_interiorD.2 ⟨j, rfl, by omega, by omega⟩
          have hj_ne : Fin.natAdd N j ≠ Fin.natAdd N w := by
            intro e; have := Fin.natAdd_injective (2 * h) N e; subst this; omega
          simp [x', Function.update_of_ne hj_ne, zeroOn, hj_mem] at hj
      · have hi_ne : Fin.natAdd N i ≠ Fin.natAdd N w :=
          fun e => hiw (Fin.natAdd_injective (2 * h) N e)
        rw [show x' (Fin.natAdd N i) = zeroOn (interiorD N h) x (Fin.natAdd N i) from
          Function.update_of_ne hi_ne _ _] at hi
        apply hno
        refine ⟨i, hi, ?_⟩
        rcases hrest with ⟨h0, hu⟩ | ⟨hlast, hv⟩ | ⟨j, hji, hj⟩
        · have hne_u : Fin.castAdd (2 * h) u ≠ Fin.natAdd N w := by
            intro e; have := congrArg Fin.val e; simp [Fin.castAdd, Fin.natAdd] at this; omega
          rw [show x' (Fin.castAdd (2 * h) u) = zeroOn (interiorD N h) x (Fin.castAdd (2 * h) u) from
            Function.update_of_ne hne_u _ _] at hu
          exact Or.inl ⟨h0, hu⟩
        · have hne_v : Fin.castAdd (2 * h) v ≠ Fin.natAdd N w := by
            intro e; have := congrArg Fin.val e; simp [Fin.castAdd, Fin.natAdd] at this; omega
          rw [show x' (Fin.castAdd (2 * h) v) = zeroOn (interiorD N h) x (Fin.castAdd (2 * h) v) from
            Function.update_of_ne hne_v _ _] at hv
          exact Or.inr (Or.inl ⟨hlast, hv⟩)
        · by_cases hjw : j = w
          · subst hjw
            have hi_mem : Fin.natAdd N i ∈ interiorD N h :=
              mem_interiorD.2 ⟨i, rfl, by omega, by omega⟩
            simp [zeroOn, hi_mem] at hi
          · have hj_ne : Fin.natAdd N j ≠ Fin.natAdd N w :=
              fun e => hjw (Fin.natAdd_injective (2 * h) N e)
            rw [show x' (Fin.natAdd N j) = zeroOn (interiorD N h) x (Fin.natAdd N j) from
              Function.update_of_ne hj_ne _ _] at hj
            exact Or.inr (Or.inr ⟨j, hji, hj⟩)
    · have htk : Function.update x' (Fin.natAdd N k) true (Fin.natAdd N k) = true :=
        Function.update_self _ _ _
      have htw : Function.update x' (Fin.natAdd N k) true (Fin.natAdd N w) = true := by
        rw [Function.update_of_ne (fun e => hw_ne_k (Fin.natAdd_injective (2 * h) N e))]
        simp [x']
      by_cases h1 : k.val ≤ 2
      · exact fullPath_edge_true _ k w (by simp [w, h1]) htk htw
      · exact fullPath_edge_true _ w k (by simp [w, h1]; omega) htw htk
  · intro x hx
    unfold fullPath at hx ⊢
    rw [Bool.or_eq_true, decide_eq_true_eq] at hx ⊢
    have hbase : (fun i : Fin N => zeroOn (interiorD N h) x (Fin.castAdd (2 * h) i)) =
        fun i : Fin N => x (Fin.castAdd (2 * h) i) := by
      funext i
      simp [zeroOn, castAdd_not_mem_interiorD]
    have hle : ∀ p, zeroOn (interiorD N h) x p = true → x p = true := by
      intro p hp
      by_cases hD : p ∈ interiorD N h
      · simp [zeroOn, hD] at hp
      · simpa [zeroOn, hD] using hp
    rcases hx with hg | ⟨i, hi, ⟨h0, hu⟩ | ⟨hlast, hv⟩ | ⟨j, hji, hj⟩⟩
    · rw [hbase] at hg; exact Or.inl hg
    · exact Or.inr ⟨i, hle _ hi, Or.inl ⟨h0, hle _ hu⟩⟩
    · exact Or.inr ⟨i, hle _ hi, Or.inr (Or.inl ⟨hlast, hle _ hv⟩)⟩
    · exact Or.inr ⟨i, hle _ hi, Or.inr (Or.inr ⟨j, hji, hle _ hj⟩)⟩
  · simp [fullPath, hg0]

def leftEmb (N h a : ℕ) (ha : a ≤ 2 * h) : Fin a → Fin (N + 2 * h) :=
  fun i => Fin.natAdd N ⟨i.val, by omega⟩

def rightEmb (N h b : ℕ) (hb : b ≤ 2 * h) : Fin b → Fin (N + 2 * h) :=
  fun i => Fin.natAdd N ⟨2 * h - 1 - i.val, by omega⟩

def baseG (N h : ℕ) (g : (Fin N → Bool) → Bool) (x : Fin (N + 2 * h) → Bool) : Bool :=
  g (fun i : Fin N => x (Fin.castAdd (2 * h) i))

def twoPath (N h : ℕ) (u v : Fin N) (g : (Fin N → Bool) → Bool)
    (a b : ℕ) (ha : a ≤ 2 * h) (hb : b ≤ 2 * h) (x : Fin (N + 2 * h) → Bool) : Bool :=
  pathOr (pathOr (baseG N h g) (Fin.castAdd (2 * h) v) (rightEmb N h b hb))
    (Fin.castAdd (2 * h) u) (leftEmb N h a ha) x

theorem leftEmb_inj (N h a : ℕ) (ha : a ≤ 2 * h) : Function.Injective (leftEmb N h a ha) := by
  intro i j hij
  have := congrArg Fin.val (Fin.natAdd_injective (2 * h) N hij)
  exact Fin.ext this

theorem rightEmb_inj (N h b : ℕ) (hb : b ≤ 2 * h) : Function.Injective (rightEmb N h b hb) := by
  intro i j hij
  have := congrArg Fin.val (Fin.natAdd_injective (2 * h) N hij)
  simp only at this
  exact Fin.ext (by omega)

theorem leftEmb_ne_castAdd (N h a : ℕ) (ha : a ≤ 2 * h) (i : Fin a) (w : Fin N) :
    leftEmb N h a ha i ≠ Fin.castAdd (2 * h) w := by
  intro e
  have := congrArg Fin.val e
  simp [leftEmb, Fin.natAdd, Fin.castAdd] at this
  omega

theorem rightEmb_ne_castAdd (N h b : ℕ) (hb : b ≤ 2 * h) (i : Fin b) (w : Fin N) :
    rightEmb N h b hb i ≠ Fin.castAdd (2 * h) w := by
  intro e
  have := congrArg Fin.val e
  simp [rightEmb, Fin.natAdd, Fin.castAdd] at this
  omega

theorem leftEmb_ne_rightEmb (N h a b : ℕ) (ha : a ≤ 2 * h) (hb : b ≤ 2 * h)
    (hab : a + b ≤ 2 * h) (i : Fin a) (j : Fin b) :
    leftEmb N h a ha i ≠ rightEmb N h b hb j := by
  intro e
  have := congrArg Fin.val (Fin.natAdd_injective (2 * h) N e)
  simp only at this
  omega

theorem baseG_indep_natAdd (N h : ℕ) (g : (Fin N → Bool) → Bool) (k : Fin (2 * h))
    (x : Fin (N + 2 * h) → Bool) (b : Bool) :
    baseG N h g (Function.update x (Fin.natAdd N k) b) = baseG N h g x := by
  unfold baseG
  congr 1
  funext i
  have hne : Fin.castAdd (2 * h) i ≠ Fin.natAdd N k := by
    intro e; have := congrArg Fin.val e; simp [Fin.castAdd, Fin.natAdd] at this; omega
  exact Function.update_of_ne hne b x

theorem pathPred_indep {M m : ℕ} (r : Fin M) (q : Fin m → Fin M) (p : Fin M)
    (hpr : p ≠ r) (hpq : ∀ i : Fin m, p ≠ q i) (x : Fin M → Bool) (b : Bool) :
    pathPred r q (Function.update x p b) = pathPred r q x := by
  simp only [pathPred]
  congr 1
  apply propext
  constructor
  · rintro ⟨i, hi, ⟨h0, hr⟩ | ⟨j, hji, hj⟩⟩
    · rw [Function.update_of_ne (hpq i).symm] at hi
      rw [Function.update_of_ne hpr.symm] at hr
      exact ⟨i, hi, Or.inl ⟨h0, hr⟩⟩
    · rw [Function.update_of_ne (hpq i).symm] at hi
      rw [Function.update_of_ne (hpq j).symm] at hj
      exact ⟨i, hi, Or.inr ⟨j, hji, hj⟩⟩
  · rintro ⟨i, hi, ⟨h0, hr⟩ | ⟨j, hji, hj⟩⟩
    · exact ⟨i, by rw [Function.update_of_ne (hpq i).symm]; exact hi,
        Or.inl ⟨h0, by rw [Function.update_of_ne hpr.symm]; exact hr⟩⟩
    · exact ⟨i, by rw [Function.update_of_ne (hpq i).symm]; exact hi,
        Or.inr ⟨j, hji, by rw [Function.update_of_ne (hpq j).symm]; exact hj⟩⟩

theorem fullPath_update_false_eq_twoPath (N h : ℕ) (u v : Fin N) (g : (Fin N → Bool) → Bool)
    (k : Fin (2 * h)) (hk1 : 1 ≤ k.val) (hk2 : k.val + 1 < 2 * h) :
    (fun x => fullPath N h u v g (Function.update x (Fin.natAdd N k) false)) =
      twoPath N h u v g k.val (2 * h - 1 - k.val) (by omega) (by omega) := by
  funext x
  unfold fullPath twoPath pathOr baseG pathPred
  have hbase : (fun i : Fin N =>
      Function.update x (Fin.natAdd N k) false (Fin.castAdd (2 * h) i)) =
      fun i : Fin N => x (Fin.castAdd (2 * h) i) := by
    funext i
    exact Function.update_of_ne (by
      intro e; have := congrArg Fin.val e; simp [Fin.castAdd, Fin.natAdd] at this; omega) _ _
  have hne_u : Fin.castAdd (2 * h) u ≠ Fin.natAdd N k := by
    intro e; have := congrArg Fin.val e; simp [Fin.castAdd, Fin.natAdd] at this; omega
  have hne_v : Fin.castAdd (2 * h) v ≠ Fin.natAdd N k := by
    intro e; have := congrArg Fin.val e; simp [Fin.castAdd, Fin.natAdd] at this; omega
  rw [hbase, Bool.or_assoc]
  congr 1
  apply Bool.eq_iff_iff.2
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, hrest⟩
    have hik : i ≠ k := by intro e; subst e; simp at hi
    rw [Function.update_of_ne (fun e => hik (Fin.natAdd_injective (2 * h) N e))] at hi
    rcases hrest with ⟨h0, hu⟩ | ⟨hlast, hv⟩ | ⟨j, hji, hj⟩
    · rw [Function.update_of_ne hne_u] at hu
      right
      refine ⟨⟨0, by omega⟩, ?_, Or.inl ⟨rfl, hu⟩⟩
      have ei : i = ⟨0, by omega⟩ := Fin.ext h0
      simpa [leftEmb, ei] using hi
    · rw [Function.update_of_ne hne_v] at hv
      left
      refine ⟨⟨0, by omega⟩, ?_, Or.inl ⟨rfl, hv⟩⟩
      have ei : i = ⟨2 * h - 1, by omega⟩ := Fin.ext (by simp; omega)
      simpa [rightEmb, ei] using hi
    · have hjk : j ≠ k := by intro e; subst e; simp at hj
      rw [Function.update_of_ne (fun e => hjk (Fin.natAdd_injective (2 * h) N e))] at hj
      by_cases hilt : i.val < k.val
      · have hjlt : j.val < k.val := by
          have : j.val ≠ k.val := fun e => hjk (Fin.ext e)
          omega
        right
        exact ⟨⟨i.val, hilt⟩, by simpa [leftEmb] using hi,
          Or.inr ⟨⟨j.val, hjlt⟩, hji, by simpa [leftEmb] using hj⟩⟩
      · have higt : k.val < i.val := by
          have : i.val ≠ k.val := fun e => hik (Fin.ext e)
          omega
        left
        refine ⟨⟨2 * h - 1 - j.val, by omega⟩, ?_,
          Or.inr ⟨⟨2 * h - 1 - i.val, by omega⟩, by simp; omega, ?_⟩⟩
        · have ej : (⟨2 * h - 1 - (2 * h - 1 - j.val), by omega⟩ : Fin (2 * h)) = j :=
            Fin.ext (by simp; omega)
          simpa [rightEmb, ej] using hj
        · have ei : (⟨2 * h - 1 - (2 * h - 1 - i.val), by omega⟩ : Fin (2 * h)) = i :=
            Fin.ext (by simp; omega)
          simpa [rightEmb, ei] using hi
  · rintro (⟨i, hi, ⟨h0, hv⟩ | ⟨j, hji, hj⟩⟩ | ⟨i, hi, ⟨h0, hu⟩ | ⟨j, hji, hj⟩⟩)
    · have hik : (⟨2 * h - 1 - i.val, by omega⟩ : Fin (2 * h)) ≠ k :=
        fun e => by have := congrArg Fin.val e; simp at this; omega
      refine ⟨⟨2 * h - 1 - i.val, by omega⟩, ?_,
        Or.inr (Or.inl ⟨by simp [h0]; omega, by rw [Function.update_of_ne hne_v]; exact hv⟩)⟩
      rw [Function.update_of_ne (fun e => hik (Fin.natAdd_injective (2 * h) N e))]
      exact hi
    · have hjk : (⟨2 * h - 1 - j.val, by omega⟩ : Fin (2 * h)) ≠ k :=
        fun e => by have := congrArg Fin.val e; simp at this; omega
      have hik : (⟨2 * h - 1 - i.val, by omega⟩ : Fin (2 * h)) ≠ k :=
        fun e => by have := congrArg Fin.val e; simp at this; omega
      refine ⟨⟨2 * h - 1 - j.val, by omega⟩, ?_,
        Or.inr (Or.inr ⟨⟨2 * h - 1 - i.val, by omega⟩, by simp; omega, ?_⟩)⟩
      · rw [Function.update_of_ne (fun e => hjk (Fin.natAdd_injective (2 * h) N e))]
        exact hj
      · rw [Function.update_of_ne (fun e => hik (Fin.natAdd_injective (2 * h) N e))]
        exact hi
    · have hik : (⟨i.val, by omega⟩ : Fin (2 * h)) ≠ k :=
        fun e => by have := congrArg Fin.val e; simp at this; omega
      refine ⟨⟨i.val, by omega⟩, ?_,
        Or.inl ⟨h0, by rw [Function.update_of_ne hne_u]; exact hu⟩⟩
      rw [Function.update_of_ne (fun e => hik (Fin.natAdd_injective (2 * h) N e))]
      exact hi
    · have hik : (⟨i.val, by omega⟩ : Fin (2 * h)) ≠ k :=
        fun e => by have := congrArg Fin.val e; simp at this; omega
      have hjk : (⟨j.val, by omega⟩ : Fin (2 * h)) ≠ k :=
        fun e => by have := congrArg Fin.val e; simp at this; omega
      refine ⟨⟨i.val, by omega⟩, ?_,
        Or.inr (Or.inr ⟨⟨j.val, by omega⟩, hji, ?_⟩)⟩
      · rw [Function.update_of_ne (fun e => hik (Fin.natAdd_injective (2 * h) N e))]
        exact hi
      · rw [Function.update_of_ne (fun e => hjk (Fin.natAdd_injective (2 * h) N e))]
        exact hj

theorem fullPath_update_true_eq_twoPath (N h : ℕ) (u v : Fin N) (g : (Fin N → Bool) → Bool)
    (k : Fin (2 * h)) (hk1 : 1 ≤ k.val) (hk2 : k.val + 1 < 2 * h) :
    (fun x => fullPath N h u v g (Function.update x (Fin.natAdd N k) true)) =
      fun x => twoPath N h u v g (k.val - 1) (2 * h - 2 - k.val) (by omega) (by omega) x ||
        x (Fin.natAdd N ⟨k.val - 1, by omega⟩) ||
        x (Fin.natAdd N ⟨k.val + 1, by omega⟩) := by
  funext x
  unfold fullPath twoPath pathOr baseG pathPred
  have hbase : (fun i : Fin N =>
      Function.update x (Fin.natAdd N k) true (Fin.castAdd (2 * h) i)) =
      fun i : Fin N => x (Fin.castAdd (2 * h) i) := by
    funext i
    exact Function.update_of_ne (by
      intro e; have := congrArg Fin.val e; simp [Fin.castAdd, Fin.natAdd] at this; omega) _ _
  have hne_u : Fin.castAdd (2 * h) u ≠ Fin.natAdd N k := by
    intro e; have := congrArg Fin.val e; simp [Fin.castAdd, Fin.natAdd] at this; omega
  have hne_v : Fin.castAdd (2 * h) v ≠ Fin.natAdd N k := by
    intro e; have := congrArg Fin.val e; simp [Fin.castAdd, Fin.natAdd] at this; omega
  rw [hbase, Bool.or_assoc, Bool.or_assoc, Bool.or_assoc]
  congr 1
  apply Bool.eq_iff_iff.2
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, ⟨h0, hu⟩ | ⟨hlast, hv⟩ | ⟨j, hji, hj⟩⟩
    · have hik : i ≠ k := fun e => by rw [e] at h0; omega
      rw [Function.update_of_ne (fun e => hik (Fin.natAdd_injective (2 * h) N e))] at hi
      rw [Function.update_of_ne hne_u] at hu
      by_cases hk : k.val = 1
      · right; right; left
        have ei : i = ⟨k.val - 1, by omega⟩ := Fin.ext (by simp; omega)
        rwa [ei] at hi
      · right; left
        refine ⟨⟨0, by omega⟩, ?_, Or.inl ⟨rfl, hu⟩⟩
        have ei : i = ⟨0, by omega⟩ := Fin.ext h0
        simpa [leftEmb, ei] using hi
    · have hik : i ≠ k := fun e => by rw [e] at hlast; omega
      rw [Function.update_of_ne (fun e => hik (Fin.natAdd_injective (2 * h) N e))] at hi
      rw [Function.update_of_ne hne_v] at hv
      by_cases hk : k.val + 2 = 2 * h
      · right; right; right
        have ei : i = ⟨k.val + 1, by omega⟩ := Fin.ext (by simp; omega)
        rwa [ei] at hi
      · left
        refine ⟨⟨0, by omega⟩, ?_, Or.inl ⟨rfl, hv⟩⟩
        have ei : i = ⟨2 * h - 1, by omega⟩ := Fin.ext (by simp; omega)
        simpa [rightEmb, ei] using hi
    · by_cases hik : i = k
      · subst hik
        have hjk : j ≠ i := fun e => by rw [e] at hji; omega
        rw [Function.update_of_ne (fun e => hjk (Fin.natAdd_injective (2 * h) N e))] at hj
        right; right; right
        have ej : j = ⟨i.val + 1, by omega⟩ := Fin.ext hji
        rwa [ej] at hj
      · rw [Function.update_of_ne (fun e => hik (Fin.natAdd_injective (2 * h) N e))] at hi
        by_cases hjk : j = k
        · subst hjk
          right; right; left
          have ei : i = ⟨j.val - 1, by omega⟩ := Fin.ext (by simp; omega)
          rwa [ei] at hi
        · rw [Function.update_of_ne (fun e => hjk (Fin.natAdd_injective (2 * h) N e))] at hj
          by_cases hjl : j.val = k.val - 1
          · right; right; left
            have ej : j = ⟨k.val - 1, by omega⟩ := Fin.ext hjl
            rwa [ej] at hj
          · by_cases hir : i.val = k.val + 1
            · right; right; right
              have ei : i = ⟨k.val + 1, by omega⟩ := Fin.ext hir
              rwa [ei] at hi
            · by_cases hilt : i.val < k.val - 1
              · have hjlt : j.val < k.val - 1 := by omega
                right; left
                exact ⟨⟨i.val, hilt⟩, by simpa [leftEmb] using hi,
                  Or.inr ⟨⟨j.val, hjlt⟩, hji, by simpa [leftEmb] using hj⟩⟩
              · have higt : k.val + 1 < i.val := by
                  have h1 : i.val ≠ k.val := fun e => hik (Fin.ext e)
                  have h2 : j.val ≠ k.val := fun e => hjk (Fin.ext e)
                  omega
                left
                refine ⟨⟨2 * h - 1 - j.val, by omega⟩, ?_,
                  Or.inr ⟨⟨2 * h - 1 - i.val, by omega⟩, by simp; omega, ?_⟩⟩
                · have ej : (⟨2 * h - 1 - (2 * h - 1 - j.val), by omega⟩ : Fin (2 * h)) = j :=
                    Fin.ext (by simp; omega)
                  simpa [rightEmb, ej] using hj
                · have ei : (⟨2 * h - 1 - (2 * h - 1 - i.val), by omega⟩ : Fin (2 * h)) = i :=
                    Fin.ext (by simp; omega)
                  simpa [rightEmb, ei] using hi
  · rintro (⟨i, hi, ⟨h0, hv⟩ | ⟨j, hji, hj⟩⟩ | ⟨i, hi, ⟨h0, hu⟩ | ⟨j, hji, hj⟩⟩ | hL | hR)
    · have hik : (⟨2 * h - 1 - i.val, by omega⟩ : Fin (2 * h)) ≠ k :=
        fun e => by have := congrArg Fin.val e; simp at this; omega
      refine ⟨⟨2 * h - 1 - i.val, by omega⟩, ?_,
        Or.inr (Or.inl ⟨by simp [h0]; omega, by rw [Function.update_of_ne hne_v]; exact hv⟩)⟩
      rw [Function.update_of_ne (fun e => hik (Fin.natAdd_injective (2 * h) N e))]
      exact hi
    · have hjk : (⟨2 * h - 1 - j.val, by omega⟩ : Fin (2 * h)) ≠ k :=
        fun e => by have := congrArg Fin.val e; simp at this; omega
      have hik : (⟨2 * h - 1 - i.val, by omega⟩ : Fin (2 * h)) ≠ k :=
        fun e => by have := congrArg Fin.val e; simp at this; omega
      refine ⟨⟨2 * h - 1 - j.val, by omega⟩, ?_,
        Or.inr (Or.inr ⟨⟨2 * h - 1 - i.val, by omega⟩, by simp; omega, ?_⟩)⟩
      · rw [Function.update_of_ne (fun e => hjk (Fin.natAdd_injective (2 * h) N e))]
        exact hj
      · rw [Function.update_of_ne (fun e => hik (Fin.natAdd_injective (2 * h) N e))]
        exact hi
    · have hik : (⟨i.val, by omega⟩ : Fin (2 * h)) ≠ k :=
        fun e => by have := congrArg Fin.val e; simp at this; omega
      refine ⟨⟨i.val, by omega⟩, ?_,
        Or.inl ⟨h0, by rw [Function.update_of_ne hne_u]; exact hu⟩⟩
      rw [Function.update_of_ne (fun e => hik (Fin.natAdd_injective (2 * h) N e))]
      exact hi
    · have hik : (⟨i.val, by omega⟩ : Fin (2 * h)) ≠ k :=
        fun e => by have := congrArg Fin.val e; simp at this; omega
      have hjk : (⟨j.val, by omega⟩ : Fin (2 * h)) ≠ k :=
        fun e => by have := congrArg Fin.val e; simp at this; omega
      refine ⟨⟨i.val, by omega⟩, ?_,
        Or.inr (Or.inr ⟨⟨j.val, by omega⟩, hji, ?_⟩)⟩
      · rw [Function.update_of_ne (fun e => hik (Fin.natAdd_injective (2 * h) N e))]
        exact hi
      · rw [Function.update_of_ne (fun e => hjk (Fin.natAdd_injective (2 * h) N e))]
        exact hj
    · have hneL : (⟨k.val - 1, by omega⟩ : Fin (2 * h)) ≠ k :=
        fun e => by have := congrArg Fin.val e; simp at this; omega
      refine ⟨⟨k.val - 1, by omega⟩, ?_, Or.inr (Or.inr ⟨k, by simp; omega, by simp⟩)⟩
      rw [Function.update_of_ne (fun e => hneL (Fin.natAdd_injective (2 * h) N e))]
      exact hL
    · have hneR : (⟨k.val + 1, by omega⟩ : Fin (2 * h)) ≠ k :=
        fun e => by have := congrArg Fin.val e; simp at this
      refine ⟨k, by simp, Or.inr (Or.inr ⟨⟨k.val + 1, by omega⟩, by simp, ?_⟩)⟩
      rw [Function.update_of_ne (fun e => hneR (Fin.natAdd_injective (2 * h) N e))]
      exact hR

theorem renum_pendant (N h : ℕ) (w : Fin N) (g : (Fin N → Bool) → Bool)
    (q0 : Fin (N + 2 * h)) (hq0 : N ≤ q0.val) (s : ℕ)
    (hc : HasCircuitSize (N + 2 * h)
      (fun x => baseG N h g x || (x (Fin.castAdd (2 * h) w) && x q0)) s) :
    HasCircuitSize (N + 1)
      (fun x : Fin (N + 1) → Bool => g (fun i : Fin N => x i.castSucc) || (x w.castSucc && x (Fin.last N))) s := by
  let π : Fin (N + 2 * h) → Fin (N + 1) := fun j =>
    if hlt : j.val < N then ⟨j.val, by omega⟩ else Fin.last N
  have h1 := renum_size π _ s hc
  have heq : (fun x : Fin (N + 1) → Bool =>
      baseG N h g (x ∘ π) || ((x ∘ π) (Fin.castAdd (2 * h) w) && (x ∘ π) q0)) =
      fun x : Fin (N + 1) → Bool =>
        g (fun i : Fin N => x i.castSucc) || (x w.castSucc && x (Fin.last N)) := by
    funext x
    have hpi : ∀ i : Fin N, π (Fin.castAdd (2 * h) i) = i.castSucc := by
      intro i; apply Fin.ext; simp [π, i.isLt]
    have hpq : π q0 = Fin.last N := by
      apply Fin.ext; simp [π, show ¬ q0.val < N by omega]
    simp only [baseG, Function.comp_apply, hpi, hpq]
  rwa [heq] at h1

theorem peel_twoPath (N h : ℕ) (u v : Fin N) (g : (Fin N → Bool) → Bool)
    (hnc : ∃ y y' : Fin N → Bool, g y ≠ g y')
    (hg0 : g (fun _ : Fin N => false) = false)
    (hu : ∃ x : Fin N → Bool, x u = true ∧ g x = false)
    (hv : ∃ x : Fin N → Bool, x v = true ∧ g x = false)
    (a b : ℕ) (ha : a ≤ 2 * h) (hb : b ≤ 2 * h) (hab : a + b ≤ 2 * h) (s : ℕ)
    (hc : HasCircuitSize (N + 2 * h) (twoPath N h u v g a b ha hb) s) :
    (1 ≤ b → ∃ s' : ℕ, (3 * a) / 2 + (3 * (b - 1)) / 2 + s' ≤ s ∧
      HasCircuitSize (N + 1) (fun x : Fin (N + 1) → Bool =>
        g (fun i : Fin N => x i.castSucc) || (x v.castSucc && x (Fin.last N))) s') ∧
    (1 ≤ a → ∃ s' : ℕ, (3 * b) / 2 + (3 * (a - 1)) / 2 + s' ≤ s ∧
      HasCircuitSize (N + 1) (fun x : Fin (N + 1) → Bool =>
        g (fun i : Fin N => x i.castSucc) || (x u.castSucc && x (Fin.last N))) s') := by
  have hzT : ∃ zT : Fin N → Bool, g zT = true := by
    obtain ⟨y, y', hne⟩ := hnc
    cases hy : g y
    · cases hy' : g y'
      · exact absurd (hy.trans hy'.symm) hne
      · exact ⟨y', hy'⟩
    · exact ⟨y, hy⟩
  obtain ⟨zT, hzT⟩ := hzT
  obtain ⟨xu, hxu1, hxu0⟩ := hu
  obtain ⟨xv, hxv1, hxv0⟩ := hv
  let ext : (Fin N → Bool) → Fin (N + 2 * h) → Bool := fun z p =>
    if hlt : p.val < N then z ⟨p.val, hlt⟩ else false
  have hext_G : ∀ z, baseG N h g (ext z) = g z := by
    intro z; unfold baseG; congr 1; funext i; simp [ext, i.isLt]
  have hext_cast : ∀ z (i : Fin N), ext z (Fin.castAdd (2 * h) i) = z i := by
    intro z i; simp [ext, i.isLt]
  have hext_nat : ∀ z (i : Fin (2 * h)), ext z (Fin.natAdd N i) = false := by
    intro z i; simp [ext, Fin.natAdd]
  have hG_true : ∃ x, baseG N h g x = true := ⟨ext zT, by rw [hext_G, hzT]⟩
  have hG_false_u0 : ∃ x, baseG N h g x = false ∧ x (Fin.castAdd (2 * h) u) = false :=
    ⟨fun _ => false, by simp [baseG, hg0], rfl⟩
  have hG_false_v0 : ∃ x, baseG N h g x = false ∧ x (Fin.castAdd (2 * h) v) = false :=
    ⟨fun _ => false, by simp [baseG, hg0], rfl⟩
  constructor
  · intro hb1
    let HR := pathOr (baseG N h g) (Fin.castAdd (2 * h) v) (rightEmb N h b hb)
    have hHR_ind : ∀ (i : Fin a) x val, HR (Function.update x (leftEmb N h a ha i) val) = HR x := by
      intro i x val
      simp only [HR, pathOr, leftEmb, baseG_indep_natAdd]
      congr 1
      exact pathPred_indep _ _ _ (leftEmb_ne_castAdd N h a ha i v)
        (fun j => leftEmb_ne_rightEmb N h a b ha hb hab i j) x val
    have hHR_true : ∃ x, HR x = true := ⟨ext zT, by simp [HR, pathOr, hext_G, hzT]⟩
    have hHR_false_u0 : ∃ x, HR x = false ∧ x (Fin.castAdd (2 * h) u) = false :=
      ⟨fun _ => false, by simp [HR, pathOr, baseG, hg0, pathPred_all_false], rfl⟩
    have hHR_false_u1 : ∃ x, HR x = false ∧ x (Fin.castAdd (2 * h) u) = true :=
      ⟨ext xu, by
        rw [show HR (ext xu) = (baseG N h g (ext xu) || pathPred _ _ (ext xu)) from rfl,
          hext_G, hxu0, pathPred_all_false _ _ _ (fun j => by simp [rightEmb, ext, Fin.natAdd])]; rfl,
        by rw [hext_cast, hxu1]⟩
    obtain ⟨s1, hs1, hc1⟩ := peel_to_zero HR (Fin.castAdd (2 * h) u)
      hHR_true hHR_false_u0 hHR_false_u1 a (leftEmb N h a ha) hHR_ind
      (leftEmb_inj N h a ha) (fun i => leftEmb_ne_castAdd N h a ha i u) s hc
    obtain ⟨s2, hs2, hc2⟩ := peel_to_one (baseG N h g) (Fin.castAdd (2 * h) v)
      hG_true hG_false_v0 b hb1 (rightEmb N h b hb)
      (fun i x val => baseG_indep_natAdd N h g _ x val)
      (rightEmb_inj N h b hb) (fun i => rightEmb_ne_castAdd N h b hb i v) s1 hc1
    refine ⟨s2, by omega, renum_pendant N h v g (rightEmb N h b hb ⟨0, by omega⟩) ?_ s2 hc2⟩
    simp [rightEmb, Fin.natAdd]
  · intro ha1
    let HL := pathOr (baseG N h g) (Fin.castAdd (2 * h) u) (leftEmb N h a ha)
    have hswap : twoPath N h u v g a b ha hb =
        pathOr HL (Fin.castAdd (2 * h) v) (rightEmb N h b hb) := by
      funext x
      simp only [twoPath, HL, pathOr, Bool.or_assoc]
      congr 1
      exact Bool.or_comm _ _
    rw [hswap] at hc
    have hHL_ind : ∀ (i : Fin b) x val, HL (Function.update x (rightEmb N h b hb i) val) = HL x := by
      intro i x val
      simp only [HL, pathOr, rightEmb, baseG_indep_natAdd]
      congr 1
      exact pathPred_indep _ _ _ (rightEmb_ne_castAdd N h b hb i u)
        (fun j => (leftEmb_ne_rightEmb N h a b ha hb hab j i).symm) x val
    have hHL_true : ∃ x, HL x = true := ⟨ext zT, by simp [HL, pathOr, hext_G, hzT]⟩
    have hHL_false_v0 : ∃ x, HL x = false ∧ x (Fin.castAdd (2 * h) v) = false :=
      ⟨fun _ => false, by simp [HL, pathOr, baseG, hg0, pathPred_all_false], rfl⟩
    have hHL_false_v1 : ∃ x, HL x = false ∧ x (Fin.castAdd (2 * h) v) = true :=
      ⟨ext xv, by
        rw [show HL (ext xv) = (baseG N h g (ext xv) || pathPred _ _ (ext xv)) from rfl,
          hext_G, hxv0, pathPred_all_false _ _ _ (fun j => by simp [leftEmb, ext, Fin.natAdd])]; rfl,
        by rw [hext_cast, hxv1]⟩
    obtain ⟨s1, hs1, hc1⟩ := peel_to_zero HL (Fin.castAdd (2 * h) v)
      hHL_true hHL_false_v0 hHL_false_v1 b (rightEmb N h b hb) hHL_ind
      (rightEmb_inj N h b hb) (fun i => rightEmb_ne_castAdd N h b hb i v) s hc
    obtain ⟨s2, hs2, hc2⟩ := peel_to_one (baseG N h g) (Fin.castAdd (2 * h) u)
      hG_true hG_false_u0 a ha1 (leftEmb N h a ha)
      (fun i x val => baseG_indep_natAdd N h g _ x val)
      (leftEmb_inj N h a ha) (fun i => leftEmb_ne_castAdd N h a ha i u) s1 hc1
    refine ⟨s2, by omega, renum_pendant N h u g (leftEmb N h a ha ⟨0, by omega⟩) ?_ s2 hc2⟩
    simp [leftEmb, Fin.natAdd]

theorem strip_free_or {M s : ℕ} (F : (Fin M → Bool) → Bool) (p : Fin M)
    (hind : ∀ x b, F (Function.update x p b) = F x)
    (hF : ∃ x, F x = false) (hT : ∃ x, F x = true)
    (hc : HasCircuitSize M (fun x => F x || x p) s) :
    ∃ s' : ℕ, s' + 1 ≤ s ∧ HasCircuitSize M F s' := by
  have heq : (fun x => (fun y => F y || y p) (Function.update x p false)) = F := by
    funext x
    simp [hind]
  obtain ⟨xF, hxF⟩ := hF
  obtain ⟨xT, hxT⟩ := hT
  have hdep : Dep (fun x => F x || x p) p := by
    apply dep_of_ft
    refine ⟨xF, ?_⟩
    simp [hind, hxF]
  have hnc : ∃ x y : Fin M → Bool,
      (fun z => F z || z p) (Function.update x p false) ≠
        (fun z => F z || z p) (Function.update y p false) := by
    refine ⟨xF, xT, ?_⟩
    simp [hind, hxF, hxT]
  obtain ⟨s', hs', hc'⟩ := drop1_var p false hdep hnc hc
  rw [heq] at hc'
  exact ⟨s', hs', hc'⟩

theorem solve_573 (N h : ℕ) (u v : Fin N) (g : (Fin N → Bool) → Bool)
    (hh : 3 ≤ h) (hnc : ∃ y y' : Fin N → Bool, g y ≠ g y')
    (hg0 : g (fun _ : Fin N => false) = false)
    (hu : ∃ x : Fin N → Bool, x u = true ∧ g x = false)
    (hv : ∃ x : Fin N → Bool, x v = true ∧ g x = false)
    (s : ℕ) (hc : HasCircuitSize (N + 2 * h) (fullPath N h u v g) s) :
    ∃ s' : ℕ, 3 * h + s' ≤ s ∧
      (HasCircuitSize (N + 1) (fun x : Fin (N + 1) → Bool =>
          g (fun i : Fin N => x i.castSucc) || (x u.castSucc && x (Fin.last N))) s' ∨
       HasCircuitSize (N + 1) (fun x : Fin (N + 1) → Bool =>
          g (fun i : Fin N => x i.castSucc) || (x v.castSucc && x (Fin.last N))) s') := by
  have hD : DeepHyp (fullPath N h u v g) (interiorD N h) :=
    fullPath_deepHyp N h u v g hh hnc hg0
  have hne : (interiorD N h).Nonempty :=
    ⟨Fin.natAdd N ⟨1, by omega⟩, mem_interiorD.2 ⟨⟨1, by omega⟩, rfl, le_refl 1, by simp; omega⟩⟩
  obtain ⟨y, hy, hdrop⟩ := stmtML_any (N + 2 * h) (by omega) (fullPath N h u v g)
    (interiorD N h) s hD hne hc
  obtain ⟨k, rfl, hk1, hk2⟩ := mem_interiorD.1 hy
  rcases hdrop with ⟨s1, hs1, hc1⟩ | ⟨s1, hs1, hc1⟩
  · rw [fullPath_update_false_eq_twoPath N h u v g k hk1 hk2] at hc1
    have hpeel := peel_twoPath N h u v g hnc hg0 hu hv k.val (2 * h - 1 - k.val)
      (by omega) (by omega) (by omega) s1 hc1
    by_cases hpar : k.val % 2 = 0
    · obtain ⟨s', hs', hc'⟩ := hpeel.1 (by omega)
      exact ⟨s', by omega, Or.inr hc'⟩
    · obtain ⟨s', hs', hc'⟩ := hpeel.2 (by omega)
      exact ⟨s', by omega, Or.inl hc'⟩
  · rw [fullPath_update_true_eq_twoPath N h u v g k hk1 hk2] at hc1
    let a' := k.val - 1
    let b' := 2 * h - 2 - k.val
    let pL : Fin (N + 2 * h) := Fin.natAdd N ⟨k.val - 1, by omega⟩
    let pR : Fin (N + 2 * h) := Fin.natAdd N ⟨k.val + 1, by omega⟩
    let T := twoPath N h u v g a' b' (by omega) (by omega)
    have hT_ind : ∀ (m : Fin (2 * h)), a' ≤ m.val → m.val < 2 * h - b' →
        ∀ x val, T (Function.update x (Fin.natAdd N m) val) = T x := by
      intro m hm1 hm2 x val
      simp only [T, twoPath, pathOr, baseG_indep_natAdd]
      have hne_u : Fin.natAdd N m ≠ Fin.castAdd (2 * h) u := by
        intro e; have := congrArg Fin.val e; simp [Fin.natAdd, Fin.castAdd] at this; omega
      have hne_v : Fin.natAdd N m ≠ Fin.castAdd (2 * h) v := by
        intro e; have := congrArg Fin.val e; simp [Fin.natAdd, Fin.castAdd] at this; omega
      have hne_L : ∀ i : Fin a', Fin.natAdd N m ≠ leftEmb N h a' (by omega) i := by
        intro i e; have := congrArg Fin.val (Fin.natAdd_injective (2 * h) N e)
        simp at this; omega
      have hne_R : ∀ i : Fin b', Fin.natAdd N m ≠ rightEmb N h b' (by omega) i := by
        intro i e; have := congrArg Fin.val (Fin.natAdd_injective (2 * h) N e)
        simp at this; omega
      rw [pathPred_indep _ _ _ hne_v hne_R, pathPred_indep _ _ _ hne_u hne_L]
    have hT_false : T (fun _ => false) = false := by
      simp [T, twoPath, pathOr, baseG, hg0, pathPred_all_false]
    have hT_true : ∃ x, T x = true := by
      obtain ⟨y, y', hne⟩ := hnc
      have hzT : ∃ zT : Fin N → Bool, g zT = true := by
        cases hy : g y
        · cases hy' : g y'
          · exact absurd (hy.trans hy'.symm) hne
          · exact ⟨y', hy'⟩
        · exact ⟨y, hy⟩
      obtain ⟨zT, hzT⟩ := hzT
      refine ⟨fun p => if hlt : p.val < N then zT ⟨p.val, hlt⟩ else false, ?_⟩
      simp only [T, twoPath, pathOr, baseG]
      have hb : (fun i : Fin N =>
          if hlt : (Fin.castAdd (2 * h) i).val < N then zT ⟨(Fin.castAdd (2 * h) i).val, hlt⟩
          else false) = zT := by
        funext i; simp [i.isLt]
      rw [hb, hzT]; rfl
    have hpL_ne_pR : pL ≠ pR := by
      intro e; have := congrArg Fin.val (Fin.natAdd_injective (2 * h) N e)
      simp at this
    have hTL_ind : ∀ x val, (fun z => T z || z pL) (Function.update x pR val) = (T x || x pL) := by
      intro x val
      dsimp only
      rw [show T (Function.update x pR val) = T x from
        hT_ind ⟨k.val + 1, by omega⟩ (by simp [a']; omega) (by simp [b']; omega) x val,
        Function.update_of_ne hpL_ne_pR]
    obtain ⟨s2, hs2, hc2⟩ := strip_free_or (fun z => T z || z pL) pR hTL_ind
      ⟨fun _ => false, by simp [hT_false]⟩
      (by obtain ⟨x, hx⟩ := hT_true; exact ⟨x, by simp [hx]⟩)
      hc1
    obtain ⟨s3, hs3, hc3⟩ := strip_free_or T pL
      (hT_ind ⟨k.val - 1, by omega⟩ (by simp [a']) (by simp [b']; omega))
      ⟨fun _ => false, hT_false⟩ hT_true hc2
    have hpeel := peel_twoPath N h u v g hnc hg0 hu hv a' b'
      (by omega) (by omega) (by omega) s3 hc3
    by_cases hpar : k.val % 2 = 0
    · obtain ⟨s', hs', hc'⟩ := hpeel.2 (by omega)
      exact ⟨s', by omega, Or.inl hc'⟩
    · obtain ⟨s', hs', hc'⟩ := hpeel.1 (by omega)
      exact ⟨s', by omega, Or.inr hc'⟩

end L573

theorem PEqualNP.Outside.L_meta_573 :
    ∀ (N h : ℕ) (u v : Fin N) (g : (Fin N → Bool) → Bool), u ≠ v → 3 ≤ h → (∃ y y' : Fin N → Bool, g y ≠ g y') → g (fun _ : Fin N => false) = false → (∃ x : Fin N → Bool, x u = true ∧ g x = false) → (∃ x : Fin N → Bool, x v = true ∧ g x = false) → ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize (N + 2 * h) (fun x : Fin (N + 2 * h) → Bool => g (fun i : Fin N => x (Fin.castAdd (2 * h) i)) || decide (∃ i : Fin (2 * h), x (Fin.natAdd N i) = true ∧ ((i.val = 0 ∧ x (Fin.castAdd (2 * h) u) = true) ∨ (i.val + 1 = 2 * h ∧ x (Fin.castAdd (2 * h) v) = true) ∨ ∃ j : Fin (2 * h), j.val = i.val + 1 ∧ x (Fin.natAdd N j) = true))) s → ∃ s' : ℕ, 3 * h + s' ≤ s ∧ (PEqualNP.MetaComplexity.HasCircuitSize (N + 1) (fun x : Fin (N + 1) → Bool => g (fun i : Fin N => x i.castSucc) || (x u.castSucc && x (Fin.last N))) s' ∨ PEqualNP.MetaComplexity.HasCircuitSize (N + 1) (fun x : Fin (N + 1) → Bool => g (fun i : Fin N => x i.castSucc) || (x v.castSucc && x (Fin.last N))) s') := by
  intro N h u v g _ hh hnc hg0 hu hv s hc
  exact L573.solve_573 N h u v g hh hnc hg0 hu hv s hc
