import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.LMeta468Aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

private lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

private lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
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

private lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

private lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

private lemma getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

private lemma hasCircuitSize_mono {n : ℕ} {f : (Fin n → Bool) → Bool} {s t : ℕ} (hst : s ≤ t)
    (h : HasCircuitSize n f s) : HasCircuitSize n f t := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  exact ⟨C, ok, le_trans hsz hst, hev⟩

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

private lemma rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
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

private lemma rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

private lemma rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
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

private lemma relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    exact (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output

def gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

private lemma mem_foldr_union {n : ℕ} (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

private lemma mem_gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom {n : ℕ} (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

private lemma suppsFrom_append {n : ℕ} (gs1 gs2 : List Gate) (L : List (Finset (Fin n))) :
    suppsFrom (gs1 ++ gs2) L = suppsFrom gs2 (suppsFrom gs1 L) := by
  simp [suppsFrom, List.foldl_append]

private lemma length_suppsFrom {n : ℕ} (gs : List Gate) :
    ∀ L : List (Finset (Fin n)), (suppsFrom gs L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; simp [suppsFrom]
  | cons g gs ih =>
    intro L
    have h1 : suppsFrom (g :: gs) L = suppsFrom gs (L ++ [gateSupp L g]) := rfl
    rw [h1, ih, List.length_append, List.length_singleton, List.length_cons]
    omega

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree {n : ℕ} (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

private lemma agree_wiresFrom {n : ℕ} (x y : Fin n → Bool) (gs : List Gate) :
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

private lemma agree_inputs {n : ℕ} (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

private lemma inputSupps_noread_at (m : ℕ) (p : Fin m) :
    ∀ j : ℕ, j ≠ (p : ℕ) → p ∉ (inputSupps m).getD j ∅ := by
  intro j hj
  by_cases hlt : j < m
  · have e : (inputSupps m).getD j ∅ = {⟨j, hlt⟩} := by simp [inputSupps, hlt]
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

private lemma supp_noread_set (m : ℕ) (p : Fin m) (B : Set ℕ) (gs : List Gate) :
    ∀ L : List (Finset (Fin m)),
    (∀ g ∈ gs, ∀ a ∈ g.inputs, a ∉ B) →
    (∀ j : ℕ, j ∉ B → p ∉ L.getD j ∅) →
    ∀ j : ℕ, j ∉ B → p ∉ (suppsFrom gs L).getD j ∅ := by
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
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g p).1 hmem
      exact h a (hno g List.mem_cons_self a ha) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

private lemma normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

private lemma normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
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

private lemma wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
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

abbrev Stat := Bool ⊕ ℕ

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

private lemma simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp [simpAnd] at hg
    · cases a <;> simp [simpAnd] at hg
    · cases a <;> cases b <;> simp [simpAnd] at hg
      subst hg; simp [Ok]
    · simp [simpAnd] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp [simpOr] at hg
    · cases a <;> simp [simpOr] at hg
    · cases a <;> cases b <;> simp [simpOr] at hg
      subst hg; simp [Ok]
    · simp [simpOr] at hg
  · rcases ins with _ | ⟨a, l⟩
    · simp [simpNot] at hg
    · cases a <;> simp [simpNot] at hg
      subst hg; simp [Ok]
  · simp at hg
  · simp at hg

private lemma simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
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

private lemma simplify_kill (op : GateOp) (m : ℕ) (ins : List Stat)
    (hlen : ins.length ≤ 2) (hnot : op = GateOp.not → ins.length ≤ 1) :
    (op = GateOp.not → Sum.inl false ∈ ins →
      (simplify op m ins).1 = none ∧ ∃ c, (simplify op m ins).2 = Sum.inl c) ∧
    (op = GateOp.and → Sum.inl false ∈ ins →
      (simplify op m ins).1 = none ∧ ∃ c, (simplify op m ins).2 = Sum.inl c) ∧
    (op = GateOp.or → Sum.inl true ∈ ins →
      (simplify op m ins).1 = none ∧ ∃ c, (simplify op m ins).2 = Sum.inl c) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl hin
    have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]
  · rintro rfl hin
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rintro rfl hin
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]

private lemma simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · rcases a with c | j <;> rcases b with d | k
      · cases c <;> cases d <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
      · cases c <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
      · cases d <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
      · simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · rcases a with c | j <;> rcases b with d | k
      · cases c <;> cases d <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
      · cases c <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
      · cases d <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
      · simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

private lemma elim_append (n : ℕ) (gs1 gs2 : List Gate) (acc : List Stat × List Gate) :
    elim n (gs1 ++ gs2) acc = elim n gs2 (elim n gs1 acc) := by
  simp [elim, List.foldl_append]

private lemma elim_stat_len (n : ℕ) (gs : List Gate) :
    ∀ acc : List Stat × List Gate, (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h1, ih]
    simp [elimStep]
    omega

private lemma elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

private lemma toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

private lemma elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
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

private lemma elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
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

private lemma elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
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

private lemma elim_count (n k : ℕ) (b : Bool) (gs : List Gate) :
    ∀ acc : List Stat × List Gate, (∀ g ∈ gs, NOk g) →
      k < acc.1.length → acc.1.getD k (.inl false) = .inl b →
      (elim n gs acc).2.length + gs.countP (fun g => decide (k ∈ g.inputs)) ≤
        acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _; simp [elim]
  | cons g gs ih =>
    intro acc hok hk hc
    let next := elimStep n acc g
    have hstep : elim n (g :: gs) acc = elim n gs next := rfl
    have htail := ih next (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (by simp [next, elimStep]; omega)
      (by
        dsimp only [next, elimStep]
        rw [getD_snoc_ne _ _ _ _ (by omega), hc])
    rw [hstep, List.length_cons, List.countP_cons]
    by_cases hread : k ∈ g.inputs
    · have hg := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (.inl false))).1 = none :=
        simplify_count _ _ _ hg.1.1 (by simpa using hg.1.2)
          (fun h => by simpa using hg.2 h)
          ⟨b, List.mem_map.2 ⟨k, hread, hc⟩⟩
      have hlen : next.2.length = acc.2.length := by
        change (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (.inl false))).1.toList).length = _
        rw [hnone]
        simp
      simp only [hread, decide_true, ite_true]
      omega
    · have hlen : next.2.length ≤ acc.2.length + 1 := by
        simp only [next, elimStep, List.length_append]
        exact Nat.add_le_add_left (toList_length_le _) _
      simp only [hread, decide_false, Bool.false_eq_true, ite_false]
      omega

private lemma Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

private lemma Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

private lemma inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
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
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

def initFix (m : ℕ) (p : Fin m) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin m => if i = p then (Sum.inl b : Stat) else Sum.inr (i : ℕ))

private lemma inv_initFix (m : ℕ) (p : Fin m) (b : Bool) (x : Fin m → Bool) :
    Inv m (List.ofFn x) (List.ofFn (Function.update x p b)) (initFix m p b, []) := by
  refine ⟨by simp [initFix], ?_⟩
  intro i
  by_cases hi : i < m
  · by_cases hip : (⟨i, hi⟩ : Fin m) = p
    · subst hip
      simp [initFix, hi, Stat.Valid, Stat.val]
    · simp [initFix, hi, hip, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [initFix]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

def padFalse (n k : ℕ) (y : Fin k → Bool) : Fin (n + k) → Bool :=
  fun i => if h : (i : ℕ) < n then false else y ⟨(i : ℕ) - n, by omega⟩

private lemma padFalse_castAdd (n k : ℕ) (y : Fin k → Bool) (a : Fin n) :
    padFalse n k y (Fin.castAdd k a) = false := by
  simp [padFalse, a.isLt]

private lemma padFalse_natAdd (n k : ℕ) (y : Fin k → Bool) (j : Fin k) :
    padFalse n k y (Fin.natAdd n j) = y j := by
  simp [padFalse]

def initDrop (n k : ℕ) : List Stat :=
  List.replicate n (Sum.inl false : Stat) ++ List.ofFn (fun j : Fin k => (Sum.inr (j : ℕ) : Stat))

private lemma inv_initDrop (n k : ℕ) (y : Fin k → Bool) :
    Inv k (List.ofFn y) (List.ofFn (padFalse n k y)) (initDrop n k, []) := by
  refine ⟨by simp [initDrop], ?_⟩
  intro i
  by_cases h1 : i < n
  · have hlt : i < n + k := by omega
    have hget : (initDrop n k).getD i (Sum.inl false) = Sum.inl false := by
      rw [initDrop, List.getD_append _ _ _ _ (by simp [h1]),
          List.getD_eq_getElem _ _ (by simp [h1])]
      simp
    rw [hget]
    refine ⟨trivial, ?_⟩
    simp [Stat.val, hlt, padFalse, h1]
  · by_cases h2 : i < n + k
    · have hget : (initDrop n k).getD i (Sum.inl false) = Sum.inr (i - n) := by
        rw [initDrop, List.getD_append_right _ _ _ _ (by simp; omega)]
        simp [show i - n < k by omega]
      rw [hget]
      refine ⟨by simp [Stat.Valid]; omega, ?_⟩
      simp [Stat.val, wiresFrom, h2, show i - n < k by omega, padFalse, h1]
    · rw [List.getD_eq_default _ _ (by simp [initDrop]; omega),
          List.getD_eq_default _ _ (by simp; omega)]
      exact ⟨trivial, rfl⟩

private lemma drop_first_n (n k s : ℕ) (g : (Fin k → Bool) → Bool)
    (hnc : ∃ y y' : Fin k → Bool, g y ≠ g y')
    (h : HasCircuitSize (n + k) (fun x => g (fun j => x (Fin.natAdd n j))) s) :
    HasCircuitSize k g s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + k) → Bool,
      (wiresFrom gs (List.ofFn x)).getD C.output false = g (fun j => x (Fin.natAdd n j)) := by
    intro x
    rw [hgs, wiresFrom_norm]
    exact hev x
  set acc := elim k gs (initDrop n k, []) with hacc
  have hval : ∀ y : Fin k → Bool,
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y)) = g y := by
    intro y
    have hinv := inv_elim k (List.ofFn y) (by simp) gs _ _
      (fun g hg => (hnok g hg).1) (inv_initDrop n k y)
    have h1 := (hinv.2 C.output).2
    rw [hevg (padFalse n k y)] at h1
    simpa [padFalse_natAdd] using h1
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl b =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | inr j =>
    have hlen : acc.2.length ≤ s := by
      have h1 := elim_len k gs (initDrop n k, [])
      rw [← hacc] at h1
      have hl : gs.length = C.gates.length := by simp [hgs]
      simp only [List.length_nil, zero_add] at h1
      omega
    refine ⟨⟨acc.2, j⟩, elim_ok k gs _ (by simp), hlen, ?_⟩
    intro y
    have hy := hval y
    rw [hst] at hy
    exact hy

private lemma gate_elim_at (m : ℕ) (f : (Fin m → Bool) → Bool) (p : Fin m) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin m → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∃ x x' : Fin m → Bool, f (Function.update x p b) ≠ f (Function.update x' p b))
    (h : HasCircuitSize m f s) :
    1 ≤ s ∧ HasCircuitSize m (fun x => f (Function.update x p b)) (s - 1) := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin m → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  set acc := elim m gs (initFix m p b, []) with hacc
  have hval : ∀ x : Fin m → Bool,
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn x)) =
        f (Function.update x p b) := by
    intro x
    have hinv := inv_elim m (List.ofFn x) (by simp) gs _ _
      (fun g hg => (hnok g hg).1) (inv_initFix m p b x)
    exact ((hinv.2 C.output).2).trans (hevg _)
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨x, x', hne⟩ := hnc
    apply hne
    rw [← hval x, ← hval x', hst]; rfl
  | inr j =>
    have hread : ∃ g ∈ gs, (p : ℕ) ∈ g.inputs := by
      by_contra! hno
      have hout : C.output ≠ (p : ℕ) := by
        intro e
        rw [e, hacc, elim_getD m (p : ℕ) _ gs _ (by simp [initFix])] at hst
        have hp : (initFix m p b).getD (p : ℕ) (Sum.inl false) = Sum.inl b := by
          simp [initFix]
        rw [show ((initFix m p b, ([] : List Gate))).1 = initFix m p b from rfl, hp] at hst
        cases hst
      obtain ⟨x, hx⟩ := hdep
      apply hx
      have hns := supp_noread_set m p {(p : ℕ)} gs (inputSupps m)
        (fun g hg a ha e => hno g hg (by simpa using e ▸ ha))
        (fun j hj => inputSupps_noread_at m p j (by simpa using hj))
        C.output (by simpa using hout)
      have hag := (agree_wiresFrom (Function.update x p (!x p)) x gs _ _ _
        (agree_inputs _ _)).2.2 C.output (by
          intro k hk
          have : k ≠ p := fun e => hns (e ▸ hk)
          simp [Function.update_of_ne this])
      rw [← hevg, ← hevg]
      exact hag
    have hlt := elim_len_lt m (p : ℕ) gs (initFix m p b, []) hnok (by simp [initFix])
      ⟨b, by simp [initFix]⟩ hread
    rw [← hacc] at hlt
    have hl : gs.length = C.gates.length := by simp [hgs]
    simp only [List.length_nil, zero_add] at hlt
    refine ⟨by omega, ⟨⟨acc.2, j⟩, elim_ok m gs _ (by simp), by simp [Circuit.size]; omega, ?_⟩⟩
    intro x
    have hx := hval x
    rw [hst] at hx
    exact hx

private lemma gate_elim_two (m : ℕ) (f : (Fin m → Bool) → Bool) (p : Fin m) (s : ℕ)
    (hdep : ∃ x : Fin m → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc0 : ∃ x x' : Fin m → Bool, f (Function.update x p false) ≠ f (Function.update x' p false))
    (hnc1 : ∃ x x' : Fin m → Bool, f (Function.update x p true) ≠ f (Function.update x' p true))
    (h : HasCircuitSize m f s) :
    2 ≤ s ∧ (HasCircuitSize m (fun x => f (Function.update x p false)) (s - 2) ∨
             HasCircuitSize m (fun x => f (Function.update x p true)) (s - 2)) := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hl : gs.length = C.gates.length := by simp [hgs]
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin m → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  have hval_b : ∀ (b : Bool) (x : Fin m → Bool),
      ((elim m gs (initFix m p b, [])).1.getD C.output (Sum.inl false)).val
        (wiresFrom (elim m gs (initFix m p b, [])).2 (List.ofFn x)) =
      f (Function.update x p b) := by
    intro b x
    have hinv := inv_elim m (List.ofFn x) (by simp) gs _ _
      (fun g hg => (hnok g hg).1) (inv_initFix m p b x)
    exact ((hinv.2 C.output).2).trans (hevg _)
  have hout_p : C.output ≠ (p : ℕ) := by
    intro e
    have hconst : ∀ x : Fin m → Bool, f (Function.update x p false) = false := by
      intro x
      have hv := hval_b false x
      rw [e, elim_getD m (p : ℕ) _ gs _ (by simp [initFix])] at hv
      have hp : (initFix m p false).getD (p : ℕ) (Sum.inl false) = Sum.inl false := by
        simp [initFix]
      rw [show ((initFix m p false, ([] : List Gate))).1 = initFix m p false from rfl, hp] at hv
      exact hv.symm
    obtain ⟨x, x', hne⟩ := hnc0
    exact hne ((hconst x).trans (hconst x').symm)
  have hread : ∃ g ∈ gs, (p : ℕ) ∈ g.inputs := by
    by_contra! hno
    obtain ⟨x, hx⟩ := hdep
    apply hx
    have hns := supp_noread_set m p {(p : ℕ)} gs (inputSupps m)
      (fun g hg a ha e => hno g hg (by simpa using e ▸ ha))
      (fun j hj => inputSupps_noread_at m p j (by simpa using hj))
      C.output (by simpa using hout_p)
    have hag := (agree_wiresFrom (Function.update x p (!x p)) x gs _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ p := fun e => hns (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hevg, ← hevg]
    exact hag
  by_cases htwo : 2 ≤ gs.countP (fun g => decide ((p : ℕ) ∈ g.inputs))
  · set acc := elim m gs (initFix m p false, []) with hacc
    have hcnt := elim_count m (p : ℕ) false gs (initFix m p false, []) hnok (by simp [initFix])
      (by simp [initFix])
    rw [← hacc] at hcnt
    simp only [List.length_nil, zero_add] at hcnt
    cases hst : acc.1.getD C.output (Sum.inl false) with
    | inl c =>
      exfalso
      obtain ⟨x, x', hne⟩ := hnc0
      apply hne
      rw [← hval_b false x, ← hval_b false x', ← hacc, hst]; rfl
    | inr j =>
      refine ⟨by omega, Or.inl ⟨⟨acc.2, j⟩, elim_ok m gs _ (by simp), by simp [Circuit.size]; omega, ?_⟩⟩
      intro x
      have hx := hval_b false x
      rw [← hacc, hst] at hx
      exact hx
  · obtain ⟨g1, hg1, hpg1⟩ := hread
    obtain ⟨gs1, gs2, hsplit⟩ := List.append_of_mem hg1
    have hcnt1 : gs.countP (fun g => decide ((p : ℕ) ∈ g.inputs)) = 1 := by
      have hpos : 0 < gs.countP (fun g => decide ((p : ℕ) ∈ g.inputs)) := by
        simpa [List.countP_pos_iff] using ⟨g1, hg1, hpg1⟩
      omega
    rw [hsplit, List.countP_append, List.countP_cons, decide_eq_true hpg1] at hcnt1
    simp only [ite_true] at hcnt1
    have hno1 : ∀ g ∈ gs1, (p : ℕ) ∉ g.inputs := by
      intro g hg hpg
      have : 0 < gs1.countP (fun g => decide ((p : ℕ) ∈ g.inputs)) := by
        simpa [List.countP_pos_iff] using ⟨g, hg, hpg⟩
      omega
    have hno2 : ∀ g ∈ gs2, (p : ℕ) ∉ g.inputs := by
      intro g hg hpg
      have : 0 < gs2.countP (fun g => decide ((p : ℕ) ∈ g.inputs)) := by
        simpa [List.countP_pos_iff] using ⟨g, hg, hpg⟩
      omega
    have hnok1 : ∀ g ∈ gs1, NOk g := fun g hg => hnok g (by rw [hsplit]; simp [hg])
    have hnok_g1 : NOk g1 := hnok g1 hg1
    have hnok2 : ∀ g ∈ gs2, NOk g := fun g hg => hnok g (by rw [hsplit]; simp [hg])
    let b : Bool := match g1.op with | GateOp.or => true | _ => false
    have hncb : ∃ x x' : Fin m → Bool, f (Function.update x p b) ≠ f (Function.update x' p b) := by
      cases hb : b
      · exact hnc0
      · exact hnc1
    set acc1 := elim m gs1 (initFix m p b, []) with hacc1
    set acc2 := elimStep m acc1 g1 with hacc2
    set acc := elim m gs2 acc2 with hacc
    have hacceq : acc = elim m gs (initFix m p b, []) := by
      rw [hsplit, elim_append]
      rfl
    set q := m + gs1.length with hq
    have hlen1 : acc1.1.length = q := by
      rw [hacc1, elim_stat_len]
      simp [initFix, hq]
    have hp1 : acc1.1.getD (p : ℕ) (Sum.inl false) = Sum.inl b := by
      rw [hacc1, elim_getD m (p : ℕ) _ gs1 _ (by simp [initFix])]
      simp [initFix]
    have hkill : (simplify g1.op (m + acc1.2.length)
        (g1.inputs.map fun i => acc1.1.getD i (Sum.inl false))).1 = none ∧
        ∃ c, (simplify g1.op (m + acc1.2.length)
        (g1.inputs.map fun i => acc1.1.getD i (Sum.inl false))).2 = Sum.inl c := by
      have hk := simplify_kill g1.op (m + acc1.2.length)
        (g1.inputs.map fun i => acc1.1.getD i (Sum.inl false))
        (by simpa using hnok_g1.1.2) (fun ho => by simpa using hnok_g1.2 ho)
      have hinb : Sum.inl b ∈ g1.inputs.map (fun i => acc1.1.getD i (Sum.inl false)) :=
        List.mem_map.2 ⟨(p : ℕ), hpg1, hp1⟩
      rcases hnok_g1.1.1 with hop | hop | hop
      · have hb : b = false := by simp [b, hop]
        rw [hb] at hinb
        exact hk.2.1 hop hinb
      · have hb : b = true := by simp [b, hop]
        rw [hb] at hinb
        exact hk.2.2 hop hinb
      · have hop' : g1.op = GateOp.not := hop
        have hb : b = false := by simp [b, hop']
        rw [hb] at hinb
        exact hk.1 hop' hinb
    obtain ⟨hnone, c, hc⟩ := hkill
    have hacc2_len : acc2.2.length = acc1.2.length := by
      show (acc1.2 ++ (simplify g1.op (m + acc1.2.length)
        (g1.inputs.map fun i => acc1.1.getD i (Sum.inl false))).1.toList).length = _
      rw [hnone]; simp
    have hacc2_q : acc2.1.getD q (Sum.inl false) = Sum.inl c := by
      show (acc1.1 ++ [(simplify g1.op (m + acc1.2.length)
        (g1.inputs.map fun i => acc1.1.getD i (Sum.inl false))).2]).getD q (Sum.inl false) = _
      rw [getD_snoc_len _ _ _ _ hlen1, hc]
    have hacc2_slen : acc2.1.length = q + 1 := by
      simp [hacc2, elimStep, hlen1]
    have hout_q : C.output ≠ q := by
      intro e
      have hconst : ∀ x : Fin m → Bool, f (Function.update x p b) = c := by
        intro x
        have hv := hval_b b x
        rw [← hacceq, e, hacc, elim_getD m q _ gs2 acc2 (by omega), hacc2_q] at hv
        exact hv.symm
      obtain ⟨x, x', hne⟩ := hncb
      exact hne ((hconst x).trans (hconst x').symm)
    have hread2 : ∃ g2 ∈ gs2, q ∈ g2.inputs := by
      by_contra! hnoq
      obtain ⟨x, hx⟩ := hdep
      apply hx
      set L1 := suppsFrom gs1 (inputSupps m) with hL1
      have hL1len : L1.length = q := by
        rw [hL1, length_suppsFrom]; simp [inputSupps, hq]
      have hns1 : ∀ j : ℕ, j ≠ (p : ℕ) → p ∉ L1.getD j ∅ := by
        intro j hj
        exact supp_noread_set m p {(p : ℕ)} gs1 (inputSupps m)
          (fun g hg a ha e => hno1 g hg (by simpa using e ▸ ha))
          (fun j hj => inputSupps_noread_at m p j (by simpa using hj))
          j (by simpa using hj)
      have hns_mid : ∀ j : ℕ, j ∉ ({(p : ℕ), q} : Set ℕ) →
          p ∉ (L1 ++ [gateSupp L1 g1]).getD j ∅ := by
        intro j hj
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hj
        rw [getD_snoc_ne _ _ _ _ (by omega)]
        exact hns1 j hj.1
      have hns2 : p ∉ (suppsFrom gs (inputSupps m)).getD C.output ∅ := by
        rw [hsplit, suppsFrom_append]
        change p ∉ (suppsFrom gs2 (L1 ++ [gateSupp L1 g1])).getD C.output ∅
        apply supp_noread_set m p ({(p : ℕ), q} : Set ℕ) gs2 (L1 ++ [gateSupp L1 g1])
        · intro g hg a ha hm
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
          rcases hm with rfl | rfl
          · exact hno2 g hg ha
          · exact hnoq g hg ha
        · exact hns_mid
        · simp [hout_p, hout_q]
      have hag := (agree_wiresFrom (Function.update x p (!x p)) x gs _ _ _
        (agree_inputs _ _)).2.2 C.output (by
          intro k hk
          have : k ≠ p := fun e => hns2 (e ▸ hk)
          simp [Function.update_of_ne this])
      rw [← hevg, ← hevg]
      exact hag
    have hlt2 := elim_len_lt m q gs2 acc2 hnok2 (by omega) ⟨c, hacc2_q⟩ hread2
    have hle1 := elim_len m gs1 (initFix m p b, [])
    rw [← hacc1] at hle1
    rw [← hacc] at hlt2
    simp only [List.length_nil, zero_add] at hle1
    have hgslen : gs.length = gs1.length + 1 + gs2.length := by
      rw [hsplit]; simp; omega
    have h2 : acc.2.length + 2 ≤ s := by omega
    cases hst : acc.1.getD C.output (Sum.inl false) with
    | inl d =>
      exfalso
      obtain ⟨x, x', hne⟩ := hncb
      apply hne
      rw [← hval_b b x, ← hval_b b x', ← hacceq, hst]; rfl
    | inr j =>
      have hcirc : HasCircuitSize m (fun x => f (Function.update x p b)) (s - 2) := by
        refine ⟨⟨acc.2, j⟩, ?_, by simp [Circuit.size]; omega, ?_⟩
        · rw [hacceq]; exact elim_ok m gs _ (by simp)
        · intro x
          have hx := hval_b b x
          rw [← hacceq, hst] at hx
          exact hx
      refine ⟨by omega, ?_⟩
      cases hb : b
      · left; rw [hb] at hcirc; exact hcirc
      · right; rw [hb] at hcirc; exact hcirc

def chainOr (m acc : ℕ) : List ℕ → List Gate × ℕ
  | [] => ([], acc)
  | w :: ws =>
    let r := chainOr (m + 1) m ws
    (⟨GateOp.or, [acc, w]⟩ :: r.1, r.2)

private lemma chainOr_len (m acc : ℕ) (ws : List ℕ) :
    (chainOr m acc ws).1.length = ws.length := by
  induction ws generalizing m acc with
  | nil => rfl
  | cons w ws ih => simp [chainOr, ih]

private lemma chainOr_ok (m acc : ℕ) (ws : List ℕ) :
    ∀ g ∈ (chainOr m acc ws).1, Ok g := by
  induction ws generalizing m acc with
  | nil => intro g hg; simp [chainOr] at hg
  | cons w ws ih =>
    intro g hg
    simp only [chainOr, List.mem_cons] at hg
    rcases hg with rfl | hg
    · simp [Ok]
    · exact ih (m + 1) m g hg

private lemma chainOr_out_lt (m acc : ℕ) (ws : List ℕ) (hacc : acc < m) :
    (chainOr m acc ws).2 < m + ws.length := by
  induction ws generalizing m acc with
  | nil => simpa [chainOr] using hacc
  | cons w ws ih =>
    simp only [chainOr, List.length_cons]
    have := ih (m + 1) m (by omega)
    omega

private lemma chainOr_eval (m acc : ℕ) (ws : List ℕ) :
    ∀ (W : List Bool), W.length = m → acc < m → (∀ w ∈ ws, w < m) →
      (wiresFrom (chainOr m acc ws).1 W).getD (chainOr m acc ws).2 false =
        (W.getD acc false || decide (∃ w ∈ ws, W.getD w false = true)) := by
  induction ws generalizing m acc with
  | nil =>
    intro W _ _ _
    simp [chainOr, wiresFrom]
  | cons w ws ih =>
    intro W hW hacc hws
    have hw : w < m := hws w List.mem_cons_self
    have hws' : ∀ u ∈ ws, u < m + 1 := fun u hu => by
      have := hws u (List.mem_cons_of_mem _ hu); omega
    let g0 : Gate := ⟨GateOp.or, [acc, w]⟩
    let W1 := W ++ [W.getD acc false || W.getD w false]
    have hstep : wiresFrom (chainOr m acc (w :: ws)).1 W =
        wiresFrom (chainOr (m + 1) m ws).1 W1 := by
      show wiresFrom (g0 :: (chainOr (m + 1) m ws).1) W = _
      change wiresFrom (chainOr (m + 1) m ws).1
        (W ++ [GateOp.or.eval ([acc, w].map fun i => W.getD i false)]) = _
      simp [W1, GateOp.eval]
    rw [hstep]
    change (wiresFrom (chainOr (m + 1) m ws).1 W1).getD (chainOr (m + 1) m ws).2 false = _
    rw [ih (m + 1) m W1 (by simp [W1, hW]) (by omega) hws']
    have hm1 : W1.getD m false = (W.getD acc false || W.getD w false) := by
      exact getD_snoc_len W _ false m hW
    have hmem : (∃ u ∈ ws, W1.getD u false = true) ↔ (∃ u ∈ ws, W.getD u false = true) := by
      constructor <;> rintro ⟨u, hu, hval⟩
      · refine ⟨u, hu, ?_⟩
        have hu' : u < W.length := by have := hws u (List.mem_cons_of_mem _ hu); omega
        rwa [List.getD_append _ _ _ _ hu'] at hval
      · refine ⟨u, hu, ?_⟩
        have hu' : u < W.length := by have := hws u (List.mem_cons_of_mem _ hu); omega
        rwa [List.getD_append _ _ _ _ hu']
    rw [hm1]
    apply Bool.eq_iff_iff.2
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_cons]
    constructor
    · rintro ((h1 | h2) | h3)
      · exact Or.inl h1
      · exact Or.inr ⟨w, Or.inl rfl, h2⟩
      · obtain ⟨u, hu, hval⟩ := hmem.1 h3
        exact Or.inr ⟨u, Or.inr hu, hval⟩
    · rintro (h1 | ⟨u, rfl | hu, hval⟩)
      · exact Or.inl (Or.inl h1)
      · exact Or.inl (Or.inr hval)
      · exact Or.inr (hmem.2 ⟨u, hu, hval⟩)

noncomputable def addCoverVerts {n : ℕ} (N : Fin n → Finset (Fin n)) (m acc : ℕ) :
    List (Fin n) → List Gate × ℕ
  | [] => ([], acc)
  | u :: us =>
    match (N u).toList with
    | [] => addCoverVerts N m acc us
    | v0 :: vs =>
      let c1 := chainOr m (v0 : ℕ) (vs.map (fun v : Fin n => (v : ℕ)))
      let m1 := m + vs.length
      let gAnd : Gate := ⟨GateOp.and, [(u : ℕ), c1.2]⟩
      let gOr : Gate := ⟨GateOp.or, [acc, m1]⟩
      let rest := addCoverVerts N (m1 + 2) (m1 + 1) us
      (c1.1 ++ [gAnd, gOr] ++ rest.1, rest.2)

private lemma addCoverVerts_ok {n : ℕ} (N : Fin n → Finset (Fin n)) (m acc : ℕ)
    (us : List (Fin n)) : ∀ g ∈ (addCoverVerts N m acc us).1, Ok g := by
  induction us generalizing m acc with
  | nil => intro g hg; simp [addCoverVerts] at hg
  | cons u us ih =>
    intro g hg
    unfold addCoverVerts at hg
    cases hNu : (N u).toList with
    | nil =>
      rw [hNu] at hg
      exact ih m acc g hg
    | cons v0 vs =>
      rw [hNu] at hg
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with (hg | rfl | rfl) | hg
      · exact chainOr_ok _ _ _ g hg
      · simp [Ok]
      · simp [Ok]
      · exact ih _ _ g hg

private lemma addCoverVerts_len {n : ℕ} (N : Fin n → Finset (Fin n)) (m acc : ℕ)
    (us : List (Fin n)) :
    (addCoverVerts N m acc us).1.length ≤ (us.map (fun u => (N u).card + 1)).sum := by
  induction us generalizing m acc with
  | nil => simp [addCoverVerts]
  | cons u us ih =>
    unfold addCoverVerts
    cases hNu : (N u).toList with
    | nil =>
      have := ih m acc
      simp only [List.map_cons, List.sum_cons]
      omega
    | cons v0 vs =>
      have hcard : (N u).card = vs.length + 1 := by
        have h1 : (N u).toList.length = (N u).card := Finset.length_toList (N u)
        rw [hNu, List.length_cons] at h1
        exact h1.symm
      have hrest := ih (m + vs.length + 2) (m + vs.length + 1)
      simp only [List.length_append, List.length_cons, List.length_nil, chainOr_len,
        List.length_map, List.map_cons, List.sum_cons]
      omega

private lemma addCoverVerts_eval {n : ℕ} (N : Fin n → Finset (Fin n)) (m acc : ℕ)
    (us : List (Fin n)) :
    ∀ (W : List Bool), W.length = m → n ≤ m → acc < m →
      (wiresFrom (addCoverVerts N m acc us).1 W).getD (addCoverVerts N m acc us).2 false =
        (W.getD acc false ||
          decide (∃ u ∈ us, W.getD (u : ℕ) false = true ∧ ∃ v ∈ N u, W.getD (v : ℕ) false = true)) := by
  induction us generalizing m acc with
  | nil =>
    intro W _ _ _
    simp [addCoverVerts, wiresFrom]
  | cons u us ih =>
    intro W hW hnm hacc
    unfold addCoverVerts
    cases hNu : (N u).toList with
    | nil =>
      have hNe : N u = ∅ := by
        rw [← Finset.toList_eq_nil]
        exact hNu
      rw [ih m acc W hW hnm hacc]
      have heq : (∃ u' ∈ u :: us, W.getD (u' : ℕ) false = true ∧ ∃ v ∈ N u', W.getD (v : ℕ) false = true) ↔
          (∃ u' ∈ us, W.getD (u' : ℕ) false = true ∧ ∃ v ∈ N u', W.getD (v : ℕ) false = true) := by
        constructor
        · rintro ⟨u', hu', h1, v, hv, h2⟩
          rcases List.mem_cons.1 hu' with rfl | hu'
          · simp [hNe] at hv
          · exact ⟨u', hu', h1, v, hv, h2⟩
        · rintro ⟨u', hu', h1, v, hv, h2⟩
          exact ⟨u', List.mem_cons_of_mem _ hu', h1, v, hv, h2⟩
      rw [decide_eq_decide.2 heq]
    | cons v0 vs =>
      set c1 := chainOr m (v0 : ℕ) (vs.map (fun v : Fin n => (v : ℕ))) with hc1
      set m1 := m + vs.length with hm1
      set gAnd : Gate := ⟨GateOp.and, [(u : ℕ), c1.2]⟩ with hgAnd
      set gOr : Gate := ⟨GateOp.or, [acc, m1]⟩ with hgOr
      set rest := addCoverVerts N (m1 + 2) (m1 + 1) us with hrest
      show (wiresFrom (c1.1 ++ [gAnd, gOr] ++ rest.1) W).getD rest.2 false = _
      rw [wiresFrom_append, wiresFrom_append]
      set W1 := wiresFrom c1.1 W with hW1
      set W2 := wiresFrom [gAnd, gOr] W1 with hW2
      have lW1 : W1.length = m1 := by
        rw [hW1, length_wiresFrom, hW, hc1, chainOr_len, List.length_map]
      have lW2 : W2.length = m1 + 2 := by
        rw [hW2, length_wiresFrom, lW1]; simp
      have hc1_eval : W1.getD c1.2 false = decide (∃ v ∈ N u, W.getD (v : ℕ) false = true) := by
        rw [hW1, hc1, chainOr_eval m (v0 : ℕ) _ W hW (by have := v0.isLt; omega)
          (by intro w hw; obtain ⟨v, _, rfl⟩ := List.mem_map.1 hw; have := v.isLt; omega)]
        have hmem_v : ∀ v : Fin n, v ∈ N u ↔ v = v0 ∨ v ∈ vs := by
          intro v
          rw [← Finset.mem_toList, hNu, List.mem_cons]
        apply Bool.eq_iff_iff.2
        simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_map]
        constructor
        · rintro (h0 | ⟨w, ⟨v, hv, rfl⟩, hval⟩)
          · exact ⟨v0, (hmem_v v0).2 (Or.inl rfl), h0⟩
          · exact ⟨v, (hmem_v v).2 (Or.inr hv), hval⟩
        · rintro ⟨v, hv, hval⟩
          rcases (hmem_v v).1 hv with rfl | hv'
          · exact Or.inl hval
          · exact Or.inr ⟨(v : ℕ), ⟨v, hv', rfl⟩, hval⟩
      have hW1_lt : ∀ i, i < m → W1.getD i false = W.getD i false := fun i hi => by
        rw [hW1, getD_wiresFrom _ _ _ (by omega)]
      have hW2_lt : ∀ i, i < m → W2.getD i false = W.getD i false := fun i hi => by
        rw [hW2, getD_wiresFrom _ _ _ (by omega), hW1_lt i hi]
      have hW2_acc : W2.getD (m1 + 1) false =
          (W.getD acc false || (W.getD (u : ℕ) false && decide (∃ v ∈ N u, W.getD (v : ℕ) false = true))) := by
        have hAnd : wiresFrom [gAnd] W1 = W1 ++ [W.getD (u : ℕ) false && decide (∃ v ∈ N u, W.getD (v : ℕ) false = true)] := by
          show W1 ++ [GateOp.and.eval ([(u : ℕ), c1.2].map fun i => W1.getD i false)] = _
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
            id_eq, Bool.and_true]
          rw [hW1_lt (u : ℕ) (by have := u.isLt; omega), hc1_eval]
        have hW2eq : W2 = wiresFrom [gOr] (wiresFrom [gAnd] W1) := by
          rw [hW2]
          exact wiresFrom_append [gAnd] [gOr] W1
        rw [hW2eq, hAnd]
        set W1' := W1 ++ [W.getD (u : ℕ) false && decide (∃ v ∈ N u, W.getD (v : ℕ) false = true)]
        have lW1' : W1'.length = m1 + 1 := by simp [W1', lW1]
        have hOr : wiresFrom [gOr] W1' =
            W1' ++ [W1'.getD acc false || W1'.getD m1 false] := by
          show W1' ++ [GateOp.or.eval ([acc, m1].map fun i => W1'.getD i false)] = _
          simp [GateOp.eval]
        rw [hOr, getD_snoc_len _ _ _ _ lW1']
        have ha1 : W1'.getD acc false = W.getD acc false := by
          rw [List.getD_append _ _ _ _ (by omega), hW1_lt acc hacc]
        have hm1' : W1'.getD m1 false = (W.getD (u : ℕ) false && decide (∃ v ∈ N u, W.getD (v : ℕ) false = true)) :=
          getD_snoc_len _ _ _ _ lW1
        rw [ha1, hm1']
      rw [ih (m1 + 2) (m1 + 1) W2 lW2 (by omega) (by omega), hW2_acc]
      have hrest_eq : (∃ u' ∈ us, W2.getD (u' : ℕ) false = true ∧ ∃ v ∈ N u', W2.getD (v : ℕ) false = true) ↔
          (∃ u' ∈ us, W.getD (u' : ℕ) false = true ∧ ∃ v ∈ N u', W.getD (v : ℕ) false = true) := by
        constructor <;> rintro ⟨u', hu', h1, v, hv, h2⟩
        · exact ⟨u', hu', by rwa [hW2_lt _ (by have := u'.isLt; omega)] at h1,
            v, hv, by rwa [hW2_lt _ (by have := v.isLt; omega)] at h2⟩
        · exact ⟨u', hu', by rwa [hW2_lt _ (by have := u'.isLt; omega)],
            v, hv, by rwa [hW2_lt _ (by have := v.isLt; omega)]⟩
      apply Bool.eq_iff_iff.2
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.mem_cons]
      constructor
      · rintro ((ha | ⟨hu, hv⟩) | h2)
        · exact Or.inl ha
        · exact Or.inr ⟨u, Or.inl rfl, hu, hv⟩
        · obtain ⟨u', hu', h1, v, hv, h2'⟩ := hrest_eq.1 h2
          exact Or.inr ⟨u', Or.inr hu', h1, v, hv, h2'⟩
      · rintro (ha | ⟨u', rfl | hu', h1, v, hv, h2'⟩)
        · exact Or.inl (Or.inl ha)
        · exact Or.inl (Or.inr ⟨h1, v, hv, h2'⟩)
        · exact Or.inr (hrest_eq.2 ⟨u', hu', h1, v, hv, h2'⟩)

def forestFn (n k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (g : (Fin k → Bool) → Bool) (x : Fin (n + k) → Bool) : Bool :=
  decide ((∃ a ∈ A, x (Fin.castAdd k a) = true) ∨
    ∃ u v : Fin n, G.Adj u v ∧ x (Fin.castAdd k u) = true ∧ x (Fin.castAdd k v) = true) ||
    g (fun j : Fin k => x (Fin.natAdd n j))

private lemma upper_bound (n k c t s : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (g : (Fin k → Bool) → Bool)
    (hgnc : ∃ y y' : Fin k → Bool, g y ≠ g y')
    (hgc : HasCircuitSize k g c)
    (hcover : ∃ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S) ∧ S.card = t)
    (hs : A.card + G.edgeFinset.card + t + c ≤ s) :
    HasCircuitSize (n + k) (forestFn n k G A g) s := by
  obtain ⟨S, hScov, hScard⟩ := hcover
  obtain ⟨C0, ok0, hsz0, hev0⟩ := relabel_size (Fin.natAdd n) g c hgc
  have hsz0' : C0.gates.length ≤ c := hsz0
  set m0 := n + k + C0.gates.length with hm0
  have hout0 : C0.output < m0 := by
    by_contra hge
    push Not at hge
    obtain ⟨y, y', hne⟩ := hgnc
    apply hne
    have hconst : ∀ z : Fin k → Bool, g z = false := by
      intro z
      have hz : C0.eval (List.ofFn (padFalse n k z)) = g (fun j => padFalse n k z (Fin.natAdd n j)) :=
        hev0 (padFalse n k z)
      have he : (fun j : Fin k => padFalse n k z (Fin.natAdd n j)) = z := by
        funext j; exact padFalse_natAdd n k z j
      rw [he] at hz
      rw [← hz, Circuit.eval, wires_eq]
      exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)
    exact (hconst y).trans (hconst y').symm
  let cA := chainOr m0 C0.output (A.toList.map (fun a : Fin n => (a : ℕ)))
  let m1 := m0 + A.card
  have hcA_len : cA.1.length = A.card := by
    simp [cA, chainOr_len]
  have hcA_out : cA.2 < m1 := by
    have := chainOr_out_lt m0 C0.output (A.toList.map (fun a : Fin n => (a : ℕ))) hout0
    simpa [cA, m1] using this
  let N : Fin n → Finset (Fin n) := fun u =>
    Finset.univ.filter (fun v : Fin n => G.Adj u v ∧ (v ∉ S ∨ u < v))
  have hNsum : ∑ u ∈ S, (N u).card = G.edgeFinset.card := by
    rw [← Finset.card_sigma]
    refine Finset.card_bij (fun p _ => s(p.1, p.2)) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and, N] at hp
      rw [SimpleGraph.mem_edgeFinset]
      exact hp.2.1
    · intro p1 hp1 p2 hp2 heq
      rcases p1 with ⟨u1, v1⟩
      rcases p2 with ⟨u2, v2⟩
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and, N] at hp1 hp2
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Sigma.ext h1 (heq_of_eq h2)
      · exfalso
        subst h1; subst h2
        rcases hp1.2.2 with hnot | hlt
        · exact hnot hp2.1
        · rcases hp2.2.2 with hnot2 | hlt2
          · exact hnot2 hp1.1
          · exact lt_asymm hlt hlt2
    · intro e he
      induction e using Sym2.ind with
      | _ u v =>
        rw [SimpleGraph.mem_edgeFinset] at he
        have huv : G.Adj u v := he
        have hne : u ≠ v := G.ne_of_adj huv
        rcases hScov u v huv with hu | hv
        · by_cases hvS : v ∈ S
          · rcases lt_or_gt_of_ne hne with hlt | hgt
            · exact ⟨⟨u, v⟩, by simp [N, hu, huv, hlt], rfl⟩
            · exact ⟨⟨v, u⟩, by simp [N, hvS, huv.symm, hgt], Sym2.eq_swap⟩
          · exact ⟨⟨u, v⟩, by simp [N, hu, huv, hvS], rfl⟩
        · by_cases huS : u ∈ S
          · rcases lt_or_gt_of_ne hne with hlt | hgt
            · exact ⟨⟨u, v⟩, by simp [N, huS, huv, hlt], rfl⟩
            · exact ⟨⟨v, u⟩, by simp [N, hv, huv.symm, hgt], Sym2.eq_swap⟩
          · exact ⟨⟨v, u⟩, by simp [N, hv, huv.symm, huS], Sym2.eq_swap⟩
  let cS := addCoverVerts N m1 cA.2 S.toList
  have hcS_len : cS.1.length ≤ G.edgeFinset.card + t := by
    have h1 := addCoverVerts_len N m1 cA.2 S.toList
    have h2 : (S.toList.map (fun u => (N u).card + 1)).sum = ∑ u ∈ S, ((N u).card + 1) := by
      rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
      rfl
    rw [h2, Finset.sum_add_distrib, hNsum, Finset.sum_const, smul_eq_mul, mul_one, hScard] at h1
    exact h1
  refine ⟨⟨C0.gates ++ cA.1 ++ cS.1, cS.2⟩, ?_, ?_, ?_⟩
  · intro gt hgt
    simp only [List.mem_append] at hgt
    rcases hgt with (hgt | hgt) | hgt
    · exact ok0 gt hgt
    · exact chainOr_ok _ _ _ gt hgt
    · exact addCoverVerts_ok N _ _ _ gt hgt
  · simp only [Circuit.size, List.length_append, hcA_len]
    omega
  · intro x
    rw [Circuit.eval, wires_eq, wiresFrom_append, wiresFrom_append]
    set W0 := wiresFrom C0.gates (List.ofFn x) with hW0
    set W1 := wiresFrom cA.1 W0 with hW1
    have lW0 : W0.length = m0 := by rw [hW0, length_wiresFrom]; simp [hm0]
    have lW1 : W1.length = m1 := by rw [hW1, length_wiresFrom, lW0, hcA_len]
    have hW0_inp : ∀ v : Fin n, W0.getD (v : ℕ) false = x (Fin.castAdd k v) := by
      intro v
      rw [hW0, getD_wiresFrom _ _ _ (by simp; have := v.isLt; omega)]
      simp [Fin.castAdd, show (v : ℕ) < n + k by have := v.isLt; omega]
      rfl
    have hW1_inp : ∀ v : Fin n, W1.getD (v : ℕ) false = x (Fin.castAdd k v) := by
      intro v
      rw [hW1, getD_wiresFrom _ _ _ (by have := v.isLt; omega), hW0_inp v]
    have hW0_out : W0.getD C0.output false = g (fun j => x (Fin.natAdd n j)) := hev0 x
    have hW1_out : W1.getD cA.2 false =
        (g (fun j => x (Fin.natAdd n j)) || decide (∃ a ∈ A, x (Fin.castAdd k a) = true)) := by
      rw [hW1]
      dsimp only [cA]
      rw [chainOr_eval m0 C0.output _ W0 lW0 hout0
        (by intro w hw; obtain ⟨a, _, rfl⟩ := List.mem_map.1 hw; have := a.isLt; omega), hW0_out]
      congr 1
      apply decide_eq_decide.2
      constructor
      · rintro ⟨w, hw, hval⟩
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hw
        exact ⟨a, Finset.mem_toList.1 ha, by rwa [hW0_inp a] at hval⟩
      · rintro ⟨a, ha, hval⟩
        exact ⟨(a : ℕ), List.mem_map.2 ⟨a, Finset.mem_toList.2 ha, rfl⟩, by rwa [hW0_inp a]⟩
    dsimp only [cS]
    rw [addCoverVerts_eval N m1 cA.2 S.toList W1 lW1 (by omega) hcA_out, hW1_out]
    have hedge_iff : (∃ u ∈ S.toList, W1.getD (u : ℕ) false = true ∧
        ∃ v ∈ N u, W1.getD (v : ℕ) false = true) ↔
        (∃ u v : Fin n, G.Adj u v ∧ x (Fin.castAdd k u) = true ∧ x (Fin.castAdd k v) = true) := by
      constructor
      · rintro ⟨u, _, hu, v, hv, hvx⟩
        simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at hv
        rw [hW1_inp u] at hu
        rw [hW1_inp v] at hvx
        exact ⟨u, v, hv.1, hu, hvx⟩
      · rintro ⟨u, v, huv, hux, hvx⟩
        have hne : u ≠ v := G.ne_of_adj huv
        rcases hScov u v huv with huS | hvS
        · by_cases hvS : v ∈ S
          · rcases lt_or_gt_of_ne hne with hlt | hgt
            · exact ⟨u, Finset.mem_toList.2 huS, by rwa [hW1_inp u],
                v, by simp [N, huv, hlt], by rwa [hW1_inp v]⟩
            · exact ⟨v, Finset.mem_toList.2 hvS, by rwa [hW1_inp v],
                u, by simp [N, huv.symm, hgt], by rwa [hW1_inp u]⟩
          · exact ⟨u, Finset.mem_toList.2 huS, by rwa [hW1_inp u],
              v, by simp [N, huv, hvS], by rwa [hW1_inp v]⟩
        · by_cases huS : u ∈ S
          · rcases lt_or_gt_of_ne hne with hlt | hgt
            · exact ⟨u, Finset.mem_toList.2 huS, by rwa [hW1_inp u],
                v, by simp [N, huv, hlt], by rwa [hW1_inp v]⟩
            · exact ⟨v, Finset.mem_toList.2 hvS, by rwa [hW1_inp v],
                u, by simp [N, huv.symm, hgt], by rwa [hW1_inp u]⟩
          · exact ⟨v, Finset.mem_toList.2 hvS, by rwa [hW1_inp v],
              u, by simp [N, huv.symm, huS], by rwa [hW1_inp u]⟩
    unfold forestFn
    apply Bool.eq_iff_iff.2
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro ((hg | hA) | hE)
      · exact Or.inr hg
      · exact Or.inl (Or.inl hA)
      · exact Or.inl (Or.inr (hedge_iff.1 hE))
    · rintro ((hA | hE) | hg)
      · exact Or.inl (Or.inr hA)
      · exact Or.inr (hedge_iff.2 hE)
      · exact Or.inl (Or.inl hg)

private lemma acyclic_no_shortcut {n : ℕ} (G : SimpleGraph (Fin n)) (hacyc : G.IsAcyclic)
    (u p1 v : Fin n) (h1 : G.Adj u p1) (p' : G.Walk p1 v)
    (hpath : (SimpleGraph.Walk.cons h1 p').IsPath)
    (z : Fin n) (hz : G.Adj u z) (hzne : z ≠ p1) : z ∉ p'.support := by
  intro hzmem
  have hup' : u ∉ p'.support := by
    have hnd := hpath.support_nodup
    simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at hnd
    exact hnd.1
  have hp' : p'.IsPath := hpath.of_cons
  let r : G.Walk p1 z := p'.takeUntil z hzmem
  have hr_path : r.IsPath := hp'.takeUntil hzmem
  have hu_r : u ∉ r.support := fun h => hup' (SimpleGraph.Walk.support_takeUntil_subset_support p' hzmem h)
  let q : G.Walk u z := SimpleGraph.Walk.cons h1 r
  have hq_path : q.IsPath := SimpleGraph.Walk.IsPath.cons hr_path hu_r
  have hnot_edge : s(u, z) ∉ q.edges := by
    simp only [q, SimpleGraph.Walk.edges_cons, List.mem_cons, not_or]
    constructor
    · intro heq
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨_, h2⟩ | ⟨h1', _⟩
      · exact hzne h2
      · exact G.ne_of_adj h1 h1'
    · intro hmem
      exact hu_r (SimpleGraph.Walk.fst_mem_support_of_mem_edges r hmem)
  have hcyc : (SimpleGraph.Walk.cons hz.symm q).IsCycle := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · refine ⟨?_⟩
      simp only [SimpleGraph.Walk.edges_cons, List.nodup_cons]
      exact ⟨by rw [Sym2.eq_swap]; exact hnot_edge, hq_path.isTrail.edges_nodup⟩
    · intro h; cases h
    · simpa using hq_path.support_nodup
  exact hacyc (SimpleGraph.Walk.cons hz.symm q) hcyc

private lemma max_path_start_leaf {n : ℕ} (G : SimpleGraph (Fin n)) (hacyc : G.IsAcyclic)
    (L : ℕ) (hmax : ∀ (a b : Fin n) (q : G.Walk a b), q.IsPath → q.length ≤ L)
    (u p1 v : Fin n) (h1 : G.Adj u p1) (p' : G.Walk p1 v)
    (hpath : (SimpleGraph.Walk.cons h1 p').IsPath) (hlen : (SimpleGraph.Walk.cons h1 p').length = L) :
    ∀ z : Fin n, G.Adj u z → z = p1 := by
  intro z hz
  by_contra hzne
  have hnotp' := acyclic_no_shortcut G hacyc u p1 v h1 p' hpath z hz hzne
  have hnotp : z ∉ (SimpleGraph.Walk.cons h1 p').support := by
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons, not_or]
    exact ⟨(G.ne_of_adj hz).symm, hnotp'⟩
  have hq : (SimpleGraph.Walk.cons hz.symm (SimpleGraph.Walk.cons h1 p')).IsPath :=
    SimpleGraph.Walk.IsPath.cons hpath hnotp
  have hle := hmax z v _ hq
  simp only [SimpleGraph.Walk.length_cons] at hle hlen
  omega

private lemma forest_leaf_structure {n : ℕ} (G : SimpleGraph (Fin n)) (hacyc : G.IsAcyclic)
    (hedge : ∃ a b : Fin n, G.Adj a b) :
    ∃ (w u : Fin n), G.Adj w u ∧ (∀ z : Fin n, G.Adj w z → z = u) ∧
      ((∃ w' : Fin n, w' ≠ w ∧ G.Adj w' u ∧ ∀ z : Fin n, G.Adj w' z → z = u) ∨
       (∀ v1 v2 : Fin n, G.Adj u v1 → G.Adj u v2 → v1 ≠ w → v2 ≠ w → v1 = v2)) := by
  classical
  let P : ℕ → Prop := fun len => ∃ (a b : Fin n) (p : G.Walk a b), p.IsPath ∧ p.length = len
  have hP1 : P 1 := by
    obtain ⟨a, b, hab⟩ := hedge
    refine ⟨a, b, SimpleGraph.Walk.cons hab SimpleGraph.Walk.nil, ?_, rfl⟩
    exact SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil (by simp [G.ne_of_adj hab])
  have hPbound : ∀ len, P len → len ≤ n := by
    rintro len ⟨a, b, p, hp, rfl⟩
    have h1 : p.support.length ≤ Fintype.card (Fin n) := hp.support_nodup.length_le_card
    rw [SimpleGraph.Walk.length_support, Fintype.card_fin] at h1
    omega
  let L := Nat.findGreatest P n
  have hL1 : 1 ≤ L := Nat.le_findGreatest (hPbound 1 hP1) hP1
  have hPL : P L := Nat.findGreatest_spec (show 0 ≤ n by omega) (by
    obtain ⟨a, b, _⟩ := hedge
    exact ⟨a, a, SimpleGraph.Walk.nil, SimpleGraph.Walk.IsPath.nil, rfl⟩)
  have hmax : ∀ (a b : Fin n) (q : G.Walk a b), q.IsPath → q.length ≤ L := by
    intro a b q hq
    exact Nat.le_findGreatest (hPbound q.length ⟨a, b, q, hq, rfl⟩) ⟨a, b, q, hq, rfl⟩
  obtain ⟨u0, v, p, hp, hplen⟩ := hPL
  cases p with
  | nil =>
    simp at hplen
    omega
  | cons h1 p' =>
    rename_i u1
    have hu0_leaf : ∀ z : Fin n, G.Adj u0 z → z = u1 :=
      max_path_start_leaf G hacyc L hmax u0 u1 v h1 p' hp hplen
    refine ⟨u0, u1, h1, hu0_leaf, ?_⟩
    cases p' with
    | nil =>
      right
      intro v1 v2 hv1 _ hv1ne _
      exfalso
      have hnot : v1 ∉ (SimpleGraph.Walk.cons h1 SimpleGraph.Walk.nil).support := by
        simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
          List.not_mem_nil, or_false, not_or]
        exact ⟨hv1ne, (G.ne_of_adj hv1).symm⟩
      have hp2 : (SimpleGraph.Walk.cons hv1.symm
          (SimpleGraph.Walk.cons h1.symm SimpleGraph.Walk.nil)).IsPath := by
        apply SimpleGraph.Walk.IsPath.cons
        · exact SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil
            (by simp [(G.ne_of_adj h1).symm])
        · simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
            List.not_mem_nil, or_false, not_or]
          exact ⟨(G.ne_of_adj hv1).symm, hv1ne⟩
      have hle := hmax v1 u0 _ hp2
      simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hle hplen
      omega
    | cons h2 p'' =>
      rename_i u2
      by_cases hex : ∃ q : Fin n, G.Adj u1 q ∧ q ≠ u0 ∧ q ≠ u2
      · left
        obtain ⟨q, hq, hqu0, hqu2⟩ := hex
        have hp' : (SimpleGraph.Walk.cons h2 p'').IsPath := hp.of_cons
        have hnotp'' := acyclic_no_shortcut G hacyc u1 u2 v h2 p'' hp' q hq hqu2
        have hnotp' : q ∉ (SimpleGraph.Walk.cons h2 p'').support := by
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons, not_or]
          exact ⟨(G.ne_of_adj hq).symm, hnotp''⟩
        have hqpath : (SimpleGraph.Walk.cons hq.symm (SimpleGraph.Walk.cons h2 p'')).IsPath :=
          SimpleGraph.Walk.IsPath.cons hp' hnotp'
        have hqlen : (SimpleGraph.Walk.cons hq.symm (SimpleGraph.Walk.cons h2 p'')).length = L := by
          simpa using hplen
        have hqleaf : ∀ z : Fin n, G.Adj q z → z = u1 :=
          max_path_start_leaf G hacyc L hmax q u1 v hq.symm (SimpleGraph.Walk.cons h2 p'') hqpath hqlen
        exact ⟨q, hqu0, hq.symm, hqleaf⟩
      · right
        push Not at hex
        intro v1 v2 hv1 hv2 hv1ne hv2ne
        exact (hex v1 hv1 hv1ne).trans (hex v2 hv2 hv2ne).symm

private lemma lower_bound_aux (n k c : ℕ) (g : (Fin k → Bool) → Bool)
    (hgnc : ∃ y y' : Fin k → Bool, g y ≠ g y')
    (hgc : ∀ r : ℕ, HasCircuitSize k g r → c ≤ r) :
    ∀ (M : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (t s : ℕ),
      2 * G.edgeFinset.card + A.card = M →
      G.IsAcyclic →
      (∀ a ∈ A, ∀ v : Fin n, ¬ G.Adj a v) →
      (∀ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S) → t ≤ S.card) →
      HasCircuitSize (n + k) (forestFn n k G A g) s →
      A.card + G.edgeFinset.card + t + c ≤ s := by
  intro M
  induction M using Nat.strong_induction_on with
  | ind M ih =>
    intro G _ A t s hM hacyc hiso hvc hcirc
    obtain ⟨y0, y1, hyne⟩ := hgnc
    have hy_split : (∃ y : Fin k → Bool, g y = false) ∧ (∃ y : Fin k → Bool, g y = true) := by
      cases h0 : g y0 <;> cases h1 : g y1
      · exact absurd (h0.trans h1.symm) hyne
      · exact ⟨⟨y0, h0⟩, ⟨y1, h1⟩⟩
      · exact ⟨⟨y1, h1⟩, ⟨y0, h0⟩⟩
      · exact absurd (h0.trans h1.symm) hyne
    obtain ⟨⟨yf, hyf⟩, ⟨yt, hyt⟩⟩ := hy_split
    by_cases hA : A.Nonempty
    · obtain ⟨a, ha⟩ := hA
      let A' := A.erase a
      have hA'card : A'.card + 1 = A.card := Finset.card_erase_add_one ha
      have hfun_eq : (fun x : Fin (n + k) → Bool =>
          forestFn n k G A g (Function.update x (Fin.castAdd k a) false)) = forestFn n k G A' g := by
        funext x
        unfold forestFn
        congr 1
        · apply decide_eq_decide.2
          constructor
          · rintro (⟨b, hb, hbx⟩ | ⟨u, v, huv, hux, hvx⟩)
            · left
              have hba : b ≠ a := by
                intro e
                subst e
                simp at hbx
              refine ⟨b, Finset.mem_erase.2 ⟨hba, hb⟩, ?_⟩
              have hne : Fin.castAdd k b ≠ Fin.castAdd k a := fun e =>
                hba (Fin.castAdd_injective n k e)
              rwa [Function.update_of_ne hne] at hbx
            · right
              have hua : u ≠ a := fun e => hiso a ha v (e ▸ huv)
              have hva : v ≠ a := fun e => hiso a ha u (e ▸ huv.symm)
              have hu' : Fin.castAdd k u ≠ Fin.castAdd k a := fun e =>
                hua (Fin.castAdd_injective n k e)
              have hv' : Fin.castAdd k v ≠ Fin.castAdd k a := fun e =>
                hva (Fin.castAdd_injective n k e)
              rw [Function.update_of_ne hu'] at hux
              rw [Function.update_of_ne hv'] at hvx
              exact ⟨u, v, huv, hux, hvx⟩
          · rintro (⟨b, hb, hbx⟩ | ⟨u, v, huv, hux, hvx⟩)
            · left
              obtain ⟨hba, hbA⟩ := Finset.mem_erase.1 hb
              have hne : Fin.castAdd k b ≠ Fin.castAdd k a := fun e =>
                hba (Fin.castAdd_injective n k e)
              exact ⟨b, hbA, by rwa [Function.update_of_ne hne]⟩
            · right
              have hua : u ≠ a := fun e => hiso a ha v (e ▸ huv)
              have hva : v ≠ a := fun e => hiso a ha u (e ▸ huv.symm)
              have hu' : Fin.castAdd k u ≠ Fin.castAdd k a := fun e =>
                hua (Fin.castAdd_injective n k e)
              have hv' : Fin.castAdd k v ≠ Fin.castAdd k a := fun e =>
                hva (Fin.castAdd_injective n k e)
              exact ⟨u, v, huv, by rwa [Function.update_of_ne hu'], by rwa [Function.update_of_ne hv']⟩
        · congr 1
          funext j
          have hne : Fin.natAdd n j ≠ Fin.castAdd k a := by
            intro e
            have := congrArg Fin.val e
            simp at this
            have := a.isLt
            omega
          exact Function.update_of_ne hne _ _
      have hdep : ∃ x : Fin (n + k) → Bool,
          forestFn n k G A g (Function.update x (Fin.castAdd k a) (!x (Fin.castAdd k a))) ≠
            forestFn n k G A g x := by
        refine ⟨padFalse n k yf, ?_⟩
        have h0 : forestFn n k G A g (padFalse n k yf) = false := by
          simp [forestFn, padFalse_castAdd, padFalse_natAdd, hyf]
        have h1 : forestFn n k G A g
            (Function.update (padFalse n k yf) (Fin.castAdd k a) (!padFalse n k yf (Fin.castAdd k a))) =
            true := by
          unfold forestFn
          have htrue : ∃ b ∈ A, Function.update (padFalse n k yf) (Fin.castAdd k a)
              (!padFalse n k yf (Fin.castAdd k a)) (Fin.castAdd k b) = true :=
            ⟨a, ha, by simp [padFalse_castAdd]⟩
          simp [htrue]
        rw [h0, h1]
        decide
      have hnc : ∃ x x' : Fin (n + k) → Bool,
          forestFn n k G A g (Function.update x (Fin.castAdd k a) false) ≠
            forestFn n k G A g (Function.update x' (Fin.castAdd k a) false) := by
        refine ⟨padFalse n k yf, padFalse n k yt, ?_⟩
        have hf1 : forestFn n k G A g (Function.update (padFalse n k yf) (Fin.castAdd k a) false) = false := by
          rw [show forestFn n k G A g (Function.update (padFalse n k yf) (Fin.castAdd k a) false) =
              forestFn n k G A' g (padFalse n k yf) from congrFun hfun_eq _]
          simp [forestFn, padFalse_castAdd, padFalse_natAdd, hyf]
        have ht1 : forestFn n k G A g (Function.update (padFalse n k yt) (Fin.castAdd k a) false) = true := by
          rw [show forestFn n k G A g (Function.update (padFalse n k yt) (Fin.castAdd k a) false) =
              forestFn n k G A' g (padFalse n k yt) from congrFun hfun_eq _]
          simp [forestFn, padFalse_natAdd, hyt]
        rw [hf1, ht1]
        decide
      obtain ⟨hs1, hcirc'⟩ := gate_elim_at (n + k) (forestFn n k G A g) (Fin.castAdd k a) false s
        hdep hnc hcirc
      rw [hfun_eq] at hcirc'
      have hih := ih (2 * G.edgeFinset.card + A'.card) (by omega) G A' t (s - 1) rfl hacyc
        (fun b hb => hiso b (Finset.mem_of_mem_erase hb)) hvc hcirc'
      omega
    · rw [Finset.not_nonempty_iff_eq_empty] at hA
      subst hA
      by_cases hedge : ∃ u v : Fin n, G.Adj u v
      · obtain ⟨w, u, hwu, hwleaf, hcases⟩ := forest_leaf_structure G hacyc hedge
        have hne_wu : w ≠ u := G.ne_of_adj hwu
        have hdep_w : ∃ x : Fin (n + k) → Bool,
            forestFn n k G ∅ g (Function.update x (Fin.castAdd k w) (!x (Fin.castAdd k w))) ≠
              forestFn n k G ∅ g x := by
          let x0 : Fin (n + k) → Bool := Function.update (padFalse n k yf) (Fin.castAdd k u) true
          refine ⟨x0, ?_⟩
          have hxw : x0 (Fin.castAdd k w) = false := by
            simp [x0, Fin.castAdd_injective n k |>.ne hne_wu, padFalse_castAdd]
          have h0 : forestFn n k G ∅ g x0 = false := by
            unfold forestFn
            have hng : g (fun j => x0 (Fin.natAdd n j)) = false := by
              have e : (fun j : Fin k => x0 (Fin.natAdd n j)) = yf := by
                funext j
                have hne : Fin.natAdd n j ≠ Fin.castAdd k u := by
                  intro h; have := congrArg Fin.val h; simp at this; have := u.isLt; omega
                simp [x0, Function.update_of_ne hne, padFalse_natAdd]
              rw [e, hyf]
            have hne_e : ¬ ∃ a b : Fin n, G.Adj a b ∧ x0 (Fin.castAdd k a) = true ∧ x0 (Fin.castAdd k b) = true := by
              rintro ⟨a, b, hab, ha, hb⟩
              have hau : a = u := by
                by_contra h
                have : x0 (Fin.castAdd k a) = false := by
                  simp [x0, Fin.castAdd_injective n k |>.ne h, padFalse_castAdd]
                rw [this] at ha; cases ha
              have hbu : b = u := by
                by_contra h
                have : x0 (Fin.castAdd k b) = false := by
                  simp [x0, Fin.castAdd_injective n k |>.ne h, padFalse_castAdd]
                rw [this] at hb; cases hb
              rw [hau, hbu] at hab
              exact G.loopless.irrefl u hab
            simp [hng, hne_e]
          have h1 : forestFn n k G ∅ g (Function.update x0 (Fin.castAdd k w) (!x0 (Fin.castAdd k w))) = true := by
            unfold forestFn
            have hex : ∃ a b : Fin n, G.Adj a b ∧
                Function.update x0 (Fin.castAdd k w) (!x0 (Fin.castAdd k w)) (Fin.castAdd k a) = true ∧
                Function.update x0 (Fin.castAdd k w) (!x0 (Fin.castAdd k w)) (Fin.castAdd k b) = true := by
              refine ⟨w, u, hwu, ?_, ?_⟩
              · simp [hxw]
              · have hne : Fin.castAdd k u ≠ Fin.castAdd k w :=
                  (Fin.castAdd_injective n k).ne hne_wu.symm
                simp [Function.update_of_ne hne, x0]
            simp [hex]
          rw [h0, h1]
          decide
        let G1 : SimpleGraph (Fin n) := {
          Adj := fun a b => G.Adj a b ∧ ¬ (a = w ∧ b = u ∨ a = u ∧ b = w)
          symm := ⟨fun a b ⟨hab, hne⟩ => ⟨hab.symm, by tauto⟩⟩
          loopless := ⟨fun a ⟨haa, _⟩ => G.loopless.irrefl a haa⟩
        }
        have hG1le : G1 ≤ G := fun a b h => h.1
        have hG1acyc : G1.IsAcyclic := fun v c hc => hacyc (c.mapLe hG1le) (hc.mapLe hG1le)
        have hG1edges : G1.edgeFinset = G.edgeFinset.erase s(w, u) := by
          ext e
          induction e using Sym2.ind with
          | _ a b =>
            simp only [SimpleGraph.mem_edgeFinset, Finset.mem_erase, SimpleGraph.mem_edgeSet,
              ne_eq, Sym2.eq_iff, G1]
            tauto
        have hG1card : G1.edgeFinset.card + 1 = G.edgeFinset.card := by
          rw [hG1edges]
          exact Finset.card_erase_add_one (by rw [SimpleGraph.mem_edgeFinset]; exact hwu)
        have hfun1 : (fun x : Fin (n + k) → Bool =>
            forestFn n k G ∅ g (Function.update x (Fin.castAdd k w) false)) =
            forestFn n k G1 ∅ g := by
          funext x
          unfold forestFn
          congr 1
          · apply decide_eq_decide.2
            simp only [Finset.notMem_empty, false_and, exists_false, false_or]
            constructor
            · rintro ⟨a, b, hab, ha, hb⟩
              have haw : a ≠ w := by
                intro e; subst e; simp at ha
              have hbw : b ≠ w := by
                intro e; subst e; simp at hb
              have ha' : Fin.castAdd k a ≠ Fin.castAdd k w := (Fin.castAdd_injective n k).ne haw
              have hb' : Fin.castAdd k b ≠ Fin.castAdd k w := (Fin.castAdd_injective n k).ne hbw
              rw [Function.update_of_ne ha'] at ha
              rw [Function.update_of_ne hb'] at hb
              exact ⟨a, b, ⟨hab, by tauto⟩, ha, hb⟩
            · rintro ⟨a, b, ⟨hab, hne⟩, ha, hb⟩
              have haw : a ≠ w := by
                intro e; subst e
                exact hne (Or.inl ⟨rfl, hwleaf b hab⟩)
              have hbw : b ≠ w := by
                intro e; subst e
                exact hne (Or.inr ⟨hwleaf a hab.symm, rfl⟩)
              have ha' : Fin.castAdd k a ≠ Fin.castAdd k w := (Fin.castAdd_injective n k).ne haw
              have hb' : Fin.castAdd k b ≠ Fin.castAdd k w := (Fin.castAdd_injective n k).ne hbw
              exact ⟨a, b, hab, by rwa [Function.update_of_ne ha'], by rwa [Function.update_of_ne hb']⟩
          · congr 1
            funext j
            have hne : Fin.natAdd n j ≠ Fin.castAdd k w := by
              intro e; have := congrArg Fin.val e; simp at this; have := w.isLt; omega
            exact Function.update_of_ne hne _ _
        have hnc0 : ∃ x x' : Fin (n + k) → Bool,
            forestFn n k G ∅ g (Function.update x (Fin.castAdd k w) false) ≠
              forestFn n k G ∅ g (Function.update x' (Fin.castAdd k w) false) := by
          refine ⟨padFalse n k yf, padFalse n k yt, ?_⟩
          have hf1 : forestFn n k G ∅ g (Function.update (padFalse n k yf) (Fin.castAdd k w) false) = false := by
            rw [show forestFn n k G ∅ g (Function.update (padFalse n k yf) (Fin.castAdd k w) false) =
                forestFn n k G1 ∅ g (padFalse n k yf) from congrFun hfun1 _]
            simp [forestFn, padFalse_castAdd, padFalse_natAdd, hyf]
          have ht1 : forestFn n k G ∅ g (Function.update (padFalse n k yt) (Fin.castAdd k w) false) = true := by
            rw [show forestFn n k G ∅ g (Function.update (padFalse n k yt) (Fin.castAdd k w) false) =
                forestFn n k G1 ∅ g (padFalse n k yt) from congrFun hfun1 _]
            simp [forestFn, padFalse_natAdd, hyt]
          rw [hf1, ht1]
          decide
        rcases hcases with ⟨w', hw'ne, hw'u, hw'leaf⟩ | hdeg2
        · have hvc1 : ∀ S : Finset (Fin n), (∀ a b, G1.Adj a b → a ∈ S ∨ b ∈ S) → t ≤ S.card := by
            intro S hS
            by_cases huS : u ∈ S
            · apply hvc S
              intro a b hab
              by_cases h1 : a = w ∧ b = u ∨ a = u ∧ b = w
              · rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                · exact Or.inr huS
                · exact Or.inl huS
              · exact hS a b ⟨hab, h1⟩
            · have hw'S : w' ∈ S := by
                have hG1w' : G1.Adj w' u := ⟨hw'u, by
                  rintro (⟨h1, _⟩ | ⟨h1, _⟩)
                  · exact hw'ne h1
                  · exact G.ne_of_adj hw'u h1⟩
                exact (hS w' u hG1w').resolve_right huS
              let S' := insert u (S.erase w')
              have hS'card : S'.card ≤ S.card := by
                have h1 : (S.erase w').card + 1 = S.card := Finset.card_erase_add_one hw'S
                have h2 : S'.card ≤ (S.erase w').card + 1 := Finset.card_insert_le _ _
                omega
              have hS'cov : ∀ a b, G.Adj a b → a ∈ S' ∨ b ∈ S' := by
                intro a b hab
                by_cases hau : a = u
                · subst hau; exact Or.inl (Finset.mem_insert_self _ _)
                · by_cases hbu : b = u
                  · subst hbu; exact Or.inr (Finset.mem_insert_self _ _)
                  · have hG1ab : G1.Adj a b := ⟨hab, by tauto⟩
                    have haw' : a ≠ w' := fun e => hbu (hw'leaf b (e ▸ hab))
                    have hbw' : b ≠ w' := fun e => hau (hw'leaf a (e ▸ hab.symm))
                    rcases hS a b hG1ab with haS | hbS
                    · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨haw', haS⟩))
                    · exact Or.inr (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hbw', hbS⟩))
              exact le_trans (hvc S' hS'cov) hS'card
          obtain ⟨hs1, hcirc1⟩ := gate_elim_at (n + k) (forestFn n k G ∅ g) (Fin.castAdd k w) false s
            hdep_w hnc0 hcirc
          rw [hfun1] at hcirc1
          have hih := ih (2 * G1.edgeFinset.card + (∅ : Finset (Fin n)).card) (by simp; omega)
            G1 ∅ t (s - 1) rfl hG1acyc (by simp) hvc1 hcirc1
          simp only [Finset.card_empty, zero_add] at hih ⊢
          omega
        · let G2 : SimpleGraph (Fin n) := {
            Adj := fun a b => G.Adj a b ∧ a ≠ u ∧ b ≠ u
            symm := ⟨fun a b ⟨hab, ha, hb⟩ => ⟨hab.symm, hb, ha⟩⟩
            loopless := ⟨fun a ⟨haa, _⟩ => G.loopless.irrefl a haa⟩
          }
          have hG2le : G2 ≤ G := fun a b h => h.1
          have hG2acyc : G2.IsAcyclic := fun v c hc => hacyc (c.mapLe hG2le) (hc.mapLe hG2le)
          have hfun2 : (fun x : Fin (n + k) → Bool =>
              forestFn n k G ∅ g (Function.update x (Fin.castAdd k w) true)) =
              forestFn n k G2 {u} g := by
            funext x
            unfold forestFn
            congr 1
            · apply decide_eq_decide.2
              simp only [Finset.notMem_empty, false_and, exists_false, false_or,
                Finset.mem_singleton, exists_eq_left]
              constructor
              · rintro ⟨a, b, hab, ha, hb⟩
                by_cases hau : a = u
                · rw [hau] at ha
                  left
                  have hne : Fin.castAdd k u ≠ Fin.castAdd k w :=
                    (Fin.castAdd_injective n k).ne hne_wu.symm
                  rwa [Function.update_of_ne hne] at ha
                · by_cases hbu : b = u
                  · rw [hbu] at hb
                    left
                    have hne : Fin.castAdd k u ≠ Fin.castAdd k w :=
                      (Fin.castAdd_injective n k).ne hne_wu.symm
                    rwa [Function.update_of_ne hne] at hb
                  · right
                    have haw : a ≠ w := fun e => hbu (hwleaf b (e ▸ hab))
                    have hbw : b ≠ w := fun e => hau (hwleaf a (e ▸ hab.symm))
                    have ha' : Fin.castAdd k a ≠ Fin.castAdd k w := (Fin.castAdd_injective n k).ne haw
                    have hb' : Fin.castAdd k b ≠ Fin.castAdd k w := (Fin.castAdd_injective n k).ne hbw
                    rw [Function.update_of_ne ha'] at ha
                    rw [Function.update_of_ne hb'] at hb
                    exact ⟨a, b, ⟨hab, hau, hbu⟩, ha, hb⟩
              · rintro (hu | ⟨a, b, ⟨hab, hau, hbu⟩, ha, hb⟩)
                · refine ⟨w, u, hwu, by simp, ?_⟩
                  have hne : Fin.castAdd k u ≠ Fin.castAdd k w :=
                    (Fin.castAdd_injective n k).ne hne_wu.symm
                  rwa [Function.update_of_ne hne]
                · have haw : a ≠ w := fun e => hbu (hwleaf b (e ▸ hab))
                  have hbw : b ≠ w := fun e => hau (hwleaf a (e ▸ hab.symm))
                  have ha' : Fin.castAdd k a ≠ Fin.castAdd k w := (Fin.castAdd_injective n k).ne haw
                  have hb' : Fin.castAdd k b ≠ Fin.castAdd k w := (Fin.castAdd_injective n k).ne hbw
                  exact ⟨a, b, hab, by rwa [Function.update_of_ne ha'], by rwa [Function.update_of_ne hb']⟩
            · congr 1
              funext j
              have hne : Fin.natAdd n j ≠ Fin.castAdd k w := by
                intro e; have := congrArg Fin.val e; simp at this; have := w.isLt; omega
              exact Function.update_of_ne hne _ _
          have hnc1 : ∃ x x' : Fin (n + k) → Bool,
              forestFn n k G ∅ g (Function.update x (Fin.castAdd k w) true) ≠
                forestFn n k G ∅ g (Function.update x' (Fin.castAdd k w) true) := by
            refine ⟨padFalse n k yf, padFalse n k yt, ?_⟩
            have hf1 : forestFn n k G ∅ g (Function.update (padFalse n k yf) (Fin.castAdd k w) true) = false := by
              rw [show forestFn n k G ∅ g (Function.update (padFalse n k yf) (Fin.castAdd k w) true) =
                  forestFn n k G2 {u} g (padFalse n k yf) from congrFun hfun2 _]
              simp [forestFn, padFalse_castAdd, padFalse_natAdd, hyf]
            have ht1 : forestFn n k G ∅ g (Function.update (padFalse n k yt) (Fin.castAdd k w) true) = true := by
              rw [show forestFn n k G ∅ g (Function.update (padFalse n k yt) (Fin.castAdd k w) true) =
                  forestFn n k G2 {u} g (padFalse n k yt) from congrFun hfun2 _]
              simp [forestFn, padFalse_natAdd, hyt]
            rw [hf1, ht1]
            decide
          obtain ⟨hs2, hbranch⟩ := gate_elim_two (n + k) (forestFn n k G ∅ g) (Fin.castAdd k w) s
            hdep_w hnc0 hnc1 hcirc
          rcases hbranch with hcirc1 | hcirc2
          · rw [hfun1] at hcirc1
            have hvc1 : ∀ S : Finset (Fin n), (∀ a b, G1.Adj a b → a ∈ S ∨ b ∈ S) → t - 1 ≤ S.card := by
              intro S hS
              have hcov : ∀ a b, G.Adj a b → a ∈ insert u S ∨ b ∈ insert u S := by
                intro a b hab
                by_cases h1 : a = w ∧ b = u ∨ a = u ∧ b = w
                · rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                  · exact Or.inr (Finset.mem_insert_self _ _)
                  · exact Or.inl (Finset.mem_insert_self _ _)
                · rcases hS a b ⟨hab, h1⟩ with haS | hbS
                  · exact Or.inl (Finset.mem_insert_of_mem haS)
                  · exact Or.inr (Finset.mem_insert_of_mem hbS)
              have h1 := hvc (insert u S) hcov
              have h2 := Finset.card_insert_le u S
              omega
            have hih := ih (2 * G1.edgeFinset.card + (∅ : Finset (Fin n)).card) (by simp; omega)
              G1 ∅ (t - 1) (s - 2) rfl hG1acyc (by simp) hvc1 hcirc1
            simp only [Finset.card_empty, zero_add] at hih ⊢
            omega
          · rw [hfun2] at hcirc2
            have hG2sub : G2.edgeFinset ⊆ G.edgeFinset := by
              intro e he
              induction e using Sym2.ind with
              | _ a b =>
                rw [SimpleGraph.mem_edgeFinset] at he ⊢
                exact he.1
            have hG2lt : G2.edgeFinset.card < G.edgeFinset.card := by
              apply Finset.card_lt_card
              refine Finset.ssubset_iff_subset_ne.2 ⟨hG2sub, ?_⟩
              intro heq
              have hmem : s(w, u) ∈ G2.edgeFinset := by
                rw [heq, SimpleGraph.mem_edgeFinset]; exact hwu
              rw [SimpleGraph.mem_edgeFinset] at hmem
              exact hmem.2.2 rfl
            have hG2diff : (G.edgeFinset \ G2.edgeFinset).card ≤ 2 := by
              by_cases hexz : ∃ z : Fin n, G.Adj u z ∧ z ≠ w
              · obtain ⟨z, huz, hzw⟩ := hexz
                have hsub : G.edgeFinset \ G2.edgeFinset ⊆ {s(u, w), s(u, z)} := by
                  intro e he
                  induction e using Sym2.ind with
                  | _ a b =>
                    rw [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeFinset] at he
                    obtain ⟨hab, hnot⟩ := he
                    have hor : a = u ∨ b = u := by
                      by_contra h
                      push Not at h
                      exact hnot ⟨hab, h.1, h.2⟩
                    simp only [Finset.mem_insert, Finset.mem_singleton]
                    rcases hor with rfl | rfl
                    · by_cases hbw : b = w
                      · left; subst hbw; rfl
                      · right; rw [hdeg2 b z hab huz hbw hzw]
                    · by_cases haw : a = w
                      · left; subst haw; exact Sym2.eq_swap
                      · right; rw [hdeg2 a z hab.symm huz haw hzw, Sym2.eq_swap]
                exact le_trans (Finset.card_le_card hsub) (by
                  exact le_trans (Finset.card_insert_le _ _) (by simp))
              · push Not at hexz
                have hsub : G.edgeFinset \ G2.edgeFinset ⊆ {s(u, w)} := by
                  intro e he
                  induction e using Sym2.ind with
                  | _ a b =>
                    rw [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeFinset] at he
                    obtain ⟨hab, hnot⟩ := he
                    have hor : a = u ∨ b = u := by
                      by_contra h
                      push Not at h
                      exact hnot ⟨hab, h.1, h.2⟩
                    simp only [Finset.mem_singleton]
                    rcases hor with rfl | rfl
                    · rw [hexz b hab]
                    · rw [hexz a hab.symm, Sym2.eq_swap]
                exact le_trans (Finset.card_le_card hsub) (by simp)
            have hG2card : G.edgeFinset.card ≤ G2.edgeFinset.card + 2 := by
              have h1 := Finset.card_sdiff_add_card_eq_card hG2sub
              omega
            have hvc2 : ∀ S : Finset (Fin n), (∀ a b, G2.Adj a b → a ∈ S ∨ b ∈ S) → t - 1 ≤ S.card := by
              intro S hS
              have hcov : ∀ a b, G.Adj a b → a ∈ insert u S ∨ b ∈ insert u S := by
                intro a b hab
                by_cases hau : a = u
                · subst hau; exact Or.inl (Finset.mem_insert_self _ _)
                · by_cases hbu : b = u
                  · subst hbu; exact Or.inr (Finset.mem_insert_self _ _)
                  · rcases hS a b ⟨hab, hau, hbu⟩ with haS | hbS
                    · exact Or.inl (Finset.mem_insert_of_mem haS)
                    · exact Or.inr (Finset.mem_insert_of_mem hbS)
              have h1 := hvc (insert u S) hcov
              have h2 := Finset.card_insert_le u S
              omega
            have hih := ih (2 * G2.edgeFinset.card + ({u} : Finset (Fin n)).card)
              (by simp at hM ⊢; omega)
              G2 {u} (t - 1) (s - 2) rfl hG2acyc
              (by intro a ha v hadj; simp at ha; subst ha; exact hadj.2.1 rfl)
              hvc2 hcirc2
            simp only [Finset.card_singleton, Finset.card_empty, zero_add] at hih ⊢
            omega
      · push Not at hedge
        have hE0 : G.edgeFinset = ∅ := by
          ext e
          induction e using Sym2.ind with
          | _ a b =>
            simp only [SimpleGraph.mem_edgeFinset, Finset.notMem_empty, iff_false]
            exact hedge a b
        have ht0 : t = 0 := by
          have := hvc ∅ (fun u v huv => (hedge u v huv).elim)
          simp at this
          exact this
        have hfun0 : forestFn n k G ∅ g = fun x => g (fun j => x (Fin.natAdd n j)) := by
          funext x
          simp [forestFn, hedge]
        rw [hfun0] at hcirc
        have hcg := hgc s (drop_first_n n k s g ⟨y0, y1, hyne⟩ hcirc)
        rw [hE0, ht0]
        simp [hcg]

end PEqualNP.Outside.LMeta468Aux

open PEqualNP.Outside.LMeta468Aux in
theorem PEqualNP.Outside.L_meta_468 : ∀ (n k c t s : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (g : (Fin k → Bool) → Bool), G.IsAcyclic → (∀ a ∈ A, ∀ v : Fin n, ¬ G.Adj a v) → (A.Nonempty ∨ ∃ u v : Fin n, G.Adj u v) → (∃ y y' : Fin k → Bool, g y ≠ g y') → (∀ r : ℕ, PEqualNP.MetaComplexity.HasCircuitSize k g r ↔ c ≤ r) → (∃ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S) ∧ S.card = t) → (∀ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S) → t ≤ S.card) → (PEqualNP.MetaComplexity.HasCircuitSize (n + k) (fun x : Fin (n + k) → Bool => decide ((∃ a ∈ A, x (Fin.castAdd k a) = true) ∨ ∃ u v : Fin n, G.Adj u v ∧ x (Fin.castAdd k u) = true ∧ x (Fin.castAdd k v) = true) || g (fun j : Fin k => x (Fin.natAdd n j))) s ↔ A.card + G.edgeFinset.card + t + c ≤ s) := by
  intro n k c t s G _ A g hacyc hiso _ hgnc hgsize hcov hvc
  constructor
  · intro hcirc
    exact lower_bound_aux n k c g hgnc (fun r hr => (hgsize r).1 hr)
      (2 * G.edgeFinset.card + A.card) G A t s rfl hacyc hiso hvc hcirc
  · intro hs
    exact upper_bound n k c t s G A g hgnc ((hgsize c).2 le_rfl) hcov hs
