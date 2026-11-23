import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private lemma wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

private lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

private lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  induction gs₁ generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]

private lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    simp
    omega

private lemma getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

private lemma getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi
  simp [List.getD]

private lemma getD_snoc_ne {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i ≠ l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  by_cases hlt : i < l.length
  · exact getD_snoc_lt l x d i hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons, ih _ (by simp; omega)]
    exact getD_snoc_lt _ _ _ _ hi

private def OkGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private def NOkGate (g : Gate) : Prop :=
  OkGate g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

private def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

private lemma normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

private lemma normGate_nok (g : Gate) (h : OkGate g) : NOkGate (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this
    exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this
    exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩
    · simp [normGate]
    · simp [normGate]

private lemma wiresFrom_norm (gs : List Gate) (w : List Bool) :
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, wiresFrom_cons, wiresFrom_cons, normGate_eval, ih]

private def statVal (w : List Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

private def statValid (m : ℕ) : Bool ⊕ ℕ → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

private def simpNot (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

private def simpAnd (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

private def simpOr (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

private def simplifyGate (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    Option Gate × (Bool ⊕ ℕ) :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

private lemma simplifyGate_ok (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    ∀ g ∈ (simplifyGate op m ins).1, OkGate g := by
  intro g hg
  cases op <;> simp only [simplifyGate] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg; simp [OkGate]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg; simp [OkGate]
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg
    subst hg; simp [OkGate]
  · simp at hg
  · simp at hg

private lemma simplifyGate_none_of_const (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplifyGate op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplifyGate, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplifyGate, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplifyGate, simpNot]

private lemma simplifyGate_and_false (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hlen : ins.length ≤ 2) (hf : Sum.inl false ∈ ins) :
    simplifyGate GateOp.and m ins = (none, Sum.inl false) := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
  · simp at hf
  · cases a <;> simp_all [simplifyGate, simpAnd]
  · cases a with
    | inl c =>
      cases b with
      | inl d => cases c <;> cases d <;> simp_all [simplifyGate, simpAnd]
      | inr j => cases c <;> simp_all [simplifyGate, simpAnd]
    | inr i =>
      cases b with
      | inl d => cases d <;> simp_all [simplifyGate, simpAnd]
      | inr j => simp at hf
  · simp at hlen

private lemma simplifyGate_or_true (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hlen : ins.length ≤ 2) (ht : Sum.inl true ∈ ins) :
    simplifyGate GateOp.or m ins = (none, Sum.inl true) := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
  · simp at ht
  · cases a <;> simp_all [simplifyGate, simpOr]
  · cases a with
    | inl c =>
      cases b with
      | inl d => cases c <;> cases d <;> simp_all [simplifyGate, simpOr]
      | inr j => cases c <;> simp_all [simplifyGate, simpOr]
    | inr i =>
      cases b with
      | inl d => cases d <;> simp_all [simplifyGate, simpOr]
      | inr j => simp at ht
  · simp at hlen

private lemma simplifyGate_not_const (m : ℕ) (c : Bool) :
    simplifyGate GateOp.not m [Sum.inl c] = (none, Sum.inl (!c)) := rfl

private lemma simplifyGate_all_const (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hall : ∀ s ∈ ins, ∃ c : Bool, s = Sum.inl c) :
    ∃ c : Bool, (simplifyGate op m ins).2 = Sum.inl c := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · exact ⟨true, rfl⟩
    · obtain ⟨c, rfl⟩ := hall a (by simp); exact ⟨c, rfl⟩
    · obtain ⟨c, rfl⟩ := hall a (by simp)
      obtain ⟨d, rfl⟩ := hall b (by simp)
      exact ⟨c && d, rfl⟩
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · exact ⟨false, rfl⟩
    · obtain ⟨c, rfl⟩ := hall a (by simp); exact ⟨c, rfl⟩
    · obtain ⟨c, rfl⟩ := hall a (by simp)
      obtain ⟨d, rfl⟩ := hall b (by simp)
      exact ⟨c || d, rfl⟩
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · exact ⟨true, rfl⟩
    · obtain ⟨c, rfl⟩ := hall a (by simp); exact ⟨!c, rfl⟩

private lemma simplifyGate_sound (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List (Bool ⊕ ℕ)) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplifyGate op w.length ins).1.toList.length)
      (simplifyGate op w.length ins).2 ∧
    statVal (wiresFrom (simplifyGate op w.length ins).1.toList w)
      (simplifyGate op w.length ins).2 = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplifyGate, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
        | inr j => simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplifyGate, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
        | inr j => simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplifyGate, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

private def elimStep (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  let r := simplifyGate g.op (m + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

private def elimPass (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  gs.foldl (elimStep m) acc

private lemma elimPass_nil (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m [] acc = acc := rfl

private lemma elimPass_cons (m : ℕ) (g : Gate) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m (g :: gs) acc = elimPass m gs (elimStep m acc g) := rfl

private lemma elimPass_append (m : ℕ) (gs₁ gs₂ : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m (gs₁ ++ gs₂) acc = elimPass m gs₂ (elimPass m gs₁ acc) := by
  induction gs₁ generalizing acc with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, elimPass_cons, ih]

private lemma elimPass_fst_len (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    (elimPass m gs acc).1.length = acc.1.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    rw [elimPass_cons, ih]
    simp [elimStep]
    omega

private lemma elimPass_getD_lt (m k : ℕ) (d : Bool ⊕ ℕ) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) (hk : k < acc.1.length) :
    (elimPass m gs acc).1.getD k d = acc.1.getD k d := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    rw [elimPass_cons, ih _ (by simp [elimStep]; omega)]
    exact getD_snoc_lt _ _ _ _ hk

private lemma toList_opt_len_le {α : Type*} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

private lemma elimPass_ok (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (h : ∀ g ∈ acc.2, OkGate g) : ∀ g ∈ (elimPass m gs acc).2, OkGate g := by
  induction gs generalizing acc with
  | nil => exact h
  | cons g gs ih =>
    rw [elimPass_cons]
    apply ih
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplifyGate_ok _ _ _ g' (by simpa using h1)

private lemma elimPass_len (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    (elimPass m gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    rw [elimPass_cons, List.length_cons]
    have h1 := ih (elimStep m acc g)
    have h2 : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_opt_len_le (simplifyGate g.op (m + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    omega

private lemma elimPass_len_lt (m k : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, NOkGate g) (hk : k < acc.1.length)
    (hc : ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c)
    (hex : ∃ g ∈ gs, k ∈ g.inputs) :
    (elimPass m gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => obtain ⟨g, hg, _⟩ := hex; simp at hg
  | cons g gs ih =>
    rw [elimPass_cons, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplifyGate g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplifyGate_none_of_const
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep m acc g).2.length = acc.2.length := by
        simp only [elimStep, hnone, Option.toList_none, List.append_nil]
      have := elimPass_len m gs (elimStep m acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep m acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          exact ⟨c, by simp only [elimStep]; rw [getD_snoc_lt _ _ _ _ hk]; exact hc⟩)
        hex'
      have h2 : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_opt_len_le (simplifyGate g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

private lemma elimPass_len_two (m k : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, NOkGate g) (hk : k < acc.1.length)
    (hc : ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c)
    (htwo : 2 ≤ (gs.filter (fun g => decide (k ∈ g.inputs))).length) :
    (elimPass m gs acc).2.length + 2 ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp at htwo
  | cons g gs ih =>
    rw [elimPass_cons, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplifyGate g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplifyGate_none_of_const
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep m acc g).2.length = acc.2.length := by
        simp only [elimStep, hnone, Option.toList_none, List.append_nil]
      have hfilt : 1 ≤ (gs.filter (fun g => decide (k ∈ g.inputs))).length := by
        simp [hkg] at htwo
        omega
      have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        have hne : gs.filter (fun g => decide (k ∈ g.inputs)) ≠ [] := by
          intro hnil; rw [hnil] at hfilt; simp at hfilt
        obtain ⟨g', hg'⟩ := List.exists_mem_of_ne_nil _ hne
        rw [List.mem_filter] at hg'
        exact ⟨g', hg'.1, of_decide_eq_true hg'.2⟩
      have h1 := elimPass_len_lt m k gs (elimStep m acc g)
        (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        ⟨c, by simp only [elimStep]; rw [getD_snoc_lt _ _ _ _ hk]; exact hc⟩
        hex'
      omega
    · have htwo' : 2 ≤ (gs.filter (fun g => decide (k ∈ g.inputs))).length := by
        simpa [hkg] using htwo
      have h1 := ih (elimStep m acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          exact ⟨c, by simp only [elimStep]; rw [getD_snoc_lt _ _ _ _ hk]; exact hc⟩)
        htwo'
      have h2 : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_opt_len_le (simplifyGate g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

private def ElimInv (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) : Prop :=
  w_in.length = m ∧
  acc.1.length = w_old.length ∧
  ∀ i : ℕ,
    statValid (m + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 w_in) (acc.1.getD i (Sum.inl false)) = w_old.getD i false

private lemma elimInv_step (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) (hok : OkGate g)
    (hinv : ElimInv m w_in w_old acc) :
    ElimInv m w_in (w_old ++ [g.op.eval (g.inputs.map fun i => w_old.getD i false)])
      (elimStep m acc g) := by
  obtain ⟨hwin, hlen, hi⟩ := hinv
  set w_new := wiresFrom acc.2 w_in with hw_new
  have hw_len : w_new.length = m + acc.2.length := by
    rw [hw_new, wiresFrom_length, hwin]
  set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
  have hins_len : ins.length ≤ 2 := by simp [hins]; exact hok.2
  have hins_val : ∀ s ∈ ins, statValid w_new.length s := by
    intro s hs
    obtain ⟨idx, _, rfl⟩ := List.mem_map.1 hs
    rw [hw_len]
    exact (hi idx).1
  have hsound := simplifyGate_sound g.op hok.1 w_new ins hins_len hins_val
  rw [hw_len] at hsound
  refine ⟨hwin, by simp [elimStep, hlen], ?_⟩
  intro i
  simp only [elimStep]
  by_cases hieq : i = acc.1.length
  · rw [getD_snoc_eq _ _ _ _ hieq, getD_snoc_eq _ _ _ _ (by omega)]
    refine ⟨?_, ?_⟩
    · rw [List.length_append, ← Nat.add_assoc]
      exact hsound.1
    · rw [wiresFrom_append, ← hw_new, hsound.2]
      congr 1
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro idx _
      exact (hi idx).2
  · rw [getD_snoc_ne _ _ _ _ hieq, getD_snoc_ne _ _ _ _ (by omega)]
    have ⟨hv, hval⟩ := hi i
    refine ⟨?_, ?_⟩
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c => trivial
      | inr j =>
        rw [hst] at hv
        simp only [statValid, List.length_append] at hv ⊢
        omega
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c =>
        rw [hst] at hval
        exact hval
      | inr j =>
        rw [hst] at hv hval
        simp only [statValid] at hv
        simp only [statVal] at hval ⊢
        rw [wiresFrom_append, ← hw_new, wiresFrom_getD_lt _ _ _ (by omega)]
        exact hval

private lemma elimInv_pass (m : ℕ) (w_in : List Bool) (gs : List Gate)
    (w_old : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, OkGate g) (hinv : ElimInv m w_in w_old acc) :
    ElimInv m w_in (wiresFrom gs w_old) (elimPass m gs acc) := by
  induction gs generalizing w_old acc with
  | nil => exact hinv
  | cons g gs ih =>
    rw [wiresFrom_cons, elimPass_cons]
    exact ih _ _ (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (elimInv_step m w_in w_old acc g (hok g List.mem_cons_self) hinv)

private lemma wiresFrom_agree (gs : List Gate) (B : Set ℕ) (w₁ w₂ : List Bool)
    (hlen : w₁.length = w₂.length) (hB : ∀ b ∈ B, b < w₁.length)
    (hagree : ∀ i ∉ B, w₁.getD i false = w₂.getD i false)
    (hread : ∀ g ∈ gs, ∀ i ∈ g.inputs, i ∉ B) :
    (wiresFrom gs w₁).length = (wiresFrom gs w₂).length ∧
    ∀ i ∉ B, (wiresFrom gs w₁).getD i false = (wiresFrom gs w₂).getD i false := by
  induction gs generalizing w₁ w₂ with
  | nil => exact ⟨hlen, hagree⟩
  | cons g gs ih =>
    rw [wiresFrom_cons, wiresFrom_cons]
    have hmap : (g.inputs.map fun i => w₁.getD i false) =
        (g.inputs.map fun i => w₂.getD i false) := by
      apply List.map_congr_left
      intro i hi
      exact hagree i (hread g List.mem_cons_self i hi)
    rw [hmap]
    apply ih
    · simp [hlen]
    · intro b hb; simp; have := hB b hb; omega
    · intro i hi
      by_cases hlt : i < w₁.length
      · rw [getD_snoc_lt _ _ _ _ hlt, getD_snoc_lt _ _ _ _ (by omega)]
        exact hagree i hi
      · by_cases heq : i = w₁.length
        · rw [getD_snoc_eq _ _ _ _ heq, getD_snoc_eq _ _ _ _ (by omega)]
        · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)]
    · intro g' hg'
      exact hread g' (List.mem_cons_of_mem _ hg')

private lemma ofFn_getD_lt {α : Type*} {m : ℕ} (f : Fin m → α) (d : α) (i : ℕ) (hi : i < m) :
    (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simp; exact hi), List.getElem_ofFn]

private def initVar (m : ℕ) (v : Fin m) (b : Bool) : List (Bool ⊕ ℕ) :=
  List.ofFn fun i : Fin m => if i = v then Sum.inl b else Sum.inr (i : ℕ)

private lemma elimInv_initVar (m : ℕ) (v : Fin m) (b : Bool) (x : Fin m → Bool) :
    ElimInv m (List.ofFn x) (List.ofFn (Function.update x v b)) (initVar m v b, []) := by
  refine ⟨by simp, by simp [initVar], ?_⟩
  intro i
  by_cases hi : i < m
  · have hget : (initVar m v b).getD i (Sum.inl false) =
        if (⟨i, hi⟩ : Fin m) = v then Sum.inl b else Sum.inr i := by
      rw [initVar, ofFn_getD_lt _ _ _ hi]
    rw [hget]
    by_cases heq : (⟨i, hi⟩ : Fin m) = v
    · simp only [heq, ↓reduceIte, statValid, statVal]
      rw [ofFn_getD_lt _ _ _ hi, heq, Function.update_self]
      exact ⟨trivial, rfl⟩
    · simp only [heq, ↓reduceIte, statValid, statVal, wiresFrom_nil]
      refine ⟨by omega, ?_⟩
      rw [ofFn_getD_lt _ _ _ hi, ofFn_getD_lt _ _ _ hi, Function.update_of_ne heq]
  · rw [List.getD_eq_default _ _ (by simp [initVar]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

private lemma elim_one_var {m s : ℕ} {F : (Fin m → Bool) → Bool} (v : Fin m) (b : Bool)
    (hC : HasCircuitSize m F s)
    (hdep : ∃ x : Fin m → Bool, F (Function.update x v false) ≠ F (Function.update x v true))
    (hnc : ∃ x x' : Fin m → Bool, F (Function.update x v b) ≠ F (Function.update x' v b)) :
    1 ≤ s ∧ HasCircuitSize m (fun x => F (Function.update x v b)) (s - 1) := by
  obtain ⟨C, hok, hsz, hev⟩ := hC
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOkGate g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hok g0 hg0)
  have hout_ne : C.output ≠ (v : ℕ) := by
    intro heq
    obtain ⟨x, x', hne⟩ := hnc
    have h1 := hev (Function.update x v b)
    have h2 := hev (Function.update x' v b)
    have hw1 : (C.wires (List.ofFn (Function.update x v b))).getD (v : ℕ) false = b := by
      show (wiresFrom C.gates (List.ofFn (Function.update x v b))).getD (v : ℕ) false = b
      rw [wiresFrom_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ v.isLt]
      simp
    have hw2 : (C.wires (List.ofFn (Function.update x' v b))).getD (v : ℕ) false = b := by
      show (wiresFrom C.gates (List.ofFn (Function.update x' v b))).getD (v : ℕ) false = b
      rw [wiresFrom_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ v.isLt]
      simp
    have e1 : F (Function.update x v b) = b := by
      rw [← h1]; show (C.wires _).getD C.output false = b; rw [heq]; exact hw1
    have e2 : F (Function.update x' v b) = b := by
      rw [← h2]; show (C.wires _).getD C.output false = b; rw [heq]; exact hw2
    exact hne (e1.trans e2.symm)
  have hex : ∃ g ∈ gs, (v : ℕ) ∈ g.inputs := by
    by_contra hno
    have hno' : ∀ g ∈ gs, (v : ℕ) ∉ g.inputs := fun g hg hv => hno ⟨g, hg, hv⟩
    obtain ⟨x, hne⟩ := hdep
    have hag := wiresFrom_agree gs {(v : ℕ)}
      (List.ofFn (Function.update x v false))
      (List.ofFn (Function.update x v true))
      (by simp)
      (by intro u hu; simp at hu; subst hu; simp)
      (by
        intro i hi
        simp at hi
        by_cases hlt : i < m
        · have hne' : (⟨i, hlt⟩ : Fin m) ≠ v := by
            intro h; apply hi; exact congrArg Fin.val h
          rw [ofFn_getD_lt _ _ _ hlt, ofFn_getD_lt _ _ _ hlt,
              Function.update_of_ne hne', Function.update_of_ne hne']
        · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)])
      (by
        intro g hg i hi hmem
        simp at hmem
        subst hmem
        exact hno' g hg hi)
    have hco : C.output ∉ ({(v : ℕ)} : Set ℕ) := by simpa using hout_ne
    have hEq := hag.2 C.output hco
    rw [hgs, wiresFrom_norm, wiresFrom_norm] at hEq
    exact hne ((hev _).symm.trans (hEq.trans (hev _)))
  set acc := elimPass m gs (initVar m v b, []) with hacc
  have hlen : acc.2.length + 1 ≤ gs.length := by
    have := elimPass_len_lt m (v : ℕ) gs (initVar m v b, []) hnok
      (by simp [initVar])
      ⟨b, by rw [initVar, ofFn_getD_lt _ _ _ v.isLt]; simp⟩
      hex
    rw [← hacc] at this
    simpa using this
  have hgs_len : gs.length = C.gates.length := by simp [hgs]
  have hsz' : C.gates.length ≤ s := hsz
  have hval : ∀ x : Fin m → Bool,
      statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
        F (Function.update x v b) := by
    intro x
    have hinv := elimInv_pass m (List.ofFn x) gs _ (initVar m v b, [])
      (fun g hg => (hnok g hg).1) (elimInv_initVar m v b x)
    rw [← hacc] at hinv
    rw [(hinv.2.2 C.output).2, hgs, wiresFrom_norm]
    exact hev (Function.update x v b)
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    obtain ⟨x, x', hne⟩ := hnc
    have hx := hval x; have hx' := hval x'
    rw [hst] at hx hx'
    exact absurd (hx.symm.trans hx') hne
  | inr j =>
    refine ⟨by omega, ⟨acc.2, j⟩, elimPass_ok m gs _ (by simp), ?_, ?_⟩
    · show acc.2.length ≤ s - 1
      omega
    · intro x
      have := hval x
      rw [hst] at this
      exact this

private lemma list_split_unique_filter {α : Type*} (p : α → Bool) (l : List α)
    (h : (l.filter p).length = 1) :
    ∃ l₁ a l₂, l = l₁ ++ [a] ++ l₂ ∧ p a = true ∧
      (∀ x ∈ l₁, p x = false) ∧ (∀ x ∈ l₂, p x = false) := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    cases hpx : p x with
    | true =>
      have h0 : (xs.filter p).length = 0 := by
        simp only [List.filter_cons, hpx, ↓reduceIte, List.length_cons] at h
        omega
      have hnil : xs.filter p = [] := List.eq_nil_of_length_eq_zero h0
      refine ⟨[], x, xs, rfl, hpx, by simp, ?_⟩
      intro y hy
      by_contra hpy
      have hpyt : p y = true := by cases hp : p y <;> simp_all
      have : y ∈ xs.filter p := List.mem_filter.2 ⟨hy, hpyt⟩
      rw [hnil] at this
      simp at this
    | false =>
      have h1 : (xs.filter p).length = 1 := by
        simpa [hpx] using h
      obtain ⟨l₁, a, l₂, rfl, hpa, hl₁, hl₂⟩ := ih h1
      refine ⟨x :: l₁, a, l₂, by simp, hpa, ?_, hl₂⟩
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy'
      · exact hpx
      · exact hl₁ y hy'

private lemma elim_two_var {m s : ℕ} {F : (Fin m → Bool) → Bool} (v : Fin m)
    (hC : HasCircuitSize m F s)
    (hdep : ∃ x : Fin m → Bool, F (Function.update x v false) ≠ F (Function.update x v true))
    (hnc0 : ∃ x x' : Fin m → Bool,
      F (Function.update x v false) ≠ F (Function.update x' v false))
    (hnc1 : ∃ x x' : Fin m → Bool,
      F (Function.update x v true) ≠ F (Function.update x' v true)) :
    2 ≤ s ∧ (HasCircuitSize m (fun x => F (Function.update x v false)) (s - 2) ∨
      HasCircuitSize m (fun x => F (Function.update x v true)) (s - 2)) := by
  obtain ⟨C, hok, hsz, hev⟩ := hC
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOkGate g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hok g0 hg0)
  have hgs_len : gs.length = C.gates.length := by simp [hgs]
  have hsz' : C.gates.length ≤ s := hsz
  have hout_ne : C.output ≠ (v : ℕ) := by
    intro heq
    obtain ⟨x, x', hne⟩ := hnc0
    have h1 := hev (Function.update x v false)
    have h2 := hev (Function.update x' v false)
    have hw1 : (C.wires (List.ofFn (Function.update x v false))).getD (v : ℕ) false = false := by
      show (wiresFrom C.gates (List.ofFn (Function.update x v false))).getD (v : ℕ) false = false
      rw [wiresFrom_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ v.isLt]
      simp
    have hw2 : (C.wires (List.ofFn (Function.update x' v false))).getD (v : ℕ) false = false := by
      show (wiresFrom C.gates (List.ofFn (Function.update x' v false))).getD (v : ℕ) false = false
      rw [wiresFrom_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ v.isLt]
      simp
    have e1 : F (Function.update x v false) = false := by
      rw [← h1]; show (C.wires _).getD C.output false = false; rw [heq]; exact hw1
    have e2 : F (Function.update x' v false) = false := by
      rw [← h2]; show (C.wires _).getD C.output false = false; rw [heq]; exact hw2
    exact hne (e1.trans e2.symm)
  set cnt := (gs.filter (fun g => decide ((v : ℕ) ∈ g.inputs))).length with hcnt
  by_cases hge2 : 2 ≤ cnt
  · set acc := elimPass m gs (initVar m v false, []) with hacc
    have hlen : acc.2.length + 2 ≤ gs.length := by
      have := elimPass_len_two m (v : ℕ) gs (initVar m v false, []) hnok
        (by simp [initVar])
        ⟨false, by rw [initVar, ofFn_getD_lt _ _ _ v.isLt]; simp⟩
        (by rw [← hcnt]; exact hge2)
      rw [← hacc] at this
      simpa using this
    have hval : ∀ x : Fin m → Bool,
        statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
          F (Function.update x v false) := by
      intro x
      have hinv := elimInv_pass m (List.ofFn x) gs _ (initVar m v false, [])
        (fun g hg => (hnok g hg).1) (elimInv_initVar m v false x)
      rw [← hacc] at hinv
      rw [(hinv.2.2 C.output).2, hgs, wiresFrom_norm]
      exact hev (Function.update x v false)
    cases hst : acc.1.getD C.output (Sum.inl false) with
    | inl c =>
      obtain ⟨x, x', hne⟩ := hnc0
      have hx := hval x; have hx' := hval x'
      rw [hst] at hx hx'
      exact absurd (hx.symm.trans hx') hne
    | inr j =>
      refine ⟨by omega, Or.inl ⟨⟨acc.2, j⟩, elimPass_ok m gs _ (by simp), ?_, ?_⟩⟩
      · show acc.2.length ≤ s - 2; omega
      · intro x; have := hval x; rw [hst] at this; exact this
  · by_cases hzero : cnt = 0
    · exfalso
      have hnil : gs.filter (fun g => decide ((v : ℕ) ∈ g.inputs)) = [] :=
        List.eq_nil_of_length_eq_zero (by rw [← hcnt]; exact hzero)
      obtain ⟨x, hne⟩ := hdep
      have hag := wiresFrom_agree gs {(v : ℕ)}
        (List.ofFn (Function.update x v false))
        (List.ofFn (Function.update x v true))
        (by simp)
        (by intro u hu; simp at hu; subst hu; simp)
        (by
          intro i hi; simp at hi
          by_cases hlt : i < m
          · have hne' : (⟨i, hlt⟩ : Fin m) ≠ v := by
              intro h; apply hi; exact congrArg Fin.val h
            rw [ofFn_getD_lt _ _ _ hlt, ofFn_getD_lt _ _ _ hlt,
                Function.update_of_ne hne', Function.update_of_ne hne']
          · rw [List.getD_eq_default _ _ (by simp; omega),
                List.getD_eq_default _ _ (by simp; omega)])
        (by
          intro g hg i hi hmem
          simp at hmem; subst hmem
          have : g ∈ gs.filter (fun g => decide ((v : ℕ) ∈ g.inputs)) :=
            List.mem_filter.2 ⟨hg, decide_eq_true hi⟩
          rw [hnil] at this; simp at this)
      have hEq := hag.2 C.output (by simpa using hout_ne)
      rw [hgs, wiresFrom_norm, wiresFrom_norm] at hEq
      exact hne ((hev _).symm.trans (hEq.trans (hev _)))
    · have hone : (gs.filter (fun g => decide ((v : ℕ) ∈ g.inputs))).length = 1 := by
        rw [← hcnt]; omega
      have hsp := list_split_unique_filter (fun g => decide ((v : ℕ) ∈ g.inputs)) gs hone
      rcases hsp with ⟨gs₁, g₁, gs₂, hsplit, hg₁in, hgs₁no, hgs₂no⟩
      have hv_in : (v : ℕ) ∈ g₁.inputs := of_decide_eq_true hg₁in
      have hnok₁ : NOkGate g₁ := hnok g₁ (by rw [hsplit]; simp)
      set b : Bool := match g₁.op with | GateOp.or => true | _ => false with hb
      have hncb : ∃ x x' : Fin m → Bool,
          F (Function.update x v b) ≠ F (Function.update x' v b) := by
        cases hbc : b with
        | false => exact hnc0
        | true => exact hnc1
      set acc₁ := elimPass m gs₁ (initVar m v b, []) with hacc₁
      set accM := elimStep m acc₁ g₁ with haccM
      set acc := elimPass m gs₂ accM with hacc
      have hacc_eq : acc = elimPass m gs (initVar m v b, []) := by
        rw [hsplit, elimPass_append, elimPass_append, ← hacc₁, elimPass_cons, elimPass_nil, ← haccM]
      have hacc₁_len : acc₁.1.length = m + gs₁.length := by
        rw [hacc₁, elimPass_fst_len]; simp [initVar]
      have hacc₁_v : acc₁.1.getD (v : ℕ) (Sum.inl false) = Sum.inl b := by
        rw [hacc₁, elimPass_getD_lt _ _ _ _ _ (by simp [initVar])]
        rw [initVar, ofFn_getD_lt _ _ _ v.isLt]
        simp
      have hmid_props : accM.2.length = acc₁.2.length ∧
          ∃ c : Bool, accM.1.getD (m + gs₁.length) (Sum.inl false) = Sum.inl c := by
        have hmem : Sum.inl b ∈ (g₁.inputs.map fun i => acc₁.1.getD i (Sum.inl false)) :=
          List.mem_map.2 ⟨(v : ℕ), hv_in, hacc₁_v⟩
        have hres : ∃ c : Bool,
            simplifyGate g₁.op (m + acc₁.2.length)
              (g₁.inputs.map fun i => acc₁.1.getD i (Sum.inl false)) = (none, Sum.inl c) := by
          rcases hnok₁.1.1 with hop | hop | hop
          · have : g₁.op = GateOp.and := hop
            have hbf : b = false := by simp [hb, this]
            rw [this]
            rw [hbf] at hmem
            exact ⟨false, simplifyGate_and_false _ _ (by simp; exact hnok₁.1.2) hmem⟩
          · have : g₁.op = GateOp.or := hop
            have hbt : b = true := by simp [hb, this]
            rw [this]
            rw [hbt] at hmem
            exact ⟨true, simplifyGate_or_true _ _ (by simp; exact hnok₁.1.2) hmem⟩
          · have : g₁.op = GateOp.not := hop
            have hbf : b = false := by simp [hb, this]
            have hlen1 : g₁.inputs.length ≤ 1 := hnok₁.2 this
            have hsing : g₁.inputs = [(v : ℕ)] := by
              rcases hgi : g₁.inputs with _ | ⟨a, _ | ⟨d, l⟩⟩
              · rw [hgi] at hv_in; simp at hv_in
              · rw [hgi] at hv_in; simp at hv_in; subst hv_in; rfl
              · rw [hgi] at hlen1; simp at hlen1
            rw [this, hsing, List.map_singleton, hacc₁_v, hbf]
            exact ⟨true, simplifyGate_not_const _ false⟩
        obtain ⟨c, hc⟩ := hres
        refine ⟨by simp only [haccM, elimStep, hc, Option.toList_none, List.append_nil], c, ?_⟩
        simp only [haccM, elimStep, hc]
        exact getD_snoc_eq _ _ _ _ hacc₁_len.symm
      have hval : ∀ x : Fin m → Bool,
          statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
            F (Function.update x v b) := by
        intro x
        have hinv := elimInv_pass m (List.ofFn x) gs _ (initVar m v b, [])
          (fun g hg => (hnok g hg).1) (elimInv_initVar m v b x)
        rw [← hacc_eq] at hinv
        rw [(hinv.2.2 C.output).2, hgs, wiresFrom_norm]
        exact hev (Function.update x v b)
      have hout_ne_w1 : C.output ≠ m + gs₁.length := by
        intro heq
        obtain ⟨c, hc⟩ := hmid_props.2
        have hacc_w1 : acc.1.getD C.output (Sum.inl false) = Sum.inl c := by
          rw [heq, hacc, elimPass_getD_lt _ _ _ _ _ (by simp [haccM, elimStep, hacc₁_len])]
          exact hc
        obtain ⟨x, x', hne⟩ := hncb
        have hx := hval x; have hx' := hval x'
        rw [hacc_w1] at hx hx'
        exact hne (hx.symm.trans hx')
      have hex₂ : ∃ g ∈ gs₂, m + gs₁.length ∈ g.inputs := by
        by_contra hno
        have hno' : ∀ g ∈ gs₂, m + gs₁.length ∉ g.inputs := fun g hg hw => hno ⟨g, hg, hw⟩
        obtain ⟨x, hne⟩ := hdep
        have hag₁ := wiresFrom_agree gs₁ {(v : ℕ)}
          (List.ofFn (Function.update x v false))
          (List.ofFn (Function.update x v true))
          (by simp)
          (by intro u hu; simp at hu; subst hu; simp)
          (by
            intro i hi; simp at hi
            by_cases hlt : i < m
            · have hne' : (⟨i, hlt⟩ : Fin m) ≠ v := by
                intro h; apply hi; exact congrArg Fin.val h
              rw [ofFn_getD_lt _ _ _ hlt, ofFn_getD_lt _ _ _ hlt,
                  Function.update_of_ne hne', Function.update_of_ne hne']
            · rw [List.getD_eq_default _ _ (by simp; omega),
                  List.getD_eq_default _ _ (by simp; omega)])
          (by
            intro g hg i hi hmem
            simp at hmem; subst hmem
            have := hgs₁no g hg
            simp [hi] at this)
        set w0 := wiresFrom gs₁ (List.ofFn (Function.update x v false))
        set w1 := wiresFrom gs₁ (List.ofFn (Function.update x v true))
        have hw0_len : w0.length = m + gs₁.length := by simp [w0, wiresFrom_length]
        have hw1_len : w1.length = m + gs₁.length := by simp [w1, wiresFrom_length]
        have hag₂ := wiresFrom_agree gs₂ {(v : ℕ), m + gs₁.length}
          (wiresFrom [g₁] w0) (wiresFrom [g₁] w1)
          (by simp [wiresFrom_length, hw0_len, hw1_len])
          (by
            intro u hu
            rcases hu with rfl | rfl
            · simp [wiresFrom_length, hw0_len]; omega
            · simp [wiresFrom_length, hw0_len])
          (by
            intro i hi
            have hiv : i ≠ (v : ℕ) := fun h => hi (Or.inl h)
            have hiw : i ≠ m + gs₁.length := fun h => hi (Or.inr h)
            simp only [wiresFrom_cons, wiresFrom_nil]
            rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
            exact hag₁.2 i (by simpa using hiv))
          (by
            intro g hg i hi hmem
            rcases hmem with rfl | rfl
            · have := hgs₂no g hg; simp [hi] at this
            · exact hno' g hg hi)
        have hco : C.output ∉ ({(v : ℕ), m + gs₁.length} : Set ℕ) := by
          intro h; rcases h with h | h
          · exact hout_ne h
          · exact hout_ne_w1 h
        have hEq := hag₂.2 C.output hco
        have hrew0 : wiresFrom gs₂ (wiresFrom [g₁] w0) =
            wiresFrom gs (List.ofFn (Function.update x v false)) := by
          rw [hsplit, wiresFrom_append, wiresFrom_append]
        have hrew1 : wiresFrom gs₂ (wiresFrom [g₁] w1) =
            wiresFrom gs (List.ofFn (Function.update x v true)) := by
          rw [hsplit, wiresFrom_append, wiresFrom_append]
        rw [hrew0, hrew1, hgs, wiresFrom_norm, wiresFrom_norm] at hEq
        exact hne ((hev _).symm.trans (hEq.trans (hev _)))
      have hlen₂ := elimPass_len_lt m (m + gs₁.length) gs₂ accM
        (fun g hg => hnok g (by rw [hsplit]; simp [hg]))
        (by simp [haccM, elimStep, hacc₁_len])
        hmid_props.2
        hex₂
      rw [← hacc] at hlen₂
      have hlen₁ : acc₁.2.length ≤ gs₁.length := by
        have := elimPass_len m gs₁ (initVar m v b, [])
        rw [← hacc₁] at this; simpa using this
      have hsplit_len : gs.length = gs₁.length + 1 + gs₂.length := by
        rw [hsplit]; simp; omega
      have htot : acc.2.length + 2 ≤ gs.length := by omega
      cases hst : acc.1.getD C.output (Sum.inl false) with
      | inl c =>
        obtain ⟨x, x', hne⟩ := hncb
        have hx := hval x; have hx' := hval x'
        rw [hst] at hx hx'
        exact absurd (hx.symm.trans hx') hne
      | inr j =>
        have hres : HasCircuitSize m (fun x => F (Function.update x v b)) (s - 2) := by
          refine ⟨⟨acc.2, j⟩, ?_, ?_, ?_⟩
          · rw [hacc_eq]; exact elimPass_ok m gs _ (by simp)
          · show acc.2.length ≤ s - 2; omega
          · intro x; have := hval x; rw [hst] at this; exact this
        refine ⟨by omega, ?_⟩
        cases hbc : b with
        | false => rw [hbc] at hres; exact Or.inl hres
        | true => rw [hbc] at hres; exact Or.inr hres

private def elimAt (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) (i : ℕ) : Bool :=
  let acc_i := elimPass m (gs.take i) acc
  match gs[i]? with
  | none => false
  | some g =>
    (simplifyGate g.op (m + acc_i.2.length)
      (g.inputs.map fun k => acc_i.1.getD k (Sum.inl false))).1.isNone

private lemma elimAt_cons_zero (m : ℕ) (g : Gate) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimAt m (g :: gs) acc 0 =
      (simplifyGate g.op (m + acc.2.length)
        (g.inputs.map fun k => acc.1.getD k (Sum.inl false))).1.isNone := rfl

private lemma elimAt_cons_succ (m : ℕ) (g : Gate) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) (i : ℕ) :
    elimAt m (g :: gs) acc (i + 1) = elimAt m gs (elimStep m acc g) i := rfl

private lemma elimPass_len_add_sum (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    (elimPass m gs acc).2.length +
      ∑ i : Fin gs.length, (if elimAt m gs acc i.1 = true then 1 else 0) =
      acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    rw [elimPass_cons, List.length_cons]
    have hsum :
        (∑ i : Fin (gs.length + 1), if elimAt m (g :: gs) acc i.1 = true then 1 else 0) =
          (if elimAt m (g :: gs) acc 0 = true then 1 else 0) +
          ∑ i : Fin gs.length, if elimAt m gs (elimStep m acc g) i.1 = true then 1 else 0 := by
      rw [Fin.sum_univ_succ]
      rfl
    rw [hsum]
    have hih := ih (elimStep m acc g)
    have hstep : (elimStep m acc g).2.length +
        (if elimAt m (g :: gs) acc 0 = true then 1 else 0) = acc.2.length + 1 := by
      unfold elimStep
      rw [elimAt_cons_zero]
      dsimp only
      rw [List.length_append]
      generalize (simplifyGate g.op (m + acc.2.length)
        (List.map (fun i => acc.1.getD i (Sum.inl false)) g.inputs)).1 = o
      cases o <;> simp
    omega

private lemma elimPass_split_at (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (i : ℕ) (hi : i < gs.length) :
    elimPass m gs acc =
      elimPass m (gs.drop (i + 1)) (elimStep m (elimPass m (gs.take i) acc) gs[i]) := by
  have hsp : gs = gs.take i ++ [gs[i]] ++ gs.drop (i + 1) := by
    rw [List.append_assoc, List.cons_append, List.nil_append, List.getElem_cons_drop,
        List.take_append_drop]
  conv_lhs => rw [hsp]
  rw [elimPass_append, elimPass_append, elimPass_cons, elimPass_nil]

private lemma elimPass_getD_eq_take (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (i k : ℕ) (hi : i < gs.length) (hk : k < acc.1.length + i) :
    (elimPass m gs acc).1.getD k (Sum.inl false) =
      (elimPass m (gs.take i) acc).1.getD k (Sum.inl false) := by
  rw [elimPass_split_at m gs acc i hi]
  have hlen1 : (elimPass m (gs.take i) acc).1.length = acc.1.length + i := by
    rw [elimPass_fst_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
  rw [elimPass_getD_lt _ _ _ _ _ (by simp [elimStep, hlen1]; omega)]
  simp only [elimStep]
  exact getD_snoc_lt _ _ _ _ (by omega)

private lemma elimPass_getD_at (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (i : ℕ) (hi : i < gs.length) :
    (elimPass m gs acc).1.getD (acc.1.length + i) (Sum.inl false) =
      (simplifyGate gs[i].op (m + (elimPass m (gs.take i) acc).2.length)
        (gs[i].inputs.map fun k => (elimPass m (gs.take i) acc).1.getD k (Sum.inl false))).2 := by
  rw [elimPass_split_at m gs acc i hi]
  have hlen1 : (elimPass m (gs.take i) acc).1.length = acc.1.length + i := by
    rw [elimPass_fst_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
  rw [elimPass_getD_lt _ _ _ _ _ (by simp [elimStep, hlen1])]
  simp only [elimStep]
  exact getD_snoc_eq _ _ _ _ hlen1.symm

private lemma elimAt_of_const_input (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hnok : ∀ g ∈ gs, NOkGate g) (i k : ℕ) (hi : i < gs.length)
    (hk_in : k ∈ gs[i].inputs) (hk_lt : k < acc.1.length + i)
    (hc : ∃ c, (elimPass m gs acc).1.getD k (Sum.inl false) = Sum.inl c) :
    elimAt m gs acc i = true := by
  obtain ⟨c, hc⟩ := hc
  have htk : (elimPass m (gs.take i) acc).1.getD k (Sum.inl false) = Sum.inl c := by
    rw [← elimPass_getD_eq_take m gs acc i k hi hk_lt]; exact hc
  have hgi : gs[i]? = some gs[i] := List.getElem?_eq_getElem hi
  have hok := hnok gs[i] (List.getElem_mem hi)
  have hnone : (simplifyGate gs[i].op (m + (elimPass m (gs.take i) acc).2.length)
      (gs[i].inputs.map fun idx => (elimPass m (gs.take i) acc).1.getD idx (Sum.inl false))).1 = none := by
    apply simplifyGate_none_of_const
    · exact hok.1.1
    · simpa using hok.1.2
    · intro h; simpa using hok.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk_in, htk⟩⟩
  simp only [elimAt, hgi, hnone, Option.isNone_none]

private lemma elimPass_st_and_false (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hnok : ∀ g ∈ gs, NOkGate g) (i k : ℕ) (hi : i < gs.length)
    (hop : gs[i].op = GateOp.and) (hk_in : k ∈ gs[i].inputs) (hk_lt : k < acc.1.length + i)
    (hf : (elimPass m gs acc).1.getD k (Sum.inl false) = Sum.inl false) :
    (elimPass m gs acc).1.getD (acc.1.length + i) (Sum.inl false) = Sum.inl false := by
  rw [elimPass_getD_at m gs acc i hi, hop]
  have htk : (elimPass m (gs.take i) acc).1.getD k (Sum.inl false) = Sum.inl false := by
    rw [← elimPass_getD_eq_take m gs acc i k hi hk_lt]; exact hf
  have hok := hnok gs[i] (List.getElem_mem hi)
  have hres := simplifyGate_and_false (m + (elimPass m (gs.take i) acc).2.length)
    (gs[i].inputs.map fun idx => (elimPass m (gs.take i) acc).1.getD idx (Sum.inl false))
    (by simp; exact hok.1.2)
    (List.mem_map.2 ⟨k, hk_in, htk⟩)
  rw [hres]

private lemma elimPass_st_or_true (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hnok : ∀ g ∈ gs, NOkGate g) (i k : ℕ) (hi : i < gs.length)
    (hop : gs[i].op = GateOp.or) (hk_in : k ∈ gs[i].inputs) (hk_lt : k < acc.1.length + i)
    (ht : (elimPass m gs acc).1.getD k (Sum.inl false) = Sum.inl true) :
    (elimPass m gs acc).1.getD (acc.1.length + i) (Sum.inl false) = Sum.inl true := by
  rw [elimPass_getD_at m gs acc i hi, hop]
  have htk : (elimPass m (gs.take i) acc).1.getD k (Sum.inl false) = Sum.inl true := by
    rw [← elimPass_getD_eq_take m gs acc i k hi hk_lt]; exact ht
  have hok := hnok gs[i] (List.getElem_mem hi)
  have hres := simplifyGate_or_true (m + (elimPass m (gs.take i) acc).2.length)
    (gs[i].inputs.map fun idx => (elimPass m (gs.take i) acc).1.getD idx (Sum.inl false))
    (by simp; exact hok.1.2)
    (List.mem_map.2 ⟨k, hk_in, htk⟩)
  rw [hres]

private lemma elimPass_st_not_const (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (i k : ℕ) (hi : i < gs.length) (c : Bool)
    (hop : gs[i].op = GateOp.not) (hins : gs[i].inputs = [k]) (hk_lt : k < acc.1.length + i)
    (hc : (elimPass m gs acc).1.getD k (Sum.inl false) = Sum.inl c) :
    (elimPass m gs acc).1.getD (acc.1.length + i) (Sum.inl false) = Sum.inl (!c) := by
  rw [elimPass_getD_at m gs acc i hi, hop, hins, List.map_singleton]
  have htk : (elimPass m (gs.take i) acc).1.getD k (Sum.inl false) = Sum.inl c := by
    rw [← elimPass_getD_eq_take m gs acc i k hi hk_lt]; exact hc
  rw [htk]
  rfl

private lemma elimPass_st_all_const (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hnok : ∀ g ∈ gs, NOkGate g) (i : ℕ) (hi : i < gs.length)
    (hall : ∀ k ∈ gs[i].inputs, k < acc.1.length + i ∧
      ∃ c : Bool, (elimPass m gs acc).1.getD k (Sum.inl false) = Sum.inl c) :
    ∃ c : Bool, (elimPass m gs acc).1.getD (acc.1.length + i) (Sum.inl false) = Sum.inl c := by
  rw [elimPass_getD_at m gs acc i hi]
  have hok := hnok gs[i] (List.getElem_mem hi)
  apply simplifyGate_all_const
  · exact hok.1.1
  · simp; exact hok.1.2
  · intro s hs
    obtain ⟨k, hk_in, rfl⟩ := List.mem_map.1 hs
    obtain ⟨hk_lt, c, hc⟩ := hall k hk_in
    exact ⟨c, by rw [← elimPass_getD_eq_take m gs acc i k hi hk_lt]; exact hc⟩

private lemma elim_var_by_set {m : ℕ} {F : (Fin m → Bool) → Bool}
    (gs : List Gate) (out : ℕ) (hnok : ∀ g ∈ gs, NOkGate g)
    (hev : ∀ x : Fin m → Bool, (wiresFrom gs (List.ofFn x)).getD out false = F x)
    (v : Fin m) (b : Bool)
    (hnc : ∃ x x' : Fin m → Bool, F (Function.update x v b) ≠ F (Function.update x' v b))
    (S : Finset (Fin gs.length))
    (hS : ∀ i ∈ S, elimAt m gs (initVar m v b, []) i.1 = true) :
    HasCircuitSize m (fun x => F (Function.update x v b)) (gs.length - S.card) := by
  set acc := elimPass m gs (initVar m v b, []) with hacc
  have hsum := elimPass_len_add_sum m gs (initVar m v b, [])
  rw [← hacc] at hsum
  simp only [List.length_nil, zero_add] at hsum
  have hcard_le : S.card ≤ ∑ i : Fin gs.length, (if elimAt m gs (initVar m v b, []) i.1 = true then 1 else 0) := by
    have h1 : S.card = ∑ i ∈ S, (1 : ℕ) := by simp
    rw [h1]
    calc ∑ i ∈ S, (1 : ℕ)
        = ∑ i ∈ S, (if elimAt m gs (initVar m v b, []) i.1 = true then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [hS i hi]
      _ ≤ ∑ i : Fin gs.length, (if elimAt m gs (initVar m v b, []) i.1 = true then 1 else 0) := by
          apply Finset.sum_le_univ_sum_of_nonneg
          intro i; exact Nat.zero_le _
  have hval : ∀ x : Fin m → Bool,
      statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD out (Sum.inl false)) =
        F (Function.update x v b) := by
    intro x
    have hinv := elimInv_pass m (List.ofFn x) gs _ (initVar m v b, [])
      (fun g hg => (hnok g hg).1) (elimInv_initVar m v b x)
    rw [← hacc] at hinv
    rw [(hinv.2.2 out).2]
    exact hev (Function.update x v b)
  cases hst : acc.1.getD out (Sum.inl false) with
  | inl c =>
    obtain ⟨x, x', hne⟩ := hnc
    have hx := hval x; have hx' := hval x'
    rw [hst] at hx hx'
    exact absurd (hx.symm.trans hx') hne
  | inr j =>
    refine ⟨⟨acc.2, j⟩, elimPass_ok m gs _ (by simp), ?_, ?_⟩
    · show acc.2.length ≤ gs.length - S.card
      omega
    · intro x
      have := hval x
      rw [hst] at this
      exact this

private def f7 (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 5) || (x 0 && x 5) || (x 0 && x 6)

private def fC6 (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 5) || (x 0 && x 5)

private lemma no_size_zero {m : ℕ} {f : (Fin m → Bool) → Bool}
    (hnf : ∃ x : Fin m → Bool, f x = true)
    (hnp : ∀ i : Fin m, ∃ x : Fin m → Bool, f x ≠ x i) :
    ¬ HasCircuitSize m f 0 := by
  rintro ⟨C, _, hsz, hev⟩
  have hnil : C.gates = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hsz)
  by_cases hlt : C.output < m
  · obtain ⟨x, hne⟩ := hnp ⟨C.output, hlt⟩
    have h1 := hev x
    have h2 : C.eval (List.ofFn x) = x ⟨C.output, hlt⟩ := by
      simp only [Circuit.eval, Circuit.wires, hnil, List.foldl_nil]
      exact ofFn_getD_lt _ _ _ hlt
    exact hne (h1.symm.trans h2)
  · obtain ⟨x, hx⟩ := hnf
    have h1 := hev x
    have h2 : C.eval (List.ofFn x) = false := by
      simp only [Circuit.eval, Circuit.wires, hnil, List.foldl_nil]
      exact List.getD_eq_default _ _ (by simp; omega)
    rw [h2] at h1
    rw [hx] at h1
    exact Bool.false_ne_true h1

private lemma hasCircuitSize_congr {m s : ℕ} {f g : (Fin m → Bool) → Bool}
    (hfg : ∀ x, f x = g x) (hf : HasCircuitSize m f s) : HasCircuitSize m g s := by
  obtain ⟨C, hok, hsz, hev⟩ := hf
  exact ⟨C, hok, hsz, fun x => (hev x).trans (hfg x)⟩

private lemma not_size_and_pair (a b : Fin 6) (hab : a ≠ b) :
    ¬ HasCircuitSize 6 (fun x : Fin 6 → Bool => x a && x b) 0 := by
  apply no_size_zero
  · exact ⟨fun _ => true, by simp⟩
  · intro i
    by_cases hia : i = a
    · subst hia
      refine ⟨fun k => decide (k = i), ?_⟩
      simp [hab.symm]
    · refine ⟨fun k => decide (k = i), ?_⟩
      simp [Ne.symm hia]

private lemma not_size_or_and_pair (a b c : Fin 6) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ HasCircuitSize 6 (fun x : Fin 6 → Bool => x a || (x b && x c)) 0 := by
  apply no_size_zero
  · exact ⟨fun _ => true, by simp⟩
  · intro i
    by_cases hia : i = a
    · subst hia
      refine ⟨fun k => decide (k = b ∨ k = c), ?_⟩
      simp [hab, hac]
    · refine ⟨fun k => decide (k = i), ?_⟩
      by_cases hib : i = b
      · subst hib; simp [Ne.symm hia, hbc.symm]
      · simp [Ne.symm hia, Ne.symm hib]

private lemma not_size_p3 (a b c : Fin 6) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ HasCircuitSize 6 (fun x : Fin 6 → Bool => (x a && x b) || (x b && x c)) 1 := by
  intro h
  have h1 := elim_one_var a false h
    ⟨fun k => decide (k = b), by
      simp [Function.update_of_ne hab.symm, Function.update_of_ne hac.symm, hbc.symm]⟩
    ⟨fun _ => false, fun k => decide (k = b ∨ k = c), by
      simp [Function.update_of_ne hab.symm, Function.update_of_ne hac.symm]⟩
  have h2 : HasCircuitSize 6 (fun x : Fin 6 → Bool => x b && x c) 0 :=
    hasCircuitSize_congr (fun x => by simp [Function.update_of_ne hab.symm, Function.update_of_ne hac.symm]) h1.2
  exact not_size_and_pair b c hbc h2

private lemma not_size_p3_zero (a b c : Fin 6) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ HasCircuitSize 6 (fun x : Fin 6 → Bool => (x a && x b) || (x b && x c)) 0 := by
  intro h
  exact not_size_p3 a b c hab hac hbc (by
    obtain ⟨C, hok, hsz, hev⟩ := h
    exact ⟨C, hok, le_trans hsz (by omega), hev⟩)

private lemma not_size_extra_p3 (d a b c : Fin 6)
    (hda : d ≠ a) (hdb : d ≠ b) (hdc : d ≠ c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ HasCircuitSize 6 (fun x : Fin 6 → Bool => x d || ((x a && x b) || (x b && x c))) 2 := by
  intro h
  have h1 := elim_one_var d false h
    ⟨fun _ => false, by simp [Function.update_of_ne hda.symm, Function.update_of_ne hdb.symm, Function.update_of_ne hdc.symm]⟩
    ⟨fun _ => false, fun _ => true, by simp [Function.update_of_ne hda.symm, Function.update_of_ne hdb.symm, Function.update_of_ne hdc.symm]⟩
  have h2 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x a && x b) || (x b && x c)) 1 :=
    hasCircuitSize_congr (fun x => by
      simp [Function.update_of_ne hda.symm, Function.update_of_ne hdb.symm, Function.update_of_ne hdc.symm]) h1.2
  exact not_size_p3 a b c hab hac hbc h2

private lemma not_size_p4 :
    ¬ HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5)) 2 := by
  intro h
  have h1 := elim_two_var (2 : Fin 6) h
    ⟨fun k => decide (k = 3), by decide⟩
    ⟨fun _ => false, fun _ => true, by decide⟩
    ⟨fun _ => false, fun _ => true, by decide⟩
  rcases h1.2 with h0 | h1'
  · have h0' : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 3 && x 4) || (x 4 && x 5)) 0 :=
      hasCircuitSize_congr (fun x => by simp) h0
    exact not_size_p3_zero 3 4 5 (by decide) (by decide) (by decide) h0'
  · have h1'' : HasCircuitSize 6 (fun x : Fin 6 → Bool => x 3 || (x 4 && x 5)) 0 :=
      hasCircuitSize_congr (fun x => by
        simp only [Function.update, Fin.reduceEq, ↓reduceIte]
        cases x 3 <;> cases x 4 <;> cases x 5 <;> rfl) h1'
    exact not_size_or_and_pair 3 4 5 (by decide) (by decide) (by decide) h1''

private lemma not_size_fC6_true_zero :
    ¬ HasCircuitSize 6 (fun x : Fin 6 → Bool => fC6 (Function.update x 0 true)) 3 := by
  intro h
  have h0 : HasCircuitSize 6 (fun x : Fin 6 → Bool => x 1 || (x 5 || ((x 2 && x 3) || (x 3 && x 4)))) 3 :=
    hasCircuitSize_congr (fun x => by
      simp only [fC6, Function.update, Fin.reduceEq, ↓reduceIte]
      cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;> rfl) h
  have h1 := elim_one_var (1 : Fin 6) false h0
    ⟨fun _ => false, by decide⟩
    ⟨fun _ => false, fun _ => true, by decide⟩
  have h2 : HasCircuitSize 6 (fun x : Fin 6 → Bool => x 5 || ((x 2 && x 3) || (x 3 && x 4))) 2 :=
    hasCircuitSize_congr (fun x => by simp) h1.2
  exact not_size_extra_p3 5 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h2

private lemma not_size_fC6_false_zero :
    ¬ HasCircuitSize 6 (fun x : Fin 6 → Bool => fC6 (Function.update x 0 false)) 4 := by
  intro h
  have h0 : HasCircuitSize 6
      (fun x : Fin 6 → Bool => (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5)) 4 :=
    hasCircuitSize_congr (fun x => by
      simp only [fC6, Function.update, Fin.reduceEq, ↓reduceIte]
      cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;> rfl) h
  have h1 := elim_two_var (1 : Fin 6) h0
    ⟨fun k => decide (k = 2), by decide⟩
    ⟨fun _ => false, fun _ => true, by decide⟩
    ⟨fun _ => false, fun _ => true, by decide⟩
  rcases h1.2 with hf | ht
  · have hf' : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5)) 2 :=
      hasCircuitSize_congr (fun x => by simp) hf
    exact not_size_p4 hf'
  · have ht' : HasCircuitSize 6 (fun x : Fin 6 → Bool => x 2 || ((x 3 && x 4) || (x 4 && x 5))) 2 :=
      hasCircuitSize_congr (fun x => by
        simp only [Function.update, Fin.reduceEq, ↓reduceIte]
        cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;> rfl) ht
    exact not_size_extra_p3 2 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ht'

private lemma fC6_rot_step (x : Fin 6 → Bool) :
    fC6 (fun i : Fin 6 => x (i - 1)) = fC6 x := by
  simp only [fC6]
  have h0 : (0 : Fin 6) - 1 = 5 := by decide
  have h1 : (1 : Fin 6) - 1 = 0 := by decide
  have h2 : (2 : Fin 6) - 1 = 1 := by decide
  have h3 : (3 : Fin 6) - 1 = 2 := by decide
  have h4 : (4 : Fin 6) - 1 = 3 := by decide
  have h5 : (5 : Fin 6) - 1 = 4 := by decide
  rw [h0, h1, h2, h3, h4, h5]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;> rfl

private lemma fC6_rot (u : Fin 6) (x : Fin 6 → Bool) :
    fC6 (fun i : Fin 6 => x (i - u)) = fC6 x := by
  have h2 : ∀ y : Fin 6 → Bool, fC6 (fun i : Fin 6 => y (i - 2)) = fC6 y := fun y => by
    have e : (fun i : Fin 6 => y (i - 2)) = (fun i => (fun j => y (j - 1)) (i - 1)) := by
      funext i; congr 1; fin_cases i <;> decide
    exact (congrArg fC6 e).trans ((fC6_rot_step _).trans (fC6_rot_step y))
  have h3 : ∀ y : Fin 6 → Bool, fC6 (fun i : Fin 6 => y (i - 3)) = fC6 y := fun y => by
    have e : (fun i : Fin 6 => y (i - 3)) = (fun i => (fun j => y (j - 2)) (i - 1)) := by
      funext i; congr 1; fin_cases i <;> decide
    exact (congrArg fC6 e).trans ((fC6_rot_step _).trans (h2 y))
  have h4 : ∀ y : Fin 6 → Bool, fC6 (fun i : Fin 6 => y (i - 4)) = fC6 y := fun y => by
    have e : (fun i : Fin 6 => y (i - 4)) = (fun i => (fun j => y (j - 3)) (i - 1)) := by
      funext i; congr 1; fin_cases i <;> decide
    exact (congrArg fC6 e).trans ((fC6_rot_step _).trans (h3 y))
  have h5 : ∀ y : Fin 6 → Bool, fC6 (fun i : Fin 6 => y (i - 5)) = fC6 y := fun y => by
    have e : (fun i : Fin 6 => y (i - 5)) = (fun i => (fun j => y (j - 4)) (i - 1)) := by
      funext i; congr 1; fin_cases i <;> decide
    exact (congrArg fC6 e).trans ((fC6_rot_step _).trans (h4 y))
  fin_cases u
  · simp
  · exact fC6_rot_step x
  · exact h2 x
  · exact h3 x
  · exact h4 x
  · exact h5 x

private lemma hasCircuitSize_reindex {m s : ℕ} {f : (Fin m → Bool) → Bool}
    (e : Fin m → Fin m) (hC : HasCircuitSize m f s)
    (hnc : ∃ x x' : Fin m → Bool, f (fun i => x (e i)) ≠ f (fun i => x' (e i))) :
    HasCircuitSize m (fun x => f (fun i => x (e i))) s := by
  obtain ⟨C, hok, hsz, hev⟩ := hC
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOkGate g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hok g0 hg0)
  set init : List (Bool ⊕ ℕ) := List.ofFn (fun i : Fin m => Sum.inr (e i : ℕ)) with hinit
  set acc := elimPass m gs (init, []) with hacc
  have hval : ∀ x : Fin m → Bool,
      statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
        f (fun i => x (e i)) := by
    intro x
    have hinv : ElimInv m (List.ofFn x) (wiresFrom gs (List.ofFn (fun i => x (e i)))) acc := by
      apply elimInv_pass m (List.ofFn x) gs _ (init, []) (fun g hg => (hnok g hg).1)
      refine ⟨by simp, by simp [hinit], ?_⟩
      intro i
      by_cases hi : i < m
      · rw [hinit, ofFn_getD_lt _ _ _ hi]
        refine ⟨by simp [statValid], ?_⟩
        simp only [statVal, wiresFrom_nil]
        rw [ofFn_getD_lt _ _ _ (e ⟨i, hi⟩).isLt, ofFn_getD_lt _ _ _ hi]
      · rw [List.getD_eq_default _ _ (by simp [hinit]; omega),
            List.getD_eq_default _ _ (by simp; omega)]
        exact ⟨trivial, rfl⟩
    rw [(hinv.2.2 C.output).2, hgs, wiresFrom_norm]
    exact hev (fun i => x (e i))
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    obtain ⟨x, x', hne⟩ := hnc
    have hx := hval x; have hx' := hval x'
    rw [hst] at hx hx'
    exact absurd (hx.symm.trans hx') hne
  | inr j =>
    refine ⟨⟨acc.2, j⟩, elimPass_ok m gs _ (by simp), ?_, ?_⟩
    · show acc.2.length ≤ s
      have := elimPass_len m gs (init, [])
      rw [← hacc] at this
      have hlen : gs.length = C.gates.length := by simp [hgs]
      have hsz' : C.gates.length ≤ s := hsz
      simp only [List.length_nil, zero_add] at this
      omega
    · intro x
      have := hval x
      rw [hst] at this
      exact this

private lemma fC6_update_rot (u : Fin 6) (b : Bool) (x : Fin 6 → Bool) :
    fC6 (Function.update (fun i : Fin 6 => x (i - u)) u b) =
      fC6 (Function.update x 0 b) := by
  have hfun : Function.update (fun i : Fin 6 => x (i - u)) u b =
      fun i : Fin 6 => Function.update x 0 b (i - u) := by
    funext i
    by_cases hiu : i = u
    · subst hiu; simp
    · have hne : i - u ≠ 0 := sub_ne_zero.mpr hiu
      rw [Function.update_of_ne hiu, Function.update_of_ne hne]
  rw [hfun]
  exact fC6_rot u (Function.update x 0 b)

private lemma fC6_update_nc (u : Fin 6) (b : Bool) :
    ∃ x x' : Fin 6 → Bool,
      fC6 (Function.update x u b) ≠ fC6 (Function.update x' u b) := by
  refine ⟨fun _ => false, fun _ => true, ?_⟩
  have h1 : fC6 (Function.update (fun _ : Fin 6 => false) u b) = false := by
    have := fC6_update_rot u b (fun _ => false)
    rw [this]; cases b <;> decide
  have h2 : fC6 (Function.update (fun _ : Fin 6 => true) u b) = true := by
    have := fC6_update_rot u b (fun _ => true)
    rw [this]; cases b <;> decide
  rw [h1, h2]
  exact Bool.false_ne_true

private lemma not_size_fC6_true (u : Fin 6) :
    ¬ HasCircuitSize 6 (fun x : Fin 6 → Bool => fC6 (Function.update x u true)) 3 := by
  intro h
  have hnc : ∃ x x' : Fin 6 → Bool,
      fC6 (Function.update (fun i => x (i - u)) u true) ≠
      fC6 (Function.update (fun i => x' (i - u)) u true) := by
    refine ⟨fun _ => false, fun _ => true, ?_⟩
    rw [fC6_update_rot u true (fun _ => false), fC6_update_rot u true (fun _ => true)]
    decide
  have hr := hasCircuitSize_reindex (fun i : Fin 6 => i - u) h hnc
  exact not_size_fC6_true_zero (hasCircuitSize_congr (fun x => fC6_update_rot u true x) hr)

private lemma not_size_fC6_false (u : Fin 6) :
    ¬ HasCircuitSize 6 (fun x : Fin 6 → Bool => fC6 (Function.update x u false)) 4 := by
  intro h
  have hnc : ∃ x x' : Fin 6 → Bool,
      fC6 (Function.update (fun i => x (i - u)) u false) ≠
      fC6 (Function.update (fun i => x' (i - u)) u false) := by
    refine ⟨fun _ => false, fun _ => true, ?_⟩
    rw [fC6_update_rot u false (fun _ => false), fC6_update_rot u false (fun _ => true)]
    decide
  have hr := hasCircuitSize_reindex (fun i : Fin 6 => i - u) h hnc
  exact not_size_fC6_false_zero (hasCircuitSize_congr (fun x => fC6_update_rot u false x) hr)

private lemma drop_last_var (h8 : HasCircuitSize 7 f7 8) : HasCircuitSize 6 fC6 7 := by
  have h1 := elim_one_var (6 : Fin 7) false h8
    ⟨fun i => decide (i = 0), by decide⟩
    ⟨fun _ => false, fun _ => true, by decide⟩
  obtain ⟨C, hok, hsz, hev⟩ := h1.2
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOkGate g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hok g0 hg0)
  set init : List (Bool ⊕ ℕ) :=
    List.ofFn (fun j : Fin 6 => Sum.inr (j : ℕ)) ++ [Sum.inl false] with hinit
  set acc := elimPass 6 gs (init, []) with hacc
  have hval : ∀ y : Fin 6 → Bool,
      statVal (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD C.output (Sum.inl false)) = fC6 y := by
    intro y
    let x7 : Fin 7 → Bool := fun i => if h : i.1 < 6 then y ⟨i.1, h⟩ else false
    have hinv : ElimInv 6 (List.ofFn y) (wiresFrom gs (List.ofFn x7)) acc := by
      apply elimInv_pass 6 (List.ofFn y) gs _ (init, []) (fun g hg => (hnok g hg).1)
      refine ⟨by simp, by simp [hinit], ?_⟩
      intro i
      by_cases hlt : i < 6
      · have hget : init.getD i (Sum.inl false) = Sum.inr i := by
          rw [hinit, getD_snoc_lt _ _ _ _ (by simp; exact hlt), ofFn_getD_lt _ _ _ hlt]
        rw [hget]
        refine ⟨by simp [statValid]; exact hlt, ?_⟩
        simp only [statVal, wiresFrom_nil]
        rw [ofFn_getD_lt _ _ _ hlt, ofFn_getD_lt _ _ _ (by omega : i < 7)]
        simp [x7, hlt]
      · by_cases heq : i = 6
        · subst heq
          have hget : init.getD 6 (Sum.inl false) = Sum.inl false := by
            rw [hinit]; exact getD_snoc_eq _ _ _ _ (by simp)
          rw [hget]
          refine ⟨trivial, ?_⟩
          simp only [statVal]
          rw [ofFn_getD_lt _ _ _ (by omega : 6 < 7)]
          simp [x7]
        · rw [List.getD_eq_default _ _ (by simp [hinit]; omega),
              List.getD_eq_default _ _ (by simp; omega)]
          exact ⟨trivial, rfl⟩
    rw [(hinv.2.2 C.output).2, hgs, wiresFrom_norm]
    have hx7 : (wiresFrom C.gates (List.ofFn x7)).getD C.output false =
        f7 (Function.update x7 6 false) := hev x7
    rw [hx7]
    simp [f7, fC6, x7, Function.update]
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    have h0 := hval (fun _ => false)
    have h1' := hval (fun _ => true)
    rw [hst] at h0 h1'
    have hne : fC6 (fun _ => false) ≠ fC6 (fun _ => true) := by decide
    exact absurd (h0.symm.trans h1') hne
  | inr j =>
    refine ⟨⟨acc.2, j⟩, elimPass_ok 6 gs _ (by simp), ?_, ?_⟩
    · show acc.2.length ≤ 7
      have := elimPass_len 6 gs (init, [])
      rw [← hacc] at this
      have hlen : gs.length = C.gates.length := by simp [hgs]
      have hsz' : C.gates.length ≤ 7 := hsz
      simp only [List.length_nil, zero_add] at this
      omega
    · intro y
      have := hval y
      rw [hst] at this
      exact this

private lemma elim_gate_at {m : ℕ} {F : (Fin m → Bool) → Bool}
    (hnc : ∃ x x' : Fin m → Bool, F x ≠ F x')
    (gs₁ gs₂ : List Gate) (g : Gate) (out : ℕ)
    (hok : ∀ g' ∈ gs₁ ++ [g] ++ gs₂, OkGate g')
    (hev : ∀ x : Fin m → Bool, (wiresFrom (gs₁ ++ [g] ++ gs₂) (List.ofFn x)).getD out false = F x)
    (r : Bool ⊕ ℕ) (hr_val : statValid (m + gs₁.length) r)
    (hr_eq : ∀ x : Fin m → Bool,
      statVal (wiresFrom gs₁ (List.ofFn x)) r =
        (wiresFrom (gs₁ ++ [g]) (List.ofFn x)).getD (m + gs₁.length) false) :
    HasCircuitSize m F (gs₁.length + gs₂.length) := by
  set init : List (Bool ⊕ ℕ) :=
    List.ofFn (fun i : Fin (m + gs₁.length) => Sum.inr (i : ℕ)) ++ [r] with hinit
  set acc := elimPass m gs₂ (init, gs₁) with hacc
  have hval : ∀ x : Fin m → Bool,
      statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD out (Sum.inl false)) = F x := by
    intro x
    have hinv : ElimInv m (List.ofFn x) (wiresFrom (gs₁ ++ [g] ++ gs₂) (List.ofFn x)) acc := by
      rw [wiresFrom_append]
      apply elimInv_pass m (List.ofFn x) gs₂ _ (init, gs₁)
        (fun g' hg' => hok g' (by simp [hg']))
      refine ⟨by simp, ?_, ?_⟩
      · simp [hinit, wiresFrom_length]; omega
      · intro i
        by_cases hlt : i < m + gs₁.length
        · have hget : init.getD i (Sum.inl false) = Sum.inr i := by
            rw [hinit, getD_snoc_lt _ _ _ _ (by simp; exact hlt), ofFn_getD_lt _ _ _ hlt]
          rw [hget]
          refine ⟨by simp [statValid]; exact hlt, ?_⟩
          simp only [statVal]
          rw [wiresFrom_append, wiresFrom_getD_lt [g] _ _ (by simp [wiresFrom_length]; exact hlt)]
        · by_cases heq : i = m + gs₁.length
          · subst heq
            have hget : init.getD (m + gs₁.length) (Sum.inl false) = r := by
              rw [hinit]; exact getD_snoc_eq _ _ _ _ (by simp)
            rw [hget]
            exact ⟨hr_val, hr_eq x⟩
          · rw [List.getD_eq_default _ _ (by simp [hinit]; omega),
                List.getD_eq_default _ _ (by simp [wiresFrom_length]; omega)]
            exact ⟨trivial, rfl⟩
    rw [(hinv.2.2 out).2]
    exact hev x
  cases hst : acc.1.getD out (Sum.inl false) with
  | inl c =>
    obtain ⟨x, x', hne⟩ := hnc
    have hx := hval x; have hx' := hval x'
    rw [hst] at hx hx'
    exact absurd (hx.symm.trans hx') hne
  | inr j =>
    refine ⟨⟨acc.2, j⟩, elimPass_ok m gs₂ (init, gs₁) (fun g' hg' => hok g' (by simp [hg'])), ?_, ?_⟩
    · show acc.2.length ≤ gs₁.length + gs₂.length
      have := elimPass_len m gs₂ (init, gs₁)
      rw [← hacc] at this
      exact this
    · intro x
      have := hval x
      rw [hst] at this
      exact this

private lemma elim_unused_gate {m : ℕ} {F : (Fin m → Bool) → Bool}
    (hnc : ∃ x x' : Fin m → Bool, F x ≠ F x')
    (gs₁ gs₂ : List Gate) (g : Gate) (out : ℕ)
    (hok : ∀ g' ∈ gs₁ ++ [g] ++ gs₂, OkGate g')
    (hev : ∀ x : Fin m → Bool, (wiresFrom (gs₁ ++ [g] ++ gs₂) (List.ofFn x)).getD out false = F x)
    (hout : out ≠ m + gs₁.length)
    (hno : ∀ d ∈ gs₂, m + gs₁.length ∉ d.inputs) :
    HasCircuitSize m F (gs₁.length + gs₂.length) := by
  let g0 : Gate := ⟨GateOp.or, []⟩
  have hok' : ∀ g' ∈ gs₁ ++ [g0] ++ gs₂, OkGate g' := by
    intro g' hg'
    simp only [List.mem_append, List.mem_singleton] at hg'
    rcases hg' with (h1 | rfl) | h2
    · exact hok g' (by simp [h1])
    · exact ⟨Or.inr (Or.inl rfl), by simp [g0]⟩
    · exact hok g' (by simp [h2])
  have hev' : ∀ x : Fin m → Bool,
      (wiresFrom (gs₁ ++ [g0] ++ gs₂) (List.ofFn x)).getD out false = F x := by
    intro x
    have hag := wiresFrom_agree gs₂ {m + gs₁.length}
      (wiresFrom (gs₁ ++ [g0]) (List.ofFn x))
      (wiresFrom (gs₁ ++ [g]) (List.ofFn x))
      (by simp [wiresFrom_length])
      (by intro u hu; simp at hu; subst hu; simp [wiresFrom_length])
      (by
        intro i hi; simp at hi
        rw [wiresFrom_append, wiresFrom_append, wiresFrom_cons, wiresFrom_cons,
            wiresFrom_nil, wiresFrom_nil]
        rw [getD_snoc_ne _ _ _ _ (by simp [wiresFrom_length]; exact hi),
            getD_snoc_ne _ _ _ _ (by simp [wiresFrom_length]; exact hi)])
      (by
        intro d hd i hi hmem
        simp at hmem; subst hmem
        exact hno d hd hi)
    have hEq := hag.2 out (by simpa using hout)
    rw [wiresFrom_append, hEq, ← wiresFrom_append]
    exact hev x
  apply elim_gate_at hnc gs₁ gs₂ g0 out hok' hev' (Sum.inl false) trivial
  intro x
  rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
  rw [getD_snoc_eq _ _ _ _ (by simp [wiresFrom_length])]
  rfl

private lemma replace_gate_at {m : ℕ} (gs₁ gs₂ : List Gate) (g g' : Gate)
    (heq : ∀ x : Fin m → Bool,
      g'.op.eval (g'.inputs.map fun i => (wiresFrom gs₁ (List.ofFn x)).getD i false) =
      g.op.eval (g.inputs.map fun i => (wiresFrom gs₁ (List.ofFn x)).getD i false))
    (x : Fin m → Bool) :
    wiresFrom (gs₁ ++ [g'] ++ gs₂) (List.ofFn x) = wiresFrom (gs₁ ++ [g] ++ gs₂) (List.ofFn x) := by
  rw [wiresFrom_append, wiresFrom_append, wiresFrom_append, wiresFrom_append,
      wiresFrom_cons, wiresFrom_cons, wiresFrom_nil, wiresFrom_nil, heq x]

private lemma split_list_at {α : Type*} (l : List α) (i : ℕ) (hi : i < l.length) :
    l = l.take i ++ [l[i]] ++ l.drop (i + 1) := by
  rw [List.append_assoc, List.cons_append, List.nil_append, List.getElem_cons_drop,
      List.take_append_drop]

private lemma min_inputs_lt {m : ℕ} {F : (Fin m → Bool) → Bool}
    (hnc : ∃ x x' : Fin m → Bool, F x ≠ F x')
    (gs : List Gate) (out : ℕ)
    (hnok : ∀ g ∈ gs, NOkGate g)
    (hev : ∀ x : Fin m → Bool, (wiresFrom gs (List.ofFn x)).getD out false = F x)
    (hmin : ¬ HasCircuitSize m F (gs.length - 1))
    (i : ℕ) (hi : i < gs.length) (k : ℕ) (hk : k ∈ gs[i].inputs) :
    k < m + i := by
  by_contra hge
  push Not at hge
  have hsp := split_list_at gs i hi
  set gs₁ := gs.take i
  set gs₂ := gs.drop (i + 1)
  have hlen1 : gs₁.length = i := by simp [gs₁, Nat.min_eq_left (Nat.le_of_lt hi)]
  have hlen_tot : gs₁.length + gs₂.length = gs.length - 1 := by
    simp [gs₁, gs₂, Nat.min_eq_left (Nat.le_of_lt hi)]; omega
  have hok_sp : ∀ g' ∈ gs₁ ++ [gs[i]] ++ gs₂, OkGate g' := by
    intro g' hg'; rw [← hsp] at hg'; exact (hnok g' hg').1
  have hev_sp : ∀ x : Fin m → Bool, (wiresFrom (gs₁ ++ [gs[i]] ++ gs₂) (List.ofFn x)).getD out false = F x := by
    intro x; rw [← hsp]; exact hev x
  have hgi_nok := hnok gs[i] (List.getElem_mem hi)
  have hval_k : ∀ x : Fin m → Bool, (wiresFrom gs₁ (List.ofFn x)).getD k false = false := by
    intro x; exact List.getD_eq_default _ _ (by simp [wiresFrom_length, hlen1]; omega)
  have hcontra : ∃ r : Bool ⊕ ℕ, statValid (m + gs₁.length) r ∧
      ∀ x : Fin m → Bool, statVal (wiresFrom gs₁ (List.ofFn x)) r =
        (wiresFrom (gs₁ ++ [gs[i]]) (List.ofFn x)).getD (m + gs₁.length) false := by
    rcases hgi_nok.1.1 with hop | hop | hop
    · refine ⟨Sum.inl false, trivial, fun x => ?_⟩
      rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil,
          getD_snoc_eq _ _ _ _ (by simp [wiresFrom_length])]
      rw [hop]
      simp only [statVal, GateOp.eval]
      symm
      rw [List.all_eq_false]
      exact ⟨false, List.mem_map.2 ⟨k, hk, hval_k x⟩, by simp⟩
    · have hlen2 : gs[i].inputs.length ≤ 2 := hgi_nok.1.2
      rcases hins : gs[i].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
      · rw [hins] at hk; simp at hk
      · rw [hins] at hk; simp at hk; subst hk
        refine ⟨Sum.inl false, trivial, fun x => ?_⟩
        rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil,
            getD_snoc_eq _ _ _ _ (by simp [wiresFrom_length])]
        rw [hop, hins]
        simp only [statVal, GateOp.eval, List.map_cons, List.map_nil, hval_k x, List.any_cons,
          List.any_nil, id_eq, Bool.or_false]
      · rw [hins] at hk; simp at hk
        rcases hk with rfl | rfl
        · by_cases hb : b < m + gs₁.length
          · refine ⟨Sum.inr b, hb, fun x => ?_⟩
            rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil,
                getD_snoc_eq _ _ _ _ (by simp [wiresFrom_length])]
            rw [hop, hins]
            simp only [statVal, GateOp.eval, List.map_cons, List.map_nil, hval_k x, List.any_cons,
              List.any_nil, id_eq, Bool.false_or, Bool.or_false]
          · refine ⟨Sum.inl false, trivial, fun x => ?_⟩
            rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil,
                getD_snoc_eq _ _ _ _ (by simp [wiresFrom_length])]
            have hvb : (wiresFrom gs₁ (List.ofFn x)).getD b false = false :=
              List.getD_eq_default _ _ (by simp [wiresFrom_length]; omega)
            rw [hop, hins]
            simp only [statVal, GateOp.eval, List.map_cons, List.map_nil, hval_k x, hvb,
              List.any_cons, List.any_nil, id_eq, Bool.or_false]
        · by_cases ha : a < m + gs₁.length
          · refine ⟨Sum.inr a, ha, fun x => ?_⟩
            rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil,
                getD_snoc_eq _ _ _ _ (by simp [wiresFrom_length])]
            rw [hop, hins]
            simp only [statVal, GateOp.eval, List.map_cons, List.map_nil, hval_k x, List.any_cons,
              List.any_nil, id_eq, Bool.or_false]
          · refine ⟨Sum.inl false, trivial, fun x => ?_⟩
            rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil,
                getD_snoc_eq _ _ _ _ (by simp [wiresFrom_length])]
            have hva : (wiresFrom gs₁ (List.ofFn x)).getD a false = false :=
              List.getD_eq_default _ _ (by simp [wiresFrom_length]; omega)
            rw [hop, hins]
            simp only [statVal, GateOp.eval, List.map_cons, List.map_nil, hval_k x, hva,
              List.any_cons, List.any_nil, id_eq, Bool.or_false]
      · rw [hins] at hlen2; simp at hlen2
    · have hlen1' := hgi_nok.2 hop
      rcases hins : gs[i].inputs with _ | ⟨a, _ | ⟨b, l⟩⟩
      · rw [hins] at hk; simp at hk
      · rw [hins] at hk; simp at hk; subst hk
        refine ⟨Sum.inl true, trivial, fun x => ?_⟩
        rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil,
            getD_snoc_eq _ _ _ _ (by simp [wiresFrom_length])]
        rw [hop, hins]
        simp only [statVal, GateOp.eval, List.map_cons, List.map_nil, hval_k x, List.headD_cons,
          Bool.not_false]
      · rw [hins] at hlen1'; simp at hlen1'
  obtain ⟨r, hr_val, hr_eq⟩ := hcontra
  have hres := elim_gate_at hnc gs₁ gs₂ gs[i] out hok_sp hev_sp r hr_val hr_eq
  rw [hlen_tot] at hres
  exact hmin hres

private lemma min_not_inputs {m : ℕ} {F : (Fin m → Bool) → Bool}
    (hnc : ∃ x x' : Fin m → Bool, F x ≠ F x')
    (gs : List Gate) (out : ℕ)
    (hnok : ∀ g ∈ gs, NOkGate g)
    (hev : ∀ x : Fin m → Bool, (wiresFrom gs (List.ofFn x)).getD out false = F x)
    (hmin : ¬ HasCircuitSize m F (gs.length - 1))
    (i : ℕ) (hi : i < gs.length) (hop : gs[i].op = GateOp.not) :
    ∃ a : ℕ, gs[i].inputs = [a] ∧ a < m + i := by
  have hgi_nok := hnok gs[i] (List.getElem_mem hi)
  have hlen1 := hgi_nok.2 hop
  rcases hins : gs[i].inputs with _ | ⟨a, _ | ⟨b, l⟩⟩
  · exfalso
    have hsp := split_list_at gs i hi
    set gs₁ := gs.take i
    set gs₂ := gs.drop (i + 1)
    have hlen_tot : gs₁.length + gs₂.length = gs.length - 1 := by
      simp [gs₁, gs₂, Nat.min_eq_left (Nat.le_of_lt hi)]; omega
    have hres := elim_gate_at hnc gs₁ gs₂ gs[i] out
      (fun g' hg' => (hnok g' (by rw [hsp]; exact hg')).1)
      (fun x => by rw [← hsp]; exact hev x)
      (Sum.inl true) trivial
      (fun x => by
        rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil,
            getD_snoc_eq _ _ _ _ (by simp [wiresFrom_length]), hop, hins]
        rfl)
    rw [hlen_tot] at hres
    exact hmin hres
  · exact ⟨a, rfl, min_inputs_lt hnc gs out hnok hev hmin i hi a (by rw [hins]; simp)⟩
  · rw [hins] at hlen1; simp at hlen1

private lemma min_bin_inputs {m : ℕ} {F : (Fin m → Bool) → Bool}
    (hnc : ∃ x x' : Fin m → Bool, F x ≠ F x')
    (gs : List Gate) (out : ℕ)
    (hnok : ∀ g ∈ gs, NOkGate g)
    (hev : ∀ x : Fin m → Bool, (wiresFrom gs (List.ofFn x)).getD out false = F x)
    (hmin : ¬ HasCircuitSize m F (gs.length - 1))
    (i : ℕ) (hi : i < gs.length) (hop : gs[i].op = GateOp.and ∨ gs[i].op = GateOp.or) :
    ∃ a b : ℕ, gs[i].inputs = [a, b] ∧ a ≠ b ∧ a < m + i ∧ b < m + i := by
  have hgi_nok := hnok gs[i] (List.getElem_mem hi)
  have hlen2 := hgi_nok.1.2
  have hsp := split_list_at gs i hi
  set gs₁ := gs.take i
  set gs₂ := gs.drop (i + 1)
  have hlen1 : gs₁.length = i := by simp [gs₁, Nat.min_eq_left (Nat.le_of_lt hi)]
  have hlen_tot : gs₁.length + gs₂.length = gs.length - 1 := by
    simp [gs₁, gs₂, Nat.min_eq_left (Nat.le_of_lt hi)]; omega
  rcases hins : gs[i].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · exfalso
    have hres := elim_gate_at hnc gs₁ gs₂ gs[i] out
      (fun g' hg' => (hnok g' (by rw [hsp]; exact hg')).1)
      (fun x => by rw [← hsp]; exact hev x)
      (Sum.inl (match gs[i].op with | GateOp.and => true | _ => false)) trivial
      (fun x => by
        rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil,
            getD_snoc_eq _ _ _ _ (by simp [wiresFrom_length]), hins]
        rcases hop with h | h <;> simp [h, statVal, GateOp.eval])
    rw [hlen_tot] at hres
    exact hmin hres
  · exfalso
    have ha : a < m + i := min_inputs_lt hnc gs out hnok hev hmin i hi a (by rw [hins]; simp)
    have hres := elim_gate_at hnc gs₁ gs₂ gs[i] out
      (fun g' hg' => (hnok g' (by rw [hsp]; exact hg')).1)
      (fun x => by rw [← hsp]; exact hev x)
      (Sum.inr a) (by simp [statValid, hlen1]; exact ha)
      (fun x => by
        rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil,
            getD_snoc_eq _ _ _ _ (by simp [wiresFrom_length]), hins]
        rcases hop with h | h <;> simp [h, statVal, GateOp.eval])
    rw [hlen_tot] at hres
    exact hmin hres
  · have ha : a < m + i := min_inputs_lt hnc gs out hnok hev hmin i hi a (by rw [hins]; simp)
    have hb : b < m + i := min_inputs_lt hnc gs out hnok hev hmin i hi b (by rw [hins]; simp)
    by_cases hab : a = b
    · exfalso
      subst hab
      have hres := elim_gate_at hnc gs₁ gs₂ gs[i] out
        (fun g' hg' => (hnok g' (by rw [hsp]; exact hg')).1)
        (fun x => by rw [← hsp]; exact hev x)
        (Sum.inr a) (by simp [statValid, hlen1]; exact ha)
        (fun x => by
          rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil,
              getD_snoc_eq _ _ _ _ (by simp [wiresFrom_length]), hins]
          rcases hop with h | h <;> simp [h, statVal, GateOp.eval])
      rw [hlen_tot] at hres
      exact hmin hres
    · exact ⟨a, b, rfl, hab, ha, hb⟩
  · rw [hins] at hlen2; simp at hlen2

private lemma min_gate_used {m : ℕ} {F : (Fin m → Bool) → Bool}
    (hnc : ∃ x x' : Fin m → Bool, F x ≠ F x')
    (gs : List Gate) (out : ℕ)
    (hnok : ∀ g ∈ gs, NOkGate g)
    (hev : ∀ x : Fin m → Bool, (wiresFrom gs (List.ofFn x)).getD out false = F x)
    (hmin : ¬ HasCircuitSize m F (gs.length - 1))
    (i : ℕ) (hi : i < gs.length) (hout : out ≠ m + i) :
    ∃ j : Fin gs.length, i < j.1 ∧ m + i ∈ gs[j.1].inputs := by
  by_contra hno
  push Not at hno
  have hsp := split_list_at gs i hi
  set gs₁ := gs.take i
  set gs₂ := gs.drop (i + 1)
  have hlen1 : gs₁.length = i := by simp [gs₁, Nat.min_eq_left (Nat.le_of_lt hi)]
  have hlen_tot : gs₁.length + gs₂.length = gs.length - 1 := by
    simp [gs₁, gs₂, Nat.min_eq_left (Nat.le_of_lt hi)]; omega
  have hres := elim_unused_gate hnc gs₁ gs₂ gs[i] out
    (fun g' hg' => (hnok g' (by rw [hsp]; exact hg')).1)
    (fun x => by rw [← hsp]; exact hev x)
    (by rw [hlen1]; exact hout)
    (by
      intro d hd
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hd
      rw [List.getElem_drop]
      have hlt : i + 1 + k < gs.length := by
        simp [gs₂] at hk; omega
      rw [hlen1]
      exact hno ⟨i + 1 + k, hlt⟩ (by dsimp; omega))
  rw [hlen_tot] at hres
  exact hmin hres

private lemma fC6_nc : ∃ x x' : Fin 6 → Bool, fC6 x ≠ fC6 x' :=
  ⟨fun _ => false, fun _ => true, by decide⟩

private lemma fC6_not_literal (u : Fin 6) (pol : Bool) :
    ∃ x : Fin 6 → Bool, fC6 x ≠ (if pol then x u else !(x u)) := by
  cases pol with
  | true =>
    refine ⟨fun i => decide (i = u), ?_⟩
    have h0 : fC6 (fun i => decide (i = u)) = false := by
      fin_cases u <;> decide
    simp [h0]
  | false =>
    refine ⟨fun _ => false, ?_⟩
    have h0 : fC6 (fun _ => false) = false := by decide
    simp [h0]

private lemma fC6_not_two_vars (u v : Fin 6) :
    ∃ x y : Fin 6 → Bool, x u = y u ∧ x v = y v ∧ fC6 x ≠ fC6 y := by
  have h : ∃ a b : Fin 6, a ≠ u ∧ a ≠ v ∧ b ≠ u ∧ b ≠ v ∧
      fC6 (fun i => decide (i = a ∨ i = b)) = true := by
    fin_cases u <;> fin_cases v <;> decide
  obtain ⟨a, b, hau, hav, hbu, hbv, htrue⟩ := h
  refine ⟨fun _ => false, fun i => decide (i = a ∨ i = b), ?_, ?_, ?_⟩
  · simp [hau.symm, hbu.symm]
  · simp [hav.symm, hbv.symm]
  · rw [htrue]; decide

private lemma fC6_no_bottleneck (u v : Fin 6) (huv : u ≠ v)
    (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (pa pb : Bool) :
    ∃ x y : Fin 6 → Bool,
      (∀ w : Fin 6, w ≠ u → w ≠ v → x w = y w) ∧
      op.eval [if pa then x u else !(x u), if pb then x v else !(x v)] =
      op.eval [if pa then y u else !(y u), if pb then y v else !(y v)] ∧
      fC6 x ≠ fC6 y := by
  have hsep : ∀ p0 q0 : Bool, ∃ (p1 q1 p2 q2 : Bool) (w : Fin 6),
      w ≠ u ∧ w ≠ v ∧
      ((p1 = p0 ∧ q1 = q0) ∨ (p1 = p0 ∧ q1 = !q0) ∨ (p1 = !p0 ∧ q1 = q0)) ∧
      ((p2 = p0 ∧ q2 = q0) ∨ (p2 = p0 ∧ q2 = !q0) ∨ (p2 = !p0 ∧ q2 = q0)) ∧
      fC6 (Function.update (Function.update (fun i => decide (i = w)) u p1) v q1) ≠
      fC6 (Function.update (Function.update (fun i => decide (i = w)) u p2) v q2) := by
    intro p0 q0
    fin_cases u <;> fin_cases v <;> first | exact absurd rfl huv | cases p0 <;> cases q0 <;> decide
  set p0 : Bool := match op with | GateOp.and => pa | _ => !pa
  set q0 : Bool := match op with | GateOp.and => pb | _ => !pb
  obtain ⟨p1, q1, p2, q2, w, hwu, hwv, h1, h2, hne⟩ := hsep (!p0) (!q0)
  refine ⟨Function.update (Function.update (fun i => decide (i = w)) u p1) v q1,
          Function.update (Function.update (fun i => decide (i = w)) u p2) v q2, ?_, ?_, hne⟩
  · intro z hzu hzv
    simp [Function.update_of_ne hzv, Function.update_of_ne hzu]
  · simp only [Function.update_self, Function.update_of_ne huv]
    rcases hop with rfl | rfl
    · simp only [GateOp.eval, p0, q0] at h1 h2 ⊢
      clear hsep hne
      cases pa <;> cases pb <;> cases p1 <;> cases q1 <;> cases p2 <;> cases q2 <;> simp_all
    · simp only [GateOp.eval, p0, q0] at h1 h2 ⊢
      clear hsep hne
      cases pa <;> cases pb <;> cases p1 <;> cases q1 <;> cases p2 <;> cases q2 <;> simp_all

private lemma min_has_binary_gate (gs : List Gate) (out : ℕ)
    (hnok : ∀ g ∈ gs, NOkGate g)
    (hev : ∀ x : Fin 6 → Bool, (wiresFrom gs (List.ofFn x)).getD out false = fC6 x) :
    ∃ i : ℕ, i < gs.length ∧ (gs[i]?.map Gate.op = some GateOp.and ∨ gs[i]?.map Gate.op = some GateOp.or) := by
  by_contra hno
  have hall_not : ∀ g ∈ gs, g.op = GateOp.not := by
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hg
    have hok := (hnok gs[i] (List.getElem_mem hi)).1.1
    rcases hok with h | h | h
    · exfalso; apply hno; exact ⟨i, hi, Or.inl (by simp [List.getElem?_eq_getElem hi, h])⟩
    · exfalso; apply hno; exact ⟨i, hi, Or.inr (by simp [List.getElem?_eq_getElem hi, h])⟩
    · exact h
  have hwire : ∀ (l : List Gate), (∀ g ∈ l, g.op = GateOp.not) →
      ∀ k : ℕ, (∃ c : Bool, ∀ x : Fin 6 → Bool, (wiresFrom l (List.ofFn x)).getD k false = c) ∨
        (∃ (u : Fin 6) (pol : Bool), ∀ x : Fin 6 → Bool,
          (wiresFrom l (List.ofFn x)).getD k false = if pol then x u else !(x u)) := by
    intro l
    induction l using List.reverseRecOn with
    | nil =>
      intro _ k
      by_cases hk : k < 6
      · exact Or.inr ⟨⟨k, hk⟩, true, fun x => by simp only [wiresFrom_nil]; exact ofFn_getD_lt _ _ _ hk⟩
      · exact Or.inl ⟨false, fun x => by
          simp only [wiresFrom_nil]; exact List.getD_eq_default _ _ (by simp; omega)⟩
    | append_singleton l g ih =>
      intro hl k
      have hl' : ∀ g' ∈ l, g'.op = GateOp.not := fun g' hg' => hl g' (by simp [hg'])
      have hg : g.op = GateOp.not := hl g (by simp)
      by_cases hlt : k < 6 + l.length
      · rcases ih hl' k with ⟨c, hc⟩ | ⟨u, pol, hu⟩
        · exact Or.inl ⟨c, fun x => by
            rw [wiresFrom_append, wiresFrom_getD_lt _ _ _ (by simp [wiresFrom_length]; exact hlt)]
            exact hc x⟩
        · exact Or.inr ⟨u, pol, fun x => by
            rw [wiresFrom_append, wiresFrom_getD_lt _ _ _ (by simp [wiresFrom_length]; exact hlt)]
            exact hu x⟩
      · by_cases heq : k = 6 + l.length
        · subst heq
          cases hgi : g.inputs with
          | nil =>
            exact Or.inl ⟨true, fun x => by
              rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil,
                  getD_snoc_eq _ _ _ _ (by simp [wiresFrom_length]), hg, hgi]
              rfl⟩
          | cons a tl =>
            rcases ih hl' a with ⟨c, hc⟩ | ⟨u, pol, hu⟩
            · exact Or.inl ⟨!c, fun x => by
                rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil,
                    getD_snoc_eq _ _ _ _ (by simp [wiresFrom_length]), hg, hgi]
                simp only [GateOp.eval, List.map_cons, List.headD_cons, hc x]⟩
            · exact Or.inr ⟨u, !pol, fun x => by
                rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil,
                    getD_snoc_eq _ _ _ _ (by simp [wiresFrom_length]), hg, hgi]
                simp only [GateOp.eval, List.map_cons, List.headD_cons, hu x]
                cases pol <;> simp⟩
        · exact Or.inl ⟨false, fun x => by
            exact List.getD_eq_default _ _ (by simp [wiresFrom_length]; omega)⟩
  rcases hwire gs hall_not out with ⟨c, hc⟩ | ⟨u, pol, hu⟩
  · obtain ⟨x, x', hne⟩ := fC6_nc
    exact hne ((hev x).symm.trans ((hc x).trans ((hc x').symm.trans (hev x'))))
  · obtain ⟨x, hne⟩ := fC6_not_literal u pol
    exact hne ((hev x).symm.trans (hu x))

private lemma elim_case_branch
    (gs : List Gate) (out : ℕ)
    (hnok : ∀ g ∈ gs, NOkGate g)
    (hev : ∀ x : Fin 6 → Bool, (wiresFrom gs (List.ofFn x)).getD out false = fC6 x)
    (hmin : ¬ HasCircuitSize 6 fC6 (gs.length - 1))
    (hlen_le : gs.length ≤ 7)
    (iStar : ℕ) (hiStar : iStar < gs.length)
    (hpre : ∀ (j : ℕ) (hj : j < iStar), ∃ u : Fin 6, gs[j]'(Nat.lt_trans hj hiStar) = ⟨GateOp.not, [u.1]⟩)
    (opStar : GateOp) (hopStar : gs[iStar].op = opStar)
    (hop_bin : opStar = GateOp.and ∨ opStar = GateOp.or)
    (a b : ℕ) (hinsStar : gs[iStar].inputs = [a, b] ∨ gs[iStar].inputs = [b, a])
    (ha_lt : a < 6 + iStar) (hb_lt : b < 6 + iStar)
    (u v : Fin 6) (huv : u ≠ v) (pa pb : Bool)
    (ha_form : (pa = true ∧ a = u.1) ∨ (pa = false ∧ ∃ (ja : ℕ) (hja : ja < iStar), a = 6 + ja ∧ gs[ja]'(Nat.lt_trans hja hiStar) = ⟨GateOp.not, [u.1]⟩))
    (hb_form : (pb = true ∧ b = v.1) ∨ (pb = false ∧ ∃ (jb : ℕ) (hjb : jb < iStar), b = 6 + jb ∧ gs[jb]'(Nat.lt_trans hjb hiStar) = ⟨GateOp.not, [v.1]⟩))
    (hout_ne_star : out ≠ 6 + iStar)
    (h : Fin gs.length) (hh_gt : iStar < h.1)
    (wu : ℕ) (hwu_in : wu ∈ gs[h.1].inputs)
    (hwu_form : wu = u.1 ∨ ∃ (ju : ℕ) (hju : ju < iStar), wu = 6 + ju ∧ gs[ju]'(Nat.lt_trans hju hiStar) = ⟨GateOp.not, [u.1]⟩) :
    False := by
  have hwire_val_u : ∀ (x : Fin 6 → Bool),
      (wiresFrom gs (List.ofFn x)).getD a false = (if pa then x u else !(x u)) := by
    intro x
    rcases ha_form with ⟨rfl, rfl⟩ | ⟨rfl, ja, hja, rfl, hgsja⟩
    · rw [wiresFrom_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ u.isLt]; rfl
    · have hlt : ja < gs.length := Nat.lt_trans hja hiStar
      have hsp := split_list_at gs ja hlt
      rw [hsp, wiresFrom_append, wiresFrom_getD_lt _ _ _ (by simp [wiresFrom_length, Nat.min_eq_left (Nat.le_of_lt hlt)]; omega)]
      rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil,
          getD_snoc_eq _ _ _ _ (by simp [wiresFrom_length, Nat.min_eq_left (Nat.le_of_lt hlt)])]
      rw [hgsja]
      simp only [GateOp.eval, List.map_singleton, List.headD_cons]
      rw [wiresFrom_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ u.isLt]
      rfl
  have hwire_val_v : ∀ (x : Fin 6 → Bool),
      (wiresFrom gs (List.ofFn x)).getD b false = (if pb then x v else !(x v)) := by
    intro x
    rcases hb_form with ⟨rfl, rfl⟩ | ⟨rfl, jb, hjb, rfl, hgsjb⟩
    · rw [wiresFrom_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ v.isLt]; rfl
    · have hlt : jb < gs.length := Nat.lt_trans hjb hiStar
      have hsp := split_list_at gs jb hlt
      rw [hsp, wiresFrom_append, wiresFrom_getD_lt _ _ _ (by simp [wiresFrom_length, Nat.min_eq_left (Nat.le_of_lt hlt)]; omega)]
      rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil,
          getD_snoc_eq _ _ _ _ (by simp [wiresFrom_length, Nat.min_eq_left (Nat.le_of_lt hlt)])]
      rw [hgsjb]
      simp only [GateOp.eval, List.map_singleton, List.headD_cons]
      rw [wiresFrom_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ v.isLt]
      rfl
  have hwire_val_wu : ∃ pwu : Bool, ∀ (x : Fin 6 → Bool),
      (wiresFrom gs (List.ofFn x)).getD wu false = (if pwu then x u else !(x u)) := by
    rcases hwu_form with rfl | ⟨ju, hju, rfl, hgsju⟩
    · exact ⟨true, fun x => by
        rw [wiresFrom_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ u.isLt]; rfl⟩
    · refine ⟨false, fun x => ?_⟩
      have hlt : ju < gs.length := Nat.lt_trans hju hiStar
      have hsp := split_list_at gs ju hlt
      rw [hsp, wiresFrom_append, wiresFrom_getD_lt _ _ _ (by simp [wiresFrom_length, Nat.min_eq_left (Nat.le_of_lt hlt)]; omega)]
      rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil,
          getD_snoc_eq _ _ _ _ (by simp [wiresFrom_length, Nat.min_eq_left (Nat.le_of_lt hlt)])]
      rw [hgsju]
      simp only [GateOp.eval, List.map_singleton, List.headD_cons]
      rw [wiresFrom_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ u.isLt]
      rfl
  have hwu_lt : wu < 6 + iStar := by
    rcases hwu_form with rfl | ⟨ju, hju, rfl, _⟩
    · omega
    · omega
  have hex_d : ∃ d : Fin gs.length, iStar < d.1 ∧ d ≠ h ∧ 6 + iStar ∈ gs[d.1].inputs := by
    by_contra hno_d
    push Not at hno_d
    obtain ⟨d0, hd0_gt, hd0_in⟩ := min_gate_used fC6_nc gs out hnok hev hmin iStar hiStar hout_ne_star
    have hd0_eq : d0 = h := by
      by_contra hne; exact hno_d d0 hd0_gt hne hd0_in
    subst hd0_eq
    have h_only : ∀ j : Fin gs.length, iStar < j.1 → j ≠ d0 → 6 + iStar ∉ gs[j.1].inputs :=
      fun j hj hne => hno_d j hj hne
    have hnok_d0 := hnok gs[d0.1] (List.getElem_mem d0.isLt)
    have hne_wu : wu ≠ 6 + iStar := by omega
    have hop_d0_bin : gs[d0.1].op = GateOp.and ∨ gs[d0.1].op = GateOp.or := by
      rcases hnok_d0.1.1 with ho | ho | ho
      · exact Or.inl ho
      · exact Or.inr ho
      · exfalso
        obtain ⟨q, hq, _⟩ := min_not_inputs fC6_nc gs out hnok hev hmin d0.1 d0.isLt ho
        rw [hq] at hwu_in hd0_in
        simp at hwu_in hd0_in
        exact hne_wu (hwu_in.trans hd0_in.symm)
    obtain ⟨c1, c2, hins_d0, hc12, _, _⟩ :=
      min_bin_inputs fC6_nc gs out hnok hev hmin d0.1 d0.isLt hop_d0_bin
    have hd0_pair : gs[d0.1].inputs = [wu, 6 + iStar] ∨ gs[d0.1].inputs = [6 + iStar, wu] := by
      rw [hins_d0] at hwu_in hd0_in
      simp at hwu_in hd0_in
      rcases hwu_in with rfl | rfl <;> rcases hd0_in with h1 | h1
      · exact absurd h1.symm hne_wu
      · rw [← h1] at hins_d0; exact Or.inl hins_d0
      · rw [← h1] at hins_d0; exact Or.inr hins_d0
      · exact absurd h1.symm hne_wu
    have hsp_d0 := split_list_at gs d0.1 d0.isLt
    set gs1 := gs.take d0.1
    set gs2 := gs.drop (d0.1 + 1)
    have hlen1 : gs1.length = d0.1 := by simp [gs1, Nat.min_eq_left (Nat.le_of_lt d0.isLt)]
    have hlen_tot : gs1.length + gs2.length = gs.length - 1 := by
      simp [gs1, gs2, Nat.min_eq_left (Nat.le_of_lt d0.isLt)]; omega
    have hpref_get : ∀ (x : Fin 6 → Bool) (k : ℕ), k < 6 + d0.1 →
        (wiresFrom gs1 (List.ofFn x)).getD k false = (wiresFrom gs (List.ofFn x)).getD k false := by
      intro x k hk
      conv_rhs =>
        rw [hsp_d0, wiresFrom_append, wiresFrom_append,
            wiresFrom_getD_lt _ _ _ (by simp [wiresFrom_length, hlen1]; omega),
            wiresFrom_getD_lt _ _ _ (by simp [wiresFrom_length, hlen1]; exact hk)]
    have hval_star : ∀ x : Fin 6 → Bool,
        (wiresFrom gs (List.ofFn x)).getD (6 + iStar) false =
          opStar.eval [if pa then x u else !(x u), if pb then x v else !(x v)] := by
      intro x
      have hsp_s := split_list_at gs iStar hiStar
      conv_lhs => rw [hsp_s]
      rw [wiresFrom_append, wiresFrom_getD_lt _ _ _ (by simp [wiresFrom_length, Nat.min_eq_left (Nat.le_of_lt hiStar)]; omega)]
      rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil,
          getD_snoc_eq _ _ _ _ (by simp [wiresFrom_length, Nat.min_eq_left (Nat.le_of_lt hiStar)])]
      have hga : (wiresFrom (gs.take iStar) (List.ofFn x)).getD a false =
          (wiresFrom gs (List.ofFn x)).getD a false := by
        conv_rhs =>
          rw [hsp_s, wiresFrom_append, wiresFrom_append,
              wiresFrom_getD_lt _ _ _ (by simp [wiresFrom_length, Nat.min_eq_left (Nat.le_of_lt hiStar)]; omega),
              wiresFrom_getD_lt _ _ _ (by simp [wiresFrom_length, Nat.min_eq_left (Nat.le_of_lt hiStar)]; exact ha_lt)]
      have hgb : (wiresFrom (gs.take iStar) (List.ofFn x)).getD b false =
          (wiresFrom gs (List.ofFn x)).getD b false := by
        conv_rhs =>
          rw [hsp_s, wiresFrom_append, wiresFrom_append,
              wiresFrom_getD_lt _ _ _ (by simp [wiresFrom_length, Nat.min_eq_left (Nat.le_of_lt hiStar)]; omega),
              wiresFrom_getD_lt _ _ _ (by simp [wiresFrom_length, Nat.min_eq_left (Nat.le_of_lt hiStar)]; exact hb_lt)]
      rw [hopStar]
      rcases hinsStar with hs | hs <;> rw [hs]
      · simp only [List.map_cons, List.map_nil, hga, hgb, hwire_val_u x, hwire_val_v x]
      · simp only [List.map_cons, List.map_nil, hga, hgb, hwire_val_u x, hwire_val_v x]
        rcases hop_bin with rfl | rfl <;> simp [GateOp.eval, Bool.and_comm, Bool.or_comm]
    obtain ⟨pwu, hpwu⟩ := hwire_val_wu
    have hd0_eval : ∀ x : Fin 6 → Bool,
        (wiresFrom (gs1 ++ [gs[d0.1]]) (List.ofFn x)).getD (6 + gs1.length) false =
          gs[d0.1].op.eval [if pwu then x u else !(x u),
            opStar.eval [if pa then x u else !(x u), if pb then x v else !(x v)]] := by
      intro x
      rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil,
          getD_snoc_eq _ _ _ _ (by simp [wiresFrom_length])]
      rcases hd0_pair with hp | hp <;> rw [hp]
      · simp only [List.map_cons, List.map_nil]
        rw [hpref_get x wu (by omega), hpref_get x (6 + iStar) (by omega), hpwu x, hval_star x]
      · simp only [List.map_cons, List.map_nil]
        rw [hpref_get x wu (by omega), hpref_get x (6 + iStar) (by omega), hpwu x, hval_star x]
        rcases hop_d0_bin with h1 | h1 <;> rw [h1] <;> simp [GateOp.eval, Bool.and_comm, Bool.or_comm]
    have hreduce_d0 : ∀ r : Bool ⊕ ℕ, statValid (6 + gs1.length) r →
        (∀ x : Fin 6 → Bool, statVal (wiresFrom gs1 (List.ofFn x)) r =
          (wiresFrom (gs1 ++ [gs[d0.1]]) (List.ofFn x)).getD (6 + gs1.length) false) → False := by
      intro r hr heq
      have hres := elim_gate_at fC6_nc gs1 gs2 gs[d0.1] out
        (fun g' hg' => (hnok g' (by rw [hsp_d0]; exact hg')).1)
        (fun x => by rw [← hsp_d0]; exact hev x)
        r hr heq
      rw [hlen_tot] at hres
      exact hmin hres
    have hreplace_and_kill : ∀ (gNew : Gate), OkGate gNew → 6 + iStar ∉ gNew.inputs →
        (∀ x : Fin 6 → Bool,
          gNew.op.eval (gNew.inputs.map fun idx => (wiresFrom gs1 (List.ofFn x)).getD idx false) =
          gs[d0.1].op.eval (gs[d0.1].inputs.map fun idx => (wiresFrom gs1 (List.ofFn x)).getD idx false)) →
        False := by
      intro gNew hokNew hnoNew heqNew
      set gs' := gs1 ++ [gNew] ++ gs2 with hgs'
      have hlen' : gs'.length = gs.length := by simp [hgs', gs1, gs2, Nat.min_eq_left (Nat.le_of_lt d0.isLt)]; omega
      have hev' : ∀ x : Fin 6 → Bool, (wiresFrom gs' (List.ofFn x)).getD out false = fC6 x := by
        intro x
        rw [hgs', replace_gate_at gs1 gs2 gs[d0.1] gNew heqNew x, ← hsp_d0]
        exact hev x
      have hok' : ∀ g' ∈ gs', OkGate g' := by
        intro g' hg'
        simp only [hgs', List.mem_append, List.mem_singleton] at hg'
        rcases hg' with (h1 | rfl) | h2
        · exact (hnok g' (by rw [hsp_d0]; simp [h1])).1
        · exact hokNew
        · exact (hnok g' (by rw [hsp_d0]; simp [h2])).1
      have hiStar' : iStar < gs'.length := by rw [hlen']; exact hiStar
      have hsp' := split_list_at gs' iStar hiStar'
      have hlen_pre' : (gs'.take iStar).length = iStar := by
        simp [Nat.min_eq_left (Nat.le_of_lt hiStar')]
      have hlen_tot' : (gs'.take iStar).length + (gs'.drop (iStar + 1)).length = gs.length - 1 := by
        rw [hlen_pre', List.length_drop, hlen']; omega
      have hres := elim_unused_gate fC6_nc (gs'.take iStar) (gs'.drop (iStar + 1))
        (gs'[iStar]'(by rw [hlen']; exact hiStar)) out
        (fun g' hg' => hok' g' (by rw [hsp']; exact hg'))
        (fun x => by rw [← hsp']; exact hev' x)
        (by rw [hlen_pre']; exact hout_ne_star)
        (by
          intro g' hg'
          rw [hlen_pre']
          obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hg'
          rw [List.getElem_drop]
          have hidx_lt : iStar + 1 + k < gs.length := by
            rw [List.length_drop, hlen'] at hk; omega
          by_cases hkd0 : iStar + 1 + k = d0.1
          · have hget_new : gs'[iStar + 1 + k]'(by rw [hlen']; exact hidx_lt) = gNew := by
              simp only [hgs', List.append_assoc]
              rw [List.getElem_append_right (by rw [hlen1]; omega)]
              simp [hlen1, hkd0]
            rw [hget_new]
            exact hnoNew
          · have hget_old : gs'[iStar + 1 + k]'(by rw [hlen']; exact hidx_lt) = gs[iStar + 1 + k] := by
              by_cases hlt_d0 : iStar + 1 + k < d0.1
              · simp only [hgs', List.append_assoc]
                rw [List.getElem_append_left (by rw [hlen1]; exact hlt_d0)]
                simp [gs1]
              · simp only [hgs', List.append_assoc]
                rw [List.getElem_append_right (by rw [hlen1]; omega)]
                have hgt_d0 : d0.1 < iStar + 1 + k := by omega
                have hpos : iStar + 1 + k - gs1.length = (iStar + 1 + k - d0.1 - 1) + 1 := by omega
                simp only [List.cons_append, List.nil_append, hpos, List.getElem_cons_succ, gs2, List.getElem_drop]
                congr 1; omega
            rw [hget_old]
            exact h_only ⟨iStar + 1 + k, hidx_lt⟩ (by dsimp; omega) (fun heq => hkd0 (congrArg Fin.val heq)))
      rw [hlen_tot'] at hres
      exact hmin hres
    rcases hop_bin with rfl | rfl <;> rcases hop_d0_bin with hd0_op | hd0_op
    · by_cases hpol : pwu = pa
      · apply hreduce_d0 (Sum.inr (6 + iStar)) (by simp [statValid, hlen1]; exact hd0_gt)
        intro x
        rw [hd0_eval x, hd0_op, hpol]
        simp only [statVal]
        rw [hpref_get x (6 + iStar) (by omega), hval_star x]
        cases x u <;> cases x v <;> cases pa <;> cases pb <;> decide
      · apply hreduce_d0 (Sum.inl false) trivial
        intro x
        rw [hd0_eval x, hd0_op]
        simp only [statVal]
        cases pwu <;> cases pa
        · exact absurd rfl hpol
        · cases x u <;> cases x v <;> cases pb <;> decide
        · cases x u <;> cases x v <;> cases pb <;> decide
        · exact absurd rfl hpol
    · by_cases hpol : pwu = pa
      · apply hreduce_d0 (Sum.inr wu) (by simp [statValid, hlen1]; omega)
        intro x
        rw [hd0_eval x, hd0_op, hpol]
        simp only [statVal]
        rw [hpref_get x wu (by omega), hpwu x, hpol]
        cases x u <;> cases x v <;> cases pa <;> cases pb <;> decide
      · apply hreplace_and_kill ⟨GateOp.or, [wu, b]⟩
          ⟨Or.inr (Or.inl rfl), by simp⟩
          (by simp; exact ⟨hne_wu.symm, by omega⟩)
        intro x
        have h1 := hd0_eval x
        rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil,
            getD_snoc_eq _ _ _ _ (by simp [wiresFrom_length])] at h1
        rw [h1, hd0_op]
        simp only [List.map_cons, List.map_nil]
        rw [hpref_get x wu (by omega), hpref_get x b (by omega), hpwu x, hwire_val_v x]
        cases pwu <;> cases pa
        · exact absurd rfl hpol
        · cases x u <;> cases x v <;> cases pb <;> decide
        · cases x u <;> cases x v <;> cases pb <;> decide
        · exact absurd rfl hpol
    · by_cases hpol : pwu = pa
      · apply hreduce_d0 (Sum.inr wu) (by simp [statValid, hlen1]; omega)
        intro x
        rw [hd0_eval x, hd0_op, hpol]
        simp only [statVal]
        rw [hpref_get x wu (by omega), hpwu x, hpol]
        cases x u <;> cases x v <;> cases pa <;> cases pb <;> decide
      · apply hreplace_and_kill ⟨GateOp.and, [wu, b]⟩
          ⟨Or.inl rfl, by simp⟩
          (by simp; exact ⟨hne_wu.symm, by omega⟩)
        intro x
        have h1 := hd0_eval x
        rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil,
            getD_snoc_eq _ _ _ _ (by simp [wiresFrom_length])] at h1
        rw [h1, hd0_op]
        simp only [List.map_cons, List.map_nil]
        rw [hpref_get x wu (by omega), hpref_get x b (by omega), hpwu x, hwire_val_v x]
        cases pwu <;> cases pa
        · exact absurd rfl hpol
        · cases x u <;> cases x v <;> cases pb <;> decide
        · cases x u <;> cases x v <;> cases pb <;> decide
        · exact absurd rfl hpol
    · by_cases hpol : pwu = pa
      · apply hreduce_d0 (Sum.inr (6 + iStar)) (by simp [statValid, hlen1]; exact hd0_gt)
        intro x
        rw [hd0_eval x, hd0_op, hpol]
        simp only [statVal]
        rw [hpref_get x (6 + iStar) (by omega), hval_star x]
        cases x u <;> cases x v <;> cases pa <;> cases pb <;> decide
      · apply hreduce_d0 (Sum.inl true) trivial
        intro x
        rw [hd0_eval x, hd0_op]
        simp only [statVal]
        cases pwu <;> cases pa
        · exact absurd rfl hpol
        · cases x u <;> cases x v <;> cases pb <;> decide
        · cases x u <;> cases x v <;> cases pb <;> decide
        · exact absurd rfl hpol
  obtain ⟨d, hd_gt, hdh, hd_in⟩ := hex_d
  set bVal : Bool := match opStar with | GateOp.and => !pa | _ => pa with hbVal
  have hst_u : ∀ bv : Bool,
      (elimPass 6 gs (initVar 6 u bv, [])).1.getD u.1 (Sum.inl false) = Sum.inl bv := by
    intro bv
    rw [elimPass_getD_lt _ _ _ _ _ (by simp [initVar])]
    rw [initVar, ofFn_getD_lt _ _ _ u.isLt]
    simp
  have hst_not_u : ∀ (bv : Bool) (j : ℕ) (hj : j < iStar),
      gs[j]'(Nat.lt_trans hj hiStar) = ⟨GateOp.not, [u.1]⟩ →
      (elimPass 6 gs (initVar 6 u bv, [])).1.getD (6 + j) (Sum.inl false) = Sum.inl (!bv) := by
    intro bv j hj hgsj
    have hlt : j < gs.length := Nat.lt_trans hj hiStar
    have h1 := elimPass_st_not_const 6 gs (initVar 6 u bv, []) j u.1 hlt bv
      (by rw [hgsj]) (by rw [hgsj]) (by simp [initVar]; omega) (hst_u bv)
    simpa [initVar] using h1
  have hst_a : (elimPass 6 gs (initVar 6 u bVal, [])).1.getD a (Sum.inl false) =
      Sum.inl (match opStar with | GateOp.and => false | _ => true) := by
    rcases ha_form with ⟨rfl, rfl⟩ | ⟨rfl, ja, hja, rfl, hgsja⟩
    · rw [hst_u bVal]; rcases hop_bin with rfl | rfl <;> rfl
    · rw [hst_not_u bVal ja hja hgsja]; rcases hop_bin with rfl | rfl <;> rfl
  have hst_star : ∃ c : Bool,
      (elimPass 6 gs (initVar 6 u bVal, [])).1.getD (6 + iStar) (Sum.inl false) = Sum.inl c := by
    have ha_in : a ∈ gs[iStar].inputs := by
      rcases hinsStar with h1 | h1 <;> rw [h1] <;> simp
    rcases hop_bin with rfl | rfl
    · refine ⟨false, ?_⟩
      have h1 := elimPass_st_and_false 6 gs (initVar 6 u bVal, []) hnok iStar a hiStar
        hopStar ha_in (by simp [initVar]; exact ha_lt) (by simpa using hst_a)
      simpa [initVar] using h1
    · refine ⟨true, ?_⟩
      have h1 := elimPass_st_or_true 6 gs (initVar 6 u bVal, []) hnok iStar a hiStar
        hopStar ha_in (by simp [initVar]; exact ha_lt) (by simpa using hst_a)
      simpa [initVar] using h1
  have hst_wu : ∃ c : Bool,
      (elimPass 6 gs (initVar 6 u bVal, [])).1.getD wu (Sum.inl false) = Sum.inl c := by
    rcases hwu_form with rfl | ⟨ju, hju, rfl, hgsju⟩
    · exact ⟨bVal, hst_u bVal⟩
    · exact ⟨!bVal, hst_not_u bVal ju hju hgsju⟩
  have helim_star : elimAt 6 gs (initVar 6 u bVal, []) iStar = true := by
    apply elimAt_of_const_input 6 gs (initVar 6 u bVal, []) hnok iStar a hiStar
      (by rcases hinsStar with h1 | h1 <;> rw [h1] <;> simp)
      (by simp [initVar]; exact ha_lt)
      ⟨_, hst_a⟩
  have helim_d : elimAt 6 gs (initVar 6 u bVal, []) d.1 = true := by
    apply elimAt_of_const_input 6 gs (initVar 6 u bVal, []) hnok d.1 (6 + iStar) d.isLt
      hd_in (by simp [initVar]; omega) hst_star
  have helim_h : elimAt 6 gs (initVar 6 u bVal, []) h.1 = true := by
    apply elimAt_of_const_input 6 gs (initVar 6 u bVal, []) hnok h.1 wu h.isLt
      hwu_in (by simp [initVar]; omega) hst_wu
  cases hbVal_eq : bVal with
  | false =>
    let S : Finset (Fin gs.length) := {⟨iStar, hiStar⟩, d, h}
    have hcard : S.card = 3 := by
      have h1 : (⟨iStar, hiStar⟩ : Fin gs.length) ≠ d := fun heq => by
        have := congrArg Fin.val heq; (try dsimp at this); omega
      have h2 : (⟨iStar, hiStar⟩ : Fin gs.length) ≠ h := fun heq => by
        have := congrArg Fin.val heq; (try dsimp at this); omega
      simp [S, h1, h2, hdh]
    have hres := elim_var_by_set gs out hnok hev u false (fC6_update_nc u false) S (by
      intro idx hidx
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hidx
      rcases hidx with rfl | rfl | rfl
      · simpa [hbVal_eq] using helim_star
      · simpa [hbVal_eq] using helim_d
      · simpa [hbVal_eq] using helim_h)
    rw [hcard] at hres
    exact not_size_fC6_false u (by
      obtain ⟨C, hok, hsz, hevC⟩ := hres
      exact ⟨C, hok, le_trans hsz (by omega), hevC⟩)
  | true =>
    by_cases hex_not : ∃ j0 : Fin gs.length, j0.1 < iStar ∧ gs[j0.1] = ⟨GateOp.not, [u.1]⟩
    · obtain ⟨j0, hj0_lt, hgsj0⟩ := hex_not
      have helim_j0 : elimAt 6 gs (initVar 6 u true, []) j0.1 = true := by
        apply elimAt_of_const_input 6 gs (initVar 6 u true, []) hnok j0.1 u.1 j0.isLt
          (by rw [hgsj0]; simp) (by simp [initVar]; omega) ⟨true, hst_u true⟩
      let S : Finset (Fin gs.length) := {j0, ⟨iStar, hiStar⟩, d, h}
      have hcard : S.card = 4 := by
        have h01 : j0 ≠ ⟨iStar, hiStar⟩ := fun heq => by have := congrArg Fin.val heq; (try dsimp at this); omega
        have h02 : j0 ≠ d := fun heq => by have := congrArg Fin.val heq; (try dsimp at this); omega
        have h03 : j0 ≠ h := fun heq => by have := congrArg Fin.val heq; (try dsimp at this); omega
        have h12 : (⟨iStar, hiStar⟩ : Fin gs.length) ≠ d := fun heq => by have := congrArg Fin.val heq; (try dsimp at this); omega
        have h13 : (⟨iStar, hiStar⟩ : Fin gs.length) ≠ h := fun heq => by have := congrArg Fin.val heq; (try dsimp at this); omega
        simp [S, h01, h02, h03, h12, h13, hdh]
      have hres := elim_var_by_set gs out hnok hev u true (fC6_update_nc u true) S (by
        intro idx hidx
        simp only [S, Finset.mem_insert, Finset.mem_singleton] at hidx
        rcases hidx with rfl | rfl | rfl | rfl
        · exact helim_j0
        · simpa [hbVal_eq] using helim_star
        · simpa [hbVal_eq] using helim_d
        · simpa [hbVal_eq] using helim_h)
      rw [hcard] at hres
      exact not_size_fC6_true u (by
        obtain ⟨C, hok, hsz, hevC⟩ := hres
        exact ⟨C, hok, le_trans hsz (by omega), hevC⟩)
    · push Not at hex_not
      have ha_eq_u : a = u.1 := by
        rcases ha_form with ⟨_, rfl⟩ | ⟨_, ja, hja, _, hgsja⟩
        · rfl
        · exact absurd hgsja (hex_not ⟨ja, Nat.lt_trans hja hiStar⟩ hja)
      have hwu_eq_u : wu = u.1 := by
        rcases hwu_form with rfl | ⟨ju, hju, _, hgsju⟩
        · rfl
        · exact absurd hgsju (hex_not ⟨ju, Nat.lt_trans hju hiStar⟩ hju)
      have hu_in_h : u.1 ∈ gs[h.1].inputs := hwu_eq_u ▸ hwu_in
      have hnok_h := hnok gs[h.1] (List.getElem_mem h.isLt)
      rcases hnok_h.1.1 with hh_op | hh_op | hh_op
      · have helim_star_f : elimAt 6 gs (initVar 6 u false, []) iStar = true := by
          apply elimAt_of_const_input 6 gs (initVar 6 u false, []) hnok iStar u.1 hiStar
            (by rw [← ha_eq_u]; rcases hinsStar with h1 | h1 <;> rw [h1] <;> simp)
            (by simp [initVar]; omega) ⟨false, hst_u false⟩
        have helim_h_f : elimAt 6 gs (initVar 6 u false, []) h.1 = true := by
          apply elimAt_of_const_input 6 gs (initVar 6 u false, []) hnok h.1 u.1 h.isLt
            hu_in_h (by simp [initVar]; omega) ⟨false, hst_u false⟩
        have hst_h_f : (elimPass 6 gs (initVar 6 u false, [])).1.getD (6 + h.1) (Sum.inl false) = Sum.inl false := by
          have h1 := elimPass_st_and_false 6 gs (initVar 6 u false, []) hnok h.1 u.1 h.isLt
            hh_op hu_in_h (by simp [initVar]; omega) (hst_u false)
          simpa [initVar] using h1
        have hout_ne_h : out ≠ 6 + h.1 := by
          intro heq
          obtain ⟨x, x', hne⟩ := fC6_update_nc u false
          have hinv1 := elimInv_pass 6 (List.ofFn x) gs _ (initVar 6 u false, [])
            (fun g hg => (hnok g hg).1) (elimInv_initVar 6 u false x)
          have hinv2 := elimInv_pass 6 (List.ofFn x') gs _ (initVar 6 u false, [])
            (fun g hg => (hnok g hg).1) (elimInv_initVar 6 u false x')
          have e1 := (hinv1.2.2 out).2
          have e2 := (hinv2.2.2 out).2
          rw [hev, heq, hst_h_f] at e1 e2
          exact hne (e1.symm.trans e2)
        obtain ⟨dh, hdh_gt, hdh_in⟩ := min_gate_used fC6_nc gs out hnok hev hmin h.1 h.isLt hout_ne_h
        have helim_dh_f : elimAt 6 gs (initVar 6 u false, []) dh.1 = true := by
          apply elimAt_of_const_input 6 gs (initVar 6 u false, []) hnok dh.1 (6 + h.1) dh.isLt
            hdh_in (by simp [initVar]; omega) ⟨false, hst_h_f⟩
        let S : Finset (Fin gs.length) := {⟨iStar, hiStar⟩, h, dh}
        have hcard : S.card = 3 := by
          have h1 : (⟨iStar, hiStar⟩ : Fin gs.length) ≠ h := fun heq => by have := congrArg Fin.val heq; (try dsimp at this); omega
          have h2 : (⟨iStar, hiStar⟩ : Fin gs.length) ≠ dh := fun heq => by have := congrArg Fin.val heq; (try dsimp at this); omega
          have h3 : h ≠ dh := fun heq => by have := congrArg Fin.val heq; (try dsimp at this); omega
          simp [S, h1, h2, h3]
        have hres := elim_var_by_set gs out hnok hev u false (fC6_update_nc u false) S (by
          intro idx hidx
          simp only [S, Finset.mem_insert, Finset.mem_singleton] at hidx
          rcases hidx with rfl | rfl | rfl
          · exact helim_star_f
          · exact helim_h_f
          · exact helim_dh_f)
        rw [hcard] at hres
        exact not_size_fC6_false u (by
          obtain ⟨C, hok, hsz, hevC⟩ := hres
          exact ⟨C, hok, le_trans hsz (by omega), hevC⟩)
      · have hst_h_t : ∃ ch : Bool,
            (elimPass 6 gs (initVar 6 u true, [])).1.getD (6 + h.1) (Sum.inl false) = Sum.inl ch := by
          refine ⟨true, ?_⟩
          have h1 := elimPass_st_or_true 6 gs (initVar 6 u true, []) hnok h.1 u.1 h.isLt
            hh_op hu_in_h (by simp [initVar]; omega) (hst_u true)
          simpa [initVar] using h1
        obtain ⟨ch, hch⟩ := hst_h_t
        have hout_ne_h : out ≠ 6 + h.1 := by
          intro heq
          obtain ⟨x, x', hne⟩ := fC6_update_nc u true
          have hinv1 := elimInv_pass 6 (List.ofFn x) gs _ (initVar 6 u true, [])
            (fun g hg => (hnok g hg).1) (elimInv_initVar 6 u true x)
          have hinv2 := elimInv_pass 6 (List.ofFn x') gs _ (initVar 6 u true, [])
            (fun g hg => (hnok g hg).1) (elimInv_initVar 6 u true x')
          have e1 := (hinv1.2.2 out).2
          have e2 := (hinv2.2.2 out).2
          rw [hev, heq, hch] at e1 e2
          exact hne (e1.symm.trans e2)
        obtain ⟨dh, hdh_gt, hdh_in⟩ := min_gate_used fC6_nc gs out hnok hev hmin h.1 h.isLt hout_ne_h
        by_cases hdh_eq_d : dh = d
        · subst hdh_eq_d
          have hst_d_t : ∃ cd : Bool,
              (elimPass 6 gs (initVar 6 u true, [])).1.getD (6 + dh.1) (Sum.inl false) = Sum.inl cd := by
            have h1 := elimPass_st_all_const 6 gs (initVar 6 u true, []) hnok dh.1 dh.isLt (by
              intro k hk
              have hlen_d := (hnok gs[dh.1] (List.getElem_mem dh.isLt)).1.2
              have hne_sh : 6 + iStar ≠ 6 + h.1 := by omega
              have hk_cases : k = 6 + iStar ∨ k = 6 + h.1 := by
                rcases hdin : gs[dh.1].inputs with _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, l⟩⟩⟩
                · rw [hdin] at hk; simp at hk
                · rw [hdin] at hd_in hdh_in; simp at hd_in hdh_in
                  exact absurd (hd_in.trans hdh_in.symm) hne_sh
                · rw [hdin] at hk hd_in hdh_in; simp at hk hd_in hdh_in
                  rcases hd_in with rfl | rfl <;> rcases hdh_in with h1 | h1
                  · exact absurd h1.symm hne_sh
                  · rcases hk with rfl | rfl <;> simp [h1]
                  · rcases hk with rfl | rfl <;> simp [h1]
                  · exact absurd h1.symm hne_sh
                · rw [hdin] at hlen_d; simp at hlen_d
              rcases hk_cases with rfl | rfl
              · exact ⟨by simp [initVar]; omega, by simpa [hbVal_eq] using hst_star⟩
              · exact ⟨by simp [initVar]; omega, ⟨ch, hch⟩⟩)
            simpa [initVar] using h1
          obtain ⟨cd, hcd⟩ := hst_d_t
          have hout_ne_d : out ≠ 6 + dh.1 := by
            intro heq
            obtain ⟨x, x', hne⟩ := fC6_update_nc u true
            have hinv1 := elimInv_pass 6 (List.ofFn x) gs _ (initVar 6 u true, [])
              (fun g hg => (hnok g hg).1) (elimInv_initVar 6 u true x)
            have hinv2 := elimInv_pass 6 (List.ofFn x') gs _ (initVar 6 u true, [])
              (fun g hg => (hnok g hg).1) (elimInv_initVar 6 u true x')
            have e1 := (hinv1.2.2 out).2
            have e2 := (hinv2.2.2 out).2
            rw [hev, heq, hcd] at e1 e2
            exact hne (e1.symm.trans e2)
          obtain ⟨d2, hd2_gt, hd2_in⟩ := min_gate_used fC6_nc gs out hnok hev hmin dh.1 dh.isLt hout_ne_d
          have helim_d2 : elimAt 6 gs (initVar 6 u true, []) d2.1 = true := by
            apply elimAt_of_const_input 6 gs (initVar 6 u true, []) hnok d2.1 (6 + dh.1) d2.isLt
              hd2_in (by simp [initVar]; omega) ⟨cd, hcd⟩
          let S : Finset (Fin gs.length) := {⟨iStar, hiStar⟩, h, dh, d2}
          have hcard : S.card = 4 := by
            have h01 : (⟨iStar, hiStar⟩ : Fin gs.length) ≠ h := fun heq => by have := congrArg Fin.val heq; (try dsimp at this); omega
            have h02 : (⟨iStar, hiStar⟩ : Fin gs.length) ≠ dh := fun heq => by have := congrArg Fin.val heq; (try dsimp at this); omega
            have h03 : (⟨iStar, hiStar⟩ : Fin gs.length) ≠ d2 := fun heq => by have := congrArg Fin.val heq; (try dsimp at this); omega
            have h12 : h ≠ dh := fun heq => by have := congrArg Fin.val heq; (try dsimp at this); omega
            have h13 : h ≠ d2 := fun heq => by have := congrArg Fin.val heq; (try dsimp at this); omega
            have h23 : dh ≠ d2 := fun heq => by have := congrArg Fin.val heq; (try dsimp at this); omega
            simp [S, h01, h02, h03, h12, h13, h23]
          have hres := elim_var_by_set gs out hnok hev u true (fC6_update_nc u true) S (by
            intro idx hidx
            simp only [S, Finset.mem_insert, Finset.mem_singleton] at hidx
            rcases hidx with rfl | rfl | rfl | rfl
            · simpa [hbVal_eq] using helim_star
            · simpa [hbVal_eq] using helim_h
            · simpa [hbVal_eq] using helim_d
            · exact helim_d2)
          rw [hcard] at hres
          exact not_size_fC6_true u (by
            obtain ⟨C, hok, hsz, hevC⟩ := hres
            exact ⟨C, hok, le_trans hsz (by omega), hevC⟩)
        · have helim_dh : elimAt 6 gs (initVar 6 u true, []) dh.1 = true := by
            apply elimAt_of_const_input 6 gs (initVar 6 u true, []) hnok dh.1 (6 + h.1) dh.isLt
              hdh_in (by simp [initVar]; omega) ⟨ch, hch⟩
          let S : Finset (Fin gs.length) := {⟨iStar, hiStar⟩, d, h, dh}
          have hcard : S.card = 4 := by
            have h01 : (⟨iStar, hiStar⟩ : Fin gs.length) ≠ d := fun heq => by have := congrArg Fin.val heq; (try dsimp at this); omega
            have h02 : (⟨iStar, hiStar⟩ : Fin gs.length) ≠ h := fun heq => by have := congrArg Fin.val heq; (try dsimp at this); omega
            have h03 : (⟨iStar, hiStar⟩ : Fin gs.length) ≠ dh := fun heq => by have := congrArg Fin.val heq; (try dsimp at this); omega
            have h13 : d ≠ dh := Ne.symm hdh_eq_d
            have h23 : h ≠ dh := fun heq => by have := congrArg Fin.val heq; (try dsimp at this); omega
            simp [S, h01, h02, h03, hdh, h13, h23]
          have hres := elim_var_by_set gs out hnok hev u true (fC6_update_nc u true) S (by
            intro idx hidx
            simp only [S, Finset.mem_insert, Finset.mem_singleton] at hidx
            rcases hidx with rfl | rfl | rfl | rfl
            · simpa [hbVal_eq] using helim_star
            · simpa [hbVal_eq] using helim_d
            · simpa [hbVal_eq] using helim_h
            · exact helim_dh)
          rw [hcard] at hres
          exact not_size_fC6_true u (by
            obtain ⟨C, hok, hsz, hevC⟩ := hres
            exact ⟨C, hok, le_trans hsz (by omega), hevC⟩)
      · obtain ⟨q, hq_ins, _⟩ := min_not_inputs fC6_nc gs out hnok hev hmin h.1 h.isLt hh_op
        have hq_eq : q = u.1 := by rw [hq_ins] at hu_in_h; simp at hu_in_h; exact hu_in_h.symm
        subst hq_eq
        have hch : (elimPass 6 gs (initVar 6 u true, [])).1.getD (6 + h.1) (Sum.inl false) = Sum.inl false := by
          have h1 := elimPass_st_not_const 6 gs (initVar 6 u true, []) h.1 u.1 h.isLt true
            hh_op hq_ins (by simp [initVar]; omega) (hst_u true)
          simpa [initVar] using h1
        have hout_ne_h : out ≠ 6 + h.1 := by
          intro heq
          obtain ⟨x, x', hne⟩ := fC6_update_nc u true
          have hinv1 := elimInv_pass 6 (List.ofFn x) gs _ (initVar 6 u true, [])
            (fun g hg => (hnok g hg).1) (elimInv_initVar 6 u true x)
          have hinv2 := elimInv_pass 6 (List.ofFn x') gs _ (initVar 6 u true, [])
            (fun g hg => (hnok g hg).1) (elimInv_initVar 6 u true x')
          have e1 := (hinv1.2.2 out).2
          have e2 := (hinv2.2.2 out).2
          rw [hev, heq, hch] at e1 e2
          exact hne (e1.symm.trans e2)
        obtain ⟨dh, hdh_gt, hdh_in⟩ := min_gate_used fC6_nc gs out hnok hev hmin h.1 h.isLt hout_ne_h
        by_cases hdh_eq_d : dh = d
        · subst hdh_eq_d
          have hst_d_t : ∃ cd : Bool,
              (elimPass 6 gs (initVar 6 u true, [])).1.getD (6 + dh.1) (Sum.inl false) = Sum.inl cd := by
            have h1 := elimPass_st_all_const 6 gs (initVar 6 u true, []) hnok dh.1 dh.isLt (by
              intro k hk
              have hlen_d := (hnok gs[dh.1] (List.getElem_mem dh.isLt)).1.2
              have hne_sh : 6 + iStar ≠ 6 + h.1 := by omega
              have hk_cases : k = 6 + iStar ∨ k = 6 + h.1 := by
                rcases hdin : gs[dh.1].inputs with _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, l⟩⟩⟩
                · rw [hdin] at hk; simp at hk
                · rw [hdin] at hd_in hdh_in; simp at hd_in hdh_in
                  exact absurd (hd_in.trans hdh_in.symm) hne_sh
                · rw [hdin] at hk hd_in hdh_in; simp at hk hd_in hdh_in
                  rcases hd_in with rfl | rfl <;> rcases hdh_in with h1 | h1
                  · exact absurd h1.symm hne_sh
                  · rcases hk with rfl | rfl <;> simp [h1]
                  · rcases hk with rfl | rfl <;> simp [h1]
                  · exact absurd h1.symm hne_sh
                · rw [hdin] at hlen_d; simp at hlen_d
              rcases hk_cases with rfl | rfl
              · exact ⟨by simp [initVar]; omega, by simpa [hbVal_eq] using hst_star⟩
              · exact ⟨by simp [initVar]; omega, ⟨false, hch⟩⟩)
            simpa [initVar] using h1
          obtain ⟨cd, hcd⟩ := hst_d_t
          have hout_ne_d : out ≠ 6 + dh.1 := by
            intro heq
            obtain ⟨x, x', hne⟩ := fC6_update_nc u true
            have hinv1 := elimInv_pass 6 (List.ofFn x) gs _ (initVar 6 u true, [])
              (fun g hg => (hnok g hg).1) (elimInv_initVar 6 u true x)
            have hinv2 := elimInv_pass 6 (List.ofFn x') gs _ (initVar 6 u true, [])
              (fun g hg => (hnok g hg).1) (elimInv_initVar 6 u true x')
            have e1 := (hinv1.2.2 out).2
            have e2 := (hinv2.2.2 out).2
            rw [hev, heq, hcd] at e1 e2
            exact hne (e1.symm.trans e2)
          obtain ⟨d2, hd2_gt, hd2_in⟩ := min_gate_used fC6_nc gs out hnok hev hmin dh.1 dh.isLt hout_ne_d
          have helim_d2 : elimAt 6 gs (initVar 6 u true, []) d2.1 = true := by
            apply elimAt_of_const_input 6 gs (initVar 6 u true, []) hnok d2.1 (6 + dh.1) d2.isLt
              hd2_in (by simp [initVar]; omega) ⟨cd, hcd⟩
          let S : Finset (Fin gs.length) := {⟨iStar, hiStar⟩, h, dh, d2}
          have hcard : S.card = 4 := by
            have h01 : (⟨iStar, hiStar⟩ : Fin gs.length) ≠ h := fun heq => by have := congrArg Fin.val heq; (try dsimp at this); omega
            have h02 : (⟨iStar, hiStar⟩ : Fin gs.length) ≠ dh := fun heq => by have := congrArg Fin.val heq; (try dsimp at this); omega
            have h03 : (⟨iStar, hiStar⟩ : Fin gs.length) ≠ d2 := fun heq => by have := congrArg Fin.val heq; (try dsimp at this); omega
            have h12 : h ≠ dh := fun heq => by have := congrArg Fin.val heq; (try dsimp at this); omega
            have h13 : h ≠ d2 := fun heq => by have := congrArg Fin.val heq; (try dsimp at this); omega
            have h23 : dh ≠ d2 := fun heq => by have := congrArg Fin.val heq; (try dsimp at this); omega
            simp [S, h01, h02, h03, h12, h13, h23]
          have hres := elim_var_by_set gs out hnok hev u true (fC6_update_nc u true) S (by
            intro idx hidx
            simp only [S, Finset.mem_insert, Finset.mem_singleton] at hidx
            rcases hidx with rfl | rfl | rfl | rfl
            · simpa [hbVal_eq] using helim_star
            · simpa [hbVal_eq] using helim_h
            · simpa [hbVal_eq] using helim_d
            · exact helim_d2)
          rw [hcard] at hres
          exact not_size_fC6_true u (by
            obtain ⟨C, hok, hsz, hevC⟩ := hres
            exact ⟨C, hok, le_trans hsz (by omega), hevC⟩)
        · have helim_dh : elimAt 6 gs (initVar 6 u true, []) dh.1 = true := by
            apply elimAt_of_const_input 6 gs (initVar 6 u true, []) hnok dh.1 (6 + h.1) dh.isLt
              hdh_in (by simp [initVar]; omega) ⟨false, hch⟩
          let S : Finset (Fin gs.length) := {⟨iStar, hiStar⟩, d, h, dh}
          have hcard : S.card = 4 := by
            have h01 : (⟨iStar, hiStar⟩ : Fin gs.length) ≠ d := fun heq => by have := congrArg Fin.val heq; (try dsimp at this); omega
            have h02 : (⟨iStar, hiStar⟩ : Fin gs.length) ≠ h := fun heq => by have := congrArg Fin.val heq; (try dsimp at this); omega
            have h03 : (⟨iStar, hiStar⟩ : Fin gs.length) ≠ dh := fun heq => by have := congrArg Fin.val heq; (try dsimp at this); omega
            have h13 : d ≠ dh := Ne.symm hdh_eq_d
            have h23 : h ≠ dh := fun heq => by have := congrArg Fin.val heq; (try dsimp at this); omega
            simp [S, h01, h02, h03, hdh, h13, h23]
          have hres := elim_var_by_set gs out hnok hev u true (fC6_update_nc u true) S (by
            intro idx hidx
            simp only [S, Finset.mem_insert, Finset.mem_singleton] at hidx
            rcases hidx with rfl | rfl | rfl | rfl
            · simpa [hbVal_eq] using helim_star
            · simpa [hbVal_eq] using helim_d
            · simpa [hbVal_eq] using helim_h
            · exact helim_dh)
          rw [hcard] at hres
          exact not_size_fC6_true u (by
            obtain ⟨C, hok, hsz, hevC⟩ := hres
            exact ⟨C, hok, le_trans hsz (by omega), hevC⟩)

private lemma not_size_fC6_7 : ¬ HasCircuitSize 6 fC6 7 := by
  classical
  intro h7
  have hex_s : ∃ s : ℕ, HasCircuitSize 6 fC6 s := ⟨7, h7⟩
  set sStar := Nat.find hex_s with hsStar
  have hsStar_le : sStar ≤ 7 := Nat.find_min' hex_s h7
  have hsStar_has : HasCircuitSize 6 fC6 sStar := Nat.find_spec hex_s
  have hsStar_pos : 1 ≤ sStar := by
    by_contra h0
    have hz : sStar = 0 := by omega
    rw [hz] at hsStar_has
    exact no_size_zero ⟨fun _ => true, by decide⟩ (fun i => fC6_not_literal i true) hsStar_has
  obtain ⟨C, hokC, hszC, hevC⟩ := hsStar_has
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOkGate g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hokC g0 hg0)
  have hev : ∀ x : Fin 6 → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = fC6 x := by
    intro x
    rw [hgs, wiresFrom_norm]
    exact hevC x
  have hlen_le : gs.length ≤ sStar := by simp [hgs]; exact hszC
  have hlen_eq : gs.length = sStar := by
    by_contra hne
    have hlt : gs.length < sStar := by omega
    have hhas : HasCircuitSize 6 fC6 gs.length :=
      ⟨⟨gs, C.output⟩, fun g hg => (hnok g hg).1, le_refl _, hev⟩
    exact Nat.find_min hex_s hlt hhas
  have hmin : ¬ HasCircuitSize 6 fC6 (gs.length - 1) := by
    rw [hlen_eq]
    exact Nat.find_min hex_s (by omega : sStar - 1 < sStar)
  have hex_bin := min_has_binary_gate gs C.output hnok hev
  set iStar := Nat.find hex_bin with hiStar_def
  have hiStar_spec := Nat.find_spec hex_bin
  have hiStar : iStar < gs.length := hiStar_spec.1
  have hop_bin : gs[iStar].op = GateOp.and ∨ gs[iStar].op = GateOp.or := by
    rcases hiStar_spec.2 with h1 | h1
    · rw [List.getElem?_eq_getElem hiStar] at h1; simp at h1; exact Or.inl h1
    · rw [List.getElem?_eq_getElem hiStar] at h1; simp at h1; exact Or.inr h1
  have hpre_not : ∀ (j : ℕ) (hj : j < iStar), (gs[j]'(Nat.lt_trans hj hiStar)).op = GateOp.not := by
    intro j hj
    have hlt := Nat.lt_trans hj hiStar
    have hno := Nat.find_min hex_bin hj
    rcases (hnok gs[j] (List.getElem_mem hlt)).1.1 with ho | ho | ho
    · exfalso; exact hno ⟨hlt, Or.inl (by simp [List.getElem?_eq_getElem hlt, ho])⟩
    · exfalso; exact hno ⟨hlt, Or.inr (by simp [List.getElem?_eq_getElem hlt, ho])⟩
    · exact ho
  have hpre : ∀ (j : ℕ) (hj : j < iStar), ∃ u : Fin 6, gs[j]'(Nat.lt_trans hj hiStar) = ⟨GateOp.not, [u.1]⟩ := by
    intro j
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro hj
      have hlt := Nat.lt_trans hj hiStar
      have hopj := hpre_not j hj
      obtain ⟨a, hins, ha_lt⟩ := min_not_inputs fC6_nc gs C.output hnok hev hmin j hlt hopj
      by_cases ha6 : a < 6
      · refine ⟨⟨a, ha6⟩, ?_⟩
        cases hgj : gs[j]
        simp only [hgj] at hopj hins
        subst hopj; subst hins; rfl
      · exfalso
        have hj' : a - 6 < j := by omega
        obtain ⟨u, hgu⟩ := ih (a - 6) hj' (Nat.lt_trans hj' hj)
        have ha_eq : a = 6 + (a - 6) := by omega
        have hsp := split_list_at gs j hlt
        set gs1 := gs.take j
        set gs2 := gs.drop (j + 1)
        have hlen1 : gs1.length = j := by simp [gs1, Nat.min_eq_left (Nat.le_of_lt hlt)]
        have hlen_tot : gs1.length + gs2.length = gs.length - 1 := by
          simp [gs1, gs2, Nat.min_eq_left (Nat.le_of_lt hlt)]; omega
        have hres := elim_gate_at fC6_nc gs1 gs2 gs[j] C.output
          (fun g' hg' => (hnok g' (by rw [hsp]; exact hg')).1)
          (fun x => by rw [← hsp]; exact hev x)
          (Sum.inr u.1) (by simp [statValid, hlen1]; omega)
          (fun x => by
            rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil,
                getD_snoc_eq _ _ _ _ (by simp [wiresFrom_length]), hopj, hins]
            simp only [statVal, GateOp.eval, List.map_singleton, List.headD_cons]
            have hval_a : (wiresFrom gs1 (List.ofFn x)).getD a false = !(x u) := by
              have hlt' : a - 6 < gs1.length := by omega
              have hsp' := split_list_at gs1 (a - 6) hlt'
              have hgs1_eq : gs1[a - 6] = ⟨GateOp.not, [u.1]⟩ := by
                simp only [gs1, List.getElem_take]; exact hgu
              conv_lhs => rw [hsp']
              rw [wiresFrom_append,
                  wiresFrom_getD_lt _ _ _ (by simp [wiresFrom_length, Nat.min_eq_left (Nat.le_of_lt hlt')]; omega)]
              rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil,
                  getD_snoc_eq _ _ _ _ (by simp [wiresFrom_length, Nat.min_eq_left (Nat.le_of_lt hlt')]; omega)]
              rw [hgs1_eq]
              simp only [GateOp.eval, List.map_singleton, List.headD_cons]
              rw [wiresFrom_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ u.isLt]
            rw [hval_a, Bool.not_not]
            rw [wiresFrom_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ u.isLt])
        rw [hlen_tot] at hres
        exact hmin hres
  obtain ⟨a, b, hinsStar, hab_ne, ha_lt, hb_lt⟩ :=
    min_bin_inputs fC6_nc gs C.output hnok hev hmin iStar hiStar hop_bin
  have hclassify : ∀ k < 6 + iStar,
      ∃ (w : Fin 6) (p : Bool),
        (p = true ∧ k = w.1) ∨
        (p = false ∧ ∃ (j : ℕ) (hj : j < iStar), k = 6 + j ∧ gs[j]'(Nat.lt_trans hj hiStar) = ⟨GateOp.not, [w.1]⟩) := by
    intro k hk
    by_cases hk6 : k < 6
    · exact ⟨⟨k, hk6⟩, true, Or.inl ⟨rfl, rfl⟩⟩
    · have hj : k - 6 < iStar := by omega
      obtain ⟨w, hgw⟩ := hpre (k - 6) hj
      exact ⟨w, false, Or.inr ⟨rfl, k - 6, hj, by omega, hgw⟩⟩
  obtain ⟨u, pa, ha_form⟩ := hclassify a ha_lt
  obtain ⟨v, pb, hb_form⟩ := hclassify b hb_lt
  have hval_k_pre : ∀ (k : ℕ) (w : Fin 6) (p : Bool),
      ((p = true ∧ k = w.1) ∨
        (p = false ∧ ∃ (j : ℕ) (hj : j < iStar), k = 6 + j ∧ gs[j]'(Nat.lt_trans hj hiStar) = ⟨GateOp.not, [w.1]⟩)) →
      ∀ x : Fin 6 → Bool, (wiresFrom (gs.take iStar) (List.ofFn x)).getD k false =
        (if p then x w else !(x w)) := by
    intro k w p hform x
    rcases hform with ⟨rfl, rfl⟩ | ⟨rfl, j, hj, rfl, hgj⟩
    · rw [wiresFrom_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ w.isLt]; rfl
    · have hltj : j < (gs.take iStar).length := by
        simp [Nat.min_eq_left (Nat.le_of_lt hiStar)]; exact hj
      have hsp' := split_list_at (gs.take iStar) j hltj
      have hget : (gs.take iStar)[j] = ⟨GateOp.not, [w.1]⟩ := by
        simp only [List.getElem_take]; exact hgj
      conv_lhs => rw [hsp']
      rw [wiresFrom_append,
          wiresFrom_getD_lt _ _ _ (by simp [wiresFrom_length]; omega)]
      rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil,
          getD_snoc_eq _ _ _ _ (by simp [wiresFrom_length]; omega)]
      rw [hget]
      simp only [GateOp.eval, List.map_singleton, List.headD_cons]
      rw [wiresFrom_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ w.isLt]
      rfl
  have huv : u ≠ v := by
    intro heq
    subst heq
    have hsp := split_list_at gs iStar hiStar
    set gs1 := gs.take iStar
    set gs2 := gs.drop (iStar + 1)
    have hlen1 : gs1.length = iStar := by simp [gs1, Nat.min_eq_left (Nat.le_of_lt hiStar)]
    have hlen_tot : gs1.length + gs2.length = gs.length - 1 := by
      simp [gs1, gs2, Nat.min_eq_left (Nat.le_of_lt hiStar)]; omega
    by_cases hpol : pa = pb
    · subst hpol
      have hres := elim_gate_at fC6_nc gs1 gs2 gs[iStar] C.output
        (fun g' hg' => (hnok g' (by rw [hsp]; exact hg')).1)
        (fun x => by rw [← hsp]; exact hev x)
        (Sum.inr a) (by simp [statValid, hlen1]; exact ha_lt)
        (fun x => by
          rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil,
              getD_snoc_eq _ _ _ _ (by simp [wiresFrom_length]), hinsStar]
          simp only [statVal, List.map_cons, List.map_nil]
          rw [hval_k_pre a u pa ha_form x, hval_k_pre b u pa hb_form x]
          rcases hop_bin with ho | ho <;> rw [ho] <;> simp [GateOp.eval])
      rw [hlen_tot] at hres
      exact hmin hres
    · have hres := elim_gate_at fC6_nc gs1 gs2 gs[iStar] C.output
        (fun g' hg' => (hnok g' (by rw [hsp]; exact hg')).1)
        (fun x => by rw [← hsp]; exact hev x)
        (Sum.inl (match gs[iStar].op with | GateOp.and => false | _ => true)) trivial
        (fun x => by
          rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil,
              getD_snoc_eq _ _ _ _ (by simp [wiresFrom_length]), hinsStar]
          simp only [statVal, List.map_cons, List.map_nil]
          rw [hval_k_pre a u pa ha_form x, hval_k_pre b u pb hb_form x]
          rcases hop_bin with ho | ho <;> rw [ho] <;> cases pa <;> cases pb
          · exact absurd rfl hpol
          · cases x u <;> decide
          · cases x u <;> decide
          · exact absurd rfl hpol
          · exact absurd rfl hpol
          · cases x u <;> decide
          · cases x u <;> decide
          · exact absurd rfl hpol)
      rw [hlen_tot] at hres
      exact hmin hres
  have hout_ne_star : C.output ≠ 6 + iStar := by
    intro heq
    obtain ⟨x, y, hxu, hxv, hne⟩ := fC6_not_two_vars u v
    have hsp := split_list_at gs iStar hiStar
    have hval_out : ∀ z : Fin 6 → Bool,
        fC6 z = gs[iStar].op.eval [if pa then z u else !(z u), if pb then z v else !(z v)] := by
      intro z
      rw [← hev z, heq]
      conv_lhs => rw [hsp]
      rw [wiresFrom_append,
          wiresFrom_getD_lt _ _ _ (by simp [wiresFrom_length, Nat.min_eq_left (Nat.le_of_lt hiStar)]; omega)]
      rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil,
          getD_snoc_eq _ _ _ _ (by simp [wiresFrom_length, Nat.min_eq_left (Nat.le_of_lt hiStar)]),
          hinsStar]
      simp only [List.map_cons, List.map_nil]
      rw [hval_k_pre a u pa ha_form z, hval_k_pre b v pb hb_form z]
    rw [hval_out x, hval_out y, hxu, hxv] at hne
    exact hne rfl
  let B : Set ℕ := {k | k = u.1 ∨ k = v.1 ∨
    ∃ (j : ℕ) (hj : j < iStar), k = 6 + j ∧ (gs[j]'(Nat.lt_trans hj hiStar) = ⟨GateOp.not, [u.1]⟩ ∨
      gs[j]'(Nat.lt_trans hj hiStar) = ⟨GateOp.not, [v.1]⟩)}
  have hout_not_B : C.output ∉ B := by
    intro hB
    rcases hB with h1 | h1 | ⟨j, hj, h1, hgj⟩
    · obtain ⟨x, hne⟩ := fC6_not_literal u true
      have hx := hev x
      rw [h1, wiresFrom_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ u.isLt] at hx
      exact hne hx.symm
    · obtain ⟨x, hne⟩ := fC6_not_literal v true
      have hx := hev x
      rw [h1, wiresFrom_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ v.isLt] at hx
      exact hne hx.symm
    · rcases hgj with hgj | hgj
      · obtain ⟨x, hne⟩ := fC6_not_literal u false
        have hx := hev x
        have hsp := split_list_at gs iStar hiStar
        rw [h1, hsp, wiresFrom_append, wiresFrom_append,
            wiresFrom_getD_lt _ _ _ (by simp [wiresFrom_length, Nat.min_eq_left (Nat.le_of_lt hiStar)]; omega),
            wiresFrom_getD_lt _ _ _ (by simp [wiresFrom_length, Nat.min_eq_left (Nat.le_of_lt hiStar)]; omega)] at hx
        rw [hval_k_pre (6 + j) u false (Or.inr ⟨rfl, j, hj, rfl, hgj⟩) x] at hx
        exact hne hx.symm
      · obtain ⟨x, hne⟩ := fC6_not_literal v false
        have hx := hev x
        have hsp := split_list_at gs iStar hiStar
        rw [h1, hsp, wiresFrom_append, wiresFrom_append,
            wiresFrom_getD_lt _ _ _ (by simp [wiresFrom_length, Nat.min_eq_left (Nat.le_of_lt hiStar)]; omega),
            wiresFrom_getD_lt _ _ _ (by simp [wiresFrom_length, Nat.min_eq_left (Nat.le_of_lt hiStar)]; omega)] at hx
        rw [hval_k_pre (6 + j) v false (Or.inr ⟨rfl, j, hj, rfl, hgj⟩) x] at hx
        exact hne hx.symm
  have hex_escape : ∃ h : Fin gs.length, iStar < h.1 ∧ ∃ w ∈ gs[h.1].inputs, w ∈ B := by
    by_contra hno
    push Not at hno
    obtain ⟨x, y, hxy_other, hxy_star, hne⟩ := fC6_no_bottleneck u v huv gs[iStar].op hop_bin pa pb
    have hsp := split_list_at gs iStar hiStar
    set w1 := wiresFrom (gs.take iStar ++ [gs[iStar]]) (List.ofFn x)
    set w2 := wiresFrom (gs.take iStar ++ [gs[iStar]]) (List.ofFn y)
    have hag := wiresFrom_agree (gs.drop (iStar + 1)) B w1 w2
      (by simp [w1, w2, wiresFrom_length])
      (by
        intro k hk
        simp only [w1, wiresFrom_length, List.length_append, List.length_take, List.length_singleton,
          List.length_ofFn, Nat.min_eq_left (Nat.le_of_lt hiStar)]
        rcases hk with rfl | rfl | ⟨j, hj, rfl, _⟩ <;> omega)
      (by
        intro k hk
        by_cases hk_lt : k < 6 + iStar
        · simp only [w1, w2]
          rw [wiresFrom_append, wiresFrom_append,
              wiresFrom_getD_lt [gs[iStar]] _ _ (by simp [wiresFrom_length, Nat.min_eq_left (Nat.le_of_lt hiStar)]; exact hk_lt),
              wiresFrom_getD_lt [gs[iStar]] _ _ (by simp [wiresFrom_length, Nat.min_eq_left (Nat.le_of_lt hiStar)]; exact hk_lt)]
          by_cases hk6 : k < 6
          · have hku : (⟨k, hk6⟩ : Fin 6) ≠ u := fun heq => hk (Or.inl (congrArg Fin.val heq))
            have hkv : (⟨k, hk6⟩ : Fin 6) ≠ v := fun heq => hk (Or.inr (Or.inl (congrArg Fin.val heq)))
            rw [wiresFrom_getD_lt _ _ _ (by simp; exact hk6),
                wiresFrom_getD_lt _ _ _ (by simp; exact hk6),
                ofFn_getD_lt _ _ _ hk6, ofFn_getD_lt _ _ _ hk6]
            exact hxy_other ⟨k, hk6⟩ hku hkv
          · have hj : k - 6 < iStar := by omega
            have hk_eq6 : k = 6 + (k - 6) := by omega
            obtain ⟨z, hgz⟩ := hpre (k - 6) hj
            have hzu : z ≠ u := fun heq => by
              subst heq; exact hk (Or.inr (Or.inr ⟨k - 6, hj, hk_eq6, Or.inl hgz⟩))
            have hzv : z ≠ v := fun heq => by
              subst heq; exact hk (Or.inr (Or.inr ⟨k - 6, hj, hk_eq6, Or.inr hgz⟩))
            rw [hval_k_pre k z false (Or.inr ⟨rfl, k - 6, hj, hk_eq6, hgz⟩) x,
                hval_k_pre k z false (Or.inr ⟨rfl, k - 6, hj, hk_eq6, hgz⟩) y]
            simp [hxy_other z hzu hzv]
        · by_cases hk_eq : k = 6 + iStar
          · subst hk_eq
            simp only [w1, w2]
            rw [wiresFrom_append, wiresFrom_append, wiresFrom_cons, wiresFrom_cons,
                wiresFrom_nil, wiresFrom_nil,
                getD_snoc_eq _ _ _ _ (by simp [wiresFrom_length, Nat.min_eq_left (Nat.le_of_lt hiStar)]),
                getD_snoc_eq _ _ _ _ (by simp [wiresFrom_length, Nat.min_eq_left (Nat.le_of_lt hiStar)]),
                hinsStar]
            simp only [List.map_cons, List.map_nil]
            rw [hval_k_pre a u pa ha_form x, hval_k_pre b v pb hb_form x,
                hval_k_pre a u pa ha_form y, hval_k_pre b v pb hb_form y]
            exact hxy_star
          · rw [List.getD_eq_default _ _ (by simp [w1, wiresFrom_length]; omega),
                List.getD_eq_default _ _ (by simp [w2, wiresFrom_length]; omega)])
      (by
        intro g hg k hk
        obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.1 hg
        rw [List.getElem_drop] at hk
        have hlt : iStar + 1 + idx < gs.length := by simp at hidx; omega
        exact hno ⟨iStar + 1 + idx, hlt⟩ (by dsimp; omega) k hk)
    have hEq := hag.2 C.output hout_not_B
    have hx_eq : (wiresFrom (gs.drop (iStar + 1)) w1).getD C.output false = fC6 x := by
      rw [← wiresFrom_append, ← hsp]; exact hev x
    have hy_eq : (wiresFrom (gs.drop (iStar + 1)) w2).getD C.output false = fC6 y := by
      rw [← wiresFrom_append, ← hsp]; exact hev y
    rw [hx_eq, hy_eq] at hEq
    exact hne hEq
  obtain ⟨h, hh_gt, w, hw_in, hw_B⟩ := hex_escape
  rcases hw_B with rfl | rfl | ⟨j, hj, rfl, hgj⟩
  · exact elim_case_branch gs C.output hnok hev hmin (by omega) iStar hiStar hpre
      gs[iStar].op rfl hop_bin a b (Or.inl hinsStar) ha_lt hb_lt u v huv pa pb ha_form hb_form
      hout_ne_star h hh_gt u.1 hw_in (Or.inl rfl)
  · exact elim_case_branch gs C.output hnok hev hmin (by omega) iStar hiStar hpre
      gs[iStar].op rfl hop_bin b a (Or.inr hinsStar) hb_lt ha_lt v u huv.symm pb pa hb_form ha_form
      hout_ne_star h hh_gt v.1 hw_in (Or.inl rfl)
  · rcases hgj with hgj | hgj
    · exact elim_case_branch gs C.output hnok hev hmin (by omega) iStar hiStar hpre
        gs[iStar].op rfl hop_bin a b (Or.inl hinsStar) ha_lt hb_lt u v huv pa pb ha_form hb_form
        hout_ne_star h hh_gt (6 + j) hw_in (Or.inr ⟨j, hj, rfl, hgj⟩)
    · exact elim_case_branch gs C.output hnok hev hmin (by omega) iStar hiStar hpre
        gs[iStar].op rfl hop_bin b a (Or.inr hinsStar) hb_lt ha_lt v u huv.symm pb pa hb_form ha_form
        hout_ne_star h hh_gt (6 + j) hw_in (Or.inr ⟨j, hj, rfl, hgj⟩)

theorem PEqualNP.Outside.L_meta_526 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7
      (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 0 && x 5) || (x 0 && x 6)) s → 9 ≤ s := by
  intro s hs
  by_contra hlt
  have hle8 : s ≤ 8 := by omega
  have h8 : HasCircuitSize 7 f7 8 := by
    obtain ⟨C, hok, hsz, hev⟩ := hs
    exact ⟨C, hok, le_trans hsz hle8, hev⟩
  exact not_size_fC6_7 (drop_last_var h8)
