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

private lemma hardwire_project {m r s : ℕ}
    {F : (Fin m → Bool) → Bool} {G : (Fin r → Bool) → Bool}
    (idx : Fin r → Fin m) (hidx : Function.Injective idx)
    (hC : HasCircuitSize m F s)
    (hFG : ∀ x : Fin m → Bool, F x = G (fun j : Fin r => x (idx j)))
    (hG_nc : ∃ y y' : Fin r → Bool, G y ≠ G y') :
    HasCircuitSize r G s := by
  classical
  obtain ⟨C, hok, hsz, hev⟩ := hC
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOkGate g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hok g0 hg0)
  set init : List (Bool ⊕ ℕ) :=
    List.ofFn (fun i : Fin m =>
      if h : ∃ j : Fin r, idx j = i then Sum.inr (Classical.choose h).val else Sum.inl false)
    with hinit
  set acc := elimPass r gs (init, []) with hacc
  let extY : (Fin r → Bool) → (Fin m → Bool) := fun y i =>
    if h : ∃ j : Fin r, idx j = i then y (Classical.choose h) else false
  have hextY_idx : ∀ (y : Fin r → Bool) (j : Fin r), extY y (idx j) = y j := by
    intro y j
    have hex : ∃ j' : Fin r, idx j' = idx j := ⟨j, rfl⟩
    simp only [extY, hex, ↓reduceDIte]
    have hch : Classical.choose hex = j := hidx (Classical.choose_spec hex)
    rw [hch]
  have hinv : ∀ y : Fin r → Bool,
      ElimInv r (List.ofFn y) (wiresFrom gs (List.ofFn (extY y))) acc := by
    intro y
    apply elimInv_pass r (List.ofFn y) gs _ (init, []) (fun g hg => (hnok g hg).1)
    refine ⟨by simp, by simp [hinit], ?_⟩
    intro i
    by_cases hi : i < m
    · rw [hinit, ofFn_getD_lt _ _ _ hi, ofFn_getD_lt _ _ _ hi]
      by_cases hex : ∃ j : Fin r, idx j = ⟨i, hi⟩
      · simp only [extY, hex, ↓reduceDIte, statValid, statVal, wiresFrom_nil]
        refine ⟨(Classical.choose hex).isLt, ?_⟩
        rw [ofFn_getD_lt _ _ _ (Classical.choose hex).isLt]
      · simp only [extY, hex, ↓reduceDIte, statValid, statVal]
        trivial
    · rw [List.getD_eq_default _ _ (by simp [hinit]; omega),
          List.getD_eq_default _ _ (by simp; omega)]
      exact ⟨trivial, rfl⟩
  have hval : ∀ y : Fin r → Bool,
      statVal (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD C.output (Sum.inl false)) = G y := by
    intro y
    rw [((hinv y).2.2 C.output).2, hgs, wiresFrom_norm]
    have h1 := hev (extY y)
    have h2 := hFG (extY y)
    have heq : (fun j : Fin r => extY y (idx j)) = y := by
      funext j; exact hextY_idx y j
    rw [heq] at h2
    exact h1.trans h2
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    obtain ⟨y, y', hne⟩ := hG_nc
    have hy := hval y; have hy' := hval y'
    rw [hst] at hy hy'
    exact absurd (hy.symm.trans hy') hne
  | inr j =>
    refine ⟨⟨acc.2, j⟩, elimPass_ok r gs _ (by simp), ?_, ?_⟩
    · show acc.2.length ≤ s
      have := elimPass_len r gs (init, [])
      rw [← hacc] at this
      have hlen : gs.length = C.gates.length := by simp [hgs]
      have hsz' : C.gates.length ≤ s := hsz
      simp only [List.length_nil, zero_add] at this
      omega
    · intro y
      have := hval y
      rw [hst] at this
      exact this

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

private def bumpWire (k w : ℕ) : ℕ :=
  if w < k then w else w + 1

private def bumpGate (k : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (bumpWire k)⟩

private lemma bumpGate_ok (k : ℕ) (g : Gate) (h : OkGate g) : OkGate (bumpGate k g) :=
  ⟨h.1, by simp [bumpGate]; exact h.2⟩

private lemma getD_bump_append (pref tail : List Bool) (z : Bool) (i : ℕ) :
    ((pref ++ [z]) ++ tail).getD (bumpWire pref.length i) false = (pref ++ tail).getD i false := by
  by_cases hi1 : i < pref.length
  · simp only [bumpWire, hi1, ↓reduceIte]
    rw [List.getD_eq_getElem _ _ (by simp; omega),
        List.getD_eq_getElem _ _ (by simp; omega),
        List.getElem_append_left (by simp; omega),
        List.getElem_append_left hi1,
        List.getElem_append_left hi1]
  · simp only [bumpWire, hi1, ↓reduceIte]
    by_cases hi2 : i < pref.length + tail.length
    · rw [List.getD_eq_getElem _ _ (by simp; omega),
          List.getD_eq_getElem _ _ (by simp; omega),
          List.getElem_append_right (by simp; omega),
          List.getElem_append_right (by omega)]
      congr 1
      simp
    · rw [List.getD_eq_default _ _ (by simp; omega),
          List.getD_eq_default _ _ (by simp; omega)]

private lemma wiresFrom_bump (pref : List Bool) (z : Bool) (gs : List Gate) (tail : List Bool) :
    ∀ i : ℕ, (wiresFrom (gs.map (bumpGate pref.length)) ((pref ++ [z]) ++ tail)).getD
      (bumpWire pref.length i) false = (wiresFrom gs (pref ++ tail)).getD i false := by
  induction gs generalizing tail with
  | nil =>
    intro i
    exact getD_bump_append pref tail z i
  | cons g gs ih =>
    intro i
    rw [List.map_cons, wiresFrom_cons, wiresFrom_cons]
    have hmap : ((bumpGate pref.length g).inputs.map
        fun j => ((pref ++ [z]) ++ tail).getD j false) =
        (g.inputs.map fun j => (pref ++ tail).getD j false) := by
      simp only [bumpGate, List.map_map]
      apply List.map_congr_left
      intro j _
      exact getD_bump_append pref tail z j
    have hop : (bumpGate pref.length g).op = g.op := rfl
    rw [hmap, hop]
    simpa only [List.append_assoc] using
      ih (tail ++ [g.op.eval (g.inputs.map fun j => (pref ++ tail).getD j false)]) i

private def gFlat {n : ℕ} (g : (Fin n → Bool) → Bool → Bool) (z : Fin (n + 1) → Bool) : Bool :=
  g (fun i : Fin n => z i.castSucc) (z (Fin.last n))

private def gStar {n : ℕ} (g : (Fin n → Bool) → Bool → Bool) (z : Fin (n + 1 + 1) → Bool) : Bool :=
  g (fun i : Fin n => z i.castSucc.castSucc) (z (Fin.last n).castSucc) ||
    (z (Fin.last n).castSucc && z (Fin.last (n + 1)))

private lemma gFlat_nonconst {n : ℕ} {g : (Fin n → Bool) → Bool → Bool}
    (hg_nc : ∃ (y y' : Fin n → Bool) (b b' : Bool), g y b ≠ g y' b') :
    ∃ z z' : Fin (n + 1) → Bool, gFlat g z ≠ gFlat g z' := by
  obtain ⟨y, y', b, b', hne⟩ := hg_nc
  refine ⟨Fin.snoc y b, Fin.snoc y' b', ?_⟩
  simp only [gFlat, Fin.snoc_castSucc, Fin.snoc_last]
  exact hne

private lemma gStar_nonconst {n : ℕ} {g : (Fin n → Bool) → Bool → Bool}
    (hg_f : ∃ y : Fin n → Bool, g y false = false) :
    ∃ z z' : Fin (n + 1 + 1) → Bool, gStar g z ≠ gStar g z' := by
  obtain ⟨y₀, hy₀⟩ := hg_f
  refine ⟨Fin.snoc (Fin.snoc y₀ false) false, Fin.snoc (Fin.snoc y₀ true) true, ?_⟩
  have h0 : gStar g (Fin.snoc (Fin.snoc y₀ false) false) = false := by
    simp only [gStar, Fin.snoc_castSucc, Fin.snoc_last, hy₀]
    decide
  have h1 : gStar g (Fin.snoc (Fin.snoc y₀ true) true) = true := by
    simp only [gStar, Fin.snoc_castSucc, Fin.snoc_last]
    simp
  rw [h0, h1]
  decide

private lemma gFlat_to_gStar {n c : ℕ} (g : (Fin n → Bool) → Bool → Bool)
    (hg_nc : ∃ (y y' : Fin n → Bool) (b b' : Bool), g y b ≠ g y' b')
    (hC : HasCircuitSize (n + 1) (gFlat g) c) :
    HasCircuitSize (n + 1 + 1) (gStar g) (c + 2) := by
  obtain ⟨C, hok, hsz, hev⟩ := hC
  have hex_true : ∃ z : Fin (n + 1) → Bool, gFlat g z = true := by
    obtain ⟨z, z', hne⟩ := gFlat_nonconst hg_nc
    cases hz : gFlat g z <;> cases hz' : gFlat g z'
    · exact absurd (hz.trans hz'.symm) hne
    · exact ⟨z', hz'⟩
    · exact ⟨z, hz⟩
    · exact absurd (hz.trans hz'.symm) hne
  obtain ⟨z₁, hz₁⟩ := hex_true
  have hout_lt : C.output < (n + 1) + C.gates.length := by
    by_contra hge
    have h1 : C.eval (List.ofFn z₁) = false := by
      show (wiresFrom C.gates (List.ofFn z₁)).getD C.output false = false
      exact List.getD_eq_default _ _ (by rw [wiresFrom_length]; simp; omega)
    have h2 := hev z₁
    rw [h1, hz₁] at h2
    exact Bool.false_ne_true h2
  set gs1 := C.gates.map (bumpGate (n + 1)) with hgs1
  set w_and := (n + 1 + 1) + gs1.length with hwand
  set gs2 := gs1 ++ [⟨GateOp.and, [n, n + 1]⟩, ⟨GateOp.or, [bumpWire (n + 1) C.output, w_and]⟩]
    with hgs2
  have hok2 : ∀ gt ∈ gs2, OkGate gt := by
    intro gt hgt
    rcases List.mem_append.1 hgt with h | h
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h
      exact bumpGate_ok (n + 1) g0 (hok g0 hg0)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> simp [OkGate]
  have hlen2 : gs2.length ≤ c + 2 := by
    have hsz' : C.gates.length ≤ c := hsz
    simp [hgs2, hgs1]
    omega
  refine ⟨⟨gs2, w_and + 1⟩, hok2, hlen2, ?_⟩
  intro z
  show (wiresFrom gs2 (List.ofFn z)).getD (w_and + 1) false = gStar g z
  set pref := List.ofFn (fun i : Fin (n + 1) => z i.castSucc) with hpref
  have hpref_len : pref.length = n + 1 := by simp [hpref]
  have hsplit : List.ofFn z = pref ++ [z (Fin.last (n + 1))] := by
    apply List.ext_getElem (by simp [hpref])
    intro i h1 h2
    rw [List.getElem_ofFn]
    by_cases hi : i < n + 1
    · rw [List.getElem_append_left (by rw [hpref_len]; exact hi)]
      simp only [hpref, List.getElem_ofFn]
      rfl
    · have hieq : i = n + 1 := by simp at h1; omega
      subst hieq
      rw [List.getElem_append_right (by rw [hpref_len])]
      simp [hpref_len, Fin.last]
  set w1 := wiresFrom gs1 (List.ofFn z) with hw1
  have hw1_len : w1.length = w_and := by
    rw [hw1, wiresFrom_length, hwand]
    simp
  have hgs2_eval : (wiresFrom gs2 (List.ofFn z)).getD (w_and + 1) false =
      (w1.getD (bumpWire (n + 1) C.output) false || (w1.getD n false && w1.getD (n + 1) false)) := by
    rw [hgs2, wiresFrom_append, ← hw1, wiresFrom_cons, wiresFrom_cons, wiresFrom_nil]
    have h1 : (w1 ++ [GateOp.and.eval ([n, n + 1].map fun i => w1.getD i false)]).length =
        w_and + 1 := by simp [hw1_len]
    rw [getD_snoc_eq _ _ _ _ h1.symm]
    simp only [List.map_cons, List.map_nil, GateOp.eval]
    have hlt_out : bumpWire (n + 1) C.output < w1.length := by
      rw [hw1_len, hwand, hgs1, List.length_map]
      simp only [bumpWire]
      split_ifs <;> omega
    rw [getD_snoc_lt _ _ _ _ hlt_out, getD_snoc_eq _ _ _ _ hw1_len.symm]
    simp
  rw [hgs2_eval]
  have hwn : w1.getD n false = z (Fin.last n).castSucc := by
    rw [hw1, wiresFrom_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ (by omega)]
    rfl
  have hwn1 : w1.getD (n + 1) false = z (Fin.last (n + 1)) := by
    rw [hw1, wiresFrom_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ (by omega)]
    rfl
  have hwout : w1.getD (bumpWire (n + 1) C.output) false =
      g (fun i : Fin n => z i.castSucc.castSucc) (z (Fin.last n).castSucc) := by
    have hb := wiresFrom_bump pref (z (Fin.last (n + 1))) C.gates [] C.output
    rw [hpref_len, List.append_nil, List.append_nil, ← hsplit, ← hgs1, ← hw1] at hb
    rw [hb]
    exact hev (fun i : Fin (n + 1) => z i.castSucc)
  rw [hwn, hwn1, hwout]
  rfl

private lemma acyclic_leaf_cases {n : ℕ} (G : SimpleGraph (Fin n)) (hAcyc : G.IsAcyclic)
    (hEdge : ∃ u v : Fin n, G.Adj u v) :
    ∃ ℓ p : Fin n, G.Adj ℓ p ∧ (∀ w, G.Adj ℓ w → w = p) ∧
      ((∃ ℓ' : Fin n, ℓ' ≠ ℓ ∧ G.Adj ℓ' p ∧ ∀ w, G.Adj ℓ' w → w = p) ∨
       (∀ w, G.Adj p w → w = ℓ) ∨
       (∃ q : Fin n, q ≠ ℓ ∧ G.Adj p q ∧ ∀ w, G.Adj p w → w = ℓ ∨ w = q)) := by
  classical
  have hlen_lt : ∀ {u v : Fin n} (P : G.Walk u v), P.IsPath → P.length < n := by
    intro u v P hP
    have h1 : P.support.length ≤ Fintype.card (Fin n) := hP.support_nodup.length_le_card
    rw [P.length_support, Fintype.card_fin] at h1
    omega
  set S : Finset ℕ := (Finset.range n).filter
    (fun k => ∃ u v : Fin n, ∃ P : G.Walk u v, P.IsPath ∧ P.length = k) with hS
  have hS_ne : S.Nonempty := by
    obtain ⟨u₀, v₀, hadj⟩ := hEdge
    refine ⟨1, Finset.mem_filter.2 ⟨Finset.mem_range.2 ?_, u₀, v₀,
      SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil, ?_, rfl⟩⟩
    · have hp : (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil).IsPath :=
        SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil (by simp [hadj.ne])
      exact hlen_lt _ hp
    · exact SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil (by simp [hadj.ne])
  set m := S.max' hS_ne with hm
  have hm_mem : m ∈ S := Finset.max'_mem S hS_ne
  have hm_ge : 1 ≤ m := by
    obtain ⟨u₀, v₀, hadj⟩ := hEdge
    have hp : (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil).IsPath :=
      SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil (by simp [hadj.ne])
    have h1 : 1 ∈ S := Finset.mem_filter.2
      ⟨Finset.mem_range.2 (hlen_lt _ hp), u₀, v₀, _, hp, rfl⟩
    exact Finset.le_max' S 1 h1
  have hm_max : ∀ {u v : Fin n} (P : G.Walk u v), P.IsPath → P.length ≤ m := by
    intro u v P hP
    have hmem : P.length ∈ S := Finset.mem_filter.2
      ⟨Finset.mem_range.2 (hlen_lt P hP), u, v, P, hP, rfl⟩
    exact Finset.le_max' S P.length hmem
  obtain ⟨_, ℓ, z, P, hP, hPlen⟩ := Finset.mem_filter.1 hm_mem
  cases P with
  | nil => simp at hPlen; omega
  | @cons _ p _ hlp Q =>
    have hQ : Q.IsPath := hP.of_cons
    have hℓ_not_Q : ℓ ∉ Q.support := by
      have hnd := hP.support_nodup
      simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at hnd
      exact hnd.1
    have hℓ_leaf : ∀ w, G.Adj ℓ w → w = p := by
      intro w hlw
      by_cases hw : w ∈ (SimpleGraph.Walk.cons hlp Q).support
      · simpa using hAcyc.eq_snd_of_adj_start hP hlw hw
      · exfalso
        have hP' : (SimpleGraph.Walk.cons hlw.symm (SimpleGraph.Walk.cons hlp Q)).IsPath :=
          SimpleGraph.Walk.IsPath.cons hP hw
        have hle := hm_max _ hP'
        simp only [SimpleGraph.Walk.length_cons] at hPlen hle
        omega
    have hnotQ_leaf : ∀ w, G.Adj p w → w ∉ Q.support → ∀ u, G.Adj w u → u = p := by
      intro w hpw hwQ u hwu
      by_contra hup
      by_cases huQ : u ∈ Q.support
      · set Q' := Q.takeUntil u huQ
        have hQ' : Q'.IsPath := hQ.takeUntil huQ
        have hR : (SimpleGraph.Walk.cons hpw (SimpleGraph.Walk.cons hwu SimpleGraph.Walk.nil)).IsPath := by
          refine SimpleGraph.Walk.IsPath.cons
            (SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil (by simp [hwu.ne])) ?_
          simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
            List.not_mem_nil, or_false, not_or]
          exact ⟨hpw.ne, Ne.symm hup⟩
        have heq := (hAcyc.subsingleton_path p u).elim ⟨Q', hQ'⟩ ⟨_, hR⟩
        have hw_in_R : w ∈ (SimpleGraph.Walk.cons hpw (SimpleGraph.Walk.cons hwu SimpleGraph.Walk.nil)).support := by
          simp
        have hw_in_Q' : w ∈ Q'.support := by
          rw [Subtype.mk.inj heq]; exact hw_in_R
        exact hwQ (SimpleGraph.Walk.support_takeUntil_subset_support Q huQ hw_in_Q')
      · have hP1 : (SimpleGraph.Walk.cons hpw.symm Q).IsPath :=
          SimpleGraph.Walk.IsPath.cons hQ hwQ
        have hu_not : u ∉ (SimpleGraph.Walk.cons hpw.symm Q).support := by
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons, not_or]
          exact ⟨hwu.ne.symm, huQ⟩
        have hP2 : (SimpleGraph.Walk.cons hwu.symm (SimpleGraph.Walk.cons hpw.symm Q)).IsPath :=
          SimpleGraph.Walk.IsPath.cons hP1 hu_not
        have hle := hm_max _ hP2
        simp only [SimpleGraph.Walk.length_cons] at hPlen hle
        omega
    refine ⟨ℓ, p, hlp, hℓ_leaf, ?_⟩
    cases Q with
    | nil =>
      by_cases hother : ∃ ℓ' : Fin n, ℓ' ≠ ℓ ∧ G.Adj z ℓ'
      · obtain ⟨ℓ', hne, hadj⟩ := hother
        have hnot : ℓ' ∉ (SimpleGraph.Walk.nil : G.Walk z z).support := by
          simp [hadj.ne.symm]
        exact Or.inl ⟨ℓ', hne, hadj.symm, hnotQ_leaf ℓ' hadj hnot⟩
      · refine Or.inr (Or.inl ?_)
        intro w hpw
        by_contra hwne
        exact hother ⟨w, hwne, hpw⟩
    | @cons _ q _ hpq Q' =>
      have hq_ne_ℓ : q ≠ ℓ := by
        intro hq
        apply hℓ_not_Q
        rw [← hq]
        simp
      by_cases hother : ∃ ℓ' : Fin n, ℓ' ≠ ℓ ∧ ℓ' ≠ q ∧ G.Adj p ℓ'
      · obtain ⟨ℓ', hne1, hne2, hadj⟩ := hother
        have hnot : ℓ' ∉ (SimpleGraph.Walk.cons hpq Q').support := by
          intro hmem
          exact hne2 (by simpa using hAcyc.eq_snd_of_adj_start hQ hadj hmem)
        exact Or.inl ⟨ℓ', hne1, hadj.symm, hnotQ_leaf ℓ' hadj hnot⟩
      · refine Or.inr (Or.inr ⟨q, hq_ne_ℓ, hpq, ?_⟩)
        intro w hpw
        by_contra hnot
        exact hother ⟨w, fun h => hnot (Or.inl h), fun h => hnot (Or.inr h), hpw⟩

private lemma acyclic_nonroot_leaf_cases {k : ℕ} (K : SimpleGraph (Fin (k + 1)))
    (hAcyc : K.IsAcyclic) (hNonRoot : ∃ u v : Fin (k + 1), K.Adj u v ∧ u ≠ 0 ∧ v ≠ 0) :
    ∃ ℓ p : Fin (k + 1), ℓ ≠ 0 ∧ p ≠ 0 ∧ K.Adj ℓ p ∧ (∀ w, K.Adj ℓ w → w = p) ∧
      ((∃ ℓ' : Fin (k + 1), ℓ' ≠ ℓ ∧ ℓ' ≠ 0 ∧ K.Adj ℓ' p ∧ ∀ w, K.Adj ℓ' w → w = p) ∨
       (∀ w, K.Adj p w → w = ℓ) ∨
       (∃ q : Fin (k + 1), q ≠ ℓ ∧ K.Adj p q ∧ ∀ w, K.Adj p w → w = ℓ ∨ w = q)) := by
  classical
  have hlen_lt : ∀ {u v : Fin (k + 1)} (P : K.Walk u v), P.IsPath → P.length < k + 1 := by
    intro u v P hP
    have h1 : P.support.length ≤ Fintype.card (Fin (k + 1)) := hP.support_nodup.length_le_card
    rw [P.length_support, Fintype.card_fin] at h1
    omega
  by_cases hpath2 : ∃ z : Fin (k + 1), ∃ P : K.Walk z 0, P.IsPath ∧ 2 ≤ P.length
  · set S : Finset ℕ := (Finset.range (k + 1)).filter
      (fun m => ∃ z : Fin (k + 1), ∃ P : K.Walk z 0, P.IsPath ∧ P.length = m) with hS
    have hS_ne : S.Nonempty := by
      obtain ⟨z₀, P₀, hP₀, _⟩ := hpath2
      exact ⟨P₀.length, Finset.mem_filter.2 ⟨Finset.mem_range.2 (hlen_lt P₀ hP₀), z₀, P₀, hP₀, rfl⟩⟩
    set m := S.max' hS_ne with hm
    have hm_mem : m ∈ S := Finset.max'_mem S hS_ne
    have hm_ge : 2 ≤ m := by
      obtain ⟨z₀, P₀, hP₀, hge⟩ := hpath2
      have hmem : P₀.length ∈ S := Finset.mem_filter.2
        ⟨Finset.mem_range.2 (hlen_lt P₀ hP₀), z₀, P₀, hP₀, rfl⟩
      have hle := Finset.le_max' S P₀.length hmem
      omega
    have hm_max : ∀ {z : Fin (k + 1)} (P : K.Walk z 0), P.IsPath → P.length ≤ m := by
      intro z P hP
      have hmem : P.length ∈ S := Finset.mem_filter.2
        ⟨Finset.mem_range.2 (hlen_lt P hP), z, P, hP, rfl⟩
      exact Finset.le_max' S P.length hmem
    obtain ⟨_, ℓ, P, hP, hPlen⟩ := Finset.mem_filter.1 hm_mem
    cases P with
    | nil => simp at hPlen; omega
    | @cons _ p _ hlp Q =>
      cases Q with
      | nil => simp at hPlen; omega
      | @cons _ q _ hpq Q' =>
        have hQ : (SimpleGraph.Walk.cons hpq Q').IsPath := hP.of_cons
        have h0_Q' : (0 : Fin (k + 1)) ∈ Q'.support := SimpleGraph.Walk.end_mem_support Q'
        have h0_Q : (0 : Fin (k + 1)) ∈ (SimpleGraph.Walk.cons hpq Q').support := by
          simp [h0_Q']
        have hndP := hP.support_nodup
        simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at hndP
        have hℓ_not_Q : ℓ ∉ (SimpleGraph.Walk.cons hpq Q').support := by
          simpa only [SimpleGraph.Walk.support_cons] using hndP.1
        have hp_not_Q' : p ∉ Q'.support := hndP.2.1
        have hℓ0 : ℓ ≠ 0 := fun h => hℓ_not_Q (h ▸ h0_Q)
        have hp0 : p ≠ 0 := fun h => hp_not_Q' (h ▸ h0_Q')
        have hq_ne_ℓ : q ≠ ℓ := by
          intro hq
          apply hℓ_not_Q
          rw [← hq]
          simp
        have hℓ_leaf : ∀ w, K.Adj ℓ w → w = p := by
          intro w hlw
          by_cases hw : w ∈ (SimpleGraph.Walk.cons hlp (SimpleGraph.Walk.cons hpq Q')).support
          · simpa using hAcyc.eq_snd_of_adj_start hP hlw hw
          · exfalso
            have hP' : (SimpleGraph.Walk.cons hlw.symm
                (SimpleGraph.Walk.cons hlp (SimpleGraph.Walk.cons hpq Q'))).IsPath :=
              SimpleGraph.Walk.IsPath.cons hP hw
            have hle := hm_max _ hP'
            simp only [SimpleGraph.Walk.length_cons] at hPlen hle
            omega
        have hnotQ_leaf : ∀ w, K.Adj p w → w ∉ (SimpleGraph.Walk.cons hpq Q').support →
            ∀ u, K.Adj w u → u = p := by
          intro w hpw hwQ u hwu
          by_contra hup
          by_cases huQ : u ∈ (SimpleGraph.Walk.cons hpq Q').support
          · set Q'' := (SimpleGraph.Walk.cons hpq Q').takeUntil u huQ
            have hQ'' : Q''.IsPath := hQ.takeUntil huQ
            have hR : (SimpleGraph.Walk.cons hpw (SimpleGraph.Walk.cons hwu SimpleGraph.Walk.nil)).IsPath := by
              refine SimpleGraph.Walk.IsPath.cons
                (SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil (by simp [hwu.ne])) ?_
              simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
                List.not_mem_nil, or_false, not_or]
              exact ⟨hpw.ne, Ne.symm hup⟩
            have heq := (hAcyc.subsingleton_path p u).elim ⟨Q'', hQ''⟩ ⟨_, hR⟩
            have hw_in_R : w ∈ (SimpleGraph.Walk.cons hpw (SimpleGraph.Walk.cons hwu SimpleGraph.Walk.nil)).support := by
              simp
            have hw_in_Q'' : w ∈ Q''.support := by
              rw [Subtype.mk.inj heq]; exact hw_in_R
            exact hwQ (SimpleGraph.Walk.support_takeUntil_subset_support _ huQ hw_in_Q'')
          · have hP1 : (SimpleGraph.Walk.cons hpw.symm (SimpleGraph.Walk.cons hpq Q')).IsPath :=
              SimpleGraph.Walk.IsPath.cons hQ hwQ
            have hu_not : u ∉ (SimpleGraph.Walk.cons hpw.symm (SimpleGraph.Walk.cons hpq Q')).support := by
              intro hmem
              rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hmem
              rcases hmem with rfl | hmem
              · exact hwu.ne.symm rfl
              · exact huQ hmem
            have hP2 : (SimpleGraph.Walk.cons hwu.symm
                (SimpleGraph.Walk.cons hpw.symm (SimpleGraph.Walk.cons hpq Q'))).IsPath :=
              SimpleGraph.Walk.IsPath.cons hP1 hu_not
            have hle := hm_max _ hP2
            simp only [SimpleGraph.Walk.length_cons] at hPlen hle
            omega
        refine ⟨ℓ, p, hℓ0, hp0, hlp, hℓ_leaf, ?_⟩
        by_cases hother : ∃ ℓ' : Fin (k + 1), ℓ' ≠ ℓ ∧ ℓ' ≠ q ∧ K.Adj p ℓ'
        · obtain ⟨ℓ', hne1, hne2, hadj⟩ := hother
          have hnot : ℓ' ∉ (SimpleGraph.Walk.cons hpq Q').support := by
            intro hmem
            exact hne2 (by simpa using hAcyc.eq_snd_of_adj_start hQ hadj hmem)
          have hℓ'0 : ℓ' ≠ 0 := fun h => hnot (h ▸ h0_Q)
          exact Or.inl ⟨ℓ', hne1, hℓ'0, hadj.symm, hnotQ_leaf ℓ' hadj hnot⟩
        · refine Or.inr (Or.inr ⟨q, hq_ne_ℓ, hpq, ?_⟩)
          intro w hpw
          by_contra hnot
          exact hother ⟨w, fun h => hnot (Or.inl h), fun h => hnot (Or.inr h), hpw⟩
  · obtain ⟨u, v, huv, hu0, hv0⟩ := hNonRoot
    have hnot_reach : ¬ K.Reachable u 0 := by
      intro hreach
      obtain ⟨P, hP⟩ := hreach.exists_isPath
      cases P with
      | nil => exact hu0 rfl
      | @cons _ w _ huw Q =>
        cases Q with
        | nil =>
          have hP2 : (SimpleGraph.Walk.cons huv.symm
              (SimpleGraph.Walk.cons huw SimpleGraph.Walk.nil)).IsPath := by
            refine SimpleGraph.Walk.IsPath.cons
              (SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil (by simp [hu0])) ?_
            simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
              List.not_mem_nil, or_false, not_or]
            exact ⟨huv.ne.symm, hv0⟩
          exact hpath2 ⟨v, _, hP2, by simp⟩
        | @cons _ x _ hwx Q' =>
          exact hpath2 ⟨u, _, hP, by simp⟩
    let K' : SimpleGraph (Fin (k + 1)) :=
      { Adj := fun a b => K.Adj a b ∧ ¬ K.Reachable a 0
        symm := ⟨fun _ _ h =>
          ⟨h.1.symm, fun hrb => h.2 ((SimpleGraph.Adj.reachable h.1).trans hrb)⟩⟩
        loopless := ⟨fun a h => K.loopless.irrefl a h.1⟩ }
    have hK'_le : K' ≤ K := fun _ _ h => h.1
    have hK'_acyc : K'.IsAcyclic := hAcyc.anti hK'_le
    have hK'_edge : ∃ a b : Fin (k + 1), K'.Adj a b := ⟨u, v, huv, hnot_reach⟩
    obtain ⟨ℓ, p, hlp', hℓ_leaf', hcases'⟩ := acyclic_leaf_cases K' hK'_acyc hK'_edge
    have hℓ_nr : ¬ K.Reachable ℓ 0 := hlp'.2
    have hp_nr : ¬ K.Reachable p 0 := fun hr => hℓ_nr ((SimpleGraph.Adj.reachable hlp'.1).trans hr)
    have hℓ0 : ℓ ≠ 0 := by intro h; subst h; exact hℓ_nr (SimpleGraph.Reachable.refl 0)
    have hp0 : p ≠ 0 := by intro h; subst h; exact hp_nr (SimpleGraph.Reachable.refl 0)
    refine ⟨ℓ, p, hℓ0, hp0, hlp'.1, fun w hlw => hℓ_leaf' w ⟨hlw, hℓ_nr⟩, ?_⟩
    rcases hcases' with ⟨ℓ', hne, hℓ'p', hℓ'leaf'⟩ | hpdeg1 | ⟨q, hqne, hpq', hpdeg2⟩
    · have hℓ'nr : ¬ K.Reachable ℓ' 0 := hℓ'p'.2
      have hℓ'0 : ℓ' ≠ 0 := by intro h; subst h; exact hℓ'nr (SimpleGraph.Reachable.refl 0)
      exact Or.inl ⟨ℓ', hne, hℓ'0, hℓ'p'.1, fun w hw => hℓ'leaf' w ⟨hw, hℓ'nr⟩⟩
    · exact Or.inr (Or.inl fun w hw => hpdeg1 w ⟨hw, hp_nr⟩)
    · exact Or.inr (Or.inr ⟨q, hqne, hpq'.1, fun w hw => hpdeg2 w ⟨hw, hp_nr⟩⟩)

private def IsVC {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S

private def deleteVertexEdges {n : ℕ} (G : SimpleGraph (Fin n)) (p : Fin n) :
    SimpleGraph (Fin n) where
  Adj u v := G.Adj u v ∧ u ≠ p ∧ v ≠ p
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun v h => G.loopless.irrefl v h.1⟩

private lemma deleteVertexEdges_le {n : ℕ} (G : SimpleGraph (Fin n)) (p : Fin n) :
    deleteVertexEdges G p ≤ G :=
  fun _ _ h => h.1

private lemma edgeFinset_card_deleteEdge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ℓ p : Fin n) (hlp : G.Adj ℓ p) [DecidableRel (G.deleteEdges {s(ℓ, p)}).Adj] :
    (G.deleteEdges {s(ℓ, p)}).edgeFinset.card + 1 = G.edgeFinset.card := by
  have heq : (G.deleteEdges {s(ℓ, p)}).edgeFinset = G.edgeFinset.erase s(ℓ, p) := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset, Finset.mem_erase, SimpleGraph.edgeSet_deleteEdges,
      Set.mem_sdiff, Set.mem_singleton_iff]
    tauto
  rw [heq]
  have hmem : s(ℓ, p) ∈ G.edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset]; exact hlp
  have hpos : 1 ≤ G.edgeFinset.card := Finset.one_le_card.2 ⟨s(ℓ, p), hmem⟩
  rw [Finset.card_erase_of_mem hmem]
  omega

private lemma edgeFinset_card_deleteVertex_deg1 {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (ℓ p : Fin n) (hlp : G.Adj ℓ p)
    (hpdeg : ∀ w, G.Adj p w → w = ℓ) [DecidableRel (deleteVertexEdges G p).Adj] :
    (deleteVertexEdges G p).edgeFinset.card + 1 = G.edgeFinset.card := by
  have heq : (deleteVertexEdges G p).edgeFinset = G.edgeFinset.erase s(ℓ, p) := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      rw [SimpleGraph.mem_edgeFinset, Finset.mem_erase, SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet, SimpleGraph.mem_edgeSet]
      dsimp only [deleteVertexEdges]
      constructor
      · rintro ⟨huv, hup, hvp⟩
        refine ⟨?_, huv⟩
        intro he
        rw [Sym2.eq_iff] at he
        rcases he with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact hvp h2
        · exact hup h1
      · rintro ⟨hne, huv⟩
        refine ⟨huv, ?_, ?_⟩
        · intro hup; subst hup
          exact hne (by rw [Sym2.eq_iff]; exact Or.inr ⟨rfl, hpdeg v huv⟩)
        · intro hvp; subst hvp
          exact hne (by rw [Sym2.eq_iff]; exact Or.inl ⟨hpdeg u huv.symm, rfl⟩)
  rw [heq]
  have hmem : s(ℓ, p) ∈ G.edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset]; exact hlp
  have hpos : 1 ≤ G.edgeFinset.card := Finset.one_le_card.2 ⟨s(ℓ, p), hmem⟩
  rw [Finset.card_erase_of_mem hmem]
  omega

private lemma edgeFinset_card_deleteVertex_deg2 {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (ℓ p q : Fin n) (hlp : G.Adj ℓ p) (hpq : G.Adj p q)
    (hqne : q ≠ ℓ) (hpdeg : ∀ w, G.Adj p w → w = ℓ ∨ w = q)
    [DecidableRel (deleteVertexEdges G p).Adj] :
    (deleteVertexEdges G p).edgeFinset.card + 2 = G.edgeFinset.card := by
  have heq : (deleteVertexEdges G p).edgeFinset =
      (G.edgeFinset.erase s(ℓ, p)).erase s(p, q) := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      rw [SimpleGraph.mem_edgeFinset, Finset.mem_erase, Finset.mem_erase,
          SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.mem_edgeSet]
      dsimp only [deleteVertexEdges]
      constructor
      · rintro ⟨huv, hup, hvp⟩
        refine ⟨?_, ?_, huv⟩
        · intro he; rw [Sym2.eq_iff] at he
          rcases he with ⟨h1, _⟩ | ⟨_, h2⟩
          · exact hup h1
          · exact hvp h2
        · intro he; rw [Sym2.eq_iff] at he
          rcases he with ⟨_, h2⟩ | ⟨h1, _⟩
          · exact hvp h2
          · exact hup h1
      · rintro ⟨hne2, hne1, huv⟩
        refine ⟨huv, ?_, ?_⟩
        · intro hup; subst hup
          rcases hpdeg v huv with rfl | rfl
          · exact hne1 (by rw [Sym2.eq_iff]; exact Or.inr ⟨rfl, rfl⟩)
          · exact hne2 (by rw [Sym2.eq_iff]; exact Or.inl ⟨rfl, rfl⟩)
        · intro hvp; subst hvp
          rcases hpdeg u huv.symm with rfl | rfl
          · exact hne1 (by rw [Sym2.eq_iff]; exact Or.inl ⟨rfl, rfl⟩)
          · exact hne2 (by rw [Sym2.eq_iff]; exact Or.inr ⟨rfl, rfl⟩)
  rw [heq]
  have hmem1 : s(ℓ, p) ∈ G.edgeFinset := by rw [SimpleGraph.mem_edgeFinset]; exact hlp
  have hne_edges : s(p, q) ≠ s(ℓ, p) := by
    intro h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact hlp.ne h1.symm
    · exact hqne h2
  have hmem2 : s(p, q) ∈ G.edgeFinset.erase s(ℓ, p) :=
    Finset.mem_erase.2 ⟨hne_edges, by rw [SimpleGraph.mem_edgeFinset]; exact hpq⟩
  have hpos2 : 1 ≤ (G.edgeFinset.erase s(ℓ, p)).card := Finset.one_le_card.2 ⟨s(p, q), hmem2⟩
  rw [Finset.card_erase_of_mem hmem2, Finset.card_erase_of_mem hmem1]
  rw [Finset.card_erase_of_mem hmem1] at hpos2
  omega

private lemma edgeFinset_card_star_single {k : ℕ} (K : SimpleGraph (Fin (k + 1)))
    [DecidableRel K.Adj] (w : Fin (k + 1))
    (hstar : ∀ u v : Fin (k + 1), K.Adj u v → u = 0 ∨ v = 0)
    (h0w : K.Adj 0 w) (huniq : ∀ u : Fin (k + 1), K.Adj 0 u → u = w) :
    K.edgeFinset.card = 1 := by
  have heq : K.edgeFinset = {s(0, w)} := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Finset.mem_singleton, Sym2.eq_iff]
      constructor
      · intro huv
        rcases hstar u v huv with rfl | rfl
        · exact Or.inl ⟨rfl, huniq v huv⟩
        · exact Or.inr ⟨huniq u huv.symm, rfl⟩
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact h0w
        · exact h0w.symm
  rw [heq, Finset.card_singleton]

private def sharedFun {n k a : ℕ}
    (K : SimpleGraph (Fin (k + 1))) [DecidableRel K.Adj]
    (A : Finset (Fin (k + 1))) (B : Finset (Fin a))
    (g : (Fin n → Bool) → Bool → Bool)
    (x : Fin (n + ((k + 1) + a)) → Bool) : Bool :=
  g (fun i : Fin n => x (Fin.castAdd ((k + 1) + a) i))
    (x (Fin.natAdd n (Fin.castAdd a (0 : Fin (k + 1))))) ||
  decide (∃ u w : Fin (k + 1), K.Adj u w ∧
    x (Fin.natAdd n (Fin.castAdd a u)) = true ∧
    x (Fin.natAdd n (Fin.castAdd a w)) = true) ||
  decide (∃ u ∈ A, x (Fin.natAdd n (Fin.castAdd a u)) = true) ||
  decide (∃ i ∈ B, x (Fin.natAdd n (Fin.natAdd (k + 1) i)) = true)

private def mkInput {n k a : ℕ} (y : Fin n → Bool) (xK : Fin (k + 1) → Bool)
    (xB : Fin a → Bool) : Fin (n + ((k + 1) + a)) → Bool :=
  Fin.append y (Fin.append xK xB)

private lemma mkInput_y {n k a : ℕ} (y : Fin n → Bool) (xK : Fin (k + 1) → Bool)
    (xB : Fin a → Bool) (i : Fin n) :
    mkInput y xK xB (Fin.castAdd ((k + 1) + a) i) = y i := by
  simp [mkInput, Fin.append_left]

private lemma mkInput_K {n k a : ℕ} (y : Fin n → Bool) (xK : Fin (k + 1) → Bool)
    (xB : Fin a → Bool) (u : Fin (k + 1)) :
    mkInput y xK xB (Fin.natAdd n (Fin.castAdd a u)) = xK u := by
  simp [mkInput, Fin.append_right, Fin.append_left]

private lemma mkInput_B {n k a : ℕ} (y : Fin n → Bool) (xK : Fin (k + 1) → Bool)
    (xB : Fin a → Bool) (i : Fin a) :
    mkInput y xK xB (Fin.natAdd n (Fin.natAdd (k + 1) i)) = xB i := by
  simp [mkInput, Fin.append_right]

private lemma fin_castAdd_ne_natAdd {n m : ℕ} (i : Fin n) (j : Fin m) :
    Fin.castAdd m i ≠ Fin.natAdd n j := by
  intro h
  have hv := congrArg Fin.val h
  simp [Fin.castAdd, Fin.natAdd] at hv
  omega

private lemma sharedFun_nonconst {n k a : ℕ}
    (K : SimpleGraph (Fin (k + 1))) [DecidableRel K.Adj]
    (A : Finset (Fin (k + 1))) (B : Finset (Fin a))
    (g : (Fin n → Bool) → Bool → Bool)
    (h0A : (0 : Fin (k + 1)) ∉ A)
    (hg_nc : ∃ (y y' : Fin n → Bool) (b b' : Bool), g y b ≠ g y' b') :
    ∃ x x' : Fin (n + ((k + 1) + a)) → Bool, sharedFun K A B g x ≠ sharedFun K A B g x' := by
  obtain ⟨y, y', b, b', hne⟩ := hg_nc
  let x1 := mkInput y (fun u : Fin (k + 1) => if u = 0 then b else false) (fun _ : Fin a => false)
  let x2 := mkInput y' (fun u : Fin (k + 1) => if u = 0 then b' else false) (fun _ : Fin a => false)
  have heval : ∀ (yv : Fin n → Bool) (bv : Bool),
      sharedFun K A B g (mkInput yv (fun u : Fin (k + 1) => if u = 0 then bv else false)
        (fun _ : Fin a => false)) = g yv bv := by
    intro yv bv
    simp only [sharedFun, mkInput_y, mkInput_K, mkInput_B, ↓reduceIte]
    have hK : ¬ ∃ u w : Fin (k + 1), K.Adj u w ∧
        (if u = 0 then bv else false) = true ∧ (if w = 0 then bv else false) = true := by
      rintro ⟨u, w, huw, hu, hw⟩
      by_cases hu0 : u = 0
      · subst hu0
        have hw0 : w ≠ 0 := huw.ne.symm
        simp [hw0] at hw
      · simp [hu0] at hu
    have hA : ¬ ∃ u ∈ A, (if u = 0 then bv else false) = true := by
      rintro ⟨u, huA, hu⟩
      have hu0 : u ≠ 0 := fun h => h0A (h ▸ huA)
      simp [hu0] at hu
    rw [decide_eq_false hK, decide_eq_false hA]
    simp
  refine ⟨x1, x2, ?_⟩
  rw [heval y b, heval y' b']
  exact hne

private lemma sharedFun_dep_B {n k a : ℕ}
    (K : SimpleGraph (Fin (k + 1))) [DecidableRel K.Adj]
    (A : Finset (Fin (k + 1))) (B : Finset (Fin a))
    (g : (Fin n → Bool) → Bool → Bool)
    (hg_f : ∃ y : Fin n → Bool, g y false = false)
    (i : Fin a) (hi : i ∈ B) :
    ∃ x : Fin (n + ((k + 1) + a)) → Bool,
      sharedFun K A B g (Function.update x (Fin.natAdd n (Fin.natAdd (k + 1) i)) false) ≠
      sharedFun K A B g (Function.update x (Fin.natAdd n (Fin.natAdd (k + 1) i)) true) := by
  obtain ⟨y₀, hy₀⟩ := hg_f
  set x0 := mkInput y₀ (fun _ => false) (fun _ => false) with hx0
  refine ⟨x0, ?_⟩
  have hupd0 : Function.update x0 (Fin.natAdd n (Fin.natAdd (k + 1) i)) false = x0 := by
    funext j
    by_cases hj : j = Fin.natAdd n (Fin.natAdd (k + 1) i)
    · subst hj; simp [hx0, mkInput_B]
    · rw [Function.update_of_ne hj]
  have h0 : sharedFun K A B g (Function.update x0 (Fin.natAdd n (Fin.natAdd (k + 1) i)) false) =
      false := by
    rw [hupd0]
    simp only [sharedFun, hx0, mkInput_y, mkInput_K, mkInput_B, hy₀]
    simp
  have h1 : sharedFun K A B g (Function.update x0 (Fin.natAdd n (Fin.natAdd (k + 1) i)) true) =
      true := by
    simp only [sharedFun]
    have ht : ∃ j ∈ B, Function.update x0 (Fin.natAdd n (Fin.natAdd (k + 1) i)) true
        (Fin.natAdd n (Fin.natAdd (k + 1) j)) = true := ⟨i, hi, by simp⟩
    simp [ht]
  rw [h0, h1]
  decide

private lemma sharedFun_update_B {n k a : ℕ}
    (K : SimpleGraph (Fin (k + 1))) [DecidableRel K.Adj]
    (A : Finset (Fin (k + 1))) (B : Finset (Fin a))
    (g : (Fin n → Bool) → Bool → Bool) (i : Fin a) :
    (fun x => sharedFun K A B g (Function.update x (Fin.natAdd n (Fin.natAdd (k + 1) i)) false)) =
      sharedFun K A (B.erase i) g := by
  funext x
  set v := Fin.natAdd n (Fin.natAdd (k + 1) i) with hv
  have hy : (fun j : Fin n => Function.update x v false (Fin.castAdd ((k + 1) + a) j)) =
      (fun j : Fin n => x (Fin.castAdd ((k + 1) + a) j)) := by
    funext j
    exact Function.update_of_ne (fin_castAdd_ne_natAdd j _) _ _
  have hK : ∀ u : Fin (k + 1),
      Function.update x v false (Fin.natAdd n (Fin.castAdd a u)) =
        x (Fin.natAdd n (Fin.castAdd a u)) := by
    intro u
    apply Function.update_of_ne
    intro h
    have h' := Fin.natAdd_injective _ _ h
    exact fin_castAdd_ne_natAdd u i h'
  simp only [sharedFun, hy, hK]
  congr 1
  apply decide_eq_decide.2
  constructor
  · rintro ⟨j, hjB, hjx⟩
    have hji : j ≠ i := by
      intro h; subst h; simp [hv] at hjx
    refine ⟨j, Finset.mem_erase.2 ⟨hji, hjB⟩, ?_⟩
    have hne : Fin.natAdd n (Fin.natAdd (k + 1) j) ≠ v := by
      intro h
      exact hji (Fin.natAdd_injective _ _ (Fin.natAdd_injective _ _ h))
    rwa [Function.update_of_ne hne] at hjx
  · rintro ⟨j, hjB, hjx⟩
    obtain ⟨hji, hjB'⟩ := Finset.mem_erase.1 hjB
    have hne : Fin.natAdd n (Fin.natAdd (k + 1) j) ≠ v := by
      intro h
      exact hji (Fin.natAdd_injective _ _ (Fin.natAdd_injective _ _ h))
    exact ⟨j, hjB', by rw [Function.update_of_ne hne]; exact hjx⟩

private lemma sharedFun_dep_A {n k a : ℕ}
    (K : SimpleGraph (Fin (k + 1))) [DecidableRel K.Adj]
    (A : Finset (Fin (k + 1))) (B : Finset (Fin a))
    (g : (Fin n → Bool) → Bool → Bool)
    (hg_f : ∃ y : Fin n → Bool, g y false = false)
    (u : Fin (k + 1)) (hu : u ∈ A) :
    ∃ x : Fin (n + ((k + 1) + a)) → Bool,
      sharedFun K A B g (Function.update x (Fin.natAdd n (Fin.castAdd a u)) false) ≠
      sharedFun K A B g (Function.update x (Fin.natAdd n (Fin.castAdd a u)) true) := by
  obtain ⟨y₀, hy₀⟩ := hg_f
  set x0 := mkInput y₀ (fun _ => false) (fun _ => false) with hx0
  refine ⟨x0, ?_⟩
  have hupd0 : Function.update x0 (Fin.natAdd n (Fin.castAdd a u)) false = x0 := by
    funext j
    by_cases hj : j = Fin.natAdd n (Fin.castAdd a u)
    · subst hj; simp [hx0, mkInput_K]
    · rw [Function.update_of_ne hj]
  have h0 : sharedFun K A B g (Function.update x0 (Fin.natAdd n (Fin.castAdd a u)) false) =
      false := by
    rw [hupd0]
    simp only [sharedFun, hx0, mkInput_y, mkInput_K, mkInput_B, hy₀]
    simp
  have h1 : sharedFun K A B g (Function.update x0 (Fin.natAdd n (Fin.castAdd a u)) true) =
      true := by
    simp only [sharedFun]
    have ht : ∃ w ∈ A, Function.update x0 (Fin.natAdd n (Fin.castAdd a u)) true
        (Fin.natAdd n (Fin.castAdd a w)) = true := ⟨u, hu, by simp⟩
    simp [ht]
  rw [h0, h1]
  decide

private lemma sharedFun_update_A {n k a : ℕ}
    (K : SimpleGraph (Fin (k + 1))) [DecidableRel K.Adj]
    (A : Finset (Fin (k + 1))) (g : (Fin n → Bool) → Bool → Bool)
    (u : Fin (k + 1)) (hu0 : u ≠ 0) (hu_iso : ∀ w : Fin (k + 1), ¬ K.Adj u w) :
    (fun x => sharedFun K A ∅ g (Function.update x (Fin.natAdd n (Fin.castAdd a u)) false)) =
      sharedFun K (A.erase u) ∅ g := by
  funext x
  set v := Fin.natAdd n (Fin.castAdd a u) with hv
  have hy : (fun j : Fin n => Function.update x v false (Fin.castAdd ((k + 1) + a) j)) =
      (fun j : Fin n => x (Fin.castAdd ((k + 1) + a) j)) := by
    funext j
    exact Function.update_of_ne (fin_castAdd_ne_natAdd j _) _ _
  have h0 : Function.update x v false (Fin.natAdd n (Fin.castAdd a (0 : Fin (k + 1)))) =
      x (Fin.natAdd n (Fin.castAdd a (0 : Fin (k + 1)))) := by
    apply Function.update_of_ne
    intro h
    exact hu0 (Fin.castAdd_injective _ _ (Fin.natAdd_injective _ _ h)).symm
  have hKeq : (∃ a1 a2 : Fin (k + 1), K.Adj a1 a2 ∧
      Function.update x v false (Fin.natAdd n (Fin.castAdd a a1)) = true ∧
      Function.update x v false (Fin.natAdd n (Fin.castAdd a a2)) = true) ↔
      (∃ a1 a2 : Fin (k + 1), K.Adj a1 a2 ∧
      x (Fin.natAdd n (Fin.castAdd a a1)) = true ∧
      x (Fin.natAdd n (Fin.castAdd a a2)) = true) := by
    constructor <;> rintro ⟨a1, a2, hadj, h1, h2⟩
    · have ha1 : a1 ≠ u := fun h => hu_iso a2 (h ▸ hadj)
      have ha2 : a2 ≠ u := fun h => hu_iso a1 (h ▸ hadj.symm)
      have hne1 : Fin.natAdd n (Fin.castAdd a a1) ≠ v := fun h =>
        ha1 (Fin.castAdd_injective _ _ (Fin.natAdd_injective _ _ h))
      have hne2 : Fin.natAdd n (Fin.castAdd a a2) ≠ v := fun h =>
        ha2 (Fin.castAdd_injective _ _ (Fin.natAdd_injective _ _ h))
      rw [Function.update_of_ne hne1] at h1
      rw [Function.update_of_ne hne2] at h2
      exact ⟨a1, a2, hadj, h1, h2⟩
    · have ha1 : a1 ≠ u := fun h => hu_iso a2 (h ▸ hadj)
      have ha2 : a2 ≠ u := fun h => hu_iso a1 (h ▸ hadj.symm)
      have hne1 : Fin.natAdd n (Fin.castAdd a a1) ≠ v := fun h =>
        ha1 (Fin.castAdd_injective _ _ (Fin.natAdd_injective _ _ h))
      have hne2 : Fin.natAdd n (Fin.castAdd a a2) ≠ v := fun h =>
        ha2 (Fin.castAdd_injective _ _ (Fin.natAdd_injective _ _ h))
      exact ⟨a1, a2, hadj, by rw [Function.update_of_ne hne1]; exact h1,
        by rw [Function.update_of_ne hne2]; exact h2⟩
  have hAeq : (∃ w ∈ A, Function.update x v false (Fin.natAdd n (Fin.castAdd a w)) = true) ↔
      (∃ w ∈ A.erase u, x (Fin.natAdd n (Fin.castAdd a w)) = true) := by
    constructor
    · rintro ⟨w, hwA, hwx⟩
      have hwu : w ≠ u := by intro h; subst h; simp [hv] at hwx
      have hne : Fin.natAdd n (Fin.castAdd a w) ≠ v := fun h =>
        hwu (Fin.castAdd_injective _ _ (Fin.natAdd_injective _ _ h))
      rw [Function.update_of_ne hne] at hwx
      exact ⟨w, Finset.mem_erase.2 ⟨hwu, hwA⟩, hwx⟩
    · rintro ⟨w, hwA, hwx⟩
      obtain ⟨hwu, hwA'⟩ := Finset.mem_erase.1 hwA
      have hne : Fin.natAdd n (Fin.castAdd a w) ≠ v := fun h =>
        hwu (Fin.castAdd_injective _ _ (Fin.natAdd_injective _ _ h))
      exact ⟨w, hwA', by rw [Function.update_of_ne hne]; exact hwx⟩
  simp only [sharedFun, hy, h0, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.or_false]
  rw [decide_eq_decide.2 hKeq, decide_eq_decide.2 hAeq]

private lemma sharedFun_dep_leaf_nonroot {n k a : ℕ}
    (K : SimpleGraph (Fin (k + 1))) [DecidableRel K.Adj]
    (g : (Fin n → Bool) → Bool → Bool)
    (hg_f : ∃ y : Fin n → Bool, g y false = false)
    (ℓ p : Fin (k + 1)) (hp0 : p ≠ 0) (hlp : K.Adj ℓ p) :
    ∃ x : Fin (n + ((k + 1) + a)) → Bool,
      sharedFun K ∅ ∅ g (Function.update x (Fin.natAdd n (Fin.castAdd a ℓ)) false) ≠
      sharedFun K ∅ ∅ g (Function.update x (Fin.natAdd n (Fin.castAdd a ℓ)) true) := by
  obtain ⟨y₀, hy₀⟩ := hg_f
  set x0 := mkInput y₀ (fun i : Fin (k + 1) => decide (i = p)) (fun _ => false) with hx0
  refine ⟨x0, ?_⟩
  have hpneℓ : Fin.natAdd n (Fin.castAdd a p) ≠ Fin.natAdd n (Fin.castAdd a ℓ) := fun h =>
    hlp.ne.symm (Fin.castAdd_injective _ _ (Fin.natAdd_injective _ _ h))
  have hupd0 : Function.update x0 (Fin.natAdd n (Fin.castAdd a ℓ)) false = x0 := by
    funext j
    by_cases hj : j = Fin.natAdd n (Fin.castAdd a ℓ)
    · subst hj; simp [hx0, mkInput_K, hlp.ne]
    · rw [Function.update_of_ne hj]
  have h0 : sharedFun K ∅ ∅ g (Function.update x0 (Fin.natAdd n (Fin.castAdd a ℓ)) false) =
      false := by
    rw [hupd0]
    simp only [sharedFun, hx0, mkInput_y, mkInput_K, mkInput_B, Finset.notMem_empty,
      false_and, exists_false, decide_false, Bool.or_false]
    have h0p : decide ((0 : Fin (k + 1)) = p) = false := decide_eq_false hp0.symm
    simp [h0p, hy₀]
  have h1 : sharedFun K ∅ ∅ g (Function.update x0 (Fin.natAdd n (Fin.castAdd a ℓ)) true) =
      true := by
    simp only [sharedFun]
    have ht : ∃ u w : Fin (k + 1), K.Adj u w ∧
        Function.update x0 (Fin.natAdd n (Fin.castAdd a ℓ)) true
          (Fin.natAdd n (Fin.castAdd a u)) = true ∧
        Function.update x0 (Fin.natAdd n (Fin.castAdd a ℓ)) true
          (Fin.natAdd n (Fin.castAdd a w)) = true := by
      refine ⟨ℓ, p, hlp, by simp, ?_⟩
      rw [Function.update_of_ne hpneℓ]
      simp [hx0, mkInput_K]
    simp [ht]
  rw [h0, h1]
  decide

private lemma sharedFun_dep_leaf_root {n k a : ℕ}
    (K : SimpleGraph (Fin (k + 1))) [DecidableRel K.Adj]
    (g : (Fin n → Bool) → Bool → Bool)
    (hg_t : ∃ y : Fin n → Bool, g y true = false)
    (w : Fin (k + 1)) (h0w : K.Adj 0 w) :
    ∃ x : Fin (n + ((k + 1) + a)) → Bool,
      sharedFun K ∅ ∅ g (Function.update x (Fin.natAdd n (Fin.castAdd a w)) false) ≠
      sharedFun K ∅ ∅ g (Function.update x (Fin.natAdd n (Fin.castAdd a w)) true) := by
  obtain ⟨y₁, hy₁⟩ := hg_t
  set x0 := mkInput y₁ (fun i : Fin (k + 1) => decide (i = 0)) (fun _ => false) with hx0
  refine ⟨x0, ?_⟩
  have h0new : Fin.natAdd n (Fin.castAdd a (0 : Fin (k + 1))) ≠ Fin.natAdd n (Fin.castAdd a w) :=
    fun h => h0w.ne (Fin.castAdd_injective _ _ (Fin.natAdd_injective _ _ h))
  have hupd0 : Function.update x0 (Fin.natAdd n (Fin.castAdd a w)) false = x0 := by
    funext j
    by_cases hj : j = Fin.natAdd n (Fin.castAdd a w)
    · subst hj; simp [hx0, mkInput_K, h0w.ne.symm]
    · rw [Function.update_of_ne hj]
  have h0 : sharedFun K ∅ ∅ g (Function.update x0 (Fin.natAdd n (Fin.castAdd a w)) false) =
      false := by
    rw [hupd0]
    simp only [sharedFun, hx0, mkInput_y, mkInput_K, mkInput_B, Finset.notMem_empty,
      false_and, exists_false, decide_false, Bool.or_false]
    simp [hy₁]
  have h1 : sharedFun K ∅ ∅ g (Function.update x0 (Fin.natAdd n (Fin.castAdd a w)) true) =
      true := by
    simp only [sharedFun]
    have ht : ∃ u v : Fin (k + 1), K.Adj u v ∧
        Function.update x0 (Fin.natAdd n (Fin.castAdd a w)) true
          (Fin.natAdd n (Fin.castAdd a u)) = true ∧
        Function.update x0 (Fin.natAdd n (Fin.castAdd a w)) true
          (Fin.natAdd n (Fin.castAdd a v)) = true := by
      refine ⟨0, w, h0w, ?_, by simp⟩
      rw [Function.update_of_ne h0new]
      simp [hx0, mkInput_K]
    simp [ht]
  rw [h0, h1]
  decide

private lemma sharedFun_update_leaf_false {n k a : ℕ}
    (K : SimpleGraph (Fin (k + 1))) [DecidableRel K.Adj]
    (g : (Fin n → Bool) → Bool → Bool) (ℓ p : Fin (k + 1)) (hℓ0 : ℓ ≠ 0)
    (hleaf : ∀ w, K.Adj ℓ w → w = p)
    [DecidableRel (K.deleteEdges {s(ℓ, p)}).Adj] :
    (fun x => sharedFun K ∅ ∅ g (Function.update x (Fin.natAdd n (Fin.castAdd a ℓ)) false)) =
      sharedFun (K.deleteEdges {s(ℓ, p)}) ∅ ∅ g := by
  funext x
  set v := Fin.natAdd n (Fin.castAdd a ℓ) with hv
  have hy : (fun j : Fin n => Function.update x v false (Fin.castAdd ((k + 1) + a) j)) =
      (fun j : Fin n => x (Fin.castAdd ((k + 1) + a) j)) := by
    funext j
    exact Function.update_of_ne (fin_castAdd_ne_natAdd j _) _ _
  have h0 : Function.update x v false (Fin.natAdd n (Fin.castAdd a (0 : Fin (k + 1)))) =
      x (Fin.natAdd n (Fin.castAdd a (0 : Fin (k + 1)))) := by
    apply Function.update_of_ne
    intro h
    exact hℓ0 (Fin.castAdd_injective _ _ (Fin.natAdd_injective _ _ h)).symm
  simp only [sharedFun, hy, h0, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.or_false]
  congr 1
  apply decide_eq_decide.2
  constructor
  · rintro ⟨u, w, huw, hux, hwx⟩
    have huℓ : u ≠ ℓ := by intro h; subst h; simp [hv] at hux
    have hwℓ : w ≠ ℓ := by intro h; subst h; simp [hv] at hwx
    have hne1 : Fin.natAdd n (Fin.castAdd a u) ≠ v := fun h =>
      huℓ (Fin.castAdd_injective _ _ (Fin.natAdd_injective _ _ h))
    have hne2 : Fin.natAdd n (Fin.castAdd a w) ≠ v := fun h =>
      hwℓ (Fin.castAdd_injective _ _ (Fin.natAdd_injective _ _ h))
    rw [Function.update_of_ne hne1] at hux
    rw [Function.update_of_ne hne2] at hwx
    refine ⟨u, w, SimpleGraph.deleteEdges_adj.2 ⟨huw, ?_⟩, hux, hwx⟩
    intro heq
    simp only [Set.mem_singleton_iff, Sym2.eq_iff] at heq
    rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact huℓ rfl
    · exact hwℓ rfl
  · rintro ⟨u, w, hadj, hux, hwx⟩
    obtain ⟨huw, hne⟩ := SimpleGraph.deleteEdges_adj.1 hadj
    simp only [Set.mem_singleton_iff] at hne
    have huℓ : u ≠ ℓ := by
      intro h; subst h
      have hw_eq : w = p := hleaf w huw
      subst hw_eq
      exact hne rfl
    have hwℓ : w ≠ ℓ := by
      intro h; subst h
      have hu_eq : u = p := hleaf u huw.symm
      subst hu_eq
      exact hne Sym2.eq_swap
    have hne1 : Fin.natAdd n (Fin.castAdd a u) ≠ v := fun h =>
      huℓ (Fin.castAdd_injective _ _ (Fin.natAdd_injective _ _ h))
    have hne2 : Fin.natAdd n (Fin.castAdd a w) ≠ v := fun h =>
      hwℓ (Fin.castAdd_injective _ _ (Fin.natAdd_injective _ _ h))
    exact ⟨u, w, huw, by rw [Function.update_of_ne hne1]; exact hux,
      by rw [Function.update_of_ne hne2]; exact hwx⟩

private lemma sharedFun_update_leaf_true {n k a : ℕ}
    (K : SimpleGraph (Fin (k + 1))) [DecidableRel K.Adj]
    (g : (Fin n → Bool) → Bool → Bool) (ℓ p : Fin (k + 1)) (hℓ0 : ℓ ≠ 0)
    (hlp : K.Adj ℓ p) (hleaf : ∀ w, K.Adj ℓ w → w = p)
    [DecidableRel (deleteVertexEdges K p).Adj] :
    (fun x => sharedFun K ∅ ∅ g (Function.update x (Fin.natAdd n (Fin.castAdd a ℓ)) true)) =
      sharedFun (deleteVertexEdges K p) {p} ∅ g := by
  funext x
  set v := Fin.natAdd n (Fin.castAdd a ℓ) with hv
  have hy : (fun j : Fin n => Function.update x v true (Fin.castAdd ((k + 1) + a) j)) =
      (fun j : Fin n => x (Fin.castAdd ((k + 1) + a) j)) := by
    funext j
    exact Function.update_of_ne (fin_castAdd_ne_natAdd j _) _ _
  have h0 : Function.update x v true (Fin.natAdd n (Fin.castAdd a (0 : Fin (k + 1)))) =
      x (Fin.natAdd n (Fin.castAdd a (0 : Fin (k + 1)))) := by
    apply Function.update_of_ne
    intro h
    exact hℓ0 (Fin.castAdd_injective _ _ (Fin.natAdd_injective _ _ h)).symm
  have hpneℓ : Fin.natAdd n (Fin.castAdd a p) ≠ v := fun h =>
    hlp.ne.symm (Fin.castAdd_injective _ _ (Fin.natAdd_injective _ _ h))
  simp only [sharedFun, hy, h0, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.or_false, Finset.mem_singleton, exists_eq_left]
  rw [Bool.or_assoc]
  congr 1
  apply Bool.eq_iff_iff.2
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨u, w, huw, hux, hwx⟩
    by_cases hup : u = p
    · subst hup
      rw [Function.update_of_ne hpneℓ] at hux
      exact Or.inr hux
    · by_cases hwp : w = p
      · subst hwp
        rw [Function.update_of_ne hpneℓ] at hwx
        exact Or.inr hwx
      · left
        have huℓ : u ≠ ℓ := fun h => hwp (hleaf w (h ▸ huw))
        have hwℓ : w ≠ ℓ := fun h => hup (hleaf u (h ▸ huw.symm))
        have hne1 : Fin.natAdd n (Fin.castAdd a u) ≠ v := fun h =>
          huℓ (Fin.castAdd_injective _ _ (Fin.natAdd_injective _ _ h))
        have hne2 : Fin.natAdd n (Fin.castAdd a w) ≠ v := fun h =>
          hwℓ (Fin.castAdd_injective _ _ (Fin.natAdd_injective _ _ h))
        rw [Function.update_of_ne hne1] at hux
        rw [Function.update_of_ne hne2] at hwx
        exact ⟨u, w, ⟨huw, hup, hwp⟩, hux, hwx⟩
  · rintro (⟨u, w, ⟨huw, hup, hwp⟩, hux, hwx⟩ | hpx)
    · have huℓ : u ≠ ℓ := fun h => hwp (hleaf w (h ▸ huw))
      have hwℓ : w ≠ ℓ := fun h => hup (hleaf u (h ▸ huw.symm))
      have hne1 : Fin.natAdd n (Fin.castAdd a u) ≠ v := fun h =>
        huℓ (Fin.castAdd_injective _ _ (Fin.natAdd_injective _ _ h))
      have hne2 : Fin.natAdd n (Fin.castAdd a w) ≠ v := fun h =>
        hwℓ (Fin.castAdd_injective _ _ (Fin.natAdd_injective _ _ h))
      exact ⟨u, w, huw, by rw [Function.update_of_ne hne1]; exact hux,
        by rw [Function.update_of_ne hne2]; exact hwx⟩
    · exact ⟨ℓ, p, hlp, by simp [hv], by rw [Function.update_of_ne hpneℓ]; exact hpx⟩

private lemma lower_bound_shared {n k a : ℕ} (g : (Fin n → Bool) → Bool → Bool)
    (hg_nc : ∃ (y y' : Fin n → Bool) (b b' : Bool), g y b ≠ g y' b')
    (hg_f : ∃ y : Fin n → Bool, g y false = false)
    (hg_t : ∃ y : Fin n → Bool, g y true = false) :
    ∀ (s : ℕ) (K : SimpleGraph (Fin (k + 1))) [DecidableRel K.Adj]
      (A : Finset (Fin (k + 1))) (B : Finset (Fin a)),
      K.IsAcyclic →
      (0 : Fin (k + 1)) ∉ A →
      (∀ u ∈ A, ∀ w : Fin (k + 1), ¬ K.Adj u w) →
      HasCircuitSize (n + ((k + 1) + a)) (sharedFun K A B g) s →
      (∃ (S : Finset (Fin (k + 1))) (c : ℕ),
        IsVC K S ∧ (0 : Fin (k + 1)) ∉ S ∧ HasCircuitSize (n + 1) (gFlat g) c ∧
        B.card + A.card + K.edgeFinset.card + c + S.card ≤ s) ∨
      (∃ (S : Finset (Fin (k + 1))) (q : ℕ),
        IsVC K S ∧ (0 : Fin (k + 1)) ∈ S ∧ HasCircuitSize (n + 1 + 1) (gStar g) q ∧
        B.card + A.card + K.edgeFinset.card + q + S.card ≤ s + 2) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro K _ A B hAcyc h0A hA_iso hC
    by_cases hBne : B.Nonempty
    · obtain ⟨i, hi⟩ := hBne
      have hdep := sharedFun_dep_B K A B g hg_f i hi
      have hrew := sharedFun_update_B K A B g i
      have hnc : ∃ x x',
          sharedFun K A B g (Function.update x (Fin.natAdd n (Fin.natAdd (k + 1) i)) false) ≠
          sharedFun K A B g (Function.update x' (Fin.natAdd n (Fin.natAdd (k + 1) i)) false) := by
        obtain ⟨x, x', hne⟩ := sharedFun_nonconst K A (B.erase i) g h0A hg_nc
        exact ⟨x, x', by rw [congrFun hrew x, congrFun hrew x']; exact hne⟩
      obtain ⟨hs1, hC'⟩ := elim_one_var (Fin.natAdd n (Fin.natAdd (k + 1) i)) false hC hdep hnc
      rw [hrew] at hC'
      have hcard : (B.erase i).card + 1 = B.card := by
        have hpos : 1 ≤ B.card := Finset.one_le_card.2 ⟨i, hi⟩
        rw [Finset.card_erase_of_mem hi]; omega
      rcases ih (s - 1) (by omega) K A (B.erase i) hAcyc h0A hA_iso hC' with
        ⟨S, c, hvc, h0S, hc, hle⟩ | ⟨S, q, hvc, h0S, hq, hle⟩
      · exact Or.inl ⟨S, c, hvc, h0S, hc, by omega⟩
      · exact Or.inr ⟨S, q, hvc, h0S, hq, by omega⟩
    · have hBempty : B = ∅ := Finset.not_nonempty_iff_eq_empty.1 hBne
      subst hBempty
      by_cases hAne : A.Nonempty
      · obtain ⟨u, hu⟩ := hAne
        have hu0 : u ≠ 0 := fun h => h0A (h ▸ hu)
        have hdep := sharedFun_dep_A K A (∅ : Finset (Fin a)) g hg_f u hu
        have hrew := sharedFun_update_A (a := a) K A g u hu0 (hA_iso u hu)
        have h0A' : (0 : Fin (k + 1)) ∉ A.erase u := fun h => h0A (Finset.mem_of_mem_erase h)
        have hnc : ∃ x x',
            sharedFun K A ∅ g (Function.update x (Fin.natAdd n (Fin.castAdd a u)) false) ≠
            sharedFun K A ∅ g (Function.update x' (Fin.natAdd n (Fin.castAdd a u)) false) := by
          obtain ⟨x, x', hne⟩ := sharedFun_nonconst K (A.erase u) (∅ : Finset (Fin a)) g h0A' hg_nc
          exact ⟨x, x', by rw [congrFun hrew x, congrFun hrew x']; exact hne⟩
        obtain ⟨hs1, hC'⟩ := elim_one_var (Fin.natAdd n (Fin.castAdd a u)) false hC hdep hnc
        rw [hrew] at hC'
        have hcard : (A.erase u).card + 1 = A.card := by
          have hpos : 1 ≤ A.card := Finset.one_le_card.2 ⟨u, hu⟩
          rw [Finset.card_erase_of_mem hu]; omega
        rcases ih (s - 1) (by omega) K (A.erase u) ∅ hAcyc h0A'
            (fun w hw => hA_iso w (Finset.mem_of_mem_erase hw)) hC' with
          ⟨S, c, hvc, h0S, hc, hle⟩ | ⟨S, q, hvc, h0S, hq, hle⟩
        · exact Or.inl ⟨S, c, hvc, h0S, hc, by omega⟩
        · exact Or.inr ⟨S, q, hvc, h0S, hq, by omega⟩
      · have hAempty : A = ∅ := Finset.not_nonempty_iff_eq_empty.1 hAne
        subst hAempty
        by_cases hNonRoot : ∃ u v : Fin (k + 1), K.Adj u v ∧ u ≠ 0 ∧ v ≠ 0
        · obtain ⟨ℓ, p, hℓ0, hp0, hlp, hleaf, hcases⟩ :=
            acyclic_nonroot_leaf_cases K hAcyc hNonRoot
          rcases hcases with ⟨ℓ', hℓ'ne, hℓ'0, hℓ'p, hℓ'leaf⟩ | hpdeg1 | ⟨q, hqne, hpq, hpdeg2⟩
          · classical
            have hdep := sharedFun_dep_leaf_nonroot (a := a) K g hg_f ℓ p hp0 hlp
            have hrew := sharedFun_update_leaf_false (a := a) K g ℓ p hℓ0 hleaf
            have hnc : ∃ x x',
                sharedFun K ∅ ∅ g (Function.update x (Fin.natAdd n (Fin.castAdd a ℓ)) false) ≠
                sharedFun K ∅ ∅ g (Function.update x' (Fin.natAdd n (Fin.castAdd a ℓ)) false) := by
              obtain ⟨x, x', hne⟩ := sharedFun_nonconst (K.deleteEdges {s(ℓ, p)}) ∅ (∅ : Finset (Fin a)) g
                (by simp) hg_nc
              exact ⟨x, x', by rw [congrFun hrew x, congrFun hrew x']; exact hne⟩
            obtain ⟨hs1, hC'⟩ := elim_one_var (Fin.natAdd n (Fin.castAdd a ℓ)) false hC hdep hnc
            rw [hrew] at hC'
            have hedge := edgeFinset_card_deleteEdge K ℓ p hlp
            rcases ih (s - 1) (by omega) (K.deleteEdges {s(ℓ, p)}) ∅ ∅
                (hAcyc.anti (SimpleGraph.deleteEdges_le _)) (by simp) (by simp) hC' with
              ⟨S', c, hvc', h0S', hc, hle⟩ | ⟨S', q', hvc', h0S', hq', hle⟩
            · by_cases hpS' : p ∈ S'
              · have hvc : IsVC K S' := by
                  intro u v huv
                  by_cases hmem : s(u, v) = s(ℓ, p)
                  · rw [Sym2.eq_iff] at hmem
                    rcases hmem with ⟨_, rfl⟩ | ⟨rfl, _⟩
                    · exact Or.inr hpS'
                    · exact Or.inl hpS'
                  · exact hvc' u v (SimpleGraph.deleteEdges_adj.2 ⟨huv, by simpa using hmem⟩)
                refine Or.inl ⟨S', c, hvc, h0S', hc, ?_⟩
                simp only [Finset.card_empty, zero_add] at hle ⊢
                omega
              · have hℓ'in : ℓ' ∈ S' := by
                  have hne_e : s(ℓ', p) ≠ s(ℓ, p) := by
                    intro he
                    rw [Sym2.eq_iff] at he
                    rcases he with ⟨h1, _⟩ | ⟨h1, _⟩
                    · exact hℓ'ne h1
                    · exact hℓ'p.ne h1
                  rcases hvc' ℓ' p (SimpleGraph.deleteEdges_adj.2 ⟨hℓ'p, by simpa using hne_e⟩) with
                    h | h
                  · exact h
                  · exact absurd h hpS'
                set S := insert p (S'.erase ℓ')
                have hvc : IsVC K S := by
                  intro u v huv
                  by_cases hmem : s(u, v) = s(ℓ, p)
                  · rw [Sym2.eq_iff] at hmem
                    rcases hmem with ⟨_, hvp⟩ | ⟨hup, _⟩
                    · exact Or.inr (hvp ▸ Finset.mem_insert_self p _)
                    · exact Or.inl (hup ▸ Finset.mem_insert_self p _)
                  · rcases hvc' u v (SimpleGraph.deleteEdges_adj.2 ⟨huv, by simpa using hmem⟩) with
                      hu | hv
                    · by_cases huℓ' : u = ℓ'
                      · subst huℓ'
                        have hv_eq : v = p := hℓ'leaf v huv
                        exact Or.inr (hv_eq ▸ Finset.mem_insert_self p _)
                      · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨huℓ', hu⟩))
                    · by_cases hvℓ' : v = ℓ'
                      · subst hvℓ'
                        have hu_eq : u = p := hℓ'leaf u huv.symm
                        exact Or.inl (hu_eq ▸ Finset.mem_insert_self p _)
                      · exact Or.inr (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hvℓ', hv⟩))
                have h0S : (0 : Fin (k + 1)) ∉ S := by
                  simp only [S, Finset.mem_insert, Finset.mem_erase, not_or]
                  exact ⟨hp0.symm, fun h => h0S' h.2⟩
                have hcard : S.card = S'.card := by
                  have hp_not : p ∉ S'.erase ℓ' := fun h => hpS' (Finset.mem_of_mem_erase h)
                  rw [Finset.card_insert_of_notMem hp_not, Finset.card_erase_of_mem hℓ'in]
                  have hpos : 1 ≤ S'.card := Finset.one_le_card.2 ⟨ℓ', hℓ'in⟩
                  omega
                refine Or.inl ⟨S, c, hvc, h0S, hc, ?_⟩
                simp only [Finset.card_empty, zero_add] at hle ⊢
                omega
            · by_cases hpS' : p ∈ S'
              · have hvc : IsVC K S' := by
                  intro u v huv
                  by_cases hmem : s(u, v) = s(ℓ, p)
                  · rw [Sym2.eq_iff] at hmem
                    rcases hmem with ⟨_, rfl⟩ | ⟨rfl, _⟩
                    · exact Or.inr hpS'
                    · exact Or.inl hpS'
                  · exact hvc' u v (SimpleGraph.deleteEdges_adj.2 ⟨huv, by simpa using hmem⟩)
                refine Or.inr ⟨S', q', hvc, h0S', hq', ?_⟩
                simp only [Finset.card_empty, zero_add] at hle ⊢
                omega
              · have hℓ'in : ℓ' ∈ S' := by
                  have hne_e : s(ℓ', p) ≠ s(ℓ, p) := by
                    intro he
                    rw [Sym2.eq_iff] at he
                    rcases he with ⟨h1, _⟩ | ⟨h1, _⟩
                    · exact hℓ'ne h1
                    · exact hℓ'p.ne h1
                  rcases hvc' ℓ' p (SimpleGraph.deleteEdges_adj.2 ⟨hℓ'p, by simpa using hne_e⟩) with
                    h | h
                  · exact h
                  · exact absurd h hpS'
                set S := insert p (S'.erase ℓ')
                have hvc : IsVC K S := by
                  intro u v huv
                  by_cases hmem : s(u, v) = s(ℓ, p)
                  · rw [Sym2.eq_iff] at hmem
                    rcases hmem with ⟨_, hvp⟩ | ⟨hup, _⟩
                    · exact Or.inr (hvp ▸ Finset.mem_insert_self p _)
                    · exact Or.inl (hup ▸ Finset.mem_insert_self p _)
                  · rcases hvc' u v (SimpleGraph.deleteEdges_adj.2 ⟨huv, by simpa using hmem⟩) with
                      hu | hv
                    · by_cases huℓ' : u = ℓ'
                      · subst huℓ'
                        have hv_eq : v = p := hℓ'leaf v huv
                        exact Or.inr (hv_eq ▸ Finset.mem_insert_self p _)
                      · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨huℓ', hu⟩))
                    · by_cases hvℓ' : v = ℓ'
                      · subst hvℓ'
                        have hu_eq : u = p := hℓ'leaf u huv.symm
                        exact Or.inl (hu_eq ▸ Finset.mem_insert_self p _)
                      · exact Or.inr (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hvℓ', hv⟩))
                have h0S : (0 : Fin (k + 1)) ∈ S :=
                  Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hℓ'0.symm, h0S'⟩)
                have hcard : S.card = S'.card := by
                  have hp_not : p ∉ S'.erase ℓ' := fun h => hpS' (Finset.mem_of_mem_erase h)
                  rw [Finset.card_insert_of_notMem hp_not, Finset.card_erase_of_mem hℓ'in]
                  have hpos : 1 ≤ S'.card := Finset.one_le_card.2 ⟨ℓ', hℓ'in⟩
                  omega
                refine Or.inr ⟨S, q', hvc, h0S, hq', ?_⟩
                simp only [Finset.card_empty, zero_add] at hle ⊢
                omega
          · classical
            have hdep := sharedFun_dep_leaf_nonroot (a := a) K g hg_f ℓ p hp0 hlp
            have hrew := sharedFun_update_leaf_true (a := a) K g ℓ p hℓ0 hlp hleaf
            have h0p : (0 : Fin (k + 1)) ∉ ({p} : Finset (Fin (k + 1))) := by
              simp [hp0.symm]
            have hnc : ∃ x x',
                sharedFun K ∅ ∅ g (Function.update x (Fin.natAdd n (Fin.castAdd a ℓ)) true) ≠
                sharedFun K ∅ ∅ g (Function.update x' (Fin.natAdd n (Fin.castAdd a ℓ)) true) := by
              obtain ⟨x, x', hne⟩ := sharedFun_nonconst (deleteVertexEdges K p) {p} (∅ : Finset (Fin a)) g h0p hg_nc
              exact ⟨x, x', by rw [congrFun hrew x, congrFun hrew x']; exact hne⟩
            obtain ⟨hs1, hC'⟩ := elim_one_var (Fin.natAdd n (Fin.castAdd a ℓ)) true hC hdep hnc
            rw [hrew] at hC'
            have hedge := edgeFinset_card_deleteVertex_deg1 K ℓ p hlp hpdeg1
            rcases ih (s - 1) (by omega) (deleteVertexEdges K p) {p} ∅
                (hAcyc.anti (deleteVertexEdges_le K p)) h0p
                (by intro u hu w h; simp at hu; subst hu; exact h.2.1 rfl) hC' with
              ⟨S', c, hvc', h0S', hc, hle⟩ | ⟨S', q', hvc', h0S', hq', hle⟩
            · have hvc : IsVC K (insert p S') := by
                intro u v huv
                by_cases hup : u = p
                · exact Or.inl (hup ▸ Finset.mem_insert_self p S')
                · by_cases hvp : v = p
                  · exact Or.inr (hvp ▸ Finset.mem_insert_self p S')
                  · rcases hvc' u v ⟨huv, hup, hvp⟩ with hu | hv
                    · exact Or.inl (Finset.mem_insert_of_mem hu)
                    · exact Or.inr (Finset.mem_insert_of_mem hv)
              have h0S : (0 : Fin (k + 1)) ∉ insert p S' := by
                simp only [Finset.mem_insert, not_or]; exact ⟨hp0.symm, h0S'⟩
              have hcard : (insert p S').card ≤ S'.card + 1 := Finset.card_insert_le p S'
              refine Or.inl ⟨insert p S', c, hvc, h0S, hc, ?_⟩
              simp only [Finset.card_empty, Finset.card_singleton, zero_add] at hle ⊢
              omega
            · have hvc : IsVC K (insert p S') := by
                intro u v huv
                by_cases hup : u = p
                · exact Or.inl (hup ▸ Finset.mem_insert_self p S')
                · by_cases hvp : v = p
                  · exact Or.inr (hvp ▸ Finset.mem_insert_self p S')
                  · rcases hvc' u v ⟨huv, hup, hvp⟩ with hu | hv
                    · exact Or.inl (Finset.mem_insert_of_mem hu)
                    · exact Or.inr (Finset.mem_insert_of_mem hv)
              have h0S : (0 : Fin (k + 1)) ∈ insert p S' := Finset.mem_insert_of_mem h0S'
              have hcard : (insert p S').card ≤ S'.card + 1 := Finset.card_insert_le p S'
              refine Or.inr ⟨insert p S', q', hvc, h0S, hq', ?_⟩
              simp only [Finset.card_empty, Finset.card_singleton, zero_add] at hle ⊢
              omega
          · classical
            have hdep := sharedFun_dep_leaf_nonroot (a := a) K g hg_f ℓ p hp0 hlp
            have hrew0 := sharedFun_update_leaf_false (a := a) K g ℓ p hℓ0 hleaf
            have hrew1 := sharedFun_update_leaf_true (a := a) K g ℓ p hℓ0 hlp hleaf
            have h0p : (0 : Fin (k + 1)) ∉ ({p} : Finset (Fin (k + 1))) := by
              simp [hp0.symm]
            have hnc0 : ∃ x x',
                sharedFun K ∅ ∅ g (Function.update x (Fin.natAdd n (Fin.castAdd a ℓ)) false) ≠
                sharedFun K ∅ ∅ g (Function.update x' (Fin.natAdd n (Fin.castAdd a ℓ)) false) := by
              obtain ⟨x, x', hne⟩ := sharedFun_nonconst (K.deleteEdges {s(ℓ, p)}) ∅ (∅ : Finset (Fin a)) g
                (by simp) hg_nc
              exact ⟨x, x', by rw [congrFun hrew0 x, congrFun hrew0 x']; exact hne⟩
            have hnc1 : ∃ x x',
                sharedFun K ∅ ∅ g (Function.update x (Fin.natAdd n (Fin.castAdd a ℓ)) true) ≠
                sharedFun K ∅ ∅ g (Function.update x' (Fin.natAdd n (Fin.castAdd a ℓ)) true) := by
              obtain ⟨x, x', hne⟩ := sharedFun_nonconst (deleteVertexEdges K p) {p} (∅ : Finset (Fin a)) g h0p hg_nc
              exact ⟨x, x', by rw [congrFun hrew1 x, congrFun hrew1 x']; exact hne⟩
            obtain ⟨hs2, hC0 | hC1⟩ :=
              elim_two_var (Fin.natAdd n (Fin.castAdd a ℓ)) hC hdep hnc0 hnc1
            · rw [hrew0] at hC0
              have hedge := edgeFinset_card_deleteEdge K ℓ p hlp
              rcases ih (s - 2) (by omega) (K.deleteEdges {s(ℓ, p)}) ∅ ∅
                  (hAcyc.anti (SimpleGraph.deleteEdges_le _)) (by simp) (by simp) hC0 with
                ⟨S', c, hvc', h0S', hc, hle⟩ | ⟨S', q', hvc', h0S', hq', hle⟩
              · have hvc : IsVC K (insert p S') := by
                  intro u v huv
                  by_cases hmem : s(u, v) = s(ℓ, p)
                  · rw [Sym2.eq_iff] at hmem
                    rcases hmem with ⟨_, hvp⟩ | ⟨hup, _⟩
                    · exact Or.inr (hvp ▸ Finset.mem_insert_self p S')
                    · exact Or.inl (hup ▸ Finset.mem_insert_self p S')
                  · rcases hvc' u v (SimpleGraph.deleteEdges_adj.2 ⟨huv, by simpa using hmem⟩) with
                      hu | hv
                    · exact Or.inl (Finset.mem_insert_of_mem hu)
                    · exact Or.inr (Finset.mem_insert_of_mem hv)
                have h0S : (0 : Fin (k + 1)) ∉ insert p S' := by
                  simp only [Finset.mem_insert, not_or]; exact ⟨hp0.symm, h0S'⟩
                have hcard : (insert p S').card ≤ S'.card + 1 := Finset.card_insert_le p S'
                refine Or.inl ⟨insert p S', c, hvc, h0S, hc, ?_⟩
                simp only [Finset.card_empty, zero_add] at hle ⊢
                omega
              · have hvc : IsVC K (insert p S') := by
                  intro u v huv
                  by_cases hmem : s(u, v) = s(ℓ, p)
                  · rw [Sym2.eq_iff] at hmem
                    rcases hmem with ⟨_, hvp⟩ | ⟨hup, _⟩
                    · exact Or.inr (hvp ▸ Finset.mem_insert_self p S')
                    · exact Or.inl (hup ▸ Finset.mem_insert_self p S')
                  · rcases hvc' u v (SimpleGraph.deleteEdges_adj.2 ⟨huv, by simpa using hmem⟩) with
                      hu | hv
                    · exact Or.inl (Finset.mem_insert_of_mem hu)
                    · exact Or.inr (Finset.mem_insert_of_mem hv)
                have h0S : (0 : Fin (k + 1)) ∈ insert p S' := Finset.mem_insert_of_mem h0S'
                have hcard : (insert p S').card ≤ S'.card + 1 := Finset.card_insert_le p S'
                refine Or.inr ⟨insert p S', q', hvc, h0S, hq', ?_⟩
                simp only [Finset.card_empty, zero_add] at hle ⊢
                omega
            · rw [hrew1] at hC1
              have hedge := edgeFinset_card_deleteVertex_deg2 K ℓ p q hlp hpq hqne hpdeg2
              rcases ih (s - 2) (by omega) (deleteVertexEdges K p) {p} ∅
                  (hAcyc.anti (deleteVertexEdges_le K p)) h0p
                  (by intro u hu w h; simp at hu; subst hu; exact h.2.1 rfl) hC1 with
                ⟨S', c, hvc', h0S', hc, hle⟩ | ⟨S', q', hvc', h0S', hq', hle⟩
              · have hvc : IsVC K (insert p S') := by
                  intro u v huv
                  by_cases hup : u = p
                  · exact Or.inl (hup ▸ Finset.mem_insert_self p S')
                  · by_cases hvp : v = p
                    · exact Or.inr (hvp ▸ Finset.mem_insert_self p S')
                    · rcases hvc' u v ⟨huv, hup, hvp⟩ with hu | hv
                      · exact Or.inl (Finset.mem_insert_of_mem hu)
                      · exact Or.inr (Finset.mem_insert_of_mem hv)
                have h0S : (0 : Fin (k + 1)) ∉ insert p S' := by
                  simp only [Finset.mem_insert, not_or]; exact ⟨hp0.symm, h0S'⟩
                have hcard : (insert p S').card ≤ S'.card + 1 := Finset.card_insert_le p S'
                refine Or.inl ⟨insert p S', c, hvc, h0S, hc, ?_⟩
                simp only [Finset.card_empty, Finset.card_singleton, zero_add] at hle ⊢
                omega
              · have hvc : IsVC K (insert p S') := by
                  intro u v huv
                  by_cases hup : u = p
                  · exact Or.inl (hup ▸ Finset.mem_insert_self p S')
                  · by_cases hvp : v = p
                    · exact Or.inr (hvp ▸ Finset.mem_insert_self p S')
                    · rcases hvc' u v ⟨huv, hup, hvp⟩ with hu | hv
                      · exact Or.inl (Finset.mem_insert_of_mem hu)
                      · exact Or.inr (Finset.mem_insert_of_mem hv)
                have h0S : (0 : Fin (k + 1)) ∈ insert p S' := Finset.mem_insert_of_mem h0S'
                have hcard : (insert p S').card ≤ S'.card + 1 := Finset.card_insert_le p S'
                refine Or.inr ⟨insert p S', q', hvc, h0S, hq', ?_⟩
                simp only [Finset.card_empty, Finset.card_singleton, zero_add] at hle ⊢
                omega
        · have hstar : ∀ u v : Fin (k + 1), K.Adj u v → u = 0 ∨ v = 0 := by
            intro u v huv
            by_contra h
            push Not at h
            exact hNonRoot ⟨u, v, huv, h.1, h.2⟩
          by_cases hhas0 : ∃ w : Fin (k + 1), K.Adj 0 w
          · obtain ⟨w₁, h0w₁⟩ := hhas0
            by_cases htwo : ∃ w₂ : Fin (k + 1), w₂ ≠ w₁ ∧ K.Adj 0 w₂
            · classical
              obtain ⟨w₂, hw₂ne, h0w₂⟩ := htwo
              have hw₁0 : w₁ ≠ 0 := h0w₁.ne.symm
              have hw₁_leaf : ∀ u, K.Adj w₁ u → u = 0 := by
                intro u hu
                rcases hstar w₁ u hu with h | h
                · exact absurd h hw₁0
                · exact h
              have hw₂_leaf : ∀ u, K.Adj w₂ u → u = 0 := by
                intro u hu
                rcases hstar w₂ u hu with h | h
                · exact absurd h h0w₂.ne.symm
                · exact h
              have hdep := sharedFun_dep_leaf_root (a := a) K g hg_t w₁ h0w₁
              have hrew := sharedFun_update_leaf_false (a := a) K g w₁ 0 hw₁0 hw₁_leaf
              have hnc : ∃ x x',
                  sharedFun K ∅ ∅ g (Function.update x (Fin.natAdd n (Fin.castAdd a w₁)) false) ≠
                  sharedFun K ∅ ∅ g (Function.update x' (Fin.natAdd n (Fin.castAdd a w₁)) false) := by
                obtain ⟨x, x', hne⟩ := sharedFun_nonconst (K.deleteEdges {s(w₁, 0)}) ∅ (∅ : Finset (Fin a)) g
                  (by simp) hg_nc
                exact ⟨x, x', by rw [congrFun hrew x, congrFun hrew x']; exact hne⟩
              obtain ⟨hs1, hC'⟩ := elim_one_var (Fin.natAdd n (Fin.castAdd a w₁)) false hC hdep hnc
              rw [hrew] at hC'
              have hedge := edgeFinset_card_deleteEdge K w₁ 0 h0w₁.symm
              rcases ih (s - 1) (by omega) (K.deleteEdges {s(w₁, 0)}) ∅ ∅
                  (hAcyc.anti (SimpleGraph.deleteEdges_le _)) (by simp) (by simp) hC' with
                ⟨S', c, hvc', h0S', hc, hle⟩ | ⟨S', q', hvc', h0S', hq', hle⟩
              · have hw₂in : w₂ ∈ S' := by
                  have hne_e : s(0, w₂) ≠ s(w₁, 0) := by
                    intro he
                    rw [Sym2.eq_iff] at he
                    rcases he with ⟨h1, _⟩ | ⟨_, h2⟩
                    · exact hw₁0 h1.symm
                    · exact hw₂ne h2
                  rcases hvc' 0 w₂ (SimpleGraph.deleteEdges_adj.2 ⟨h0w₂, by simpa using hne_e⟩) with
                    h | h
                  · exact absurd h h0S'
                  · exact h
                set S := insert (0 : Fin (k + 1)) (S'.erase w₂)
                have hvc : IsVC K S := by
                  intro u v huv
                  rcases hstar u v huv with rfl | rfl
                  · exact Or.inl (Finset.mem_insert_self 0 _)
                  · exact Or.inr (Finset.mem_insert_self 0 _)
                have h0S : (0 : Fin (k + 1)) ∈ S := Finset.mem_insert_self 0 _
                have hcard : S.card = S'.card := by
                  have h0not : (0 : Fin (k + 1)) ∉ S'.erase w₂ :=
                    fun h => h0S' (Finset.mem_of_mem_erase h)
                  rw [Finset.card_insert_of_notMem h0not, Finset.card_erase_of_mem hw₂in]
                  have hpos : 1 ≤ S'.card := Finset.one_le_card.2 ⟨w₂, hw₂in⟩
                  omega
                have hq : HasCircuitSize (n + 1 + 1) (gStar g) (c + 2) :=
                  gFlat_to_gStar g hg_nc hc
                refine Or.inr ⟨S, c + 2, hvc, h0S, hq, ?_⟩
                simp only [Finset.card_empty, zero_add] at hle ⊢
                omega
              · have hvc : IsVC K S' := by
                  intro u v huv
                  rcases hstar u v huv with rfl | rfl
                  · exact Or.inl h0S'
                  · exact Or.inr h0S'
                refine Or.inr ⟨S', q', hvc, h0S', hq', ?_⟩
                simp only [Finset.card_empty, zero_add] at hle ⊢
                omega
            · have huniq : ∀ u : Fin (k + 1), K.Adj 0 u → u = w₁ := by
                intro u hu
                by_contra hne
                exact htwo ⟨u, hne, hu⟩
              have hedge1 : K.edgeFinset.card = 1 :=
                edgeFinset_card_star_single K w₁ hstar h0w₁ huniq
              let idx : Fin (n + 1 + 1) → Fin (n + ((k + 1) + a)) :=
                Fin.snoc (Fin.snoc (fun i : Fin n => Fin.castAdd ((k + 1) + a) i)
                  (Fin.natAdd n (Fin.castAdd a (0 : Fin (k + 1)))))
                  (Fin.natAdd n (Fin.castAdd a w₁))
              have hidx_inj : Function.Injective idx := by
                intro i j
                refine Fin.lastCases ?_ (fun i1 => ?_) i
                · refine Fin.lastCases ?_ (fun j1 => ?_) j
                  · intro _; rfl
                  · refine Fin.lastCases ?_ (fun j2 => ?_) j1
                    · intro hij
                      exfalso
                      simp only [idx, Fin.snoc_last, Fin.snoc_castSucc] at hij
                      exact h0w₁.ne.symm (Fin.castAdd_injective _ _ (Fin.natAdd_injective _ _ hij))
                    · intro hij
                      exfalso
                      simp only [idx, Fin.snoc_last, Fin.snoc_castSucc] at hij
                      exact fin_castAdd_ne_natAdd j2 _ hij.symm
                · refine Fin.lastCases ?_ (fun j1 => ?_) j
                  · refine Fin.lastCases ?_ (fun i2 => ?_) i1
                    · intro hij
                      exfalso
                      simp only [idx, Fin.snoc_last, Fin.snoc_castSucc] at hij
                      exact h0w₁.ne (Fin.castAdd_injective _ _ (Fin.natAdd_injective _ _ hij))
                    · intro hij
                      exfalso
                      simp only [idx, Fin.snoc_last, Fin.snoc_castSucc] at hij
                      exact fin_castAdd_ne_natAdd i2 _ hij
                  · refine Fin.lastCases ?_ (fun i2 => ?_) i1
                    · refine Fin.lastCases ?_ (fun j2 => ?_) j1
                      · intro _; rfl
                      · intro hij
                        exfalso
                        simp only [idx, Fin.snoc_last, Fin.snoc_castSucc] at hij
                        exact fin_castAdd_ne_natAdd j2 _ hij.symm
                    · refine Fin.lastCases ?_ (fun j2 => ?_) j1
                      · intro hij
                        exfalso
                        simp only [idx, Fin.snoc_last, Fin.snoc_castSucc] at hij
                        exact fin_castAdd_ne_natAdd i2 _ hij
                      · intro hij
                        simp only [idx, Fin.snoc_castSucc] at hij
                        congr 2
                        exact Fin.castAdd_injective _ _ hij
              have hFG : ∀ x : Fin (n + ((k + 1) + a)) → Bool,
                  sharedFun K ∅ ∅ g x = gStar g (fun j : Fin (n + 1 + 1) => x (idx j)) := by
                intro x
                simp only [sharedFun, gStar, idx, Fin.snoc_castSucc, Fin.snoc_last,
                  Finset.notMem_empty, false_and, exists_false, decide_false, Bool.or_false]
                congr 1
                apply Bool.eq_iff_iff.2
                simp only [decide_eq_true_eq, Bool.and_eq_true]
                constructor
                · rintro ⟨u, v, huv, hux, hvx⟩
                  rcases hstar u v huv with rfl | rfl
                  · rw [huniq v huv] at hvx; exact ⟨hux, hvx⟩
                  · rw [huniq u huv.symm] at hux; exact ⟨hvx, hux⟩
                · rintro ⟨h0x, hw1x⟩
                  exact ⟨0, w₁, h0w₁, h0x, hw1x⟩
              have hCgStar : HasCircuitSize (n + 1 + 1) (gStar g) s :=
                hardwire_project idx hidx_inj hC hFG (gStar_nonconst hg_f)
              refine Or.inr ⟨{0}, s, ?_, Finset.mem_singleton_self 0, hCgStar, ?_⟩
              · intro u v huv
                rcases hstar u v huv with rfl | rfl
                · exact Or.inl (Finset.mem_singleton_self 0)
                · exact Or.inr (Finset.mem_singleton_self 0)
              · simp [hedge1]; omega
          · have hempty : ∀ u v : Fin (k + 1), ¬ K.Adj u v := by
              intro u v huv
              rcases hstar u v huv with rfl | rfl
              · exact hhas0 ⟨v, huv⟩
              · exact hhas0 ⟨u, huv.symm⟩
            have he0 : K.edgeFinset.card = 0 := by
              apply Finset.card_eq_zero.2
              ext e
              induction e using Sym2.ind with
              | _ u v => simp [SimpleGraph.mem_edgeFinset, hempty u v]
            let idx : Fin (n + 1) → Fin (n + ((k + 1) + a)) :=
              Fin.snoc (fun i : Fin n => Fin.castAdd ((k + 1) + a) i)
                (Fin.natAdd n (Fin.castAdd a (0 : Fin (k + 1))))
            have hidx_inj : Function.Injective idx := by
              intro i j
              refine Fin.lastCases ?_ (fun i1 => ?_) i
              · refine Fin.lastCases ?_ (fun j1 => ?_) j
                · intro _; rfl
                · intro hij
                  exfalso
                  simp only [idx, Fin.snoc_last, Fin.snoc_castSucc] at hij
                  exact fin_castAdd_ne_natAdd j1 _ hij.symm
              · refine Fin.lastCases ?_ (fun j1 => ?_) j
                · intro hij
                  exfalso
                  simp only [idx, Fin.snoc_last, Fin.snoc_castSucc] at hij
                  exact fin_castAdd_ne_natAdd i1 _ hij
                · intro hij
                  simp only [idx, Fin.snoc_castSucc] at hij
                  congr 1
                  exact Fin.castAdd_injective _ _ hij
            have hFG : ∀ x : Fin (n + ((k + 1) + a)) → Bool,
                sharedFun K ∅ ∅ g x = gFlat g (fun j : Fin (n + 1) => x (idx j)) := by
              intro x
              simp only [sharedFun, gFlat, idx, Fin.snoc_castSucc, Fin.snoc_last,
                Finset.notMem_empty, false_and, exists_false, decide_false, Bool.or_false]
              have hno : ¬ ∃ u v : Fin (k + 1), K.Adj u v ∧
                  x (Fin.natAdd n (Fin.castAdd a u)) = true ∧
                  x (Fin.natAdd n (Fin.castAdd a v)) = true := by
                rintro ⟨u, v, huv, _, _⟩; exact hempty u v huv
              simp [hno]
            have hCgFlat : HasCircuitSize (n + 1) (gFlat g) s :=
              hardwire_project idx hidx_inj hC hFG (gFlat_nonconst hg_nc)
            refine Or.inl ⟨∅, s, fun u v huv => absurd huv (hempty u v),
              Finset.notMem_empty 0, hCgFlat, ?_⟩
            simp [he0]

theorem PEqualNP.Outside.L_meta_549 :
    ∀ (n k a : ℕ) (K : SimpleGraph (Fin (k + 1))) [DecidableRel K.Adj] (g : (Fin n → Bool) → Bool → Bool), K.IsAcyclic → (∃ (y y' : Fin n → Bool) (b b' : Bool), g y b ≠ g y' b') → (∃ y : Fin n → Bool, g y false = false) → (∃ y : Fin n → Bool, g y true = false) → ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize (n + ((k + 1) + a)) (fun x : Fin (n + ((k + 1) + a)) → Bool => g (fun i : Fin n => x (Fin.castAdd ((k + 1) + a) i)) (x (Fin.natAdd n (Fin.castAdd a (0 : Fin (k + 1))))) || decide (∃ u w : Fin (k + 1), K.Adj u w ∧ x (Fin.natAdd n (Fin.castAdd a u)) = true ∧ x (Fin.natAdd n (Fin.castAdd a w)) = true) || decide (∃ i : Fin a, x (Fin.natAdd n (Fin.natAdd (k + 1) i)) = true)) s → (∃ (S : Finset (Fin (k + 1))) (c : ℕ), (∀ u w : Fin (k + 1), K.Adj u w → u ∈ S ∨ w ∈ S) ∧ (0 : Fin (k + 1)) ∉ S ∧ PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun z : Fin (n + 1) → Bool => g (fun i : Fin n => z i.castSucc) (z (Fin.last n))) c ∧ a + K.edgeFinset.card + c + S.card ≤ s) ∨ (∃ (S : Finset (Fin (k + 1))) (q : ℕ), (∀ u w : Fin (k + 1), K.Adj u w → u ∈ S ∨ w ∈ S) ∧ (0 : Fin (k + 1)) ∈ S ∧ PEqualNP.MetaComplexity.HasCircuitSize (n + 1 + 1) (fun z : Fin (n + 1 + 1) → Bool => g (fun i : Fin n => z i.castSucc.castSucc) (z (Fin.last n).castSucc) || (z (Fin.last n).castSucc && z (Fin.last (n + 1)))) q ∧ a + K.edgeFinset.card + q + S.card ≤ s + 2) := by
  intro n k a K _ g hAcyc hg_nc hg_f hg_t s hC
  have hfun : (fun x : Fin (n + ((k + 1) + a)) → Bool =>
      g (fun i : Fin n => x (Fin.castAdd ((k + 1) + a) i))
        (x (Fin.natAdd n (Fin.castAdd a (0 : Fin (k + 1))))) ||
      decide (∃ u w : Fin (k + 1), K.Adj u w ∧
        x (Fin.natAdd n (Fin.castAdd a u)) = true ∧
        x (Fin.natAdd n (Fin.castAdd a w)) = true) ||
      decide (∃ i : Fin a, x (Fin.natAdd n (Fin.natAdd (k + 1) i)) = true)) =
      sharedFun K ∅ Finset.univ g := by
    funext x
    simp [sharedFun]
  rw [hfun] at hC
  rcases lower_bound_shared g hg_nc hg_f hg_t s K ∅ Finset.univ hAcyc
      (Finset.notMem_empty 0) (by simp) hC with
    ⟨S, c, hvc, h0S, hc, hle⟩ | ⟨S, q, hvc, h0S, hq, hle⟩
  · refine Or.inl ⟨S, c, hvc, h0S, hc, ?_⟩
    simp only [Finset.card_univ, Fintype.card_fin, Finset.card_empty, add_zero] at hle
    exact hle
  · refine Or.inr ⟨S, q, hvc, h0S, hq, ?_⟩
    simp only [Finset.card_univ, Fintype.card_fin, Finset.card_empty, add_zero] at hle
    exact hle
