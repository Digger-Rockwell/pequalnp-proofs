import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def wiresFrom (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private theorem wiresFrom_nil (x : List Bool) : wiresFrom [] x = x := rfl

private theorem wiresFrom_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    wiresFrom (g :: gs) x = wiresFrom gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

private theorem wiresFrom_append (gs₁ gs₂ : List Gate) (x : List Bool) :
    wiresFrom (gs₁ ++ gs₂) x = wiresFrom gs₂ (wiresFrom gs₁ x) :=
  List.foldl_append

private theorem length_wiresFrom (gs : List Gate) : ∀ x : List Bool,
    (wiresFrom gs x).length = x.length + gs.length := by
  induction gs with
  | nil => intro x; simp [wiresFrom]
  | cons g gs ih =>
    intro x
    rw [wiresFrom_cons, ih]
    simp; omega

private theorem wiresFrom_prefix (gs : List Gate) : ∀ x : List Bool,
    ∃ t : List Bool, wiresFrom gs x = x ++ t := by
  induction gs with
  | nil => intro x; exact ⟨[], by simp [wiresFrom]⟩
  | cons g gs ih =>
    intro x
    obtain ⟨t, ht⟩ := ih (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])
    exact ⟨[g.op.eval (g.inputs.map fun i => x.getD i false)] ++ t, by
      rw [wiresFrom_cons, ht, List.append_assoc]⟩

private theorem getD_wiresFrom (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (wiresFrom gs x).getD i false = x.getD i false := by
  obtain ⟨t, ht⟩ := wiresFrom_prefix gs x
  rw [ht, List.getD_append _ _ _ _ hi]

private theorem getD_snoc_eq {α : Type} (L : List α) (a d : α) :
    (L ++ [a]).getD L.length d = a := by
  simp

private theorem getD_snoc_len {α : Type} (L : List α) (a d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [a]).getD k d = a := by
  subst h; simp

private theorem getD_snoc_ne {α : Type} (L : List α) (a d : α) (k : ℕ) (h : k ≠ L.length) :
    (L ++ [a]).getD k d = L.getD k d := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · exact List.getD_append _ _ _ _ hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private def Ok (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

private def NOk (g : Gate) : Prop :=
  Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

private theorem fanInTwo_iff_ok (C : Circuit) : FanInTwo C ↔ ∀ g ∈ C.gates, Ok g := by
  rfl

private def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

private theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

private theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with rfl | rfl | rfl
  · exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

private theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    rw [List.map_cons, wiresFrom_cons, wiresFrom_cons, normGate_eval, ih]

private theorem mem_normGate_inputs_iff (g : Gate) (a : ℕ) :
    a ∈ (normGate g).inputs ↔
      (g.op = GateOp.not ∧ g.inputs.head? = some a) ∨
      (g.op ≠ GateOp.not ∧ a ∈ g.inputs) := by
  obtain ⟨op, inputs⟩ := g
  cases op with
  | not =>
    cases inputs with
    | nil => simp [normGate]
    | cons b bs =>
      simp [normGate, eq_comm]
  | and => simp [normGate]
  | or => simp [normGate]
  | mod m => simp [normGate]
  | maj => simp [normGate]

private theorem normGate_eq_of_or (g : Gate) (h : (normGate g).op = GateOp.or) :
    g.op = GateOp.or ∧ normGate g = g := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp [normGate] at h ⊢

private def statVal (w : List Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

private def statValid (m : ℕ) : Bool ⊕ ℕ → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

private theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Bool ⊕ ℕ,
    statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

private theorem statVal_append (w t : List Bool) : ∀ s : Bool ⊕ ℕ, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

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

private def simplify (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) : Option Gate × (Bool ⊕ ℕ) :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

private theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
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

private theorem simplify_count (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
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

private theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List (Bool ⊕ ℕ)) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

private theorem simplify_inr_of_mem_false (g : Gate) (m u : ℕ) (f : ℕ → Bool ⊕ ℕ)
    (hnok : NOk g) (hmem : Sum.inl false ∈ g.inputs.map f)
    (hinr : (simplify g.op m (g.inputs.map f)).2 = Sum.inr u) :
    g.op = GateOp.or ∧ g.inputs.length = 2 ∧
      ∃ a b : ℕ, g.inputs = [a, b] ∧
        ((f a = Sum.inl false ∧ f b = Sum.inr u) ∨
         (f a = Sum.inr u ∧ f b = Sum.inl false)) := by
  obtain ⟨⟨hop, hlen⟩, hnot⟩ := hnok
  rcases hop with hop | hop | hop
  · rw [hop] at hinr
    rcases h : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp [h] at hmem
    · rw [h] at hmem hinr
      cases hfa : f a <;> simp_all [simplify, simpAnd]
    · rw [h] at hmem hinr
      cases hfa : f a <;> cases hfb : f b <;> (try rename_i c1; cases c1) <;>
        (try rename_i c2; cases c2) <;> simp_all [simplify, simpAnd]
    · rw [h] at hlen; simp at hlen
  · rw [hop] at hinr
    refine ⟨hop, ?_⟩
    rcases h : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp [h] at hmem
    · rw [h] at hmem hinr
      cases hfa : f a <;> simp_all [simplify, simpOr]
    · rw [h] at hmem hinr
      refine ⟨by simp, a, b, rfl, ?_⟩
      cases hfa : f a with
      | inl c1 =>
        cases hfb : f b with
        | inl c2 => simp [hfa, hfb, simplify, simpOr] at hinr
        | inr v =>
          cases c1 <;> simp [hfa, hfb, simplify, simpOr] at hinr
          subst hinr; exact Or.inl ⟨rfl, rfl⟩
      | inr v =>
        cases hfb : f b with
        | inl c2 =>
          cases c2 <;> simp [hfa, hfb, simplify, simpOr] at hinr
          subst hinr; exact Or.inr ⟨rfl, rfl⟩
        | inr v2 => simp [hfa, hfb] at hmem
    · rw [h] at hlen; simp at hlen
  · have hlen1 := hnot hop
    rw [hop] at hinr
    rcases h : g.inputs with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp [h] at hmem
    · rw [h] at hmem hinr
      cases hfa : f a <;> simp_all [simplify, simpNot]
    · rw [h] at hlen1; simp at hlen1

private def elimStep (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  (acc.1 ++ [(simplify g.op (m + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (m + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

private def elim (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  gs.foldl (elimStep m) acc

private theorem elim_append (m : ℕ) (gs₁ gs₂ : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    elim m (gs₁ ++ gs₂) acc = elim m gs₂ (elim m gs₁ acc) :=
  List.foldl_append

private theorem elim_stat_len (m : ℕ) (gs : List Gate) : ∀ acc : List (Bool ⊕ ℕ) × List Gate,
    (elim m gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    show (elim m gs (elimStep m acc g)).1.length = _
    rw [ih]
    simp [elimStep]; omega

private theorem elim_getD (m k : ℕ) (d : Bool ⊕ ℕ) (gs : List Gate) :
    ∀ acc : List (Bool ⊕ ℕ) × List Gate,
      k < acc.1.length → (elim m gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    show (elim m gs (elimStep m acc g)).1.getD k d = _
    rw [ih (elimStep m acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

private theorem elim_gates_prefix (m : ℕ) (gs : List Gate) :
    ∀ acc : List (Bool ⊕ ℕ) × List Gate, ∃ t : List Gate, (elim m gs acc).2 = acc.2 ++ t := by
  induction gs with
  | nil => intro acc; exact ⟨[], by simp [elim]⟩
  | cons g gs ih =>
    intro acc
    obtain ⟨t, ht⟩ := ih (elimStep m acc g)
    refine ⟨(simplify g.op (m + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList ++ t, ?_⟩
    show (elim m gs (elimStep m acc g)).2 = _
    rw [ht, elimStep, List.append_assoc]

private theorem elim_ok (m : ℕ) (gs : List Gate) : ∀ acc : List (Bool ⊕ ℕ) × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim m gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep m acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

private theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

private theorem elim_len (m : ℕ) (gs : List Gate) : ∀ acc : List (Bool ⊕ ℕ) × List Gate,
    (elim m gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep m acc g)
    have h2 : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (m + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    show (elim m gs (elimStep m acc g)).2.length ≤ _
    rw [List.length_cons]; omega

private theorem elim_len_lt (m k : ℕ) (gs : List Gate) : ∀ acc : List (Bool ⊕ ℕ) × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim m gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    show (elim m gs (elimStep m acc g)).2.length + 1 ≤ acc.2.length + (g :: gs).length
    rw [List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep m acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len m gs (elimStep m acc g)
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
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

private def elimInv (m : ℕ) (x : List Bool) (w : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate) :
    Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    statValid (m + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 x) (acc.1.getD i (Sum.inl false)) = w.getD i false

private theorem inv_elim (m : ℕ) (x : List Bool) (hx : x.length = m) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate), (∀ g ∈ gs, Ok g) →
      elimInv m x w acc → elimInv m x (wiresFrom gs w) (elim m gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep m acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 x with hw'
    have lw' : w'.length = m + acc.2.length := by rw [hw', length_wiresFrom, hx]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (m + acc.2.length) ins with hr
    have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) x = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show statValid (m + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ r.1.toList) x) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

private theorem minimal_output_lt {m : ℕ} {C : Circuit}
    (hnc : ∃ x y : Fin m → Bool, circuitFun m C x ≠ circuitFun m C y) :
    C.output < m + C.gates.length := by
  by_contra h
  obtain ⟨x, y, hxy⟩ := hnc
  apply hxy
  have hx : (C.wires (List.ofFn x)).length = m + C.gates.length := by
    show (wiresFrom C.gates (List.ofFn x)).length = _
    rw [length_wiresFrom]; simp
  have hy : (C.wires (List.ofFn y)).length = m + C.gates.length := by
    show (wiresFrom C.gates (List.ofFn y)).length = _
    rw [length_wiresFrom]; simp
  simp only [circuitFun, Circuit.eval]
  rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

private theorem minimal_output_last {m : ℕ} {C : Circuit}
    (hmin : IsMinimalCircuit m C)
    (hnc : ∃ x y : Fin m → Bool, circuitFun m C x ≠ circuitFun m C y)
    (hpos : 0 < C.gates.length) :
    C.output = m + (C.gates.length - 1) := by
  have hlt := minimal_output_lt hnc
  by_contra hne
  have hlt' : C.output < m + (C.gates.length - 1) := by omega
  let gs' := C.gates.take (C.gates.length - 1)
  have hlen' : gs'.length = C.gates.length - 1 := by simp [gs']
  have hfan' : FanInTwo ⟨gs', C.output⟩ := by
    intro g hg
    exact hmin.1 g (List.mem_of_mem_take hg)
  have heq : circuitFun m ⟨gs', C.output⟩ = circuitFun m C := by
    funext x
    simp only [circuitFun, Circuit.eval]
    show (wiresFrom gs' (List.ofFn x)).getD C.output false =
      (wiresFrom C.gates (List.ofFn x)).getD C.output false
    have hsplit : C.gates = gs' ++ C.gates.drop (C.gates.length - 1) :=
      (List.take_append_drop _ _).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    symm
    exact getD_wiresFrom _ _ _ (by rw [length_wiresFrom, List.length_ofFn, hlen']; exact hlt')
  have hle := hmin.2 ⟨gs', C.output⟩ hfan' heq
  simp only [Circuit.size] at hle
  omega

private theorem minimal_inputs_lt {m : ℕ} {C : Circuit}
    (hmin : IsMinimalCircuit m C)
    (hnc : ∃ x y : Fin m → Bool, circuitFun m C x ≠ circuitFun m C y) :
    let gs := C.gates.map normGate
    ∀ (j : Fin gs.length) (a : ℕ), a ∈ (gs.get j).inputs → a < m + j.val := by
  intro gs j a ha
  by_contra hge
  push Not at hge
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hmin.1 g0 hg0)
  let init : List (Bool ⊕ ℕ) := List.ofFn (fun i : Fin m => Sum.inr i.val)
  let acc := elim m gs (init, [])
  have hinv : ∀ x : Fin m → Bool, elimInv m (List.ofFn x) (wiresFrom gs (List.ofFn x)) acc := by
    intro x
    apply inv_elim m (List.ofFn x) (by simp) gs (List.ofFn x) (init, [])
      (fun g hg => (hnok g hg).1)
    refine ⟨by simp [init], fun i => ?_⟩
    by_cases hi : i < m
    · simp [init, hi, statValid, statVal, wiresFrom]
    · rw [List.getD_eq_default _ _ (by simp [init]; omega),
          List.getD_eq_default _ _ (by simp; omega)]
      exact ⟨trivial, rfl⟩
  have hval : ∀ x : Fin m → Bool,
      statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
        circuitFun m C x := by
    intro x
    rw [((hinv x).2 C.output).2]
    show (wiresFrom (C.gates.map normGate) (List.ofFn x)).getD C.output false = _
    rw [wiresFrom_norm]; rfl
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    obtain ⟨x, y, hxy⟩ := hnc
    apply hxy
    rw [← hval x, ← hval y, hst]; rfl
  | inr out' =>
    have hsplit : gs = gs.take j.val ++ (gs.get j) :: gs.drop (j.val + 1) := by
      have h1 := List.take_append_drop j.val gs
      have h2 : gs.drop j.val = gs.get j :: gs.drop (j.val + 1) := by
        simpa [List.get_eq_getElem] using List.drop_eq_getElem_cons j.isLt
      rw [← h2, h1]
    set acc1 := elim m (gs.take j.val) (init, []) with hacc1
    have hlen1 : acc1.1.length = m + j.val := by
      rw [hacc1, elim_stat_len]; simp [init, Nat.min_eq_left (le_of_lt j.isLt)]
    have hgeta : acc1.1.getD a (Sum.inl false) = Sum.inl false :=
      List.getD_eq_default _ _ (by omega)
    have hgj_nok : NOk (gs.get j) := hnok _ (List.get_mem _ _)
    have hnone : (simplify (gs.get j).op (m + acc1.2.length)
        ((gs.get j).inputs.map fun i => acc1.1.getD i (Sum.inl false))).1 = none := by
      apply simplify_count
      · exact hgj_nok.1.1
      · simpa using hgj_nok.1.2
      · intro h; simpa using hgj_nok.2 h
      · exact ⟨false, List.mem_map.2 ⟨a, ha, hgeta⟩⟩
    have hacc_eq : acc = elim m (gs.drop (j.val + 1)) (elimStep m acc1 (gs.get j)) := by
      show elim m gs (init, []) = _
      conv_lhs => rw [hsplit, elim_append]
      rfl
    have hlen_acc : acc.2.length + 1 ≤ gs.length := by
      have hle1 := elim_len m (gs.take j.val) (init, [])
      rw [← hacc1] at hle1
      have hle2 := elim_len m (gs.drop (j.val + 1)) (elimStep m acc1 (gs.get j))
      have hmid : (elimStep m acc1 (gs.get j)).2.length = acc1.2.length := by
        show (acc1.2 ++ (simplify (gs.get j).op (m + acc1.2.length)
          ((gs.get j).inputs.map fun i => acc1.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      rw [hacc_eq]
      simp only [List.length_nil, zero_add, List.length_take, List.length_drop] at hle1 hle2
      have hjlt := j.isLt
      omega
    have hle := hmin.2 ⟨acc.2, out'⟩ (elim_ok m gs _ (by simp)) (by
      funext x
      have := hval x
      rw [hst] at this
      exact this)
    have hgs_len : gs.length = C.gates.length := by simp [gs]
    simp only [Circuit.size] at hle
    omega

private def shiftWire (k a : ℕ) : ℕ :=
  if a < k then a else a - 1

private def shiftGate (k : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (shiftWire k)⟩

private theorem getD_erase_shift (w₁ w₂ : List Bool) (v : Bool) (a : ℕ) (hne : a ≠ w₁.length) :
    (w₁ ++ w₂).getD (shiftWire w₁.length a) false = (w₁ ++ v :: w₂).getD a false := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · simp only [shiftWire, if_pos hlt]
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hlt]
  · simp only [shiftWire, if_neg (show ¬ a < w₁.length by omega)]
    rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
    obtain ⟨d, hd⟩ : ∃ d, a - w₁.length = d + 1 := ⟨a - w₁.length - 1, by omega⟩
    have h1 : a - 1 - w₁.length = d := by omega
    rw [h1, hd]; rfl

private theorem wiresFrom_erase_orphan (gs : List Gate) (w₁ : List Bool) (v : Bool) :
    ∀ w₂ : List Bool, (∀ g ∈ gs, w₁.length ∉ g.inputs) →
      ∃ w₂' : List Bool,
        wiresFrom (gs.map (shiftGate w₁.length)) (w₁ ++ w₂) = w₁ ++ w₂' ∧
        wiresFrom gs (w₁ ++ v :: w₂) = w₁ ++ v :: w₂' := by
  induction gs with
  | nil => intro w₂ _; exact ⟨w₂, rfl, rfl⟩
  | cons g gs ih =>
    intro w₂ hno
    have hgno : w₁.length ∉ g.inputs := hno g List.mem_cons_self
    have hev : (shiftGate w₁.length g).op.eval
        ((shiftGate w₁.length g).inputs.map fun i => (w₁ ++ w₂).getD i false) =
        g.op.eval (g.inputs.map fun i => (w₁ ++ v :: w₂).getD i false) := by
      simp only [shiftGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact getD_erase_shift w₁ w₂ v a (fun e => hgno (e ▸ ha))
    rw [List.map_cons, wiresFrom_cons, wiresFrom_cons, hev, List.append_assoc]
    have hassoc : w₁ ++ v :: w₂ ++ [g.op.eval (g.inputs.map fun i => (w₁ ++ v :: w₂).getD i false)] =
        w₁ ++ v :: (w₂ ++ [g.op.eval (g.inputs.map fun i => (w₁ ++ v :: w₂).getD i false)]) := by
      simp [List.append_assoc]
    rw [hassoc]
    exact ih _ (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))

private theorem minimal_gate_read {m : ℕ} {C : Circuit}
    (hmin : IsMinimalCircuit m C)
    (hnc : ∃ x y : Fin m → Bool, circuitFun m C x ≠ circuitFun m C y) :
    let gs := C.gates.map normGate
    ∀ j : Fin gs.length, m + j.val ≠ C.output →
      ∃ j' : Fin gs.length, m + j.val ∈ (gs.get j').inputs := by
  intro gs j hne
  by_contra hnone
  push Not at hnone
  let k := m + j.val
  let gs₁ := gs.take j.val
  let gs₂ := gs.drop (j.val + 1)
  have hgs_split : gs = gs₁ ++ gs.get j :: gs₂ := by
    have h1 := List.take_append_drop j.val gs
    have h2 : gs.drop j.val = gs.get j :: gs₂ := by
      rw [List.get_eq_getElem]
      exact List.drop_eq_getElem_cons j.isLt
    rw [← h2, h1]
  have hgs₁_len : gs₁.length = j.val := by simp [gs₁]
  let gs' := gs₁ ++ gs₂.map (shiftGate k)
  have hgs'_len : gs'.length + 1 = gs.length := by
    simp only [gs', List.length_append, List.length_map, hgs₁_len, gs₂, List.length_drop]
    have := j.isLt; omega
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hmin.1 g0 hg0)
  have hfan' : FanInTwo ⟨gs', shiftWire k C.output⟩ := by
    intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact (hnok g (List.mem_of_mem_take hg)).1
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
      have h0 := (hnok g0 (List.mem_of_mem_drop hg0)).1
      exact ⟨h0.1, by simp [shiftGate, h0.2]⟩
  have hno_gs₂ : ∀ g ∈ gs₂, k ∉ g.inputs := by
    intro g hg hmem
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hg
    have hi' : j.val + 1 + i < gs.length := by
      simp [gs₂] at hi; omega
    have hget : gs₂[i] = gs.get ⟨j.val + 1 + i, hi'⟩ := by
      simp [gs₂, List.getElem_drop, List.get_eq_getElem]
    rw [hget] at hmem
    exact hnone ⟨j.val + 1 + i, hi'⟩ hmem
  have heq : circuitFun m ⟨gs', shiftWire k C.output⟩ = circuitFun m C := by
    funext x
    simp only [circuitFun, Circuit.eval]
    show (wiresFrom gs' (List.ofFn x)).getD (shiftWire k C.output) false =
      (wiresFrom C.gates (List.ofFn x)).getD C.output false
    rw [← wiresFrom_norm C.gates (List.ofFn x)]
    change (wiresFrom (gs₁ ++ gs₂.map (shiftGate k)) (List.ofFn x)).getD (shiftWire k C.output) false =
      (wiresFrom gs (List.ofFn x)).getD C.output false
    conv_rhs => rw [hgs_split]
    rw [wiresFrom_append, wiresFrom_append, wiresFrom_cons]
    set w₁ := wiresFrom gs₁ (List.ofFn x) with hw₁
    have lw₁ : w₁.length = k := by
      rw [hw₁, length_wiresFrom, List.length_ofFn, hgs₁_len]
    have hno' : ∀ g ∈ gs₂, w₁.length ∉ g.inputs := by rw [lw₁]; exact hno_gs₂
    obtain ⟨w₂', he1, he2⟩ := wiresFrom_erase_orphan gs₂ w₁
      ((gs.get j).op.eval ((gs.get j).inputs.map fun i => w₁.getD i false)) [] hno'
    simp only [List.append_nil] at he1
    rw [← lw₁, he1]
    have he2' : wiresFrom gs₂ (w₁ ++ [(gs.get j).op.eval ((gs.get j).inputs.map fun i => w₁.getD i false)]) =
        w₁ ++ ((gs.get j).op.eval ((gs.get j).inputs.map fun i => w₁.getD i false)) :: w₂' := he2
    rw [he2']
    exact getD_erase_shift w₁ w₂' _ C.output (by rw [lw₁]; exact Ne.symm hne)
  have hle := hmin.2 ⟨gs', shiftWire k C.output⟩ hfan' heq
  have hgs_len : gs.length = C.gates.length := by simp [gs]
  simp only [Circuit.size] at hle
  omega

private theorem wiresFrom_agree_outside (S : ℕ → Prop) (gs : List Gate) :
    ∀ w₁ w₂ : List Bool,
      w₁.length = w₂.length →
      (∀ a, S a → a < w₁.length) →
      (∀ a < w₁.length, ¬ S a → w₁.getD a false = w₂.getD a false) →
      (∀ g ∈ gs, ∀ a ∈ g.inputs, ¬ S a) →
      ∀ a, ¬ S a → (wiresFrom gs w₁).getD a false = (wiresFrom gs w₂).getD a false := by
  induction gs with
  | nil =>
    intro w₁ w₂ hlen _ hag _ a ha
    by_cases hlt : a < w₁.length
    · exact hag a hlt ha
    · rw [wiresFrom_nil, wiresFrom_nil,
          List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  | cons g gs ih =>
    intro w₁ w₂ hlen hSlt hag hno a ha
    rw [wiresFrom_cons, wiresFrom_cons]
    have hev : g.op.eval (g.inputs.map fun i => w₁.getD i false) =
        g.op.eval (g.inputs.map fun i => w₂.getD i false) := by
      congr 1
      apply List.map_congr_left
      intro i hi
      have hni : ¬ S i := hno g List.mem_cons_self i hi
      by_cases hlt : i < w₁.length
      · exact hag i hlt hni
      · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    rw [hev]
    apply ih
    · simp [hlen]
    · intro b hb; simp; have := hSlt b hb; omega
    · intro b hb hnb
      by_cases hbl : b = w₁.length
      · subst hbl
        rw [getD_snoc_eq, getD_snoc_len _ _ _ _ hlen.symm]
      · rw [getD_snoc_ne _ _ _ _ hbl, getD_snoc_ne _ _ _ _ (by omega)]
        exact hag b (by simp at hb; omega) hnb
    · exact fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')
    · exact ha

private theorem snoc_eta {n : ℕ} (x : Fin (n + 1) → Bool) :
    Fin.snoc (fun i : Fin n => x i.castSucc) (x (Fin.last n)) = x := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · simp
  · intro j; simp

private theorem snoc_val_last {α : Type} {n : ℕ} (y : Fin n → α) (b : α) :
    (Fin.snoc y b : Fin (n + 1) → α) ⟨n, Nat.lt_succ_self n⟩ = b := by
  have : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = Fin.last n := rfl
  rw [this]; simp

private theorem snoc_val_lt {α : Type} {n : ℕ} (y : Fin n → α) (b : α) {a : ℕ} (ha : a < n) :
    (Fin.snoc y b : Fin (n + 1) → α) ⟨a, Nat.lt_succ_of_lt ha⟩ = y ⟨a, ha⟩ := by
  exact Fin.snoc_castSucc (α := fun _ => α) b y ⟨a, ha⟩

private theorem exists_H_false_true {n : ℕ} {H : (Fin n → Bool) → Bool}
    (hH : ∃ y y' : Fin n → Bool, H y ≠ H y') :
    (∃ yF : Fin n → Bool, H yF = false) ∧ (∃ yT : Fin n → Bool, H yT = true) := by
  obtain ⟨y, y', hne⟩ := hH
  cases hy : H y <;> cases hy' : H y'
  · exact absurd (hy.trans hy'.symm) hne
  · exact ⟨⟨y, hy⟩, ⟨y', hy'⟩⟩
  · exact ⟨⟨y', hy'⟩, ⟨y, hy⟩⟩
  · exact absurd (hy.trans hy'.symm) hne

private theorem eval_nonconst {n : ℕ} {C : Circuit} {H : (Fin n → Bool) → Bool}
    (hH : ∃ y y' : Fin n → Bool, H y ≠ H y')
    (hev : ∀ x : Fin (n + 1) → Bool,
      circuitFun (n + 1) C x = (x (Fin.last n) || H (fun i : Fin n => x i.castSucc))) :
    ∃ x y : Fin (n + 1) → Bool, circuitFun (n + 1) C x ≠ circuitFun (n + 1) C y := by
  obtain ⟨⟨yF, hyF⟩, _⟩ := exists_H_false_true hH
  refine ⟨Fin.snoc yF false, Fin.snoc yF true, ?_⟩
  rw [hev, hev]
  simp [hyF]

private theorem gates_pos {n : ℕ} {C : Circuit} {H : (Fin n → Bool) → Bool}
    (hH : ∃ y y' : Fin n → Bool, H y ≠ H y')
    (hev : ∀ x : Fin (n + 1) → Bool,
      circuitFun (n + 1) C x = (x (Fin.last n) || H (fun i : Fin n => x i.castSucc))) :
    0 < C.gates.length := by
  by_contra h0
  have hnil : C.gates = [] := List.eq_nil_of_length_eq_zero (by omega)
  obtain ⟨⟨yF, hyF⟩, ⟨yT, hyT⟩⟩ := exists_H_false_true hH
  have hce : ∀ x : Fin (n + 1) → Bool,
      (List.ofFn x).getD C.output false =
        (x (Fin.last n) || H (fun i : Fin n => x i.castSucc)) := by
    intro x
    have := hev x
    simpa [circuitFun, Circuit.eval, Circuit.wires, hnil] using this
  by_cases hlt : C.output < n + 1
  · by_cases hlast : C.output = n
    · have := hce (Fin.snoc yT false)
      rw [hlast] at this
      have hget : (List.ofFn (Fin.snoc yT false : Fin (n + 1) → Bool)).getD n false = false := by
        rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
        exact snoc_val_last yT false
      rw [hget] at this
      simp [hyT] at this
    · have hlt' : C.output < n := by omega
      have h1 := hce (Fin.snoc yF false)
      have h2 := hce (Fin.snoc yF true)
      have hg1 : (List.ofFn (Fin.snoc yF false : Fin (n + 1) → Bool)).getD C.output false =
          yF ⟨C.output, hlt'⟩ := by
        rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
        exact snoc_val_lt yF false hlt'
      have hg2 : (List.ofFn (Fin.snoc yF true : Fin (n + 1) → Bool)).getD C.output false =
          yF ⟨C.output, hlt'⟩ := by
        rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
        exact snoc_val_lt yF true hlt'
      rw [hg1] at h1; rw [hg2] at h2
      simp [hyF] at h1 h2
      rw [h1] at h2; cases h2
  · have := hce (Fin.snoc yF true)
    rw [List.getD_eq_default _ _ (by simp; omega)] at this
    simp at this

private theorem list_set_eq_self {α : Type} (L : List α) (k : ℕ) (a d : α)
    (hk : k < L.length) (heq : L.getD k d = a) : L.set k a = L := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    by_cases hik : i = k
    · subst hik
      rw [List.getElem_set_self]
      rw [List.getD_eq_getElem _ _ hk] at heq
      exact heq.symm
    · rw [List.getElem_set_ne (Ne.symm hik)]

private theorem getD_set_eq {α : Type} {L : List α} {k : ℕ} {a d : α} (hk : k < L.length) :
    (L.set k a).getD k d = a := by
  rw [List.getD_eq_getElem _ _ (by simp [hk]), List.getElem_set_self]

private theorem getD_set_ne {α : Type} {L : List α} {k i : ℕ} {a d : α} (hne : i ≠ k) :
    (L.set k a).getD i d = L.getD i d := by
  by_cases hi : i < L.length
  · rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getD_eq_getElem _ _ hi,
      List.getElem_set_ne (Ne.symm hne)]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private theorem chain_step {n : ℕ} {C : Circuit} {H : (Fin n → Bool) → Bool}
    (hmin : IsMinimalCircuit (n + 1) C)
    (hH : ∃ y y' : Fin n → Bool, H y ≠ H y')
    (hev : ∀ x : Fin (n + 1) → Bool,
      circuitFun (n + 1) C x = (x (Fin.last n) || H (fun i : Fin n => x i.castSucc)))
    (split : ℕ) (S : ℕ → Prop)
    (hsplit : split < (C.gates.map normGate).length)
    (hS_lt : ∀ a, S a → a < n + split)
    (hS_noread : ∀ j : Fin (C.gates.map normGate).length, split ≤ j.val →
      ∀ a ∈ ((C.gates.map normGate).get j).inputs, ¬ S a)
    (hpre_indep : ∀ (y : Fin n → Bool) (a : ℕ), a < n + split → ¬ S a →
      (wiresFrom ((C.gates.map normGate).take split) (List.ofFn (Fin.snoc y false))).getD a false =
      (wiresFrom ((C.gates.map normGate).take split) (List.ofFn (Fin.snoc y true))).getD a false)
    (hz_true : ∀ y : Fin n → Bool,
      (wiresFrom ((C.gates.map normGate).take split)
        (List.ofFn (Fin.snoc y true))).getD (n + split) false = true) :
    let gs := C.gates.map normGate
    ∃ j₁ : Fin gs.length,
      split ≤ j₁.val ∧
      (gs.get j₁).op = GateOp.or ∧
      (gs.get j₁).inputs.length = 2 ∧
      (n + split) ∈ (gs.get j₁).inputs ∧
      (∃ w ∈ (gs.get j₁).inputs, w ≠ n + split ∧ w < n + 1 + j₁.val) ∧
      (∀ j : Fin gs.length, (n + split) ∈ (gs.get j).inputs → j = j₁) := by
  set gs := C.gates.map normGate with hgs_def
  have hgs_len : gs.length = C.gates.length := by simp [hgs_def]
  have hnc := eval_nonconst hH hev
  have hpos := gates_pos hH hev
  have hout_last : C.output = n + 1 + (C.gates.length - 1) := minimal_output_last hmin hnc hpos
  have hlt_all := minimal_inputs_lt hmin hnc
  have hread_all := minimal_gate_read hmin hnc
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hmin.1 g0 hg0)
  let m := n + 1
  let z := n + split
  let gs_pre := gs.take split
  let gs_post := gs.drop split
  have hpre_len : gs_pre.length = split := by simp [gs_pre]; omega
  have hpost_len : gs_post.length = gs.length - split := by simp [gs_post]
  have hgs_eq : gs = gs_pre ++ gs_post := (List.take_append_drop split gs).symm
  have hpost_noread : ∀ g ∈ gs_post, ∀ a ∈ g.inputs, ¬ S a := by
    intro g hg a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hg
    have hi' : split + i < gs.length := by simp [gs_post] at hi; omega
    have hget : gs_post[i] = gs.get ⟨split + i, hi'⟩ := by
      simp [gs_post, List.getElem_drop, List.get_eq_getElem]
    rw [hget] at ha
    exact hS_noread ⟨split + i, hi'⟩ (by dsimp; omega) a ha
  let wpre (x : Fin m → Bool) : List Bool := wiresFrom gs_pre (List.ofFn x)
  have lwpre : ∀ x, (wpre x).length = z + 1 := by
    intro x
    show (wiresFrom gs_pre (List.ofFn x)).length = _
    rw [length_wiresFrom, List.length_ofFn, hpre_len]; omega
  let D (x : Fin m → Bool) (b : Bool) : Bool :=
    (wiresFrom gs_post ((wpre x).set z b)).getD C.output false
  have hev_gs : ∀ x : Fin m → Bool,
      (wiresFrom gs_post (wpre x)).getD C.output false = circuitFun m C x := by
    intro x
    rw [← wiresFrom_append, ← hgs_eq]
    show (wiresFrom (C.gates.map normGate) (List.ofFn x)).getD C.output false = _
    rw [wiresFrom_norm]; rfl
  have hS_out : ¬ S C.output := by
    intro hSo
    have := hS_lt C.output hSo
    omega
  have hD_true : ∀ x : Fin m → Bool, D x true = true := by
    intro x
    let y : Fin n → Bool := fun i => x i.castSucc
    have hx_eq : x = Fin.snoc y (x (Fin.last n)) := (snoc_eta x).symm
    have hag : D x true = (wiresFrom gs_post (wpre (Fin.snoc y true))).getD C.output false := by
      apply wiresFrom_agree_outside S gs_post
      · simp [lwpre]
      · intro a ha; simp [lwpre]; have := hS_lt a ha; omega
      · intro a ha hna
        simp only [List.length_set, lwpre] at ha
        by_cases haz : a = z
        · subst haz
          rw [getD_set_eq (by rw [lwpre]; omega)]
          exact (hz_true y).symm
        · rw [getD_set_ne haz]
          rw [hx_eq]
          cases x (Fin.last n)
          · exact hpre_indep y a (by omega) hna
          · rfl
      · exact hpost_noread
      · exact hS_out
    rw [hag, hev_gs, hev]
    simp
  have hD_false_indep : ∀ y : Fin n → Bool,
      D (Fin.snoc y false) false = D (Fin.snoc y true) false := by
    intro y
    apply wiresFrom_agree_outside S gs_post
    · simp [lwpre]
    · intro a ha; simp [lwpre]; have := hS_lt a ha; omega
    · intro a ha hna
      simp only [List.length_set, lwpre] at ha
      by_cases haz : a = z
      · subst haz
        rw [getD_set_eq (by rw [lwpre]; omega),
            getD_set_eq (by rw [lwpre]; omega)]
      · rw [getD_set_ne haz, getD_set_ne haz]
        exact hpre_indep y a (by omega) hna
    · exact hpost_noread
    · exact hS_out
  have hdecomp : ∀ x : Fin m → Bool,
      circuitFun m C x = ((wpre x).getD z false || D x false) := by
    intro x
    cases hb : (wpre x).getD z false
    · have hset : (wpre x).set z false = wpre x :=
        list_set_eq_self _ _ _ false (by rw [lwpre]; omega) hb
      simp only [Bool.false_or, D, hset, hev_gs]
    · have hset : (wpre x).set z true = wpre x :=
        list_set_eq_self _ _ _ false (by rw [lwpre]; omega) hb
      have h1 := hD_true x
      simp only [D, hset, hev_gs] at h1
      rw [h1]; simp
  obtain ⟨⟨yF, hyF⟩, _⟩ := exists_H_false_true hH
  have hDF : D (Fin.snoc yF false) false = false := by
    have h1 := hdecomp (Fin.snoc yF false)
    rw [hev] at h1
    simp [hyF] at h1
    exact h1.2
  have hex_post : ∃ g ∈ gs_post, z ∈ g.inputs := by
    by_contra hno
    push Not at hno
    have hag : (wiresFrom gs_post (wpre (Fin.snoc yF true))).getD C.output false =
        D (Fin.snoc yF true) false := by
      apply wiresFrom_agree_outside (fun a => a = z) gs_post
      · simp [lwpre]
      · intro a ha; subst ha; rw [lwpre]; omega
      · intro a _ hna
        exact (getD_set_ne hna).symm
      · intro g hg a ha e; subst e; exact hno g hg ha
      · omega
    rw [hev_gs, hev, ← hD_false_indep yF, hDF] at hag
    simp at hag
  let initStat : List (Bool ⊕ ℕ) :=
    List.ofFn (fun i : Fin (z + 1) => if i.val = z then Sum.inl false else Sum.inr i.val)
  let acc := elim m gs_post (initStat, gs_pre)
  have hinv_init : ∀ x : Fin m → Bool,
      elimInv m (List.ofFn x) ((wpre x).set z false) (initStat, gs_pre) := by
    intro x
    refine ⟨by simp [initStat, lwpre], fun i => ?_⟩
    by_cases hilt : i < z + 1
    · by_cases hiz : i = z
      · subst hiz
        have hg1 : initStat.getD z (Sum.inl false) = Sum.inl false := by
          rw [List.getD_eq_getElem _ _ (by simp [initStat])]
          simp only [initStat, List.getElem_ofFn, ↓reduceIte]
        rw [hg1, getD_set_eq (by rw [lwpre]; omega)]
        exact ⟨trivial, rfl⟩
      · have hg1 : initStat.getD i (Sum.inl false) = Sum.inr i := by
          rw [List.getD_eq_getElem _ _ (by simp [initStat, hilt])]
          simp only [initStat, List.getElem_ofFn, if_neg hiz]
        rw [hg1, getD_set_ne hiz]
        refine ⟨?_, rfl⟩
        show i < m + gs_pre.length
        rw [hpre_len]; omega
    · rw [List.getD_eq_default _ _ (by simp [initStat]; omega),
          List.getD_eq_default _ _ (by simp [lwpre]; omega)]
      exact ⟨trivial, rfl⟩
  have hinv_acc : ∀ x : Fin m → Bool,
      elimInv m (List.ofFn x) (wiresFrom gs_post ((wpre x).set z false)) acc := by
    intro x
    exact inv_elim m (List.ofFn x) (by simp [m]) gs_post _ _
      (fun g hg => (hnok g (List.mem_of_mem_drop hg)).1) (hinv_init x)
  have hval_acc : ∀ x : Fin m → Bool,
      statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) = D x false :=
    fun x => ((hinv_acc x).2 C.output).2
  have hacc_ok : ∀ g ∈ acc.2, Ok g :=
    elim_ok m gs_post (initStat, gs_pre) (fun g hg => (hnok g (List.mem_of_mem_take hg)).1)
  have hout_inr : ∃ out' : ℕ, acc.1.getD C.output (Sum.inl false) = Sum.inr out' := by
    cases hst : acc.1.getD C.output (Sum.inl false) with
    | inr out' => exact ⟨out', rfl⟩
    | inl c =>
      exfalso
      cases c with
      | true =>
        have := hval_acc (Fin.snoc yF false)
        rw [hst, hDF] at this
        simp [statVal] at this
      | false =>
        have hD0 : ∀ x, D x false = false := by
          intro x
          have := hval_acc x
          rw [hst] at this
          exact this.symm
        have hsame : circuitFun m ⟨gs_pre, z⟩ = circuitFun m C := by
          funext x
          rw [hdecomp x, hD0 x, Bool.or_false]; rfl
        have hfan_pre : FanInTwo ⟨gs_pre, z⟩ :=
          fun g hg => (hnok g (List.mem_of_mem_take hg)).1
        have hle := hmin.2 ⟨gs_pre, z⟩ hfan_pre hsame
        simp only [Circuit.size, hpre_len] at hle
        omega
  obtain ⟨out', hout'⟩ := hout_inr
  have hacc_size_lb : gs.length ≤ acc.2.length + 1 := by
    let Cnew : Circuit := ⟨acc.2 ++ [⟨GateOp.or, [z, out']⟩], m + acc.2.length⟩
    have hfan_new : FanInTwo Cnew := by
      intro g hg
      rcases List.mem_append.1 hg with hg | hg
      · exact hacc_ok g hg
      · simp only [List.mem_singleton] at hg; subst hg; exact ⟨Or.inr (Or.inl rfl), by simp⟩
    have hsame : circuitFun m Cnew = circuitFun m C := by
      funext x
      rw [hdecomp x]
      simp only [circuitFun, Circuit.eval, Cnew]
      show (wiresFrom (acc.2 ++ [⟨GateOp.or, [z, out']⟩]) (List.ofFn x)).getD (m + acc.2.length) false = _
      rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
      set wa := wiresFrom acc.2 (List.ofFn x) with hwa
      have lwa : wa.length = m + acc.2.length := by rw [hwa, length_wiresFrom, List.length_ofFn]
      rw [getD_snoc_len _ _ _ _ lwa]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        Bool.or_false, id]
      have hz_eq : wa.getD z false = (wpre x).getD z false := by
        obtain ⟨t, ht⟩ := elim_gates_prefix m gs_post (initStat, gs_pre)
        change (wiresFrom acc.2 (List.ofFn x)).getD z false = _
        rw [ht, wiresFrom_append, getD_wiresFrom]
        rw [lwpre]; omega
      have hout_eq : wa.getD out' false = D x false := by
        have := hval_acc x
        rw [hout'] at this
        exact this
      rw [hz_eq, hout_eq]
    have hle := hmin.2 Cnew hfan_new hsame
    simp only [Circuit.size, Cnew, List.length_append, List.length_singleton] at hle
    omega
  obtain ⟨g₁, hg₁_mem, hz_g₁⟩ := hex_post
  obtain ⟨i₁, hi₁, rfl⟩ := List.mem_iff_getElem.1 hg₁_mem
  have hj₁_lt : split + i₁ < gs.length := by simp [gs_post] at hi₁; omega
  let j₁ : Fin gs.length := ⟨split + i₁, hj₁_lt⟩
  have hget_j₁ : gs_post[i₁] = gs.get j₁ := by
    simp [gs_post, List.getElem_drop, List.get_eq_getElem, j₁]
  have hz_j₁ : z ∈ (gs.get j₁).inputs := by rw [← hget_j₁]; exact hz_g₁
  have hpost_split : gs_post = gs_post.take i₁ ++ gs.get j₁ :: gs_post.drop (i₁ + 1) := by
    have h1 := List.take_append_drop i₁ gs_post
    have h2 : gs_post.drop i₁ = gs.get j₁ :: gs_post.drop (i₁ + 1) := by
      rw [← hget_j₁]
      exact List.drop_eq_getElem_cons hi₁
    rw [← h2, h1]
  set acc1 := elim m (gs_post.take i₁) (initStat, gs_pre) with hacc1
  have hacc1_slen : acc1.1.length = n + 1 + j₁.val := by
    rw [hacc1, elim_stat_len]
    simp only [initStat, List.length_ofFn, List.length_take, z, j₁]
    have : i₁ ≤ gs_post.length := le_of_lt hi₁
    omega
  have hacc1_getz : acc1.1.getD z (Sum.inl false) = Sum.inl false := by
    rw [hacc1, elim_getD m z (Sum.inl false) (gs_post.take i₁) (initStat, gs_pre)
      (by simp [initStat])]
    rw [List.getD_eq_getElem _ _ (by simp [initStat])]
    simp only [initStat, List.getElem_ofFn, ↓reduceIte]
  have hj₁_nok : NOk (gs.get j₁) := hnok _ (List.get_mem _ _)
  have hnone1 : (simplify (gs.get j₁).op (m + acc1.2.length)
      ((gs.get j₁).inputs.map fun i => acc1.1.getD i (Sum.inl false))).1 = none := by
    apply simplify_count
    · exact hj₁_nok.1.1
    · simpa using hj₁_nok.1.2
    · intro h; simpa using hj₁_nok.2 h
    · exact ⟨false, List.mem_map.2 ⟨z, hz_j₁, hacc1_getz⟩⟩
  set acc_mid := elimStep m acc1 (gs.get j₁) with hacc_mid
  have hmid_len : acc_mid.2.length = acc1.2.length := by
    show (acc1.2 ++ (simplify (gs.get j₁).op (m + acc1.2.length)
      ((gs.get j₁).inputs.map fun i => acc1.1.getD i (Sum.inl false))).1.toList).length = _
    rw [hnone1]; simp
  have hacc_from_mid : acc = elim m (gs_post.drop (i₁ + 1)) acc_mid := by
    show elim m gs_post (initStat, gs_pre) = _
    conv_lhs => rw [hpost_split, elim_append]
    rfl
  have hno_second_elim : ∀ k : ℕ, k < acc_mid.1.length →
      (∃ c, acc_mid.1.getD k (Sum.inl false) = Sum.inl c) →
      ¬ ∃ g ∈ gs_post.drop (i₁ + 1), k ∈ g.inputs := by
    intro k hk hkc hex2
    have hle1 := elim_len m (gs_post.take i₁) (initStat, gs_pre)
    rw [← hacc1] at hle1
    have hle2 := elim_len_lt m k (gs_post.drop (i₁ + 1)) acc_mid
      (fun g hg => hnok g (List.mem_of_mem_drop (List.mem_of_mem_drop hg))) hk hkc hex2
    rw [← hacc_from_mid, hmid_len] at hle2
    simp only [List.length_take, List.length_drop, hpre_len, hpost_len] at hle1 hle2
    omega
  have hno_earlier_z : ∀ i₂ : ℕ, (hi₂ : i₂ < i₁) → z ∉ (gs_post[i₂]'(lt_trans hi₂ hi₁)).inputs := by
    intro i₂ hi₂ hz₂
    have hle1 := elim_len_lt m z (gs_post.take i₁) (initStat, gs_pre)
      (fun g hg => hnok g (List.mem_of_mem_drop (List.mem_of_mem_take hg)))
      (by simp [initStat])
      ⟨false, by rw [List.getD_eq_getElem _ _ (by simp [initStat])]; simp only [initStat, List.getElem_ofFn, ↓reduceIte]⟩
      ⟨gs_post[i₂]'(lt_trans hi₂ hi₁),
        by
          have hmem : (gs_post.take i₁)[i₂]'(by simp; omega) ∈ gs_post.take i₁ :=
            List.getElem_mem _
          simpa [List.getElem_take] using hmem,
        hz₂⟩
    rw [← hacc1] at hle1
    have hle2 := elim_len m (gs_post.drop (i₁ + 1)) acc_mid
    rw [← hacc_from_mid, hmid_len] at hle2
    simp only [List.length_take, List.length_drop, hpre_len, hpost_len] at hle1 hle2
    omega
  have huniq : ∀ j : Fin gs.length, z ∈ (gs.get j).inputs → j = j₁ := by
    intro j hzj
    have hj_ge : split ≤ j.val := by
      have := hlt_all j z hzj
      omega
    have hj_sub : j.val - split < gs_post.length := by simp [gs_post]; omega
    have hget_j : gs_post[j.val - split]'hj_sub = gs.get j := by
      simp [gs_post, List.getElem_drop, List.get_eq_getElem, Nat.add_sub_of_le hj_ge]
    rcases lt_trichotomy (j.val - split) i₁ with hlt | heq | hgt
    · exact absurd (hget_j.symm ▸ hzj) (hno_earlier_z _ hlt)
    · exact Fin.ext (by simp [j₁]; omega)
    · exfalso
      apply hno_second_elim z (by simp [acc_mid, elimStep, hacc1_slen, z, j₁]; omega)
        ⟨false, by
          simp only [acc_mid, elimStep]
          rw [getD_snoc_ne _ _ _ _ (by simp [hacc1_slen, z, j₁]; omega)]
          exact hacc1_getz⟩
      have hidx : j.val - split - (i₁ + 1) < (gs_post.drop (i₁ + 1)).length := by
        simp [gs_post]; omega
      refine ⟨(gs_post.drop (i₁ + 1))[j.val - split - (i₁ + 1)]'hidx, List.getElem_mem _, ?_⟩
      have hget_drop : (gs_post.drop (i₁ + 1))[j.val - split - (i₁ + 1)]'hidx = gs.get j := by
        simp only [List.getElem_drop, gs_post, List.get_eq_getElem]
        congr 1; omega
      rw [hget_drop]
      exact hzj
  set st₁ := (simplify (gs.get j₁).op (m + acc1.2.length)
      ((gs.get j₁).inputs.map fun i => acc1.1.getD i (Sum.inl false))).2 with hst₁
  have hmid_get : acc_mid.1.getD (m + j₁.val) (Sum.inl false) = st₁ := by
    simp only [acc_mid, elimStep, ← hst₁]
    exact getD_snoc_len _ _ _ _ hacc1_slen
  have hst₁_inr : ∃ u : ℕ, st₁ = Sum.inr u := by
    cases hst : st₁ with
    | inr u => exact ⟨u, rfl⟩
    | inl c =>
      exfalso
      by_cases hjout : m + j₁.val = C.output
      · have hacc_get : acc.1.getD C.output (Sum.inl false) = Sum.inl c := by
          rw [← hjout, hacc_from_mid,
              elim_getD m (m + j₁.val) (Sum.inl false) (gs_post.drop (i₁ + 1)) acc_mid
                (by simp [acc_mid, elimStep, hacc1_slen]; omega),
              hmid_get, hst]
        rw [hout'] at hacc_get
        cases hacc_get
      · obtain ⟨j₂, hj₂⟩ := hread_all j₁ hjout
        have hj₂_gt : j₁.val < j₂.val := by
          have := hlt_all j₂ (m + j₁.val) hj₂
          omega
        apply hno_second_elim (m + j₁.val)
          (by simp [acc_mid, elimStep, hacc1_slen]; omega)
          ⟨c, by rw [hmid_get, hst]⟩
        have hidx : j₂.val - split - (i₁ + 1) < (gs_post.drop (i₁ + 1)).length := by
          have hj₂_lt : j₂.val < gs.length := j₂.isLt
          simp only [List.length_drop, gs_post, j₁] at hj₂_gt hj₂_lt ⊢; omega
        refine ⟨(gs_post.drop (i₁ + 1))[j₂.val - split - (i₁ + 1)]'hidx, List.getElem_mem _, ?_⟩
        have hget_drop : (gs_post.drop (i₁ + 1))[j₂.val - split - (i₁ + 1)]'hidx = gs.get j₂ := by
          simp only [List.getElem_drop, gs_post, List.get_eq_getElem]
          congr 1; simp only [j₁] at hj₂_gt; omega
        rw [hget_drop]
        exact hj₂
  obtain ⟨u, hu⟩ := hst₁_inr
  obtain ⟨hop, hlen2, a, b, hab, hcases⟩ :=
    simplify_inr_of_mem_false (gs.get j₁) (m + acc1.2.length) u
      (fun i => acc1.1.getD i (Sum.inl false)) hj₁_nok
      (List.mem_map.2 ⟨z, hz_j₁, hacc1_getz⟩) hu
  have hw_ex : ∃ w ∈ (gs.get j₁).inputs, w ≠ z ∧ w < n + 1 + j₁.val := by
    rcases hcases with ⟨_, hfb⟩ | ⟨hfa, _⟩
    · refine ⟨b, by rw [hab]; simp, ?_, ?_⟩
      · intro e; subst e; rw [hacc1_getz] at hfb; cases hfb
      · exact hlt_all j₁ b (by rw [hab]; simp)
    · refine ⟨a, by rw [hab]; simp, ?_, ?_⟩
      · intro e; subst e; rw [hacc1_getz] at hfa; cases hfa
      · exact hlt_all j₁ a (by rw [hab]; simp)
  exact ⟨j₁, by simp [j₁], hop, hlen2, hz_j₁, hw_ex, huniq⟩

private theorem chain_step_advance {n : ℕ} {C : Circuit}
    (split : ℕ) (S : ℕ → Prop) (j₁ : Fin (C.gates.map normGate).length)
    (hj₁_ge : split ≤ j₁.val)
    (hop : ((C.gates.map normGate).get j₁).op = GateOp.or)
    (hz_in : (n + split) ∈ ((C.gates.map normGate).get j₁).inputs)
    (huniq : ∀ j : Fin (C.gates.map normGate).length,
      (n + split) ∈ ((C.gates.map normGate).get j).inputs → j = j₁)
    (hS_lt : ∀ a, S a → a < n + split)
    (hS_noread : ∀ j : Fin (C.gates.map normGate).length, split ≤ j.val →
      ∀ a ∈ ((C.gates.map normGate).get j).inputs, ¬ S a)
    (hpre_indep : ∀ (y : Fin n → Bool) (a : ℕ), a < n + split → ¬ S a →
      (wiresFrom ((C.gates.map normGate).take split) (List.ofFn (Fin.snoc y false))).getD a false =
      (wiresFrom ((C.gates.map normGate).take split) (List.ofFn (Fin.snoc y true))).getD a false)
    (hz_true : ∀ y : Fin n → Bool,
      (wiresFrom ((C.gates.map normGate).take split)
        (List.ofFn (Fin.snoc y true))).getD (n + split) false = true) :
    let gs := C.gates.map normGate
    let S' : ℕ → Prop := fun a => S a ∨ a = n + split
    (∀ a, S' a → a < n + (j₁.val + 1)) ∧
    (∀ j : Fin gs.length, j₁.val + 1 ≤ j.val → ∀ a ∈ (gs.get j).inputs, ¬ S' a) ∧
    (∀ (y : Fin n → Bool) (a : ℕ), a < n + (j₁.val + 1) → ¬ S' a →
      (wiresFrom (gs.take (j₁.val + 1)) (List.ofFn (Fin.snoc y false))).getD a false =
      (wiresFrom (gs.take (j₁.val + 1)) (List.ofFn (Fin.snoc y true))).getD a false) ∧
    (∀ y : Fin n → Bool,
      (wiresFrom (gs.take (j₁.val + 1))
        (List.ofFn (Fin.snoc y true))).getD (n + (j₁.val + 1)) false = true) := by
  intro gs S'
  have hj₁_lt : j₁.val < gs.length := j₁.isLt
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    rcases ha with ha | rfl
    · have := hS_lt a ha; omega
    · omega
  · intro j hj a ha hSa
    rcases hSa with hSa | rfl
    · exact hS_noread j (by omega) a ha hSa
    · have := huniq j ha
      omega
  · intro y a ha hna
    have hsplit1 : gs.take (j₁.val + 1) = gs.take j₁.val ++ [gs.get j₁] := by
      rw [List.take_add_one, List.getElem?_eq_getElem j₁.isLt, Option.toList_some, List.get_eq_getElem]
    have hlen_j₁ : (gs.take j₁.val).length = j₁.val := by simp [le_of_lt hj₁_lt]
    rw [hsplit1, wiresFrom_append, wiresFrom_append]
    rw [getD_wiresFrom [gs.get j₁] _ a (by rw [length_wiresFrom, List.length_ofFn, hlen_j₁]; omega),
        getD_wiresFrom [gs.get j₁] _ a (by rw [length_wiresFrom, List.length_ofFn, hlen_j₁]; omega)]
    have htake_take : (gs.take j₁.val).take split = gs.take split := by
      rw [List.take_take, Nat.min_eq_left hj₁_ge]
    have hsplit2' : gs.take j₁.val = gs.take split ++ (gs.take j₁.val).drop split := by
      rw [← htake_take]; exact (List.take_append_drop split _).symm
    rw [hsplit2', wiresFrom_append, wiresFrom_append]
    apply wiresFrom_agree_outside S' ((gs.take j₁.val).drop split)
    · rw [length_wiresFrom, length_wiresFrom, List.length_ofFn, List.length_ofFn]
    · intro b hb
      rw [length_wiresFrom, List.length_ofFn, List.length_take]
      have hlen_s : min split gs.length = split := Nat.min_eq_left (by omega)
      rw [hlen_s]
      rcases hb with hb | rfl
      · have := hS_lt b hb; omega
      · omega
    · intro b hb hnb
      rw [length_wiresFrom, List.length_ofFn, List.length_take] at hb
      have hlen_s : min split gs.length = split := Nat.min_eq_left (by omega)
      rw [hlen_s] at hb
      have hnb1 : ¬ S b := fun h => hnb (Or.inl h)
      have hnb2 : b ≠ n + split := fun h => hnb (Or.inr h)
      exact hpre_indep y b (by omega) hnb1
    · intro g hg b hb hSb
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hg
      have hi' : split + i < j₁.val := by simp at hi; omega
      have hlt_gs : split + i < gs.length := by omega
      have hget : ((gs.take j₁.val).drop split)[i] = gs.get ⟨split + i, hlt_gs⟩ := by
        simp [List.getElem_drop, List.getElem_take, List.get_eq_getElem]
      rw [hget] at hb
      rcases hSb with hSb | rfl
      · exact hS_noread ⟨split + i, hlt_gs⟩ (by dsimp; omega) b hb hSb
      · have := huniq ⟨split + i, hlt_gs⟩ hb
        have : split + i = j₁.val := congrArg Fin.val this
        omega
    · exact hna
  · intro y
    have hsplit1 : gs.take (j₁.val + 1) = gs.take j₁.val ++ [gs.get j₁] := by
      rw [List.take_add_one, List.getElem?_eq_getElem j₁.isLt, Option.toList_some, List.get_eq_getElem]
    have hlen_j₁ : (gs.take j₁.val).length = j₁.val := by simp [le_of_lt hj₁_lt]
    rw [hsplit1, wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
    set w := wiresFrom (gs.take j₁.val) (List.ofFn (Fin.snoc y true)) with hw
    have lw : w.length = n + (j₁.val + 1) := by
      rw [hw, length_wiresFrom, List.length_ofFn, hlen_j₁]; omega
    rw [getD_snoc_len _ _ _ _ lw, hop]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    refine ⟨true, ⟨n + split, hz_in, ?_⟩, rfl⟩
    have htake_take : (gs.take j₁.val).take split = gs.take split := by
      rw [List.take_take, Nat.min_eq_left hj₁_ge]
    have hsplit2 : gs.take j₁.val = gs.take split ++ (gs.take j₁.val).drop split := by
      rw [← htake_take]; exact (List.take_append_drop split _).symm
    rw [hw, hsplit2, wiresFrom_append, getD_wiresFrom]
    · exact hz_true y
    · rw [length_wiresFrom, List.length_ofFn, List.length_take]
      have : min split gs.length = split := Nat.min_eq_left (by omega)
      omega

private theorem extend_chain {n : ℕ} {C : Circuit} {H : (Fin n → Bool) → Bool}
    (hmin : IsMinimalCircuit (n + 1) C)
    (hH : ∃ y y' : Fin n → Bool, H y ≠ H y')
    (hev : ∀ x : Fin (n + 1) → Bool,
      circuitFun (n + 1) C x = (x (Fin.last n) || H (fun i : Fin n => x i.castSucc))) :
    let gs := C.gates.map normGate
    ∀ (d : ℕ) (k : ℕ) (c : Fin (k + 1) → Fin gs.length),
      gs.length - ((c (Fin.last k)).val + 1) ≤ d →
      StrictMono c →
      (∀ i : Fin (k + 1), (gs.get (c i)).op = GateOp.or ∧ (gs.get (c i)).inputs.length = 2) →
      n ∈ (gs.get (c 0)).inputs →
      (∀ i : Fin k, n + 1 + (c i.castSucc).val ∈ (gs.get (c i.succ)).inputs) →
      (∀ j : Fin gs.length, n ∈ (gs.get j).inputs → j = c 0) →
      (∀ (i : Fin k) (j : Fin gs.length),
        n + 1 + (c i.castSucc).val ∈ (gs.get j).inputs → j = c i.succ) →
      (∃ w ∈ (gs.get (c 0)).inputs, w ≠ n ∧ w < n + 1 + (c 0).val) →
      (∀ i : Fin k, ∃ w ∈ (gs.get (c i.succ)).inputs,
        w ≠ n + 1 + (c i.castSucc).val ∧ w < n + 1 + (c i.succ).val) →
      (∀ a, (a = n ∨ ∃ i : Fin k, a = n + 1 + (c i.castSucc).val) →
        a < n + ((c (Fin.last k)).val + 1)) →
      (∀ j : Fin gs.length, (c (Fin.last k)).val + 1 ≤ j.val →
        ∀ a ∈ (gs.get j).inputs, ¬ (a = n ∨ ∃ i : Fin k, a = n + 1 + (c i.castSucc).val)) →
      (∀ (y : Fin n → Bool) (a : ℕ), a < n + ((c (Fin.last k)).val + 1) →
        ¬ (a = n ∨ ∃ i : Fin k, a = n + 1 + (c i.castSucc).val) →
        (wiresFrom (gs.take ((c (Fin.last k)).val + 1))
          (List.ofFn (Fin.snoc y false))).getD a false =
        (wiresFrom (gs.take ((c (Fin.last k)).val + 1))
          (List.ofFn (Fin.snoc y true))).getD a false) →
      (∀ y : Fin n → Bool,
        (wiresFrom (gs.take ((c (Fin.last k)).val + 1))
          (List.ofFn (Fin.snoc y true))).getD (n + ((c (Fin.last k)).val + 1)) false = true) →
      ∃ (k' : ℕ) (c' : Fin (k' + 1) → Fin gs.length),
        StrictMono c' ∧
        (c' (Fin.last k')).val + 1 = gs.length ∧
        (∀ i : Fin (k' + 1), (gs.get (c' i)).op = GateOp.or ∧ (gs.get (c' i)).inputs.length = 2) ∧
        n ∈ (gs.get (c' 0)).inputs ∧
        (∀ i : Fin k', n + 1 + (c' i.castSucc).val ∈ (gs.get (c' i.succ)).inputs) ∧
        (∀ j : Fin gs.length, n ∈ (gs.get j).inputs → j = c' 0) ∧
        (∀ (i : Fin k') (j : Fin gs.length),
          n + 1 + (c' i.castSucc).val ∈ (gs.get j).inputs → j = c' i.succ) ∧
        (∃ w ∈ (gs.get (c' 0)).inputs, w ≠ n ∧ w < n + 1 + (c' 0).val) ∧
        (∀ i : Fin k', ∃ w ∈ (gs.get (c' i.succ)).inputs,
          w ≠ n + 1 + (c' i.castSucc).val ∧ w < n + 1 + (c' i.succ).val) := by
  intro gs d
  induction d with
  | zero =>
    intro k c hd hmono hor h0 hsucc hu0 husucc hw0 hwsucc _ _ _ _
    have hlast : (c (Fin.last k)).val + 1 = gs.length := by
      have := (c (Fin.last k)).isLt; omega
    exact ⟨k, c, hmono, hlast, hor, h0, hsucc, hu0, husucc, hw0, hwsucc⟩
  | succ d ih =>
    intro k c hd hmono hor h0 hsucc hu0 husucc hw0 hwsucc hSlt hSnoread hpre hzt
    by_cases hdone : (c (Fin.last k)).val + 1 = gs.length
    · exact ⟨k, c, hmono, hdone, hor, h0, hsucc, hu0, husucc, hw0, hwsucc⟩
    · have hsplit_lt : (c (Fin.last k)).val + 1 < gs.length := by
        have := (c (Fin.last k)).isLt; omega
      let S : ℕ → Prop := fun a => a = n ∨ ∃ i : Fin k, a = n + 1 + (c i.castSucc).val
      obtain ⟨j₁, hj₁_ge, hj₁_op, hj₁_len, hj₁_in, hj₁_w, hj₁_uniq⟩ :=
        chain_step hmin hH hev ((c (Fin.last k)).val + 1) S hsplit_lt hSlt hSnoread hpre hzt
      obtain ⟨hSlt', hSnoread', hpre', hzt'⟩ :=
        chain_step_advance ((c (Fin.last k)).val + 1) S j₁ hj₁_ge hj₁_op hj₁_in hj₁_uniq
          hSlt hSnoread hpre hzt
      let c' : Fin (k + 2) → Fin gs.length := Fin.snoc c j₁
      have hc'_last : c' (Fin.last (k + 1)) = j₁ := by simp [c']
      have hc'_zero : c' 0 = c 0 := by
        have h0eq : (0 : Fin (k + 2)) = (0 : Fin (k + 1)).castSucc := rfl
        rw [h0eq]; simp [c']
      have hc'_cast : ∀ i : Fin (k + 1), c' i.castSucc = c i := fun i => by simp [c']
      have hS'_iff : ∀ a,
          (a = n ∨ ∃ i : Fin (k + 1), a = n + 1 + (c' i.castSucc).val) ↔
          (S a ∨ a = n + ((c (Fin.last k)).val + 1)) := by
        intro a
        constructor
        · rintro (rfl | ⟨i, rfl⟩)
          · exact Or.inl (Or.inl rfl)
          · refine Fin.lastCases ?_ ?_ i
            · right; rw [hc'_cast]; omega
            · intro i'; left; right; exact ⟨i', by rw [hc'_cast]⟩
        · rintro ((rfl | ⟨i, rfl⟩) | rfl)
          · exact Or.inl rfl
          · right; exact ⟨i.castSucc, by rw [hc'_cast]⟩
          · right; exact ⟨Fin.last k, by rw [hc'_cast]; omega⟩
      apply ih (k + 1) c'
      · rw [hc'_last]; omega
      · intro a b hab
        revert hab
        refine Fin.lastCases ?_ ?_ b
        · refine Fin.lastCases ?_ ?_ a
          · intro hlt; exact absurd hlt (lt_irrefl _)
          · intro a' _
            rw [hc'_last, hc'_cast]
            have hle : c a' ≤ c (Fin.last k) := hmono.monotone (Fin.le_last a')
            exact lt_of_le_of_lt hle (by exact Nat.lt_of_succ_le hj₁_ge)
        · intro b'
          refine Fin.lastCases ?_ ?_ a
          · intro hlt; exact absurd (Fin.le_last b'.castSucc) (not_le_of_gt hlt)
          · intro a' hlt
            rw [hc'_cast, hc'_cast]
            exact hmono (by simpa using hlt)
      · intro i
        refine Fin.lastCases ?_ ?_ i
        · rw [hc'_last]; exact ⟨hj₁_op, hj₁_len⟩
        · intro i'; rw [hc'_cast]; exact hor i'
      · rw [hc'_zero]; exact h0
      · intro i
        refine Fin.lastCases ?_ ?_ i
        · rw [hc'_cast, Fin.succ_last, hc'_last]
          have hadd : n + 1 + (c (Fin.last k)).val = n + ((c (Fin.last k)).val + 1) := by omega
          rw [hadd]
          exact hj₁_in
        · intro i'
          rw [hc'_cast]
          have h1 : i'.castSucc.succ = i'.succ.castSucc := rfl
          rw [h1, hc'_cast]
          exact hsucc i'
      · intro j hj; rw [hc'_zero]; exact hu0 j hj
      · intro i j hj
        revert hj
        refine Fin.lastCases ?_ ?_ i
        · intro hj
          rw [hc'_cast] at hj
          rw [Fin.succ_last, hc'_last]
          have hadd : n + 1 + (c (Fin.last k)).val = n + ((c (Fin.last k)).val + 1) := by omega
          rw [hadd] at hj
          exact hj₁_uniq j hj
        · intro i' hj
          rw [hc'_cast] at hj
          have h1 : i'.castSucc.succ = i'.succ.castSucc := rfl
          rw [h1, hc'_cast]
          exact husucc i' j hj
      · rw [hc'_zero]; exact hw0
      · intro i
        refine Fin.lastCases ?_ ?_ i
        · rw [hc'_cast, Fin.succ_last, hc'_last]
          obtain ⟨w, hw, hne, hlt⟩ := hj₁_w
          exact ⟨w, hw, by omega, hlt⟩
        · intro i'
          rw [hc'_cast]
          have h1 : i'.castSucc.succ = i'.succ.castSucc := rfl
          rw [h1, hc'_cast]
          exact hwsucc i'
      · intro a ha; rw [hc'_last]; exact hSlt' a ((hS'_iff a).1 ha)
      · intro j hj a ha hSa
        rw [hc'_last] at hj
        exact hSnoread' j hj a ha ((hS'_iff a).1 hSa)
      · intro y a ha hna
        rw [hc'_last] at ha ⊢
        exact hpre' y a ha (fun h => hna ((hS'_iff a).2 h))
      · intro y; rw [hc'_last]; exact hzt' y

theorem PEqualNP.Outside.L_meta_568 :
    ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (H : (Fin n → Bool) → Bool),
      PEqualNP.MetaComplexity.IsMinimalCircuit (n + 1) C →
      (∃ y y' : Fin n → Bool, H y ≠ H y') →
      (∀ x : Fin (n + 1) → Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C x =
        (x (Fin.last n) || H (fun i : Fin n => x i.castSucc))) →
      ∃ (k : ℕ) (c : Fin (k + 1) → Fin C.gates.length),
        StrictMono c ∧
        (c (Fin.last k)).val + 1 = C.gates.length ∧
        C.output = n + 1 + (c (Fin.last k)).val ∧
        (∀ i : Fin (k + 1), (C.gates.get (c i)).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
          (C.gates.get (c i)).inputs.length = 2) ∧
        n ∈ (C.gates.get (c 0)).inputs ∧
        (∀ i : Fin k, n + 1 + (c i.castSucc).val ∈ (C.gates.get (c i.succ)).inputs) ∧
        (∀ j : Fin C.gates.length,
          ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
            (C.gates.get j).inputs.head? = some n ∨
           (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧
            n ∈ (C.gates.get j).inputs) → j = c 0) ∧
        (∀ (i : Fin k) (j : Fin C.gates.length),
          ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
            (C.gates.get j).inputs.head? = some (n + 1 + (c i.castSucc).val) ∨
           (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧
            (n + 1 + (c i.castSucc).val) ∈ (C.gates.get j).inputs) → j = c i.succ) ∧
        (∀ j : Fin C.gates.length,
          Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧
            ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
              (C.gates.get j).inputs.head? = some a ∨
             (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧
              a ∈ (C.gates.get j).inputs)) n (n + 1 + j.val) ↔
            ∃ i : Fin (k + 1), c i = j) ∧
        (∃ w ∈ (C.gates.get (c 0)).inputs, w ≠ n ∧ w < n + 1 + (c 0).val ∧
          ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧
            ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
              (C.gates.get j).inputs.head? = some a ∨
             (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧
              a ∈ (C.gates.get j).inputs)) n w) ∧
        (∀ i : Fin k, ∃ w ∈ (C.gates.get (c i.succ)).inputs,
          w ≠ n + 1 + (c i.castSucc).val ∧ w ≠ n ∧ w < n + 1 + (c i.succ).val ∧
          ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧
            ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
              (C.gates.get j).inputs.head? = some a ∨
             (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧
              a ∈ (C.gates.get j).inputs)) n w) := by
  intro n C H hmin hH hev
  set gs := C.gates.map normGate with hgs_def
  have hgs_len : gs.length = C.gates.length := by simp [hgs_def]
  have hnc := eval_nonconst hH hev
  have hpos := gates_pos hH hev
  have hout_last := minimal_output_last hmin hnc hpos
  have hlt_all := minimal_inputs_lt hmin hnc
  have h0_pre : ∀ (y : Fin n → Bool) (a : ℕ), a < n + 0 → ¬ False →
      (wiresFrom (gs.take 0) (List.ofFn (Fin.snoc y false))).getD a false =
      (wiresFrom (gs.take 0) (List.ofFn (Fin.snoc y true))).getD a false := by
    intro y a ha _
    simp only [List.take_zero, wiresFrom_nil]
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega),
      List.getElem_ofFn, List.getElem_ofFn]
    have hlt : a < n := by omega
    rw [snoc_val_lt y false hlt, snoc_val_lt y true hlt]
  have h0_zt : ∀ y : Fin n → Bool,
      (wiresFrom (gs.take 0) (List.ofFn (Fin.snoc y true))).getD (n + 0) false = true := by
    intro y
    simp only [List.take_zero, wiresFrom_nil, Nat.add_zero]
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    exact snoc_val_last y true
  obtain ⟨c0, hc0_ge, hc0_op, hc0_len, hc0_in, hc0_w, hc0_uniq⟩ :=
    chain_step hmin hH hev 0 (fun _ => False) (by rw [← hgs_def, hgs_len]; exact hpos)
      (fun _ h => h.elim) (fun _ _ _ _ h => h.elim) h0_pre h0_zt
  obtain ⟨hS0_lt, hS0_nr, hS0_pre, hS0_zt⟩ :=
    chain_step_advance 0 (fun _ => False) c0 hc0_ge hc0_op hc0_in hc0_uniq
      (fun _ h => h.elim) (fun _ _ _ _ h => h.elim) h0_pre h0_zt
  have hS0_iff : ∀ a, (a = n ∨ ∃ i : Fin 0, a = n + 1 + ((fun _ : Fin 1 => c0) i.castSucc).val) ↔
      (False ∨ a = n + 0) := by
    intro a; simp
  obtain ⟨k, cgs, hmono_gs, hlast_gs, hor_gs, h0_gs, hsucc_gs, hu0_gs, husucc_gs, hw0_gs, hwsucc_gs⟩ :=
    extend_chain hmin hH hev gs.length 0 (fun _ => c0) (Nat.sub_le _ _)
      (fun a b hab => absurd (Fin.ext (by omega) : a = b) (ne_of_lt hab))
      (fun _ => ⟨hc0_op, hc0_len⟩) hc0_in (fun i => i.elim0) hc0_uniq (fun i => i.elim0)
      hc0_w (fun i => i.elim0)
      (fun a ha => hS0_lt a ((hS0_iff a).1 ha))
      (fun j hj a ha hSa => hS0_nr j hj a ha ((hS0_iff a).1 hSa))
      (fun y a ha hna => hS0_pre y a ha (fun h => hna ((hS0_iff a).2 h)))
      hS0_zt
  let c : Fin (k + 1) → Fin C.gates.length := fun i => Fin.cast hgs_len (cgs i)
  have hget_gs : ∀ j : Fin C.gates.length,
      gs.get (Fin.cast hgs_len.symm j) = normGate (C.gates.get j) := by
    intro j
    simp [gs, List.get_eq_getElem]
  have hc_get : ∀ i : Fin (k + 1), C.gates.get (c i) = gs.get (cgs i) := by
    intro i
    have h1 : gs.get (cgs i) = normGate (C.gates.get (c i)) := by
      have := hget_gs (c i)
      simpa [c] using this
    have h2 := normGate_eq_of_or (C.gates.get (c i)) (h1 ▸ (hor_gs i).1)
    exact (h1.trans h2.2).symm
  have hc_val : ∀ i : Fin (k + 1), (c i).val = (cgs i).val := fun _ => rfl
  have hmono : StrictMono c := fun a b hab => by
    change (cgs a).val < (cgs b).val
    exact hmono_gs hab
  have hlast : (c (Fin.last k)).val + 1 = C.gates.length := by
    rw [hc_val, hlast_gs, hgs_len]
  have hout : C.output = n + 1 + (c (Fin.last k)).val := by
    rw [hout_last]; omega
  have hor : ∀ i : Fin (k + 1),
      (C.gates.get (c i)).op = GateOp.or ∧ (C.gates.get (c i)).inputs.length = 2 := by
    intro i; rw [hc_get i]; exact hor_gs i
  have h0 : n ∈ (C.gates.get (c 0)).inputs := by
    rw [hc_get 0]; exact h0_gs
  have hsucc : ∀ i : Fin k, n + 1 + (c i.castSucc).val ∈ (C.gates.get (c i.succ)).inputs := by
    intro i; rw [hc_get i.succ, hc_val]; exact hsucc_gs i
  have heff_iff : ∀ (j : Fin C.gates.length) (a : ℕ),
      ((C.gates.get j).op = GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨
       (C.gates.get j).op ≠ GateOp.not ∧ a ∈ (C.gates.get j).inputs) ↔
      a ∈ (gs.get (Fin.cast hgs_len.symm j)).inputs := by
    intro j a
    rw [hget_gs j, mem_normGate_inputs_iff]
  have hu0 : ∀ j : Fin C.gates.length,
      ((C.gates.get j).op = GateOp.not ∧ (C.gates.get j).inputs.head? = some n ∨
       (C.gates.get j).op ≠ GateOp.not ∧ n ∈ (C.gates.get j).inputs) → j = c 0 := by
    intro j hj
    have h1 := hu0_gs (Fin.cast hgs_len.symm j) ((heff_iff j n).1 hj)
    exact Fin.ext (by simpa [c] using congrArg Fin.val h1)
  have husucc : ∀ (i : Fin k) (j : Fin C.gates.length),
      ((C.gates.get j).op = GateOp.not ∧
        (C.gates.get j).inputs.head? = some (n + 1 + (c i.castSucc).val) ∨
       (C.gates.get j).op ≠ GateOp.not ∧
        (n + 1 + (c i.castSucc).val) ∈ (C.gates.get j).inputs) → j = c i.succ := by
    intro i j hj
    have h1 := husucc_gs i (Fin.cast hgs_len.symm j) ((heff_iff j _).1 hj)
    exact Fin.ext (by simpa [c] using congrArg Fin.val h1)
  let edge : ℕ → ℕ → Prop := fun a b =>
    ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧
      ((C.gates.get j).op = GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨
       (C.gates.get j).op ≠ GateOp.not ∧ a ∈ (C.gates.get j).inputs)
  have hreach_all : ∀ u : ℕ, Relation.TransGen edge n u ↔ ∃ i : Fin (k + 1), u = n + 1 + (c i).val := by
    intro u
    constructor
    · intro htr
      induction htr with
      | single h =>
        obtain ⟨j, rfl, hj⟩ := h
        exact ⟨0, by rw [hu0 j hj]⟩
      | tail _ h ih =>
        obtain ⟨i, rfl⟩ := ih
        obtain ⟨j, rfl, hj⟩ := h
        revert hj
        refine Fin.lastCases ?_ ?_ i
        · intro hj
          exfalso
          have hlt := hlt_all (Fin.cast hgs_len.symm j) (n + 1 + (c (Fin.last k)).val)
            ((heff_iff j _).1 hj)
          have hjlt := j.isLt
          simp only [Fin.val_cast] at hlt
          omega
        · intro i' hj
          exact ⟨i'.succ, by rw [husucc i' j hj]⟩
    · rintro ⟨i, rfl⟩
      induction i using Fin.induction with
      | zero =>
        exact Relation.TransGen.single ⟨c 0, rfl, Or.inr ⟨by rw [(hor 0).1]; simp, h0⟩⟩
      | succ i ih =>
        exact Relation.TransGen.tail ih
          ⟨c i.succ, rfl, Or.inr ⟨by rw [(hor i.succ).1]; simp, hsucc i⟩⟩
  have hreach : ∀ j : Fin C.gates.length,
      Relation.TransGen edge n (n + 1 + j.val) ↔ ∃ i : Fin (k + 1), c i = j := by
    intro j
    rw [hreach_all]
    constructor
    · rintro ⟨i, hi⟩; exact ⟨i, Fin.ext (by omega)⟩
    · rintro ⟨i, rfl⟩; exact ⟨i, rfl⟩
  have hw0 : ∃ w ∈ (C.gates.get (c 0)).inputs,
      w ≠ n ∧ w < n + 1 + (c 0).val ∧ ¬ Relation.TransGen edge n w := by
    obtain ⟨w, hw, hne, hlt⟩ := hw0_gs
    rw [← hc_val 0] at hlt
    refine ⟨w, by rw [hc_get 0]; exact hw, hne, hlt, ?_⟩
    intro htr
    obtain ⟨i, rfl⟩ := (hreach_all w).1 htr
    have hle : (c 0).val ≤ (c i).val := hmono.monotone (Fin.zero_le i)
    omega
  have hwsucc : ∀ i : Fin k, ∃ w ∈ (C.gates.get (c i.succ)).inputs,
      w ≠ n + 1 + (c i.castSucc).val ∧ w ≠ n ∧ w < n + 1 + (c i.succ).val ∧
      ¬ Relation.TransGen edge n w := by
    intro i
    obtain ⟨w, hw, hne, hlt⟩ := hwsucc_gs i
    rw [← hc_val i.castSucc] at hne
    rw [← hc_val i.succ] at hlt
    have hw_in : w ∈ (C.gates.get (c i.succ)).inputs := by rw [hc_get i.succ]; exact hw
    have hne_n : w ≠ n := by
      intro e
      subst e
      have h1 := hu0 (c i.succ) (Or.inr ⟨by rw [(hor i.succ).1]; simp, hw_in⟩)
      have h2 : (0 : Fin (k + 1)) < i.succ := Fin.succ_pos i
      exact absurd (congrArg Fin.val h1) (ne_of_gt (hmono h2))
    refine ⟨w, hw_in, hne, hne_n, hlt, ?_⟩
    intro htr
    obtain ⟨r, rfl⟩ := (hreach_all w).1 htr
    have hr_lt : r < i.succ := by
      by_contra hge
      have hle : (c i.succ).val ≤ (c r).val := hmono.monotone (not_lt.1 hge)
      omega
    have hr_ne : r ≠ i.castSucc := by
      intro e; subst e; exact hne rfl
    have hr_lt_k : r.val < k := by
      have h1 : r.val < i.succ.val := hr_lt
      simp only [Fin.val_succ] at h1
      have h2 := i.isLt
      omega
    let r' : Fin k := ⟨r.val, hr_lt_k⟩
    have hr_eq : r = r'.castSucc := Fin.ext rfl
    rw [hr_eq] at hw_in
    have hceq := husucc r' (c i.succ) (Or.inr ⟨by rw [(hor i.succ).1]; simp, hw_in⟩)
    have hreq : i.succ = r'.succ := hmono.injective hceq
    have : r'.val = i.val := by
      have := congrArg Fin.val hreq
      simp at this; omega
    exact hr_ne (Fin.ext (by simpa [r'] using this))
  exact ⟨k, c, hmono, hlast, hout, hor, h0, hsucc, hu0, husucc, hreach, hw0, hwsucc⟩
