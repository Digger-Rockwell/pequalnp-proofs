import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_749_aux

open PEqualNP.CircuitLowerBounds

lemma wires_nil (xs : List Bool) :
    Circuit.wires ⟨[], 0⟩ xs = xs := rfl

lemma wires_cons (g : Gate) (gs : List Gate) (xs : List Bool) :
    Circuit.wires ⟨g :: gs, 0⟩ xs =
      Circuit.wires ⟨gs, 0⟩ (xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]) := rfl

lemma wires_append_singleton (gs : List Gate) (g : Gate) (xs : List Bool) :
    Circuit.wires ⟨gs ++ [g], 0⟩ xs =
      Circuit.wires ⟨gs, 0⟩ xs ++
        [g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨gs, 0⟩ xs).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]

lemma getD_append_singleton_mono (w1 w2 : List Bool) (b1 b2 : Bool)
    (hlen : w1.length = w2.length)
    (hw : ∀ i, w1.getD i false = true → w2.getD i false = true)
    (hb : b1 = true → b2 = true) :
    ∀ i, (w1 ++ [b1]).getD i false = true → (w2 ++ [b2]).getD i false = true := by
  intro i hi
  by_cases hlt : i < w1.length
  · have hlt2 : i < w2.length := hlen ▸ hlt
    have h1 : (w1 ++ [b1]).getD i false = w1.getD i false := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
    have h2 : (w2 ++ [b2]).getD i false = w2.getD i false := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt2]
    rw [h2]
    exact hw i (h1 ▸ hi)
  · by_cases heq : i = w1.length
    · subst heq
      have h1 : (w1 ++ [b1]).getD w1.length false = b1 := by
        simp [List.getD_eq_getElem?_getD]
      have h2 : (w2 ++ [b2]).getD w1.length false = b2 := by
        rw [hlen]
        simp [List.getD_eq_getElem?_getD]
      rw [h2]
      exact hb (h1 ▸ hi)
    · have hgt : w1.length + 1 ≤ i := by omega
      have h1 : (w1 ++ [b1]).getD i false = false := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
        · rfl
        · simp; omega
      rw [h1] at hi
      exact Bool.noConfusion hi

lemma gate_eval_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (w1 w2 : List Bool) (hw : ∀ i, w1.getD i false = true → w2.getD i false = true) :
    g.op.eval (g.inputs.map fun i => w1.getD i false) = true →
      g.op.eval (g.inputs.map fun i => w2.getD i false) = true := by
  rcases hg with h | h
  · rw [h]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂]
    intro h1 i hi
    exact hw i (h1 i hi)
  · rw [h]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨b, ⟨i, hi, rfl⟩, hb⟩
    exact ⟨w2.getD i false, ⟨i, hi, rfl⟩, hw i hb⟩

lemma wires_mono (gs : List Gate) (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (xs ys : List Bool), xs.length = ys.length →
      (∀ i, xs.getD i false = true → ys.getD i false = true) →
      (Circuit.wires ⟨gs, 0⟩ xs).length = (Circuit.wires ⟨gs, 0⟩ ys).length ∧
      ∀ w, (Circuit.wires ⟨gs, 0⟩ xs).getD w false = true →
        (Circuit.wires ⟨gs, 0⟩ ys).getD w false = true := by
  induction gs with
  | nil =>
    intro xs ys hlen hxy
    exact ⟨hlen, hxy⟩
  | cons g gs ih =>
    intro xs ys hlen hxy
    have hg : g.op = GateOp.and ∨ g.op = GateOp.or := hmono g (List.mem_cons_self ..)
    have hgs : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or :=
      fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')
    have hb := gate_eval_mono g hg xs ys hxy
    have hlen' : (xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]).length =
        (ys ++ [g.op.eval (g.inputs.map fun i => ys.getD i false)]).length := by
      simp [hlen]
    have hxy' := getD_append_singleton_mono xs ys
      (g.op.eval (g.inputs.map fun i => xs.getD i false))
      (g.op.eval (g.inputs.map fun i => ys.getD i false)) hlen hxy hb
    simpa [wires_cons] using ih hgs _ _ hlen' hxy'

lemma ofFn_mono {n : ℕ} (y x : Fin n → Bool) (h : ∀ p : Fin n, y p = true → x p = true) :
    ∀ i, (List.ofFn y).getD i false = true → (List.ofFn x).getD i false = true := by
  intro i hi
  by_cases hlt : i < n
  · simp [List.getD_eq_getElem?_getD, hlt] at hi ⊢
    exact h ⟨i, hlt⟩ hi
  · simp [List.getD_eq_getElem?_getD, hlt] at hi

lemma main
    (n : ℕ) (C C' : List Gate) (X : Set (Fin n → Bool)) (y : Fin n → Bool)
    (hC_ops : ∀ g ∈ C, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hy : y ∈ X)
    (hy_min : ∀ u ∈ X, ∀ p : Fin n, y p = true → u p = true)
    (hC_not : ∀ (j1 : ℕ) (g1 : Gate), C[j1]? = some g1 → g1.op = GateOp.not →
      ((g1.inputs.map (fun i1 => (Circuit.wires ⟨C.take j1, 0⟩ (List.ofFn y)).getD i1 false)).headD false) = false →
      ∀ z ∈ X, ((g1.inputs.map (fun i2 => (Circuit.wires ⟨C.take j1, 0⟩ (List.ofFn z)).getD i2 false)).headD false) = false)
    (hlen : C'.length = C.length)
    (hC' : ∀ (j2 : ℕ) (g2 : Gate), C[j2]? = some g2 →
      (g2.op = GateOp.not →
        (((g2.inputs.map (fun i3 => (Circuit.wires ⟨C.take j2, 0⟩ (List.ofFn y)).getD i3 false)).headD false) = true →
          C'[j2]? = some ({ op := GateOp.or, inputs := [] } : Gate)) ∧
        (((g2.inputs.map (fun i4 => (Circuit.wires ⟨C.take j2, 0⟩ (List.ofFn y)).getD i4 false)).headD false) = false →
          C'[j2]? = some ({ op := GateOp.and, inputs := [] } : Gate))) ∧
      (g2.op ≠ GateOp.not → C'[j2]? = some g2)) :
    ∀ x ∈ X, ∀ w : ℕ,
      (Circuit.wires ⟨C', 0⟩ (List.ofFn x)).getD w false =
        (Circuit.wires ⟨C, 0⟩ (List.ofFn x)).getD w false := by
  have hC'_mono : ∀ g' ∈ C', g'.op = GateOp.and ∨ g'.op = GateOp.or := by
    intro g' hg'
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hg'
    have hjlt' : j < C'.length := by
      by_contra hge
      rw [List.getElem?_eq_none (Nat.le_of_not_lt hge)] at hj
      cases hj
    have hjlt : j < C.length := hlen ▸ hjlt'
    have hCj : C[j]? = some C[j] := List.getElem?_eq_getElem hjlt
    obtain ⟨hnot_spec, hne_spec⟩ := hC' j C[j] hCj
    by_cases hop : C[j].op = GateOp.not
    · obtain ⟨ht, hf⟩ := hnot_spec hop
      cases hval : (C[j].inputs.map (fun i => (Circuit.wires ⟨C.take j, 0⟩ (List.ofFn y)).getD i false)).headD false
      · have hEq := hf hval
        rw [hj] at hEq
        cases Option.some.inj hEq
        exact Or.inl rfl
      · have hEq := ht hval
        rw [hj] at hEq
        cases Option.some.inj hEq
        exact Or.inr rfl
    · have hEq := hne_spec hop
      rw [hj] at hEq
      cases Option.some.inj hEq
      have hmem : C[j] ∈ C := List.getElem_mem hjlt
      rcases (hC_ops C[j] hmem).1 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact False.elim (hop h)
  have hpref : ∀ m ≤ C.length, ∀ x ∈ X,
      Circuit.wires ⟨C'.take m, 0⟩ (List.ofFn x) =
        Circuit.wires ⟨C.take m, 0⟩ (List.ofFn x) := by
    intro m
    induction m with
    | zero =>
      intro _ x _
      simp [wires_nil]
    | succ m ih =>
      intro hm x hx
      have hmlt : m < C.length := Nat.lt_of_succ_le hm
      have hmlt' : m < C'.length := hlen ▸ hmlt
      have hCm : C[m]? = some C[m] := List.getElem?_eq_getElem hmlt
      have hCm' : C'[m]? = some C'[m] := List.getElem?_eq_getElem hmlt'
      have htakeC : C.take (m + 1) = C.take m ++ [C[m]] := by
        rw [List.take_add_one, hCm]
        rfl
      have htakeC' : C'.take (m + 1) = C'.take m ++ [C'[m]] := by
        rw [List.take_add_one, hCm']
        rfl
      have ihx : Circuit.wires ⟨C'.take m, 0⟩ (List.ofFn x) =
          Circuit.wires ⟨C.take m, 0⟩ (List.ofFn x) :=
        ih (Nat.le_of_lt hmlt) x hx
      have ihy : Circuit.wires ⟨C'.take m, 0⟩ (List.ofFn y) =
          Circuit.wires ⟨C.take m, 0⟩ (List.ofFn y) :=
        ih (Nat.le_of_lt hmlt) y hy
      rw [htakeC', htakeC, wires_append_singleton, wires_append_singleton, ihx]
      congr 2
      obtain ⟨hnot_spec, hne_spec⟩ := hC' m C[m] hCm
      by_cases hop : C[m].op = GateOp.not
      · obtain ⟨ht, hf⟩ := hnot_spec hop
        cases hval : (C[m].inputs.map (fun i => (Circuit.wires ⟨C.take m, 0⟩ (List.ofFn y)).getD i false)).headD false
        · have hEq := hf hval
          rw [hCm'] at hEq
          have hg' : C'[m] = { op := GateOp.and, inputs := [] } := Option.some.inj hEq
          have hvalx := hC_not m C[m] hCm hop hval x hx
          rw [hg', hop]
          simp only [GateOp.eval, List.map_nil, List.all_nil, hvalx]
          rfl
        · have hEq := ht hval
          rw [hCm'] at hEq
          have hg' : C'[m] = { op := GateOp.or, inputs := [] } := Option.some.inj hEq
          have hvalx : (C[m].inputs.map (fun i => (Circuit.wires ⟨C.take m, 0⟩ (List.ofFn x)).getD i false)).headD false = true := by
            cases hinputs : C[m].inputs with
            | nil =>
              rw [hinputs] at hval
              simp at hval
            | cons i0 rest =>
              rw [hinputs] at hval
              simp only [List.map_cons, List.headD_cons] at hval ⊢
              have hmono_m : ∀ g' ∈ C'.take m, g'.op = GateOp.and ∨ g'.op = GateOp.or :=
                fun g' hg' => hC'_mono g' (List.mem_of_mem_take hg')
              have hwy : (Circuit.wires ⟨C'.take m, 0⟩ (List.ofFn y)).getD i0 false = true := by
                rw [ihy]
                exact hval
              have hwx := (wires_mono (C'.take m) hmono_m (List.ofFn y) (List.ofFn x)
                (by simp) (ofFn_mono y x (hy_min x hx))).2 i0 hwy
              rwa [ihx] at hwx
          rw [hg', hop]
          simp only [GateOp.eval, List.map_nil, List.any_nil, hvalx]
          rfl
      · have hEq := hne_spec hop
        rw [hCm'] at hEq
        have hg' : C'[m] = C[m] := Option.some.inj hEq
        rw [hg']
  intro x hx w
  have hfull := hpref C.length (Nat.le_refl _) x hx
  have htakeC : C.take C.length = C := List.take_length
  have htakeC' : C'.take C.length = C' := by
    rw [← hlen]
    exact List.take_length
  rw [htakeC', htakeC] at hfull
  rw [hfull]

end PEqualNP.Outside.L_meta_749_aux

theorem PEqualNP.Outside.L_meta_749 :
    ∀ (n : ℕ) (C C' : List PEqualNP.CircuitLowerBounds.Gate) (X : Set (Fin n → Bool)) (y : Fin n → Bool), (∀ g ∈ C, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → y ∈ X → (∀ u ∈ X, ∀ p : Fin n, y p = true → u p = true) → (∀ (j1 : ℕ) (g1 : PEqualNP.CircuitLowerBounds.Gate), C[j1]? = some g1 → g1.op = PEqualNP.CircuitLowerBounds.GateOp.not → ((g1.inputs.map (fun i1 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j1, 0⟩ (List.ofFn y)).getD i1 false)).headD false) = false → ∀ z ∈ X, ((g1.inputs.map (fun i2 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j1, 0⟩ (List.ofFn z)).getD i2 false)).headD false) = false) → C'.length = C.length → (∀ (j2 : ℕ) (g2 : PEqualNP.CircuitLowerBounds.Gate), C[j2]? = some g2 → (g2.op = PEqualNP.CircuitLowerBounds.GateOp.not → (((g2.inputs.map (fun i3 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j2, 0⟩ (List.ofFn y)).getD i3 false)).headD false) = true → C'[j2]? = some ({ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] } : PEqualNP.CircuitLowerBounds.Gate)) ∧ (((g2.inputs.map (fun i4 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j2, 0⟩ (List.ofFn y)).getD i4 false)).headD false) = false → C'[j2]? = some ({ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } : PEqualNP.CircuitLowerBounds.Gate))) ∧ (g2.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → C'[j2]? = some g2)) → ∀ x ∈ X, ∀ w : ℕ, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C', 0⟩ (List.ofFn x)).getD w false = (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C, 0⟩ (List.ofFn x)).getD w false :=
  PEqualNP.Outside.L_meta_749_aux.main
