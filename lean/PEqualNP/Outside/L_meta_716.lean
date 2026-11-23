import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_716_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def shiftWire (n w : ℕ) : ℕ :=
  if w < n then w else w + 1

def shiftGate (n : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (shiftWire n)⟩

def evalStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma length_foldl_evalStep (gs : List Gate) (x : List Bool) :
    (gs.foldl evalStep x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp [List.foldl_cons, ih, evalStep]
    omega

lemma getD_append_left (l1 l2 : List Bool) (i : ℕ) (hi : i < l1.length) :
    (l1 ++ l2).getD i false = l1.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_single_eq (l : List Bool) (b : Bool) :
    (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_eq_false_of_le (l : List Bool) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma ofFn_eq_append_last {n : ℕ} (x : Fin (n + 1) → Bool) :
    List.ofFn x = List.ofFn (fun i : Fin n => x i.castSucc) ++ [x (Fin.last n)] := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_ofFn, List.getElem_append, List.length_ofFn]
    split_ifs with hi
    · rfl
    · have hi' : i = n := by
        simp only [List.length_ofFn] at h1
        omega
      subst hi'
      simp [Fin.last]

lemma foldl_shiftGate_inv (n : ℕ) (gs : List Gate) (w1 w2 : List Bool)
    (hlen : w2.length = w1.length + 1) (hn : n ≤ w1.length)
    (heq : ∀ i, w2.getD (shiftWire n i) false = w1.getD i false) :
    (∀ i, ((gs.map (shiftGate n)).foldl evalStep w2).getD (shiftWire n i) false =
      (gs.foldl evalStep w1).getD i false) ∧
    ((gs.map (shiftGate n)).foldl evalStep w2).getD n false = w2.getD n false := by
  induction gs generalizing w1 w2 with
  | nil => exact ⟨heq, rfl⟩
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hmap : (shiftGate n g).inputs.map (fun i => w2.getD i false) =
        g.inputs.map (fun i => w1.getD i false) := by
      simp only [shiftGate, List.map_map, Function.comp_def, heq]
    have hstep2 : evalStep w2 (shiftGate n g) =
        w2 ++ [g.op.eval (g.inputs.map fun i => w1.getD i false)] := by
      unfold evalStep
      rw [hmap]
      rfl
    have hstep1 : evalStep w1 g =
        w1 ++ [g.op.eval (g.inputs.map fun i => w1.getD i false)] := rfl
    set b := g.op.eval (g.inputs.map fun i => w1.getD i false)
    rw [hstep1, hstep2]
    have hlen' : (w2 ++ [b]).length = (w1 ++ [b]).length + 1 := by simp; omega
    have hn' : n ≤ (w1 ++ [b]).length := by simp; omega
    have heq' : ∀ i, (w2 ++ [b]).getD (shiftWire n i) false = (w1 ++ [b]).getD i false := by
      intro i
      by_cases h1 : i < w1.length
      · have h2 : shiftWire n i < w2.length := by
          unfold shiftWire
          split_ifs <;> omega
        rw [getD_append_left w2 [b] _ h2, getD_append_left w1 [b] _ h1, heq i]
      · by_cases h2 : i = w1.length
        · subst h2
          have hsw : shiftWire n w1.length = w2.length := by
            unfold shiftWire
            split_ifs <;> omega
          rw [hsw, getD_append_single_eq, getD_append_single_eq]
        · have h3 : (w1 ++ [b]).length ≤ i := by simp; omega
          have h4 : (w2 ++ [b]).length ≤ shiftWire n i := by
            unfold shiftWire
            simp only [List.length_append, List.length_singleton]
            split_ifs <;> omega
          rw [getD_eq_false_of_le _ _ h4, getD_eq_false_of_le _ _ h3]
    have hih := ih (w1 ++ [b]) (w2 ++ [b]) hlen' hn' heq'
    refine ⟨hih.1, ?_⟩
    rw [hih.2, getD_append_left w2 [b] n (by omega)]

lemma getD_safeWire (w extra : List Bool) (n m o : ℕ) (hw : w.length = n + 1 + m)
    (he : extra.length ≤ 10) :
    (w ++ extra).getD (if o < n + m then shiftWire n o else n + 1 + m + 10) false =
      w.getD (if o < n + m then shiftWire n o else n + 1 + m + 10) false := by
  split_ifs with h
  · apply getD_append_left
    unfold shiftWire
    split_ifs <;> omega
  · rw [getD_eq_false_of_le (w ++ extra) _ (by simp; omega),
      getD_eq_false_of_le w _ (by omega)]

lemma eval_base_wires (n : ℕ) (C : Circuit) (x : Fin (n + 1) → Bool) :
    let w := (C.gates.map (shiftGate n)).foldl evalStep (List.ofFn x)
    let o' := if C.output < n + C.gates.length then shiftWire n C.output
      else n + 1 + C.gates.length + 10
    w.length = n + 1 + C.gates.length ∧
    w.getD n false = x (Fin.last n) ∧
    w.getD o' false = C.eval (List.ofFn (fun i : Fin n => x i.castSucc)) := by
  intro w o'
  have hlen_w : w.length = n + 1 + C.gates.length := by
    dsimp only [w]
    rw [length_foldl_evalStep, List.length_ofFn, List.length_map]
  set xs := List.ofFn (fun i : Fin n => x i.castSucc)
  have hof : List.ofFn x = xs ++ [x (Fin.last n)] := ofFn_eq_append_last x
  have hlen_xs : xs.length = n := List.length_ofFn
  have hlen0 : (List.ofFn x).length = xs.length + 1 := by simp [xs]
  have heq0 : ∀ i, (List.ofFn x).getD (shiftWire n i) false = xs.getD i false := by
    intro i
    rw [hof]
    unfold shiftWire
    split_ifs with hi
    · exact getD_append_left xs [x (Fin.last n)] i (by omega)
    · rw [getD_eq_false_of_le (xs ++ [x (Fin.last n)]) (i + 1) (by simp [hlen_xs]; omega),
        getD_eq_false_of_le xs i (by omega)]
  have hinv := foldl_shiftGate_inv n C.gates xs (List.ofFn x) hlen0 (by omega) heq0
  have hlast : (List.ofFn x).getD n false = x (Fin.last n) := by
    rw [hof]
    have htmp := getD_append_single_eq xs (x (Fin.last n))
    rw [hlen_xs] at htmp
    exact htmp
  refine ⟨hlen_w, ?_, ?_⟩
  · exact hinv.2.trans hlast
  · dsimp only [o', Circuit.eval, Circuit.wires]
    change w.getD (if C.output < n + C.gates.length then shiftWire n C.output
      else n + 1 + C.gates.length + 10) false = (C.gates.foldl evalStep xs).getD C.output false
    split_ifs with ho
    · exact hinv.1 C.output
    · rw [getD_eq_false_of_le w _ (by omega),
        getD_eq_false_of_le (C.gates.foldl evalStep xs) C.output
          (by rw [length_foldl_evalStep, hlen_xs]; omega)]

lemma fanInTwo_shift_append (n : ℕ) (C : Circuit) (hC : FanInTwo C) (tail : List Gate)
    (htail : ∀ g ∈ tail,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    FanInTwo ⟨C.gates.map (shiftGate n) ++ tail, n + 1 + C.gates.length + 3⟩ := by
  intro g hg
  simp only [List.mem_append, List.mem_map] at hg
  rcases hg with ⟨g0, hg0, rfl⟩ | hg
  · simpa [shiftGate] using hC g0 hg0
  · exact htail g hg

lemma evalStep_and (w : List Bool) (i j : ℕ) (a b : Bool)
    (hi : w.getD i false = a) (hj : w.getD j false = b) :
    evalStep w ⟨GateOp.and, [i, j]⟩ = w ++ [a && b] := by
  simp only [evalStep, List.map_cons, List.map_nil, hi, hj, GateOp.eval,
    List.all_cons, List.all_nil, id_eq, Bool.and_true]

lemma evalStep_or (w : List Bool) (i j : ℕ) (a b : Bool)
    (hi : w.getD i false = a) (hj : w.getD j false = b) :
    evalStep w ⟨GateOp.or, [i, j]⟩ = w ++ [a || b] := by
  simp only [evalStep, List.map_cons, List.map_nil, hi, hj, GateOp.eval,
    List.any_cons, List.any_nil, id_eq, Bool.or_false]

lemma evalStep_not (w : List Bool) (i : ℕ) (a : Bool)
    (hi : w.getD i false = a) :
    evalStep w ⟨GateOp.not, [i]⟩ = w ++ [!a] := by
  simp only [evalStep, List.map_cons, List.map_nil, hi, GateOp.eval, List.headD_cons]

lemma case_pos (n s : ℕ) (g : (Fin n → Bool) → Bool)
    (h : HasCircuitSize n g s) :
    HasCircuitSize (n + 1)
      (fun x : Fin (n + 1) → Bool => xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc)))
      (s + 4) := by
  rcases h with ⟨C, hfan, hsize, heval⟩
  set m := C.gates.length
  set k := n + 1 + m
  set o' := if C.output < n + m then shiftWire n C.output else k + 10
  set tail : List Gate :=
    [⟨GateOp.or, [n, o']⟩, ⟨GateOp.and, [n, o']⟩, ⟨GateOp.not, [k + 1]⟩,
      ⟨GateOp.and, [k, k + 2]⟩]
  refine ⟨⟨C.gates.map (shiftGate n) ++ tail, k + 3⟩, ?_, ?_, ?_⟩
  · apply fanInTwo_shift_append n C hfan tail
    intro gt hgt
    simp only [tail, List.mem_cons, List.not_mem_nil, or_false] at hgt
    rcases hgt with rfl | rfl | rfl | rfl <;> simp
  · simp [Circuit.size, tail] at hsize ⊢
    omega
  · intro x
    have hbase := eval_base_wires n C x
    set w := (C.gates.map (shiftGate n)).foldl evalStep (List.ofFn x)
    have hwlen : w.length = k := hbase.1
    have hwn : w.getD n false = x (Fin.last n) := hbase.2.1
    have hwo : w.getD o' false = g (fun i : Fin n => x i.castSucc) := by
      rw [hbase.2.2, heval]
    set y := x (Fin.last n)
    set v := g (fun i : Fin n => x i.castSucc)
    have h0 : evalStep w ⟨GateOp.or, [n, o']⟩ = w ++ [y || v] :=
      evalStep_or w n o' y v hwn hwo
    have h1 : evalStep (w ++ [y || v]) ⟨GateOp.and, [n, o']⟩ = w ++ [y || v, y && v] := by
      have hn1 : (w ++ [y || v]).getD n false = y := by
        rw [getD_append_left w [y || v] n (by omega), hwn]
      have ho1 : (w ++ [y || v]).getD o' false = v := by
        rw [getD_safeWire w [y || v] n m C.output hwlen (by simp), hwo]
      rw [evalStep_and (w ++ [y || v]) n o' y v hn1 ho1]
      simp [List.append_assoc]
    have h2 : evalStep (w ++ [y || v, y && v]) ⟨GateOp.not, [k + 1]⟩ =
        w ++ [y || v, y && v, !(y && v)] := by
      have hk1 : (w ++ [y || v, y && v]).getD (k + 1) false = (y && v) := by
        have hsp : w ++ [y || v, y && v] = (w ++ [y || v]) ++ [y && v] := by simp
        rw [hsp]
        have hlen1 : (w ++ [y || v]).length = k + 1 := by simp [hwlen]
        rw [← hlen1, getD_append_single_eq]
      rw [evalStep_not (w ++ [y || v, y && v]) (k + 1) (y && v) hk1]
      simp [List.append_assoc]
    have h3 : evalStep (w ++ [y || v, y && v, !(y && v)]) ⟨GateOp.and, [k, k + 2]⟩ =
        w ++ [y || v, y && v, !(y && v), (y || v) && !(y && v)] := by
      have hk0 : (w ++ [y || v, y && v, !(y && v)]).getD k false = (y || v) := by
        have hsp : w ++ [y || v, y && v, !(y && v)] =
            (w ++ [y || v]) ++ [y && v, !(y && v)] := by simp
        rw [hsp, getD_append_left (w ++ [y || v]) _ k (by simp [hwlen]), ← hwlen,
          getD_append_single_eq]
      have hk2 : (w ++ [y || v, y && v, !(y && v)]).getD (k + 2) false = !(y && v) := by
        have hsp : w ++ [y || v, y && v, !(y && v)] =
            (w ++ [y || v, y && v]) ++ [!(y && v)] := by simp
        rw [hsp]
        have hlen2 : (w ++ [y || v, y && v]).length = k + 2 := by simp [hwlen]
        rw [← hlen2, getD_append_single_eq]
      rw [evalStep_and (w ++ [y || v, y && v, !(y && v)]) k (k + 2) (y || v) (!(y && v)) hk0 hk2]
      simp [List.append_assoc]
    change (((C.gates.map (shiftGate n) ++ tail).foldl evalStep (List.ofFn x)).getD (k + 3) false) =
      xor y v
    rw [List.foldl_append]
    change (tail.foldl evalStep w).getD (k + 3) false = xor y v
    simp only [tail, List.foldl_cons, List.foldl_nil, h0, h1, h2, h3]
    have hsplit : w ++ [y || v, y && v, !(y && v), (y || v) && !(y && v)] =
        (w ++ [y || v, y && v, !(y && v)]) ++ [(y || v) && !(y && v)] := by simp
    rw [hsplit]
    have hlen3 : (w ++ [y || v, y && v, !(y && v)]).length = k + 3 := by simp [hwlen]
    rw [← hlen3, getD_append_single_eq]
    cases y <;> cases v <;> rfl

lemma case_neg (n s : ℕ) (g : (Fin n → Bool) → Bool)
    (h : HasCircuitSize n (fun y : Fin n → Bool => !(g y)) s) :
    HasCircuitSize (n + 1)
      (fun x : Fin (n + 1) → Bool => xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc)))
      (s + 4) := by
  rcases h with ⟨C, hfan, hsize, heval⟩
  set m := C.gates.length
  set k := n + 1 + m
  set o' := if C.output < n + m then shiftWire n C.output else k + 10
  set tail : List Gate :=
    [⟨GateOp.and, [n, o']⟩, ⟨GateOp.or, [n, o']⟩, ⟨GateOp.not, [k + 1]⟩,
      ⟨GateOp.or, [k, k + 2]⟩]
  refine ⟨⟨C.gates.map (shiftGate n) ++ tail, k + 3⟩, ?_, ?_, ?_⟩
  · apply fanInTwo_shift_append n C hfan tail
    intro gt hgt
    simp only [tail, List.mem_cons, List.not_mem_nil, or_false] at hgt
    rcases hgt with rfl | rfl | rfl | rfl <;> simp
  · simp [Circuit.size, tail] at hsize ⊢
    omega
  · intro x
    have hbase := eval_base_wires n C x
    set w := (C.gates.map (shiftGate n)).foldl evalStep (List.ofFn x)
    have hwlen : w.length = k := hbase.1
    have hwn : w.getD n false = x (Fin.last n) := hbase.2.1
    have hwo : w.getD o' false = !(g (fun i : Fin n => x i.castSucc)) := by
      rw [hbase.2.2, heval]
    set y := x (Fin.last n)
    set v := g (fun i : Fin n => x i.castSucc)
    have h0 : evalStep w ⟨GateOp.and, [n, o']⟩ = w ++ [y && !v] :=
      evalStep_and w n o' y (!v) hwn hwo
    have h1 : evalStep (w ++ [y && !v]) ⟨GateOp.or, [n, o']⟩ = w ++ [y && !v, y || !v] := by
      have hn1 : (w ++ [y && !v]).getD n false = y := by
        rw [getD_append_left w [y && !v] n (by omega), hwn]
      have ho1 : (w ++ [y && !v]).getD o' false = !v := by
        rw [getD_safeWire w [y && !v] n m C.output hwlen (by simp), hwo]
      rw [evalStep_or (w ++ [y && !v]) n o' y (!v) hn1 ho1]
      simp [List.append_assoc]
    have h2 : evalStep (w ++ [y && !v, y || !v]) ⟨GateOp.not, [k + 1]⟩ =
        w ++ [y && !v, y || !v, !(y || !v)] := by
      have hk1 : (w ++ [y && !v, y || !v]).getD (k + 1) false = (y || !v) := by
        have hsp : w ++ [y && !v, y || !v] = (w ++ [y && !v]) ++ [y || !v] := by simp
        rw [hsp]
        have hlen1 : (w ++ [y && !v]).length = k + 1 := by simp [hwlen]
        rw [← hlen1, getD_append_single_eq]
      rw [evalStep_not (w ++ [y && !v, y || !v]) (k + 1) (y || !v) hk1]
      simp [List.append_assoc]
    have h3 : evalStep (w ++ [y && !v, y || !v, !(y || !v)]) ⟨GateOp.or, [k, k + 2]⟩ =
        w ++ [y && !v, y || !v, !(y || !v), (y && !v) || !(y || !v)] := by
      have hk0 : (w ++ [y && !v, y || !v, !(y || !v)]).getD k false = (y && !v) := by
        have hsp : w ++ [y && !v, y || !v, !(y || !v)] =
            (w ++ [y && !v]) ++ [y || !v, !(y || !v)] := by simp
        rw [hsp, getD_append_left (w ++ [y && !v]) _ k (by simp [hwlen]), ← hwlen,
          getD_append_single_eq]
      have hk2 : (w ++ [y && !v, y || !v, !(y || !v)]).getD (k + 2) false = !(y || !v) := by
        have hsp : w ++ [y && !v, y || !v, !(y || !v)] =
            (w ++ [y && !v, y || !v]) ++ [!(y || !v)] := by simp
        rw [hsp]
        have hlen2 : (w ++ [y && !v, y || !v]).length = k + 2 := by simp [hwlen]
        rw [← hlen2, getD_append_single_eq]
      rw [evalStep_or (w ++ [y && !v, y || !v, !(y || !v)]) k (k + 2) (y && !v) (!(y || !v))
        hk0 hk2]
      simp [List.append_assoc]
    change (((C.gates.map (shiftGate n) ++ tail).foldl evalStep (List.ofFn x)).getD (k + 3) false) =
      xor y v
    rw [List.foldl_append]
    change (tail.foldl evalStep w).getD (k + 3) false = xor y v
    simp only [tail, List.foldl_cons, List.foldl_nil, h0, h1, h2, h3]
    have hsplit : w ++ [y && !v, y || !v, !(y || !v), (y && !v) || !(y || !v)] =
        (w ++ [y && !v, y || !v, !(y || !v)]) ++ [(y && !v) || !(y || !v)] := by simp
    rw [hsplit]
    have hlen3 : (w ++ [y && !v, y || !v, !(y || !v)]).length = k + 3 := by simp [hwlen]
    rw [← hlen3, getD_append_single_eq]
    cases y <;> cases v <;> rfl

end PEqualNP.Outside.L_meta_716_aux

theorem PEqualNP.Outside.L_meta_716 :
    ∀ (n s : ℕ) (g : (Fin n → Bool) → Bool), (PEqualNP.MetaComplexity.HasCircuitSize n g s → PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun x : Fin (n + 1) → Bool => xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc))) (s + 4)) ∧ (PEqualNP.MetaComplexity.HasCircuitSize n (fun y : Fin n → Bool => !(g y)) s → PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun x : Fin (n + 1) → Bool => xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc))) (s + 4)) := by
  intro n s g
  exact ⟨PEqualNP.Outside.L_meta_716_aux.case_pos n s g,
    PEqualNP.Outside.L_meta_716_aux.case_neg n s g⟩
