import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_792_aux

open PEqualNP.CircuitLowerBounds

def wireStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_wireStep_length (gs : List Gate) (x : List Bool) :
    (gs.foldl wireStep x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, wireStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wireStep_getD_lt (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (gs.foldl wireStep x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    have hi' : i < (wireStep x g).length := by
      simp only [wireStep, List.length_append, List.length_singleton]
      omega
    rw [List.foldl_cons, ih (wireStep x g) hi']
    simp only [wireStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_wireStep_append_getD_lt (gs1 gs2 : List Gate) (x : List Bool) (i : ℕ)
    (hi : i < x.length + gs1.length) :
    ((gs1 ++ gs2).foldl wireStep x).getD i false = (gs1.foldl wireStep x).getD i false := by
  rw [List.foldl_append]
  apply foldl_wireStep_getD_lt
  rw [foldl_wireStep_length]
  exact hi

lemma wires_getD_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false := by
  exact foldl_wireStep_getD_lt C.gates x i hi

lemma wires_getD_gate (C : Circuit) (x : List Bool) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) :
    (C.wires x).getD (x.length + j) false =
      g.op.eval (g.inputs.map fun i => if i < x.length + j then (C.wires x).getD i false else false) := by
  have hj : j < C.gates.length := by
    by_contra h
    rw [List.getElem?_eq_none (Nat.le_of_not_lt h)] at hg
    cases hg
  have hg_eq : C.gates[j] = g := by
    rw [List.getElem?_eq_getElem hj] at hg
    exact Option.some.inj hg
  have hsplit : C.gates = C.gates.take j ++ [g] ++ C.gates.drop (j + 1) := by
    rw [← hg_eq, List.append_assoc, List.singleton_append]
    have hdrop : C.gates[j] :: C.gates.drop (j + 1) = C.gates.drop j := by
      symm
      exact List.drop_eq_getElem_cons hj
    rw [hdrop, List.take_append_drop]
  have htake_len : (C.gates.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
  let w0 := (C.gates.take j).foldl wireStep x
  have hw0_len : w0.length = x.length + j := by
    dsimp [w0]
    rw [foldl_wireStep_length, htake_len]
  have hwires_eq : C.wires x = (C.gates.take j ++ [g] ++ C.gates.drop (j + 1)).foldl wireStep x := by
    unfold Circuit.wires
    conv_lhs => rw [hsplit]
    rfl
  have hidx_lt : x.length + j < x.length + (C.gates.take j ++ [g]).length := by
    simp [htake_len]
  have hval : (C.wires x).getD (x.length + j) false =
      ((C.gates.take j ++ [g]).foldl wireStep x).getD (x.length + j) false := by
    rw [hwires_eq]
    exact foldl_wireStep_append_getD_lt (C.gates.take j ++ [g]) (C.gates.drop (j + 1)) x (x.length + j) hidx_lt
  rw [hval, List.foldl_append, List.foldl_cons, List.foldl_nil]
  change (wireStep w0 g).getD (x.length + j) false = _
  simp only [wireStep, List.getD_eq_getElem?_getD]
  conv_lhs => rw [← hw0_len]
  rw [List.getElem?_append_right (Nat.le_refl w0.length), Nat.sub_self]
  simp only [List.getElem?_cons_zero, Option.getD_some]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < x.length + j
  · simp only [hi, ↓reduceIte]
    have hi' : i < x.length + (C.gates.take j).length := by rw [htake_len]; exact hi
    have h2 : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
    have h3 : (C.wires x).getD i false = w0.getD i false := by
      unfold Circuit.wires
      conv_lhs => rw [h2]
      exact foldl_wireStep_append_getD_lt (C.gates.take j) (C.gates.drop j) x i hi'
    rw [← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD, h3]
  · simp only [hi, ↓reduceIte]
    have hge : w0.length ≤ i := by rw [hw0_len]; exact Nat.le_of_not_lt hi
    rw [List.getElem?_eq_none hge, Option.getD_none]

def activeSet (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p : Fin n =>
    (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD w false = true)

lemma activeSet_input_card (n : ℕ) (C : Circuit) (w : ℕ) (hw : w < n) :
    (activeSet n C w).card = 1 := by
  have hset : activeSet n C w = {⟨w, hw⟩} := by
    ext p
    simp only [activeSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    have hlen : (List.ofFn (fun q : Fin n => decide (q = p))).length = n := List.length_ofFn
    have hget := wires_getD_input C (List.ofFn (fun q : Fin n => decide (q = p))) w (by rw [hlen]; exact hw)
    rw [hget, List.getD_eq_getElem?_getD]
    have hw' : w < (List.ofFn (fun q : Fin n => decide (q = p))).length := by rw [hlen]; exact hw
    rw [List.getElem?_eq_getElem hw', Option.getD_some, List.getElem_ofFn]
    simp only [decide_eq_true_eq]
    constructor
    · intro h; exact h.symm
    · intro h; exact h.symm
  rw [hset, Finset.card_singleton]

lemma activeSet_and_subset_left (n : ℕ) (C : Circuit) (j a b : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) (hop : g.op = GateOp.and) (hin : g.inputs = [a, b]) :
    activeSet n C (n + j) ⊆ if a < n + j then activeSet n C a else ∅ := by
  intro p hp
  simp only [activeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  have hlen : (List.ofFn (fun q : Fin n => decide (q = p))).length = n := List.length_ofFn
  have hgate := wires_getD_gate C (List.ofFn (fun q : Fin n => decide (q = p))) j g hg
  rw [hlen, hop, hin] at hgate
  rw [hgate] at hp
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
    Bool.and_true, Bool.and_eq_true] at hp
  by_cases ha : a < n + j
  · simp only [ha, ↓reduceIte, activeSet, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [ha, ↓reduceIte] at hp
    exact hp.1
  · simp only [ha, ↓reduceIte] at hp
    cases hp.1

lemma activeSet_and_subset_right (n : ℕ) (C : Circuit) (j a b : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) (hop : g.op = GateOp.and) (hin : g.inputs = [a, b]) :
    activeSet n C (n + j) ⊆ if b < n + j then activeSet n C b else ∅ := by
  intro p hp
  simp only [activeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  have hlen : (List.ofFn (fun q : Fin n => decide (q = p))).length = n := List.length_ofFn
  have hgate := wires_getD_gate C (List.ofFn (fun q : Fin n => decide (q = p))) j g hg
  rw [hlen, hop, hin] at hgate
  rw [hgate] at hp
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
    Bool.and_true, Bool.and_eq_true] at hp
  by_cases hb : b < n + j
  · simp only [hb, ↓reduceIte, activeSet, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [hb, ↓reduceIte] at hp
    exact hp.2
  · simp only [hb, ↓reduceIte] at hp
    cases hp.2

lemma activeSet_or_subset (n : ℕ) (C : Circuit) (j a b : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) (hop : g.op = GateOp.or) (hin : g.inputs = [a, b]) :
    activeSet n C (n + j) ⊆
      (if a < n + j then activeSet n C a else ∅) ∪ (if b < n + j then activeSet n C b else ∅) := by
  intro p hp
  simp only [activeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  have hlen : (List.ofFn (fun q : Fin n => decide (q = p))).length = n := List.length_ofFn
  have hgate := wires_getD_gate C (List.ofFn (fun q : Fin n => decide (q = p))) j g hg
  rw [hlen, hop, hin] at hgate
  rw [hgate] at hp
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
    Bool.or_false, Bool.or_eq_true] at hp
  rw [Finset.mem_union]
  rcases hp with ha_val | hb_val
  · left
    by_cases ha : a < n + j
    · simp only [ha, ↓reduceIte, activeSet, Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [ha, ↓reduceIte] at ha_val
      exact ha_val
    · simp only [ha, ↓reduceIte] at ha_val
      cases ha_val
  · right
    by_cases hb : b < n + j
    · simp only [hb, ↓reduceIte, activeSet, Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [hb, ↓reduceIte] at hb_val
      exact hb_val
    · simp only [hb, ↓reduceIte] at hb_val
      cases hb_val

end PEqualNP.Outside.L_meta_792_aux

theorem PEqualNP.Outside.L_meta_792 :
    ∀ (n r : ℕ) (S : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (Q : Finset ℕ) (ψ : ℕ → Bool), (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ p : Fin n, (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + r) false = true → p ∈ S) → r ∈ Q → (∀ j ∈ Q, j < C.size ∧ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)) ⊆ S ∧ 2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)).card) → (∀ j ∈ Q, ∀ j' : ℕ, j' < j → (∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g ∧ n + j' ∈ g.inputs) → (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j') false = true)) ⊆ S → 2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j') false = true)).card → j' ∈ Q) → (∀ j ∈ Q, ∀ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g → ψ (n + j) = g.op.eval (g.inputs.map (fun w => if w < n + j then ψ w else false))) → (∀ w : ℕ, (∀ j ∈ Q, w ≠ n + j) → ψ w = false → (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (w) false = true)) ⊆ S) → ψ (n + r) = false → (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (n + r) false = true)).card ≤ Q.card + 1 := by
  intro n r S C Q ψ hGates _hSubS hrQ hQ hClosed hPsi hOut hPsiR
  let L := PEqualNP.Outside.L_meta_792_aux.activeSet n C
  let F : Finset ℕ := Q.filter (fun j => ψ (n + j) = false)
  have hChildInv : ∀ j ∈ Q, ∀ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g →
      ∀ w : ℕ, w ∈ g.inputs → w < n + j → ψ w = false →
      (∃ j' ∈ F, w = n + j') ∨ (L w).card ≤ 1 := by
    intro j hjQ g hg w hw_in hw_lt hψw
    by_cases hwn : w < n
    · right
      have hcard := PEqualNP.Outside.L_meta_792_aux.activeSet_input_card n C w hwn
      dsimp only [L]
      omega
    · let j' := w - n
      have hw_eq : w = n + j' := by omega
      have hj'_lt : j' < j := by omega
      by_cases hj'Q : j' ∈ Q
      · left
        refine ⟨j', ?_, hw_eq⟩
        simp only [F, Finset.mem_filter]
        exact ⟨hj'Q, by rw [← hw_eq]; exact hψw⟩
      · right
        have hnotQ : ∀ k ∈ Q, w ≠ n + k := by
          intro k hkQ heq
          have hkj : k = j' := by omega
          rw [hkj] at hkQ
          exact hj'Q hkQ
        have hsubS : L (n + j') ⊆ S := by
          rw [← hw_eq]
          exact hOut w hnotQ hψw
        by_contra hgt
        have hge2 : 2 ≤ (L (n + j')).card := by
          rw [← hw_eq]
          omega
        have hj'_in_Q := hClosed j hjQ j' hj'_lt ⟨g, hg, by rw [← hw_eq]; exact hw_in⟩ hsubS hge2
        exact hj'Q hj'_in_Q
  have hMain : ∀ m : ℕ, ∀ W : Finset ℕ,
      (∀ w ∈ W, w < n + m) →
      (∀ w ∈ W, (∃ j ∈ F, w = n + j) ∨ (L w).card ≤ 1) →
      (W.biUnion L).card ≤ W.card + (F.filter (· < m)).card := by
    intro m
    induction m with
    | zero =>
      intro W hBound _hInv
      have h1 : (W.biUnion L).card ≤ ∑ w ∈ W, (L w).card := Finset.card_biUnion_le
      have h2 : ∑ w ∈ W, (L w).card = W.card := by
        calc
          ∑ w ∈ W, (L w).card = ∑ _w ∈ W, 1 := by
            apply Finset.sum_congr rfl
            intro w hw
            have hwn : w < n := by
              have := hBound w hw
              omega
            exact PEqualNP.Outside.L_meta_792_aux.activeSet_input_card n C w hwn
          _ = W.card := by simp
      omega
    | succ m ih =>
      intro W hBound hInv
      have hFsub : (F.filter (· < m)).card ≤ (F.filter (· < m + 1)).card := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_filter] at hx ⊢
        exact ⟨hx.1, Nat.lt_succ_of_lt hx.2⟩
      by_cases hmem : n + m ∈ W
      · let W0 := W.erase (n + m)
        have hW0_card : W0.card + 1 = W.card := Finset.card_erase_add_one hmem
        have hW0_bound : ∀ w ∈ W0, w < n + m := by
          intro w hw
          have hwW : w ∈ W := Finset.mem_of_mem_erase hw
          have hne : w ≠ n + m := Finset.ne_of_mem_erase hw
          have hlt := hBound w hwW
          omega
        have hW0_inv : ∀ w ∈ W0, (∃ j ∈ F, w = n + j) ∨ (L w).card ≤ 1 := by
          intro w hw
          exact hInv w (Finset.mem_of_mem_erase hw)
        by_cases hmF : m ∈ F
        · have hFcard : (F.filter (· < m + 1)).card = (F.filter (· < m)).card + 1 := by
            have hEq : F.filter (· < m + 1) = insert m (F.filter (· < m)) := by
              ext x
              simp only [Finset.mem_filter, Finset.mem_insert]
              constructor
              · rintro ⟨hxF, hxlt⟩
                by_cases hxm : x = m
                · left; exact hxm
                · right; exact ⟨hxF, by omega⟩
              · rintro (hxm | ⟨hxF, hxlt⟩)
                · rw [hxm]; exact ⟨hmF, Nat.lt_succ_self m⟩
                · exact ⟨hxF, Nat.lt_succ_of_lt hxlt⟩
            rw [hEq, Finset.card_insert_of_notMem]
            simp only [Finset.mem_filter, lt_self_iff_false, and_false, not_false_eq_true]
          have hmQ : m ∈ Q := (Finset.mem_filter.mp hmF).1
          have hψm : ψ (n + m) = false := (Finset.mem_filter.mp hmF).2
          have hm_lt : m < C.gates.length := (hQ m hmQ).1
          let g := C.gates[m]
          have hg : C.gates[m]? = some g := List.getElem?_eq_getElem hm_lt
          have hg_mem : g ∈ C.gates := List.getElem_mem hm_lt
          have hg_spec := hGates g hg_mem
          have hlen2 : g.inputs.length = 2 := hg_spec.2
          match hin : g.inputs with
          | [a, b] =>
            have hpsi_eq := hPsi m hmQ g hg
            rw [hψm, hin] at hpsi_eq
            rcases hg_spec.1 with hop | hop
            · rw [hop] at hpsi_eq
              simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
                List.all_cons, List.all_nil, id_eq, Bool.and_true] at hpsi_eq
              have hdisj : (if a < n + m then ψ a else false) = false ∨
                  (if b < n + m then ψ b else false) = false := by
                cases ha_b : (if a < n + m then ψ a else false)
                · left; rfl
                · right
                  rw [ha_b, Bool.true_and] at hpsi_eq
                  exact hpsi_eq.symm
              have hStepAnd : ∀ c : ℕ, c ∈ g.inputs →
                  (if c < n + m then ψ c else false) = false →
                  L (n + m) ⊆ (if c < n + m then L c else ∅) →
                  (W.biUnion L).card ≤ W.card + (F.filter (· < m + 1)).card := by
                intro c hc_in hc_psi hc_sub
                by_cases hclt : c < n + m
                · simp only [hclt, ↓reduceIte] at hc_psi hc_sub
                  let W' := insert c W0
                  have hW'_sub : W.biUnion L ⊆ W'.biUnion L := by
                    intro p hp
                    rw [Finset.mem_biUnion] at hp ⊢
                    rcases hp with ⟨w, hwW, hpw⟩
                    by_cases hwm : w = n + m
                    · subst hwm
                      exact ⟨c, Finset.mem_insert_self c W0, hc_sub hpw⟩
                    · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hwm, hwW⟩), hpw⟩
                  have hW'_bound : ∀ w ∈ W', w < n + m := by
                    intro w hw
                    rcases Finset.mem_insert.mp hw with rfl | hw0
                    · exact hclt
                    · exact hW0_bound w hw0
                  have hW'_inv : ∀ w ∈ W', (∃ j ∈ F, w = n + j) ∨ (L w).card ≤ 1 := by
                    intro w hw
                    rcases Finset.mem_insert.mp hw with hwc | hw0
                    · rw [hwc]
                      exact hChildInv m hmQ g hg c hc_in hclt hc_psi
                    · exact hW0_inv w hw0
                  have hih := ih W' hW'_bound hW'_inv
                  have hle1 : (W.biUnion L).card ≤ (W'.biUnion L).card := Finset.card_le_card hW'_sub
                  have hW'_card : W'.card ≤ W0.card + 1 := Finset.card_insert_le c W0
                  omega
                · simp only [hclt, ↓reduceIte] at hc_sub
                  have hW0_sub : W.biUnion L ⊆ W0.biUnion L := by
                    intro p hp
                    rw [Finset.mem_biUnion] at hp ⊢
                    rcases hp with ⟨w, hwW, hpw⟩
                    by_cases hwm : w = n + m
                    · subst hwm
                      exact absurd (hc_sub hpw) (Finset.notMem_empty p)
                    · exact ⟨w, Finset.mem_erase.mpr ⟨hwm, hwW⟩, hpw⟩
                  have hih := ih W0 hW0_bound hW0_inv
                  have hle1 : (W.biUnion L).card ≤ (W0.biUnion L).card := Finset.card_le_card hW0_sub
                  omega
              rcases hdisj with ha_false | hb_false
              · exact hStepAnd a (by rw [hin]; simp) ha_false
                  (PEqualNP.Outside.L_meta_792_aux.activeSet_and_subset_left n C m a b g hg hop hin)
              · exact hStepAnd b (by rw [hin]; simp) hb_false
                  (PEqualNP.Outside.L_meta_792_aux.activeSet_and_subset_right n C m a b g hg hop hin)
            · rw [hop] at hpsi_eq
              simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
                List.any_cons, List.any_nil, id_eq, Bool.or_false] at hpsi_eq
              have hboth : (if a < n + m then ψ a else false) = false ∧
                  (if b < n + m then ψ b else false) = false := by
                cases ha_b : (if a < n + m then ψ a else false)
                · rw [ha_b, Bool.false_or] at hpsi_eq
                  exact ⟨rfl, hpsi_eq.symm⟩
                · rw [ha_b, Bool.true_or] at hpsi_eq
                  cases hpsi_eq
              let Ia : Finset ℕ := if a < n + m then {a} else ∅
              let Ib : Finset ℕ := if b < n + m then {b} else ∅
              let W' : Finset ℕ := W0 ∪ (Ia ∪ Ib)
              have hIa_card : Ia.card ≤ 1 := by
                dsimp [Ia]
                split_ifs <;> simp
              have hIb_card : Ib.card ≤ 1 := by
                dsimp [Ib]
                split_ifs <;> simp
              have hW'_card : W'.card ≤ W0.card + 2 := by
                have h1 : W'.card ≤ W0.card + (Ia ∪ Ib).card := Finset.card_union_le W0 (Ia ∪ Ib)
                have h2 : (Ia ∪ Ib).card ≤ Ia.card + Ib.card := Finset.card_union_le Ia Ib
                omega
              have hW'_bound : ∀ w ∈ W', w < n + m := by
                intro w hw
                rw [Finset.mem_union, Finset.mem_union] at hw
                rcases hw with hw0 | hwa | hwb
                · exact hW0_bound w hw0
                · dsimp [Ia] at hwa
                  split_ifs at hwa with halt
                  · rw [Finset.mem_singleton.mp hwa]; exact halt
                  · exact absurd hwa (Finset.notMem_empty w)
                · dsimp [Ib] at hwb
                  split_ifs at hwb with hblt
                  · rw [Finset.mem_singleton.mp hwb]; exact hblt
                  · exact absurd hwb (Finset.notMem_empty w)
              have hW'_inv : ∀ w ∈ W', (∃ j ∈ F, w = n + j) ∨ (L w).card ≤ 1 := by
                intro w hw
                rw [Finset.mem_union, Finset.mem_union] at hw
                rcases hw with hw0 | hwa | hwb
                · exact hW0_inv w hw0
                · dsimp [Ia] at hwa
                  split_ifs at hwa with halt
                  · rw [Finset.mem_singleton.mp hwa]
                    have hψa : ψ a = false := by
                      have := hboth.1
                      simp only [halt, ↓reduceIte] at this
                      exact this
                    exact hChildInv m hmQ g hg a (by rw [hin]; simp) halt hψa
                  · exact absurd hwa (Finset.notMem_empty w)
                · dsimp [Ib] at hwb
                  split_ifs at hwb with hblt
                  · rw [Finset.mem_singleton.mp hwb]
                    have hψb : ψ b = false := by
                      have := hboth.2
                      simp only [hblt, ↓reduceIte] at this
                      exact this
                    exact hChildInv m hmQ g hg b (by rw [hin]; simp) hblt hψb
                  · exact absurd hwb (Finset.notMem_empty w)
              have hor_sub := PEqualNP.Outside.L_meta_792_aux.activeSet_or_subset n C m a b g hg hop hin
              have hW'_sub : W.biUnion L ⊆ W'.biUnion L := by
                intro p hp
                rw [Finset.mem_biUnion] at hp ⊢
                rcases hp with ⟨w, hwW, hpw⟩
                by_cases hwm : w = n + m
                · subst hwm
                  have hpab := hor_sub hpw
                  rw [Finset.mem_union] at hpab
                  rcases hpab with hpa | hpb
                  · by_cases halt : a < n + m
                    · simp only [halt, ↓reduceIte] at hpa
                      refine ⟨a, ?_, hpa⟩
                      rw [Finset.mem_union, Finset.mem_union]
                      right; left
                      simp [Ia, halt]
                    · simp only [halt, ↓reduceIte] at hpa
                      exact absurd hpa (Finset.notMem_empty p)
                  · by_cases hblt : b < n + m
                    · simp only [hblt, ↓reduceIte] at hpb
                      refine ⟨b, ?_, hpb⟩
                      rw [Finset.mem_union, Finset.mem_union]
                      right; right
                      simp [Ib, hblt]
                    · simp only [hblt, ↓reduceIte] at hpb
                      exact absurd hpb (Finset.notMem_empty p)
                · refine ⟨w, ?_, hpw⟩
                  rw [Finset.mem_union]
                  left
                  exact Finset.mem_erase.mpr ⟨hwm, hwW⟩
              have hih := ih W' hW'_bound hW'_inv
              have hle1 : (W.biUnion L).card ≤ (W'.biUnion L).card := Finset.card_le_card hW'_sub
              omega
          | [] => simp [hin] at hlen2
          | [_] => simp [hin] at hlen2
          | _ :: _ :: _ :: _ => simp [hin] at hlen2
        · have hLm_card : (L (n + m)).card ≤ 1 := by
            rcases hInv (n + m) hmem with ⟨j, hjF, heq⟩ | hle
            · have hjm : j = m := by omega
              rw [hjm] at hjF
              exact absurd hjF hmF
            · exact hle
          have hsub : W.biUnion L ⊆ W0.biUnion L ∪ L (n + m) := by
            intro p hp
            rw [Finset.mem_biUnion] at hp
            rcases hp with ⟨w, hwW, hpw⟩
            rw [Finset.mem_union]
            by_cases hwm : w = n + m
            · subst hwm; right; exact hpw
            · left
              rw [Finset.mem_biUnion]
              exact ⟨w, Finset.mem_erase.mpr ⟨hwm, hwW⟩, hpw⟩
          have hle1 : (W.biUnion L).card ≤ (W0.biUnion L ∪ L (n + m)).card := Finset.card_le_card hsub
          have hle2 : (W0.biUnion L ∪ L (n + m)).card ≤ (W0.biUnion L).card + (L (n + m)).card :=
            Finset.card_union_le (W0.biUnion L) (L (n + m))
          have hih := ih W0 hW0_bound hW0_inv
          omega
      · have hBound' : ∀ w ∈ W, w < n + m := by
          intro w hw
          have hne : w ≠ n + m := by
            intro heq
            rw [heq] at hw
            exact hmem hw
          have hlt := hBound w hw
          omega
        have hih := ih W hBound' hInv
        omega
  have hrF : r ∈ F := Finset.mem_filter.mpr ⟨hrQ, hPsiR⟩
  have hr_lt : r < C.size := (hQ r hrQ).1
  have hFinal := hMain C.size {n + r}
    (by
      intro w hw
      rw [Finset.mem_singleton.mp hw]
      omega)
    (by
      intro w hw
      rw [Finset.mem_singleton.mp hw]
      left
      exact ⟨r, hrF, rfl⟩)
  have hbi : ({n + r} : Finset ℕ).biUnion L = L (n + r) := Finset.singleton_biUnion
  rw [hbi, Finset.card_singleton] at hFinal
  have hF_le_Q : (F.filter (· < C.size)).card ≤ Q.card := by
    apply Finset.card_le_card
    intro x hx
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
  have hL_eq : L (n + r) =
      Finset.univ.filter (fun a : Fin n =>
        (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (n + r) false = true) := rfl
  rw [← hL_eq]
  omega
