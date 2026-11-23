import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_669_aux

open PEqualNP.CircuitLowerBounds

def wires (gates : List Gate) (x : List Bool) : List Bool :=
  Circuit.wires ⟨gates, 0⟩ x

def fixInput {n : ℕ} (T Z : Finset (Fin n)) (x : Fin n → Bool) : List Bool :=
  List.ofFn (fun i : Fin n => if i ∈ T then true else if i ∈ Z then false else x i)

def IsValidGate (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

def WireRel {n : ℕ} (T Z : Finset (Fin n)) (gs gates' : List Gate)
    (st : List (Sum Bool ℕ)) : Prop :=
  st.length = n + gs.length ∧
  ∀ w : ℕ, match st.getD w (Sum.inl false) with
    | Sum.inl b => ∀ x : Fin n → Bool, (wires gs (fixInput T Z x)).getD w false = b
    | Sum.inr w' =>
        w' < n + gates'.length ∧
        ∀ x : Fin n → Bool,
          (wires gates' (List.ofFn x)).getD w' false = (wires gs (fixInput T Z x)).getD w false

lemma getD_append_lt {α : Type} (l : List α) (v d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [v]).getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_eq {α : Type} (l : List α) (v d : α) :
    (l ++ [v]).getD l.length d = v := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_of_ge {α : Type} (l : List α) (d : α) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma getD_ofFn_lt {α : Type} {n : ℕ} (f : Fin n → α) (d : α) (i : ℕ) (hi : i < n) :
    (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]

lemma wires_append_singleton (gs : List Gate) (g : Gate) (x : List Bool) :
    wires (gs ++ [g]) x =
      wires gs x ++ [g.op.eval (g.inputs.map fun i => (wires gs x).getD i false)] := by
  simp [wires, Circuit.wires, List.foldl_append]

lemma wires_length (gs : List Gate) (x : List Bool) :
    (wires gs x).length = x.length + gs.length := by
  refine List.reverseRecOn gs ?_ ?_
  · simp [wires, Circuit.wires]
  · intro l g ih
    rw [wires_append_singleton]
    simp [ih]
    omega

lemma fixInput_length {n : ℕ} (T Z : Finset (Fin n)) (x : Fin n → Bool) :
    (fixInput T Z x).length = n := by
  simp [fixInput]

lemma wires_fixInput_length {n : ℕ} (T Z : Finset (Fin n)) (gs : List Gate) (x : Fin n → Bool) :
    (wires gs (fixInput T Z x)).length = n + gs.length := by
  rw [wires_length, fixInput_length]

lemma wires_ofFn_length {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (wires gs (List.ofFn x)).length = n + gs.length := by
  rw [wires_length, List.length_ofFn]

lemma eval_and_nil : GateOp.eval GateOp.and [] = true := rfl
lemma eval_or_nil : GateOp.eval GateOp.or [] = false := rfl
lemma eval_and_single (u : Bool) : GateOp.eval GateOp.and [u] = u := by cases u <;> rfl
lemma eval_or_single (u : Bool) : GateOp.eval GateOp.or [u] = u := by cases u <;> rfl
lemma eval_and_pair (u v : Bool) : GateOp.eval GateOp.and [u, v] = (u && v) := by
  cases u <;> cases v <;> rfl
lemma eval_or_pair (u v : Bool) : GateOp.eval GateOp.or [u, v] = (u || v) := by
  cases u <;> cases v <;> rfl

lemma wireRel_base {n : ℕ} (T Z : Finset (Fin n)) :
    WireRel T Z [] []
      (List.ofFn (fun i : Fin n => if i ∈ T then Sum.inl true else if i ∈ Z then Sum.inl false else Sum.inr i.1)) := by
  constructor
  · simp
  · intro w
    by_cases hw : w < n
    · rw [getD_ofFn_lt _ _ w hw]
      by_cases hT : (⟨w, hw⟩ : Fin n) ∈ T
      · simp only [hT, ↓reduceIte]
        intro x
        simp [wires, Circuit.wires, fixInput, hw, hT]
      · simp only [hT, ↓reduceIte]
        by_cases hZ : (⟨w, hw⟩ : Fin n) ∈ Z
        · simp only [hZ, ↓reduceIte]
          intro x
          simp [wires, Circuit.wires, fixInput, hw, hT, hZ]
        · simp only [hZ, ↓reduceIte]
          refine ⟨by omega, ?_⟩
          intro x
          simp [wires, Circuit.wires, fixInput, hw, hT, hZ]
    · have hge : (List.ofFn (fun i : Fin n =>
          if i ∈ T then Sum.inl true else if i ∈ Z then Sum.inl false else Sum.inr i.1)).length ≤ w := by
        simp; omega
      rw [getD_of_ge _ _ w hge]
      intro x
      have hge2 : (wires [] (fixInput T Z x)).length ≤ w := by
        rw [wires_fixInput_length]; simp; omega
      exact getD_of_ge _ _ w hge2

lemma wireRel_step_keep {n : ℕ} (T Z : Finset (Fin n)) (gs gates' : List Gate)
    (st : List (Sum Bool ℕ)) (g : Gate) (s : Sum Bool ℕ)
    (hrel : WireRel T Z gs gates' st)
    (hs : match s with
      | Sum.inl b =>
          ∀ x : Fin n → Bool,
            g.op.eval (g.inputs.map fun i => (wires gs (fixInput T Z x)).getD i false) = b
      | Sum.inr w' =>
          w' < n + gates'.length ∧
          ∀ x : Fin n → Bool,
            (wires gates' (List.ofFn x)).getD w' false =
              g.op.eval (g.inputs.map fun i => (wires gs (fixInput T Z x)).getD i false)) :
    WireRel T Z (gs ++ [g]) gates' (st ++ [s]) := by
  constructor
  · simp [hrel.1]; omega
  · intro w
    rcases lt_trichotomy w (n + gs.length) with hlt | heq | hgt
    · have hlt_st : w < st.length := by rw [hrel.1]; exact hlt
      rw [getD_append_lt st s (Sum.inl false) w hlt_st]
      have hstep : ∀ x : Fin n → Bool,
          (wires (gs ++ [g]) (fixInput T Z x)).getD w false =
            (wires gs (fixInput T Z x)).getD w false := by
        intro x
        rw [wires_append_singleton]
        apply getD_append_lt
        rw [wires_fixInput_length]
        exact hlt
      have hw := hrel.2 w
      cases hst : st.getD w (Sum.inl false) with
      | inl b =>
          rw [hst] at hw
          intro x
          rw [hstep x, hw x]
      | inr w' =>
          rw [hst] at hw
          refine ⟨hw.1, ?_⟩
          intro x
          rw [hstep x, hw.2 x]
    · subst heq
      have hst_eq : (st ++ [s]).getD (n + gs.length) (Sum.inl false) = s := by
        rw [← hrel.1]
        exact getD_append_eq st s (Sum.inl false)
      rw [hst_eq]
      have hstep : ∀ x : Fin n → Bool,
          (wires (gs ++ [g]) (fixInput T Z x)).getD (n + gs.length) false =
            g.op.eval (g.inputs.map fun i => (wires gs (fixInput T Z x)).getD i false) := by
        intro x
        rw [wires_append_singleton]
        have hlen : (wires gs (fixInput T Z x)).length = n + gs.length :=
          wires_fixInput_length T Z gs x
        rw [← hlen]
        exact getD_append_eq _ _ false
      cases s with
      | inl b =>
          intro x
          rw [hstep x, hs x]
      | inr w' =>
          refine ⟨hs.1, ?_⟩
          intro x
          rw [hstep x, hs.2 x]
    · have hge_st : (st ++ [s]).length ≤ w := by simp [hrel.1]; omega
      rw [getD_of_ge _ _ w hge_st]
      intro x
      have hge_w : (wires (gs ++ [g]) (fixInput T Z x)).length ≤ w := by
        rw [wires_fixInput_length]; simp; omega
      exact getD_of_ge _ _ w hge_w

lemma wireRel_step_push {n : ℕ} (T Z : Finset (Fin n)) (gs gates' : List Gate)
    (st : List (Sum Bool ℕ)) (g g' : Gate)
    (hrel : WireRel T Z gs gates' st)
    (hg' : ∀ x : Fin n → Bool,
      g'.op.eval (g'.inputs.map fun i => (wires gates' (List.ofFn x)).getD i false) =
        g.op.eval (g.inputs.map fun i => (wires gs (fixInput T Z x)).getD i false)) :
    WireRel T Z (gs ++ [g]) (gates' ++ [g']) (st ++ [Sum.inr (n + gates'.length)]) := by
  constructor
  · simp [hrel.1]; omega
  · intro w
    rcases lt_trichotomy w (n + gs.length) with hlt | heq | hgt
    · have hlt_st : w < st.length := by rw [hrel.1]; exact hlt
      rw [getD_append_lt st _ (Sum.inl false) w hlt_st]
      have hstep : ∀ x : Fin n → Bool,
          (wires (gs ++ [g]) (fixInput T Z x)).getD w false =
            (wires gs (fixInput T Z x)).getD w false := by
        intro x
        rw [wires_append_singleton]
        apply getD_append_lt
        rw [wires_fixInput_length]
        exact hlt
      have hw := hrel.2 w
      cases hst : st.getD w (Sum.inl false) with
      | inl b =>
          rw [hst] at hw
          intro x
          rw [hstep x, hw x]
      | inr w' =>
          rw [hst] at hw
          refine ⟨by simp; omega, ?_⟩
          intro x
          rw [hstep x, wires_append_singleton]
          have hlt' : w' < (wires gates' (List.ofFn x)).length := by
            rw [wires_ofFn_length]
            exact hw.1
          rw [getD_append_lt _ _ false w' hlt', hw.2 x]
    · subst heq
      have hst_eq : (st ++ [Sum.inr (n + gates'.length)]).getD (n + gs.length) (Sum.inl false) =
          Sum.inr (n + gates'.length) := by
        rw [← hrel.1]
        exact getD_append_eq st _ (Sum.inl false)
      rw [hst_eq]
      refine ⟨by simp, ?_⟩
      intro x
      rw [wires_append_singleton, wires_append_singleton]
      have hlen1 : (wires gates' (List.ofFn x)).length = n + gates'.length :=
        wires_ofFn_length gates' x
      have hlen2 : (wires gs (fixInput T Z x)).length = n + gs.length :=
        wires_fixInput_length T Z gs x
      conv_lhs => rw [← hlen1]
      conv_rhs => rw [← hlen2]
      rw [getD_append_eq, getD_append_eq]
      exact hg' x
    · have hge_st : (st ++ [Sum.inr (n + gates'.length)]).length ≤ w := by simp [hrel.1]; omega
      rw [getD_of_ge _ _ w hge_st]
      intro x
      have hge_w : (wires (gs ++ [g]) (fixInput T Z x)).length ≤ w := by
        rw [wires_fixInput_length]; simp; omega
      exact getD_of_ge _ _ w hge_w

lemma prop_gates {n : ℕ} (T Z : Finset (Fin n)) (gates : List Gate)
    (hgates : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∃ (gates' : List Gate) (st : List (Sum Bool ℕ)),
      (∀ g ∈ gates', IsValidGate g) ∧
      gates'.length ≤ gates.length ∧
      WireRel T Z gates gates' st := by
  revert hgates
  refine List.reverseRecOn gates ?_ ?_
  · intro _
    refine ⟨[], List.ofFn (fun i : Fin n =>
      if i ∈ T then Sum.inl true else if i ∈ Z then Sum.inl false else Sum.inr i.1),
      by simp, by simp, wireRel_base T Z⟩
  · intro gs g ih hgates
    have hgs : ∀ h ∈ gs, (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2 := by
      intro h hh
      exact hgates h (List.mem_append_left [g] hh)
    have hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 :=
      hgates g (List.mem_append_right gs (List.mem_singleton_self g))
    rcases ih hgs with ⟨gates', st, hvalid, hlen, hrel⟩
    rcases g with ⟨op, inps⟩
    dsimp only at hg
    rcases hg with ⟨hop, hinps⟩
    match inps with
    | [] =>
        rcases hop with rfl | rfl
        · refine ⟨gates', st ++ [Sum.inl true], hvalid, by simp; omega, ?_⟩
          refine wireRel_step_keep T Z gs gates' st ⟨GateOp.and, []⟩ (Sum.inl true) hrel ?_
          intro x
          exact eval_and_nil
        · refine ⟨gates', st ++ [Sum.inl false], hvalid, by simp; omega, ?_⟩
          refine wireRel_step_keep T Z gs gates' st ⟨GateOp.or, []⟩ (Sum.inl false) hrel ?_
          intro x
          exact eval_or_nil
    | [a] =>
        refine ⟨gates', st ++ [st.getD a (Sum.inl false)], hvalid, by simp; omega, ?_⟩
        refine wireRel_step_keep T Z gs gates' st ⟨op, [a]⟩ (st.getD a (Sum.inl false)) hrel ?_
        have ha := hrel.2 a
        cases hsa : st.getD a (Sum.inl false) with
        | inl b =>
            rw [hsa] at ha
            intro x
            rcases hop with rfl | rfl
            · simp only [List.map, eval_and_single, ha x]
            · simp only [List.map, eval_or_single, ha x]
        | inr a' =>
            rw [hsa] at ha
            refine ⟨ha.1, ?_⟩
            intro x
            rcases hop with rfl | rfl
            · simp only [List.map, eval_and_single, ha.2 x]
            · simp only [List.map, eval_or_single, ha.2 x]
    | [a, b] =>
        have ha := hrel.2 a
        have hb := hrel.2 b
        rcases hop with rfl | rfl
        · cases hsa : st.getD a (Sum.inl false) with
          | inl ba =>
              rw [hsa] at ha
              cases ba with
              | false =>
                  refine ⟨gates', st ++ [Sum.inl false], hvalid, by simp; omega, ?_⟩
                  refine wireRel_step_keep T Z gs gates' st ⟨GateOp.and, [a, b]⟩ (Sum.inl false) hrel ?_
                  intro x
                  simp only [List.map, eval_and_pair, ha x, Bool.false_and]
              | true =>
                  refine ⟨gates', st ++ [st.getD b (Sum.inl false)], hvalid, by simp; omega, ?_⟩
                  refine wireRel_step_keep T Z gs gates' st ⟨GateOp.and, [a, b]⟩ (st.getD b (Sum.inl false)) hrel ?_
                  cases hsb : st.getD b (Sum.inl false) with
                  | inl bb =>
                      rw [hsb] at hb
                      intro x
                      simp only [List.map, eval_and_pair, ha x, hb x, Bool.true_and]
                  | inr b' =>
                      rw [hsb] at hb
                      refine ⟨hb.1, ?_⟩
                      intro x
                      simp only [List.map, eval_and_pair, ha x, Bool.true_and, hb.2 x]
          | inr a' =>
              rw [hsa] at ha
              cases hsb : st.getD b (Sum.inl false) with
              | inl bb =>
                  rw [hsb] at hb
                  cases bb with
                  | false =>
                      refine ⟨gates', st ++ [Sum.inl false], hvalid, by simp; omega, ?_⟩
                      refine wireRel_step_keep T Z gs gates' st ⟨GateOp.and, [a, b]⟩ (Sum.inl false) hrel ?_
                      intro x
                      simp only [List.map, eval_and_pair, hb x, Bool.and_false]
                  | true =>
                      refine ⟨gates', st ++ [Sum.inr a'], hvalid, by simp; omega, ?_⟩
                      refine wireRel_step_keep T Z gs gates' st ⟨GateOp.and, [a, b]⟩ (Sum.inr a') hrel ?_
                      refine ⟨ha.1, ?_⟩
                      intro x
                      simp only [List.map, eval_and_pair, hb x, Bool.and_true, ha.2 x]
              | inr b' =>
                  rw [hsb] at hb
                  refine ⟨gates' ++ [⟨GateOp.and, [a', b']⟩],
                    st ++ [Sum.inr (n + gates'.length)], ?_, by simp; omega, ?_⟩
                  · intro h hh
                    rcases List.mem_append.mp hh with hh | hh
                    · exact hvalid h hh
                    · simp only [List.mem_singleton] at hh
                      subst hh
                      exact ⟨Or.inl rfl, rfl⟩
                  · refine wireRel_step_push T Z gs gates' st ⟨GateOp.and, [a, b]⟩
                      ⟨GateOp.and, [a', b']⟩ hrel ?_
                    intro x
                    simp only [List.map, eval_and_pair, ha.2 x, hb.2 x]
        · cases hsa : st.getD a (Sum.inl false) with
          | inl ba =>
              rw [hsa] at ha
              cases ba with
              | true =>
                  refine ⟨gates', st ++ [Sum.inl true], hvalid, by simp; omega, ?_⟩
                  refine wireRel_step_keep T Z gs gates' st ⟨GateOp.or, [a, b]⟩ (Sum.inl true) hrel ?_
                  intro x
                  simp only [List.map, eval_or_pair, ha x, Bool.true_or]
              | false =>
                  refine ⟨gates', st ++ [st.getD b (Sum.inl false)], hvalid, by simp; omega, ?_⟩
                  refine wireRel_step_keep T Z gs gates' st ⟨GateOp.or, [a, b]⟩ (st.getD b (Sum.inl false)) hrel ?_
                  cases hsb : st.getD b (Sum.inl false) with
                  | inl bb =>
                      rw [hsb] at hb
                      intro x
                      simp only [List.map, eval_or_pair, ha x, hb x, Bool.false_or]
                  | inr b' =>
                      rw [hsb] at hb
                      refine ⟨hb.1, ?_⟩
                      intro x
                      simp only [List.map, eval_or_pair, ha x, Bool.false_or, hb.2 x]
          | inr a' =>
              rw [hsa] at ha
              cases hsb : st.getD b (Sum.inl false) with
              | inl bb =>
                  rw [hsb] at hb
                  cases bb with
                  | true =>
                      refine ⟨gates', st ++ [Sum.inl true], hvalid, by simp; omega, ?_⟩
                      refine wireRel_step_keep T Z gs gates' st ⟨GateOp.or, [a, b]⟩ (Sum.inl true) hrel ?_
                      intro x
                      simp only [List.map, eval_or_pair, hb x, Bool.or_true]
                  | false =>
                      refine ⟨gates', st ++ [Sum.inr a'], hvalid, by simp; omega, ?_⟩
                      refine wireRel_step_keep T Z gs gates' st ⟨GateOp.or, [a, b]⟩ (Sum.inr a') hrel ?_
                      refine ⟨ha.1, ?_⟩
                      intro x
                      simp only [List.map, eval_or_pair, hb x, Bool.or_false, ha.2 x]
              | inr b' =>
                  rw [hsb] at hb
                  refine ⟨gates' ++ [⟨GateOp.or, [a', b']⟩],
                    st ++ [Sum.inr (n + gates'.length)], ?_, by simp; omega, ?_⟩
                  · intro h hh
                    rcases List.mem_append.mp hh with hh | hh
                    · exact hvalid h hh
                    · simp only [List.mem_singleton] at hh
                      subst hh
                      exact ⟨Or.inr rfl, rfl⟩
                  · refine wireRel_step_push T Z gs gates' st ⟨GateOp.or, [a, b]⟩
                      ⟨GateOp.or, [a', b']⟩ hrel ?_
                    intro x
                    simp only [List.map, eval_or_pair, ha.2 x, hb.2 x]
    | _ :: _ :: _ :: _ =>
        simp at hinps

lemma main :
    ∀ (n : ℕ) (gates : List Gate) (T Z : Finset (Fin n)),
      (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
      ∃ (gates' : List Gate) (r : ℕ → ℕ),
        (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
        gates'.length ≤ gates.length ∧
        ∀ o : ℕ,
          (∃ x y : Fin n → Bool,
            Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠
            Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) →
          ∀ x : Fin n → Bool,
            Circuit.eval ⟨gates', r o⟩ (List.ofFn x) =
            Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) := by
  intro n gates T Z hgates
  rcases prop_gates T Z gates hgates with ⟨gates', st, hvalid, hlen, hrel⟩
  refine ⟨gates', fun o => match st.getD o (Sum.inl false) with | Sum.inl _ => 0 | Sum.inr w' => w',
    hvalid, hlen, ?_⟩
  intro o hnc x
  have ho := hrel.2 o
  cases hso : st.getD o (Sum.inl false) with
  | inl b =>
      rw [hso] at ho
      rcases hnc with ⟨x1, x2, hne⟩
      exfalso
      apply hne
      have h1 : Circuit.eval ⟨gates, o⟩ (fixInput T Z x1) = b := ho x1
      have h2 : Circuit.eval ⟨gates, o⟩ (fixInput T Z x2) = b := ho x2
      exact h1.trans h2.symm
  | inr w' =>
      rw [hso] at ho
      dsimp only
      rw [hso]
      exact ho.2 x

end PEqualNP.Outside.L_meta_669_aux

theorem PEqualNP.Outside.L_meta_669 :
    ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) :=
  PEqualNP.Outside.L_meta_669_aux.main
