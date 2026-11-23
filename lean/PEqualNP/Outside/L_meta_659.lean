import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.Elim

namespace PEqualNP.Outside.L_meta_659_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open SimpleGraph

noncomputable def F {n : ℕ} (K : SimpleGraph (Fin n)) (A : Finset (Fin n)) (x : Fin n → Bool) :
    Bool :=
  @decide ((∃ a ∈ A, x a = true) ∨ ∃ u v : Fin n, K.Adj u v ∧ x u = true ∧ x v = true)
    (Classical.propDecidable _)

def Cov {n : ℕ} (K : SimpleGraph (Fin n)) (T : Finset (Fin n)) : Prop :=
  ∀ u v : Fin n, K.Adj u v → u ∈ T ∨ v ∈ T

def DepG {n k : ℕ} (G : Fin k → (Fin n → Bool) → Bool) (i : Fin n) : Prop :=
  ∃ (j : Fin k) (x : Fin n → Bool),
    G j (Function.update x i false) ≠ G j (Function.update x i true)

def MultiCirc (n k s : ℕ) (f : (Fin n → Bool) → Bool) (G : Fin k → (Fin n → Bool) → Bool) :
    Prop :=
  ∃ C : Circuit, FanInTwo C ∧ C.size ≤ s ∧
    ∃ (o1 : ℕ) (o : Fin k → ℕ), ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD o1 false = f x ∧
      ∀ j : Fin k, (C.wires (List.ofFn x)).getD (o j) false = G j x

def CircG (n k t : ℕ) (G : Fin k → (Fin n → Bool) → Bool) : Prop :=
  ∃ C : Circuit, FanInTwo C ∧ C.size ≤ t ∧
    ∃ o : Fin k → ℕ, ∀ (x : Fin n → Bool) (j : Fin k),
      (C.wires (List.ofFn x)).getD (o j) false = G j x

theorem F_true {n : ℕ} (K : SimpleGraph (Fin n)) (A : Finset (Fin n)) (x : Fin n → Bool) :
    F K A x = true ↔
      ((∃ a ∈ A, x a = true) ∨ ∃ u v : Fin n, K.Adj u v ∧ x u = true ∧ x v = true) := by
  unfold F
  exact @decide_eq_true_iff _ (Classical.propDecidable _)

theorem F_eq {n : ℕ} (K K' : SimpleGraph (Fin n)) (A A' : Finset (Fin n)) (x y : Fin n → Bool)
    (h : ((∃ a ∈ A, x a = true) ∨ ∃ u v : Fin n, K.Adj u v ∧ x u = true ∧ x v = true) ↔
      ((∃ a ∈ A', y a = true) ∨ ∃ u v : Fin n, K'.Adj u v ∧ y u = true ∧ y v = true)) :
    F K A x = F K' A' y := by
  rw [Bool.eq_iff_iff, F_true, F_true]
  exact h

theorem F_zero {n : ℕ} (K : SimpleGraph (Fin n)) (A : Finset (Fin n)) :
    F K A (fun _ => false) = false := by
  rw [Bool.eq_false_iff, ne_eq, F_true]
  simp

theorem F_nc {n : ℕ} (K : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (h : A.Nonempty ∨ ∃ u v : Fin n, K.Adj u v) :
    ∃ x y : Fin n → Bool, F K A x ≠ F K A y := by
  refine ⟨fun _ => true, fun _ => false, ?_⟩
  rw [F_zero]
  have : F K A (fun _ => true) = true := by
    rw [F_true]
    rcases h with ⟨a, ha⟩ | ⟨u, v, huv⟩
    · exact Or.inl ⟨a, ha, rfl⟩
    · exact Or.inr ⟨u, v, huv, rfl, rfl⟩
  rw [this]
  simp

theorem F_dep_edge {n : ℕ} (K : SimpleGraph (Fin n)) (A : Finset (Fin n)) (u v : Fin n)
    (huv : K.Adj u v) (hv : v ∉ A) :
    ∃ x : Fin n → Bool, F K A (Function.update x u (!x u)) ≠ F K A x := by
  have hne : u ≠ v := huv.ne
  refine ⟨Function.update (fun _ => false) v true, ?_⟩
  have h1 : F K A (Function.update (Function.update (fun _ => false) v true) u
      (!(Function.update (fun _ => false) v true u))) = true := by
    rw [F_true]
    right
    refine ⟨u, v, huv, ?_, ?_⟩
    · simp [Function.update_of_ne hne]
    · simp [Function.update_of_ne hne.symm]
  have h2 : F K A (Function.update (fun _ => false) v true) = false := by
    rw [Bool.eq_false_iff, ne_eq, F_true]
    rintro (⟨a, ha, hx⟩ | ⟨i, j, hij, hi, hj⟩)
    · by_cases hav : a = v
      · exact hv (hav ▸ ha)
      · simp [Function.update_of_ne hav] at hx
    · have hiv : i = v := by
        by_contra h
        simp [Function.update_of_ne h] at hi
      have hjv : j = v := by
        by_contra h
        simp [Function.update_of_ne h] at hj
      exact hij.ne (hiv.trans hjv.symm)
  rw [h1, h2]
  simp

theorem F_dep_A {n : ℕ} (K : SimpleGraph (Fin n)) (A : Finset (Fin n)) (a : Fin n)
    (ha : a ∈ A) :
    ∃ x : Fin n → Bool, F K A (Function.update x a (!x a)) ≠ F K A x := by
  refine ⟨fun _ => false, ?_⟩
  rw [F_zero]
  have : F K A (Function.update (fun _ => false) a (!false)) = true := by
    rw [F_true]
    exact Or.inl ⟨a, ha, by simp⟩
  rw [this]
  simp

theorem not_depG_update {n k : ℕ} (G : Fin k → (Fin n → Bool) → Bool) (v : Fin n)
    (h : ¬ DepG G v) (j : Fin k) (x : Fin n → Bool) (b : Bool) :
    G j (Function.update x v b) = G j x := by
  have h1 : ∀ y : Fin n → Bool,
      G j (Function.update y v false) = G j (Function.update y v true) := by
    intro y
    by_contra hne
    exact h ⟨j, y, hne⟩
  have h2 : Function.update x v (x v) = x := Function.update_eq_self v x
  cases hb : b <;> cases hx : x v
  · rw [← hx, h2]
  · rw [h1 x, ← hx, h2]
  · rw [← h1 x, ← hx, h2]
  · rw [← hx, h2]

theorem restrict_false_A {n : ℕ} (K : SimpleGraph (Fin n)) (A : Finset (Fin n)) (a : Fin n)
    (hK : ∀ u v : Fin n, ¬ K.Adj u v) (x : Fin n → Bool) :
    F K A (Function.update x a false) = F K (A.erase a) x := by
  apply F_eq
  constructor
  · rintro (⟨b, hb, h⟩ | ⟨u, v, huv, _, _⟩)
    · have hba : b ≠ a := by
        rintro rfl
        simp at h
      exact Or.inl ⟨b, Finset.mem_erase.2 ⟨hba, hb⟩, by rwa [Function.update_of_ne hba] at h⟩
    · exact absurd huv (hK u v)
  · rintro (⟨b, hb, h⟩ | ⟨u, v, huv, _, _⟩)
    · obtain ⟨hba, hbA⟩ := Finset.mem_erase.1 hb
      exact Or.inl ⟨b, hbA, by rwa [Function.update_of_ne hba]⟩
    · exact absurd huv (hK u v)

theorem restrict_false_edge {n : ℕ} (K : SimpleGraph (Fin n)) (A : Finset (Fin n)) (l p : Fin n)
    (hlA : l ∉ A) (hleaf : ∀ w, K.Adj l w → w = p) (x : Fin n → Bool) :
    F K A (Function.update x l false) = F (K.deleteEdges {s(l, p)}) A x := by
  apply F_eq
  apply or_congr
  · constructor
    · rintro ⟨a, ha, h⟩
      have hal : a ≠ l := fun e => hlA (e ▸ ha)
      exact ⟨a, ha, by rwa [Function.update_of_ne hal] at h⟩
    · rintro ⟨a, ha, h⟩
      have hal : a ≠ l := fun e => hlA (e ▸ ha)
      exact ⟨a, ha, by rwa [Function.update_of_ne hal]⟩
  · constructor
    · rintro ⟨i, j, hij, hi, hj⟩
      have hil : i ≠ l := by rintro rfl; simp at hi
      have hjl : j ≠ l := by rintro rfl; simp at hj
      refine ⟨i, j, ?_, by rwa [Function.update_of_ne hil] at hi,
        by rwa [Function.update_of_ne hjl] at hj⟩
      rw [deleteEdges_adj]
      refine ⟨hij, ?_⟩
      simp [hil, hjl]
    · rintro ⟨i, j, hij, hi, hj⟩
      rw [deleteEdges_adj] at hij
      obtain ⟨hij, hne⟩ := hij
      have hil : i ≠ l := by
        rintro rfl
        have := hleaf j hij
        subst this
        exact hne rfl
      have hjl : j ≠ l := by
        rintro rfl
        have := hleaf i hij.symm
        subst this
        exact hne Sym2.eq_swap
      exact ⟨i, j, hij, by rwa [Function.update_of_ne hil], by rwa [Function.update_of_ne hjl]⟩

theorem restrict_true_leaf {n : ℕ} (K : SimpleGraph (Fin n)) (A : Finset (Fin n)) (l p q : Fin n)
    (hlA : l ∉ A) (hlp : K.Adj l p) (hleaf : ∀ w, K.Adj l w → w = p)
    (hp : ∀ w, K.Adj p w → w = l ∨ w = q) (x : Fin n → Bool) :
    F K A (Function.update x l true) = F (K.deleteEdges {s(p, l), s(p, q)}) (insert p A) x := by
  have hpl : p ≠ l := hlp.ne.symm
  have hA : ∀ a ∈ A, Function.update x l true a = x a := fun a ha =>
    Function.update_of_ne (by rintro rfl; exact hlA ha) _ _
  have hG1 : ∀ i j, (K.deleteEdges {s(p, l), s(p, q)}).Adj i j → i ≠ p ∧ i ≠ l := by
    intro i j hij
    rw [deleteEdges_adj] at hij
    obtain ⟨hij, hne⟩ := hij
    constructor
    · rintro rfl
      rcases hp j hij with rfl | rfl
      · exact hne (by simp)
      · exact hne (by simp)
    · rintro rfl
      have := hleaf j hij
      subst this
      exact hne (by simp [Sym2.eq_swap])
  apply F_eq
  constructor
  · rintro (⟨a, ha, h⟩ | ⟨i, j, hij, hi, hj⟩)
    · exact Or.inl ⟨a, Finset.mem_insert_of_mem ha, by rwa [hA a ha] at h⟩
    · by_cases hip : i = p
      · subst hip
        exact Or.inl ⟨i, Finset.mem_insert_self _ _, by rwa [Function.update_of_ne hpl] at hi⟩
      by_cases hjp : j = p
      · subst hjp
        exact Or.inl ⟨j, Finset.mem_insert_self _ _, by rwa [Function.update_of_ne hpl] at hj⟩
      have hil : i ≠ l := by
        rintro rfl; exact hjp (hleaf j hij)
      have hjl : j ≠ l := by
        rintro rfl; exact hip (hleaf i hij.symm)
      right
      refine ⟨i, j, ?_, by rwa [Function.update_of_ne hil] at hi,
        by rwa [Function.update_of_ne hjl] at hj⟩
      rw [deleteEdges_adj]
      refine ⟨hij, ?_⟩
      simp [hip, hjp]
  · rintro (⟨a, ha, h⟩ | ⟨i, j, hij, hi, hj⟩)
    · rcases Finset.mem_insert.1 ha with rfl | ha
      · right
        exact ⟨l, a, hlp, by simp, by rwa [Function.update_of_ne hpl]⟩
      · exact Or.inl ⟨a, ha, by rwa [hA a ha]⟩
    · right
      have hi' := hG1 i j hij
      have hj' := hG1 j i hij.symm
      rw [deleteEdges_adj] at hij
      exact ⟨i, j, hij.1, by rwa [Function.update_of_ne hi'.2],
        by rwa [Function.update_of_ne hj'.2]⟩

def orList (m : ℕ) : List ℕ → List Gate × ℕ
  | [] => ([], 0)
  | [w] => ([], w)
  | w :: w' :: rest =>
    let r := orList m (w' :: rest)
    (r.1 ++ [⟨GateOp.or, [w, r.2]⟩], m + r.1.length)

theorem orList_spec (m : ℕ) (ws : List ℕ) (hws : ws ≠ []) (hb : ∀ w ∈ ws, w < m) :
    (∀ g ∈ (orList m ws).1, Ok g) ∧
    (orList m ws).1.length = ws.length - 1 ∧
    (orList m ws).2 < m + (orList m ws).1.length ∧
    ∀ v : List Bool, v.length = m →
      ((wiresFrom (orList m ws).1 v).getD (orList m ws).2 false = true ↔
        ∃ w ∈ ws, v.getD w false = true) := by
  induction ws with
  | nil => exact absurd rfl hws
  | cons w tail ih =>
    cases tail with
    | nil =>
      refine ⟨by simp [orList], by simp [orList], ?_, ?_⟩
      · simp only [orList, List.length_nil, add_zero]
        exact hb w List.mem_cons_self
      · intro v _
        simp [orList, wiresFrom]
    | cons w' rest =>
      have hne : w' :: rest ≠ [] := List.cons_ne_nil _ _
      have hb' : ∀ u ∈ w' :: rest, u < m := fun u hu => hb u (List.mem_cons_of_mem _ hu)
      obtain ⟨hok, hlen, hout, hev⟩ := ih hne hb'
      set r := orList m (w' :: rest) with hr
      have hw : w < m := hb w List.mem_cons_self
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro g hg
        simp only [orList, ← hr, List.mem_append, List.mem_singleton] at hg
        rcases hg with hg | rfl
        · exact hok g hg
        · simp [Ok]
      · simp only [orList, ← hr, List.length_append, List.length_cons]
        rw [hlen]
        simp
      · simp only [orList, ← hr, List.length_append, List.length_singleton]
        omega
      · intro v hv
        simp only [orList, ← hr]
        rw [wiresFrom_append]
        set v1 := wiresFrom r.1 v with hv1
        have lv1 : v1.length = m + r.1.length := by rw [hv1, length_wiresFrom, hv]
        have hstep : wiresFrom [⟨GateOp.or, [w, r.2]⟩] v1 =
            v1 ++ [(v1.getD w false || v1.getD r.2 false)] := by
          simp [wiresFrom, GateOp.eval]
        rw [hstep, ← lv1, getD_snoc_eq]
        have hw1 : v1.getD w false = v.getD w false := by
          rw [hv1, getD_wiresFrom _ _ _ (by omega)]
        rw [hw1, Bool.or_eq_true, hev v hv]
        simp

theorem pair_inj_left {n : ℕ} (u : Fin n) :
    Function.Injective (fun v : Fin n => (s(u, v) : Sym2 (Fin n))) := by
  intro v1 v2 h
  rw [Sym2.eq_iff] at h
  rcases h with ⟨_, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

theorem build_cover_terms {n : ℕ} (T : Finset (Fin n)) :
    ∀ (m : ℕ), n ≤ m → ∀ (K : SimpleGraph (Fin n)), Cov K T →
      ∃ (gs : List Gate) (terms : List ℕ),
        (∀ g ∈ gs, Ok g) ∧
        gs.length = K.edgeSet.ncard ∧
        terms.length ≤ T.card ∧
        (∀ w ∈ terms, w < m + gs.length) ∧
        ((∃ a b : Fin n, K.Adj a b) → terms ≠ []) ∧
        ∀ (x : Fin n → Bool) (w0 : List Bool),
          w0.length = m → (∀ i : Fin n, w0.getD i.val false = x i) →
          ((∃ w ∈ terms, (wiresFrom gs w0).getD w false = true) ↔
            ∃ a b : Fin n, K.Adj a b ∧ x a = true ∧ x b = true) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro m _ K hCov
    have hno : ∀ a b : Fin n, ¬ K.Adj a b := fun a b hab => by
      rcases hCov a b hab with h | h <;> simp at h
    have hcard : K.edgeSet.ncard = 0 := by
      have : K.edgeSet = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.2
        intro e
        induction e using Sym2.ind with
        | _ a b => exact fun he => hno a b (K.mem_edgeSet.1 he)
      rw [this, Set.ncard_empty]
    refine ⟨[], [], by simp, by simp [hcard], by simp, by simp, ?_, ?_⟩
    · rintro ⟨a, b, hab⟩
      exact absurd hab (hno a b)
    · intro x w0 _ _
      constructor
      · rintro ⟨w, hw, _⟩; simp at hw
      · rintro ⟨a, b, hab, _, _⟩; exact absurd hab (hno a b)
  | @insert u T hu ih =>
    intro m hm K hCov
    let N : Finset (Fin n) := Finset.univ.filter (fun v => K.Adj u v)
    let E_u : Finset (Sym2 (Fin n)) := N.image (fun v => s(u, v))
    let K' : SimpleGraph (Fin n) := K.deleteEdges (E_u : Set (Sym2 (Fin n)))
    have hEu_sub : (E_u : Set (Sym2 (Fin n))) ⊆ K.edgeSet := by
      intro e he
      rw [Finset.mem_coe, Finset.mem_image] at he
      obtain ⟨v, hv, rfl⟩ := he
      exact K.mem_edgeSet.2 (Finset.mem_filter.1 hv).2
    have hEu_card : (E_u : Set (Sym2 (Fin n))).ncard = N.card := by
      rw [Set.ncard_coe_finset]
      exact Finset.card_image_of_injective N (pair_inj_left u)
    have hncard : K'.edgeSet.ncard + N.card = K.edgeSet.ncard := by
      rw [edgeSet_deleteEdges, ← hEu_card]
      have hdisj : Disjoint (K.edgeSet \ (E_u : Set (Sym2 (Fin n)))) (E_u : Set (Sym2 (Fin n))) :=
        disjoint_sdiff_self_left
      rw [← Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
        Set.sdiff_union_of_subset hEu_sub]
    have hCov' : Cov K' T := by
      intro a b hab
      rw [deleteEdges_adj] at hab
      obtain ⟨hab, hnot⟩ := hab
      have hau : a ≠ u := by
        rintro rfl
        apply hnot
        rw [Finset.mem_coe, Finset.mem_image]
        exact ⟨b, Finset.mem_filter.2 ⟨Finset.mem_univ _, hab⟩, rfl⟩
      have hbu : b ≠ u := by
        rintro rfl
        apply hnot
        rw [Finset.mem_coe, Finset.mem_image]
        exact ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, hab.symm⟩, Sym2.eq_swap⟩
      rcases hCov a b hab with h | h
      · rcases Finset.mem_insert.1 h with rfl | hT
        · exact absurd rfl hau
        · exact Or.inl hT
      · rcases Finset.mem_insert.1 h with rfl | hT
        · exact absurd rfl hbu
        · exact Or.inr hT
    by_cases hN : N.Nonempty
    · let ws : List ℕ := N.toList.map Fin.val
      have hws_len : ws.length = N.card := by simp [ws]
      have hws_ne : ws ≠ [] := by
        intro h
        have := congrArg List.length h
        rw [hws_len, List.length_nil] at this
        have := Finset.card_pos.2 hN
        omega
      have hws_b : ∀ w ∈ ws, w < m := by
        intro w hw
        obtain ⟨v, _, rfl⟩ := List.mem_map.1 hw
        exact lt_of_lt_of_le v.isLt hm
      obtain ⟨hok_or, hlen_or, hout_or, hev_or⟩ := orList_spec m ws hws_ne hws_b
      let gs_or := (orList m ws).1
      let w_or := (orList m ws).2
      let gs_u := gs_or ++ [⟨GateOp.and, [u.val, w_or]⟩]
      let w_u := m + gs_or.length
      have hgs_u_len : gs_u.length = N.card := by
        have hpos : 1 ≤ N.card := Finset.card_pos.2 hN
        simp only [gs_u, List.length_append, List.length_singleton]
        rw [show gs_or.length = ws.length - 1 from hlen_or, hws_len]
        omega
      have hgs_u_ok : ∀ g ∈ gs_u, Ok g := by
        intro g hg
        simp only [gs_u, List.mem_append, List.mem_singleton] at hg
        rcases hg with hg | rfl
        · exact hok_or g hg
        · simp [Ok]
      obtain ⟨gs', terms', hok', hlen', htc', htb', _, hev'⟩ :=
        ih (m + gs_u.length) (by omega) K' hCov'
      refine ⟨gs_u ++ gs', w_u :: terms', ?_, ?_, ?_, ?_, by simp, ?_⟩
      · intro g hg
        rcases List.mem_append.1 hg with hg | hg
        · exact hgs_u_ok g hg
        · exact hok' g hg
      · simp only [List.length_append]
        rw [hgs_u_len, hlen']
        omega
      · simp only [List.length_cons, Finset.card_insert_of_notMem hu]
        omega
      · intro w hw
        rcases List.mem_cons.1 hw with rfl | hw'
        · simp only [w_u, gs_u, List.length_append, List.length_singleton]
          omega
        · have := htb' w hw'
          simp only [List.length_append]
          omega
      · intro x w0 hw0 hx0
        rw [wiresFrom_append]
        set w1 := wiresFrom gs_u w0 with hw1
        have lw1 : w1.length = m + gs_u.length := by rw [hw1, length_wiresFrom, hw0]
        have hx1 : ∀ i : Fin n, w1.getD i.val false = x i := by
          intro i
          rw [hw1, getD_wiresFrom _ _ _ (by have := i.isLt; omega)]
          exact hx0 i
        have hwu_eval : w1.getD w_u false = true ↔
            x u = true ∧ ∃ v : Fin n, K.Adj u v ∧ x v = true := by
          have hw1' : w1 = wiresFrom [⟨GateOp.and, [u.val, w_or]⟩] (wiresFrom gs_or w0) := by
            rw [hw1, show gs_u = gs_or ++ [⟨GateOp.and, [u.val, w_or]⟩] from rfl, wiresFrom_append]
          set v1 := wiresFrom gs_or w0 with hv1
          have lv1 : v1.length = w_u := by rw [hv1, length_wiresFrom, hw0]
          have hstep : wiresFrom [⟨GateOp.and, [u.val, w_or]⟩] v1 =
              v1 ++ [(v1.getD u.val false && v1.getD w_or false)] := by
            simp [wiresFrom, GateOp.eval]
          rw [hw1', hstep, ← lv1, getD_snoc_eq, Bool.and_eq_true]
          have hu1 : v1.getD u.val false = x u := by
            rw [hv1, getD_wiresFrom _ _ _ (by have := u.isLt; omega)]
            exact hx0 u
          rw [hu1, hev_or w0 hw0]
          constructor
          · rintro ⟨hxu, w, hw, hvw⟩
            obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
            rw [Finset.mem_toList, Finset.mem_filter] at hv
            rw [hx0 v] at hvw
            exact ⟨hxu, v, hv.2, hvw⟩
          · rintro ⟨hxu, v, huv, hxv⟩
            refine ⟨hxu, v.val, List.mem_map.2 ⟨v, Finset.mem_toList.2
              (Finset.mem_filter.2 ⟨Finset.mem_univ _, huv⟩), rfl⟩, ?_⟩
            rw [hx0 v]
            exact hxv
        have hwu_final : (wiresFrom gs' w1).getD w_u false = w1.getD w_u false := by
          apply getD_wiresFrom
          rw [lw1]
          simp only [w_u, gs_u, List.length_append, List.length_singleton]
          omega
        constructor
        · rintro ⟨w, hw, hwt⟩
          rcases List.mem_cons.1 hw with rfl | hw'
          · rw [hwu_final, hwu_eval] at hwt
            obtain ⟨hxu, v, huv, hxv⟩ := hwt
            exact ⟨u, v, huv, hxu, hxv⟩
          · obtain ⟨a, b, hab', hxa, hxb⟩ := (hev' x w1 lw1 hx1).1 ⟨w, hw', hwt⟩
            exact ⟨a, b, (deleteEdges_adj.1 hab').1, hxa, hxb⟩
        · rintro ⟨a, b, hab, hxa, hxb⟩
          by_cases hau : a = u
          · subst hau
            refine ⟨w_u, List.mem_cons_self, ?_⟩
            rw [hwu_final, hwu_eval]
            exact ⟨hxa, b, hab, hxb⟩
          · by_cases hbu : b = u
            · subst hbu
              refine ⟨w_u, List.mem_cons_self, ?_⟩
              rw [hwu_final, hwu_eval]
              exact ⟨hxb, a, hab.symm, hxa⟩
            · have hab' : K'.Adj a b := by
                rw [deleteEdges_adj]
                refine ⟨hab, ?_⟩
                rw [Finset.mem_coe, Finset.mem_image]
                rintro ⟨v, _, hv⟩
                rw [Sym2.eq_iff] at hv
                rcases hv with ⟨h1, _⟩ | ⟨h1, _⟩
                · exact hau h1.symm
                · exact hbu h1.symm
              obtain ⟨w, hw', hwt⟩ := (hev' x w1 lw1 hx1).2 ⟨a, b, hab', hxa, hxb⟩
              exact ⟨w, List.mem_cons_of_mem _ hw', hwt⟩
    · rw [Finset.not_nonempty_iff_eq_empty] at hN
      have hKeq : K' = K := by
        ext a b
        simp [K', E_u, hN]
      have hN0 : N.card = 0 := by rw [hN]; simp
      obtain ⟨gs', terms', hok', hlen', htc', htb', hne', hev'⟩ := ih m hm K' hCov'
      rw [hKeq] at hlen' hne' hev'
      refine ⟨gs', terms', hok', hlen', ?_, htb', hne', hev'⟩
      rw [Finset.card_insert_of_notMem hu]
      omega

theorem upper_bound (n k s : ℕ) (K : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (G : Fin k → (Fin n → Bool) → Bool)
    (hNonempty : A.Nonempty ∨ ∃ u v : Fin n, K.Adj u v)
    (hGnc : ∀ j : Fin k, ∃ y y' : Fin n → Bool, G j y ≠ G j y')
    (T : Finset (Fin n)) (t : ℕ) (hCov : Cov K T)
    (hBound : A.card + K.edgeSet.ncard + T.card + t ≤ s + 1)
    (hCG : CircG n k t G) :
    MultiCirc n k s (F K A) G := by
  obtain ⟨C, hFit, hSize, o, hEv⟩ := hCG
  have hSize' : C.gates.length ≤ t := hSize
  let m := n + C.gates.length
  obtain ⟨gs_K, terms_K, hok_K, hlen_K, htc_K, htb_K, hne_K, hev_K⟩ :=
    build_cover_terms T m (by omega) K hCov
  let terms_A : List ℕ := A.toList.map Fin.val
  let all_terms : List ℕ := terms_A ++ terms_K
  have hall_len : all_terms.length = A.card + terms_K.length := by
    simp [all_terms, terms_A]
  have hall_ne : all_terms ≠ [] := by
    rcases hNonempty with ⟨a, ha⟩ | hE
    · intro h
      have hmem : a.val ∈ all_terms :=
        List.mem_append_left _ (List.mem_map.2 ⟨a, Finset.mem_toList.2 ha, rfl⟩)
      rw [h] at hmem
      simp at hmem
    · intro h
      have := hne_K hE
      simp only [all_terms, List.append_eq_nil_iff] at h
      exact this h.2
  have hall_b : ∀ w ∈ all_terms, w < m + gs_K.length := by
    intro w hw
    rcases List.mem_append.1 hw with hwA | hwK
    · obtain ⟨a, _, rfl⟩ := List.mem_map.1 hwA
      have := a.isLt
      omega
    · exact htb_K w hwK
  obtain ⟨hok_or, hlen_or, _, hev_or⟩ := orList_spec (m + gs_K.length) all_terms hall_ne hall_b
  let gs_or := (orList (m + gs_K.length) all_terms).1
  let o1 := (orList (m + gs_K.length) all_terms).2
  have hpos_terms : 1 ≤ all_terms.length := by
    cases h : all_terms with
    | nil => exact absurd h hall_ne
    | cons _ _ => simp
  refine ⟨⟨C.gates ++ gs_K ++ gs_or, o1⟩, ?_, ?_, o1, o, ?_⟩
  · intro g hg
    simp only [List.mem_append] at hg
    rcases hg with (hg | hg) | hg
    · exact hFit g hg
    · exact hok_K g hg
    · exact hok_or g hg
  · show (C.gates ++ gs_K ++ gs_or).length ≤ s
    simp only [List.length_append]
    rw [hlen_K, show gs_or.length = all_terms.length - 1 from hlen_or]
    omega
  · intro x
    have hcw_len : (C.wires (List.ofFn x)).length = m := by
      rw [wires_eq, length_wiresFrom]
      simp [m]
    have hx0 : ∀ i : Fin n, (C.wires (List.ofFn x)).getD i.val false = x i := by
      intro i
      rw [wires_eq, getD_wiresFrom _ _ _ (by simp)]
      simp
    have hw_all : (Circuit.mk (C.gates ++ gs_K ++ gs_or) o1).wires (List.ofFn x) =
        wiresFrom gs_or (wiresFrom gs_K (C.wires (List.ofFn x))) := by
      rw [wires_eq, wiresFrom_append, wiresFrom_append]
      rfl
    constructor
    · rw [hw_all, Bool.eq_iff_iff, F_true]
      have hlen1 : (wiresFrom gs_K (C.wires (List.ofFn x))).length = m + gs_K.length := by
        rw [length_wiresFrom, hcw_len]
      rw [hev_or _ hlen1]
      constructor
      · rintro ⟨w, hw, hwt⟩
        rcases List.mem_append.1 hw with hwA | hwK
        · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hwA
          rw [Finset.mem_toList] at ha
          rw [getD_wiresFrom _ _ _ (by rw [hcw_len]; have := a.isLt; omega), hx0 a] at hwt
          exact Or.inl ⟨a, ha, hwt⟩
        · exact Or.inr ((hev_K x _ hcw_len hx0).1 ⟨w, hwK, hwt⟩)
      · rintro (⟨a, ha, hxa⟩ | hE)
        · refine ⟨a.val, List.mem_append_left _
            (List.mem_map.2 ⟨a, Finset.mem_toList.2 ha, rfl⟩), ?_⟩
          rw [getD_wiresFrom _ _ _ (by rw [hcw_len]; have := a.isLt; omega), hx0 a]
          exact hxa
        · obtain ⟨w, hwK, hwt⟩ := (hev_K x _ hcw_len hx0).2 hE
          exact ⟨w, List.mem_append_right _ hwK, hwt⟩
    · intro j
      have hoj_lt : o j < m := by
        by_contra hge
        push Not at hge
        obtain ⟨y, y', hne⟩ := hGnc j
        apply hne
        rw [← hEv y j, ← hEv y' j]
        have hy : (C.wires (List.ofFn y)).length = m := by
          rw [wires_eq, length_wiresFrom]; simp [m]
        have hy' : (C.wires (List.ofFn y')).length = m := by
          rw [wires_eq, length_wiresFrom]; simp [m]
        rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      rw [hw_all, ← wiresFrom_append, getD_wiresFrom _ _ _ (by omega)]
      exact hEv x j

def initStatsAt (n : ℕ) (v : Fin n) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => if i = v then Stat.const b else Stat.wire i.val)

theorem initStatsAt_len (n : ℕ) (v : Fin n) (b : Bool) :
    (initStatsAt n v b).length = n := by
  simp [initStatsAt]

theorem initStatsAt_at (n : ℕ) (v : Fin n) (b : Bool) :
    (initStatsAt n v b).getD v.val (Stat.const false) = Stat.const b := by
  rw [initStatsAt, List.getD_eq_getElem _ _ (by simp)]
  simp

theorem inv_initAt (n : ℕ) (v : Fin n) (b : Bool) (x : Fin n → Bool) :
    Inv n (List.ofFn x) (List.ofFn (Function.update x v b)) (initStatsAt n v b, []) := by
  refine ⟨by simp [initStatsAt], ?_⟩
  intro i
  by_cases hi : i < n
  · have hget : (initStatsAt n v b).getD i (Stat.const false) =
        if (⟨i, hi⟩ : Fin n) = v then Stat.const b else Stat.wire i := by
      rw [initStatsAt, List.getD_eq_getElem _ _ (by simp; exact hi)]
      simp
    rw [hget]
    by_cases hv : (⟨i, hi⟩ : Fin n) = v
    · simp only [hv, ↓reduceIte, Stat.Valid, Stat.val]
      refine ⟨trivial, ?_⟩
      rw [List.getD_eq_getElem _ _ (by simp; exact hi), List.getElem_ofFn, hv]
      simp
    · simp only [hv, ↓reduceIte, Stat.Valid, Stat.val]
      refine ⟨by simp [hi], ?_⟩
      change (List.ofFn x).getD i false = (List.ofFn (Function.update x v b)).getD i false
      rw [List.getD_eq_getElem _ _ (by simp; exact hi), List.getElem_ofFn,
        List.getD_eq_getElem _ _ (by simp; exact hi), List.getElem_ofFn,
        Function.update_of_ne hv]
  · rw [List.getD_eq_default _ _ (by simp [initStatsAt]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

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

theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Stat.const b ∈ ins) : ∃ c, (simplify op m ins).2 = Stat.const c := by
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
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Stat.const false) = Stat.const c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
  rw [hnone]; simp

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Stat.const false) = Stat.const c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Stat.const false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2 := getD_snoc_eq _ _ _
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

theorem supp_noread_at {n : ℕ} (v : Fin n) (D : ℕ → Prop) (gs : List Gate) :
    ∀ L : List (Finset (Fin n)),
    (∀ g ∈ gs, ∀ a ∈ g.inputs, ¬ D a) → (∀ j : ℕ, ¬ D j → v ∉ L.getD j ∅) →
    ∀ j : ℕ, ¬ D j → v ∉ (suppsFrom gs L).getD j ∅ := by
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
      exact h a (hno g List.mem_cons_self a ha) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem inputSupps_noread_at {n : ℕ} (v : Fin n) :
    ∀ j : ℕ, j ≠ v.val → v ∉ (inputSupps n).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n
  · have e : (inputSupps n).getD j ∅ = {⟨j, hlt⟩} := inputSupps_getD n j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem dep_mem_supp {n : ℕ} (gs : List Gate) (o : ℕ) (f : (Fin n → Bool) → Bool) (v : Fin n)
    (hevg : ∀ x : Fin n → Bool, (wiresFrom gs (List.ofFn x)).getD o false = f x)
    (hdep : ∃ x : Fin n → Bool, f (Function.update x v (!x v)) ≠ f x) :
    v ∈ (suppsFrom gs (inputSupps n)).getD o ∅ := by
  by_contra hns
  obtain ⟨x, hx⟩ := hdep
  apply hx
  have hag := (agree_wiresFrom (Function.update x v (!x v)) x gs _ _ _
    (agree_inputs _ _)).2.2 o (by
      intro k hk
      have : k ≠ v := fun e => hns (e ▸ hk)
      simp [Function.update_of_ne this])
  rw [← hevg, ← hevg]
  exact hag

def statWire : Stat → ℕ
  | Stat.wire j => j
  | Stat.const _ => 0

theorem stat_eq_wire_of_nc {n : ℕ} (st : Stat) (gs' : List Gate) (g : (Fin n → Bool) → Bool)
    (hval : ∀ x : Fin n → Bool, st.val (wiresFrom gs' (List.ofFn x)) = g x)
    (hnc : ∃ y y' : Fin n → Bool, g y ≠ g y') :
    st = Stat.wire (statWire st) := by
  cases st with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y']
    rfl
  | wire j => rfl

theorem multi_elim_one_drop_o1 (n k s : ℕ) (f : (Fin n → Bool) → Bool)
    (G : Fin k → (Fin n → Bool) → Bool) (v w : Fin n) (hvw : w ≠ v)
    (hdepv : ∃ x : Fin n → Bool, f (Function.update x v (!x v)) ≠ f x)
    (hdepw : ∃ x : Fin n → Bool, f (Function.update x w (!x w)) ≠ f x)
    (hGnc : ∀ j : Fin k, ∃ y y' : Fin n → Bool, G j y ≠ G j y')
    (hnoG : ¬ DepG G v)
    (hMC : MultiCirc n k s f G) :
    ∃ s' : ℕ, s' + 1 ≤ s ∧ CircG n k s' G := by
  obtain ⟨C, hFit, hSize, o1, o, hEv⟩ := hMC
  have hSize' : C.gates.length ≤ s := hSize
  set gs := C.gates.map normGate with hgs
  have hlen_gs : gs.length = C.gates.length := by simp [hgs]
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hFit g0 hg0)
  have hevg1 : ∀ x : Fin n → Bool, (wiresFrom gs (List.ofFn x)).getD o1 false = f x := by
    intro x
    rw [hgs, wiresFrom_norm]
    exact (hEv x).1
  have hevgG : ∀ (x : Fin n → Bool) (j : Fin k),
      (wiresFrom gs (List.ofFn x)).getD (o j) false = G j x := by
    intro x j
    rw [hgs, wiresFrom_norm]
    exact (hEv x).2 j
  have ho1_ne : o1 ≠ v.val := by
    intro e
    obtain ⟨x, hx⟩ := hdepw
    apply hx
    rw [← hevg1, ← hevg1, e, getD_wiresFrom _ _ _ (by simp), getD_wiresFrom _ _ _ (by simp)]
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn,
      List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn,
      Function.update_of_ne hvw.symm]
  have hread : ∃ g ∈ gs, v.val ∈ g.inputs := by
    by_contra hno
    push Not at hno
    have hns := supp_noread_at v (fun j => j = v.val) gs (inputSupps n)
      (fun g hg a ha e => hno g hg (e ▸ ha))
      (fun j hj => inputSupps_noread_at v j hj) o1 ho1_ne
    exact hns (dep_mem_supp gs o1 f v hevg1 hdepv)
  set acc := elim n gs (initStatsAt n v false, []) with hacc
  have hlt : acc.2.length + 1 ≤ s := by
    have h1 := elim_len_lt n v.val gs (initStatsAt n v false, []) hnok
      (by rw [initStatsAt_len]; exact v.isLt) ⟨false, initStatsAt_at n v false⟩ hread
    rw [← hacc] at h1
    simp only [List.length_nil, zero_add] at h1
    omega
  have hinv : ∀ x : Fin n → Bool,
      Inv n (List.ofFn x) (wiresFrom gs (List.ofFn (Function.update x v false))) acc := by
    intro x
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_initAt n v false x)
  let o' : Fin k → ℕ := fun j => statWire (acc.1.getD (o j) (Stat.const false))
  refine ⟨acc.2.length, hlt, ⟨acc.2, 0⟩, elim_ok n gs _ (by simp), le_refl _, o', ?_⟩
  intro x j
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD (o j) (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y)) = G j y := by
    intro y
    rw [((hinv y).2 (o j)).2, hevgG, not_depG_update G v hnoG j y false]
  have hst := stat_eq_wire_of_nc _ acc.2 (G j) hval (hGnc j)
  have hx := hval x
  rw [hst] at hx
  exact hx

theorem multi_elim_one (n k s : ℕ) (f : (Fin n → Bool) → Bool)
    (G : Fin k → (Fin n → Bool) → Bool) (v : Fin n) (b : Bool)
    (hdep : ∃ x : Fin n → Bool, f (Function.update x v (!x v)) ≠ f x)
    (hnc1 : ∃ x y : Fin n → Bool, f (Function.update x v b) ≠ f (Function.update y v b))
    (hGnc : ∀ j : Fin k, ∃ y y' : Fin n → Bool, G j y ≠ G j y')
    (hnoG : ¬ DepG G v)
    (hMC : MultiCirc n k s f G) :
    ∃ s' : ℕ, s' + 1 ≤ s ∧ MultiCirc n k s' (fun x => f (Function.update x v b)) G := by
  obtain ⟨C, hFit, hSize, o1, o, hEv⟩ := hMC
  have hSize' : C.gates.length ≤ s := hSize
  set gs := C.gates.map normGate with hgs
  have hlen_gs : gs.length = C.gates.length := by simp [hgs]
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hFit g0 hg0)
  have hevg1 : ∀ x : Fin n → Bool, (wiresFrom gs (List.ofFn x)).getD o1 false = f x := by
    intro x
    rw [hgs, wiresFrom_norm]
    exact (hEv x).1
  have hevgG : ∀ (x : Fin n → Bool) (j : Fin k),
      (wiresFrom gs (List.ofFn x)).getD (o j) false = G j x := by
    intro x j
    rw [hgs, wiresFrom_norm]
    exact (hEv x).2 j
  set acc := elim n gs (initStatsAt n v b, []) with hacc
  have hinv : ∀ x : Fin n → Bool,
      Inv n (List.ofFn x) (wiresFrom gs (List.ofFn (Function.update x v b))) acc := by
    intro x
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_initAt n v b x)
  have hval1 : ∀ x : Fin n → Bool,
      (acc.1.getD o1 (Stat.const false)).val (wiresFrom acc.2 (List.ofFn x)) =
        f (Function.update x v b) := by
    intro x
    rw [((hinv x).2 o1).2, hevg1]
  have hst1 := stat_eq_wire_of_nc _ acc.2 (fun x => f (Function.update x v b)) hval1 hnc1
  have ho1_ne : o1 ≠ v.val := by
    intro e
    have h1 : acc.1.getD o1 (Stat.const false) = Stat.const b := by
      rw [e, hacc, elim_getD n v.val _ gs _ (by rw [initStatsAt_len]; exact v.isLt)]
      exact initStatsAt_at n v b
    rw [h1] at hst1
    cases hst1
  have hread : ∃ g ∈ gs, v.val ∈ g.inputs := by
    by_contra hno
    push Not at hno
    have hns := supp_noread_at v (fun j => j = v.val) gs (inputSupps n)
      (fun g hg a ha e => hno g hg (e ▸ ha))
      (fun j hj => inputSupps_noread_at v j hj) o1 ho1_ne
    exact hns (dep_mem_supp gs o1 f v hevg1 hdep)
  have hlt : acc.2.length + 1 ≤ s := by
    have h1 := elim_len_lt n v.val gs (initStatsAt n v b, []) hnok
      (by rw [initStatsAt_len]; exact v.isLt) ⟨b, initStatsAt_at n v b⟩ hread
    rw [← hacc] at h1
    simp only [List.length_nil, zero_add] at h1
    omega
  let o1' := statWire (acc.1.getD o1 (Stat.const false))
  let o' : Fin k → ℕ := fun j => statWire (acc.1.getD (o j) (Stat.const false))
  refine ⟨acc.2.length, hlt, ⟨acc.2, o1'⟩, elim_ok n gs _ (by simp), le_refl _, o1', o', ?_⟩
  intro x
  constructor
  · have hx := hval1 x
    rw [hst1] at hx
    exact hx
  · intro j
    have hval : ∀ y : Fin n → Bool,
        (acc.1.getD (o j) (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y)) = G j y := by
      intro y
      rw [((hinv y).2 (o j)).2, hevgG, not_depG_update G v hnoG j y b]
    have hst := stat_eq_wire_of_nc _ acc.2 (G j) hval (hGnc j)
    have hx := hval x
    rw [hst] at hx
    exact hx

theorem two_saved_at (n : ℕ) (v : Fin n) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (o : ℕ)
    (hdep : v ∈ (suppsFrom gs (inputSupps n)).getD o ∅)
    (hout : ∀ b c, (elim n gs (initStatsAt n v b, [])).1.getD o (Stat.const false) ≠ Stat.const c) :
    ∃ b, (elim n gs (initStatsAt n v b, [])).2.length + 2 ≤ gs.length := by
  have hon : o ≠ v.val := by
    intro e
    apply hout false false
    rw [e, elim_getD n v.val _ gs _ (by rw [initStatsAt_len]; exact v.isLt)]
    exact initStatsAt_at n v false
  by_cases hread : ∃ g ∈ gs, v.val ∈ g.inputs
  swap
  · exfalso
    push Not at hread
    exact supp_noread_at v (fun j => j = v.val) gs (inputSupps n)
      (fun g hg a ha e => hread g hg (e ▸ ha))
      (fun j hj => inputSupps_noread_at v j hj) o hon hdep
  obtain ⟨g, hg, hng⟩ := hread
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hg
  have hgn : NOk g := hnok g hg
  have hpren : ∀ g' ∈ pre, NOk g' := fun g' h => hnok g' (List.mem_append_left _ h)
  have hpostn : ∀ g' ∈ post, NOk g' :=
    fun g' h => hnok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have hsplit : ∀ b, elim n (pre ++ g :: post) (initStatsAt n v b, [])
      = elim n post (elimStep n (elim n pre (initStatsAt n v b, [])) g) :=
    fun b => by rw [elim_append, elim_cons]
  have hAn : ∀ b, (elim n pre (initStatsAt n v b, [])).1.getD v.val (Stat.const false) =
      Stat.const b := by
    intro b
    rw [elim_getD n v.val _ pre _ (by rw [initStatsAt_len]; exact v.isLt)]
    exact initStatsAt_at n v b
  have hAl : ∀ b, (elim n pre (initStatsAt n v b, [])).1.length = n + pre.length := by
    intro b
    rw [elim_fst_len, initStatsAt_len]
  have hA2 : ∀ b, (elim n pre (initStatsAt n v b, [])).2.length ≤ 0 + pre.length :=
    fun b => elim_len n pre (initStatsAt n v b, [])
  have hB2 := fun b => elimStep_none n (elim n pre (initStatsAt n v b, [])) g hgn v.val hng b (hAn b)
  have hBl : ∀ b, (elimStep n (elim n pre (initStatsAt n v b, [])) g).1.length
      = n + pre.length + 1 := by
    intro b
    simp [elimStep, hAl b]
  have hBn : ∀ b, (elimStep n (elim n pre (initStatsAt n v b, [])) g).1.getD v.val (Stat.const false)
      = Stat.const b := by
    intro b
    show ((elim n pre (initStatsAt n v b, [])).1 ++ [_]).getD v.val _ = _
    rw [getD_snoc_ne _ _ _ _ (by rw [hAl b]; have := v.isLt; omega)]
    exact hAn b
  have hF := fun b => elim_len n post (elimStep n (elim n pre (initStatsAt n v b, [])) g)
  have hlen : (pre ++ g :: post).length = pre.length + post.length + 1 := by
    simp only [List.length_append, List.length_cons]; omega
  by_cases h1 : ∃ g' ∈ pre, v.val ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 : (elim n pre (initStatsAt n v false, [])).2.length + 1 ≤ 0 + pre.length :=
      elim_len_lt n v.val pre (initStatsAt n v false, []) hpren
        (by rw [initStatsAt_len]; exact v.isLt) ⟨false, initStatsAt_at n v false⟩ h1
    have := hF false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  by_cases h2 : ∃ g' ∈ post, v.val ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 := elim_len_lt n v.val post (elimStep n (elim n pre (initStatsAt n v false, [])) g) hpostn
      (by rw [hBl]; have := v.isLt; omega) ⟨false, hBn false⟩ h2
    have := hA2 false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  obtain ⟨c, hc⟩ := elimStep_const n (elim n pre (initStatsAt n v (fixBit g), [])) g hgn v.val hng
    (hAn (fixBit g))
  rw [hAl (fixBit g)] at hc
  refine ⟨fixBit g, ?_⟩
  by_cases h3 : ∃ g' ∈ post, (n + pre.length) ∈ g'.inputs
  · have a1 := elim_len_lt n (n + pre.length) post
      (elimStep n (elim n pre (initStatsAt n v (fixBit g), [])) g) hpostn
      (by rw [hBl]; omega) ⟨c, hc⟩ h3
    have := hA2 (fixBit g)
    have := hB2 (fixBit g)
    rw [hsplit, hlen]
    omega
  · exfalso
    have hom : o ≠ n + pre.length := by
      intro e
      apply hout (fixBit g) c
      rw [hsplit, e, elim_getD n _ _ post _ (by rw [hBl]; omega)]
      exact hc
    push Not at h1 h2 h3
    have hs : suppsFrom (pre ++ g :: post) (inputSupps n)
        = suppsFrom post (suppsFrom pre (inputSupps n)
          ++ [gateSupp (suppsFrom pre (inputSupps n)) g]) := by
      rw [suppsFrom_append]; rfl
    rw [hs] at hdep
    have hL := supp_noread_at v (fun j => j = v.val) pre (inputSupps n)
      (fun g' hg' a ha e => h1 g' hg' (e ▸ ha))
      (fun j hj => inputSupps_noread_at v j hj)
    have hLl : (suppsFrom pre (inputSupps n)).length = n + pre.length := by
      rw [length_suppsFrom]
      simp [inputSupps]
    refine supp_noread_at v (fun j => j = v.val ∨ j = n + pre.length) post _ ?_ ?_ o
      (by simp [hon, hom]) hdep
    · intro g' hg' a ha hD
      rcases hD with rfl | rfl
      · exact h2 g' hg' ha
      · exact h3 g' hg' ha
    · intro j hj
      have hj' : j ≠ v.val ∧ j ≠ n + pre.length := by
        constructor
        · exact fun e => hj (Or.inl e)
        · exact fun e => hj (Or.inr e)
      rw [getD_snoc_ne _ _ _ _ (by rw [hLl]; exact hj'.2)]
      exact hL j hj'.1

theorem multi_elim_two (n k s : ℕ) (f : (Fin n → Bool) → Bool)
    (G : Fin k → (Fin n → Bool) → Bool) (v : Fin n)
    (hdep : ∃ x : Fin n → Bool, f (Function.update x v (!x v)) ≠ f x)
    (hnc1 : ∀ b : Bool, ∃ x y : Fin n → Bool,
      f (Function.update x v b) ≠ f (Function.update y v b))
    (hGnc : ∀ j : Fin k, ∃ y y' : Fin n → Bool, G j y ≠ G j y')
    (hnoG : ¬ DepG G v)
    (hMC : MultiCirc n k s f G) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      MultiCirc n k s' (fun x => f (Function.update x v b)) G := by
  obtain ⟨C, hFit, hSize, o1, o, hEv⟩ := hMC
  have hSize' : C.gates.length ≤ s := hSize
  set gs := C.gates.map normGate with hgs
  have hlen_gs : gs.length = C.gates.length := by simp [hgs]
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hFit g0 hg0)
  have hevg1 : ∀ x : Fin n → Bool, (wiresFrom gs (List.ofFn x)).getD o1 false = f x := by
    intro x
    rw [hgs, wiresFrom_norm]
    exact (hEv x).1
  have hevgG : ∀ (x : Fin n → Bool) (j : Fin k),
      (wiresFrom gs (List.ofFn x)).getD (o j) false = G j x := by
    intro x j
    rw [hgs, wiresFrom_norm]
    exact (hEv x).2 j
  have hinv : ∀ (b : Bool) (x : Fin n → Bool),
      Inv n (List.ofFn x) (wiresFrom gs (List.ofFn (Function.update x v b)))
        (elim n gs (initStatsAt n v b, [])) := by
    intro b x
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_initAt n v b x)
  have hval1 : ∀ (b : Bool) (x : Fin n → Bool),
      ((elim n gs (initStatsAt n v b, [])).1.getD o1 (Stat.const false)).val
        (wiresFrom (elim n gs (initStatsAt n v b, [])).2 (List.ofFn x)) =
          f (Function.update x v b) := by
    intro b x
    rw [((hinv b x).2 o1).2, hevg1]
  have hout : ∀ b c,
      (elim n gs (initStatsAt n v b, [])).1.getD o1 (Stat.const false) ≠ Stat.const c := by
    intro b c hst
    obtain ⟨x, y, hne⟩ := hnc1 b
    apply hne
    rw [← hval1 b x, ← hval1 b y, hst]
    rfl
  have hsupp : v ∈ (suppsFrom gs (inputSupps n)).getD o1 ∅ :=
    dep_mem_supp gs o1 f v hevg1 hdep
  obtain ⟨b, hb⟩ := two_saved_at n v gs hnok o1 hsupp hout
  set acc := elim n gs (initStatsAt n v b, []) with hacc
  have hst1 := stat_eq_wire_of_nc _ acc.2 (fun x => f (Function.update x v b)) (hval1 b) (hnc1 b)
  let o1' := statWire (acc.1.getD o1 (Stat.const false))
  let o' : Fin k → ℕ := fun j => statWire (acc.1.getD (o j) (Stat.const false))
  refine ⟨b, acc.2.length, by omega, ⟨acc.2, o1'⟩, elim_ok n gs _ (by simp), le_refl _, o1', o', ?_⟩
  intro x
  constructor
  · have hx := hval1 b x
    rw [← hacc, hst1] at hx
    exact hx
  · intro j
    have hval : ∀ y : Fin n → Bool,
        (acc.1.getD (o j) (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y)) = G j y := by
      intro y
      rw [((hinv b y).2 (o j)).2, hevgG, not_depG_update G v hnoG j y b]
    have hst := stat_eq_wire_of_nc _ acc.2 (G j) hval (hGnc j)
    have hx := hval x
    rw [hst] at hx
    exact hx

theorem exists_longest_path {V : Type*} [Fintype V] (G : SimpleGraph V) [Nonempty V] :
    ∃ (a b : V) (P : G.Walk a b), P.IsPath ∧
      ∀ (c d : V) (Q : G.Walk c d), Q.IsPath → Q.length ≤ P.length := by
  by_contra hno
  push Not at hno
  have hk : ∀ k : ℕ, ∃ (a b : V) (P : G.Walk a b), P.IsPath ∧ k ≤ P.length := by
    intro k
    induction k with
    | zero =>
      obtain ⟨v⟩ := ‹Nonempty V›
      exact ⟨v, v, Walk.nil, Walk.IsPath.nil, le_refl _⟩
    | succ k ih =>
      obtain ⟨a, b, P, hP, hk⟩ := ih
      obtain ⟨c, d, Q, hQ, hlt⟩ := hno a b P hP
      exact ⟨c, d, Q, hQ, by omega⟩
  obtain ⟨a, b, P, hP, hle⟩ := hk (Fintype.card V)
  have := hP.length_lt
  omega

theorem good_leaf_of_longest_path {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.IsAcyclic)
    {a b : V} (P : G.Walk a b) (hP : P.IsPath) (h1 : 1 ≤ P.length)
    (hmax : ∀ (c d : V) (Q : G.Walk c d), Q.IsPath → Q.length ≤ P.length) :
    ∃ p : V, G.Adj a p ∧ (∀ w, G.Adj a w → w = p) ∧
      ((∃ q : V, ∀ w, G.Adj p w → w = a ∨ w = q) ∨
        (∃ l' : V, l' ≠ a ∧ G.Adj p l' ∧ ∀ w, G.Adj l' w → w = p)) := by
  classical
  cases P with
  | nil => simp at h1
  | @cons _ p _ hlp P' =>
    rw [Walk.cons_isPath_iff] at hP
    obtain ⟨hP', hlP'⟩ := hP
    have hmax' : ∀ (c d : V) (Q : G.Walk c d), Q.IsPath → Q.length ≤ P'.length + 1 := by
      intro c d Q hQ
      have := hmax c d Q hQ
      simpa using this
    have hPfull : (Walk.cons hlp P').IsPath := (Walk.cons_isPath_iff _ _).2 ⟨hP', hlP'⟩
    have hleaf : ∀ w, G.Adj a w → w = p := by
      intro w hw
      by_cases hm : w ∈ (Walk.cons hlp P').support
      · have := hG.eq_snd_of_adj_start hPfull hw hm
        simpa using this
      · exfalso
        have hQ : (Walk.cons hw.symm (Walk.cons hlp P')).IsPath :=
          (Walk.cons_isPath_iff _ _).2 ⟨hPfull, hm⟩
        have := hmax' _ _ _ hQ
        simp at this
    refine ⟨p, hlp, hleaf, ?_⟩
    have hoff : ∀ w, G.Adj p w → w ∉ (Walk.cons hlp P').support →
        ∀ u, G.Adj w u → u = p := by
      intro w hw hwm u hu
      have hwP' : w ∉ P'.support := by
        intro h; exact hwm (by simp [h])
      have hQ : (Walk.cons hw.symm P').IsPath := (Walk.cons_isPath_iff _ _).2 ⟨hP', hwP'⟩
      by_cases hm : u ∈ (Walk.cons hw.symm P').support
      · have := hG.eq_snd_of_adj_start hQ hu hm
        simpa using this
      · exfalso
        have hQ2 : (Walk.cons hu.symm (Walk.cons hw.symm P')).IsPath :=
          (Walk.cons_isPath_iff _ _).2 ⟨hQ, hm⟩
        have := hmax' _ _ _ hQ2
        simp at this
    by_cases hex : ∃ l' : V, l' ≠ a ∧ G.Adj p l' ∧ ∀ w, G.Adj l' w → w = p
    · exact Or.inr hex
    · left
      refine ⟨P'.snd, fun w hw => ?_⟩
      by_cases hwl : w = a
      · exact Or.inl hwl
      · right
        by_cases hm : w ∈ P'.support
        · exact hG.eq_snd_of_adj_start hP' hw hm
        · exfalso
          apply hex
          refine ⟨w, hwl, hw, hoff w hw ?_⟩
          simp [hwl, hm]

theorem forest_two_good_leaves {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.IsAcyclic)
    (he : ∃ u v : V, G.Adj u v) :
    ∃ a b : V, a ≠ b ∧
      (∃ p : V, G.Adj a p ∧ (∀ w, G.Adj a w → w = p) ∧
        ((∃ q : V, ∀ w, G.Adj p w → w = a ∨ w = q) ∨
          (∃ l' : V, l' ≠ a ∧ G.Adj p l' ∧ ∀ w, G.Adj l' w → w = p))) ∧
      (∃ p : V, G.Adj b p ∧ (∀ w, G.Adj b w → w = p) ∧
        ((∃ q : V, ∀ w, G.Adj p w → w = b ∨ w = q) ∨
          (∃ l' : V, l' ≠ b ∧ G.Adj p l' ∧ ∀ w, G.Adj l' w → w = p))) := by
  obtain ⟨u0, v0, h0⟩ := he
  have : Nonempty V := ⟨u0⟩
  obtain ⟨a, b, P, hP, hmax⟩ := exists_longest_path G
  have h1 : 1 ≤ P.length := by
    have := hmax u0 v0 (Walk.cons h0 Walk.nil) (by simp [Walk.cons_isPath_iff, h0.ne])
    simpa using this
  have hab : a ≠ b := by
    rintro rfl
    cases P with
    | nil => simp at h1
    | @cons _ p _ hlp P' =>
      rw [Walk.cons_isPath_iff] at hP
      exact hP.2 P'.end_mem_support
  have hmax_rev : ∀ (c d : V) (Q : G.Walk c d), Q.IsPath → Q.length ≤ P.reverse.length := by
    intro c d Q hQ
    rw [Walk.length_reverse]
    exact hmax c d Q hQ
  have h1_rev : 1 ≤ P.reverse.length := by
    rw [Walk.length_reverse]
    exact h1
  exact ⟨a, b, hab,
    good_leaf_of_longest_path G hG P hP h1 hmax,
    good_leaf_of_longest_path G hG P.reverse hP.reverse h1_rev hmax_rev⟩

theorem ncard_del1 {n : ℕ} (K : SimpleGraph (Fin n)) (l p : Fin n) (h : K.Adj l p) :
    (K.deleteEdges {s(l, p)}).edgeSet.ncard + 1 = K.edgeSet.ncard := by
  rw [edgeSet_deleteEdges]
  exact Set.ncard_sdiff_singleton_add_one (K.mem_edgeSet.2 h)

theorem ncard_del2 {n : ℕ} (K : SimpleGraph (Fin n)) (l p q : Fin n) (h : K.Adj l p) :
    K.edgeSet.ncard ≤ (K.deleteEdges {s(p, l), s(p, q)}).edgeSet.ncard + 2 ∧
      (K.deleteEdges {s(p, l), s(p, q)}).edgeSet.ncard < K.edgeSet.ncard := by
  rw [edgeSet_deleteEdges]
  constructor
  · have h1 := Set.ncard_le_ncard_sdiff_add_ncard K.edgeSet ({s(p, l), s(p, q)} : Set (Sym2 (Fin n)))
    have h2 := Set.ncard_insert_le (s(p, l)) ({s(p, q)} : Set (Sym2 (Fin n)))
    rw [Set.ncard_singleton] at h2
    omega
  · have hmem : s(l, p) ∈ K.edgeSet := K.mem_edgeSet.2 h
    have hsub : K.edgeSet \ {s(p, l), s(p, q)} ⊆ K.edgeSet \ {s(l, p)} := by
      intro e he
      refine ⟨he.1, ?_⟩
      intro he'
      apply he.2
      rw [Set.mem_singleton_iff] at he'
      rw [he', Sym2.eq_swap]
      exact Set.mem_insert _ _
    have h1 := Set.ncard_le_ncard hsub
    have h2 := Set.ncard_sdiff_singleton_lt_of_mem hmem
    omega

theorem noedge_ncard {n : ℕ} (K : SimpleGraph (Fin n)) (h : ∀ i j, ¬ K.Adj i j) :
    K.edgeSet.ncard = 0 := by
  have : K.edgeSet = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro e
    induction e using Sym2.ind with
    | _ i j => exact fun he => h i j (K.mem_edgeSet.1 he)
  rw [this, Set.ncard_empty]

theorem cov_insert {n : ℕ} (K : SimpleGraph (Fin n)) (S : Set (Sym2 (Fin n))) (p : Fin n)
    (hS : ∀ e ∈ S, p ∈ e) (T : Finset (Fin n)) (hT : Cov (K.deleteEdges S) T) :
    Cov K (insert p T) := by
  intro i j hij
  by_cases he : s(i, j) ∈ S
  · have := hS _ he
    rcases Sym2.mem_iff.1 this with rfl | rfl
    · exact Or.inl (Finset.mem_insert_self _ _)
    · exact Or.inr (Finset.mem_insert_self _ _)
  · rcases hT i j ((deleteEdges_adj).2 ⟨hij, he⟩) with h | h
    · exact Or.inl (Finset.mem_insert_of_mem h)
    · exact Or.inr (Finset.mem_insert_of_mem h)

theorem cov_swap_exists {n : ℕ} (K : SimpleGraph (Fin n)) (l p l' : Fin n)
    (hll' : l' ≠ l) (hl'p : K.Adj p l') (hleaf' : ∀ w, K.Adj l' w → w = p)
    (T0 : Finset (Fin n)) (hT0 : Cov (K.deleteEdges {s(l, p)}) T0) :
    ∃ T : Finset (Fin n), Cov K T ∧ T.card ≤ T0.card := by
  have hS : ∀ e ∈ ({s(l, p)} : Set (Sym2 (Fin n))), p ∈ e := by
    intro e he
    rw [Set.mem_singleton_iff] at he
    subst he
    exact Sym2.mem_mk_right _ _
  by_cases hpT : p ∈ T0
  · refine ⟨T0, ?_, le_refl _⟩
    have := cov_insert K _ p hS T0 hT0
    rwa [Finset.insert_eq_of_mem hpT] at this
  · have hl'T : l' ∈ T0 := by
      have hpl' : p ≠ l' := hl'p.ne
      rcases hT0 p l' ((deleteEdges_adj).2 ⟨hl'p, by
          simp [hll', hpl'.symm]⟩) with h | h
      · exact absurd h hpT
      · exact h
    refine ⟨insert p (T0.erase l'), ?_, ?_⟩
    · intro i j hij
      by_cases hip : i = p
      · exact Or.inl (hip ▸ Finset.mem_insert_self _ _)
      by_cases hjp : j = p
      · exact Or.inr (hjp ▸ Finset.mem_insert_self _ _)
      have h0 : (K.deleteEdges {s(l, p)}).Adj i j :=
        (deleteEdges_adj).2 ⟨hij, by simp [hip, hjp]⟩
      rcases hT0 i j h0 with h | h
      · have hil' : i ≠ l' := by
          rintro rfl; exact hjp (hleaf' j hij)
        exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hil', h⟩))
      · have hjl' : j ≠ l' := by
          rintro rfl; exact hip (hleaf' i hij.symm)
        exact Or.inr (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hjl', h⟩))
    · have h2 := Finset.card_insert_le p (T0.erase l')
      have h3 := Finset.card_erase_add_one hl'T
      omega

theorem del_p_adj {n : ℕ} (K : SimpleGraph (Fin n)) (l p q : Fin n)
    (hp : ∀ w, K.Adj p w → w = l ∨ w = q) (i j : Fin n)
    (hij : (K.deleteEdges {s(p, l), s(p, q)}).Adj i j) : i ≠ p := by
  rw [deleteEdges_adj] at hij
  obtain ⟨hij, hne⟩ := hij
  rintro rfl
  rcases hp j hij with rfl | rfl
  · exact hne (by simp)
  · exact hne (by simp)

theorem lower_bound_no_edges (n k : ℕ) (K : SimpleGraph (Fin n))
    (G : Fin k → (Fin n → Bool) → Bool)
    (hnoE : ∀ u v : Fin n, ¬ K.Adj u v)
    (hGnc : ∀ j : Fin k, ∃ y y' : Fin n → Bool, G j y ≠ G j y') :
    ∀ (c : ℕ) (A : Finset (Fin n)) (s : ℕ),
      A.card = c → A.Nonempty →
      (∀ i i' : Fin n, i ∈ A → i' ∈ A → DepG G i → DepG G i' → i = i') →
      MultiCirc n k s (F K A) G →
      ∃ (T : Finset (Fin n)) (t : ℕ),
        Cov K T ∧ A.card + K.edgeSet.ncard + T.card + t ≤ s + 1 ∧ CircG n k t G := by
  intro c
  induction c with
  | zero =>
    intro A _ hc hne _ _
    have := Finset.card_pos.2 hne
    omega
  | succ c ih =>
    intro A s hc hne hShare hMC
    have hE0 : K.edgeSet.ncard = 0 := noedge_ncard K hnoE
    cases c with
    | zero =>
      obtain ⟨C, hFit, hSize, o1, o, hEv⟩ := hMC
      refine ⟨∅, s, fun u v h => absurd h (hnoE u v), ?_,
        C, hFit, hSize, o, fun x j => (hEv x).2 j⟩
      rw [hc, hE0, Finset.card_empty]
      omega
    | succ c' =>
      have h2 : 1 < A.card := by omega
      obtain ⟨a1, ha1, a2, ha2, hne12⟩ := Finset.one_lt_card.1 h2
      have hex : ∃ a ∈ A, ¬ DepG G a := by
        by_cases h1 : DepG G a1
        · refine ⟨a2, ha2, fun h2 => hne12 (hShare a1 a2 ha1 ha2 h1 h2)⟩
        · exact ⟨a1, ha1, h1⟩
      obtain ⟨a, haA, hnoG⟩ := hex
      set A' := A.erase a with hA'
      have hA'card : A'.card = c' + 1 := by
        have := Finset.card_erase_of_mem haA
        rw [← hA'] at this
        omega
      have hA'ne : A'.Nonempty := Finset.card_pos.1 (by omega)
      have hdepa := F_dep_A K A a haA
      have hrf : (fun x => F K A (Function.update x a false)) = F K A' :=
        funext (restrict_false_A K A a hnoE)
      have hnc1 : ∃ x y : Fin n → Bool,
          F K A (Function.update x a false) ≠ F K A (Function.update y a false) := by
        obtain ⟨x, y, hxy⟩ := F_nc K A' (Or.inl hA'ne)
        refine ⟨x, y, ?_⟩
        rw [congrFun hrf x, congrFun hrf y]
        exact hxy
      obtain ⟨s', hs', hMC'⟩ := multi_elim_one n k s (F K A) G a false hdepa hnc1 hGnc hnoG hMC
      rw [hrf] at hMC'
      have hShare' : ∀ i i' : Fin n, i ∈ A' → i' ∈ A' → DepG G i → DepG G i' → i = i' := by
        intro i i' hi hi'
        exact hShare i i' (Finset.mem_of_mem_erase hi) (Finset.mem_of_mem_erase hi')
      obtain ⟨T, t, hCov, hBd, hCG⟩ := ih A' s' hA'card hA'ne hShare' hMC'
      refine ⟨T, t, hCov, ?_, hCG⟩
      omega

theorem lower_bound_aux (n k : ℕ) (G : Fin k → (Fin n → Bool) → Bool)
    (hGnc : ∀ j : Fin k, ∃ y y' : Fin n → Bool, G j y ≠ G j y') :
    ∀ (m : ℕ) (K : SimpleGraph (Fin n)) (A : Finset (Fin n)) (s : ℕ),
      K.edgeSet.ncard = m →
      K.IsAcyclic →
      (∀ a ∈ A, ∀ w : Fin n, ¬ K.Adj a w) →
      (A.Nonempty ∨ ∃ u v : Fin n, K.Adj u v) →
      (∀ i i' : Fin n, (i ∈ A ∨ ∃ w, K.Adj i w) → (i' ∈ A ∨ ∃ w, K.Adj i' w) →
        DepG G i → DepG G i' → i = i') →
      MultiCirc n k s (F K A) G →
      ∃ (T : Finset (Fin n)) (t : ℕ),
        Cov K T ∧ A.card + m + T.card + t ≤ s + 1 ∧ CircG n k t G := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro K A s hm hAcyc hDisj hNonempty hShare hMC
    by_cases hE : ∃ u v : Fin n, K.Adj u v
    swap
    · push Not at hE
      have hm0 : m = 0 := by rw [← hm]; exact noedge_ncard K hE
      have hAne : A.Nonempty := by
        rcases hNonempty with h | ⟨u, v, huv⟩
        · exact h
        · exact absurd huv (hE u v)
      have hShareA : ∀ i i' : Fin n, i ∈ A → i' ∈ A → DepG G i → DepG G i' → i = i' := by
        intro i i' hi hi'
        exact hShare i i' (Or.inl hi) (Or.inl hi')
      obtain ⟨T, t, hCov, hBd, hCG⟩ :=
        lower_bound_no_edges n k K G hE hGnc A.card A s rfl hAne hShareA hMC
      refine ⟨T, t, hCov, ?_, hCG⟩
      rw [hm] at hBd
      exact hBd
    obtain ⟨a, b, hab, ⟨pa, hapa, hleafa, hcasea⟩, ⟨pb, hbpb, hleafb, hcaseb⟩⟩ :=
      forest_two_good_leaves K hAcyc hE
    have hgood : ∃ l p : Fin n, ¬ DepG G l ∧ K.Adj l p ∧ (∀ w, K.Adj l w → w = p) ∧
        ((∃ q : Fin n, ∀ w, K.Adj p w → w = l ∨ w = q) ∨
          (∃ l' : Fin n, l' ≠ l ∧ K.Adj p l' ∧ ∀ w, K.Adj l' w → w = p)) := by
      by_cases ha : DepG G a
      · refine ⟨b, pb, fun hb => hab (hShare a b (Or.inr ⟨pa, hapa⟩) (Or.inr ⟨pb, hbpb⟩) ha hb),
          hbpb, hleafb, hcaseb⟩
      · exact ⟨a, pa, ha, hapa, hleafa, hcasea⟩
    obtain ⟨l, p, hnoGl, hlp, hleaf, hcase⟩ := hgood
    have hlA : l ∉ A := fun h => hDisj l h p hlp
    have hpA : p ∉ A := fun h => hDisj p h l hlp.symm
    have hdepl := F_dep_edge K A l p hlp hpA
    have hdepp := F_dep_edge K A p l hlp.symm hlA
    set K0 := K.deleteEdges {s(l, p)} with hK0
    have hm0 : K0.edgeSet.ncard + 1 = m := by rw [← hm]; exact ncard_del1 K l p hlp
    have hac0 : K0.IsAcyclic := hAcyc.anti (deleteEdges_le _)
    have hDisj0 : ∀ a ∈ A, ∀ w : Fin n, ¬ K0.Adj a w := fun a ha w hw =>
      hDisj a ha w (deleteEdges_adj.1 hw).1
    have hShare0 : ∀ i i' : Fin n, (i ∈ A ∨ ∃ w, K0.Adj i w) → (i' ∈ A ∨ ∃ w, K0.Adj i' w) →
        DepG G i → DepG G i' → i = i' := by
      intro i i' hi hi'
      apply hShare i i'
      · rcases hi with h | ⟨w, hw⟩
        · exact Or.inl h
        · exact Or.inr ⟨w, (deleteEdges_adj.1 hw).1⟩
      · rcases hi' with h | ⟨w, hw⟩
        · exact Or.inl h
        · exact Or.inr ⟨w, (deleteEdges_adj.1 hw).1⟩
    have hS0 : ∀ e ∈ ({s(l, p)} : Set (Sym2 (Fin n))), p ∈ e := by
      intro e he
      rw [Set.mem_singleton_iff] at he
      subst he
      exact Sym2.mem_mk_right _ _
    have hrf : (fun x => F K A (Function.update x l false)) = F K0 A :=
      funext (restrict_false_edge K A l p hlA hleaf)
    rcases hcase with ⟨q, hq⟩ | ⟨l', hl'l, hpl', hleaf'⟩
    · set K1 := K.deleteEdges {s(p, l), s(p, q)} with hK1
      by_cases h0 : A.Nonempty ∨ ∃ u v : Fin n, K0.Adj u v
      · have hrt : (fun x => F K A (Function.update x l true)) = F K1 (insert p A) :=
          funext (restrict_true_leaf K A l p q hlA hlp hleaf hq)
        have hnc : ∀ b : Bool, ∃ x y : Fin n → Bool,
            F K A (Function.update x l b) ≠ F K A (Function.update y l b) := by
          intro b
          cases b
          · obtain ⟨x, y, hxy⟩ := F_nc K0 A h0
            refine ⟨x, y, ?_⟩
            rw [congrFun hrf x, congrFun hrf y]
            exact hxy
          · obtain ⟨x, y, hxy⟩ := F_nc K1 (insert p A) (Or.inl (Finset.insert_nonempty _ _))
            refine ⟨x, y, ?_⟩
            rw [congrFun hrt x, congrFun hrt y]
            exact hxy
        obtain ⟨b, s', hs', hMC'⟩ := multi_elim_two n k s (F K A) G l hdepl hnc hGnc hnoGl hMC
        cases b
        · rw [hrf] at hMC'
          obtain ⟨T0, t0, hCov0, hBd0, hCG0⟩ :=
            ih K0.edgeSet.ncard (by omega) K0 A s' rfl hac0 hDisj0 h0 hShare0 hMC'
          refine ⟨insert p T0, t0, cov_insert K _ p hS0 T0 hCov0, ?_, hCG0⟩
          have := Finset.card_insert_le p T0
          omega
        · rw [hrt] at hMC'
          have hS1 : ∀ e ∈ ({s(p, l), s(p, q)} : Set (Sym2 (Fin n))), p ∈ e := by
            intro e he
            rcases he with rfl | he
            · exact Sym2.mem_mk_left _ _
            · rw [Set.mem_singleton_iff] at he
              subst he
              exact Sym2.mem_mk_left _ _
          have hac1 : K1.IsAcyclic := hAcyc.anti (deleteEdges_le _)
          have hDisj1 : ∀ a ∈ insert p A, ∀ w : Fin n, ¬ K1.Adj a w := by
            intro a ha w hw
            rcases Finset.mem_insert.1 ha with hap | haA
            · exact del_p_adj K l p q hq a w hw hap
            · exact hDisj a haA w (deleteEdges_adj.1 hw).1
          have hShare1 : ∀ i i' : Fin n,
              (i ∈ insert p A ∨ ∃ w, K1.Adj i w) →
              (i' ∈ insert p A ∨ ∃ w, K1.Adj i' w) →
              DepG G i → DepG G i' → i = i' := by
            intro i i' hi hi'
            apply hShare i i'
            · rcases hi with h | ⟨w, hw⟩
              · rcases Finset.mem_insert.1 h with rfl | hA
                · exact Or.inr ⟨l, hlp.symm⟩
                · exact Or.inl hA
              · exact Or.inr ⟨w, (deleteEdges_adj.1 hw).1⟩
            · rcases hi' with h | ⟨w, hw⟩
              · rcases Finset.mem_insert.1 h with rfl | hA
                · exact Or.inr ⟨l, hlp.symm⟩
                · exact Or.inl hA
              · exact Or.inr ⟨w, (deleteEdges_adj.1 hw).1⟩
          obtain ⟨hc1, hc2⟩ := ncard_del2 K l p q hlp
          rw [← hK1] at hc1 hc2
          obtain ⟨T1, t1, hCov1, hBd1, hCG1⟩ :=
            ih K1.edgeSet.ncard (by omega) K1 (insert p A) s' rfl hac1 hDisj1
              (Or.inl (Finset.insert_nonempty _ _)) hShare1 hMC'
          rw [Finset.card_insert_of_notMem hpA] at hBd1
          refine ⟨insert p T1, t1, cov_insert K _ p hS1 T1 hCov1, ?_, hCG1⟩
          have := Finset.card_insert_le p T1
          omega
      · push Not at h0
        obtain ⟨hA0, hK00⟩ := h0
        have hm1 : m = 1 := by
          have := noedge_ncard K0 hK00
          omega
        obtain ⟨s', hs', hCG'⟩ :=
          multi_elim_one_drop_o1 n k s (F K A) G l p hlp.ne.symm hdepl hdepp hGnc hnoGl hMC
        have hCovp : Cov K {p} := by
          intro u v huv
          have h1 := hK00 u v
          rw [deleteEdges_adj] at h1
          push Not at h1
          have h2 := h1 huv
          rw [Set.mem_singleton_iff, Sym2.eq_iff] at h2
          rcases h2 with ⟨_, rfl⟩ | ⟨rfl, _⟩
          · exact Or.inr (Finset.mem_singleton_self _)
          · exact Or.inl (Finset.mem_singleton_self _)
        refine ⟨{p}, s', hCovp, ?_, hCG'⟩
        subst hA0
        simp only [Finset.card_empty, Finset.card_singleton]
        omega
    · have hpl'0 : K0.Adj p l' := (deleteEdges_adj).2 ⟨hpl', by
        simp [hl'l, hpl'.ne.symm]⟩
      have hnc0 : ∃ x y : Fin n → Bool,
          F K A (Function.update x l false) ≠ F K A (Function.update y l false) := by
        obtain ⟨x, y, hxy⟩ := F_nc K0 A (Or.inr ⟨p, l', hpl'0⟩)
        refine ⟨x, y, ?_⟩
        rw [congrFun hrf x, congrFun hrf y]
        exact hxy
      obtain ⟨s', hs', hMC'⟩ := multi_elim_one n k s (F K A) G l false hdepl hnc0 hGnc hnoGl hMC
      rw [hrf] at hMC'
      obtain ⟨T0, t0, hCov0, hBd0, hCG0⟩ :=
        ih K0.edgeSet.ncard (by omega) K0 A s' rfl hac0 hDisj0 (Or.inr ⟨p, l', hpl'0⟩) hShare0 hMC'
      obtain ⟨T, hCov, hTcard⟩ := cov_swap_exists K l p l' hl'l hpl' hleaf' T0 hCov0
      refine ⟨T, t0, hCov, ?_, hCG0⟩
      omega

end PEqualNP.Outside.L_meta_659_aux

theorem PEqualNP.Outside.L_meta_659 :
    ∀ (n k s : ℕ) (K : SimpleGraph (Fin n)) (A : Finset (Fin n)) (G : Fin k → (Fin n → Bool) → Bool),
      (∀ (v : Fin n) (c : K.Walk v v), ¬ c.IsCycle) →
      (∀ a ∈ A, ∀ w : Fin n, ¬ K.Adj a w) →
      (A.Nonempty ∨ ∃ u v : Fin n, K.Adj u v) →
      (∀ j : Fin k, ∃ y y' : Fin n → Bool, G j y ≠ G j y') →
      (∀ i i' : Fin n, (i ∈ A ∨ ∃ w, K.Adj i w) → (i' ∈ A ∨ ∃ w, K.Adj i' w) →
        (∃ (j : Fin k) (x : Fin n → Bool), G j (Function.update x i false) ≠ G j (Function.update x i true)) →
        (∃ (j : Fin k) (x : Fin n → Bool), G j (Function.update x i' false) ≠ G j (Function.update x i' true)) →
        i = i') →
      ((∃ C : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ s ∧
          ∃ (o1 : ℕ) (o : Fin k → ℕ),
            ∀ x : Fin n → Bool,
              ((C.wires (List.ofFn x)).getD o1 false = true ↔
                ((∃ a ∈ A, x a = true) ∨ ∃ u v : Fin n, K.Adj u v ∧ x u = true ∧ x v = true)) ∧
              ∀ j : Fin k, (C.wires (List.ofFn x)).getD (o j) false = G j x) ↔
        ∃ (T : Finset (Fin n)) (t : ℕ),
          (∀ u v : Fin n, K.Adj u v → u ∈ T ∨ v ∈ T) ∧
          A.card + K.edgeSet.ncard + T.card + t ≤ s + 1 ∧
          ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
            PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ t ∧
            ∃ o : Fin k → ℕ,
              ∀ (x : Fin n → Bool) (j : Fin k), (C.wires (List.ofFn x)).getD (o j) false = G j x) := by
  intro n k s K A G hAcyc hDisj hNonempty hGnc hShare
  constructor
  · intro h
    have hMC : PEqualNP.Outside.L_meta_659_aux.MultiCirc n k s
        (PEqualNP.Outside.L_meta_659_aux.F K A) G := by
      obtain ⟨C, hFit, hSize, o1, o, hEv⟩ := h
      refine ⟨C, hFit, hSize, o1, o, fun x => ⟨?_, (hEv x).2⟩⟩
      rw [Bool.eq_iff_iff, PEqualNP.Outside.L_meta_659_aux.F_true]
      exact (hEv x).1
    exact PEqualNP.Outside.L_meta_659_aux.lower_bound_aux n k G hGnc K.edgeSet.ncard K A s rfl
      hAcyc hDisj hNonempty hShare hMC
  · rintro ⟨T, t, hCov, hBound, hCG⟩
    obtain ⟨C, hFit, hSize, o1, o, hEv⟩ :=
      PEqualNP.Outside.L_meta_659_aux.upper_bound n k s K A G hNonempty hGnc T t hCov hBound hCG
    refine ⟨C, hFit, hSize, o1, o, fun x => ⟨?_, (hEv x).2⟩⟩
    rw [(hEv x).1, PEqualNP.Outside.L_meta_659_aux.F_true]
