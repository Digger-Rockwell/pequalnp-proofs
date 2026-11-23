import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_282_aux

open PEqualNP.CircuitLowerBounds

def edgeList : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5), (2, 3)]

def adj (i j : Fin 6) : Bool :=
  decide ((i.val, j.val) ∈ edgeList ∨ (j.val, i.val) ∈ edgeList)

def e (i : Fin 6) : Fin 6 → Bool := fun k => decide (k = i)

def pair (i j : Fin 6) : Fin 6 → Bool := fun k => e i k || e j k

def P (f : Fin 6 → Bool) (i j : Fin 6) : Bool := f i || f j

def hom (a : (Fin 6 → Bool) → Bool) : Prop :=
  ∀ x y : Fin 6 → Bool, a (fun i => x i || y i) = (a x || a y)

theorem hom_pair {a : (Fin 6 → Bool) → Bool} (ha : hom a) (i j : Fin 6) :
    a (pair i j) = P (fun k => a (e k)) i j := ha _ _

set_option maxRecDepth 100000 in
theorem edge_iff : ∀ i j : Fin 6,
    ((∃ u v : Fin 6, (u.val, v.val) ∈ edgeList ∧ pair i j u = true ∧ pair i j v = true)
      ↔ adj i j = true) := by decide

theorem adj_self : ∀ i : Fin 6, adj i i = false := by decide
theorem adj_symm : ∀ i j : Fin 6, adj i j = adj j i := by decide

theorem bool_hz : ∀ p r : Bool, false = ((p || p) || r) → p = false := by decide
theorem bool_o1 : ∀ p q : Bool, false = (p || q) → p = false := by decide
theorem bool_o2 : ∀ p q : Bool, false = (p || q) → q = false := by decide
theorem bool_a2 : ∀ p q : Bool, true = (p && q) → q = true := by decide
theorem bool_t1 : ∀ p q r : Bool, true = (p && q && r) → p = true := by decide
theorem bool_t2 : ∀ p q r : Bool, true = (p && q && r) → q = true := by decide
theorem bool_t3 : ∀ p q r : Bool, true = (p && q && r) → r = true := by decide
theorem bool_u0 : ∀ p q m r : Bool,
    false = (((p || q) || m) && (true || r)) → q = false := by decide

theorem five_form1_aux : ∀ a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Bool,
    ((a0 || a0) && (b0 || b0)) = false →
    ((a1 || a1) && (b1 || b1)) = false →
    ((a2 || a2) && (b2 || b2)) = false →
    ((a3 || a3) && (b3 || b3)) = false →
    ((a4 || a4) && (b4 || b4)) = false →
    ((a3 || a0) && (b3 || b0)) = false →
    ((a3 || a1) && (b3 || b1)) = false →
    ((a3 || a2) && (b3 || b2)) = false →
    ((a4 || a1) && (b4 || b1)) = false →
    ((a4 || a2) && (b4 || b2)) = false →
    ((((a3 || a4) && (b3 || b4)) && ((a0 || a1) && (b0 || b1))) ||
     (((a3 || a4) && (b3 || b4)) && ((a0 || a2) && (b0 || b2))) ||
     (((a3 || a4) && (b3 || b4)) && ((a1 || a2) && (b1 || b2))) ||
     (((a0 || a1) && (b0 || b1)) && ((a0 || a2) && (b0 || b2)) && ((a1 || a2) && (b1 || b2)))) = false := by
  decide

theorem five_form1_comb : ∀ p01 p02 p12 p34 q01 q02 q12 q34 : Bool,
    ((p34 && p01) || (p34 && p02) || (p34 && p12) || (p01 && p02 && p12)) = false →
    ((q34 && q01) || (q34 && q02) || (q34 && q12) || (q01 && q02 && q12)) = false →
    true = (p01 || q01) → true = (p02 || q02) → true = (p12 || q12) → true = (p34 || q34) →
    False := by
  decide

theorem five_vc_nonedges : ∀ v0 v1 v2 v3 v4 : Bool,
    (v0 || v1) = true → (v0 || v2) = true → (v1 || v2) = true → (v3 || v4) = true →
    ((((v3 || v0) || (v3 || v1)) && ((v3 || v0) || (v3 || v2)) && ((v3 || v0) || (v4 || v1)) &&
      ((v3 || v1) || (v3 || v2)) && ((v3 || v1) || (v4 || v1)) && ((v3 || v2) || (v4 || v1))) = true) := by
  decide

theorem five_triple_fin : ∀ pa1 pa2 pa3 pa4 pb1 pb2 pb3 pb4 pd1 pd2 pd3 pd4 : Bool,
    (((pa1 || pa2) && (pa1 || pa3) && (pa1 || pa4) && (pa2 || pa3) && (pa2 || pa4) && (pa3 || pa4)) = true) →
    (((pb1 || pb2) && (pb1 || pb3) && (pb1 || pb4) && (pb2 || pb3) && (pb2 || pb4) && (pb3 || pb4)) = true) →
    (((pd1 || pd2) && (pd1 || pd3) && (pd1 || pd4) && (pd2 || pd3) && (pd2 || pd4) && (pd3 || pd4)) = true) →
    (pa1 && pb1 && pd1) = false → (pa2 && pb2 && pd2) = false →
    (pa3 && pb3 && pd3) = false → (pa4 && pb4 && pd4) = false → False := by
  decide

theorem five_2k2_aux : ∀ a1 a2 a3 a4 b1 b2 b3 b4 : Bool,
    ((a3 || a4) && (b3 || b4)) = true →
    ((a1 || a2) && (b1 || b2)) = true →
    ((a3 || a1) && (b3 || b1)) = false →
    ((a3 || a2) && (b3 || b2)) = false →
    ((a4 || a1) && (b4 || b1)) = false →
    ((a4 || a2) && (b4 || b2)) = false →
    ((a1 || a1) && (b1 || b1)) = false →
    ((a2 || a2) && (b2 || b2)) = false →
    ((a4 || a4) && (b4 || b4)) = false →
    False := by
  decide

theorem five_k1 (t0 t1 t2 d0 d1 : Fin 6) (a b c d : Fin 6 → Bool)
    (he01 : adj t0 t1 = true) (he02 : adj t0 t2 = true) (he12 : adj t1 t2 = true) (he34 : adj d0 d1 = true)
    (hn30 : adj d0 t0 = false) (hn31 : adj d0 t1 = false) (hn32 : adj d0 t2 = false)
    (hn41 : adj d1 t1 = false) (hn42 : adj d1 t2 = false)
    (H : ∀ i ∈ [t0, t1, t2, d0, d1], ∀ j ∈ [t0, t1, t2, d0, d1],
      adj i j = ((P a i j && P b i j) || (P c i j && P d i j))) : False := by
  have hP : ∀ i ∈ [t0, t1, t2, d0, d1], ∀ j ∈ [t0, t1, t2, d0, d1],
      adj i j = false → (P a i j && P b i j) = false :=
    fun i hi j hj hij => bool_o1 _ _ (hij.symm.trans (H i hi j hj))
  have hQ : ∀ i ∈ [t0, t1, t2, d0, d1], ∀ j ∈ [t0, t1, t2, d0, d1],
      adj i j = false → (P c i j && P d i j) = false :=
    fun i hi j hj hij => bool_o2 _ _ (hij.symm.trans (H i hi j hj))
  have hp := five_form1_aux (a t0) (a t1) (a t2) (a d0) (a d1) (b t0) (b t1) (b t2) (b d0) (b d1)
    (hP t0 (by simp) t0 (by simp) (adj_self t0))
    (hP t1 (by simp) t1 (by simp) (adj_self t1))
    (hP t2 (by simp) t2 (by simp) (adj_self t2))
    (hP d0 (by simp) d0 (by simp) (adj_self d0))
    (hP d1 (by simp) d1 (by simp) (adj_self d1))
    (hP d0 (by simp) t0 (by simp) hn30)
    (hP d0 (by simp) t1 (by simp) hn31)
    (hP d0 (by simp) t2 (by simp) hn32)
    (hP d1 (by simp) t1 (by simp) hn41)
    (hP d1 (by simp) t2 (by simp) hn42)
  have hq := five_form1_aux (c t0) (c t1) (c t2) (c d0) (c d1) (d t0) (d t1) (d t2) (d d0) (d d1)
    (hQ t0 (by simp) t0 (by simp) (adj_self t0))
    (hQ t1 (by simp) t1 (by simp) (adj_self t1))
    (hQ t2 (by simp) t2 (by simp) (adj_self t2))
    (hQ d0 (by simp) d0 (by simp) (adj_self d0))
    (hQ d1 (by simp) d1 (by simp) (adj_self d1))
    (hQ d0 (by simp) t0 (by simp) hn30)
    (hQ d0 (by simp) t1 (by simp) hn31)
    (hQ d0 (by simp) t2 (by simp) hn32)
    (hQ d1 (by simp) t1 (by simp) hn41)
    (hQ d1 (by simp) t2 (by simp) hn42)
  exact five_form1_comb _ _ _ _ _ _ _ _ hp hq
    (he01.symm.trans (H t0 (by simp) t1 (by simp)))
    (he02.symm.trans (H t0 (by simp) t2 (by simp)))
    (he12.symm.trans (H t1 (by simp) t2 (by simp)))
    (he34.symm.trans (H d0 (by simp) d1 (by simp)))

theorem five_triple (t0 t1 t2 d0 d1 : Fin 6) (a b v : Fin 6 → Bool)
    (he01 : adj t0 t1 = true) (he02 : adj t0 t2 = true) (he12 : adj t1 t2 = true) (he34 : adj d0 d1 = true)
    (hn30 : adj d0 t0 = false) (hn31 : adj d0 t1 = false) (hn32 : adj d0 t2 = false) (hn41 : adj d1 t1 = false)
    (H : ∀ i ∈ [t0, t1, t2, d0, d1], ∀ j ∈ [t0, t1, t2, d0, d1],
      adj i j = (P a i j && P b i j && P v i j)) : False := by
  have ca : ∀ i ∈ [t0, t1, t2, d0, d1], ∀ j ∈ [t0, t1, t2, d0, d1], adj i j = true → P a i j = true :=
    fun i hi j hj hij => bool_t1 _ _ _ (hij.symm.trans (H i hi j hj))
  have cb : ∀ i ∈ [t0, t1, t2, d0, d1], ∀ j ∈ [t0, t1, t2, d0, d1], adj i j = true → P b i j = true :=
    fun i hi j hj hij => bool_t2 _ _ _ (hij.symm.trans (H i hi j hj))
  have cv : ∀ i ∈ [t0, t1, t2, d0, d1], ∀ j ∈ [t0, t1, t2, d0, d1], adj i j = true → P v i j = true :=
    fun i hi j hj hij => bool_t3 _ _ _ (hij.symm.trans (H i hi j hj))
  have Fa := five_vc_nonedges (a t0) (a t1) (a t2) (a d0) (a d1)
    (ca t0 (by simp) t1 (by simp) he01) (ca t0 (by simp) t2 (by simp) he02)
    (ca t1 (by simp) t2 (by simp) he12) (ca d0 (by simp) d1 (by simp) he34)
  have Fb := five_vc_nonedges (b t0) (b t1) (b t2) (b d0) (b d1)
    (cb t0 (by simp) t1 (by simp) he01) (cb t0 (by simp) t2 (by simp) he02)
    (cb t1 (by simp) t2 (by simp) he12) (cb d0 (by simp) d1 (by simp) he34)
  have Fv := five_vc_nonedges (v t0) (v t1) (v t2) (v d0) (v d1)
    (cv t0 (by simp) t1 (by simp) he01) (cv t0 (by simp) t2 (by simp) he02)
    (cv t1 (by simp) t2 (by simp) he12) (cv d0 (by simp) d1 (by simp) he34)
  exact five_triple_fin _ _ _ _ _ _ _ _ _ _ _ _ Fa Fb Fv
    ((H d0 (by simp) t0 (by simp)).symm.trans hn30)
    ((H d0 (by simp) t1 (by simp)).symm.trans hn31)
    ((H d0 (by simp) t2 (by simp)).symm.trans hn32)
    ((H d1 (by simp) t1 (by simp)).symm.trans hn41)

theorem five_k2 (t0 t1 t2 d0 d1 : Fin 6) (u a b v : Fin 6 → Bool)
    (he01 : adj t0 t1 = true) (he02 : adj t0 t2 = true) (he12 : adj t1 t2 = true) (he34 : adj d0 d1 = true)
    (hn30 : adj d0 t0 = false) (hn31 : adj d0 t1 = false) (hn32 : adj d0 t2 = false)
    (hn41 : adj d1 t1 = false) (hn42 : adj d1 t2 = false)
    (H : ∀ i ∈ [t0, t1, t2, d0, d1], ∀ j ∈ [t0, t1, t2, d0, d1],
      adj i j = ((P u i j || (P a i j && P b i j)) && P v i j)) : False := by
  have hv : ∀ i ∈ [t0, t1, t2, d0, d1], ∀ j ∈ [t0, t1, t2, d0, d1], adj i j = true → P v i j = true :=
    fun i hi j hj hij => bool_a2 _ _ (hij.symm.trans (H i hi j hj))
  have kill_u : ∀ i ∈ [t0, t1, t2, d0, d1], ∀ j ∈ [t0, t1, t2, d0, d1],
      v i = true → adj i j = false → u j = false := by
    intro i hi j hj hvi hij
    have h3 := H i hi j hj
    rw [hij] at h3
    simp only [P, hvi] at h3
    exact bool_u0 _ _ _ _ h3
  have hv12 : v t1 = true ∨ v t2 = true := by
    have h := hv t1 (by simp) t2 (by simp) he12
    cases ht1 : v t1 <;> cases ht2 : v t2 <;> simp [P, ht1, ht2] at h ⊢
  have hv34 : v d0 = true ∨ v d1 = true := by
    have h := hv d0 (by simp) d1 (by simp) he34
    cases hd0 : v d0 <;> cases hd1 : v d1 <;> simp [P, hd0, hd1] at h ⊢
  have hu_d0 : u d0 = false := by
    rcases hv12 with h | h
    · exact kill_u t1 (by simp) d0 (by simp) h (by rw [adj_symm]; exact hn31)
    · exact kill_u t2 (by simp) d0 (by simp) h (by rw [adj_symm]; exact hn32)
  have hu_d1 : u d1 = false := by
    rcases hv12 with h | h
    · exact kill_u t1 (by simp) d1 (by simp) h (by rw [adj_symm]; exact hn41)
    · exact kill_u t2 (by simp) d1 (by simp) h (by rw [adj_symm]; exact hn42)
  have hu_t1 : u t1 = false := by
    rcases hv34 with h | h
    · exact kill_u d0 (by simp) t1 (by simp) h hn31
    · exact kill_u d1 (by simp) t1 (by simp) h hn41
  have hu_t2 : u t2 = false := by
    rcases hv34 with h | h
    · exact kill_u d0 (by simp) t2 (by simp) h hn32
    · exact kill_u d1 (by simp) t2 (by simp) h hn42
  cases hu0 : u t0
  · refine five_triple t0 t1 t2 d0 d1 a b v he01 he02 he12 he34 hn30 hn31 hn32 hn41 ?_
    intro i hi j hj
    have hui : u i = false := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption
    have huj : u j = false := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl <;> assumption
    have h1 := H i hi j hj
    simp only [P, hui, huj, Bool.false_or] at h1
    exact h1
  · have hvd0 : v d0 = false := by
      cases h : v d0
      · rfl
      · have h0 := kill_u d0 (by simp) t0 (by simp) h hn30
        rw [hu0] at h0; cases h0
    have hvd1 : v d1 = true := by
      rcases hv34 with h | h
      · rw [hvd0] at h; cases h
      · exact h
    have hvt0 : v t0 = false := by
      cases h : v t0
      · rfl
      · have h0 := kill_u t0 (by simp) t0 (by simp) h (adj_self t0)
        rw [hu0] at h0; cases h0
    have hvt1 : v t1 = true := by
      have h := hv t0 (by simp) t1 (by simp) he01
      simp only [P, hvt0, Bool.false_or] at h; exact h
    have hvt2 : v t2 = true := by
      have h := hv t0 (by simp) t2 (by simp) he02
      simp only [P, hvt0, Bool.false_or] at h; exact h
    have h_ab : ∀ i ∈ [t1, t2, d0, d1], ∀ j ∈ [t1, t2, d0, d1],
        P v i j = true → adj i j = (P a i j && P b i j) := by
      intro i hi j hj hvij
      have hi5 : i ∈ [t0, t1, t2, d0, d1] := by simp only [List.mem_cons] at hi ⊢; tauto
      have hj5 : j ∈ [t0, t1, t2, d0, d1] := by simp only [List.mem_cons] at hj ⊢; tauto
      have hui : u i = false := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl <;> assumption
      have huj : u j = false := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl <;> assumption
      have h1 := H i hi5 j hj5
      rw [hvij] at h1
      simp only [P, hui, huj, Bool.false_or, Bool.and_true] at h1
      exact h1
    exact five_2k2_aux (a t1) (a t2) (a d0) (a d1) (b t1) (b t2) (b d0) (b d1)
      ((h_ab d0 (by simp) d1 (by simp) (by simp [P, hvd1])).symm.trans he34)
      ((h_ab t1 (by simp) t2 (by simp) (by simp [P, hvt1])).symm.trans he12)
      ((h_ab d0 (by simp) t1 (by simp) (by simp [P, hvt1])).symm.trans hn31)
      ((h_ab d0 (by simp) t2 (by simp) (by simp [P, hvt2])).symm.trans hn32)
      ((h_ab d1 (by simp) t1 (by simp) (by simp [P, hvd1])).symm.trans hn41)
      ((h_ab d1 (by simp) t2 (by simp) (by simp [P, hvd1])).symm.trans hn42)
      ((h_ab t1 (by simp) t1 (by simp) (by simp [P, hvt1])).symm.trans (adj_self t1))
      ((h_ab t2 (by simp) t2 (by simp) (by simp [P, hvt2])).symm.trans (adj_self t2))
      ((h_ab d1 (by simp) d1 (by simp) (by simp [P, hvd1])).symm.trans (adj_self d1))

theorem five_core (t0 t1 t2 d0 d1 : Fin 6)
    (he01 : adj t0 t1 = true) (he02 : adj t0 t2 = true) (he12 : adj t1 t2 = true) (he34 : adj d0 d1 = true)
    (hn30 : adj d0 t0 = false) (hn31 : adj d0 t1 = false) (hn32 : adj d0 t2 = false)
    (hn41 : adj d1 t1 = false) (hn42 : adj d1 t2 = false)
    (h a b u v : Fin 6 → Bool) (c1 c2 cu cv : Bool)
    (H : ∀ i ∈ [t0, t1, t2, d0, d1], ∀ j ∈ [t0, t1, t2, d0, d1],
      adj i j = (P h i j || (c1 && (P a i j && P b i j) ||
        c2 && ((P u i j || cu && (P a i j && P b i j)) &&
          (P v i j || cv && (P a i j && P b i j)))))) : False := by
  have hh0 : ∀ i ∈ [t0, t1, t2, d0, d1], h i = false :=
    fun i hi => bool_hz _ _ ((adj_self i).symm.trans (H i hi i hi))
  have H' : ∀ i ∈ [t0, t1, t2, d0, d1], ∀ j ∈ [t0, t1, t2, d0, d1],
      adj i j = (c1 && (P a i j && P b i j) ||
        c2 && ((P u i j || cu && (P a i j && P b i j)) &&
          (P v i j || cv && (P a i j && P b i j)))) := fun i hi j hj => by
    have h1 := H i hi j hj
    simp only [P, hh0 i hi, hh0 j hj, Bool.false_or] at h1
    exact h1
  rcases c1 <;> rcases c2 <;> rcases cu <;> rcases cv <;>
  first
    | (refine five_k1 t0 t1 t2 d0 d1 (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false)
        he01 he02 he12 he34 hn30 hn31 hn32 hn41 hn42 ?_;
        intro i hi j hj; rw [H' i hi j hj];
        cases (P a i j && P b i j) <;> cases (P u i j) <;> cases (P v i j) <;> rfl)
    | (refine five_k1 t0 t1 t2 d0 d1 a b (fun _ => false) (fun _ => false)
        he01 he02 he12 he34 hn30 hn31 hn32 hn41 hn42 ?_;
        intro i hi j hj; rw [H' i hi j hj];
        cases (P a i j && P b i j) <;> cases (P u i j) <;> cases (P v i j) <;> rfl)
    | (refine five_k1 t0 t1 t2 d0 d1 (fun _ => false) (fun _ => false) u v
        he01 he02 he12 he34 hn30 hn31 hn32 hn41 hn42 ?_;
        intro i hi j hj; rw [H' i hi j hj];
        cases (P a i j && P b i j) <;> cases (P u i j) <;> cases (P v i j) <;> rfl)
    | (refine five_k1 t0 t1 t2 d0 d1 a b u v
        he01 he02 he12 he34 hn30 hn31 hn32 hn41 hn42 ?_;
        intro i hi j hj; rw [H' i hi j hj];
        cases (P a i j && P b i j) <;> cases (P u i j) <;> cases (P v i j) <;> rfl)
    | (refine five_k2 t0 t1 t2 d0 d1 u a b v
        he01 he02 he12 he34 hn30 hn31 hn32 hn41 hn42 ?_;
        intro i hi j hj; rw [H' i hi j hj];
        cases (P a i j && P b i j) <;> cases (P u i j) <;> cases (P v i j) <;> rfl)
    | (refine five_k2 t0 t1 t2 d0 d1 v a b u
        he01 he02 he12 he34 hn30 hn31 hn32 hn41 hn42 ?_;
        intro i hi j hj; rw [H' i hi j hj];
        cases (P a i j && P b i j) <;> cases (P u i j) <;> cases (P v i j) <;> rfl)

theorem no_2and_del (x : Fin 6) (h a b u v : Fin 6 → Bool) (c1 c2 cu cv : Bool)
    (H : ∀ i j : Fin 6, i ≠ x → j ≠ x →
      adj i j = (P h i j || (c1 && (P a i j && P b i j) ||
        c2 && ((P u i j || cu && (P a i j && P b i j)) &&
          (P v i j || cv && (P a i j && P b i j)))))) : False := by
  fin_cases x
  · exact five_core 3 4 5 1 2 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) h a b u v c1 c2 cu cv
      (fun i hi j hj => H i j (by revert i hi; decide) (by revert j hj; decide))
  · exact five_core 3 4 5 0 2 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) h a b u v c1 c2 cu cv
      (fun i hi j hj => H i j (by revert i hi; decide) (by revert j hj; decide))
  · exact five_core 3 4 5 0 1 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) h a b u v c1 c2 cu cv
      (fun i hi j hj => H i j (by revert i hi; decide) (by revert j hj; decide))
  · exact five_core 0 1 2 4 5 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) h a b u v c1 c2 cu cv
      (fun i hi j hj => H i j (by revert i hi; decide) (by revert j hj; decide))
  · exact five_core 2 0 1 5 3 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) h a b u v c1 c2 cu cv
      (fun i hi j hj => H i j (by revert i hi; decide) (by revert j hj; decide))
  · exact five_core 2 0 1 4 3 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) h a b u v c1 c2 cu cv
      (fun i hi j hj => H i j (by revert i hi; decide) (by revert j hj; decide))

def eval2 (h a b u v : Fin 6 → Bool) (c1 c2 cu cv : Bool) (i j : Fin 6) : Bool :=
  P h i j || (c1 && (P a i j && P b i j) ||
    c2 && ((P u i j || cu && (P a i j && P b i j)) &&
      (P v i j || cv && (P a i j && P b i j))))

theorem ble_or {x1 x2 y1 y2 : Bool} (hx : x1 = true → x2 = true) (hy : y1 = true → y2 = true) :
    (x1 || y1) = true → (x2 || y2) = true := by
  cases x1 <;> cases y1 <;> simp at *
  · exact Or.inr hy
  · exact Or.inl hx
  · exact Or.inl hx

theorem ble_and {x1 x2 y1 y2 : Bool} (hx : x1 = true → x2 = true) (hy : y1 = true → y2 = true) :
    (x1 && y1) = true → (x2 && y2) = true := by
  cases x1 <;> cases y1 <;> simp at *
  exact ⟨hx, hy⟩

theorem ble_P (f : Fin 6 → Bool) (y w : Fin 6) : P f y y = true → P f y w = true := by
  unfold P; cases f y <;> simp

theorem eval2_mono_diag (h a b u v : Fin 6 → Bool) (c1 c2 cu cv : Bool) (y w : Fin 6) :
    eval2 h a b u v c1 c2 cu cv y w = false →
    eval2 h a b u v c1 c2 cu cv y y = false := by
  intro hw
  cases hdiag : eval2 h a b u v c1 c2 cu cv y y
  · rfl
  · exfalso
    have hg1 : (P a y y && P b y y) = true → (P a y w && P b y w) = true :=
      ble_and (ble_P a y w) (ble_P b y w)
    have hstep : eval2 h a b u v c1 c2 cu cv y y = true → eval2 h a b u v c1 c2 cu cv y w = true := by
      unfold eval2
      exact ble_or (ble_P h y w)
        (ble_or (ble_and id hg1)
          (ble_and id (ble_and (ble_or (ble_P u y w) (ble_and id hg1))
            (ble_or (ble_P v y w) (ble_and id hg1)))))
    have ht := hstep hdiag
    rw [hw] at ht
    cases ht

theorem vc_non_neighbor : ∀ V : Fin 6 → Bool,
    (∀ i j : Fin 6, adj i j = true → (V i || V j) = true) →
    ∀ y : Fin 6, ∃ w : Fin 6, V w = true ∧ adj y w = false := by
  decide

theorem vc_miss_at_most_one_after_del : ∀ V : Fin 6 → Bool,
    (∀ i j : Fin 6, adj i j = true → (V i || V j) = true) →
    (∀ i : Fin 6, V i = true) ∨
    (∃ x : Fin 6, ∀ i j : Fin 6, i ≠ x → j ≠ x → (V i || V j) = true ∨ i = j) := by
  decide

theorem no_hom_and_2and (V h a b u v : Fin 6 → Bool) (c1 c2 cu cv : Bool)
    (H : ∀ i j : Fin 6, adj i j = (P V i j && eval2 h a b u v c1 c2 cu cv i j)) : False := by
  have hvc : ∀ i j : Fin 6, adj i j = true → (V i || V j) = true := by
    intro i j hij
    have h1 := hij.symm.trans (H i j)
    cases hV : P V i j
    · rw [hV] at h1; cases h1
    · exact hV
  rcases vc_miss_at_most_one_after_del V hvc with hall | ⟨x, hx⟩
  · refine no_2and_del 0 h a b u v c1 c2 cu cv (fun i j _ _ => ?_)
    have h1 := H i j
    simp only [P, hall i, Bool.true_or, Bool.true_and] at h1
    exact h1
  · refine no_2and_del x h a b u v c1 c2 cu cv (fun i j hi hj => ?_)
    rcases hx i j hi hj with hV | rfl
    · have h1 := H i j
      simp only [P, hV, Bool.true_and] at h1
      exact h1
    · obtain ⟨w, hwV, hnw⟩ := vc_non_neighbor V hvc i
      have h1 := H i w
      rw [hnw] at h1
      simp only [P, hwV, Bool.or_true, Bool.true_and] at h1
      have hdiag := eval2_mono_diag h a b u v c1 c2 cu cv i w h1.symm
      rw [adj_self i]
      exact hdiag.symm

theorem no_k22 : ∀ i1 i2 j1 j2 : Fin 6,
    i1 ≠ i2 → j1 ≠ j2 →
    adj i1 j1 = true → adj i1 j2 = true → adj i2 j1 = true → adj i2 j2 = true → False := by
  decide

theorem two_true_of_not_le1 (f : Fin 6 → Bool) (h : ¬ ∃ x : Fin 6, ∀ i : Fin 6, i ≠ x → f i = false) :
    ∃ i1 i2 : Fin 6, i1 ≠ i2 ∧ f i1 = true ∧ f i2 = true := by
  by_cases hex : ∃ i : Fin 6, f i = true
  · obtain ⟨i1, hi1⟩ := hex
    by_cases hex2 : ∃ i2 : Fin 6, i2 ≠ i1 ∧ f i2 = true
    · obtain ⟨i2, hne, hi2⟩ := hex2
      exact ⟨i1, i2, hne.symm, hi1, hi2⟩
    · exfalso
      apply h
      refine ⟨i1, fun i2 hne => ?_⟩
      cases hf2 : f i2
      · rfl
      · exact absurd ⟨i2, hne, hf2⟩ hex2
  · exfalso
    apply h
    refine ⟨0, fun i _ => ?_⟩
    cases hf : f i
    · rfl
    · exact absurd ⟨i, hf⟩ hex

theorem star_of_le_adj (a b : Fin 6 → Bool)
    (hle : ∀ i j : Fin 6, ((a i || a j) && (b i || b j)) = true → adj i j = true) :
    (∃ x : Fin 6, ∀ i : Fin 6, i ≠ x → a i = false) ∨
    (∃ x : Fin 6, ∀ i : Fin 6, i ≠ x → b i = false) := by
  by_cases ha : ∃ x : Fin 6, ∀ i : Fin 6, i ≠ x → a i = false
  · exact Or.inl ha
  · by_cases hb : ∃ x : Fin 6, ∀ i : Fin 6, i ≠ x → b i = false
    · exact Or.inr hb
    · exfalso
      obtain ⟨i1, i2, hi, ha1, ha2⟩ := two_true_of_not_le1 a ha
      obtain ⟨j1, j2, hj, hb1, hb2⟩ := two_true_of_not_le1 b hb
      exact no_k22 i1 i2 j1 j2 hi hj
        (hle i1 j1 (by simp [ha1, hb1]))
        (hle i1 j2 (by simp [ha1, hb2]))
        (hle i2 j1 (by simp [ha2, hb1]))
        (hle i2 j2 (by simp [ha2, hb2]))

theorem not_le_adj_g1 (a1 b1 a2 b2 a3 b3 : Fin 6 → Bool) (c21 d21 c31 d31 c32 d32 o1 o2 o3 : Bool)
    (H : ∀ i j : Fin 6,
      let g1 := P a1 i j && P b1 i j
      let g2 := (P a2 i j || c21 && g1) && (P b2 i j || d21 && g1)
      let g3 := (P a3 i j || c31 && g1 || c32 && g2) && (P b3 i j || d31 && g1 || d32 && g2)
      adj i j = (o1 && g1 || o2 && g2 || o3 && g3))
    (hle : ∀ i j : Fin 6, (P a1 i j && P b1 i j) = true → adj i j = true) : False := by
  have hstar := star_of_le_adj a1 b1 hle
  have hex : ∃ x : Fin 6, ∀ i j : Fin 6, i ≠ x → j ≠ x → (P a1 i j && P b1 i j) = false := by
    rcases hstar with ⟨x, hx⟩ | ⟨x, hx⟩
    · exact ⟨x, fun i j hi hj => by simp [P, hx i hi, hx j hj]⟩
    · exact ⟨x, fun i j hi hj => by simp [P, hx i hi, hx j hj]⟩
  obtain ⟨x, hx⟩ := hex
  refine no_2and_del x (fun _ => false) a2 b2 a3 b3 o2 o3 c32 d32 (fun i j hi hj => ?_)
  have h1 := H i j
  dsimp only at h1
  rw [hx i j hi hj] at h1
  simp only [P, Bool.false_or, Bool.and_false, Bool.or_false] at h1 ⊢
  exact h1

theorem caseA4_8bool : ∀ ax bx ay by_ ar br as_ bs : Bool,
    (ax && bx) = false → (ay && by_) = false → (ar && br) = false → (as_ && bs) = false →
    ((ax || ay) && (bx || by_)) = true →
    ((ar || as_) && (br || bs)) = true →
    ((ax || ar) && (bx || br)) = false →
    ((ax || as_) && (bx || bs)) = false → False := by
  decide

theorem caseA4_pick_side (v2 v3 : Fin 6) (B2 B3 : Fin 6 → Bool)
    (hv2 : v2 = 0 ∨ v2 = 1 ∨ v2 = 2) (hv3 : v3 = 3 ∨ v3 = 4 ∨ v3 = 5)
    (hb2 : ∀ u : Fin 6, B2 u = true → adj v2 u = true)
    (hb3 : ∀ u : Fin 6, B3 u = true → adj v3 u = true)
    (hvc : ∀ i j : Fin 6, adj i j = true → ((B2 i || B3 i) || (B2 j || B3 j)) = true) :
    ∃ x y r s : Fin 6,
      adj x y = true ∧ adj r s = true ∧
      adj x r = false ∧ adj x s = false ∧
      (B2 x || B3 x) = true ∧
      x ≠ v2 ∧ y ≠ v2 ∧ x ≠ v3 ∧ y ≠ v3 ∧
      r ≠ v2 ∧ s ≠ v2 ∧ r ≠ v3 ∧ s ≠ v3 := by
  have hrs : ∃ r s : Fin 6, (r = 3 ∨ r = 4 ∨ r = 5) ∧ (s = 3 ∨ s = 4 ∨ s = 5) ∧
      adj r s = true ∧ r ≠ v3 ∧ s ≠ v3 := by
    rcases hv3 with rfl | rfl | rfl
    · exact ⟨4, 5, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl), by decide, by decide, by decide⟩
    · exact ⟨3, 5, Or.inl rfl, Or.inr (Or.inr rfl), by decide, by decide, by decide⟩
    · exact ⟨3, 4, Or.inl rfl, Or.inr (Or.inl rfl), by decide, by decide, by decide⟩
  obtain ⟨r, s, hr3, hs3, hadjrs, hrv3, hsv3⟩ := hrs
  have hxy : ∃ x y : Fin 6, (x = 0 ∨ x = 1) ∧ (y = 0 ∨ y = 1 ∨ y = 2) ∧
      adj x y = true ∧ (B2 x || B3 x) = true ∧ x ≠ v2 ∧ y ≠ v2 := by
    have h01 := hvc 0 1 (by decide)
    have hb3_0 : B3 0 = false := by
      cases h : B3 0
      · rfl
      · have ha := hb3 0 h
        rcases hv3 with rfl | rfl | rfl <;> simp [adj, edgeList] at ha
    have hb3_1 : B3 1 = false := by
      cases h : B3 1
      · rfl
      · have ha := hb3 1 h
        rcases hv3 with rfl | rfl | rfl <;> simp [adj, edgeList] at ha
    rcases hv2 with rfl | rfl | rfl
    · have hb2_0 : B2 0 = false := by
        cases h : B2 0
        · rfl
        · have ha := hb2 0 h; simp [adj, edgeList] at ha
      rw [hb2_0, hb3_0] at h01
      simp only [Bool.false_or] at h01
      exact ⟨1, 2, Or.inr rfl, Or.inr (Or.inr rfl), by decide, h01, by decide, by decide⟩
    · have hb2_1 : B2 1 = false := by
        cases h : B2 1
        · rfl
        · have ha := hb2 1 h; simp [adj, edgeList] at ha
      rw [hb2_1, hb3_1] at h01
      simp only [Bool.or_false] at h01
      exact ⟨0, 2, Or.inl rfl, Or.inr (Or.inr rfl), by decide, h01, by decide, by decide⟩
    · cases hU0 : (B2 0 || B3 0)
      · rw [hU0, Bool.false_or] at h01
        exact ⟨1, 0, Or.inr rfl, Or.inl rfl, by decide, h01, by decide, by decide⟩
      · exact ⟨0, 1, Or.inl rfl, Or.inr (Or.inl rfl), by decide, hU0, by decide, by decide⟩
  obtain ⟨x, y, hx01, hy012, hadjxy, hUx, hxv2, hyv2⟩ := hxy
  refine ⟨x, y, r, s, hadjxy, hadjrs, ?_, ?_, hUx, hxv2, hyv2, ?_, ?_, ?_, ?_, hrv3, hsv3⟩
  · rcases hx01 with rfl | rfl <;> rcases hr3 with rfl | rfl | rfl <;> decide
  · rcases hx01 with rfl | rfl <;> rcases hs3 with rfl | rfl | rfl <;> decide
  · rcases hx01 with rfl | rfl <;> rcases hv3 with rfl | rfl | rfl <;> decide
  · rcases hy012 with rfl | rfl | rfl <;> rcases hv3 with rfl | rfl | rfl <;> decide
  · rcases hr3 with rfl | rfl | rfl <;> rcases hv2 with rfl | rfl | rfl <;> decide
  · rcases hs3 with rfl | rfl | rfl <;> rcases hv2 with rfl | rfl | rfl <;> decide

theorem fin6_split (v : Fin 6) : (v = 0 ∨ v = 1 ∨ v = 2) ∨ (v = 3 ∨ v = 4 ∨ v = 5) := by
  fin_cases v <;> simp

theorem caseA4_pick (v2 v3 : Fin 6) (B2 B3 : Fin 6 → Bool)
    (hb2 : ∀ u : Fin 6, B2 u = true → adj v2 u = true)
    (hb3 : ∀ u : Fin 6, B3 u = true → adj v3 u = true)
    (hvc : ∀ i j : Fin 6, adj i j = true → ((B2 i || B3 i) || (B2 j || B3 j)) = true) :
    ∃ x y r s : Fin 6,
      adj x y = true ∧ adj r s = true ∧
      adj x r = false ∧ adj x s = false ∧
      (B2 x || B3 x) = true ∧
      x ≠ v2 ∧ y ≠ v2 ∧ x ≠ v3 ∧ y ≠ v3 ∧
      r ≠ v2 ∧ s ≠ v2 ∧ r ≠ v3 ∧ s ≠ v3 := by
  rcases fin6_split v2 with h2 | h2 <;> rcases fin6_split v3 with h3 | h3
  · exfalso
    have h45 := hvc 4 5 (by decide)
    have h24 : B2 4 = false := by
      cases h : B2 4; · rfl
      have ha := hb2 4 h; rcases h2 with rfl | rfl | rfl <;> simp [adj, edgeList] at ha
    have h25 : B2 5 = false := by
      cases h : B2 5; · rfl
      have ha := hb2 5 h; rcases h2 with rfl | rfl | rfl <;> simp [adj, edgeList] at ha
    have h34 : B3 4 = false := by
      cases h : B3 4; · rfl
      have ha := hb3 4 h; rcases h3 with rfl | rfl | rfl <;> simp [adj, edgeList] at ha
    have h35 : B3 5 = false := by
      cases h : B3 5; · rfl
      have ha := hb3 5 h; rcases h3 with rfl | rfl | rfl <;> simp [adj, edgeList] at ha
    rw [h24, h25, h34, h35] at h45; cases h45
  · exact caseA4_pick_side v2 v3 B2 B3 h2 h3 hb2 hb3 hvc
  · obtain ⟨x, y, r, s, h1, h2', h3', h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ :=
      caseA4_pick_side v3 v2 B3 B2 h3 h2 hb3 hb2 (fun i j hij => by
        have h := hvc i j hij
        revert h
        cases B2 i <;> cases B3 i <;> cases B2 j <;> cases B3 j <;> simp)
    refine ⟨x, y, r, s, h1, h2', h3', h4, ?_, h8, h9, h6, h7, h12, h13, h10, h11⟩
    revert h5
    cases B2 x <;> cases B3 x <;> simp
  · exfalso
    have h01 := hvc 0 1 (by decide)
    have h20 : B2 0 = false := by
      cases h : B2 0; · rfl
      have ha := hb2 0 h; rcases h2 with rfl | rfl | rfl <;> simp [adj, edgeList] at ha
    have h21 : B2 1 = false := by
      cases h : B2 1; · rfl
      have ha := hb2 1 h; rcases h2 with rfl | rfl | rfl <;> simp [adj, edgeList] at ha
    have h30 : B3 0 = false := by
      cases h : B3 0; · rfl
      have ha := hb3 0 h; rcases h3 with rfl | rfl | rfl <;> simp [adj, edgeList] at ha
    have h31 : B3 1 = false := by
      cases h : B3 1; · rfl
      have ha := hb3 1 h; rcases h3 with rfl | rfl | rfl <;> simp [adj, edgeList] at ha
    rw [h20, h21, h30, h31] at h01; cases h01

theorem caseA4 (a1 b1 a2 b2 a3 b3 : Fin 6 → Bool)
    (H : ∀ i j : Fin 6,
      adj i j = (((P a2 i j || (P a1 i j && P b1 i j)) && P b2 i j) ||
                 ((P a3 i j || (P a1 i j && P b1 i j)) && P b3 i j))) : False := by
  have hb2_ge2 : ¬ ∃ x : Fin 6, ∀ i : Fin 6, i ≠ x → b2 i = false := by
    rintro ⟨x, hx⟩
    refine no_2and_del x (fun _ => false) a1 b1 a3 b3 false true true false (fun i j hi hj => ?_)
    have h1 := H i j
    simp only [P, hx i hi, hx j hj, Bool.false_or, Bool.and_false, Bool.false_and, Bool.true_and,
      Bool.or_false] at h1 ⊢
    exact h1
  have hb3_ge2 : ¬ ∃ x : Fin 6, ∀ i : Fin 6, i ≠ x → b3 i = false := by
    rintro ⟨x, hx⟩
    refine no_2and_del x (fun _ => false) a1 b1 a2 b2 false true true false (fun i j hi hj => ?_)
    have h1 := H i j
    simp only [P, hx i hi, hx j hj, Bool.false_or, Bool.and_false, Bool.false_and, Bool.true_and,
      Bool.or_false] at h1 ⊢
    exact h1
  have ha2b2_le : ∀ i j : Fin 6, (P a2 i j && P b2 i j) = true → adj i j = true := by
    intro i j h
    rw [H i j]
    cases h1 : P a2 i j <;> cases h2 : P b2 i j <;> simp [h1, h2] at h ⊢
  have ha3b3_le : ∀ i j : Fin 6, (P a3 i j && P b3 i j) = true → adj i j = true := by
    intro i j h
    rw [H i j]
    cases h1 : P a3 i j <;> cases h2 : P b3 i j <;> simp [h1, h2] at h ⊢
  have ha2_le1 : ∃ v2 : Fin 6, ∀ i : Fin 6, i ≠ v2 → a2 i = false := by
    rcases star_of_le_adj a2 b2 ha2b2_le with h | h
    · exact h
    · exact absurd h hb2_ge2
  have ha3_le1 : ∃ v3 : Fin 6, ∀ i : Fin 6, i ≠ v3 → a3 i = false := by
    rcases star_of_le_adj a3 b3 ha3b3_le with h | h
    · exact h
    · exact absurd h hb3_ge2
  obtain ⟨v2, hv2⟩ := ha2_le1
  obtain ⟨v3, hv3⟩ := ha3_le1
  cases ha2v : a2 v2
  · refine no_2and_del v3 (fun _ => false) a1 b1 (fun _ => false) (fun i => b2 i || b3 i)
      false true true false (fun i j hi hj => ?_)
    have ha2_all : ∀ k : Fin 6, a2 k = false := fun k => by
      by_cases hk : k = v2
      · subst hk; exact ha2v
      · exact hv2 k hk
    have h1 := H i j
    simp only [P, ha2_all i, ha2_all j, hv3 i hi, hv3 j hj, Bool.false_or, Bool.false_and,
      Bool.true_and, Bool.or_false] at h1 ⊢
    rw [h1]
    cases (a1 i || a1 j) && (b1 i || b1 j) <;> cases b2 i <;> cases b2 j <;> cases b3 i <;> cases b3 j <;> rfl
  · cases ha3v : a3 v3
    · refine no_2and_del v2 (fun _ => false) a1 b1 (fun _ => false) (fun i => b2 i || b3 i)
        false true true false (fun i j hi hj => ?_)
      have ha3_all : ∀ k : Fin 6, a3 k = false := fun k => by
        by_cases hk : k = v3
        · subst hk; exact ha3v
        · exact hv3 k hk
      have h1 := H i j
      simp only [P, ha3_all i, ha3_all j, hv2 i hi, hv2 j hj, Bool.false_or, Bool.false_and,
        Bool.true_and, Bool.or_false] at h1 ⊢
      rw [h1]
      cases (a1 i || a1 j) && (b1 i || b1 j) <;> cases b2 i <;> cases b2 j <;> cases b3 i <;> cases b3 j <;> rfl
    · have hb2_sub : ∀ u : Fin 6, b2 u = true → adj v2 u = true := by
        intro u hu
        exact ha2b2_le v2 u (by simp [P, ha2v, hu])
      have hb3_sub : ∀ u : Fin 6, b3 u = true → adj v3 u = true := by
        intro u hu
        exact ha3b3_le v3 u (by simp [P, ha3v, hu])
      have hU_vc : ∀ i j : Fin 6, adj i j = true → ((b2 i || b3 i) || (b2 j || b3 j)) = true := by
        intro i j hij
        have h1 := hij.symm.trans (H i j)
        cases hb2i : b2 i <;> cases hb2j : b2 j <;> cases hb3i : b3 i <;> cases hb3j : b3 j <;>
          simp [P, hb2i, hb2j, hb3i, hb3j] at h1 ⊢
      have hg1_U : ∀ i j : Fin 6,
          ((P a1 i j && P b1 i j) && ((b2 i || b3 i) || (b2 j || b3 j))) = true → adj i j = true := by
        intro i j h
        rw [H i j]
        cases hg : (P a1 i j && P b1 i j)
        · rw [hg] at h; cases h
        · rw [hg] at h
          cases hb2i : b2 i <;> cases hb2j : b2 j <;> cases hb3i : b3 i <;> cases hb3j : b3 j <;>
            simp [P, hb2i, hb2j, hb3i, hb3j] at h ⊢
      have hdiag : ∀ v : Fin 6, (a1 v && b1 v) = false := by
        intro v
        obtain ⟨w, hwU, hnw⟩ := vc_non_neighbor (fun k => b2 k || b3 k) hU_vc v
        cases ha1v : a1 v <;> cases hb1v : b1 v
        · rfl
        · rfl
        · rfl
        · have ht := hg1_U v w (by simp [P, ha1v, hb1v, hwU])
          rw [hnw] at ht; cases ht
      obtain ⟨x, y, r, s, hxy, hrs, hxr, hxs, hUx, hxv2, hyv2, hxv3, hyv3, hrv2, hsv2, hrv3, hsv3⟩ :=
        caseA4_pick v2 v3 b2 b3 hb2_sub hb3_sub hU_vc
      have hg1_xy : (P a1 x y && P b1 x y) = true := by
        have h1 := hxy.symm.trans (H x y)
        simp only [P, hv2 x hxv2, hv2 y hyv2, hv3 x hxv3, hv3 y hyv3, Bool.false_or] at h1
        cases h : (a1 x || a1 y) && (b1 x || b1 y)
        · rw [h] at h1; simp at h1
        · exact h
      have hg1_rs : (P a1 r s && P b1 r s) = true := by
        have h1 := hrs.symm.trans (H r s)
        simp only [P, hv2 r hrv2, hv2 s hsv2, hv3 r hrv3, hv3 s hsv3, Bool.false_or] at h1
        cases h : (a1 r || a1 s) && (b1 r || b1 s)
        · rw [h] at h1; simp at h1
        · exact h
      have hg1_xr : (P a1 x r && P b1 x r) = false := by
        cases h : (P a1 x r && P b1 x r)
        · rfl
        · have ht := hg1_U x r (by rw [h, hUx]; rfl)
          rw [hxr] at ht; cases ht
      have hg1_xs : (P a1 x s && P b1 x s) = false := by
        cases h : (P a1 x s && P b1 x s)
        · rfl
        · have ht := hg1_U x s (by rw [h, hUx]; rfl)
          rw [hxs] at ht; cases ht
      exact caseA4_8bool (a1 x) (b1 x) (a1 y) (b1 y) (a1 r) (b1 r) (a1 s) (b1 s)
        (hdiag x) (hdiag y) (hdiag r) (hdiag s) hg1_xy hg1_rs hg1_xr hg1_xs

theorem caseA_sub (a1 b1 a2 b2 a3 b3 : Fin 6 → Bool) (c21 c31 : Bool)
    (H : ∀ i j : Fin 6,
      adj i j = (((P a2 i j || c21 && (P a1 i j && P b1 i j)) && P b2 i j) ||
                 ((P a3 i j || c31 && (P a1 i j && P b1 i j)) && P b3 i j))) : False := by
  cases c21 <;> cases c31
  · refine no_2and_del 0 (fun _ => false) a2 b2 a3 b3 true true false false (fun i j _ _ => ?_)
    have h1 := H i j
    simp only [P, Bool.false_and, Bool.or_false, Bool.true_and, Bool.false_or] at h1 ⊢
    exact h1
  · have ha2b2_le : ∀ i j : Fin 6, (P a2 i j && P b2 i j) = true → adj i j = true := by
      intro i j h; rw [H i j]; simp only [Bool.false_and, Bool.or_false]; rw [h]; rfl
    have hex : ∃ x : Fin 6, ∀ i j : Fin 6, i ≠ x → j ≠ x → (P a2 i j && P b2 i j) = false := by
      rcases star_of_le_adj a2 b2 ha2b2_le with ⟨x, hx⟩ | ⟨x, hx⟩
      · exact ⟨x, fun i j hi hj => by simp [P, hx i hi, hx j hj]⟩
      · exact ⟨x, fun i j hi hj => by simp [P, hx i hi, hx j hj]⟩
    obtain ⟨x, hx⟩ := hex
    refine no_2and_del x (fun _ => false) a1 b1 a3 b3 false true true false (fun i j hi hj => ?_)
    have h1 := H i j
    simp only [Bool.false_and, Bool.or_false, Bool.true_and] at h1
    rw [hx i j hi hj] at h1
    simp only [P, Bool.false_or, Bool.false_and, Bool.true_and, Bool.or_false] at h1 ⊢
    exact h1
  · have ha3b3_le : ∀ i j : Fin 6, (P a3 i j && P b3 i j) = true → adj i j = true := by
      intro i j h; rw [H i j]; simp only [Bool.false_and, Bool.or_false]; rw [h]; simp
    have hex : ∃ x : Fin 6, ∀ i j : Fin 6, i ≠ x → j ≠ x → (P a3 i j && P b3 i j) = false := by
      rcases star_of_le_adj a3 b3 ha3b3_le with ⟨x, hx⟩ | ⟨x, hx⟩
      · exact ⟨x, fun i j hi hj => by simp [P, hx i hi, hx j hj]⟩
      · exact ⟨x, fun i j hi hj => by simp [P, hx i hi, hx j hj]⟩
    obtain ⟨x, hx⟩ := hex
    refine no_2and_del x (fun _ => false) a1 b1 a2 b2 false true true false (fun i j hi hj => ?_)
    have h1 := H i j
    simp only [Bool.false_and, Bool.or_false, Bool.true_and] at h1
    rw [hx i j hi hj] at h1
    simp only [P, Bool.false_or, Bool.false_and, Bool.true_and, Bool.or_false] at h1 ⊢
    exact h1
  · exact caseA4 a1 b1 a2 b2 a3 b3 (fun i j => by simpa using H i j)

theorem caseA (a1 b1 a2 b2 a3 b3 : Fin 6 → Bool) (c21 c31 d31 c32 d32 : Bool)
    (H : ∀ i j : Fin 6,
      let g1 := P a1 i j && P b1 i j
      let g2 := (P a2 i j || c21 && g1) && P b2 i j
      let g3 := (P a3 i j || c31 && g1 || c32 && g2) && (P b3 i j || d31 && g1 || d32 && g2)
      adj i j = (g2 || g3)) : False := by
  have H' : ∀ i j : Fin 6,
      let g1 := P a1 i j && P b1 i j
      let g2 := (P a2 i j || c21 && g1) && P b2 i j
      let g3 := (P a3 i j || c31 && g1) && (P b3 i j || d31 && g1)
      adj i j = (g2 || g3) := fun i j => by
    have h1 := H i j
    dsimp only at h1 ⊢
    rw [h1]
    cases ((P a2 i j || c21 && (P a1 i j && P b1 i j)) && P b2 i j) <;>
    cases (P a3 i j || c31 && (P a1 i j && P b1 i j)) <;>
    cases (P b3 i j || d31 && (P a1 i j && P b1 i j)) <;>
    cases c32 <;> cases d32 <;> rfl
  cases d31
  · exact caseA_sub a1 b1 a2 b2 a3 b3 c21 c31 (fun i j => by simpa using H' i j)
  · cases c31
    · refine caseA_sub a1 b1 a2 b2 b3 a3 c21 true (fun i j => ?_)
      have h1 := H' i j
      dsimp only at h1
      rw [h1]
      cases ((P a2 i j || c21 && (P a1 i j && P b1 i j)) && P b2 i j) <;>
      cases P a3 i j <;> cases P b3 i j <;> cases (P a1 i j && P b1 i j) <;> rfl
    · refine not_le_adj_g1 a1 b1 a2 b2 a3 b3 c21 false true true c32 d32 false true true
        (fun i j => by simpa using H i j) (fun i j hg1 => ?_)
      have h1 := H' i j
      dsimp only at h1
      rw [h1, hg1]
      simp

theorem caseB_sub (a1 b1 a2 b2 a3 b3 : Fin 6 → Bool) (c21 c31 d31 c32 : Bool)
    (H : ∀ i j : Fin 6,
      let g1 := P a1 i j && P b1 i j
      let g2 := (P a2 i j || c21 && g1) && P b2 i j
      let g3 := (P a3 i j || c31 && g1 || c32 && g2) && (P b3 i j || d31 && g1)
      adj i j = g3) : False := by
  cases d31
  · refine no_hom_and_2and b3 a3 a1 b1 a2 b2 c31 c32 c21 false (fun i j => ?_)
    have h1 := H i j
    dsimp only at h1
    rw [h1]
    unfold eval2
    cases P b3 i j <;> cases P a3 i j <;> cases (P a1 i j && P b1 i j) <;>
    cases P a2 i j <;> cases P b2 i j <;>
    cases c21 <;> cases c31 <;> cases c32 <;> rfl
  · cases c31
    · cases c32
      · refine no_hom_and_2and a3 b3 a1 b1 (fun _ => false) (fun _ => false) true false false false (fun i j => ?_)
        have h1 := H i j
        dsimp only at h1
        rw [h1]
        unfold eval2
        cases P a3 i j <;> cases P b3 i j <;> cases (P a1 i j && P b1 i j) <;> rfl
      · refine no_hom_and_2and (fun k => a3 k || b2 k) (fun _ => false) a1 b1
          (fun k => a3 k || a2 k) b3 false true c21 true (fun i j => ?_)
        have h1 := H i j
        dsimp only at h1
        rw [h1]
        unfold eval2 P
        dsimp only
        have hstep : ∀ a3i a3j b2i b2j a2i a2j b3' g1 c21' : Bool,
            ((a3i || a3j || false && g1 || true && ((a2i || a2j || c21' && g1) && (b2i || b2j))) &&
              (b3' || true && g1)) =
            (((a3i || b2i) || (a3j || b2j)) &&
              (false || false || (false && g1 ||
                true && (((a3i || a2i) || (a3j || a2j) || c21' && g1) && (b3' || true && g1))))) := by
          decide
        exact hstep _ _ _ _ _ _ _ _ _
    · refine not_le_adj_g1 a1 b1 a2 b2 a3 b3 c21 false true true c32 false false false true
        (fun i j => by simpa using H i j) (fun i j hg1 => ?_)
      have h1 := H i j
      dsimp only at h1
      rw [h1, hg1]
      simp

theorem core3_norm (a1 b1 a2 b2 a3 b3 : Fin 6 → Bool) (c21 c31 d31 c32 d32 o2 : Bool)
    (H : ∀ i j : Fin 6,
      let g1 := P a1 i j && P b1 i j
      let g2 := (P a2 i j || c21 && g1) && P b2 i j
      let g3 := (P a3 i j || c31 && g1 || c32 && g2) && (P b3 i j || d31 && g1 || d32 && g2)
      adj i j = (o2 && g2 || g3)) : False := by
  cases o2
  · cases d32
    · exact caseB_sub a1 b1 a2 b2 a3 b3 c21 c31 d31 c32 (fun i j => by simpa using H i j)
    · cases c32
      · refine caseB_sub a1 b1 a2 b2 b3 a3 c21 d31 c31 true (fun i j => ?_)
        have h1 := H i j
        dsimp only at h1 ⊢
        rw [h1]
        generalize ((P a2 i j || c21 && (P a1 i j && P b1 i j)) && P b2 i j) = g2
        generalize (P a1 i j && P b1 i j) = g1
        cases P a3 i j <;> cases P b3 i j <;> cases g1 <;> cases g2 <;>
        cases c31 <;> cases d31 <;> rfl
      · refine caseA a1 b1 a2 b2 a3 b3 c21 c31 d31 false false (fun i j => ?_)
        have h1 := H i j
        dsimp only at h1 ⊢
        rw [h1]
        cases (P a3 i j || c31 && (P a1 i j && P b1 i j)) <;>
        cases (P b3 i j || d31 && (P a1 i j && P b1 i j)) <;>
        cases ((P a2 i j || c21 && (P a1 i j && P b1 i j)) && P b2 i j) <;> rfl
  · exact caseA a1 b1 a2 b2 a3 b3 c21 c31 d31 c32 d32 (fun i j => by simpa using H i j)

theorem core3 (h a1 b1 a2 b2 a3 b3 : Fin 6 → Bool) (c21 d21 c31 d31 c32 d32 o1 o2 o3 : Bool)
    (H : ∀ i j : Fin 6,
      let g1 := P a1 i j && P b1 i j
      let g2 := (P a2 i j || c21 && g1) && (P b2 i j || d21 && g1)
      let g3 := (P a3 i j || c31 && g1 || c32 && g2) && (P b3 i j || d31 && g1 || d32 && g2)
      adj i j = (P h i j || (o1 && g1 || o2 && g2 || o3 && g3))) : False := by
  have hh0 : ∀ i : Fin 6, h i = false := fun i => bool_hz _ _ ((adj_self i).symm.trans (H i i))
  have H0 : ∀ i j : Fin 6,
      let g1 := P a1 i j && P b1 i j
      let g2 := (P a2 i j || c21 && g1) && (P b2 i j || d21 && g1)
      let g3 := (P a3 i j || c31 && g1 || c32 && g2) && (P b3 i j || d31 && g1 || d32 && g2)
      adj i j = (o1 && g1 || o2 && g2 || o3 && g3) := fun i j => by
    have h1 := H i j
    dsimp only at h1 ⊢
    simp only [P, hh0 i, hh0 j, Bool.false_or] at h1
    exact h1
  cases o1
  · cases o3
    · refine no_2and_del 0 (fun _ => false) a1 b1 a2 b2 false o2 c21 d21 (fun i j _ _ => ?_)
      have h1 := H0 i j
      dsimp only at h1
      simp only [P, Bool.false_and, Bool.false_or, Bool.or_false] at h1 ⊢
      exact h1
    · cases d21
      · exact core3_norm a1 b1 a2 b2 a3 b3 c21 c31 d31 c32 d32 o2 (fun i j => by simpa using H0 i j)
      · cases c21
        · refine core3_norm a1 b1 b2 a2 a3 b3 true c31 d31 c32 d32 o2 (fun i j => ?_)
          have h1 := H0 i j
          dsimp only at h1 ⊢
          rw [h1]
          have hg2eq : ((P a2 i j || false && (P a1 i j && P b1 i j)) &&
              (P b2 i j || true && (P a1 i j && P b1 i j))) =
              ((P b2 i j || true && (P a1 i j && P b1 i j)) && P a2 i j) := by
            cases P a2 i j <;> cases P b2 i j <;> cases (P a1 i j && P b1 i j) <;> rfl
          rw [hg2eq]
          simp only [Bool.false_and, Bool.false_or, Bool.true_and]
        · cases o2
          · refine core3_norm a1 b1 a2 b2 a3 b3 false (c31 || c32) (d31 || d32) c32 d32 false (fun i j => ?_)
            have h1 := H0 i j
            dsimp only at h1 ⊢
            rw [h1]
            have hstep : ∀ g1 a2' b2' a3' b3' c31' d31' c32' d32' : Bool,
                (false && ((a2' || true && g1) && (b2' || true && g1)) ||
                  (a3' || c31' && g1 || c32' && ((a2' || true && g1) && (b2' || true && g1))) &&
                  (b3' || d31' && g1 || d32' && ((a2' || true && g1) && (b2' || true && g1)))) =
                (false && ((a2' || false && g1) && b2') ||
                  (a3' || (c31' || c32') && g1 || c32' && ((a2' || false && g1) && b2')) &&
                  (b3' || (d31' || d32') && g1 || d32' && ((a2' || false && g1) && b2'))) := by
              decide
            exact hstep _ _ _ _ _ _ _ _ _
          · refine not_le_adj_g1 a1 b1 a2 b2 a3 b3 true true c31 d31 c32 d32 false true true H0
              (fun i j hg1 => ?_)
            have h1 := H0 i j
            dsimp only at h1
            rw [h1, hg1]
            simp
  · refine not_le_adj_g1 a1 b1 a2 b2 a3 b3 c21 d21 c31 d31 c32 d32 true o2 o3 H0
      (fun i j hg1 => ?_)
    have h1 := H0 i j
    dsimp only at h1
    rw [h1, hg1]
    simp

def cl (G : List ((Fin 6 → Bool) → Bool)) (w : (Fin 6 → Bool) → Bool) : Prop :=
  ∃ h, hom h ∧ ∃ G' : List ((Fin 6 → Bool) → Bool),
    (∀ g ∈ G', g ∈ G) ∧ ∀ x, w x = (h x || G'.any (fun g => g x))

def good : List ((Fin 6 → Bool) → Bool) → Prop
  | [] => True
  | g :: G => (∃ u v, cl G u ∧ cl G v ∧ ∀ x, g x = (u x && v x)) ∧ good G

theorem hom_false : hom (fun _ => false) := fun _ _ => rfl

theorem hom_true : hom (fun _ => true) := fun _ _ => rfl

theorem cl_of_hom {G : List ((Fin 6 → Bool) → Bool)} {h : (Fin 6 → Bool) → Bool}
    (hh : hom h) : cl G h :=
  ⟨h, hh, [], by simp, by simp⟩

theorem cl_congr {G : List ((Fin 6 → Bool) → Bool)} {u w : (Fin 6 → Bool) → Bool}
    (hu : cl G u) (e : ∀ x, w x = u x) : cl G w := by
  obtain ⟨h, hh, G', hs, he⟩ := hu
  exact ⟨h, hh, G', hs, fun x => by rw [e x, he x]⟩

theorem cl_mono {G : List ((Fin 6 → Bool) → Bool)} {w : (Fin 6 → Bool) → Bool}
    (g : (Fin 6 → Bool) → Bool) (hw : cl G w) : cl (g :: G) w := by
  obtain ⟨h, hh, G', hs, he⟩ := hw
  exact ⟨h, hh, G', fun g' hg' => List.mem_cons_of_mem _ (hs g' hg'), he⟩

theorem cl_or {G : List ((Fin 6 → Bool) → Bool)} {u v : (Fin 6 → Bool) → Bool}
    (hu : cl G u) (hv : cl G v) : cl G (fun x => u x || v x) := by
  obtain ⟨h, hh, G1, hs, he⟩ := hu
  obtain ⟨k, hk, G2, hs2, he2⟩ := hv
  refine ⟨fun x => h x || k x, ?_, G1 ++ G2, ?_, ?_⟩
  · intro x y
    show (h _ || k _) = ((h x || k x) || (h y || k y))
    rw [hh x y, hk x y]
    cases h x <;> cases h y <;> cases k x <;> cases k y <;> rfl
  · intro g hg
    rcases List.mem_append.mp hg with h1 | h1
    · exact hs g h1
    · exact hs2 g h1
  · intro x
    show (u x || v x) = ((h x || k x) || (G1 ++ G2).any fun g => g x)
    rw [he x, he2 x, List.any_append]
    cases h x <;> cases k x <;> cases (G1.any fun g => g x) <;> cases (G2.any fun g => g x) <;> rfl

theorem cl_new (G : List ((Fin 6 → Bool) → Bool)) (g : (Fin 6 → Bool) → Bool) :
    cl (g :: G) g :=
  ⟨fun _ => false, hom_false, [g], by simp, by simp⟩

theorem gate_or (G : List ((Fin 6 → Bool) → Bool)) (f : ℕ → (Fin 6 → Bool) → Bool)
    (hw : ∀ k, cl G (f k)) (ins : List ℕ) (hl : ins.length ≤ 2) :
    cl G (fun x => GateOp.eval GateOp.or (ins.map fun i => f i x)) := by
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, t⟩⟩⟩
  · exact cl_congr (cl_of_hom hom_false) (fun x => by simp [GateOp.eval])
  · exact cl_congr (hw i) (fun x => by simp [GateOp.eval])
  · exact cl_congr (cl_or (hw i) (hw j)) (fun x => by simp [GateOp.eval])
  · exact absurd hl (by simp only [List.length_cons]; omega)

theorem gate_and (G : List ((Fin 6 → Bool) → Bool)) (f : ℕ → (Fin 6 → Bool) → Bool)
    (hw : ∀ k, cl G (f k)) (ins : List ℕ) (hl : ins.length ≤ 2) :
    ∃ u v, cl G u ∧ cl G v ∧
      ∀ x, GateOp.eval GateOp.and (ins.map fun i => f i x) = (u x && v x) := by
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, t⟩⟩⟩
  · exact ⟨fun _ => true, fun _ => true, cl_of_hom hom_true, cl_of_hom hom_true,
      fun x => by simp [GateOp.eval]⟩
  · exact ⟨f i, f i, hw i, hw i, fun x => by simp [GateOp.eval]⟩
  · exact ⟨f i, f j, hw i, hw j, fun x => by simp [GateOp.eval]⟩
  · exact absurd hl (by simp only [List.length_cons]; omega)

def W (gs : List Gate) (x : Fin 6 → Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)

def wf (gs : List Gate) (k : ℕ) : (Fin 6 → Bool) → Bool :=
  fun x => (W gs x).getD k false

theorem fold_len (gs : List Gate) : ∀ w0 : List Bool,
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w0).length
      = w0.length + gs.length := by
  induction gs with
  | nil => intro w0; simp
  | cons g gs ih => intro w0; rw [List.foldl_cons, ih]; simp; omega

theorem W_len (gs : List Gate) (x : Fin 6 → Bool) :
    (W gs x).length = 6 + gs.length := by
  unfold W
  rw [fold_len]
  simp

theorem W_snoc (gs : List Gate) (g : Gate) (x : Fin 6 → Bool) :
    W (gs ++ [g]) x
      = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

theorem wf_snoc (gs : List Gate) (g : Gate) (k : ℕ) :
    wf (gs ++ [g]) k = if k = 6 + gs.length then
      (fun x => g.op.eval (g.inputs.map fun i => wf gs i x)) else wf gs k := by
  funext x
  have hl := W_len gs x
  by_cases hk : k = 6 + gs.length
  · simp only [hk, ↓reduceIte]
    show (W (gs ++ [g]) x).getD (6 + gs.length) false =
      g.op.eval (g.inputs.map fun i => (W gs x).getD i false)
    rw [W_snoc]
    simp [List.getD_eq_getElem?_getD, hl]
  · simp only [hk, ↓reduceIte]
    show (W (gs ++ [g]) x).getD k false = (W gs x).getD k false
    rw [W_snoc]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append, hl]
    split
    · rfl
    · rename_i h2
      have h3 : ¬ (k - (6 + gs.length) = 0) := by omega
      simp [h3, hl, h2]

theorem base_hom (k : ℕ) : hom (wf [] k) := by
  intro x y
  unfold wf W
  simp only [List.foldl_nil, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases hk : k < 6
  · simp [hk]
  · simp [hk]

theorem inv (A : Finset ℕ) (gs : List Gate)
    (hm : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hA : ∀ (j : ℕ) (g : Gate), gs[j]? = some g → g.op = GateOp.and → j ∈ A) :
    ∃ G, good G ∧ G.length ≤ (A.filter (fun j => j < gs.length)).card ∧
      ∀ k, cl G (wf gs k) := by
  induction gs using List.reverseRecOn with
  | nil => exact ⟨[], trivial, by simp, fun k => cl_of_hom (base_hom k)⟩
  | append_singleton gs g ih =>
    obtain ⟨G, hG, hlen, hw⟩ := ih (fun g' hg' => hm g' (by simp [hg']))
      (fun j g' hj ho => hA j g' (by
        have hjl : j < gs.length := (List.getElem?_eq_some_iff.mp hj).1
        rw [List.getElem?_append_left hjl]; exact hj) ho)
    obtain ⟨hop, hl⟩ := hm g (by simp)
    rcases hop with hop | hop
    · obtain ⟨u, v, hu, hv, he⟩ := gate_and G (wf gs) hw g.inputs hl
      have hmem : gs.length ∈ A := hA gs.length g (by simp) hop
      refine ⟨(fun x => GateOp.eval GateOp.and (g.inputs.map fun i => wf gs i x)) :: G,
        ⟨⟨u, v, hu, hv, he⟩, hG⟩, ?_, ?_⟩
      · have hsub : insert gs.length (A.filter (fun j => j < gs.length))
            ⊆ A.filter (fun j => j < (gs ++ [g]).length) := by
          intro j hj
          simp only [Finset.mem_insert, Finset.mem_filter, List.length_append, List.length_cons,
            List.length_nil] at hj ⊢
          rcases hj with rfl | ⟨h1, h2⟩
          · exact ⟨hmem, by omega⟩
          · exact ⟨h1, by omega⟩
        have hc := Finset.card_le_card hsub
        rw [Finset.card_insert_of_notMem (by simp)] at hc
        simp only [List.length_cons]
        omega
      · intro k
        rw [wf_snoc, hop]
        by_cases hk : k = 6 + gs.length
        · simp only [hk, ↓reduceIte]; exact cl_new _ _
        · simp only [hk, ↓reduceIte]; exact cl_mono _ (hw k)
    · refine ⟨G, hG, ?_, ?_⟩
      · refine le_trans hlen (Finset.card_le_card ?_)
        intro j hj
        simp only [Finset.mem_filter, List.length_append, List.length_cons, List.length_nil] at hj ⊢
        exact ⟨hj.1, by omega⟩
      · intro k
        rw [wf_snoc, hop]
        by_cases hk : k = 6 + gs.length
        · simp only [hk, ↓reduceIte]; exact gate_or G (wf gs) hw g.inputs hl
        · simp only [hk, ↓reduceIte]; exact hw k

theorem any3 (g1 g2 g3 : (Fin 6 → Bool) → Bool) (G' : List ((Fin 6 → Bool) → Bool)) :
    (∀ g ∈ G', g = g3 ∨ g = g2 ∨ g = g1) →
    ∃ c1 c2 c3 : Bool, ∀ x, G'.any (fun g => g x) = (c1 && g1 x || c2 && g2 x || c3 && g3 x) := by
  induction G' with
  | nil => intro _; exact ⟨false, false, false, fun _ => rfl⟩
  | cons g G' ih =>
    intro hs
    obtain ⟨c1, c2, c3, hc⟩ := ih (fun g' hg' => hs g' (List.mem_cons_of_mem _ hg'))
    rcases hs g List.mem_cons_self with hg | hg | hg
    · refine ⟨c1, c2, true, fun x => ?_⟩
      rw [List.any_cons, hc x, hg]
      cases c1 <;> cases c2 <;> cases c3 <;> cases (g1 x) <;> cases (g2 x) <;> cases (g3 x) <;> rfl
    · refine ⟨c1, true, c3, fun x => ?_⟩
      rw [List.any_cons, hc x, hg]
      cases c1 <;> cases c2 <;> cases c3 <;> cases (g1 x) <;> cases (g2 x) <;> cases (g3 x) <;> rfl
    · refine ⟨true, c2, c3, fun x => ?_⟩
      rw [List.any_cons, hc x, hg]
      cases c1 <;> cases c2 <;> cases c3 <;> cases (g1 x) <;> cases (g2 x) <;> cases (g3 x) <;> rfl

theorem cl_nil {a : (Fin 6 → Bool) → Bool} (ha : cl [] a) : hom a := by
  obtain ⟨h, hh, G', hs, he⟩ := ha
  have hG : G' = [] := List.eq_nil_iff_forall_not_mem.mpr (fun g hg => by simpa using hs g hg)
  subst hG
  have he' : ∀ x, a x = h x := fun x => by simpa using he x
  intro x y
  rw [he', he', he']
  exact hh x y

theorem cl_one {g1 u : (Fin 6 → Bool) → Bool} (hu : cl [g1] u) :
    ∃ h, hom h ∧ ∃ c : Bool, ∀ x, u x = (h x || (c && g1 x)) := by
  obtain ⟨h, hh, G', hs, he⟩ := hu
  obtain ⟨c1, c2, c3, hc⟩ := any3 g1 g1 g1 G' (fun g hg => by simpa using hs g hg)
  refine ⟨h, hh, c1 || c2 || c3, fun x => ?_⟩
  rw [he x, hc x]
  cases c1 <;> cases c2 <;> cases c3 <;> cases (g1 x) <;> cases (h x) <;> rfl

theorem cl_two {g1 g2 w : (Fin 6 → Bool) → Bool} (hw : cl [g2, g1] w) :
    ∃ h, hom h ∧ ∃ c1 c2 : Bool, ∀ x, w x = (h x || c1 && g1 x || c2 && g2 x) := by
  obtain ⟨h, hh, G', hs, he⟩ := hw
  obtain ⟨c1, c2, c3, hc⟩ := any3 g1 g2 g2 G' (fun g hg => by
    have hm := hs g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr rfl))
  refine ⟨h, hh, c1, c2 || c3, fun x => ?_⟩
  rw [he x, hc x]
  cases c1 <;> cases c2 <;> cases c3 <;> cases (g1 x) <;> cases (g2 x) <;> cases (h x) <;> rfl

theorem cl_three {g1 g2 g3 w : (Fin 6 → Bool) → Bool} (hw : cl [g3, g2, g1] w) :
    ∃ h, hom h ∧ ∃ o1 o2 o3 : Bool, ∀ x, w x = (h x || (o1 && g1 x || o2 && g2 x || o3 && g3 x)) := by
  obtain ⟨h, hh, G', hs, he⟩ := hw
  obtain ⟨o1, o2, o3, hc⟩ := any3 g1 g2 g3 G' (fun g hg => by
    have hm := hs g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    exact hm)
  exact ⟨h, hh, o1, o2, o3, fun x => by rw [he x, hc x]⟩

theorem pad {G : List ((Fin 6 → Bool) → Bool)} (hG : good G) :
    good ((fun _ => false) :: G) :=
  ⟨⟨fun _ => false, fun _ => false, cl_of_hom hom_false, cl_of_hom hom_false,
    fun _ => rfl⟩, hG⟩

theorem three_contra (g1 g2 g3 w : (Fin 6 → Bool) → Bool) (hG : good [g3, g2, g1])
    (hw : cl [g3, g2, g1] w) (hadj : ∀ i j, w (pair i j) = adj i j) : False := by
  obtain ⟨⟨u3, v3, hu3, hv3, eg3⟩, ⟨u2, v2, hu2, hv2, eg2⟩, ⟨a1, b1, ha1, hb1, eg1⟩, -⟩ := hG
  have ha1' := cl_nil ha1
  have hb1' := cl_nil hb1
  obtain ⟨a2, ha2, c21, eu2⟩ := cl_one hu2
  obtain ⟨b2, hb2, d21, ev2⟩ := cl_one hv2
  obtain ⟨a3, ha3, c31, c32, eu3⟩ := cl_two hu3
  obtain ⟨b3, hb3, d31, d32, ev3⟩ := cl_two hv3
  obtain ⟨h, hh, o1, o2, o3, ew⟩ := cl_three hw
  refine core3 (fun i => h (e i)) (fun i => a1 (e i)) (fun i => b1 (e i))
    (fun i => a2 (e i)) (fun i => b2 (e i)) (fun i => a3 (e i)) (fun i => b3 (e i))
    c21 d21 c31 d31 c32 d32 o1 o2 o3 (fun i j => ?_)
  dsimp only
  rw [← hadj i j, ew, eg3, eu3, ev3, eg2, eu2, ev2, eg1,
    hom_pair hh, hom_pair ha1', hom_pair hb1', hom_pair ha2, hom_pair hb2, hom_pair ha3, hom_pair hb3]

theorem final_contra (G : List ((Fin 6 → Bool) → Bool)) (hG : good G)
    (hlen : G.length ≤ 3) (w : (Fin 6 → Bool) → Bool) (hw : cl G w)
    (hadj : ∀ i j, w (pair i j) = adj i j) : False := by
  rcases G with _ | ⟨g3, _ | ⟨g2, _ | ⟨g1, _ | ⟨g0, t⟩⟩⟩⟩
  · exact three_contra _ _ _ w (pad (pad (pad hG))) (cl_mono _ (cl_mono _ (cl_mono _ hw))) hadj
  · exact three_contra _ _ _ w (pad (pad hG)) (cl_mono _ (cl_mono _ hw)) hadj
  · exact three_contra _ _ _ w (pad hG) (cl_mono _ hw) hadj
  · exact three_contra _ _ _ w hG hw hadj
  · exact absurd hlen (by simp only [List.length_cons]; omega)

end PEqualNP.Outside.L_meta_282_aux

theorem PEqualNP.Outside.L_meta_282 :
    ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, (PEqualNP.MetaComplexity.Monotone2 C ∧ (∃ A : Finset ℕ, A.card ≤ 3 ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A)) ∧ (∀ x : Fin 6 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5), (2, 3)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  rintro ⟨C, ⟨hmono, A, hAc, hA⟩, hC⟩
  obtain ⟨G, hG, hlen, hw⟩ := PEqualNP.Outside.L_meta_282_aux.inv A C.gates
    (fun g hg => ⟨by have h1 := (hmono g hg).1; simpa using h1, (hmono g hg).2⟩) hA
  have hlen3 : G.length ≤ 3 :=
    le_trans hlen (le_trans (Finset.card_le_card (Finset.filter_subset _ _)) hAc)
  refine PEqualNP.Outside.L_meta_282_aux.final_contra G hG hlen3
    (PEqualNP.Outside.L_meta_282_aux.wf C.gates C.output) (hw C.output) (fun i j => ?_)
  exact Bool.eq_iff_iff.mpr ((hC (PEqualNP.Outside.L_meta_282_aux.pair i j)).trans
    (PEqualNP.Outside.L_meta_282_aux.edge_iff i j))
