import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_706_aux

open PEqualNP.AndCount

def skip {s : ℕ} (i : Fin s) (k : Fin (s - 1)) : Fin s :=
  if h : k.val < i.val then ⟨k.val, lt_trans h i.isLt⟩ else ⟨k.val + 1, by omega⟩

lemma skip_ne {s : ℕ} (i : Fin s) (k : Fin (s - 1)) : skip i k ≠ i := by
  unfold skip
  split_ifs with h
  · intro heq
    have := congrArg Fin.val heq
    simp at this
    omega
  · intro heq
    have := congrArg Fin.val heq
    simp at this
    omega

lemma skip_lt_iff {s : ℕ} (i : Fin s) (k₁ k₂ : Fin (s - 1)) :
    skip i k₁ < skip i k₂ ↔ k₁ < k₂ := by
  unfold skip
  simp only [Fin.lt_def]
  split_ifs <;> simp <;> omega

lemma exists_skip_of_ne {s : ℕ} (i j : Fin s) (hj : j ≠ i) :
    ∃ k : Fin (s - 1), skip i k = j := by
  have hval : j.val ≠ i.val := fun h => hj (Fin.ext h)
  by_cases h : j.val < i.val
  · refine ⟨⟨j.val, by omega⟩, ?_⟩
    apply Fin.ext
    simp [skip, h]
  · refine ⟨⟨j.val - 1, by omega⟩, ?_⟩
    apply Fin.ext
    have hnot : ¬ j.val - 1 < i.val := by omega
    simp [skip, hnot]
    omega

def substVars {n s : ℕ} (i : Fin s) (B : Finset (Fin n)) (V : Finset (Fin n))
    (G : Finset (Fin s)) : Finset (Fin n) :=
  if i ∈ G then V ∪ B else V

def substGates {s : ℕ} (i : Fin s) (F : Finset (Fin s)) (G : Finset (Fin s)) :
    Finset (Fin (s - 1)) :=
  Finset.univ.filter (fun k => skip i k ∈ G ∨ (i ∈ G ∧ skip i k ∈ F))

def removeGate {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size)
    (B : Finset (Fin n)) (F : Finset (Fin C.size)) : AndCountCircuit n where
  size := C.size - 1
  leftVars k := substVars i B (C.leftVars (skip i k)) (C.leftGates (skip i k))
  leftGates k := substGates i F (C.leftGates (skip i k))
  rightVars k := substVars i B (C.rightVars (skip i k)) (C.rightGates (skip i k))
  rightGates k := substGates i F (C.rightGates (skip i k))
  outVars := substVars i B C.outVars C.outGates
  outGates := substGates i F C.outGates

lemma substGates_lt {s : ℕ} (i : Fin s) (F G : Finset (Fin s)) (k : Fin (s - 1))
    (hF : ∀ j ∈ F, j < i) (hG : ∀ j ∈ G, j < skip i k) :
    ∀ k' ∈ substGates i F G, k' < k := by
  intro k' hk'
  simp only [substGates, Finset.mem_filter, Finset.mem_univ, true_and] at hk'
  rw [← skip_lt_iff i]
  rcases hk' with h1 | ⟨hiG, h2⟩
  · exact hG _ h1
  · exact lt_trans (hF _ h2) (hG _ hiG)

lemma removeGate_wellFormed {n : ℕ} (C : AndCountCircuit n) (hWF : C.WellFormed)
    (i : Fin C.size) (B : Finset (Fin n)) (F : Finset (Fin C.size))
    (hF : ∀ j ∈ F, j < i) :
    (removeGate C i B F).WellFormed := by
  intro k
  constructor
  · exact substGates_lt i F (C.leftGates (skip i k)) k hF (hWF (skip i k)).1
  · exact substGates_lt i F (C.rightGates (skip i k)) k hF (hWF (skip i k)).2

lemma sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (val₁ val₂ : Fin k → Bool) (h : ∀ j < i, val₁ j = val₂ j) :
    AndCountCircuit.sideTrue U B F i val₁ = AndCountCircuit.sideTrue U B F i val₂ := by
  unfold AndCountCircuit.sideTrue
  apply decide_eq_decide.mpr
  constructor
  · rintro (hv | ⟨j, hjF, hji, hval⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hjF, hji, by rw [← h j hji]; exact hval⟩
  · rintro (hv | ⟨j, hjF, hji, hval⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hjF, hji, by rw [h j hji]; exact hval⟩

lemma gateValFuel_stable {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (m : ℕ) (j : Fin C.size), j.val ≤ m → ∀ d, j.val < d →
      C.gateValFuel U d j = C.gateValFuel U (j.val + 1) j := by
  intro m
  induction m with
  | zero =>
    intro j hj d hd
    have hj0 : j.val = 0 := Nat.le_zero.mp hj
    obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
    simp only [AndCountCircuit.gateValFuel, hj0]
    congr 1
    · apply sideTrue_congr
      intro x hx
      exfalso
      have : x.val < j.val := hx
      omega
    · apply sideTrue_congr
      intro x hx
      exfalso
      have : x.val < j.val := hx
      omega
  | succ m ih =>
    intro j hj d hd
    obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
    simp only [AndCountCircuit.gateValFuel]
    have hprev : ∀ x < j, C.gateValFuel U d' x = C.gateValFuel U j.val x := by
      intro x hx
      have hxlt : x.val < j.val := hx
      have hxm : x.val ≤ m := by omega
      rw [ih x hxm d' (by omega), ih x hxm j.val hxlt]
    congr 1
    · exact sideTrue_congr _ _ _ _ _ _ hprev
    · exact sideTrue_congr _ _ _ _ _ _ hprev

lemma gateVal_eq {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (j : Fin C.size) :
    C.gateVal U j =
      (AndCountCircuit.sideTrue U (C.leftVars j) (C.leftGates j) j (C.gateVal U) &&
        AndCountCircuit.sideTrue U (C.rightVars j) (C.rightGates j) j (C.gateVal U)) := by
  unfold AndCountCircuit.gateVal
  rw [gateValFuel_stable C U j.val j le_rfl C.size j.isLt]
  simp only [AndCountCircuit.gateValFuel]
  have hprev : ∀ x < j, C.gateValFuel U j.val x = C.gateValFuel U C.size x := by
    intro x hx
    have hxlt : x.val < j.val := hx
    rw [gateValFuel_stable C U x.val x le_rfl j.val hxlt,
      gateValFuel_stable C U x.val x le_rfl C.size x.isLt]
  congr 1
  · exact sideTrue_congr _ _ _ _ _ _ hprev
  · exact sideTrue_congr _ _ _ _ _ _ hprev

lemma subst_iff {n s : ℕ} (U B V : Finset (Fin n)) (i : Fin s) (F G : Finset (Fin s))
    (P : Fin s → Prop) (Q : Fin (s - 1) → Prop)
    (hF : ∀ j ∈ F, j < i)
    (hPi : P i ↔ ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, P j))
    (hPQ : ∀ k ∈ substGates i F G, Q k ↔ P (skip i k)) :
    ((∃ v ∈ substVars i B V G, v ∈ U) ∨ ∃ k ∈ substGates i F G, Q k) ↔
      ((∃ v ∈ V, v ∈ U) ∨ ∃ j ∈ G, P j) := by
  constructor
  · rintro (⟨v, hv, hvU⟩ | ⟨k, hk, hQk⟩)
    · unfold substVars at hv
      split_ifs at hv with hiG
      · rcases Finset.mem_union.mp hv with hvV | hvB
        · exact Or.inl ⟨v, hvV, hvU⟩
        · exact Or.inr ⟨i, hiG, hPi.mpr (Or.inl ⟨v, hvB, hvU⟩)⟩
      · exact Or.inl ⟨v, hv, hvU⟩
    · have hPk : P (skip i k) := (hPQ k hk).mp hQk
      simp only [substGates, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      rcases hk with h1 | ⟨hiG, h2⟩
      · exact Or.inr ⟨skip i k, h1, hPk⟩
      · exact Or.inr ⟨i, hiG, hPi.mpr (Or.inr ⟨skip i k, h2, hPk⟩)⟩
  · rintro (⟨v, hvV, hvU⟩ | ⟨j, hjG, hPj⟩)
    · left
      refine ⟨v, ?_, hvU⟩
      unfold substVars
      split_ifs
      · exact Finset.mem_union_left B hvV
      · exact hvV
    · by_cases hji : j = i
      · subst hji
        rcases hPi.mp hPj with ⟨v, hvB, hvU⟩ | ⟨j', hj'F, hPj'⟩
        · left
          refine ⟨v, ?_, hvU⟩
          unfold substVars
          split_ifs
          exact Finset.mem_union_right V hvB
        · have hj'ne : j' ≠ j := ne_of_lt (hF j' hj'F)
          obtain ⟨k, hk⟩ := exists_skip_of_ne j j' hj'ne
          have hkmem : k ∈ substGates j F G := by
            simp only [substGates, Finset.mem_filter, Finset.mem_univ, true_and]
            exact Or.inr ⟨hjG, by rwa [hk]⟩
          right
          refine ⟨k, hkmem, (hPQ k hkmem).mpr ?_⟩
          rwa [hk]
      · obtain ⟨k, hk⟩ := exists_skip_of_ne i j hji
        have hkmem : k ∈ substGates i F G := by
          simp only [substGates, Finset.mem_filter, Finset.mem_univ, true_and]
          exact Or.inl (by rwa [hk])
        right
        refine ⟨k, hkmem, (hPQ k hkmem).mpr ?_⟩
        rwa [hk]

lemma sideTrue_subst {n s : ℕ} (U B V : Finset (Fin n)) (i : Fin s) (F G : Finset (Fin s))
    (k : Fin (s - 1)) (valC : Fin s → Bool) (valC' : Fin (s - 1) → Bool)
    (hF : ∀ j ∈ F, j < i)
    (hG : ∀ j ∈ G, j < skip i k)
    (hPi : valC i = true ↔ ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, valC j = true))
    (hIH : ∀ k' < k, valC' k' = valC (skip i k')) :
    AndCountCircuit.sideTrue U (substVars i B V G) (substGates i F G) k valC' =
      AndCountCircuit.sideTrue U V G (skip i k) valC := by
  unfold AndCountCircuit.sideTrue
  apply decide_eq_decide.mpr
  have hlt' : ∀ k' ∈ substGates i F G, k' < k := substGates_lt i F G k hF hG
  have hL :
      ((∃ v ∈ substVars i B V G, v ∈ U) ∨ ∃ k' ∈ substGates i F G, k' < k ∧ valC' k' = true) ↔
        ((∃ v ∈ substVars i B V G, v ∈ U) ∨ ∃ k' ∈ substGates i F G, valC' k' = true) := by
    constructor
    · rintro (h | ⟨k', hk', _, hval⟩)
      · exact Or.inl h
      · exact Or.inr ⟨k', hk', hval⟩
    · rintro (h | ⟨k', hk', hval⟩)
      · exact Or.inl h
      · exact Or.inr ⟨k', hk', hlt' k' hk', hval⟩
  have hR :
      ((∃ v ∈ V, v ∈ U) ∨ ∃ j ∈ G, j < skip i k ∧ valC j = true) ↔
        ((∃ v ∈ V, v ∈ U) ∨ ∃ j ∈ G, valC j = true) := by
    constructor
    · rintro (h | ⟨j, hj, _, hval⟩)
      · exact Or.inl h
      · exact Or.inr ⟨j, hj, hval⟩
    · rintro (h | ⟨j, hj, hval⟩)
      · exact Or.inl h
      · exact Or.inr ⟨j, hj, hG j hj, hval⟩
  rw [hL, hR]
  exact subst_iff U B V i F G (fun j => valC j = true) (fun k' => valC' k' = true) hF hPi
    (fun k' hk' => by rw [hIH k' (hlt' k' hk')])

lemma removeGate_gateVal {n : ℕ} (C : AndCountCircuit n) (hWF : C.WellFormed)
    (U : Finset (Fin n)) (i : Fin C.size) (B : Finset (Fin n)) (F : Finset (Fin C.size))
    (hF : ∀ j ∈ F, j < i)
    (hU : C.gateVal U i = true ↔ ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, C.gateVal U j = true)) :
    ∀ (m : ℕ) (k : Fin (C.size - 1)), k.val ≤ m →
      (removeGate C i B F).gateVal U k = C.gateVal U (skip i k) := by
  intro m
  induction m with
  | zero =>
    intro k hk
    have hk0 : k.val = 0 := Nat.le_zero.mp hk
    rw [gateVal_eq (removeGate C i B F) U k, gateVal_eq C U (skip i k)]
    have hIH : ∀ k' < k, (removeGate C i B F).gateVal U k' = C.gateVal U (skip i k') := by
      intro k' hk'
      have : k'.val < k.val := hk'
      omega
    congr 1
    · exact sideTrue_subst U B (C.leftVars (skip i k)) i F (C.leftGates (skip i k)) k
        (C.gateVal U) ((removeGate C i B F).gateVal U) hF (hWF (skip i k)).1 hU hIH
    · exact sideTrue_subst U B (C.rightVars (skip i k)) i F (C.rightGates (skip i k)) k
        (C.gateVal U) ((removeGate C i B F).gateVal U) hF (hWF (skip i k)).2 hU hIH
  | succ m ih =>
    intro k hk
    rw [gateVal_eq (removeGate C i B F) U k, gateVal_eq C U (skip i k)]
    have hIH : ∀ k' < k, (removeGate C i B F).gateVal U k' = C.gateVal U (skip i k') := by
      intro k' hk'
      have : k'.val < k.val := hk'
      exact ih k' (by omega)
    congr 1
    · exact sideTrue_subst U B (C.leftVars (skip i k)) i F (C.leftGates (skip i k)) k
        (C.gateVal U) ((removeGate C i B F).gateVal U) hF (hWF (skip i k)).1 hU hIH
    · exact sideTrue_subst U B (C.rightVars (skip i k)) i F (C.rightGates (skip i k)) k
        (C.gateVal U) ((removeGate C i B F).gateVal U) hF (hWF (skip i k)).2 hU hIH

end PEqualNP.Outside.L_meta_706_aux

theorem PEqualNP.Outside.L_meta_706 :
  ∀ (n : ℕ) (C : PEqualNP.AndCount.AndCountCircuit n), C.WellFormed →
    ∀ (D : Set (Finset (Fin n))) (i : Fin C.size) (B : Finset (Fin n)) (F : Finset (Fin C.size)),
      (∀ j ∈ F, j < i) →
      (∀ U ∈ D, C.gateVal U i = true ↔ ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, C.gateVal U j = true)) →
      ∃ C' : PEqualNP.AndCount.AndCountCircuit n, C'.WellFormed ∧ C'.size + 1 ≤ C.size ∧
        ∀ U ∈ D, C'.eval U = C.eval U := by
  intro n C hWF D i B F hF hD
  refine ⟨PEqualNP.Outside.L_meta_706_aux.removeGate C i B F,
    PEqualNP.Outside.L_meta_706_aux.removeGate_wellFormed C hWF i B F hF, ?_, ?_⟩
  · have hi := i.isLt
    change (C.size - 1) + 1 ≤ C.size
    omega
  · intro U hU
    unfold PEqualNP.AndCount.AndCountCircuit.eval
    apply decide_eq_decide.mpr
    exact PEqualNP.Outside.L_meta_706_aux.subst_iff U B C.outVars i F C.outGates
      (fun j => C.gateVal U j = true)
      (fun k => (PEqualNP.Outside.L_meta_706_aux.removeGate C i B F).gateVal U k = true)
      hF (hD U hU)
      (fun k _ => by
        rw [PEqualNP.Outside.L_meta_706_aux.removeGate_gateVal C hWF U i B F hF (hD U hU)
          k.val k le_rfl])
