import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside

private lemma ite_zero_add {P : Prop} [Decidable P] (x y : ℂ) :
    (if P then (0 : ℂ) else x + y) = (if P then 0 else x) + (if P then 0 else y) := by
  split_ifs <;> ring

private lemma sum_ne1 {q : ℕ} (l : Fin q) :
    (∑ j : Fin q, if j = l then (0 : ℂ) else 1) = ((q - 1 : ℕ) : ℂ) := by
  have h : (∑ j : Fin q, if j = l then (0 : ℂ) else 1) =
      ∑ j ∈ Finset.univ.erase l, (1 : ℂ) := by
    have hs : Finset.univ.erase l = Finset.univ.filter (fun j : Fin q => j ≠ l) := by
      ext j
      simp
    rw [hs, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hjl : j = l <;> simp [hjl]
  rw [h, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ l),
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

private lemma sum_ne2 {q : ℕ} {l m : Fin q} (hlm : l ≠ m) :
    (∑ j : Fin q, if j = l ∨ j = m then (0 : ℂ) else 1) = ((q - 2 : ℕ) : ℂ) := by
  have h : (∑ j : Fin q, if j = l ∨ j = m then (0 : ℂ) else 1) =
      ∑ j ∈ (Finset.univ.erase l).erase m, (1 : ℂ) := by
    have hs : (Finset.univ.erase l).erase m =
        Finset.univ.filter (fun j : Fin q => ¬(j = l ∨ j = m)) := by
      ext j
      simp [and_comm]
    rw [hs, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j = l ∨ j = m <;> simp [hj]
  have hm : m ∈ Finset.univ.erase l := Finset.mem_erase.mpr ⟨hlm.symm, Finset.mem_univ m⟩
  rw [h, Finset.sum_const, Finset.card_erase_of_mem hm,
    Finset.card_erase_of_mem (Finset.mem_univ l), Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  rfl

private lemma sum_ne3 {q : ℕ} {l m n : Fin q} (hlm : l ≠ m) (hln : l ≠ n) (hmn : m ≠ n) :
    (∑ j : Fin q, if j = l ∨ j = m ∨ j = n then (0 : ℂ) else 1) = ((q - 3 : ℕ) : ℂ) := by
  have h : (∑ j : Fin q, if j = l ∨ j = m ∨ j = n then (0 : ℂ) else 1) =
      ∑ j ∈ ((Finset.univ.erase l).erase m).erase n, (1 : ℂ) := by
    have hs : ((Finset.univ.erase l).erase m).erase n =
        Finset.univ.filter (fun j : Fin q => ¬(j = l ∨ j = m ∨ j = n)) := by
      ext j
      simp [not_or]
      tauto
    rw [hs, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j = l ∨ j = m ∨ j = n <;> simp [hj]
  have hm : m ∈ Finset.univ.erase l := Finset.mem_erase.mpr ⟨hlm.symm, Finset.mem_univ m⟩
  have hn : n ∈ (Finset.univ.erase l).erase m :=
    Finset.mem_erase.mpr ⟨hmn.symm, Finset.mem_erase.mpr ⟨hln.symm, Finset.mem_univ n⟩⟩
  rw [h, Finset.sum_const, Finset.card_erase_of_mem hn, Finset.card_erase_of_mem hm,
    Finset.card_erase_of_mem (Finset.mem_univ l), Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  rfl

theorem L_gct_202 :
    ∀ (q : ℕ) (t : Fin 4 × Fin q → ℂ) (c : ℂ), 4 ≤ q → (∀ j, t (0, j) = c) → (∑ i : Fin 4, ∑ j, t (i, j)) = 0 ∧ (∑ j, ∑ l, if j = l then 0 else ∑ a : Fin 4, ∑ b : Fin 4, if a < b then t (a, j) * t (b, l) else 0) = 0 ∧ (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, if a < b ∧ b < c then t (a, j) * t (b, l) * t (c, m) else 0) = 0 ∧ (∑ j, ∑ l, ∑ m, ∑ n, if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0 else t (0, j) * t (1, l) * t (2, m) * t (3, n)) = 0 → c = 0 := by
  intro q t c hq ht0 ⟨hS1, hS2, hS3, hS4⟩
  let P1 : ℂ := ∑ l : Fin q, (t (1, l) + t (2, l) + t (3, l))
  let P2 : ℂ := ∑ l : Fin q, ∑ m : Fin q, if l = m then 0 else
    (t (1, l) * t (2, m) + t (1, l) * t (3, m) + t (2, l) * t (3, m))
  let P3 : ℂ := ∑ l : Fin q, ∑ m : Fin q, ∑ n : Fin q,
    if l = m ∨ l = n ∨ m = n then 0 else t (1, l) * t (2, m) * t (3, n)
  have h1 : P1 + (q : ℂ) * c = 0 := by
    have hS1' : (∑ i : Fin 4, ∑ j : Fin q, t (i, j)) = (q : ℂ) * c + P1 := by
      rw [Fin.sum_univ_four]
      simp only [ht0, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, P1,
        Finset.sum_add_distrib]
      ring
    rw [hS1'] at hS1
    linear_combination hS1
  have h2 : P2 + ((q - 1 : ℕ) : ℂ) * c * P1 = 0 := by
    have hinner : ∀ j l : Fin q,
        (∑ a : Fin 4, ∑ b : Fin 4, if a < b then t (a, j) * t (b, l) else 0) =
          c * (t (1, l) + t (2, l) + t (3, l)) +
          (t (1, j) * t (2, l) + t (1, j) * t (3, l) + t (2, j) * t (3, l)) := by
      intro j l
      simp only [Fin.sum_univ_four]
      norm_num
      simp only [ht0]
      ring
    have hS2' : (∑ j : Fin q, ∑ l : Fin q, if j = l then (0 : ℂ) else
        ∑ a : Fin 4, ∑ b : Fin 4, if a < b then t (a, j) * t (b, l) else 0) =
        ((q - 1 : ℕ) : ℂ) * c * P1 + P2 := by
      simp_rw [hinner, ite_zero_add, Finset.sum_add_distrib]
      have hA : (∑ j : Fin q, ∑ l : Fin q, if j = l then (0 : ℂ) else
          c * (t (1, l) + t (2, l) + t (3, l))) = ((q - 1 : ℕ) : ℂ) * c * P1 := by
        rw [Finset.sum_comm]
        simp only [P1, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        have hstep : (∑ j : Fin q, if j = l then (0 : ℂ) else
            c * (t (1, l) + t (2, l) + t (3, l))) =
            (∑ j : Fin q, if j = l then (0 : ℂ) else 1) *
              (c * (t (1, l) + t (2, l) + t (3, l))) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          by_cases hjl : j = l <;> simp [hjl]
        rw [hstep, sum_ne1 l]
        ring
      rw [hA]
      simp only [P2, ite_zero_add, Finset.sum_add_distrib]
    rw [hS2'] at hS2
    linear_combination hS2
  have h3 : P3 + ((q - 2 : ℕ) : ℂ) * c * P2 = 0 := by
    have hinner : ∀ j l m : Fin q,
        (∑ a : Fin 4, ∑ b : Fin 4, ∑ d : Fin 4,
          if a < b ∧ b < d then t (a, j) * t (b, l) * t (d, m) else 0) =
          c * (t (1, l) * t (2, m) + t (1, l) * t (3, m) + t (2, l) * t (3, m)) +
          t (1, j) * t (2, l) * t (3, m) := by
      intro j l m
      simp only [Fin.sum_univ_four]
      norm_num
      simp only [ht0]
      ring
    have hS3' : (∑ j : Fin q, ∑ l : Fin q, ∑ m : Fin q,
        if j = l ∨ j = m ∨ l = m then (0 : ℂ) else
          ∑ a : Fin 4, ∑ b : Fin 4, ∑ d : Fin 4,
            if a < b ∧ b < d then t (a, j) * t (b, l) * t (d, m) else 0) =
        ((q - 2 : ℕ) : ℂ) * c * P2 + P3 := by
      simp_rw [hinner, ite_zero_add, Finset.sum_add_distrib]
      have hA : (∑ j : Fin q, ∑ l : Fin q, ∑ m : Fin q,
          if j = l ∨ j = m ∨ l = m then (0 : ℂ) else
            c * (t (1, l) * t (2, m) + t (1, l) * t (3, m) + t (2, l) * t (3, m))) =
          ((q - 2 : ℕ) : ℂ) * c * P2 := by
        rw [Finset.sum_comm]
        conv_lhs =>
          arg 2; ext l
          rw [Finset.sum_comm]
        simp only [P2, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
        by_cases hlm : l = m
        · simp [hlm]
        · simp only [hlm, ↓reduceIte, or_false]
          have hstep : (∑ j : Fin q, if j = l ∨ j = m then (0 : ℂ) else
              c * (t (1, l) * t (2, m) + t (1, l) * t (3, m) + t (2, l) * t (3, m))) =
              (∑ j : Fin q, if j = l ∨ j = m then (0 : ℂ) else 1) *
                (c * (t (1, l) * t (2, m) + t (1, l) * t (3, m) + t (2, l) * t (3, m))) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun j _ => ?_
            by_cases hj : j = l ∨ j = m <;> simp [hj]
          rw [hstep, sum_ne2 hlm]
          ring
      rw [hA]
    rw [hS3'] at hS3
    linear_combination hS3
  have h4 : ((q - 3 : ℕ) : ℂ) * c * P3 = 0 := by
    have hS4' : (∑ j : Fin q, ∑ l : Fin q, ∑ m : Fin q, ∑ n : Fin q,
        if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then (0 : ℂ) else
          t (0, j) * t (1, l) * t (2, m) * t (3, n)) =
        ((q - 3 : ℕ) : ℂ) * c * P3 := by
      rw [Finset.sum_comm]
      conv_lhs =>
        arg 2; ext l
        rw [Finset.sum_comm]
      conv_lhs =>
        arg 2; ext l; arg 2; ext m
        rw [Finset.sum_comm]
      simp only [P3, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ =>
        Finset.sum_congr rfl fun n _ => ?_
      by_cases hlmn : l = m ∨ l = n ∨ m = n
      · simp only [hlmn, ↓reduceIte, mul_zero]
        refine Finset.sum_eq_zero fun j _ => ?_
        simp
      · simp only [hlmn, ↓reduceIte, or_false]
        have hlm : l ≠ m := fun h => hlmn (Or.inl h)
        have hln : l ≠ n := fun h => hlmn (Or.inr (Or.inl h))
        have hmn : m ≠ n := fun h => hlmn (Or.inr (Or.inr h))
        have hstep : (∑ j : Fin q,
            if j = l ∨ j = m ∨ j = n then (0 : ℂ) else
              t (0, j) * t (1, l) * t (2, m) * t (3, n)) =
            (∑ j : Fin q, if j = l ∨ j = m ∨ j = n then (0 : ℂ) else 1) *
              (c * (t (1, l) * t (2, m) * t (3, n))) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          by_cases hj : j = l ∨ j = m ∨ j = n
          · simp [hj]
          · simp only [hj, ↓reduceIte, one_mul, ht0]
            ring
        rw [hstep, sum_ne3 hlm hln hmn]
        ring
    rw [hS4'] at hS4
    exact hS4
  have hprod : ((q : ℂ) * ((q - 1 : ℕ) : ℂ) * ((q - 2 : ℕ) : ℂ) * ((q - 3 : ℕ) : ℂ)) * c ^ 4 = 0 := by
    have hP1 : P1 = -(q : ℂ) * c := by linear_combination h1
    have hP2 : P2 = (q : ℂ) * ((q - 1 : ℕ) : ℂ) * c ^ 2 := by
      rw [hP1] at h2
      linear_combination h2
    have hP3 : P3 = -(q : ℂ) * ((q - 1 : ℕ) : ℂ) * ((q - 2 : ℕ) : ℂ) * c ^ 3 := by
      rw [hP2] at h3
      linear_combination h3
    rw [hP3] at h4
    linear_combination -h4
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hq1 : ((q - 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hq2 : ((q - 2 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hq3 : ((q - 3 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcoeff : (q : ℂ) * ((q - 1 : ℕ) : ℂ) * ((q - 2 : ℕ) : ℂ) * ((q - 3 : ℕ) : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hq0 hq1) hq2) hq3
  have hc4 : c ^ 4 = 0 := (mul_eq_zero.mp hprod).resolve_left hcoeff
  exact (pow_eq_zero_iff (by norm_num : 4 ≠ 0)).mp hc4

end PEqualNP.Outside
