import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside

private lemma pairs_cover (a : ℕ) : ∀ (k : ℕ) (c : ℕ → Bool),
    (∀ i < k, c (a + 2 * i) = true ∨ c (a + 2 * i + 1) = true) →
    k ≤ ((Finset.Ico a (a + 2 * k)).filter (fun j => c j = true)).card
  | 0, _, _ => Nat.zero_le _
  | k + 1, c, h => by
    have ih := pairs_cover a k c (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have hpair := h k (Nat.lt_succ_self k)
    have hsub : (Finset.Ico a (a + 2 * k)).filter (fun j => c j = true) ⊆
        (Finset.Ico a (a + 2 * (k + 1))).filter (fun j => c j = true) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_Ico] at hx ⊢
      exact ⟨⟨hx.1.1, by omega⟩, hx.2⟩
    rcases hpair with h1 | h2
    · have hmem : a + 2 * k ∈ (Finset.Ico a (a + 2 * (k + 1))).filter (fun j => c j = true) := by
        simp only [Finset.mem_filter, Finset.mem_Ico]
        exact ⟨⟨by omega, by omega⟩, h1⟩
      have hnot : a + 2 * k ∉ (Finset.Ico a (a + 2 * k)).filter (fun j => c j = true) := by
        simp only [Finset.mem_filter, Finset.mem_Ico]
        omega
      have hssub : (Finset.Ico a (a + 2 * k)).filter (fun j => c j = true) ⊂
          (Finset.Ico a (a + 2 * (k + 1))).filter (fun j => c j = true) :=
        Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq => hnot (heq ▸ hmem)⟩
      have hlt := Finset.card_lt_card hssub
      omega
    · have hmem : a + 2 * k + 1 ∈ (Finset.Ico a (a + 2 * (k + 1))).filter (fun j => c j = true) := by
        simp only [Finset.mem_filter, Finset.mem_Ico]
        exact ⟨⟨by omega, by omega⟩, h2⟩
      have hnot : a + 2 * k + 1 ∉ (Finset.Ico a (a + 2 * k)).filter (fun j => c j = true) := by
        simp only [Finset.mem_filter, Finset.mem_Ico]
        omega
      have hssub : (Finset.Ico a (a + 2 * k)).filter (fun j => c j = true) ⊂
          (Finset.Ico a (a + 2 * (k + 1))).filter (fun j => c j = true) :=
        Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq => hnot (heq ▸ hmem)⟩
      have hlt := Finset.card_lt_card hssub
      omega

theorem L_meta_301 :
    ∀ (k : ℕ) (c : ℕ → Bool), (∀ j : ℕ, j ≤ 2 * k → c j = true ∨ c (j + 1) = true) → k + (if c 0 = false ∧ c (2 * k + 1) = false then 1 else 0) ≤ ((Finset.Icc 1 (2 * k)).filter (fun j => c j = true)).card := by
  intro k c h
  split_ifs with hboth
  · rcases hboth with ⟨h0, hend⟩
    cases k with
    | zero =>
      have h01 := h 0 (by omega)
      simp [h0, hend] at h01
    | succ k' =>
      have hc1 : c 1 = true := by
        have h01 := h 0 (by omega)
        simp [h0] at h01
        exact h01
      have hclast : c (2 * k' + 2) = true := by
        have hlast := h (2 * k' + 2) (by omega)
        simp [show 2 * (k' + 1) + 1 = 2 * k' + 2 + 1 by omega] at hend
        simp [hend] at hlast
        exact hlast
      have hmid : k' ≤ ((Finset.Ico 2 (2 + 2 * k')).filter (fun j => c j = true)).card :=
        pairs_cover 2 k' c (fun i hi => h (2 + 2 * i) (by omega))
      let M := (Finset.Ico 2 (2 + 2 * k')).filter (fun j => c j = true)
      let E : Finset ℕ := {1, 2 * k' + 2}
      have hdisj : Disjoint M E := by
        rw [Finset.disjoint_left]
        intro x hxM hxE
        simp only [M, Finset.mem_filter, Finset.mem_Ico] at hxM
        simp only [E, Finset.mem_insert, Finset.mem_singleton] at hxE
        omega
      have hsub : M ∪ E ⊆ (Finset.Icc 1 (2 * (k' + 1))).filter (fun j => c j = true) := by
        intro x hx
        simp only [Finset.mem_union, M, E, Finset.mem_filter, Finset.mem_Ico,
          Finset.mem_insert, Finset.mem_singleton] at hx
        simp only [Finset.mem_filter, Finset.mem_Icc]
        rcases hx with ⟨⟨h1, h2⟩, hc⟩ | rfl | rfl
        · exact ⟨⟨by omega, by omega⟩, hc⟩
        · exact ⟨⟨by omega, by omega⟩, hc1⟩
        · exact ⟨⟨by omega, by omega⟩, hclast⟩
      have hcardE : E.card = 2 := by
        refine Finset.card_pair ?_
        omega
      have hle := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hdisj, hcardE] at hle
      dsimp only [M] at hle
      omega
  · have hbase : k ≤ ((Finset.Ico 1 (1 + 2 * k)).filter (fun j => c j = true)).card :=
      pairs_cover 1 k c (fun i hi => h (1 + 2 * i) (by omega))
    have heq : Finset.Ico 1 (1 + 2 * k) = Finset.Icc 1 (2 * k) := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_Icc]
      omega
    rw [heq] at hbase
    omega

end PEqualNP.Outside
