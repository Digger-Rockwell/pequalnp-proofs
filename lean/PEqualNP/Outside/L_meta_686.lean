import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_686_aux

lemma main_proof (m n r : ℕ) (S : Fin m → Finset (Fin n))
    (hcov : ∀ x y : Fin n, x ≠ y → ∃ i : Fin m, x ∈ S i ∧ y ∈ S i)
    (hreg : ∀ x : Fin n, (Finset.univ.filter (fun i : Fin m => x ∈ S i)).card = r)
    (B : Finset (Fin n)) :
    (Finset.univ.filter (fun i : Fin m => ∃ x ∈ B, x ∈ S i)).card + B.card ≤ B.card * r + 1 := by
  by_cases hB : B = ∅
  · subst hB
    simp
  · obtain ⟨x0, hx0⟩ := Finset.nonempty_iff_ne_empty.mpr hB
    set F : Fin n → Finset (Fin m) := fun x => Finset.univ.filter (fun i : Fin m => x ∈ S i)
    have hsub : Finset.univ.filter (fun i : Fin m => ∃ x ∈ B, x ∈ S i) ⊆
        F x0 ∪ (B.erase x0).biUnion (fun x => F x \ F x0) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      obtain ⟨x, hxB, hxi⟩ := hi
      by_cases hix0 : i ∈ F x0
      · exact Finset.mem_union_left _ hix0
      · apply Finset.mem_union_right
        refine Finset.mem_biUnion.mpr ⟨x, Finset.mem_erase.mpr ⟨?_, hxB⟩, ?_⟩
        · rintro rfl
          exact hix0 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxi⟩)
        · exact Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxi⟩, hix0⟩
    have hdiff : ∀ x ∈ B.erase x0, (F x \ F x0).card + 1 ≤ r := by
      intro x hx
      have hne : x ≠ x0 := (Finset.mem_erase.mp hx).1
      obtain ⟨i, hxi, hx0i⟩ := hcov x x0 hne
      have hi_fx : i ∈ F x := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxi⟩
      have hi_fx0 : i ∈ F x0 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx0i⟩
      have hsub' : F x \ F x0 ⊆ (F x).erase i := by
        intro j hj
        rw [Finset.mem_sdiff] at hj
        exact Finset.mem_erase.mpr ⟨fun h => hj.2 (h ▸ hi_fx0), hj.1⟩
      have hle := Finset.card_le_card hsub'
      have her := Finset.card_erase_add_one hi_fx
      rw [hreg x] at her
      omega
    have hcard1 : (Finset.univ.filter (fun i : Fin m => ∃ x ∈ B, x ∈ S i)).card ≤
        (F x0).card + ((B.erase x0).biUnion (fun x => F x \ F x0)).card :=
      le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
    have hcard2 : ((B.erase x0).biUnion (fun x => F x \ F x0)).card ≤
        ∑ x ∈ B.erase x0, (F x \ F x0).card := Finset.card_biUnion_le
    have hsum : (∑ x ∈ B.erase x0, (F x \ F x0).card) + (B.erase x0).card ≤
        (B.erase x0).card * r := by
      calc (∑ x ∈ B.erase x0, (F x \ F x0).card) + (B.erase x0).card
          = ∑ x ∈ B.erase x0, ((F x \ F x0).card + 1) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
        _ ≤ ∑ _x ∈ B.erase x0, r := Finset.sum_le_sum hdiff
        _ = (B.erase x0).card * r := by rw [Finset.sum_const, smul_eq_mul]
    have hBe : (B.erase x0).card + 1 = B.card := Finset.card_erase_add_one hx0
    have hfx0 : (F x0).card = r := hreg x0
    have hmul : B.card * r = (B.erase x0).card * r + r := by
      rw [← hBe, add_mul, one_mul]
    omega

end PEqualNP.Outside.L_meta_686_aux

theorem PEqualNP.Outside.L_meta_686 : ∀ (m n r : ℕ) (S : Fin m → Finset (Fin n)),
    (∀ x y : Fin n, x ≠ y → ∃ i : Fin m, x ∈ S i ∧ y ∈ S i) →
    (∀ x : Fin n, (Finset.univ.filter (fun i : Fin m => x ∈ S i)).card = r) →
    ∀ B : Finset (Fin n),
      (Finset.univ.filter (fun i : Fin m => ∃ x ∈ B, x ∈ S i)).card + B.card ≤ B.card * r + 1 :=
  PEqualNP.Outside.L_meta_686_aux.main_proof
