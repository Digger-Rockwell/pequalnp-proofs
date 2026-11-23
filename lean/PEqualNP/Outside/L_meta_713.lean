import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_713_aux

lemma main_proof (n m r : ℕ) (S : Fin m → Finset (Fin n)) (B : Finset (Fin n))
    (hr : ∀ p : Fin n, (Finset.univ.filter (fun i : Fin m => p ∈ S i)).card ≤ r) :
    (Finset.univ.filter (fun i : Fin m => ∃ p ∈ B, p ∈ S i)).card ≤ B.card * r := by
  have hsub : Finset.univ.filter (fun i : Fin m => ∃ p ∈ B, p ∈ S i) ⊆
      B.biUnion (fun p => Finset.univ.filter (fun i : Fin m => p ∈ S i)) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨p, hpB, hpi⟩ := hi
    exact Finset.mem_biUnion.mpr ⟨p, hpB, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpi⟩⟩
  calc (Finset.univ.filter (fun i : Fin m => ∃ p ∈ B, p ∈ S i)).card
      ≤ (B.biUnion (fun p => Finset.univ.filter (fun i : Fin m => p ∈ S i))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ p ∈ B, (Finset.univ.filter (fun i : Fin m => p ∈ S i)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ B, r := Finset.sum_le_sum (fun p _ => hr p)
    _ = B.card * r := by rw [Finset.sum_const, smul_eq_mul]

end PEqualNP.Outside.L_meta_713_aux

theorem PEqualNP.Outside.L_meta_713 : ∀ (n m r : ℕ) (S : Fin m → Finset (Fin n)) (B : Finset (Fin n)), (∀ p : Fin n, (Finset.univ.filter (fun i : Fin m => p ∈ S i)).card ≤ r) → (Finset.univ.filter (fun i : Fin m => ∃ p ∈ B, p ∈ S i)).card ≤ B.card * r :=
  PEqualNP.Outside.L_meta_713_aux.main_proof
