import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_732_aux

def eEdges : List (Nat × Nat) :=
  [(0, 1), (0, 3), (0, 4), (0, 5), (0, 6), (1, 3), (1, 4), (1, 6), (2, 4),
    (2, 6), (2, 7), (3, 4), (3, 5), (3, 7), (4, 5), (4, 6), (4, 7), (5, 7)]

def dArcs : List (Nat × Nat) :=
  [(0, 3), (0, 4), (1, 0), (1, 6), (2, 4), (2, 6), (3, 1), (3, 5), (3, 7),
    (4, 1), (4, 3), (5, 0), (5, 4), (5, 7), (6, 0), (6, 4), (7, 2), (7, 4)]

abbrev eRel (u v : Fin 8) : Prop :=
  (u.val, v.val) ∈ eEdges ∨ (v.val, u.val) ∈ eEdges

abbrev dRel (u v : Fin 8) : Prop :=
  (u.val, v.val) ∈ dArcs

theorem eRel_iff_dRel : ∀ u v : Fin 8, eRel u v ↔ (dRel u v ∨ dRel v u) := by
  decide

theorem dRel_asym : ∀ u v : Fin 8, dRel u v → ¬ dRel v u := by
  decide

theorem dRel_0 : ∀ k : Fin 8, dRel 0 k → k = 3 ∨ k = 4 := by decide
theorem dRel_1 : ∀ k : Fin 8, dRel 1 k → k = 0 ∨ k = 6 := by decide
theorem dRel_2 : ∀ k : Fin 8, dRel 2 k → k = 4 ∨ k = 6 := by decide
theorem dRel_3 : ∀ k : Fin 8, dRel 3 k → k = 1 ∨ k = 5 ∨ k = 7 := by decide
theorem dRel_4 : ∀ k : Fin 8, dRel 4 k → k = 1 ∨ k = 3 := by decide
theorem dRel_5 : ∀ k : Fin 8, dRel 5 k → k = 0 ∨ k = 4 ∨ k = 7 := by decide
theorem dRel_6 : ∀ k : Fin 8, dRel 6 k → k = 0 ∨ k = 4 := by decide
theorem dRel_7 : ∀ k : Fin 8, dRel 7 k → k = 2 ∨ k = 4 := by decide

theorem eRel_4 : ∀ u : Fin 8, u ≠ 4 → eRel 4 u := by decide

theorem eRel_not_mem {S : Set (Fin 8)} (hS : ∀ u ∈ S, ∀ v ∈ S, ¬ eRel u v)
    {u v : Fin 8} (hu : u ∈ S) (huv : eRel u v) : v ∉ S :=
  fun hv => hS u hu v hv huv

theorem main_aux (W K : Set (Fin 8))
    (hW : ∀ u ∈ W, ∀ v ∈ W, ¬ eRel u v)
    (hK : ∀ u ∈ K, ∀ v ∈ K, ¬ eRel u v) :
    ∃ v, v ∉ W ∧ v ∉ K ∧ ∀ k ∈ K, ¬ dRel v k := by
  by_cases h4K : (4 : Fin 8) ∈ K
  · have hK4 : ∀ u : Fin 8, u ≠ 4 → u ∉ K := fun u hu => eRel_not_mem hK h4K (eRel_4 u hu)
    by_cases h1W : (1 : Fin 8) ∈ W
    · refine ⟨3, eRel_not_mem hW h1W (by decide), hK4 3 (by decide), ?_⟩
      intro k hk hdk
      rcases dRel_3 k hdk with rfl | rfl | rfl
      · exact hK4 1 (by decide) hk
      · exact hK4 5 (by decide) hk
      · exact hK4 7 (by decide) hk
    · refine ⟨1, h1W, hK4 1 (by decide), ?_⟩
      intro k hk hdk
      rcases dRel_1 k hdk with rfl | rfl
      · exact hK4 0 (by decide) hk
      · exact hK4 6 (by decide) hk
  · by_cases h4W : (4 : Fin 8) ∈ W
    · have hW4 : ∀ u : Fin 8, u ≠ 4 → u ∉ W := fun u hu => eRel_not_mem hW h4W (eRel_4 u hu)
      by_cases h6K : (6 : Fin 8) ∈ K
      · have h0K : (0 : Fin 8) ∉ K := eRel_not_mem hK h6K (by decide)
        have h2K : (2 : Fin 8) ∉ K := eRel_not_mem hK h6K (by decide)
        by_cases h7K : (7 : Fin 8) ∈ K
        · have h3K : (3 : Fin 8) ∉ K := eRel_not_mem hK h7K (by decide)
          refine ⟨0, hW4 0 (by decide), h0K, ?_⟩
          intro k hk hdk
          rcases dRel_0 k hdk with rfl | rfl
          · exact h3K hk
          · exact h4K hk
        · refine ⟨7, hW4 7 (by decide), h7K, ?_⟩
          intro k hk hdk
          rcases dRel_7 k hdk with rfl | rfl
          · exact h2K hk
          · exact h4K hk
      · by_cases h0K : (0 : Fin 8) ∈ K
        · have h1K : (1 : Fin 8) ∉ K := eRel_not_mem hK h0K (by decide)
          have h3K : (3 : Fin 8) ∉ K := eRel_not_mem hK h0K (by decide)
          have h5K : (5 : Fin 8) ∉ K := eRel_not_mem hK h0K (by decide)
          by_cases h7K : (7 : Fin 8) ∈ K
          · have h2K : (2 : Fin 8) ∉ K := eRel_not_mem hK h7K (by decide)
            refine ⟨2, hW4 2 (by decide), h2K, ?_⟩
            intro k hk hdk
            rcases dRel_2 k hdk with rfl | rfl
            · exact h4K hk
            · exact h6K hk
          · refine ⟨3, hW4 3 (by decide), h3K, ?_⟩
            intro k hk hdk
            rcases dRel_3 k hdk with rfl | rfl | rfl
            · exact h1K hk
            · exact h5K hk
            · exact h7K hk
        · refine ⟨6, hW4 6 (by decide), h6K, ?_⟩
          intro k hk hdk
          rcases dRel_6 k hdk with rfl | rfl
          · exact h0K hk
          · exact h4K hk
    · by_cases h1K : (1 : Fin 8) ∈ K
      · have h0K : (0 : Fin 8) ∉ K := eRel_not_mem hK h1K (by decide)
        have h3K : (3 : Fin 8) ∉ K := eRel_not_mem hK h1K (by decide)
        have h6K : (6 : Fin 8) ∉ K := eRel_not_mem hK h1K (by decide)
        by_cases h0W : (0 : Fin 8) ∈ W
        · refine ⟨6, eRel_not_mem hW h0W (by decide), h6K, ?_⟩
          intro k hk hdk
          rcases dRel_6 k hdk with rfl | rfl
          · exact h0K hk
          · exact h4K hk
        · refine ⟨0, h0W, h0K, ?_⟩
          intro k hk hdk
          rcases dRel_0 k hdk with rfl | rfl
          · exact h3K hk
          · exact h4K hk
      · by_cases h3K : (3 : Fin 8) ∈ K
        · have h0K : (0 : Fin 8) ∉ K := eRel_not_mem hK h3K (by decide)
          have h5K : (5 : Fin 8) ∉ K := eRel_not_mem hK h3K (by decide)
          have h7K : (7 : Fin 8) ∉ K := eRel_not_mem hK h3K (by decide)
          by_cases h5W : (5 : Fin 8) ∈ W
          · have h7W : (7 : Fin 8) ∉ W := eRel_not_mem hW h5W (by decide)
            by_cases h2K : (2 : Fin 8) ∈ K
            · have h6K : (6 : Fin 8) ∉ K := eRel_not_mem hK h2K (by decide)
              by_cases h1W : (1 : Fin 8) ∈ W
              · refine ⟨6, eRel_not_mem hW h1W (by decide), h6K, ?_⟩
                intro k hk hdk
                rcases dRel_6 k hdk with rfl | rfl
                · exact h0K hk
                · exact h4K hk
              · refine ⟨1, h1W, h1K, ?_⟩
                intro k hk hdk
                rcases dRel_1 k hdk with rfl | rfl
                · exact h0K hk
                · exact h6K hk
            · refine ⟨7, h7W, h7K, ?_⟩
              intro k hk hdk
              rcases dRel_7 k hdk with rfl | rfl
              · exact h2K hk
              · exact h4K hk
          · refine ⟨5, h5W, h5K, ?_⟩
            intro k hk hdk
            rcases dRel_5 k hdk with rfl | rfl | rfl
            · exact h0K hk
            · exact h4K hk
            · exact h7K hk
        · refine ⟨4, h4W, h4K, ?_⟩
          intro k hk hdk
          rcases dRel_4 k hdk with rfl | rfl
          · exact h1K hk
          · exact h3K hk

end PEqualNP.Outside.L_meta_732_aux

theorem PEqualNP.Outside.L_meta_732 :
    ∀ (E D : Fin 8 → Fin 8 → Prop),
      (∀ u v, E u v ↔ ((u.val, v.val) ∈ [(0, 1), (0, 3), (0, 4), (0, 5), (0, 6), (1, 3), (1, 4), (1, 6), (2, 4),
          (2, 6), (2, 7), (3, 4), (3, 5), (3, 7), (4, 5), (4, 6), (4, 7), (5, 7)] ∨
        (v.val, u.val) ∈ [(0, 1), (0, 3), (0, 4), (0, 5), (0, 6), (1, 3), (1, 4), (1, 6), (2, 4),
          (2, 6), (2, 7), (3, 4), (3, 5), (3, 7), (4, 5), (4, 6), (4, 7), (5, 7)])) →
      (∀ u v, D u v ↔ (u.val, v.val) ∈ [(0, 3), (0, 4), (1, 0), (1, 6), (2, 4), (2, 6), (3, 1), (3, 5), (3, 7),
          (4, 1), (4, 3), (5, 0), (5, 4), (5, 7), (6, 0), (6, 4), (7, 2), (7, 4)]) →
      (∀ u v, E u v ↔ (D u v ∨ D v u)) ∧ (∀ u v, D u v → ¬ D v u) ∧
      ∀ W K : Set (Fin 8),
        (∀ u ∈ W, ∀ v ∈ W, ¬ E u v) → Disjoint K W → (∀ u ∈ K, ∀ v ∈ K, ¬ E u v) →
        ∃ v, v ∉ W ∧ v ∉ K ∧ ∀ k ∈ K, ¬ D v k := by
  intro E D hE hD
  refine ⟨?_, ?_, ?_⟩
  · intro u v
    rw [hE u v, hD u v, hD v u]
    exact PEqualNP.Outside.L_meta_732_aux.eRel_iff_dRel u v
  · intro u v h
    rw [hD u v] at h
    rw [hD v u]
    exact PEqualNP.Outside.L_meta_732_aux.dRel_asym u v h
  · intro W K hW _ hK
    have hW' : ∀ u ∈ W, ∀ v ∈ W, ¬ PEqualNP.Outside.L_meta_732_aux.eRel u v := fun u hu v hv h =>
      hW u hu v hv ((hE u v).2 h)
    have hK' : ∀ u ∈ K, ∀ v ∈ K, ¬ PEqualNP.Outside.L_meta_732_aux.eRel u v := fun u hu v hv h =>
      hK u hu v hv ((hE u v).2 h)
    rcases PEqualNP.Outside.L_meta_732_aux.main_aux W K hW' hK' with ⟨v, hvW, hvK, hvk⟩
    exact ⟨v, hvW, hvK, fun k hk hd => hvk k hk ((hD v k).1 hd)⟩
