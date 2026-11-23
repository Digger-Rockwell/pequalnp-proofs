import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_734_aux

lemma extend_indep {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (hS : ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v) :
    ∃ I : Finset (Fin n), S ⊆ I ∧
      (∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) ∧
      (∀ v : Fin n, v ∉ I → ∃ u ∈ I, G.Adj v u) := by
  classical
  let F : Finset (Finset (Fin n)) :=
    Finset.univ.filter (fun A => S ⊆ A ∧ ∀ u ∈ A, ∀ v ∈ A, ¬ G.Adj u v)
  have hFne : F.Nonempty := ⟨S, Finset.mem_filter.2 ⟨Finset.mem_univ _, Finset.Subset.refl _, hS⟩⟩
  obtain ⟨I, hIF, hImax⟩ := F.exists_max_image Finset.card hFne
  have hIprop := (Finset.mem_filter.1 hIF).2
  refine ⟨I, hIprop.1, hIprop.2, ?_⟩
  intro v hv
  by_contra hno
  push Not at hno
  have hInsF : insert v I ∈ F := by
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, hIprop.1.trans (Finset.subset_insert v I), ?_⟩
    intro a ha b hb
    simp only [Finset.mem_insert] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact G.irrefl
    · exact hno b hb
    · exact fun hadj => hno a ha (G.adj_symm hadj)
    · exact hIprop.2 a ha b hb
  have hle := hImax (insert v I) hInsF
  rw [Finset.card_insert_of_notMem hv] at hle
  omega

lemma fin2_eq_of_ne (col a b : Fin 2) (ha : a ≠ col) (hb : b ≠ col) : a = b := by
  fin_cases col <;> fin_cases a <;> fin_cases b <;> simp_all

lemma fin2_eq_zero_or_one (a : Fin 2) : a = 0 ∨ a = 1 := by
  fin_cases a <;> simp

lemma contra_of_color_le_two {n : ℕ} (G : SimpleGraph (Fin n))
    (c : G.Coloring (Fin 2)) (col : Fin 2)
    (hc4 : ∀ a b d e, G.Adj a b → G.Adj b d → G.Adj d e → G.Adj e a → a = d ∨ b = e)
    (hdeg : ∀ v, 3 ≤ {w : Fin n | G.Adj v w}.ncard)
    (T : Set (Fin n))
    (hcol : (T ∩ {v : Fin n | c v = col}).ncard ≤ 2)
    (hT : ∀ I : Set (Fin n), (∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) →
      (∀ v, v ∉ I → ∃ u ∈ I, G.Adj v u) → ∃ t ∈ T, t ∈ I)
    (hno : ∀ v ∈ T, ∃ w, G.Adj v w ∧ w ∉ T) : False := by
  classical
  let TY : Finset (Fin n) := Finset.univ.filter (fun v => v ∈ T ∧ c v = col)
  have hTY_card : TY.card ≤ 2 := by
    have hEq : TY = (T ∩ {v : Fin n | c v = col}).toFinset := by
      ext v
      simp [TY]
    rw [hEq, ← Set.ncard_eq_toFinset_card']
    exact hcol
  have hchoose : ∀ y : Fin n, y ∈ TY → ∃ x : Fin n, G.Adj y x ∧ x ∉ T := fun y hy =>
    hno y (Finset.mem_filter.1 hy).2.1
  choose f hf_adj hf_notT using hchoose
  let SX : Finset (Fin n) := TY.attach.image (fun y => f y.1 y.2)
  have hSX_card : SX.card ≤ 2 := by
    calc SX.card ≤ TY.attach.card := Finset.card_image_le
      _ = TY.card := Finset.card_attach
      _ ≤ 2 := hTY_card
  have hSX_notT : ∀ x ∈ SX, x ∉ T := by
    intro x hx
    obtain ⟨⟨y, hy⟩, _, rfl⟩ := Finset.mem_image.1 hx
    exact hf_notT y hy
  have hSX_col : ∀ x ∈ SX, c x ≠ col := by
    intro x hx
    obtain ⟨⟨y, hy⟩, _, rfl⟩ := Finset.mem_image.1 hx
    have hcy : c y = col := (Finset.mem_filter.1 hy).2.2
    intro hcx
    exact c.valid (hf_adj y hy) (hcy.trans hcx.symm)
  let SY : Finset (Fin n) := Finset.univ.filter (fun y => c y = col ∧ ∀ x ∈ SX, ¬ G.Adj x y)
  let S : Finset (Fin n) := SX ∪ SY
  have hS_indep : ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v := by
    intro u hu v hv hadj
    simp only [S, Finset.mem_union] at hu hv
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · exact c.valid hadj (fin2_eq_of_ne col (c u) (c v) (hSX_col u hu) (hSX_col v hv))
    · exact (Finset.mem_filter.1 hv).2.2 u hu hadj
    · exact (Finset.mem_filter.1 hu).2.2 v hv (G.adj_symm hadj)
    · exact c.valid hadj ((Finset.mem_filter.1 hu).2.1.trans (Finset.mem_filter.1 hv).2.1.symm)
  have hT_dom : ∀ t ∈ T, ∃ u ∈ S, G.Adj t u := by
    intro t ht
    by_cases hct : c t = col
    · have htY : t ∈ TY := Finset.mem_filter.2 ⟨Finset.mem_univ _, ht, hct⟩
      refine ⟨f t htY, Finset.mem_union_left _ ?_, hf_adj t htY⟩
      exact Finset.mem_image.2 ⟨⟨t, htY⟩, Finset.mem_attach _ _, rfl⟩
    · have ht_notSX : t ∉ SX := fun h => hSX_notT t h ht
      let N : Finset (Fin n) := Finset.univ.filter (fun w => G.Adj t w)
      have hN_card : 3 ≤ N.card := by
        have hEq : N = {w : Fin n | G.Adj t w}.toFinset := by
          ext w
          simp [N]
        rw [hEq, ← Set.ncard_eq_toFinset_card']
        exact hdeg t
      by_contra hno_dom
      push Not at hno_dom
      have hN_sub : N ⊆ SX.biUnion (fun x => Finset.univ.filter (fun w => G.Adj t w ∧ G.Adj x w)) := by
        intro w hw
        have htw : G.Adj t w := (Finset.mem_filter.1 hw).2
        have hcw : c w = col := by
          by_contra hcw
          exact c.valid htw (fin2_eq_of_ne col (c t) (c w) hct hcw)
        have hw_notSY : w ∉ SY := fun hwSY => hno_dom w (Finset.mem_union_right _ hwSY) htw
        simp only [SY, Finset.mem_filter, Finset.mem_univ, true_and, hcw, not_forall, not_not] at hw_notSY
        obtain ⟨x, hxSX, hxw⟩ := hw_notSY
        exact Finset.mem_biUnion.2 ⟨x, hxSX, Finset.mem_filter.2 ⟨Finset.mem_univ _, htw, hxw⟩⟩
      have hle : N.card ≤ ∑ x ∈ SX, (Finset.univ.filter (fun w => G.Adj t w ∧ G.Adj x w)).card :=
        (Finset.card_le_card hN_sub).trans Finset.card_biUnion_le
      have hcommon : ∀ x ∈ SX, (Finset.univ.filter (fun w => G.Adj t w ∧ G.Adj x w)).card ≤ 1 := by
        intro x hx
        have htx : t ≠ x := fun h => ht_notSX (h ▸ hx)
        refine Finset.card_le_one.2 ?_
        intro w₁ hw₁ w₂ hw₂
        obtain ⟨htw₁, hxw₁⟩ := (Finset.mem_filter.1 hw₁).2
        obtain ⟨htw₂, hxw₂⟩ := (Finset.mem_filter.1 hw₂).2
        rcases hc4 t w₁ x w₂ htw₁ (G.adj_symm hxw₁) hxw₂ (G.adj_symm htw₂) with h | h
        · exact (htx h).elim
        · exact h
      have hsum : ∑ x ∈ SX, (Finset.univ.filter (fun w => G.Adj t w ∧ G.Adj x w)).card ≤ SX.card := by
        calc ∑ x ∈ SX, (Finset.univ.filter (fun w => G.Adj t w ∧ G.Adj x w)).card
            ≤ ∑ _x ∈ SX, 1 := Finset.sum_le_sum hcommon
          _ = SX.card := by simp
      omega
  obtain ⟨I, hSI, hI_indep, hI_max⟩ := extend_indep G S hS_indep
  obtain ⟨t, htT, htI⟩ := hT (I : Set (Fin n)) (fun u hu v hv => hI_indep u hu v hv)
    (fun v hv => hI_max v hv)
  obtain ⟨u, huS, htu⟩ := hT_dom t htT
  exact hI_indep t htI u (hSI huS) htu

end PEqualNP.Outside.L_meta_734_aux

theorem PEqualNP.Outside.L_meta_734 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.Colorable 2 →
      (∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
      (∀ v, 3 ≤ {w : Fin n | G.Adj v w}.ncard) →
      ∀ T : Set (Fin n), T.ncard ≤ 5 →
        (∀ I : Set (Fin n), (∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) → (∀ v, v ∉ I → ∃ u ∈ I, G.Adj v u) →
          ∃ t ∈ T, t ∈ I) →
        ∃ v ∈ T, ∀ w, G.Adj v w → w ∈ T := by
  intro n G hcol hc4 hdeg T hTcard hT
  obtain ⟨c⟩ := hcol
  by_contra hno
  push Not at hno
  have hsplit : (T ∩ {v : Fin n | c v = 0}).ncard + (T ∩ {v : Fin n | c v = 1}).ncard = T.ncard := by
    rw [← Set.ncard_union_eq]
    · congr 1
      ext v
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · rintro (⟨hv, _⟩ | ⟨hv, _⟩) <;> exact hv
      · intro hv
        rcases PEqualNP.Outside.L_meta_734_aux.fin2_eq_zero_or_one (c v) with h | h
        · exact Or.inl ⟨hv, h⟩
        · exact Or.inr ⟨hv, h⟩
    · rw [Set.disjoint_left]
      intro v hv0 hv1
      have h0 : c v = 0 := hv0.2
      have h1 : c v = 1 := hv1.2
      exact absurd (h0.symm.trans h1) (by decide)
  by_cases h0 : (T ∩ {v : Fin n | c v = 0}).ncard ≤ 2
  · exact PEqualNP.Outside.L_meta_734_aux.contra_of_color_le_two G c 0 hc4 hdeg T h0 hT hno
  · have h1 : (T ∩ {v : Fin n | c v = 1}).ncard ≤ 2 := by omega
    exact PEqualNP.Outside.L_meta_734_aux.contra_of_color_le_two G c 1 hc4 hdeg T h1 hT hno
