import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_729_aux

def WalkIn {n : ℕ} (D : Fin n → Fin n → Prop) (S : Finset (Fin n)) (m : ℕ) (u v : Fin n) : Prop :=
  ∃ c : ℕ → Fin n,
    c 0 = u ∧ c m = v ∧ (∀ i, i ≤ m → c i ∈ S) ∧ (∀ i, i < m → D (c i) (c (i + 1)))

def ReachIn {n : ℕ} (D : Fin n → Fin n → Prop) (S : Finset (Fin n)) (u v : Fin n) : Prop :=
  ∃ m, WalkIn D S m u v

theorem walkIn_zero {n : ℕ} {D : Fin n → Fin n → Prop} {S : Finset (Fin n)} {u : Fin n}
    (hu : u ∈ S) : WalkIn D S 0 u u :=
  ⟨fun _ => u, rfl, rfl, fun _ _ => hu, fun _ hi => (Nat.not_lt_zero _ hi).elim⟩

theorem walkIn_step {n : ℕ} {D : Fin n → Fin n → Prop} {S : Finset (Fin n)} {m : ℕ}
    {u v w : Fin n} (h : WalkIn D S m u v) (hw : w ∈ S) (hd : D v w) :
    WalkIn D S (m + 1) u w := by
  rcases h with ⟨c, h0, hm, hmem, hedge⟩
  refine ⟨fun i => if i ≤ m then c i else w, ?_, ?_, ?_, ?_⟩
  · simp [h0]
  · simp
  · intro i hi
    by_cases hle : i ≤ m
    · simp [hle, hmem i hle]
    · simp [hle, hw]
  · intro i hi
    by_cases hlt : i < m
    · have h1 : i ≤ m := Nat.le_of_lt hlt
      have h2 : i + 1 ≤ m := hlt
      simp [h1, h2, hedge i hlt]
    · have heq : i = m := by omega
      subst heq
      simp [hm, hd]

theorem walkIn_append {n : ℕ} {D : Fin n → Fin n → Prop} {S : Finset (Fin n)} {m₁ m₂ : ℕ}
    {u v w : Fin n} (h₁ : WalkIn D S m₁ u v) (h₂ : WalkIn D S m₂ v w) :
    WalkIn D S (m₁ + m₂) u w := by
  rcases h₁ with ⟨c₁, h₁0, h₁m, h₁mem, h₁edge⟩
  rcases h₂ with ⟨c₂, h₂0, h₂m, h₂mem, h₂edge⟩
  refine ⟨fun i => if i ≤ m₁ then c₁ i else c₂ (i - m₁), ?_, ?_, ?_, ?_⟩
  · simp [h₁0]
  · by_cases hm₂ : m₂ = 0
    · subst hm₂
      simp [h₁m, ← h₂0, h₂m]
    · have hgt : ¬ m₁ + m₂ ≤ m₁ := by omega
      simp [hgt, h₂m]
  · intro i hi
    by_cases hle : i ≤ m₁
    · simp [hle, h₁mem i hle]
    · have hsub : i - m₁ ≤ m₂ := by omega
      simp [hle, h₂mem (i - m₁) hsub]
  · intro i hi
    by_cases hlt : i < m₁
    · have h1 : i ≤ m₁ := Nat.le_of_lt hlt
      have h2 : i + 1 ≤ m₁ := hlt
      simp [h1, h2, h₁edge i hlt]
    · by_cases heq : i = m₁
      · subst i
        have hpos : 0 < m₂ := by omega
        have hnot : ¬ m₁ + 1 ≤ m₁ := by omega
        have hsub : m₁ + 1 - m₁ = 1 := by omega
        simp only [le_refl, ↓reduceIte, hnot, hsub]
        rw [h₁m, ← h₂0]
        exact h₂edge 0 hpos
      · have h1 : ¬ i ≤ m₁ := by omega
        have h2 : ¬ i + 1 ≤ m₁ := by omega
        have hlt2 : i - m₁ < m₂ := by omega
        have hsub : i + 1 - m₁ = i - m₁ + 1 := by omega
        simp only [h1, h2, ↓reduceIte, hsub]
        exact h₂edge (i - m₁) hlt2

theorem walkIn_pos_first {n : ℕ} {D : Fin n → Fin n → Prop} {S : Finset (Fin n)} {m : ℕ}
    {u v : Fin n} (h : WalkIn D S (m + 1) u v) :
    ∃ w ∈ S, D u w ∧ WalkIn D S m w v := by
  rcases h with ⟨c, h0, hm, hmem, hedge⟩
  refine ⟨c 1, hmem 1 (by omega), ?_, ⟨fun i => c (i + 1), rfl, hm, ?_, ?_⟩⟩
  · rw [← h0]
    exact hedge 0 (by omega)
  · intro i hi
    exact hmem (i + 1) (by omega)
  · intro i hi
    exact hedge (i + 1) (by omega)

theorem reachIn_refl {n : ℕ} {D : Fin n → Fin n → Prop} {S : Finset (Fin n)} {u : Fin n}
    (hu : u ∈ S) : ReachIn D S u u :=
  ⟨0, walkIn_zero hu⟩

theorem reachIn_trans {n : ℕ} {D : Fin n → Fin n → Prop} {S : Finset (Fin n)} {u v w : Fin n}
    (h₁ : ReachIn D S u v) (h₂ : ReachIn D S v w) : ReachIn D S u w := by
  rcases h₁ with ⟨m₁, hm₁⟩
  rcases h₂ with ⟨m₂, hm₂⟩
  exact ⟨m₁ + m₂, walkIn_append hm₁ hm₂⟩

theorem reachIn_step {n : ℕ} {D : Fin n → Fin n → Prop} {S : Finset (Fin n)} {u v w : Fin n}
    (h : ReachIn D S u v) (hw : w ∈ S) (hd : D v w) : ReachIn D S u w := by
  rcases h with ⟨m, hm⟩
  exact ⟨m + 1, walkIn_step hm hw hd⟩

theorem walkIn_odd_closed_false {n : ℕ} {D : Fin n → Fin n → Prop}
    (hnodd : ¬ ∃ (k : ℕ) (c : ℕ → Fin n), c (2 * k + 1) = c 0 ∧ ∀ i, i < 2 * k + 1 → D (c i) (c (i + 1)))
    {S : Finset (Fin n)} {k : ℕ} {u : Fin n} (h : WalkIn D S (2 * k + 1) u u) : False := by
  rcases h with ⟨c, h0, hm, _, hedge⟩
  exact hnodd ⟨k, c, hm.trans h0.symm, hedge⟩

theorem kernel_of_finset {n : ℕ} (D : Fin n → Fin n → Prop)
    (hnodd : ¬ ∃ (k : ℕ) (c : ℕ → Fin n), c (2 * k + 1) = c 0 ∧ ∀ i, i < 2 * k + 1 → D (c i) (c (i + 1))) :
    ∀ (m : ℕ) (S : Finset (Fin n)), S.card = m →
      ∃ K : Finset (Fin n), K ⊆ S ∧ (∀ u ∈ K, ∀ v ∈ K, ¬ D u v) ∧
        (∀ v ∈ S, v ∉ K → ∃ k ∈ K, D v k) := by
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro S hScard
    classical
    by_cases hSne : S.Nonempty
    · let R : Fin n → Finset (Fin n) := fun u => S.filter (fun v => ReachIn D S u v)
      obtain ⟨u₀, hu₀S, hmin⟩ := Finset.exists_min_image S (fun u => (R u).card) hSne
      let C : Finset (Fin n) := R u₀
      have hCS : C ⊆ S := Finset.filter_subset _ _
      have hu₀C : u₀ ∈ C := Finset.mem_filter.mpr ⟨hu₀S, reachIn_refl hu₀S⟩
      have hC_closed : ∀ x ∈ C, ∀ y ∈ S, D x y → y ∈ C := by
        intro x hx y hy hxy
        have hrx : ReachIn D S u₀ x := (Finset.mem_filter.mp hx).2
        exact Finset.mem_filter.mpr ⟨hy, reachIn_step hrx hy hxy⟩
      have hC_back : ∀ x ∈ C, ReachIn D S x u₀ := by
        intro x hx
        have hxS : x ∈ S := hCS hx
        have hrx : ReachIn D S u₀ x := (Finset.mem_filter.mp hx).2
        have hsub : R x ⊆ C := by
          intro w hw
          have hwS : w ∈ S := (Finset.mem_filter.mp hw).1
          have hrw : ReachIn D S x w := (Finset.mem_filter.mp hw).2
          exact Finset.mem_filter.mpr ⟨hwS, reachIn_trans hrx hrw⟩
        have heq : R x = C := Finset.eq_of_subset_of_card_le hsub (hmin x hxS)
        have hu₀Rx : u₀ ∈ R x := heq ▸ hu₀C
        exact (Finset.mem_filter.mp hu₀Rx).2
      let A : Finset (Fin n) := C.filter (fun v => ∃ t, WalkIn D S (2 * t) u₀ v)
      have hAC : A ⊆ C := Finset.filter_subset _ _
      have hAS : A ⊆ S := Finset.Subset.trans hAC hCS
      have hu₀A : u₀ ∈ A := Finset.mem_filter.mpr ⟨hu₀C, 0, walkIn_zero hu₀S⟩
      have hno_both : ∀ v ∈ C, (∃ t₁, WalkIn D S (2 * t₁) u₀ v) →
          (∃ t₂, WalkIn D S (2 * t₂ + 1) u₀ v) → False := by
        intro v hv ⟨t₁, h₁⟩ ⟨t₂, h₂⟩
        obtain ⟨r, hr⟩ := hC_back v hv
        rcases Nat.even_or_odd r with ⟨q, rfl⟩ | ⟨q, rfl⟩
        · have hw : WalkIn D S (2 * t₂ + 1 + (q + q)) u₀ u₀ := walkIn_append h₂ hr
          have hlen : 2 * t₂ + 1 + (q + q) = 2 * (t₂ + q) + 1 := by omega
          rw [hlen] at hw
          exact walkIn_odd_closed_false hnodd hw
        · have hw : WalkIn D S (2 * t₁ + (2 * q + 1)) u₀ u₀ := walkIn_append h₁ hr
          have hlen : 2 * t₁ + (2 * q + 1) = 2 * (t₁ + q) + 1 := by omega
          rw [hlen] at hw
          exact walkIn_odd_closed_false hnodd hw
      have hA_indep : ∀ x ∈ A, ∀ y ∈ A, ¬ D x y := by
        intro x hx y hy hxy
        have hx_even : ∃ t₁, WalkIn D S (2 * t₁) u₀ x := (Finset.mem_filter.mp hx).2
        have hy_even : ∃ t₂, WalkIn D S (2 * t₂) u₀ y := (Finset.mem_filter.mp hy).2
        rcases hx_even with ⟨t₁, ht₁⟩
        have hy_odd : ∃ t, WalkIn D S (2 * t + 1) u₀ y := ⟨t₁, walkIn_step ht₁ (hAS hy) hxy⟩
        exact hno_both y (hAC hy) hy_even hy_odd
      have hB_abs : ∀ b ∈ C, b ∉ A → ∃ a ∈ A, D b a := by
        intro b hbC hbA
        have hne : b ≠ u₀ := fun h => hbA (h ▸ hu₀A)
        obtain ⟨r, hr⟩ := hC_back b hbC
        cases r with
        | zero =>
          rcases hr with ⟨c, h0, hm0, _, _⟩
          exact (hne (h0.symm.trans hm0)).elim
        | succ r' =>
          obtain ⟨a, haS, hba, _⟩ := walkIn_pos_first hr
          have haC : a ∈ C := hC_closed b hbC a haS hba
          obtain ⟨t, ht⟩ := (Finset.mem_filter.mp hbC).2
          rcases Nat.even_or_odd t with ⟨q, rfl⟩ | ⟨q, rfl⟩
          · have h2 : q + q = 2 * q := by omega
            rw [h2] at ht
            exact (hbA (Finset.mem_filter.mpr ⟨hbC, q, ht⟩)).elim
          · have hwa : WalkIn D S (2 * q + 1 + 1) u₀ a := walkIn_step ht haS hba
            have hlen : 2 * q + 1 + 1 = 2 * (q + 1) := by omega
            rw [hlen] at hwa
            exact ⟨a, Finset.mem_filter.mpr ⟨haC, q + 1, hwa⟩, hba⟩
      let S' : Finset (Fin n) := S.filter (fun v => v ∉ C ∧ ∀ a ∈ A, ¬ D v a)
      have hS'S : S' ⊆ S := Finset.filter_subset _ _
      have hS'lt : S'.card < m := by
        rw [← hScard]
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset hS'S]
        refine ⟨u₀, hu₀S, ?_⟩
        intro hu₀S'
        exact (Finset.mem_filter.mp hu₀S').2.1 hu₀C
      obtain ⟨K', hK'S', hK'indep, hK'abs⟩ := ih S'.card hS'lt S' rfl
      refine ⟨A ∪ K', ?_, ?_, ?_⟩
      · exact Finset.union_subset hAS (Finset.Subset.trans hK'S' hS'S)
      · intro u hu v hv huv
        rcases Finset.mem_union.mp hu with huA | huK' <;>
        rcases Finset.mem_union.mp hv with hvA | hvK'
        · exact hA_indep u huA v hvA huv
        · have hvS' : v ∈ S' := hK'S' hvK'
          have hvC : v ∈ C := hC_closed u (hAC huA) v (hS'S hvS') huv
          exact (Finset.mem_filter.mp hvS').2.1 hvC
        · have huS' : u ∈ S' := hK'S' huK'
          exact (Finset.mem_filter.mp huS').2.2 v hvA huv
        · exact hK'indep u huK' v hvK' huv
      · intro v hvS hvK
        have hvA : v ∉ A := fun h => hvK (Finset.mem_union_left _ h)
        have hvK' : v ∉ K' := fun h => hvK (Finset.mem_union_right _ h)
        by_cases hvC : v ∈ C
        · obtain ⟨a, haA, hva⟩ := hB_abs v hvC hvA
          exact ⟨a, Finset.mem_union_left _ haA, hva⟩
        · by_cases hex : ∃ a ∈ A, D v a
          · obtain ⟨a, haA, hva⟩ := hex
            exact ⟨a, Finset.mem_union_left _ haA, hva⟩
          · have hvS' : v ∈ S' := by
              refine Finset.mem_filter.mpr ⟨hvS, hvC, ?_⟩
              intro a haA hva
              exact hex ⟨a, haA, hva⟩
            obtain ⟨k', hk'K', hvk'⟩ := hK'abs v hvS' hvK'
            exact ⟨k', Finset.mem_union_right _ hk'K', hvk'⟩
    · refine ⟨∅, Finset.empty_subset S, ?_, ?_⟩
      · intro u hu
        exact (Finset.notMem_empty u hu).elim
      · intro v hvS
        exact (hSne ⟨v, hvS⟩).elim

end PEqualNP.Outside.L_meta_729_aux

theorem PEqualNP.Outside.L_meta_729 :
    ∀ (n : ℕ) (D : Fin n → Fin n → Prop),
      (∀ v, ¬ D v v) → (∀ u v, D u v → ¬ D v u) →
      (¬ ∃ (k : ℕ) (c : ℕ → Fin n), c (2 * k + 1) = c 0 ∧ ∀ i, i < 2 * k + 1 → D (c i) (c (i + 1))) →
      ∃ K : Set (Fin n), (∀ u ∈ K, ∀ v ∈ K, ¬ D u v) ∧ ∀ v, v ∉ K → ∃ k ∈ K, D v k := by
  intro n D _ _ hnodd
  obtain ⟨K, _, hKindep, hKabs⟩ :=
    PEqualNP.Outside.L_meta_729_aux.kernel_of_finset D hnodd (Finset.univ : Finset (Fin n)).card
      Finset.univ rfl
  refine ⟨(K : Set (Fin n)), ?_, ?_⟩
  · intro u hu v hv
    exact hKindep u (Finset.mem_coe.mp hu) v (Finset.mem_coe.mp hv)
  · intro v hv
    obtain ⟨k, hkK, hvk⟩ := hKabs v (Finset.mem_univ v) (fun h => hv (Finset.mem_coe.mpr h))
    exact ⟨k, Finset.mem_coe.mpr hkK, hvk⟩
