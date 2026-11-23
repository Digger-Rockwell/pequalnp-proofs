import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_704 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n)),
    (∀ a b : Fin n, G.Adj a b → a ∈ T ∨ b ∈ T) →
      (PEqualNP.AndCount.AndCountCircuit.starCircuit G T).WellFormed ∧
      (PEqualNP.AndCount.AndCountCircuit.starCircuit G T).size = T.card ∧
      ∀ I : Finset (Fin n), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) → (∀ x : Fin n, x ∉ I → ∃ v ∈ I, G.Adj x v) →
        (PEqualNP.AndCount.AndCountCircuit.starCircuit G T).eval I = false ∧
        ∀ x : Fin n, x ∉ I → (PEqualNP.AndCount.AndCountCircuit.starCircuit G T).eval (insert x I) = true := by
  intro n G _ T hT
  have hgate : ∀ (U : Finset (Fin n)) (j : Fin (PEqualNP.AndCount.AndCountCircuit.starCircuit G T).size),
      (PEqualNP.AndCount.AndCountCircuit.starCircuit G T).gateVal U j = true ↔
        T.orderEmbOfFin rfl j ∈ U ∧ ∃ w ∈ U, G.Adj (T.orderEmbOfFin rfl j) w := by
    intro U j
    have hpos : (PEqualNP.AndCount.AndCountCircuit.starCircuit G T).size ≠ 0 := by
      have hj := j.isLt
      omega
    obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero hpos
    unfold PEqualNP.AndCount.AndCountCircuit.gateVal
    rw [hd]
    dsimp only [PEqualNP.AndCount.AndCountCircuit.gateValFuel, PEqualNP.AndCount.AndCountCircuit.sideTrue]
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    dsimp only [PEqualNP.AndCount.AndCountCircuit.starCircuit]
    constructor
    · rintro ⟨h1, h2⟩
      constructor
      · rcases h1 with ⟨v, hv, hvU⟩ | ⟨j1, hj1, _⟩
        · rw [Finset.mem_singleton.mp hv] at hvU
          exact hvU
        · exact absurd hj1 (Finset.notMem_empty j1)
      · rcases h2 with ⟨w, hw, hwU⟩ | ⟨j1, hj1, _⟩
        · exact ⟨w, hwU, (Finset.mem_filter.mp hw).2⟩
        · exact absurd hj1 (Finset.notMem_empty j1)
    · rintro ⟨htU, w, hwU, hadj⟩
      exact ⟨Or.inl ⟨_, Finset.mem_singleton_self _, htU⟩,
        Or.inl ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ w, hadj⟩, hwU⟩⟩
  have heval : ∀ (U : Finset (Fin n)),
      (PEqualNP.AndCount.AndCountCircuit.starCircuit G T).eval U = true ↔
        ∃ j : Fin (PEqualNP.AndCount.AndCountCircuit.starCircuit G T).size,
          T.orderEmbOfFin rfl j ∈ U ∧ ∃ w ∈ U, G.Adj (T.orderEmbOfFin rfl j) w := by
    intro U
    unfold PEqualNP.AndCount.AndCountCircuit.eval
    rw [decide_eq_true_eq]
    constructor
    · rintro (⟨v, hv, _⟩ | ⟨j, _, hj⟩)
      · exact absurd hv (Finset.notMem_empty v)
      · exact ⟨j, (hgate U j).mp hj⟩
    · rintro ⟨j, hj⟩
      exact Or.inr ⟨j, Finset.mem_univ j, (hgate U j).mpr hj⟩
  refine ⟨?_, rfl, ?_⟩
  · intro i
    exact ⟨fun j hj => absurd hj (Finset.notMem_empty j),
      fun j hj => absurd hj (Finset.notMem_empty j)⟩
  · intro I hI hmax
    constructor
    · rw [Bool.eq_false_iff]
      intro htrue
      rw [heval] at htrue
      rcases htrue with ⟨j, hjI, w, hwI, hadj⟩
      exact hI _ hjI _ hwI hadj
    · intro x hx
      rcases hmax x hx with ⟨v, hvI, hxv⟩
      rw [heval]
      have hmem : ∀ t ∈ T, ∃ j : Fin T.card, T.orderEmbOfFin rfl j = t := by
        intro t ht
        have hrange : t ∈ Set.range (T.orderEmbOfFin rfl) := by
          rw [Finset.range_orderEmbOfFin]
          exact ht
        exact hrange
      rcases hT x v hxv with hxT | hvT
      · rcases hmem x hxT with ⟨j, hj⟩
        refine ⟨j, ?_, v, Finset.mem_insert_of_mem hvI, ?_⟩
        · rw [hj]
          exact Finset.mem_insert_self x I
        · rw [hj]
          exact hxv
      · rcases hmem v hvT with ⟨j, hj⟩
        refine ⟨j, ?_, x, Finset.mem_insert_self x I, ?_⟩
        · rw [hj]
          exact Finset.mem_insert_of_mem hvI
        · rw [hj]
          exact hxv.symm
