import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_791_aux

def eval7 (b0 b1 b2 b3 b4 b5 b6 : Bool) : Bool :=
  ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 13]⟩], output := 14 } : PEqualNP.CircuitLowerBounds.Circuit).eval [b0, b1, b2, b3, b4, b5, b6]

def spec7 (b0 b1 b2 b3 b4 b5 b6 : Bool) : Bool :=
  (b0 && b1) || (b1 && b2) || (b2 && b3) || (b3 && b4) || (b4 && b5) || (b5 && b6)

lemma eq7 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, eval7 b0 b1 b2 b3 b4 b5 b6 = spec7 b0 b1 b2 b3 b4 b5 b6 := by
  decide

lemma ofFn7 (x : Fin 7 → Bool) :
    List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
  rfl

end PEqualNP.Outside.L_meta_791_aux

theorem PEqualNP.Outside.L_meta_791 :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 13]⟩], output := 14 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 8 ∧ (∀ x : Fin 7 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 7, (u.val, v.val) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  intro C hC
  subst hC
  refine ⟨?_, rfl, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    rw [PEqualNP.Outside.L_meta_791_aux.ofFn7]
    change PEqualNP.Outside.L_meta_791_aux.eval7 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) = true ↔ _
    rw [PEqualNP.Outside.L_meta_791_aux.eq7]
    unfold PEqualNP.Outside.L_meta_791_aux.spec7
    constructor
    · intro h
      simp only [Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with (((((⟨h0, h1⟩ | ⟨h1, h2⟩) | ⟨h2, h3⟩) | ⟨h3, h4⟩) | ⟨h4, h5⟩) | ⟨h5, h6⟩)
      · exact ⟨0, 1, by simp, h0, h1⟩
      · exact ⟨1, 2, by simp, h1, h2⟩
      · exact ⟨2, 3, by simp, h2, h3⟩
      · exact ⟨3, 4, by simp, h3, h4⟩
      · exact ⟨4, 5, by simp, h4, h5⟩
      · exact ⟨5, 6, by simp, h5, h6⟩
    · rintro ⟨u, v, hmem, hu, hv⟩
      fin_cases u <;> fin_cases v <;> simp_all
