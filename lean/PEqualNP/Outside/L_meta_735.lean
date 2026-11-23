import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_735_aux

open PEqualNP.CircuitLowerBounds

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def remapGate (phi : ℕ → ℕ) (g : Gate) : Gate :=
  { op := g.op, inputs := g.inputs.map phi }

noncomputable def buildPhi
    (n n' M : ℕ) (Z : Finset (Fin n)) (e : Fin n' → Fin n)
    (hZ : ∀ k : Fin n, k ∉ Z ↔ ∃ j : Fin n', e j = k) (i : ℕ) : ℕ :=
  if hi : i < n then
    if hmem : (⟨i, hi⟩ : Fin n) ∈ Z then
      M
    else
      (Classical.choose ((hZ ⟨i, hi⟩).mp hmem)).val
  else
    n' + (i - n)

lemma getD_append_lt (w : List Bool) (v : Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ [v]).getD i false = w.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_eq (w : List Bool) (v : Bool) :
    (w ++ [v]).getD w.length false = v := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_of_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_step_getD
    (n n' M : ℕ) (phi : ℕ → ℕ)
    (hge : ∀ i : ℕ, n ≤ i → phi i = n' + (i - n))
    (hlt : ∀ i : ℕ, i < n → phi i < n' ∨ M ≤ phi i)
    (gs : List Gate) :
    ∀ (w w' : List Bool),
      n ≤ w.length →
      w'.length + n = w.length + n' →
      w'.length + gs.length ≤ M →
      (∀ i : ℕ, w'.getD (phi i) false = w.getD i false) →
      ∀ i : ℕ,
        ((gs.map (remapGate phi)).foldl stepWire w').getD (phi i) false =
        (gs.foldl stepWire w).getD i false := by
  induction gs with
  | nil =>
    intro w w' _ _ _ hagree i
    exact hagree i
  | cons g gs ih =>
    intro w w' hwn hlen hM hagree i
    simp only [List.map_cons, List.foldl_cons]
    have hv :
        (remapGate phi g).op.eval ((remapGate phi g).inputs.map fun k => w'.getD k false) =
        g.op.eval (g.inputs.map fun k => w.getD k false) := by
      simp only [remapGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro k _
      exact hagree k
    have hstep' : stepWire w' (remapGate phi g) =
        w' ++ [g.op.eval (g.inputs.map fun k => w.getD k false)] := by
      simp only [stepWire, hv]
    apply ih (stepWire w g) (stepWire w' (remapGate phi g))
    · simp only [stepWire, List.length_append, List.length_singleton]
      omega
    · simp only [stepWire, List.length_append, List.length_singleton]
      omega
    · simp only [stepWire, List.length_append, List.length_singleton]
      simp only [List.length_cons] at hM
      omega
    · intro k
      rw [hstep']
      change (w' ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]).getD (phi k) false =
        (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]).getD k false
      set v := g.op.eval (g.inputs.map fun j => w.getD j false)
      by_cases hk : k < n
      · rw [getD_append_lt w v k (by omega)]
        rcases hlt k hk with h1 | h2
        · rw [getD_append_lt w' v (phi k) (by omega)]
          exact hagree k
        · have hM1 : (w' ++ [v]).length ≤ phi k := by
            simp only [List.length_append, List.length_singleton]
            simp only [List.length_cons] at hM
            omega
          have hM0 : w'.length ≤ phi k := by
            simp only [List.length_cons] at hM
            omega
          rw [getD_of_ge (w' ++ [v]) (phi k) hM1]
          exact (getD_of_ge w' (phi k) hM0).symm.trans (hagree k)
      · have hnk : n ≤ k := by omega
        have hphik : phi k = n' + (k - n) := hge k hnk
        by_cases hkw : k < w.length
        · rw [getD_append_lt w v k hkw]
          rw [getD_append_lt w' v (phi k) (by omega)]
          exact hagree k
        · by_cases hkeq : k = w.length
          · have hpeq : phi k = w'.length := by omega
            rw [hpeq, hkeq, getD_append_eq w' v, getD_append_eq w v]
          · have h1 : (w ++ [v]).length ≤ k := by
              simp only [List.length_append, List.length_singleton]
              omega
            have h2 : (w' ++ [v]).length ≤ phi k := by
              simp only [List.length_append, List.length_singleton]
              omega
            rw [getD_of_ge (w' ++ [v]) (phi k) h2, getD_of_ge (w ++ [v]) k h1]

lemma buildPhi_ge
    (n n' M : ℕ) (Z : Finset (Fin n)) (e : Fin n' → Fin n)
    (hZ : ∀ k : Fin n, k ∉ Z ↔ ∃ j : Fin n', e j = k)
    (i : ℕ) (hi : n ≤ i) :
    buildPhi n n' M Z e hZ i = n' + (i - n) := by
  simp [buildPhi, Nat.not_lt.mpr hi]

lemma buildPhi_lt
    (n n' M : ℕ) (Z : Finset (Fin n)) (e : Fin n' → Fin n)
    (hZ : ∀ k : Fin n, k ∉ Z ↔ ∃ j : Fin n', e j = k)
    (i : ℕ) (hi : i < n) :
    buildPhi n n' M Z e hZ i < n' ∨ M ≤ buildPhi n n' M Z e hZ i := by
  unfold buildPhi
  split_ifs with hmem
  · exact Or.inr (le_refl M)
  · exact Or.inl (Classical.choose ((hZ ⟨i, hi⟩).mp hmem)).isLt

lemma buildPhi_agree
    (n n' M : ℕ) (Z : Finset (Fin n)) (e : Fin n' → Fin n)
    (hZ : ∀ k : Fin n, k ∉ Z ↔ ∃ j : Fin n', e j = k)
    (hMn' : n' ≤ M)
    (x x' : List Bool) (hx : x.length = n) (hx' : x'.length = n')
    (hZero : ∀ k ∈ Z, x.getD (k : ℕ) false = false)
    (hEq : ∀ j : Fin n', x.getD (e j : ℕ) false = x'.getD (j : ℕ) false)
    (i : ℕ) :
    x'.getD (buildPhi n n' M Z e hZ i) false = x.getD i false := by
  unfold buildPhi
  split_ifs with hi hmem
  · rw [getD_of_ge x' M (by omega)]
    exact (hZero ⟨i, hi⟩ hmem).symm
  · have hspec : e (Classical.choose ((hZ ⟨i, hi⟩).mp hmem)) = ⟨i, hi⟩ :=
      Classical.choose_spec ((hZ ⟨i, hi⟩).mp hmem)
    rw [← hEq (Classical.choose ((hZ ⟨i, hi⟩).mp hmem))]
    have hval : (e (Classical.choose ((hZ ⟨i, hi⟩).mp hmem)) : ℕ) = i :=
      congrArg Fin.val hspec
    rw [hval]
  · rw [getD_of_ge x' (n' + (i - n)) (by omega)]
    rw [getD_of_ge x i (by omega)]

end PEqualNP.Outside.L_meta_735_aux

theorem PEqualNP.Outside.L_meta_735 :
    ∀ (n n' : ℕ) (Z : Finset (Fin n)) (e : Fin n' → Fin n), StrictMono e →
      (∀ k : Fin n, k ∉ Z ↔ ∃ j : Fin n', e j = k) → n' + Z.card = n →
      ∀ gates : List PEqualNP.CircuitLowerBounds.Gate,
      ∃ phi : ℕ → ℕ, ∀ x x' : List Bool, x.length = n → x'.length = n' →
        (∀ k ∈ Z, x.getD (k : ℕ) false = false) →
        (∀ j : Fin n', x.getD (e j : ℕ) false = x'.getD (j : ℕ) false) →
        (∀ i : ℕ, (PEqualNP.CircuitLowerBounds.Circuit.wires
            { gates := gates.map (fun g => { op := g.op, inputs := g.inputs.map phi }), output := 0 } x').getD (phi i) false
          = (PEqualNP.CircuitLowerBounds.Circuit.wires { gates := gates, output := 0 } x).getD i false) ∧
        (∀ o : ℕ, PEqualNP.CircuitLowerBounds.Circuit.eval
            { gates := gates.map (fun g => { op := g.op, inputs := g.inputs.map phi }), output := phi o } x'
          = PEqualNP.CircuitLowerBounds.Circuit.eval { gates := gates, output := o } x) := by
  intro n n' Z e _ hZ _ gates
  refine ⟨PEqualNP.Outside.L_meta_735_aux.buildPhi n n' (n' + gates.length) Z e hZ, ?_⟩
  intro x x' hx hx' hZero hEq
  have hwires :
      ∀ i : ℕ,
        (PEqualNP.CircuitLowerBounds.Circuit.wires
          { gates := gates.map (fun g =>
              { op := g.op,
                inputs := g.inputs.map (PEqualNP.Outside.L_meta_735_aux.buildPhi n n' (n' + gates.length) Z e hZ) }),
            output := 0 } x').getD
          (PEqualNP.Outside.L_meta_735_aux.buildPhi n n' (n' + gates.length) Z e hZ i) false =
        (PEqualNP.CircuitLowerBounds.Circuit.wires { gates := gates, output := 0 } x).getD i false := by
    intro i
    exact PEqualNP.Outside.L_meta_735_aux.foldl_step_getD
      n n' (n' + gates.length)
      (PEqualNP.Outside.L_meta_735_aux.buildPhi n n' (n' + gates.length) Z e hZ)
      (PEqualNP.Outside.L_meta_735_aux.buildPhi_ge n n' (n' + gates.length) Z e hZ)
      (PEqualNP.Outside.L_meta_735_aux.buildPhi_lt n n' (n' + gates.length) Z e hZ)
      gates x x' (by omega) (by omega) (by omega)
      (PEqualNP.Outside.L_meta_735_aux.buildPhi_agree n n' (n' + gates.length) Z e hZ (by omega) x x' hx hx' hZero hEq)
      i
  refine ⟨hwires, ?_⟩
  intro o
  exact hwires o
