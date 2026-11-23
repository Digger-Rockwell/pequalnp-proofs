import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_250 :
    ∀ (N k : ℕ) (E : Fin N → Fin N → Prop) (pos pos' : Fin N → ℕ), 1 ≤ k → ((∀ u v : Fin N, E u v → E v u) ∧ (∀ u v : Fin N, E u v → pos u ≠ 0 ∨ pos v ≠ 0) ∧ ∀ v : Fin N, pos v ≠ 0 → pos v ≤ 2 * k ∧ ∃ a b : Fin N, (∀ w : Fin N, E v w ↔ w = a ∨ w = b) ∧ pos a + 1 = pos v ∧ pos b = (pos v + 1) % (2 * k + 1)) → (∀ v : Fin N, pos' v ≤ 2 * k ∧ (pos v + pos' v) % (2 * k + 1) = 0) → ((∀ u v : Fin N, E u v → E v u) ∧ (∀ u v : Fin N, E u v → pos' u ≠ 0 ∨ pos' v ≠ 0) ∧ ∀ v : Fin N, pos' v ≠ 0 → pos' v ≤ 2 * k ∧ ∃ a b : Fin N, (∀ w : Fin N, E v w ↔ w = a ∨ w = b) ∧ pos' a + 1 = pos' v ∧ pos' b = (pos' v + 1) % (2 * k + 1)) := by
  intro N k E pos pos' hk ⟨hsym, hedge, hpos⟩ hrefl
  have hzero : ∀ v : Fin N, pos v = 0 ↔ pos' v = 0 := by
    intro v
    obtain ⟨hle', hmod⟩ := hrefl v
    constructor
    · intro hz
      rw [hz, zero_add, Nat.mod_eq_of_lt (by omega)] at hmod
      exact hmod
    · intro hz'
      by_contra hnz
      have hle : pos v ≤ 2 * k := (hpos v hnz).1
      rw [hz', add_zero, Nat.mod_eq_of_lt (by omega)] at hmod
      exact hnz hmod
  have hsum : ∀ v : Fin N, pos v ≠ 0 → pos v + pos' v = 2 * k + 1 := by
    intro v hnz
    have hle : pos v ≤ 2 * k := (hpos v hnz).1
    obtain ⟨hle', hmod⟩ := hrefl v
    have hnz' : pos' v ≠ 0 := fun hz' => hnz ((hzero v).mpr hz')
    have hdiv : 2 * k + 1 ∣ pos v + pos' v := Nat.dvd_of_mod_eq_zero hmod
    obtain ⟨q, hq⟩ := hdiv
    have hq1 : q = 1 := by
      have h1 : 1 ≤ q := by
        rcases Nat.eq_zero_or_pos q with rfl | hposq
        · omega
        · exact hposq
      have h2 : q ≤ 1 := by
        by_contra hgt
        have hge2 : 2 ≤ q := by omega
        have : 2 * (2 * k + 1) ≤ (2 * k + 1) * q := by
          rw [Nat.mul_comm 2 (2 * k + 1)]
          exact Nat.mul_le_mul_left (2 * k + 1) hge2
        omega
      omega
    subst hq1
    omega
  refine ⟨hsym, ?_, ?_⟩
  · intro u v huv
    rcases hedge u v huv with hu | hv
    · exact Or.inl fun hu' => hu ((hzero u).mpr hu')
    · exact Or.inr fun hv' => hv ((hzero v).mpr hv')
  · intro v hnz'
    have hnz : pos v ≠ 0 := fun hz => hnz' ((hzero v).mp hz)
    obtain ⟨hle, a, b, hnbr, ha, hb⟩ := hpos v hnz
    have hvsum := hsum v hnz
    refine ⟨(hrefl v).1, b, a, ?_, ?_, ?_⟩
    · intro w
      rw [hnbr, or_comm]
    · by_cases htop : pos v = 2 * k
      · have hbz : pos b = 0 := by
          rw [hb, htop, Nat.mod_self]
        have hbz' : pos' b = 0 := (hzero b).mp hbz
        omega
      · have hbeq : pos b = pos v + 1 := by
          rw [hb, Nat.mod_eq_of_lt (by omega)]
        have hbnz : pos b ≠ 0 := by omega
        have hbsum := hsum b hbnz
        omega
    · by_cases hbot : pos v = 1
      · have haz : pos a = 0 := by omega
        have haz' : pos' a = 0 := (hzero a).mp haz
        have hvp : pos' v = 2 * k := by omega
        rw [haz', hvp, Nat.mod_self]
      · have hanz : pos a ≠ 0 := by omega
        have hasum := hsum a hanz
        have hlt : pos' v + 1 < 2 * k + 1 := by omega
        rw [Nat.mod_eq_of_lt hlt]
        omega
