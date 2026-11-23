import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside

private lemma div_mod_unique {d a b r s : ℕ} (hr : r < d) (hs : s < d)
    (h : d * a + r = d * b + s) : a = b ∧ r = s := by
  have hd : 0 < d := by omega
  have hq : (d * a + r) / d = (d * b + s) / d := congrArg (· / d) h
  have hrem : (d * a + r) % d = (d * b + s) % d := congrArg (· % d) h
  rw [Nat.mul_add_div hd, Nat.mul_add_div hd, Nat.div_eq_of_lt hr, Nat.div_eq_of_lt hs,
    add_zero, add_zero] at hq
  rw [Nat.mul_add_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hs] at hrem
  exact ⟨hq, hrem⟩

theorem L_meta_294 :
    ∀ (m k : ℕ) (u v u' v' : Fin m) (i i' : ℕ), i < 2 * k → i' < 2 * k → m + 2 * k * (u.val * m + v.val) + i = m + 2 * k * (u'.val * m + v'.val) + i' → u = u' ∧ v = v' ∧ i = i' := by
  intro m k u v u' v' i i' hi hi' h
  have h1 : 2 * k * (u.val * m + v.val) + i = 2 * k * (u'.val * m + v'.val) + i' := by omega
  obtain ⟨huv, hii⟩ := div_mod_unique hi hi' h1
  have h2 : m * u.val + v.val = m * u'.val + v'.val := by
    rw [Nat.mul_comm m u.val, Nat.mul_comm m u'.val]
    exact huv
  obtain ⟨hu, hv⟩ := div_mod_unique v.isLt v'.isLt h2
  exact ⟨Fin.ext hu, Fin.ext hv, hii⟩

end PEqualNP.Outside
