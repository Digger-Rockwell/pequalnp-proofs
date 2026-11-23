import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside

private lemma perm4_expand (w : Fin 4 → Fin 4 → ℂ) :
    (∑ σ : Equiv.Perm (Fin 4), ∏ i : Fin 4, w i (σ i)) =
      (w 0 0 * w 1 1 + w 0 1 * w 1 0) * (w 2 2 * w 3 3 + w 2 3 * w 3 2) +
      (w 0 0 * w 1 2 + w 0 2 * w 1 0) * (w 2 1 * w 3 3 + w 2 3 * w 3 1) +
      (w 0 0 * w 1 3 + w 0 3 * w 1 0) * (w 2 1 * w 3 2 + w 2 2 * w 3 1) +
      (w 0 1 * w 1 2 + w 0 2 * w 1 1) * (w 2 0 * w 3 3 + w 2 3 * w 3 0) +
      (w 0 1 * w 1 3 + w 0 3 * w 1 1) * (w 2 0 * w 3 2 + w 2 2 * w 3 0) +
      (w 0 2 * w 1 3 + w 0 3 * w 1 2) * (w 2 0 * w 3 1 + w 2 1 * w 3 0) := by
  have sum_perm_succ : ∀ {n : ℕ} (g : Equiv.Perm (Fin (n + 1)) → ℂ),
      ∑ σ, g σ = ∑ a : Fin (n + 1), ∑ τ : Equiv.Perm (Fin n),
        g (Equiv.Perm.decomposeFin.symm (a, τ)) := by
    intro n g
    rw [← Equiv.Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]
  rw [sum_perm_succ]
  simp only [sum_perm_succ (n := 2), sum_perm_succ (n := 1), sum_perm_succ (n := 0)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ,
    Fintype.sum_unique]
  simp +decide [Equiv.swap_apply_def]
  ring

theorem L_gct_193 :
    ∀ c : ℂ, (∑ σ : Equiv.Perm (Fin 4), ∏ i : Fin 4, (1 + c * (if (σ i).val = i.val then (1 : ℂ) else if (σ i).val = (i.val + 1) % 4 then Complex.I else if (σ i).val = (i.val + 2) % 4 then -Complex.I else -1))) = 24 := by
  intro c
  rw [perm4_expand (fun i j : Fin 4 =>
    1 + c * (if j.val = i.val then (1 : ℂ) else if j.val = (i.val + 1) % 4 then Complex.I else if j.val = (i.val + 2) % 4 then -Complex.I else -1))]
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    rw [pow_succ, hI2]
    ring
  have hI4 : Complex.I ^ 4 = 1 := by
    rw [pow_succ, hI3]
    linear_combination -hI2
  norm_num
  ring_nf
  simp only [hI2, hI3, hI4]
  ring

end PEqualNP.Outside
