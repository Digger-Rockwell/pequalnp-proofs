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

private lemma subdiv_inj {k m : ℕ} {u₁ v₁ u₂ v₂ : Fin m} {i₁ i₂ : Fin (2 * k)}
    (h : m + 2 * k * (u₁.val * m + v₁.val) + i₁.val =
      m + 2 * k * (u₂.val * m + v₂.val) + i₂.val) :
    u₁ = u₂ ∧ v₁ = v₂ ∧ i₁ = i₂ := by
  have h1 : 2 * k * (u₁.val * m + v₁.val) + i₁.val =
      2 * k * (u₂.val * m + v₂.val) + i₂.val := by omega
  obtain ⟨huv, hi⟩ := div_mod_unique i₁.isLt i₂.isLt h1
  have h2 : m * u₁.val + v₁.val = m * u₂.val + v₂.val := by
    rw [Nat.mul_comm m u₁.val, Nat.mul_comm m u₂.val]
    exact huv
  obtain ⟨hu, hv⟩ := div_mod_unique v₁.isLt v₂.isLt h2
  exact ⟨Fin.ext hu, Fin.ext hv, Fin.ext hi⟩

private lemma subdiv_lt {k m : ℕ} (u v : Fin m) (i : Fin (2 * k)) :
    m + 2 * k * (u.val * m + v.val) + i.val < m + 2 * k * m * m := by
  have h1 : u.val * m + v.val + 1 ≤ m * m := by
    have hu : u.val + 1 ≤ m := u.isLt
    have hv : v.val + 1 ≤ m := v.isLt
    calc u.val * m + v.val + 1
        ≤ u.val * m + m := by omega
      _ = (u.val + 1) * m := by ring
      _ ≤ m * m := Nat.mul_le_mul_right m hu
  have h2 : 2 * k * (u.val * m + v.val) + i.val < 2 * k * (u.val * m + v.val + 1) := by
    have hi : i.val < 2 * k := i.isLt
    have hmul : 2 * k * (u.val * m + v.val + 1) = 2 * k * (u.val * m + v.val) + 2 * k := by ring
    omega
  have h3 : 2 * k * (u.val * m + v.val + 1) ≤ 2 * k * (m * m) :=
    Nat.mul_le_mul_left (2 * k) h1
  have h4 : 2 * k * (m * m) = 2 * k * m * m := by ring
  omega

theorem L_meta_291 :
    ∀ (k m : ℕ) (H : SimpleGraph (Fin m)) (T : Finset (Fin m)), 1 ≤ k → (∀ u v : Fin m, H.Adj u v → u ∈ T ∨ v ∈ T) → (∀ t ∈ T, ∃ w : Fin m, H.Adj t w ∧ w ∉ T) → ∀ S : SimpleGraph (Fin (m + 2 * k * m * m)), S = SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k), x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ ((i.val = 0 ∧ y.val = u.val) ∨ (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨ (i.val + 1 = 2 * k ∧ y.val = v.val))) → ∀ F : Finset (Fin (m + 2 * k * m * m)), (∀ j : Fin (m + 2 * k * m * m), j ∈ F ↔ (∃ u ∈ T, j.val = u.val) ∨ ∃ u v : Fin m, ∃ i : Fin (2 * k), u < v ∧ H.Adj u v ∧ j.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ (i.val % 2 = 1 ↔ u ∈ T)) → ∀ x ∈ F, ∃ y : Fin (m + 2 * k * m * m), S.Adj x y ∧ y ∉ F := by
  intro k m H T hk _ hmin S hS F hF x hx
  subst hS
  have hxF := (hF x).mp hx
  rcases hxF with ⟨t, htT, hxt⟩ | ⟨u, v, i, huv, hadj, hxi, hpar⟩
  · obtain ⟨w, htw, hwT⟩ := hmin t htT
    have hne : t ≠ w := H.ne_of_adj htw
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · let i0 : Fin (2 * k) := ⟨0, by omega⟩
      let y : Fin (m + 2 * k * m * m) :=
        ⟨m + 2 * k * (t.val * m + w.val) + i0.val, subdiv_lt t w i0⟩
      refine ⟨y, ?_, ?_⟩
      · rw [SimpleGraph.fromRel_adj]
        refine ⟨?_, Or.inr ?_⟩
        · intro hxy
          have hv : x.val = y.val := congrArg Fin.val hxy
          have htlt : t.val < m := t.isLt
          dsimp [y, i0] at hv
          omega
        · exact ⟨t, w, hlt, htw, i0, rfl, Or.inl ⟨rfl, hxt⟩⟩
      · intro hyF
        rcases (hF y).mp hyF with ⟨u', _, hyu'⟩ | ⟨u', v', i', _, _, hyi', hpar'⟩
        · have hu' : u'.val < m := u'.isLt
          dsimp [y, i0] at hyu'
          omega
        · obtain ⟨hu, _, hi⟩ := subdiv_inj hyi'
          subst hu
          subst hi
          have h0 : i0.val % 2 = 1 := hpar'.mpr htT
          dsimp [i0] at h0
          omega
    · let ilast : Fin (2 * k) := ⟨2 * k - 1, by omega⟩
      let y : Fin (m + 2 * k * m * m) :=
        ⟨m + 2 * k * (w.val * m + t.val) + ilast.val, subdiv_lt w t ilast⟩
      refine ⟨y, ?_, ?_⟩
      · rw [SimpleGraph.fromRel_adj]
        refine ⟨?_, Or.inr ?_⟩
        · intro hxy
          have hv : x.val = y.val := congrArg Fin.val hxy
          have htlt : t.val < m := t.isLt
          dsimp [y, ilast] at hv
          omega
        · refine ⟨w, t, hgt, htw.symm, ilast, rfl, Or.inr (Or.inr ⟨?_, hxt⟩)⟩
          dsimp [ilast]
          omega
      · intro hyF
        rcases (hF y).mp hyF with ⟨u', _, hyu'⟩ | ⟨u', v', i', _, _, hyi', hpar'⟩
        · have hu' : u'.val < m := u'.isLt
          dsimp [y, ilast] at hyu'
          omega
        · obtain ⟨hu, _, hi⟩ := subdiv_inj hyi'
          subst hu
          subst hi
          have hodd : ilast.val % 2 = 1 := by
            dsimp [ilast]
            omega
          exact hwT (hpar'.mp hodd)
  · by_cases hlt : i.val + 1 < 2 * k
    · let j : Fin (2 * k) := ⟨i.val + 1, hlt⟩
      let y : Fin (m + 2 * k * m * m) :=
        ⟨m + 2 * k * (u.val * m + v.val) + j.val, subdiv_lt u v j⟩
      refine ⟨y, ?_, ?_⟩
      · rw [SimpleGraph.fromRel_adj]
        refine ⟨?_, Or.inl ?_⟩
        · intro hxy
          have hv : x.val = y.val := congrArg Fin.val hxy
          dsimp [y, j] at hv
          omega
        · refine ⟨u, v, huv, hadj, i, hxi, Or.inr (Or.inl ⟨hlt, ?_⟩)⟩
          dsimp [y, j]
          omega
      · intro hyF
        rcases (hF y).mp hyF with ⟨u', _, hyu'⟩ | ⟨u', v', i', _, _, hyi', hpar'⟩
        · have hu' : u'.val < m := u'.isLt
          dsimp [y, j] at hyu'
          omega
        · obtain ⟨hu, _, hi⟩ := subdiv_inj hyi'
          subst hu
          subst hi
          have hiff : j.val % 2 = 1 ↔ i.val % 2 = 1 := hpar'.trans hpar.symm
          dsimp [j] at hiff
          omega
    · have hi_ge : 1 ≤ i.val := by
        have hilt : i.val < 2 * k := i.isLt
        omega
      let j : Fin (2 * k) := ⟨i.val - 1, by omega⟩
      let y : Fin (m + 2 * k * m * m) :=
        ⟨m + 2 * k * (u.val * m + v.val) + j.val, subdiv_lt u v j⟩
      refine ⟨y, ?_, ?_⟩
      · rw [SimpleGraph.fromRel_adj]
        refine ⟨?_, Or.inr ?_⟩
        · intro hxy
          have hv : x.val = y.val := congrArg Fin.val hxy
          dsimp [y, j] at hv
          omega
        · refine ⟨u, v, huv, hadj, j, rfl, Or.inr (Or.inl ⟨?_, ?_⟩)⟩
          · dsimp [j]
            omega
          · dsimp [j]
            omega
      · intro hyF
        rcases (hF y).mp hyF with ⟨u', _, hyu'⟩ | ⟨u', v', i', _, _, hyi', hpar'⟩
        · have hu' : u'.val < m := u'.isLt
          dsimp [y, j] at hyu'
          omega
        · obtain ⟨hu, _, hi⟩ := subdiv_inj hyi'
          subst hu
          subst hi
          have hiff : j.val % 2 = 1 ↔ i.val % 2 = 1 := hpar'.trans hpar.symm
          dsimp [j] at hiff
          omega

end PEqualNP.Outside
