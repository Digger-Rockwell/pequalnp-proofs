import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_127_aux

def sL {n : ℕ} (e : Fin n × Bool) : Fin n × Bool :=
  (e.1, !e.2)

lemma sL_invol {n : ℕ} (e : Fin n × Bool) : sL (sL e) = e := by
  rcases e with ⟨r, b⟩
  cases b <;> rfl

lemma sL_ne {n : ℕ} (e : Fin n × Bool) : sL e ≠ e := by
  rcases e with ⟨r, b⟩
  cases b <;> simp [sL]

def sR {n : ℕ} (π : Equiv.Perm (Fin n × Bool)) (e : Fin n × Bool) : Fin n × Bool :=
  π.symm (sL (π e))

lemma sR_invol {n : ℕ} (π : Equiv.Perm (Fin n × Bool)) (e : Fin n × Bool) :
    sR π (sR π e) = e := by
  simp [sR, sL_invol]

lemma sR_ne {n : ℕ} (π : Equiv.Perm (Fin n × Bool)) (e : Fin n × Bool) :
    sR π e ≠ e := by
  intro h
  apply sL_ne (π e)
  have h' := congrArg π h
  simpa [sR] using h'

def T {n : ℕ} (π : Equiv.Perm (Fin n × Bool)) : Equiv.Perm (Fin n × Bool) :=
  { toFun := fun e => sR π (sL e)
    invFun := fun e => sL (sR π e)
    left_inv := fun e => by simp [sL_invol, sR_invol]
    right_inv := fun e => by simp [sL_invol, sR_invol] }

lemma pow_T_ne_sL {n : ℕ} (π : Equiv.Perm (Fin n × Bool)) :
    ∀ (k : ℕ) (e : Fin n × Bool), ((T π) ^ k) e ≠ sL e := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro e
    match k with
    | 0 =>
      simpa using (sL_ne e).symm
    | 1 =>
      simpa [T] using sR_ne π (sL e)
    | m + 2 =>
      intro h
      have hpow : ((T π) ^ (m + 2)) e = T π (((T π) ^ m) (T π e)) := by
        have h1 : (T π) ^ (m + 2) = T π * ((T π) ^ m * T π) := by
          rw [pow_succ, pow_succ', mul_assoc]
        rw [h1]
        rfl
      rw [hpow] at h
      have h2 := congrArg (T π).symm h
      rw [Equiv.symm_apply_apply] at h2
      have h3 : (T π).symm (sL e) = sL (T π e) := rfl
      rw [h3] at h2
      exact ih m (by omega) (T π e) h2

lemma zpow_T_ne_sL {n : ℕ} (π : Equiv.Perm (Fin n × Bool)) (z : ℤ) (e : Fin n × Bool) :
    ((T π) ^ z) e ≠ sL e := by
  cases z with
  | ofNat k =>
    simpa using pow_T_ne_sL π k e
  | negSucc k =>
    intro h
    have h1 := congrArg ((T π) ^ (k + 1)) h
    have h2 : ((T π) ^ (k + 1)) (((T π) ^ (Int.negSucc k)) e) = e := by
      rw [zpow_negSucc]
      exact ((T π) ^ (k + 1)).apply_symm_apply e
    rw [h2] at h1
    exact pow_T_ne_sL π (k + 1) (sL e) (by rw [sL_invol, ← h1])

noncomputable def orb {n : ℕ} (π : Equiv.Perm (Fin n × Bool)) (e : Fin n × Bool) :
    Finset (Fin n × Bool) :=
  @Finset.filter _ (fun x => Equiv.Perm.SameCycle (T π) e x) (Classical.decPred _) Finset.univ

lemma mem_orb {n : ℕ} (π : Equiv.Perm (Fin n × Bool)) (e x : Fin n × Bool) :
    x ∈ orb π e ↔ Equiv.Perm.SameCycle (T π) e x := by
  simp [orb]

lemma self_mem_orb {n : ℕ} (π : Equiv.Perm (Fin n × Bool)) (e : Fin n × Bool) :
    e ∈ orb π e := by
  rw [mem_orb]

lemma orb_eq_of_sameCycle {n : ℕ} (π : Equiv.Perm (Fin n × Bool))
    {e₁ e₂ : Fin n × Bool} (h : Equiv.Perm.SameCycle (T π) e₁ e₂) :
    orb π e₁ = orb π e₂ := by
  ext x
  simp only [mem_orb]
  exact ⟨fun hx => h.symm.trans hx, fun hx => h.trans hx⟩

lemma orb_sR {n : ℕ} (π : Equiv.Perm (Fin n × Bool)) (e : Fin n × Bool) :
    orb π (sR π e) = orb π (sL e) := by
  apply orb_eq_of_sameCycle
  refine ⟨-1, ?_⟩
  change (T π).symm (sR π e) = sL e
  simp [T, sR_invol]

lemma orb_sL_sR {n : ℕ} (π : Equiv.Perm (Fin n × Bool)) (e : Fin n × Bool) :
    orb π (sL (sR π e)) = orb π e := by
  apply orb_eq_of_sameCycle
  refine ⟨1, ?_⟩
  change T π (sL (sR π e)) = e
  simp [T, sL_invol, sR_invol]

lemma orb_disjoint_sL {n : ℕ} (π : Equiv.Perm (Fin n × Bool)) (e : Fin n × Bool) :
    Disjoint (orb π e) (orb π (sL e)) := by
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  rw [mem_orb] at hx1 hx2
  rcases hx1.trans hx2.symm with ⟨z, hz⟩
  exact zpow_T_ne_sL π z e hz

def enc {n : ℕ} (e : Fin n × Bool) : ℕ :=
  e.1.val * 2 + if e.2 then 1 else 0

lemma enc_injective {n : ℕ} : Function.Injective (@enc n) := by
  intro a b h
  rcases a with ⟨ar, ab⟩
  rcases b with ⟨br, bb⟩
  simp only [enc] at h
  cases ab <;> cases bb <;> simp at h
  · exact Prod.ext (Fin.ext (by omega)) rfl
  · omega
  · omega
  · exact Prod.ext (Fin.ext (by omega)) rfl

noncomputable def key {n : ℕ} (π : Equiv.Perm (Fin n × Bool)) (e : Fin n × Bool) : ℕ :=
  ((orb π e).image enc).min' (Finset.Nonempty.image ⟨e, self_mem_orb π e⟩ enc)

lemma key_eq_of_orb_eq {n : ℕ} (π : Equiv.Perm (Fin n × Bool))
    {e₁ e₂ : Fin n × Bool} (h : orb π e₁ = orb π e₂) :
    key π e₁ = key π e₂ := by
  simp [key, h]

lemma key_sR {n : ℕ} (π : Equiv.Perm (Fin n × Bool)) (e : Fin n × Bool) :
    key π (sR π e) = key π (sL e) :=
  key_eq_of_orb_eq π (orb_sR π e)

lemma key_sL_sR {n : ℕ} (π : Equiv.Perm (Fin n × Bool)) (e : Fin n × Bool) :
    key π (sL (sR π e)) = key π e :=
  key_eq_of_orb_eq π (orb_sL_sR π e)

lemma key_ne_sL {n : ℕ} (π : Equiv.Perm (Fin n × Bool)) (e : Fin n × Bool) :
    key π e ≠ key π (sL e) := by
  intro h
  have h1 : key π e ∈ (orb π e).image enc := Finset.min'_mem _ _
  have h2 : key π (sL e) ∈ (orb π (sL e)).image enc := Finset.min'_mem _ _
  rw [Finset.mem_image] at h1 h2
  rcases h1 with ⟨x, hx, hxe⟩
  rcases h2 with ⟨y, hy, hye⟩
  have hxy : x = y := enc_injective (by omega)
  subst hxy
  exact Finset.disjoint_left.mp (orb_disjoint_sL π e) hx hy

noncomputable def col {n : ℕ} (π : Equiv.Perm (Fin n × Bool)) (e : Fin n × Bool) : Bool :=
  decide (key π e < key π (sL e))

lemma col_sL {n : ℕ} (π : Equiv.Perm (Fin n × Bool)) (e : Fin n × Bool) :
    col π (sL e) = !(col π e) := by
  simp only [col, sL_invol]
  have hne := key_ne_sL π e
  by_cases hlt : key π e < key π (sL e)
  · have hnot : ¬ key π (sL e) < key π e := by omega
    simp [hlt, hnot]
  · have hgt : key π (sL e) < key π e := by omega
    simp [hlt, hgt]

lemma col_sR {n : ℕ} (π : Equiv.Perm (Fin n × Bool)) (e : Fin n × Bool) :
    col π (sR π e) = !(col π e) := by
  have h1 : col π (sR π e) = col π (sL e) := by
    simp only [col, key_sR, key_sL_sR, sL_invol]
  rw [h1, col_sL]

lemma bne_col {n : ℕ} (π : Equiv.Perm (Fin n × Bool)) (ρ : Fin n) (β : Bool) :
    (β != col π (ρ, false)) = col π (ρ, β) := by
  cases β
  · simp
  · have h := col_sL π (ρ, false)
    simp only [sL, Bool.not_false] at h
    simpa using h.symm

lemma half_inj {n : ℕ} (π : Equiv.Perm (Fin n × Bool)) (c : Bool) :
    Function.Injective (fun ρ : Fin n => (π (ρ, c != col π (ρ, false))).1) := by
  intro ρ₁ ρ₂ h
  set e₁ : Fin n × Bool := (ρ₁, c != col π (ρ₁, false))
  set e₂ : Fin n × Bool := (ρ₂, c != col π (ρ₂, false))
  have hc₁ : col π e₁ = c := by
    rw [← bne_col]
    cases c <;> cases col π (ρ₁, false) <;> rfl
  have hc₂ : col π e₂ = c := by
    rw [← bne_col]
    cases c <;> cases col π (ρ₂, false) <;> rfl
  by_cases hb : (π e₁).2 = (π e₂).2
  · have hpe : π e₁ = π e₂ := Prod.ext h hb
    have he : e₁ = e₂ := π.injective hpe
    exact congrArg Prod.fst he
  · exfalso
    have hb' : (π e₂).2 = !(π e₁).2 := by
      cases h1 : (π e₁).2 <;> cases h2 : (π e₂).2 <;> simp_all
    have hpe : π e₂ = sL (π e₁) := Prod.ext h.symm hb'
    have he : e₂ = sR π e₁ := by
      unfold sR
      rw [← hpe, Equiv.symm_apply_apply]
    have hcol := col_sR π e₁
    rw [← he, hc₁, hc₂] at hcol
    cases c <;> simp at hcol

end PEqualNP.Outside.L_lib_127_aux

theorem PEqualNP.Outside.L_lib_127 :
    ∀ (n : ℕ) (π : Equiv.Perm (Fin n × Bool)), ∃ b : Fin n → Bool, ∃ π₀ π₁ : Equiv.Perm (Fin n), ∀ (ρ : Fin n) (β : Bool), (π (ρ, β)).1 = (if (β != b ρ) = true then π₁ else π₀) ρ := by
  intro n π
  let b : Fin n → Bool := fun ρ => PEqualNP.Outside.L_lib_127_aux.col π (ρ, false)
  let π₀ : Equiv.Perm (Fin n) :=
    Equiv.ofBijective (fun ρ : Fin n => (π (ρ, false != b ρ)).1)
      (Finite.injective_iff_bijective.mp (PEqualNP.Outside.L_lib_127_aux.half_inj π false))
  let π₁ : Equiv.Perm (Fin n) :=
    Equiv.ofBijective (fun ρ : Fin n => (π (ρ, true != b ρ)).1)
      (Finite.injective_iff_bijective.mp (PEqualNP.Outside.L_lib_127_aux.half_inj π true))
  refine ⟨b, π₀, π₁, ?_⟩
  intro ρ β
  cases β <;> cases hb : b ρ <;> simp [π₀, π₁, hb]
