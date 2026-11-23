import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_685_aux

lemma nat_card_add_subgroup_mul_quotient {G : Type*} [AddCommGroup G] [Finite G]
    (H : AddSubgroup G) :
    Nat.card (G ⧸ H) * Nat.card H = Nat.card G := by
  rw [← AddSubgroup.index_eq_card]
  exact AddSubgroup.index_mul_card H

lemma nat_card_ker_mul_range {G H : Type*} [AddCommGroup G] [AddCommGroup H] [Finite G]
    (f : G →+ H) :
    Nat.card f.range * Nat.card f.ker = Nat.card G := by
  have h1 : Nat.card (G ⧸ f.ker) = Nat.card f.range :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv
  rw [← h1]
  exact nat_card_add_subgroup_mul_quotient f.ker

lemma ker_card_eq_one_or_prime (p : ℕ) [hp : Fact p.Prime] (F : Type) [Field F] [Fintype F]
    [CharP F p] (m : F) (L : F →+ F) (hL : ∀ x, L x = x ^ p - m * x) :
    Nat.card L.ker = 1 ∨ Nat.card L.ker = p := by
  classical
  have hle : Nat.card L.ker ≤ p := by
    let P : Polynomial F := Polynomial.X ^ p - Polynomial.C m * Polynomial.X
    have hPne : P ≠ 0 := by
      intro h0
      have hc : P.coeff p = 0 := by simp [h0]
      have h1 : P.coeff p = 1 := by
        simp [P, Polynomial.coeff_X_pow, Polynomial.coeff_X, hp.out.ne_one.symm]
      rw [h1] at hc
      exact one_ne_zero hc
    have hdeg : P.natDegree ≤ p := by
      refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le (Polynomial.natDegree_X_pow_le p) ?_)
      exact le_trans (Polynomial.natDegree_C_mul_le m Polynomial.X)
        (le_trans Polynomial.natDegree_X_le hp.out.one_le)
    have hmem : ∀ x : L.ker, (x : F) ∈ P.roots.toFinset := by
      intro x
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hPne]
      have hx : L x = 0 := x.2
      rw [hL] at hx
      simpa [P, Polynomial.IsRoot] using hx
    let g : L.ker → P.roots.toFinset := fun x => ⟨x.1, hmem x⟩
    have hginj : Function.Injective g := by
      intro a b hab
      have hval : (g a).1 = (g b).1 := congrArg Subtype.val hab
      exact Subtype.ext hval
    have hcard1 : Nat.card L.ker ≤ Nat.card P.roots.toFinset :=
      Nat.card_le_card_of_injective g hginj
    have hcard2 : Nat.card P.roots.toFinset = P.roots.toFinset.card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    have hcard3 : P.roots.toFinset.card ≤ P.roots.card := Multiset.toFinset_card_le P.roots
    have hcard4 : P.roots.card ≤ P.natDegree := Polynomial.card_roots' P
    omega
  by_cases hzero : ∀ x ∈ L.ker, x = 0
  · left
    have : Subsingleton L.ker := ⟨fun a b => Subtype.ext (by rw [hzero a.1 a.2, hzero b.1 b.2])⟩
    exact Nat.card_unique
  · right
    push Not at hzero
    rcases hzero with ⟨u, hu_mem, hu_ne⟩
    let i : ZMod p →+* F := ZMod.castHom (dvd_refl p) F
    have hmap : ∀ c : ZMod p, i c * u ∈ L.ker := by
      intro c
      change L (i c * u) = 0
      rw [hL, mul_pow, ← map_pow, ZMod.pow_card]
      have hu0 : u ^ p - m * u = 0 := by
        rw [← hL]
        exact hu_mem
      calc
        i c * u ^ p - m * (i c * u) = i c * (u ^ p - m * u) := by ring
        _ = i c * 0 := by rw [hu0]
        _ = 0 := mul_zero _
    let f : ZMod p → L.ker := fun c => ⟨i c * u, hmap c⟩
    have hfinj : Function.Injective f := by
      intro a b hab
      have h1 : i a * u = i b * u := congrArg Subtype.val hab
      exact i.injective (mul_right_cancel₀ hu_ne h1)
    have hge : p ≤ Nat.card L.ker := by
      have h1 : Nat.card (ZMod p) ≤ Nat.card L.ker := Nat.card_le_card_of_injective f hfinj
      rwa [Nat.card_zmod] at h1
    omega

end PEqualNP.Outside.L_meta_685_aux

theorem PEqualNP.Outside.L_meta_685 :
    ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Fintype F] [CharP F p]
    (A : AddSubgroup F),
    (∀ a ∈ A, ∀ c : ZMod p, (ZMod.cast c : F) * a ∈ A) →
    ∀ m k : F,
      Nat.card {x : F // x ^ p - m * x + k ∈ A} = 0 ∨
      Nat.card {x : F // x ^ p - m * x + k ∈ A} = Nat.card A ∨
      Nat.card {x : F // x ^ p - m * x + k ∈ A} = p * Nat.card A := by
  intro p hp F _ _ _ A _ m k
  let L : F →+ F :=
    { toFun := fun x => x ^ p - m * x
      map_zero' := by simp [hp.out.ne_zero]
      map_add' := fun x y => by
        rw [add_pow_char, mul_add]
        ring }
  by_cases hne : ∃ x₀ : F, L x₀ + k ∈ A
  · rcases hne with ⟨x₀, hx₀⟩
    let K : AddSubgroup F := A.comap L
    have hcard_eq : Nat.card {x : F // x ^ p - m * x + k ∈ A} = Nat.card K := by
      refine Nat.card_congr
        { toFun := fun x => ⟨x.1 - x₀, ?_⟩
          invFun := fun y => ⟨y.1 + x₀, ?_⟩
          left_inv := fun x => Subtype.ext (sub_add_cancel x.1 x₀)
          right_inv := fun y => Subtype.ext (add_sub_cancel_right y.1 x₀) }
      · change L (x.1 - x₀) ∈ A
        have h1 : L (x.1 - x₀) = (x.1 ^ p - m * x.1 + k) - (L x₀ + k) := by
          rw [map_sub]
          change x.1 ^ p - m * x.1 - L x₀ = (x.1 ^ p - m * x.1 + k) - (L x₀ + k)
          ring
        rw [h1]
        exact A.sub_mem x.2 hx₀
      · have h1 : (y.1 + x₀) ^ p - m * (y.1 + x₀) + k = L y.1 + (L x₀ + k) := by
          have h2 : L (y.1 + x₀) = L y.1 + L x₀ := map_add L y.1 x₀
          change L (y.1 + x₀) + k = L y.1 + (L x₀ + k)
          rw [h2, add_assoc]
        rw [h1]
        exact A.add_mem y.2 hx₀
    rw [hcard_eq]
    let φ : K →+ (A ⊓ L.range : AddSubgroup F) :=
      { toFun := fun y => ⟨L y.1, ⟨y.2, ⟨y.1, rfl⟩⟩⟩
        map_zero' := Subtype.ext (map_zero L)
        map_add' := fun a b => Subtype.ext (map_add L a.1 b.1) }
    have hφ_surj : Function.Surjective φ := by
      rintro ⟨z, hzA, ⟨y, rfl⟩⟩
      exact ⟨⟨y, hzA⟩, rfl⟩
    have hφ_range : Nat.card φ.range = Nat.card (A ⊓ L.range : AddSubgroup F) := by
      have htop : φ.range = ⊤ := AddMonoidHom.range_eq_top.mpr hφ_surj
      rw [htop]
      exact Nat.card_congr AddSubgroup.topEquiv.toEquiv
    have hφ_ker : Nat.card φ.ker = Nat.card L.ker := by
      refine Nat.card_congr
        { toFun := fun y => ⟨y.1.1, by
            have h0 : φ y.1 = 0 := y.2
            exact congrArg Subtype.val h0⟩
          invFun := fun z => ⟨⟨z.1, by
            change L z.1 ∈ A
            have hz : L z.1 = 0 := z.2
            rw [hz]
            exact A.zero_mem⟩, Subtype.ext z.2⟩
          left_inv := fun y => Subtype.ext (Subtype.ext rfl)
          right_inv := fun z => Subtype.ext rfl }
    have hK_card : Nat.card K = Nat.card L.ker * Nat.card (A ⊓ L.range : AddSubgroup F) := by
      have hmul := PEqualNP.Outside.L_meta_685_aux.nat_card_ker_mul_range φ
      rw [hφ_range, hφ_ker] at hmul
      linarith
    rcases PEqualNP.Outside.L_meta_685_aux.ker_card_eq_one_or_prime p F m L (fun _ => rfl) with
      hker1 | hkerp
    · right
      left
      have hker_bot : L.ker = ⊥ := by
        ext x
        simp only [AddSubgroup.mem_bot]
        constructor
        · intro hx
          have hsub : Subsingleton L.ker := (Nat.card_eq_one_iff_unique.mp hker1).1
          exact congrArg Subtype.val (@Subsingleton.elim _ hsub ⟨x, hx⟩ ⟨0, L.ker.zero_mem⟩)
        · rintro rfl
          exact L.ker.zero_mem
      have hL_inj : Function.Injective L := (AddMonoidHom.ker_eq_bot_iff L).mp hker_bot
      have hL_surj : Function.Surjective L := Finite.injective_iff_surjective.mp hL_inj
      have hL_range : L.range = ⊤ := AddMonoidHom.range_eq_top.mpr hL_surj
      rw [hK_card, hker1, one_mul, hL_range, inf_top_eq]
    · right
      let ψ : A →+ F ⧸ L.range := (QuotientAddGroup.mk' L.range).comp A.subtype
      have hψ_ker : Nat.card ψ.ker = Nat.card (A ⊓ L.range : AddSubgroup F) := by
        refine Nat.card_congr
          { toFun := fun a => ⟨a.1.1, ⟨a.1.2, (QuotientAddGroup.eq_zero_iff a.1.1).mp a.2⟩⟩
            invFun := fun a => ⟨⟨a.1, a.2.1⟩, (QuotientAddGroup.eq_zero_iff a.1).mpr a.2.2⟩
            left_inv := fun a => Subtype.ext (Subtype.ext rfl)
            right_inv := fun a => Subtype.ext rfl }
      have hA_mul : Nat.card ψ.range * Nat.card (A ⊓ L.range : AddSubgroup F) = Nat.card A := by
        have h := PEqualNP.Outside.L_meta_685_aux.nat_card_ker_mul_range ψ
        rwa [hψ_ker] at h
      have hquot_card : Nat.card (F ⧸ L.range) = p := by
        have h1 := PEqualNP.Outside.L_meta_685_aux.nat_card_ker_mul_range L
        have h2 := PEqualNP.Outside.L_meta_685_aux.nat_card_add_subgroup_mul_quotient L.range
        rw [hkerp] at h1
        have hpos : 0 < Nat.card L.range := Nat.card_pos
        nlinarith
      have hdvd : Nat.card ψ.range ∣ p := by
        rw [← hquot_card]
        have h3 := PEqualNP.Outside.L_meta_685_aux.nat_card_add_subgroup_mul_quotient ψ.range
        exact ⟨Nat.card ((F ⧸ L.range) ⧸ ψ.range), by linarith⟩
      rcases hp.out.eq_one_or_self_of_dvd (Nat.card ψ.range) hdvd with h1 | hp'
      · right
        rw [h1, one_mul] at hA_mul
        rw [hK_card, hkerp, hA_mul]
      · left
        rw [hp'] at hA_mul
        rw [hK_card, hkerp, hA_mul]
  · left
    classical
    have : IsEmpty {x : F // x ^ p - m * x + k ∈ A} := ⟨fun x => hne ⟨x.1, x.2⟩⟩
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_eq_zero
