import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_684 :
    ∀ (G H : Type) [AddCommGroup G] [AddCommGroup H] [Finite G] [Finite H]
    (L : G →+ H) (A : AddSubgroup H) (g : H),
    Nat.card {t : G // L t - g ∈ A} = 0 ∨
    Nat.card {t : G // L t - g ∈ A} = Nat.card L.ker * Nat.card (A ⊓ L.range : AddSubgroup H) := by
  intro G H _ _ _ _ L A g
  by_cases hne : Nonempty {t : G // L t - g ∈ A}
  · right
    rcases hne with ⟨⟨t0, ht0⟩⟩
    let K : AddSubgroup G := A.comap L
    have heq1 : {t : G // L t - g ∈ A} ≃ K :=
      { toFun := fun t => ⟨t.1 - t0, by
          show L (t.1 - t0) ∈ A
          rw [map_sub]
          have hsub : L t.1 - L t0 = (L t.1 - g) - (L t0 - g) := by abel
          rw [hsub]
          exact A.sub_mem t.2 ht0⟩
        invFun := fun u => ⟨u.1 + t0, by
          rw [map_add]
          have hadd : L u.1 + L t0 - g = L u.1 + (L t0 - g) := by abel
          rw [hadd]
          exact A.add_mem u.2 ht0⟩
        left_inv := fun t => Subtype.ext (sub_add_cancel t.1 t0)
        right_inv := fun u => Subtype.ext (add_sub_cancel_right u.1 t0) }
    rw [Nat.card_congr heq1]
    let f : K →+ H := L.comp K.subtype
    have hker : f.ker ≃ L.ker :=
      { toFun := fun x => ⟨x.1.1, x.2⟩
        invFun := fun y => ⟨⟨y.1, by
          show L y.1 ∈ A
          rw [y.2]
          exact A.zero_mem⟩, y.2⟩
        left_inv := fun x => by
          ext
          rfl
        right_inv := fun y => by
          ext
          rfl }
    have hrange : f.range = A ⊓ L.range := by
      ext h
      constructor
      · rintro ⟨⟨u, hu⟩, rfl⟩
        exact ⟨hu, u, rfl⟩
      · rintro ⟨hA, u, rfl⟩
        exact ⟨⟨u, hA⟩, rfl⟩
    have hcard_range : Nat.card f.range = Nat.card (A ⊓ L.range : AddSubgroup H) := by
      rw [hrange]
    have hq : Nat.card (K ⧸ f.ker) = Nat.card f.range :=
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv
    have hlag : Nat.card K = Nat.card (K ⧸ f.ker) * Nat.card f.ker :=
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker
    rw [hlag, hq, hcard_range, Nat.card_congr hker, mul_comm]
  · left
    have : IsEmpty {t : G // L t - g ∈ A} := not_nonempty_iff.mp hne
    simp
