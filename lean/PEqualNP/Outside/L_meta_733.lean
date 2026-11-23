import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_733 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (X : Set (Fin n)),
      (∀ u v, G.Adj u v → (u ∈ X ↔ v ∉ X)) →
      ∀ I : Set (Fin n),
        ((∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) ∧ (∀ v, v ∉ I → ∃ u ∈ I, G.Adj v u)) ↔
        ∃ B : Set (Fin n), (∀ b ∈ B, b ∉ X) ∧
          (∀ y, y ∉ X → ((∀ x, G.Adj y x → ∃ b ∈ B, G.Adj x b) ↔ y ∈ B)) ∧
          ∀ v, v ∈ I ↔ (v ∈ B ∨ (v ∈ X ∧ ∀ b ∈ B, ¬ G.Adj v b)) := by
  intro n G X hbip I
  constructor
  · rintro ⟨hind, hmax⟩
    refine ⟨{b | b ∈ I ∧ b ∉ X}, ?_, ?_, ?_⟩
    · intro b hb
      exact hb.2
    · intro y hyX
      constructor
      · intro hsat
        refine ⟨?_, hyX⟩
        by_contra hyI
        obtain ⟨u, huI, hyu⟩ := hmax y hyI
        obtain ⟨b, hbB, hub⟩ := hsat u hyu
        exact hind u huI b hbB.1 hub
      · intro hyB x hyx
        exact ⟨y, hyB, (G.adj_comm y x).mp hyx⟩
    · intro v
      constructor
      · intro hvI
        by_cases hvX : v ∈ X
        · right
          exact ⟨hvX, fun b hbB => hind v hvI b hbB.1⟩
        · left
          exact ⟨hvI, hvX⟩
      · rintro (⟨hvI, _⟩ | ⟨hvX, hno⟩)
        · exact hvI
        · by_contra hvI
          obtain ⟨u, huI, hvu⟩ := hmax v hvI
          have huX : u ∉ X := (hbip v u hvu).mp hvX
          exact hno u ⟨huI, huX⟩ hvu
  · rintro ⟨B, hBX, hsat, hI⟩
    constructor
    · intro u huI v hvI huv
      rcases (hI u).mp huI with huB | ⟨huX, huNo⟩
      · rcases (hI v).mp hvI with hvB | ⟨_, hvNo⟩
        · exact (hBX u huB) ((hbip u v huv).mpr (hBX v hvB))
        · exact hvNo u huB ((G.adj_comm u v).mp huv)
      · rcases (hI v).mp hvI with hvB | ⟨hvX, _⟩
        · exact huNo v hvB huv
        · exact (hbip u v huv).mp huX hvX
    · intro v hvI
      by_cases hvX : v ∈ X
      · have hnot : ¬ ∀ b ∈ B, ¬ G.Adj v b := by
          intro hall
          exact hvI ((hI v).mpr (Or.inr ⟨hvX, hall⟩))
        push Not at hnot
        obtain ⟨b, hbB, hvb⟩ := hnot
        exact ⟨b, (hI b).mpr (Or.inl hbB), hvb⟩
      · have hvB : v ∉ B := fun hvB => hvI ((hI v).mpr (Or.inl hvB))
        have hnot : ¬ ∀ x, G.Adj v x → ∃ b ∈ B, G.Adj x b := by
          intro hall
          exact hvB ((hsat v hvX).mp hall)
        push Not at hnot
        obtain ⟨x, hvx, hno⟩ := hnot
        have hxX : x ∈ X := by
          by_contra hxX
          exact hvX ((hbip v x hvx).mpr hxX)
        exact ⟨x, (hI x).mpr (Or.inr ⟨hxX, hno⟩), hvx⟩
