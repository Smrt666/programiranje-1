-- Izomorfizmi

theorem eq1 {A B : Prop} : (A ∧ B) ↔ (B ∧ A) :=
  by
    apply Iff.intro
    intro h
    symm at h
    exact h
    intro h
    symm at h
    exact h


theorem eq2 {A B : Prop} : (A ∨ B) ↔ (B ∨ A) :=
  by
    apply Iff.intro
    intro h
    symm at h
    exact h
    intro h
    symm at h
    exact h

theorem eq3 {A B C : Prop} : (A ∧ (B ∧ C)) ↔ (B ∧ (A ∧ C)) :=
  by
    apply Iff.intro
    intro h
    have h1 : B ∧ C := h.right
    have h2 : A := h.left
    have h3 : A ∧ C := ⟨h2, h1.right⟩
    exact ⟨h1.left, h3⟩
    intro h
    have h1 : A ∧ C := h.right
    have h2 : B := h.left
    have h3 : B ∧ C := ⟨h2, h1.right⟩
    exact ⟨h1.left, h3⟩

theorem eq4 {A B C : Prop} : (A ∨ (B ∨ C)) ↔ (B ∨ (A ∨ C)) :=
  by
    apply Iff.intro
    intro abc
    cases abc
    case inl a =>
      right
      left
      exact a
    case inr bc =>
      cases bc
      case inl b =>
        left
        exact b
      case inr c =>
        right
        right
        exact c
    intro bac
    cases bac
    case inl b =>
      right
      left
      exact b
    case inr ac =>
      cases ac
      case inl a =>
        left
        exact a
      case inr c =>
        right
        right
        exact c

theorem eq5 {A B C : Prop} : A ∧ (B ∨ C) ↔ (A ∧ B) ∨ (A ∧ C) :=
  sorry

theorem eq6 {A B C : Prop} : (B ∨ C) → A ↔ (B → A) ∧ (C → A) := by
  constructor
  intro h
  constructor
  intro hb
  apply h
  left
  exact hb
  intro hc
  have bc : B ∨ C := Or.inr hc
  exact h bc

  intro h bc
  cases bc
  case inl b =>
    exact h.left b
  case inr c =>
    exact h.right c

theorem eq7 {A B C : Prop} : C → (A ∧ B) ↔ (C → A) ∧ (C → B) :=
  sorry
