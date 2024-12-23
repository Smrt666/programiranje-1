def reverse {A : Type} : List A → List A :=
  fun l =>
    match l with
    | [] => []
    | h :: t => reverse t ++ [h]

def aux {A : Type} : List A → List A → List A :=
  fun l acc =>
    match l with
    | [] => acc
    | h :: t => aux t (h :: acc)

def reverse' {A : Type} : List A → List A :=
  fun l => aux l []


theorem rev_aux {A : Type} : ∀ {l : List A}, ∀ {acc : List A},
  (reverse l) ++ acc = aux l acc := by
  intros l
  induction l with
  | nil =>
    simp [reverse, aux]
  | cons h t ih =>
    intro acc
    simp [aux, reverse]
    rw [ih]

theorem revs_eq {A : Type} {l : List A} : reverse l = reverse' l :=
  by
    rw [reverse']
    rw [←rev_aux]
    simp [List.concat]
