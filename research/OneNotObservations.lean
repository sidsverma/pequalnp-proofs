import PEqualNP.Defs

theorem replace_not_by_true {α : Type} (f g : α → Bool) (F : α → Bool → Bool)
    (mono : ∀ x, F x false = true → F x true = true)
    (correct : ∀ x, F x (!g x) = f x)
    (negative : ∀ x, f x = false → g x = false) :
    ∀ x, F x true = f x := by
  intro x
  cases hg : g x with
  | false => simpa [hg] using correct x
  | true =>
    cases hf : f x with
    | false =>
      have impossible := negative x hf
      simp [hg] at impossible
    | true =>
      apply mono x
      simpa [hg, hf] using correct x

theorem replace_not_by_false {α : Type} (f g : α → Bool) (F : α → Bool → Bool)
    (mono : ∀ x, F x false = true → F x true = true)
    (correct : ∀ x, F x (!g x) = f x)
    (positive : ∀ x, f x = true → g x = true) :
    ∀ x, F x false = f x := by
  intro x
  cases hg : g x with
  | true => simpa [hg] using correct x
  | false =>
    cases hf : f x with
    | true =>
      have impossible := positive x hf
      simp [hg] at impossible
    | false =>
      cases hout : F x false with
      | false => rfl
      | true =>
        have contradiction := mono x hout
        have off : F x true = false := by simpa [hg, hf] using correct x
        simp [off] at contradiction
