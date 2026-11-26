-- Sample Lean 4 proof with branching (cases / induction / have) for Seto SM visualization

theorem list_map_append_length {α β : Type} (f : α → β) (xs ys : List α) :
    (xs.map f ++ ys.map f).length = xs.length + ys.length := by
  induction xs with
  | nil =>
    simp only [List.map_nil, List.nil_append, List.length_nil, Nat.zero_add]
    have h_len : (ys.map f).length = ys.length := by
      induction ys with
      | nil =>
        simp
      | cons y yt ihy =>
        simp [List.map_cons, List.length_cons, ihy]
    exact h_len
  | cons x xt ih =>
    simp only [List.map_cons, List.cons_append, List.length_cons]
    rw [ih]
    omega
