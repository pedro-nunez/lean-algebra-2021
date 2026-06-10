import Mathlib

theorem euclidean_division (n m : Nat) (hm : m ≠ 0) :
    ∃! a : Nat, ∃! b : Nat, n = a * m + b ∧ b < m := by
  have hm' : m - 1 + 1 = m := by
    apply Nat.sub_add_cancel
    apply Nat.succ_le_of_lt
    exact Nat.pos_of_ne_zero hm
  have hm_le : m - 1 < m := by
    rw [← hm']
    exact Nat.lt_succ_self (m - 1)
  induction n with
  | zero =>
    -- Proof when n = 0.
    sorry
  | succ n ih =>
    -- Proof for n + 1, assuming the result is true for n.
    sorry
