import Mathlib

theorem euclidean_division (n m : Nat) (hm : m ≠ 0) :
    ∃! a : Nat, ∃! b : Nat, n = a * m + b ∧ b < m := by
  have hm' : m - 1 + 1 = m := by
    -- Recall that when working with natural numbers in Lean m - 1 + 1 would be 1 if m = 0.
    apply Nat.sub_add_cancel
    apply Nat.succ_le_of_lt
    exact Nat.pos_of_ne_zero hm
  have hm_le : m - 1 < m := by
    rw [← hm']
    exact Nat.lt_succ_self (m - 1)
  induction n with
  | zero =>
    -- Proof when n = 0.
    use 0
    constructor <;> dsimp
    · -- Proof that a = 0 works, i.e., for a = 0 there exists a unique b such that...
      use 0
      constructor <;> dsimp
      · -- Proof that b = 0 works.
        constructor
        · simp
        · exact Nat.zero_lt_of_ne_zero hm
      · -- Proof that b = 0 is the unique possible b for a = 0.
        intros y hy
        simp at hy
        have y_is_zero := hy.left
        symm
        exact y_is_zero
    · -- Proof that a = 0 is the unique possible a such that there exists a unique b...
      intros y hy
      cases hy with
      | intro b hb =>
        rcases hb with ⟨hb_exists, hb_unique⟩
        have hb_eq := hb_exists.left
        have b_eq_zero : b = 0 := by
          symm at hb_eq
          exact Nat.eq_zero_of_add_eq_zero_left hb_eq
        rw [b_eq_zero] at hb_eq
        simp at hb_eq
        rcases hb_eq with y_zero | m_zero
        · exact y_zero
        · contradiction
  | succ n ih =>
    -- Proof for n + 1, assuming the result is true for n.
    rcases ih with ⟨a, ha_exists, ha_unique⟩
    rcases ha_exists with ⟨b, hb_exists, hb_unique⟩
    rcases hb_exists with ⟨ih_ab, hb_lt⟩
    -- From the induction hypothesis we have obtained unique a and b such that n = a * m + b with b < m.
    by_cases b_case : b < m - 1
    -- Case distinction: b < m - 1 or not, i.e., b < m - 1 or b = m - 1.
    · -- Proof when b < m - 1.
      use a
      constructor <;> dsimp
      · -- Proof that a still works for n + 1.
        use b + 1
        constructor <;> dsimp
        · -- Proof that b + 1 is satisfies n + 1 = a * m + (b + 1) and b + 1 < m.
          constructor
          · rw [ih_ab]
            ring
          · exact Nat.add_lt_of_lt_sub b_case
        · -- Proof that b + 1 is the unique number satisfying both conditions.
          intros y hy
          rcases hy with ⟨hy_left, hy_right⟩
          rw [ih_ab] at hy_left
          rw [Nat.add_assoc] at hy_left
          symm at hy_left
          exact Nat.add_left_cancel hy_left
      · -- Proof that a is the unique number for which there exists c such that n + 1 = a * m + c with c < m.
        intros y hy
        rcases hy with ⟨c, hc_exists, hc_unique⟩
        rcases hc_exists with ⟨hc_left, hc_right⟩
        cases c with
        | zero =>
          -- Proof that c = 0 is not possible.
          exfalso
          cases y with
          -- Case distinction on y as well.
          | zero =>
            simp at hc_left
          | succ y' =>
            dsimp at ha_unique
            dsimp at hb_unique
            dsimp at hc_unique
            have claim1 : b = m - 1 := by
              -- This will contradict the current assumption that b < m - 1.
              symm
              apply hb_unique (m - 1)
              constructor
              -- Proof that m - 1 satisfies the two defining properties of b.
              · -- Proof that n = a * m + (m - 1).
                simp at hc_left
                have hc_left' : n + 1 = (y' * m + (m - 1)) + 1 := by
                  calc
                    n + 1 = Nat.succ y' * m := hc_left
                    _ = y' * m + m := by rw [Nat.succ_mul]
                    _ = y' * m + ((m - 1) + 1) := by rw [hm']
                    _ = (y' * m + (m - 1)) + 1 := by rw [← Nat.add_assoc]
                have claim2 : y' = a := by
                  apply ha_unique y'
                  use m - 1
                  constructor <;> dsimp
                  · constructor
                    · exact Nat.add_right_cancel hc_left'
                    · exact hm_le
                  · intros z hz
                    rcases hz with ⟨hz_left, hz_right⟩
                    rw [hz_left] at hc_left'
                    have hc_left'' := Nat.add_right_cancel hc_left'
                    exact Nat.add_left_cancel hc_left''
                rw [claim2] at hc_left'
                exact Nat.add_right_cancel hc_left'
              · -- Proof that m - 1 < m.
                exact hm_le
            -- Now use b = m - 1 to obtain a contradiction and prove False.
            rw [← claim1] at b_case
            exact Nat.lt_irrefl b b_case
        | succ c' =>
          -- Proof of uniqueness of a when c > 0.
          apply ha_unique
          use c'
          constructor <;> dsimp
          · constructor
            · rw [← Nat.add_assoc] at hc_left
              exact Nat.add_right_cancel hc_left
            · linarith
          · intros d hd
            rcases hd with ⟨hd_left, hd_right⟩
            have hc_left' : n = y * m + c' := by
              rw [← Nat.add_assoc] at hc_left
              exact Nat.add_right_cancel hc_left
            rw [hc_left'] at hd_left
            symm
            exact add_left_cancel hd_left
    · -- Proof when b = m - 1.
      have hb_le : b ≤ m - 1 := by
        exact Nat.le_pred_of_lt hb_lt
      have hb_ge : m - 1 ≤ b := by
        exact Nat.le_of_not_gt b_case
      have hb : b = m - 1 := by
        exact le_antisymm hb_le hb_ge
      rw [hb] at ih_ab
      have claim : n + 1 = (a + 1) * m := by
        rw [ih_ab]
        rw [Nat.add_assoc]
        rw [hm']
        ring
      use a + 1
      constructor <;> dsimp
      · -- Proof that a + 1 works when b = m - 1.
        use 0
        constructor <;> dsimp
        · -- Proof that reminder 0 works.
          constructor
          · exact claim
          · exact Nat.pos_of_ne_zero hm
        · -- Proof that 0 is unique reminder that works.
          intros y hy
          have hy_left := hy.left
          rw [claim] at hy_left
          have hy_left' : (a + 1) * m + 0 = (a + 1) * m + y := by
            simpa using hy_left
          symm
          exact Nat.add_left_cancel hy_left'
      · -- Proof that a + 1 is unique.
        intros y hy
        rcases hy with ⟨c, hc_exists, hc_unique⟩
        rcases hc_exists with ⟨hc_left, hc_right⟩
        rw [claim] at hc_left
        cases c with
        | zero =>
          simp at hc_left
          rcases hc_left with case_1 | case_2
          · symm
            exact case_1
          · exfalso
            exact hm case_2
        | succ c' =>
          rw [hc_left] at claim
          rw [← Nat.add_assoc] at claim
          have claim2 := Nat.add_right_cancel claim
          have claim3 : y = a := by
            {
              apply ha_unique y
              use c'
              constructor <;> dsimp
              · constructor
                · exact claim2
                · linarith
              · intros z hz
                have hz_left := hz.left
                rw [hz_left] at claim2
                exact Nat.add_left_cancel claim2
            }
          rw [claim3] at hc_left
          have hc_left' : a * m + m = a * m + (c' + 1) := by
            calc
              a * m + m = (a + 1) * m := by ring
              _ = a * m + (c' + 1) := hc_left
          have hc_right' : m = c' + 1 := Nat.add_left_cancel hc_left'
          rw [hc_right'] at hc_right
          exfalso
          exact Nat.lt_irrefl (c' + 1) hc_right
