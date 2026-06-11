import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Nilpotent.Basic

variable (R : Type*) [CommRing R]

namespace Ideal

def nilradical : Ideal R :=
{ carrier := {x : R | IsNilpotent x}
  zero_mem' := by
    -- Proof that it contains the zero element.
    dsimp
    unfold IsNilpotent
    use 1
    simp
  add_mem' := by
    -- Proof that it is closed under addition.
    dsimp
    intros a b ha hb
    unfold IsNilpotent
    unfold IsNilpotent at ha hb
    rcases ha with ⟨n, hn⟩
    rcases hb with ⟨m, hm⟩
    use n + m - 1
    -- Apply binomial expansion.
    rw [Commute.add_pow]
    · apply Finset.sum_eq_zero
      intros k hk
      apply mul_eq_zero_of_left
      by_cases hnk : n ≤ k
      · apply mul_eq_zero_of_left
        exact pow_eq_zero_of_le hnk hn
      · have hmk : m ≤ n + m - 1 - k := by
          omega
        apply mul_eq_zero_of_right
        exact pow_eq_zero_of_le hmk hm
    · exact Commute.all a b
  smul_mem' := by
    -- Proof that it is closed under scalar multiplication.
    dsimp
    intros c x hx
    unfold IsNilpotent
    unfold IsNilpotent at hx
    rcases hx with ⟨n, hn⟩
    use n
    ring_nf
    rw [hn]
    ring
}

end Ideal
