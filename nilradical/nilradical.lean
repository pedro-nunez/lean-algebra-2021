import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Nilpotent.Basic

variable (R : Type*) [CommRing R]

namespace Ideal

def nilradical : Ideal R :=
{ carrier := {x : R | IsNilpotent x}
  zero_mem' := by
    -- Proof that it contains the zero element.
    sorry
  add_mem' := by
    -- Proof that it is closed under addition.
    sorry
  smul_mem' := by
    -- Proof that it is closed under scalar multiplication.
    sorry
}

end Ideal
