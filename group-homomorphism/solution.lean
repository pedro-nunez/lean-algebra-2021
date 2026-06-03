import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.ApplyFun

-- First define a class encoding the group homomorphism axiom.
class GroupHom {G G' : Type} [Group G] [Group G'] (f : G → G') : Prop where
  hom_mul : ∀ a b, f (a * b) = f a * f b

-- Then state and prove the desired result.
theorem image_of_one {G G' : Type} [Group G] [Group G']
  (f : G → G') [GroupHom f] : f 1 = 1 := by
  have h : f 1 = (f 1) * (f 1) := by
    nth_rw 1 [← mul_one 1]
    rw [GroupHom.hom_mul (f := f) 1 1]
  apply_fun (fun x => (x * (f 1)⁻¹)) at h
  rw [mul_assoc (f 1) (f 1) (f 1)⁻¹] at h
  simp at h
  symm at h
  exact h
