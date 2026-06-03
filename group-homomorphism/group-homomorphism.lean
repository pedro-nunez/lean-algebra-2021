import Mathlib.Algebra.Group.Defs

-- First define a class encoding the group homomorphism axiom.
class GroupHom {G G' : Type} [Group G] [Group G'] (f : G → G') : Prop where
  hom_mul : ∀ a b, f (a * b) = f a * f b

-- Then state and prove the desired result.
theorem image_of_one {G G' : Type} [Group G] [Group G']
  (f : G → G') [GroupHom f] : f 1 = 1 := by
  sorry -- Erase sorry and replace it with your own proof!
