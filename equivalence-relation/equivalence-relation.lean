import Mathlib.Algebra.Group.Subgroup.Basic

variable {G : Type} [Group G] (H : Subgroup G)

def Rel (H : Subgroup G) (g g' : G) : Prop := g⁻¹ * g' ∈ H

lemma Rel_is_equivalence_relation : Equivalence (Rel H) := by
  constructor
  · sorry
  · sorry
  · sorry
