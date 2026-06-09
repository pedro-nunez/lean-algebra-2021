import Mathlib.Algebra.Group.Subgroup.Basic

variable {G : Type} [Group G] (H : Subgroup G)

def Rel (H : Subgroup G) (g g' : G) : Prop := g⁻¹ * g' ∈ H

lemma Rel_is_equivalence_relation : Equivalence (Rel H) := by
  constructor
  · intro g
    unfold Rel
    simp only [inv_mul_cancel]
    exact one_mem H
  · intros g g'
    unfold Rel
    intro assumpt
    have claim1 := H.inv_mem assumpt
    simp at claim1
    assumption
  · unfold Rel
    intros g g' g'' assumpt1 assumpt2
    have claim2 := H.mul_mem assumpt1 assumpt2
    simp at claim2
    assumption
