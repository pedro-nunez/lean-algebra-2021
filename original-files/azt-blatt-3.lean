import group_theory.subgroup.basic 
variables {G : Type} [group G] (H : subgroup G)
def Rel (H : subgroup G) (g g' : G) : Prop := g⁻¹ * g' ∈ H
lemma Rel_is_equivalence_relation : equivalence (Rel H) :=
begin
  unfold equivalence, split,
  unfold reflexive,
  intro g,
  unfold Rel,
  simp,
  exact subgroup.one_mem H,
  split,
  unfold symmetric,
  intros g g',
  unfold Rel,
  intro assumpt,
  have claim1 := H.inv_mem' assumpt,
  simp at claim1,
  assumption,
  unfold transitive,
  unfold Rel,
  intros g g' g'',
  intros assumpt1 assumpt2,
  have claim2 := H.mul_mem' assumpt1 assumpt2,
  rw ← mul_assoc at claim2,
  simp at claim2,
  assumption,
end