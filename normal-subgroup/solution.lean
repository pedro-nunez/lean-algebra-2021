import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.TFAE

variable {G : Type} [Group G] (N : Subgroup G)

def normal_a :
  Prop := ∀ g : G, (∀ h : N, ∃ h' : N, h * g = g * h') ∧
  (∀ h : N, ∃ h' : N, g * h = h' * g)

def normal_b :
  Prop := ∀ g : G, (∀ h : N, ∃ h' : N, g⁻¹ * h * g = ↑h') ∧
  (∀ h : N, ∃ h' : N, ↑h = g⁻¹ * h' * g)

def normal_c :
  Prop := ∀ g : G, ∀ h : N, ∃ h' : N, g⁻¹ * h * g = ↑h'

def normal_d :
  Prop := ∀ g g' : G, (∃ h : N, g * g' = ↑h) ↔ (∃ h : N, g' * g = ↑h)

lemma a_implies_b :
  ∀ (N : Subgroup G), normal_a N → normal_b N := by
  intros N assumpt
  unfold normal_a at assumpt
  unfold normal_b
  intro g
  constructor
  · intro h
    specialize assumpt g
    have assumpt_h := assumpt.left h
    rcases assumpt_h with ⟨h', assumpt_h'⟩
    have new_eq : g⁻¹ * h * g = g⁻¹ * g * h' := by
      rw [mul_assoc]
      rw [assumpt_h']
      rw [← mul_assoc]
    have new_eq' : g⁻¹ * h * g = h' := by
      rw [new_eq]
      rw [inv_mul_cancel]
      rw [one_mul]
    use h'
  · intro h
    specialize assumpt (g⁻¹)
    have assumpt_h := assumpt.left h
    rcases assumpt_h with ⟨h', assumpt_h'⟩
    use h'
    have new_eq : ↑h * g⁻¹ * g = g⁻¹ * h' * g := by
      rw [assumpt_h']
    rw [mul_assoc] at new_eq
    rw [inv_mul_cancel] at new_eq
    simp at new_eq
    assumption

lemma b_implies_c :
  ∀ (N : Subgroup G), normal_b N → normal_c N := by
  intro N
  unfold normal_b
  unfold normal_c
  intros assumpt g h
  specialize assumpt g
  rcases assumpt with ⟨assumpt1, assumpt2⟩
  specialize assumpt1 h
  assumption

lemma c_implies_d :
  ∀ (N : Subgroup G), normal_c N → normal_d N := by
  unfold normal_c
  unfold normal_d
  intros N assumpt g g'
  constructor
  · intro assumpt2
    specialize assumpt g
    rcases assumpt2 with ⟨h', assumpt_h'⟩
    specialize assumpt h'
    rcases assumpt with ⟨h, assumpt_h⟩
    use h
    rw [← assumpt_h'] at assumpt_h
    simp at assumpt_h
    assumption
  · intro assumpt2
    specialize assumpt (g⁻¹)
    rcases assumpt2 with ⟨h', assumpt_h'⟩
    specialize assumpt h'
    rcases assumpt with ⟨h, assumpt_h⟩
    use h
    rw [← assumpt_h'] at assumpt_h
    rw [← assumpt_h]
    rw [mul_assoc]
    simp

lemma d_implies_a :
  ∀ (N : Subgroup G), normal_d N → normal_a N := by
  unfold normal_d
  unfold normal_a
  intros N assumpt g
  constructor
  · intro h
    specialize assumpt g (g⁻¹ * h)
    rcases assumpt with ⟨assumpt1, assumpt2⟩
    have assumpt3 : ∃ (h_1 : ↥N), g * (g⁻¹ * ↑h) = ↑h_1 := by
      use h
      simp
    have assumpt4 := assumpt1 assumpt3
    rcases assumpt4 with ⟨h', assumpt_h'⟩
    use h'
    rw [← assumpt_h']
    rw [← mul_assoc g (g⁻¹ * ↑h) g]
    rw [← mul_assoc g g⁻¹ ↑h]
    simp
  · intro h
    specialize assumpt g⁻¹ (g * h)
    rcases assumpt with ⟨assumpt1, assumpt2⟩
    have assumpt3 : ∃ (h_1 : ↥N), g⁻¹ * (g * h) = ↑h_1 := by
      use h
      simp
    have assumpt4 := assumpt1 assumpt3
    rcases assumpt4 with ⟨h', assumpt_h'⟩
    use h'
    rw [← assumpt_h']
    simp

theorem tfae_normal_subgroup :
  List.TFAE [normal_a N, normal_b N, normal_c N, normal_d N] := by
  tfae_have 1 → 2 := a_implies_b N
  tfae_have 2 → 3 := b_implies_c N
  tfae_have 3 → 4 := c_implies_d N
  tfae_have 4 → 1 := d_implies_a N
  tfae_finish

