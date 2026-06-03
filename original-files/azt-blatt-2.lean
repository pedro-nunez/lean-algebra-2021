import group_theory.subgroup.basic

variables {G : Type} [group G] (N : subgroup G)

def normal_a : Prop :=
  ∀ g : G, ∀ h : N, ∃ h' : N, ↑h * g = g * h'

def normal_b : Prop :=
  ∀ g : G, (∀ h : N, ∃ h' : N, g⁻¹ * h * g = h') ∧ (∀ h : N, ∃ h' : N, ↑h = g⁻¹ * h' * g)

def normal_c : Prop :=
  ∀ g : G, ∀ h : N, ∃ h' : N, g⁻¹ * h * g = h'

def normal_d : Prop :=
  ∀ g₁ g₂ : G, (∃ h : N, g₁ * g₂ = h) ↔ (∃ h : N, g₂ * g₁ = h)

lemma a_implies_b : normal_a N → normal_b N :=
begin
  intro assumpt,
  unfold normal_a at assumpt,
  unfold normal_b,
  intro g,
  split,
  intro h,
  specialize assumpt g h,
  cases assumpt with h' assumpth',
  have new_eq : g⁻¹ * h * g = g⁻¹ * g * h',
  rw mul_assoc,
  rw assumpth',
  simp,
  have new_eq' : g⁻¹ * h * g = h',
  rw new_eq,
  rw mul_left_inv,
  rw one_mul,
  use h',
  assumption,
  intro h,
  specialize assumpt g⁻¹ h,
  cases assumpt with h' assumpth',
  use h',
  have new_eq : ↑h * g⁻¹ * g = g⁻¹ * h' * g,
  rw assumpth',
  rw mul_assoc at new_eq,
  rw mul_left_inv at new_eq,
  simp at new_eq,
  assumption,
end

lemma b_implies_c : normal_b N → normal_c N :=
begin
  unfold normal_b,
  unfold normal_c,
  intro assumpt,
  intros g h,
  specialize assumpt g,
  cases assumpt with assumpt1 assumpt2,
  specialize assumpt1 h,
  assumption,
end

lemma c_implies_d : normal_c N → normal_d N :=
begin
  unfold normal_c,
  unfold normal_d,
  intro assumpt,
  intros g g',
  split,
  intro assumpt2,
  specialize assumpt g,
  cases assumpt2 with h' assumpth',
  specialize assumpt h',
  cases assumpt with h assumpth,
  use h,
  rw ← assumpth' at assumpth,
  simp at assumpth,
  assumption,
  intro assumpt2,
  specialize assumpt g⁻¹,
  cases assumpt2 with h' assumpth',
  specialize assumpt h',
  cases assumpt with h assumpth,
  use h,
  rw ← assumpth' at assumpth,
  rw ← assumpth,
  rw mul_assoc,
  simp,
end

lemma d_implies_a : normal_d N → normal_a N :=
begin
  unfold normal_d,
  unfold normal_a,
  intro assumpt,
  intros g h,
  specialize assumpt g (g⁻¹ * h),
  cases assumpt with assumpt1 assumpt2,
  have assumpt3 : ∃ (h_1 : ↥N), g * (g⁻¹ * ↑h) = ↑h_1,
  use h,
  simp,
  have assumpt4 := assumpt1(assumpt3),
  cases assumpt4 with h' assumpth',
  use h',
  rw ← assumpth',
  rw ← mul_assoc g (g⁻¹ * ↑h) g,
  rw ← mul_assoc g g⁻¹ ↑h,
  simp,
end