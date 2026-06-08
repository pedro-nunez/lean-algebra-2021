import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.TFAE

variable {G : Type} [Group G] (N : Subgroup G)

def normal_a :
  Prop := ∀ g : G, ∀ h : N, ∃ h' : N, ↑h * g = g * h'

def normal_b :
  Prop := ∀ g : G, (∀ h : N, ∃ h' : N, g⁻¹ * h * g = h') ∧
  (∀ h : N, ∃ h' : N, ↑h = g⁻¹ * h' * g)

def normal_c :
  Prop := ∀ g : G, ∀ h : N, ∃ h' : N, g⁻¹ * h * g = h'

def normal_d :
  Prop := ∀ g1 g2 : G, (∃ h : N, g1 * g2 = h) ↔ (∃ h : N, g2 * g1 = h)

lemma a_implies_b :
  ∀ (N : Subgroup G), normal_a N → normal_b N := by
  intros N assumpt
  unfold normal_a at assumpt
  sorry

theorem tfae_normal_subgroup :
  List.TFAE [normal_a N, normal_b N, normal_c N, normal_d N] := by
  tfae_have 1 → 2 := a_implies_b N
  tfae_have 2 → 3 := by
    sorry
  tfae_have 3 → 4 := by
    sorry
  tfae_have 4 → 1 := by
    sorry
  tfae_finish
