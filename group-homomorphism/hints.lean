import Mathlib.Algebra.Group.Basic

-- This is a one line comment.

/-
This is a comment
that occupies several lines.
-/

/-
On the right-hand side of the screen you should see a panel with some info.
This is called the Lean Infoview. It will display different things depending
on where your cursor is currently placed.
-/

#print Group
/-
If you place the cursor on the previous line, the Infoview will display some
information about the Group class. Don't worry if you don't understand most
of this information at this point!
-/

/-
# Example: Uniqueness of the neutral element of a group.
To warm up, let us start with an example in which we state and prove the
uniqueness of the neutral element of a group. There are some naming
conventions for theorems and objects in Lean's Mathlib library, and it is a
good idea to be aware of them and try to follow them whenever possible:
https://leanprover-community.github.io/contribute/naming.html
-/

theorem unique_one {G : Type} [Group G]
  (a : G) (h : (∀ b : G, (a * b = b * a) ∧ (a * b = a))) : a = 1 := by
    /-
    We tell Lean that we are stating a theorem by saying "theorem", and
    we give our theorem a name which can be referenced later. In this 
    case we call it "unique_one". Then we list the assumptions:

    * G is a type which we assume to be a group. Lean works with types
    instead of sets; no need to worry too much about this for now.
    * a is an element of G. You can think of (a : G) as the equivalent of
    a ∈ G. This is again related to Lean using types instead of sets.
    * We have an hypothesis called "h" which says that for all elements
    b ∈ G we have ab = ba and ab = a.

    After the assumptions we state the conclusion of the theorem and
    separate it from the assumptions with the colon ":".

    Finally we write := before starting the proof. The reason this symbol
    makes sense is again related to type theory, so let us not worry about
    it here.

    You may have noticed that it was enough to write 1 for the neutral
    element of G, and Lean knows that we are talking about the neutral
    element of G and not about the natural number 1. This is a feature of
    Lean called type inference. Roughly speaking, since the left-hand side
    of the equality is a ∈ G, Lean expects the right-hand side of the
    equality to be something in G as well.
    -/

    /-
    After := by, on the line below it (or below this long comment), you can
    start writing the proof of the theorem. When you place the cursor there,
    ready to start writing the proof, you will see on the Infoview what the
    current goal is. The statement that you have to prove is marked with the
    symbol "⊢". Above it, you will see all the assumptions and hypothesis
    that you can use to prove it.

    Currently, when you place the cursor outside of this comment and below
    the := by line, you should see the following:

    * A single goal (only one thing to show now).
    * The type G.
    * The assumption that G is a group. We left this assumption implicit
    without giving it a name, so it is automatically named "inst✝".
    * a is an element of G.
    * We have our hypothesis h.
    * The target statement that we need to show, marked with ⊢, is a = 1.
    -/

    specialize h a
    /-
    The hypothesis h is a forall statement. We apply it to the given element
    a ∈ G. This specializes the forall statement h into a statement about a,
    which is in turn the conjunction of two statements. You can see the
    change in the Infoview by placing the cursor before and after
    "specialize h a".
    -/
    have h2 := h.right
    /-
    We keep the right-hand statement in the conjunction, which is the one
    that we will use to prove the target statement, and call it h2.
    -/
    have h3 : (a * a) * a⁻¹ = 1 := by
      /-
      We claim that the equality (a * a) * a⁻¹ = 1 holds as well. We give
      this claim a name, "h3". Since this was only a claim, Lean creates a
      new goal, and the new target is marked with another ⊢.
      -/
      rw [h2]
      /-
      This is the rewrite tactic: we rewrite the hypothesis h2 into the
      target of the current goal. By default, Lean takes the current goal
      to be the last one that we have created.
      -/
      exact mul_inv_cancel a
      /-
      The exact tactic tells Lean that the current goal is precisely
      achieved by applying the proposition mul_right_inv (a theorem which
      is already available in Lean's Mathlib library) to the element a.
      This resolves this auxiliary goal that we created to obtain h3,
      and now we can use the hypothesis h3 to prove the original goal.
      You can hover your mouse over mul_inv_cancel to see more info about
      this theorem. For example, the round parentheses indicate the required
      arguments of the theorem. In this case, there is only one required
      argument, namely an element a of a group G. It just so happens that we
      are working with a group called G and an element of G called a;
      hopefully this will not be too confusing.
      -/
    /-
    We have resolved the goal created by the claim h3 by proving the claim.
    Now we can go back to our original goal.
    -/
    rw [mul_assoc a a a⁻¹] at h3
    rw [mul_inv_cancel a] at h3
    rw [← mul_one a]
    /-
    Here we apply the rewrite tactic backwards. mul_one a says that
    a * 1 = a, so we change our target statement from a = 1 to a * 1 = 1,
    to match the hypothesis h3. Of course, it would be more natural to
    rw [mul_one a] at h3 to then match the target, but this allows us to
    showcase how to apply the rewrite tactic backwards.
    -/
    assumption
    /-
    Once h3 matches the target, we can resolve the goal with exact h3
    as before, or with the assumption tactic. The assumption tactic
    searches the current local ontext for a hypothesis that exactly
    matches the target of the current goal. In this case, it will find
    the hypothesis h3, thus resolving the goal.
    -/

/-
# Back to our exercise.
-/

-- First define a class encoding the group homomorphism axiom.
class GroupHom {G G' : Type} [Group G] [Group G'] (f : G → G') : Prop where
  hom_mul : ∀ a b, f (a * b) = f a * f b

-- Then state and prove the desired result.
theorem image_of_one {G G' : Type} [Group G] [Group G']
  (f : G → G') [GroupHom f] : f 1 = 1 := by
  sorry -- Erase sorry and replace it with your own proof!

/-
# Hints.
Maybe you will find some of the following tactics useful:
* nth_rw
* apply_fun
* simp
* symm
Don't forget to check Mathlib's Documentation for more info!
-/
