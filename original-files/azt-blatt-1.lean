import algebra

-- This is a one line comment

/-
This is a comment
that occupies several lines
-/

/-
The right hand side of the screen gives you the necessary
feedback. But you need to move the cursor around, you will always
receive the feedback corresponding to the current line
-/

#print group
/-
This tells us (on the right hand side) what we get from the
assumption that something is a group. Don't worry too much about
the details that you don't understand!
-/

/-
# Example: uniqueness of the neutral element of a group
Let us start with an example in which we state and prove the
uniqueness of the neutral element of a group.
-/

lemma unique_neutral_element {G : Type} [group G]
  (a : G) (h : (∀ b : G, (a * b = b * a) ∧ (a * b = a))) : a = 1 :=
  /-
  We tell Lean that we are stating a lemma by saying "lemma", and
  we give our lemma a name which can be referenced later. In this 
  case we call it "unique_neutral_element". Then we list the 
  assumptions:

* G is a type (Lean works with types instead of sets, don't worry
too much about this the first time) which we assume then to be 
a group
* a is an element of G. You can think of (a : G) as the equivalent
of a ∈ G. This is again related to Lean using types instead of 
sets, so you don't need to worry about it now.
* We have an hypothesis called "h" which says that for all 
elements b ∈ G we have ab = ba and ab = a.

  After the assumptions we state the conclusion of the lemma and 
  separate it from the assumptions with the colon ":"

  Finally we write := before starting the proof. The reason this 
  symbol makes sense is again related to type theory, so let us 
  not worry about it here.

  You may have noticed that it was enough to write 1 for the neutral 
  element of G, and Lean knows that we are talking about the neutral 
  element of G and not about the natural number 1. This is one of 
  the cool features of Lean called type inference. Roughly speaking, 
  since the left hand side of the equality is a ∈ G, Lean expects 
  the right hand side of the equality to be something in G as well.
  -/
  begin
    /-
    It is convenient to write proofs in Lean inside a begin-end block
    like this one. This will make it easier to write the proof step 
    by step, with the right hand side indicating the current goal 
    and the current assumptions that we have available:

* There is only 1 goal currently (1 thing to show)
* G is a type (again, let's not worry about that here)
* We are assuming that G is a group. We left this assumption 
implicit and didn't give it a name, so it is automatically 
named "_inst_1"
* a is an element of G
* We have our hypothesis h
* The goal, marked with ⊢, is to show that a = 1
    
    -/
    specialize h a,
    /-
    The hypothesis h is a forall statement. We apply it to the 
    given element a ∈ G. This turns the forall statement h into 
    its conclusion, which is in turn the conjunction of two 
    statements.
    -/
    cases h with h1 h2,
    /-
    We split the conjunction h into its two statements and call 
    them h1 and h2.
    -/
    have h3 : (a * a) * a⁻¹ = 1,
    /-
    We claim that the equality (a * a) * a⁻¹ = 1 holds as well. 
    We give this claim a name, "h3". Since this was only a claim, 
    Lean creates a new goal, marked with another ⊢.
    -/
    rw h2,
    /-
    This is the "rewrite" tactic: we rewrite our hypothesis h2 
    into the current goal. By default, Lean takes the current 
    goal to be the last one that we added.
    -/
    exact mul_right_inv a,
    /-
    The "exact" tactic tells Lean that the current goal is 
    precisely obtained from applying the proposition mul_right_inv 
    (already existing in the Lean libraries) to the element a.
    This solves this goal and now we can use our claim h3 to prove 
    the original goal.
    -/
    have h4 : a * (a * a⁻¹) = 1,
    rw ← mul_assoc,
    /-
    Here we apply the "rewrite" tactic backwards. mul_assoc tells 
    us that (x * y) * z = x * (y * z), so by default (i.e. without 
    ←) the rewrite tactic would look for an expression of the form 
    (x * y) * z and substitute it by the expression x * (y * z).
    -/
    exact h3,
    /-
    After applying associativity, claim h4 reduces to our 
    hypothesis h3. So we tell this to Lean with the "exact" tactic. 
    The goal corresponding to claim h4 is then solved and we can 
    use now the statement h4 to finish our original goal.
    -/
    rw mul_right_inv a at h4,
    /-
    Here we use the "rewrite" tactic to modify an hypothesis, 
    instead of the current goal.
    -/
    rw mul_one a at h4,
    exact h4,
    /-
    After the last two rewrites, the statement h4 is exactly what 
    we wanted to show. So we tell this to Lean and Lean confirms 
    that the proof is complete (hence correct) by saying "no goals".
    -/
end

class group_hom {G G' : Type} [group G] [group G'] (f : G → G') : Prop :=
  (hom_mul : ∀ a b, f (a * b) = f a * f b)

lemma image_of_neutral_element {G G' : Type} [group G] [group G']
  (f : G → G') [group_hom f] : f(1) = 1 :=
  begin
    sorry, -- Erase sorry and replace it with your proof!
  end