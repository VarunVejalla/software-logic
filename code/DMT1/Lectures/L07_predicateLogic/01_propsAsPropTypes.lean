/- @@@
# Propositions as Types in Prop

<!-- toc -->

In the previous chapter, we saw that we could represent
propositions as *computational types*, and proofs of them
as various programs and data structures. Reasoning is thus
reduced to programming!

However, there are some problems with the approach so far:

- it doesn't distinguish logical from computational types
- it enables one to distinguish between proofs of propositions

What we would like, then, is to have a slightly different sort
of type, differing from the usual data types in these two ways:

- connectives can only accept types representing *propositions*
- the choice of a proof to show validity is entirely irrelevant
- and of course we'd like to use the usual logical notations

To this end, Lean and similar logics define a new sort of type,
called *Prop*, dedicated to the representation of propositions,
and having these additional properties.

In this chapter, we run through exactly the same examples as
in the last, but now using Prop instead of Type as the type
of propositions.
@@@ -/

/-@@@
## False replaces Empty
@@@ -/

#check False
-- inductive False : Prop

/- @@@
## Set-Up for Running Example

We can represent elementary propositions, and their truth or
falsing, by defining types that either do or do not have any
values. Here we define three true propositions, *P, Q, R,* and
one false one, *N*, the negation of which will then be true.
@@@ -/
inductive P : Prop  where | mk
inductive Q : Prop  where | mk
inductive R : Prop  where | mk
inductive N : Prop  where



/- @@@
## Proofs are Values of "Logical" Types

We continue to represent proofs as values of a given type,
and we can use Lean to check that proofs are correct relative
to the propositions they mean to prove. It's just type checking!
We do have a new keyword available: *theorem*. It informs the
reader explicitly that a value is intended as a proof of some
proposition.
@@@ -/

def p' : P := P.mk
example : Q := Q.mk
theorem p : P := P.mk

/- @@@
The same principles hold regard false propositions represented
as types. They are *logical* types with no proofs. Therefore you
can't prove them in Lean.
@@@ -/
theorem r : N := _    -- No. There's no proof term for it!

/- @@@
## The Logical Connectives

Lean 4 defines separate logical connectives just for types
in Prop.

### P × Q (Product Types) becomes P ∧ Q

Here as a reminder is Lean's definition of the polymorphic
pair type in Lean 4, followed by its definition of *And*.
@@@ -/

#check And

namespace hide

structure Prod (α : Type u) (β : Type v) where
  mk ::
  fst : α
  snd : β

structure And (a b : Prop) : Prop where
  intro ::
  left : a
  right : b

end hide

/- @@@
We now make the following replacements:

- replace × with ∧
- replace Prof.mk with And.intro
- replace Prod.fst and Prod.snd with And.left and And.right
@@@ -/

abbrev PAndQ := P ∧ Q    -- Representing the proposition, P ∧ Q
def pandq : P ∧ Q := And.intro P.mk Q.mk  -- Representing proof!
example : P ∧ Q := ⟨ P.mk, Q.mk ⟩       -- Notation for Prod.mk


/- @@@
@@@ -/

#check pandq.left
#check pandq.right

/- @@@
All of the usual theorems then go through as before
@@@ -/

def andCommutative : P ∧ Q → Q ∧ P
| And.intro p q  => And.intro q p

def andCommutative' : P ∧ Q → Q ∧ P
| ⟨ p, q ⟩ => ⟨ q, p ⟩

def andCommutative'' : P ∧ Q → Q ∧ P := λ ⟨ p, q ⟩ => ⟨ q, p ⟩

/- @@@

### Replace P ⊕ Q (Sum Type) with P ∨ Q

As we represented the conjunction of propositions as a
product type, we will represent a disjunction as what is
called a *sum* type. Whereas a product type has but one
constructor with multiple arguments, a sum types has two
constructors each taking one argument. A value of a product
type holds *one of these and one of those*, while a sum
type holds *one of these or one of those*. We thus used
the polymnorphic *Prod* type to represent conjunctions,
and now we do the same, using the polymorphic Sum type to
represent disjunctions and their proofs.
@@@ -/

#check Sum
#check Or


/- @@@ OR AS SUM

inductive Sum (α : Type u) (β : Type v) where
  | inl (val : α) : Sum α β
  | inr (val : β) : Sum α β


inductive Or (a b : Prop) : Prop where
  | inl (h : a) : Or a b
  | inr (h : b) : Or a b

@@@ -/

-- Proof of *or* by proof of left side
def porq1 : Or P Q := Or.inl P.mk

-- Proof by proof of right side, with notation
def porq2 : P ∨ Q := Or.inr Q.mk

/- @@@
All the theorems from before also go through just fine.
@@@ -/

example : P ∨ Q → Q ∨ P
| Or.inl p => Or.inr p
| Or.inr q => Or.inl q





/- @@@
### Implication as Function Type

Implications continue to be represented by function types.
@@@ -/

example : P ∧ Q → P := λ h => h.left


/- @@@
### Negation as Proof of Emptiness

Negation continues to be represented as the existence
of a function from a type to an empty type, but now
instead of (Empty : Type) we use (False : Prop).
@@@ -/

-- Can't prove that P is false, as it has a proof
def falseP : P → False
| P.mk => _   -- can't return value of Empty type!


-- But *N* is empty so this definition works
def notr : N → False := fun r => nomatch r

/- @@@
Again, we prove that a proposition, say *N*, is false
by proving that it has no proofs, and we do that by
proving that there *is* a function from that type to
*False*. Lean defines *not* (rather than *neg* as we
defined it previously) along with ¬ as a notation to
this end.
@@@ -/

#check Not
-- def Not (a : Prop) : Prop := a → False
example : ¬N := λ h => nomatch h

/- @@@
## Summing Up

In class exercise. Take this example from last time
and fix it to use Prop.
@@@ -/

example : P × (Q ⊕ R) → (P × Q ⊕ P × R)
| ⟨ p, Sum.inl q ⟩ => Sum.inl ⟨ p, q ⟩
-- you write the second missing case

/-@@@
## Homework

Write and prove the following propositions from the
identities file in the propositional logic chapter.
Use the space below. If you ever get to the point where
you're sure there's no possible proof, just say so and
explain why. Use ×, ⊕, and ~ as notations for logical
and, or, and not when translating these propositions
into our current embedding of predicate logic in Lean
(just as we did in the preceding example).

- P ∧ (Q ∧ R) → (P ∧ Q) ∧ R   -- and is associative
- P ∨ (Q ∨ R) → (P ∨ Q) ∨ R   -- or is associative
- ¬(P ∧ Q) → ¬P ∨ ¬Q
- ¬(P ∨ Q) → ¬P ∧ ¬Q
- ¬(P ∧ N)
- (P ∨ N)

@@@ -/

-- Your answers here


/- @@@
## Extra Credit

Not all of the axioms that are valid in propositional
logic are valid in our embedding of constructive logic
into Lean. One that's not is negation elimination: that
is, *¬¬P → P*. Try to prove it in the stype we've used
here here and explain exactly where things go wrong (in
a comment).
-/
