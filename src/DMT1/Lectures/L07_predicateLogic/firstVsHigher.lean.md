First-order predicate logic can be considered
as either an untyped, or equivalently (and better)
as a monomorphic (one-type) language. Every entity
has the same type: we'll call it *Object*. In this
sense, first-order logic is like Python. You can
apply any function to any object and it is the job
of the function definition to (1) figure out if it
is really the right kind of object for that function
to process,m and (2) decide what to do if it's not.

Here's a simple version of first-order logic embedded
in Lean 4.

Object is the type of every entity in first-order
logic. Here we use Lean to allow objects of what we
might call different "runtime types" but all having
Object as their "static types". In particular, here
we define (Object.person n) to be the n'th person in
whatever world we might be modeling, and (rock n) to
be the n'th rock.
```lean
inductive Object
| person (n : Nat)
| rock (r : Nat)
```

In first-order logic, the only way to know what kind
of object on has been given is to apply a predicate.
So here are two predicates, the first true for objects
deemed to be people and the second, rocks.
```lean
def isPerson : Object → Bool
| Object.person _ => true
| _ => false

def isRock : Object → Bool
| Object.rock _ => true
| _ => false
```

Now we'd like to assert that everyone is mortal.
So we'll define a predicate, which is to say, a
proposition with one or more arguments that, when
applied to arguments, yields a proposition. We'll
think of predicates then as functions that applied
to arguments reduce to propositions. However, as
there are only Object-type entities in first-order
theory, we need a function that takes any Object
value and answers accordingly. This function will
answer *true* if the argument is a person, as all
people are in fact mortal. But if applied to, say,
a rock, the function will still have to answer with
a Boolean value. We define it here to answer false
in such cases, but the reality is the the question
itself doesn't make sense. It's just like in Python
you can pass a string to a function that expects a
number and nothing will go wrong--until you *run*
the program, at which point the argument can be
runtime-tested to determine what kind of thing it
is really meant to represent.

```lean
def isMortal : Object → Bool
| o => if isPerson o then true else false
```

We're now ready to use our first order logic.
First we define some objects: a person named
*socrates* and a rock that we'll simple call,
*someRock*.

```lean
def socrates : Object := Object.person 0
def someRock : Object := Object.rock 0
```

Now we can ask whether either of these objects
satisfies the isMortal predicate.

```lean
#eval isMortal socrates   -- yes/true
#eval isMortal someRock   -- no/false
```

But, again, it doesn't even make sense to
ask if a rock is mortal. If it is then one
might conclude that at some point in time
the rock was alive and it is or eventually
will be dead, and if it's not then what? It
is alive and will live forever? I don't know
about you, but to me, these statements don't
"type check."

Essentially the same world but expressed in
the strongly and statically typed language of
Lean 4.


First, Person and Rock are now separate types,
not just differently shaped terms of the same
type, Object.

```lean
structure Person where
(n : Nat)

structure Rock where
(n : Nat)
```

Second, we define isMortal' (with a tick mark so
as not to have a name conflict) as a property of
values of type Person only. In more detail, here
we define isMortal' as a predicate parameterized
by a person, with a single constructor for proofs
of propositions obtained by apply8ing the predicate
to a Person. The constructor takes any Person, p, as
an argument and yields a proof of the proposition,
isMortal' p.
```lean
inductive isMortal' : Person → Prop
| everyoneMortal: (p : Person) →  isMortal' p
open isMortal'
```

Next we define a person entity and a rock entity,
but now they are of completely unrelated types.
```lean
def quine : Person := Person.mk 0
def doorStop : Rock := Rock.mk 0

#check quine    -- type Person
#check someRock -- type Rock

-- We can ask if Quine is mortal
def p0IsMortal : isMortal' quine := everyoneMortal quine

-- But the question whether a rock is mortal is a type error
def r0IsMortal : isMortal' doorStop := sorry
```

```lean
application type mismatch
  isMortal' doorStop
argument
  doorStop
has type
  Rock : Type
but is expected to have type
  Person : Type
```
