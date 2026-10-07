module

public import Mathlib.Algebra.GroupWithZero.Associated
public import Mathlib.Algebra.Prime.Defs
public import Mathlib.RingTheory.Ideal.Maximal
import StacksCheckRecall

/-!
# Associated, Irreducible, and Prime Elements

@stack 034P
-/

@[expose] public section

universe u

variable {R : Type u} [CommRing R] [IsDomain R]

/- Definition 10.120.1 (1): the source notion of associated elements is Mathlib's canonical
`Associated` relation. -/
@[stacks 034P "(1)"]
#check (Associated : R → R → Prop)

/- Definition 10.120.1 (2): the source notion of an irreducible element is Mathlib's canonical
`Irreducible` predicate. -/
@[stacks 034P "(2)"]
#check (Irreducible : R → Prop)

/- Definition 10.120.1 (3): a source-prime element is one whose principal ideal is prime. -/
@[stacks 034P "(3)"]
#check (fun x : R => (Ideal.span ({x} : Set R)).IsPrime)

/- For nonzero elements, Mathlib's `Prime` predicate is the canonical multiplicative form. -/
@[stacks 034P "nonzero principal-ideal prime criterion"]
#check @Ideal.span_singleton_prime
