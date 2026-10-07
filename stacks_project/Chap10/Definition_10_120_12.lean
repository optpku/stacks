module

public import Mathlib.RingTheory.Ideal.Span
import StacksCheckRecall

/-!
# Principal ideal domains

@stack 034U
-/

@[expose] public section

universe u

variable (R : Type u) [CommRing R]

/- Definition 10.120.12 (Stacks `034U`): a principal ideal domain is a domain in which every
ideal is principal. Mathlib intentionally represents the two clauses by canonical classes. -/
@[stacks 034U]
#check (IsDomain R ∧ IsPrincipalIdealRing R : Prop)

@[stacks 034U "principal-ideal-ring component"]
#check @IsPrincipalIdealRing
