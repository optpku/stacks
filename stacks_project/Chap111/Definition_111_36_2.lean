module

public import ReasLib.Topology.Specialization.Closure
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 111.36.2: on a topological space `X`, a point `x` is a specialization of
`x'` iff `x ∈ closure {x'}`. This is the canonical relation `Specializes`, written
`x' ⤳ x` in mathlib binder order. -/
@[stacks 029P]
#check (mem_closure_singleton_iff_specializes :
  ∀ {X : Type u} [TopologicalSpace X] (x x' : X),
    x ∈ closure ({x'} : Set X) ↔ x' ⤳ x)

/- Companion check: `x ⤳ y` iff `y ∈ closure {x}`, so Stacks "`x` is a specialization of
`x'`" is `x' ⤳ x`. -/
#check (specializes_iff_mem_closure :
  ∀ {X : Type u} [TopologicalSpace X] {x y : X},
    x ⤳ y ↔ y ∈ closure ({x} : Set X))
