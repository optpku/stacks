module

public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.Inseparable
import StacksCheckRecall

@[expose] public section

/- Definition 111.6.22 (1): a point `x` of a topological space `X` is closed when
`closure {x} = {x}`. This is membership in the canonical set `closedPoints X`, equivalently
`x ∈ closedPoints X` iff `IsClosed {x}` iff `closure {x} = {x}`. -/
@[stacks 027H]
#check closedPoints

/- Companion check: `x ∈ closedPoints X` iff `IsClosed {x}`. -/
#check mem_closedPoints_iff

/- Companion check: `closure s = s` iff `IsClosed s`, recovering the source formula on
singletons. -/
#check closure_eq_iff_isClosed

/- Definition 111.6.22 (2): for points `x`, `y` of `X`, Stacks says `x` is a specialization of
`y` (equivalently `y` is a generalization of `x`) when `x ∈ closure {y}`. This is the
canonical relation `Specializes`, written `y ⤳ x` in mathlib binder order. -/
@[stacks 027H]
#check Specializes

/- Companion check: `x ⤳ y` iff `y ∈ closure {x}`, so Stacks "`x` is a specialization of `y`"
is `y ⤳ x`. -/
#check specializes_iff_mem_closure
