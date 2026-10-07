module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.BaseChange.Core
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.BaseChange.Bijective
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.BaseChange.Properties

/-!
# Stage base change for directed algebra approximations

This aggregate is the stable import boundary for the stage tensor comparison,
its computation laws, and the associated property/equivalence API.  Focused
consumers can import `BaseChange.Core` for the construction or
`BaseChange.Bijective` for the lightweight bijectivity API.
-/

@[expose] public section
