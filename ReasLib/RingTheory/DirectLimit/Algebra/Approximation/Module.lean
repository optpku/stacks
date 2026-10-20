module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Module.Core
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Module.BaseChange
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Module.Tail
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Module.Reindex

/-!
# Directed finite-module approximations

Aggregate import for the finite-module approximation API.  The concrete data
owner is `Approximation.Module.Core`; transition and limiting base-change
computations are in `Approximation.Module.BaseChange`.  Consumers that only
construct the data can import `Module.Core` directly; tail and reindex
constructors retain the finite-type specialization of the generic
`ModuleSystem` transport API.
-/

@[expose] public section
