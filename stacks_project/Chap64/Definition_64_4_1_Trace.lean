module

public import ReasLib.LinearAlgebra.Trace.CommutatorQuotient

universe u v

variable (R : Type u) [Ring R] (n : Type v) [Fintype n] [DecidableEq n]

#check (LinearMap.traceNatural : Module.End R (n → R) →+ Ring.CommutatorQuotient R)
