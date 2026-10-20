module

public import ReasLib.Algebra.Module.DifferentialOperator.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.133.1

@stack 09CI

Definition 10.133.1 (Tag 09CI): for a ring map `R → S`, an `R`-linear map
between `S`-modules is a differential operator of order at most `k` when its
iterated scalar commutators vanish after `k + 1` steps.  At order zero this is
exactly `S`-linearity.

The canonical owner is `LinearMap.IsDifferentialOperatorOfOrder`.  The
order-bounded `S`-submodule and its subtype are derived shared APIs, not
Chapter 10 aliases.
-/

@[stacks 09CI "finite order differential operators"]
#check @LinearMap.IsDifferentialOperatorOfOrder

#check @differentialOperatorsOrderLESubmodule
#check @differentialOperatorsOrderLE
