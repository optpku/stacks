module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor.ChangeOfRings.Counterexample
import StacksCheckRecall

/-!
# Remark 15.60.4 (Warning)

@stack 08YT

The reusable owner keeps the explicit rings, modules, and derived tensor products.  This file is
the source-facing recall of the warning that the two choices of target-ring action need not agree.
-/

@[expose] public section

/- The polynomial and quotient rings in the source counterexample. -/
@[stacks 08YT "counterexample rings"]
#check @CategoryTheory.DerivedTensorChangeOfRings.Counterexample.baseRing

@[stacks 08YT "counterexample quotient ring"]
#check @CategoryTheory.DerivedTensorChangeOfRings.Counterexample.targetRing

/- The two quotient generators satisfying `x * y = 0`. -/
@[stacks 08YT "counterexample quotient generators"]
#check @CategoryTheory.DerivedTensorChangeOfRings.Counterexample.x

@[stacks 08YT "counterexample quotient generators"]
#check @CategoryTheory.DerivedTensorChangeOfRings.Counterexample.y

/- The source modules `N = A/(x)` and `N' = A`, placed in degree zero. -/
@[stacks 08YT "counterexample derived objects"]
#check @CategoryTheory.DerivedTensorChangeOfRings.Counterexample.quotientObject

@[stacks 08YT "counterexample derived objects"]
#check @CategoryTheory.DerivedTensorChangeOfRings.Counterexample.regularObject

/- Remark 15.60.4 (Warning) (1): restricting `N` gives the powered-Koszul representative. -/
@[stacks 08YT "Remark 15.60.4 (Warning) (1)"]
#check @CategoryTheory.DerivedTensorChangeOfRings.Counterexample.quotientRestrictedTensorRegular_iso_koszulStage

/- Remark 15.60.4 (Warning) (2): restricting `N'` gives `N[1] ⊞ N`. -/
@[stacks 08YT "Remark 15.60.4 (Warning) (2)"]
#check @CategoryTheory.DerivedTensorChangeOfRings.Counterexample.regularRestrictedTensorQuotient_iso_shiftBiproduct

/- Remark 15.60.4 (Warning) (3): the two resulting objects of `D(A)` are not isomorphic. -/
@[stacks 08YT "Remark 15.60.4 (Warning) (3)"]
#check @CategoryTheory.DerivedTensorChangeOfRings.Counterexample.not_isomorphic
