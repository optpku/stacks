module

public import ReasLib.Algebra.Module.DifferentialOperator.Localization
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.133.12

@stack 0G36

Lemma 10.133.12 (Tag 0G36): an `R`-linear differential operator between
`S`-modules extends uniquely to the localizations at a submonoid `T : Submonoid S`,
without increasing its order.

The source statement is the localization specialization of formally-etale
base change.  The reusable owner is
`LinearMap.IsDifferentialOperatorOfOrder.Localization.existsUnique_extension`;
its `IsExtension` predicate keeps the generator compatibility and order bound
together, rather than duplicating a tensor-product transport proof in this
chapter file.
-/

@[stacks 0G36 "localization of differential operators"]
#check @LinearMap.IsDifferentialOperatorOfOrder.Localization.IsExtension

#check @LinearMap.IsDifferentialOperatorOfOrder.Localization.existsUnique_extension
