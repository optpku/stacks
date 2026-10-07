module

public import ReasLib.Algebra.Module.PrincipalParts.FormallyEtale
public import ReasLib.Algebra.Module.DifferentialOperator.FormallyEtale
import StacksCheckRecall

@[expose] public section

/-
Lemma 10.150.8 (Tag 0H94): formally étale scalar extension commutes with
principal parts, and therefore extends differential operators uniquely without
increasing their order.

@stack 0H94

The comparison belongs to `PrincipalParts.BaseChange.FormallyEtale`; the
resulting universal extension property belongs to
`LinearMap.IsDifferentialOperatorOfOrder.BaseChange.FormallyEtale`. This
source file records both clauses without introducing a chapter-local
quotient-presentation owner.
-/

@[stacks 0H94 "formally etale principal-parts base change"]
#check @PrincipalParts.BaseChange.FormallyEtale.isBaseChange

@[stacks 0H94 "principal-parts equivalence"]
#check @PrincipalParts.BaseChange.FormallyEtale.equiv

@[stacks 0H94 "finite-order differential-operator extension"]
#check @LinearMap.IsDifferentialOperatorOfOrder.BaseChange.FormallyEtale.existsUnique_extension
