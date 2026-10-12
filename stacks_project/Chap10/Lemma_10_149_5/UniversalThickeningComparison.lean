/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Extension.FirstOrder.Comparison
import StacksCheckRecall

/-!
# Comparison of Universal First-Order Thickenings

The reusable comparison is expressed as an equivalence of algebra extensions,
rather than a naked algebra equivalence accompanied by a commuting equation.

@stack 04EF
-/

@[expose] public section

@[stacks 04EF "equivalence of algebra extensions"]
#check @Algebra.Extension.Equiv

@[stacks 04EF "existence of the comparison equivalence"]
#check @Algebra.Extension.FirstOrder.IsUniversal.existsEquiv

@[stacks 04EF "uniqueness of the comparison equivalence"]
#check @Algebra.Extension.FirstOrder.IsUniversal.equiv_eq

@[stacks 04EF "subsingleton comparison equivalences"]
#check @Algebra.Extension.FirstOrder.IsUniversal.subsingletonEquiv
