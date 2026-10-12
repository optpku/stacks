/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Nilpotent.GeometricallyReduced.Localization
public import ReasLib.RingTheory.Nilpotent.GeometricallyReduced.Polynomial
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.43.3 (Tag 04KN) is a canonical recall block.

Its localization clause currently recalls the source-facing arbitrary-localization theorem from
Lemma 10.43.2.  Its polynomial clause is the direct reusable API
`Algebra.IsGeometricallyReduced.polynomial`, which is deliberately stated over an arbitrary
commutative base ring rather than only over a field.

@stack 04KN
-/

@[stacks 04KN]
#check @Algebra.IsGeometricallyReduced.of_isLocalization

@[stacks 04KN]
#check @Algebra.IsGeometricallyReduced.polynomial
