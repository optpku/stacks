/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.CochainComplex.KFlat.ModuleCat.ChangeOfRings

/-!
# Lemma 15.59.3

@stack 06Y1

The reusable statement is `CochainComplex.IsKFlat.extendScalars`.  This file recalls its
commutative-ring specialization.  The textbook states the result for rings; the current
`ModuleCat` tensor owner is formulated for commutative rings.
-/

@[expose] public section

/- Lemma 15.59.3 (06Y1): extension of scalars sends a K-flat complex to a K-flat complex. -/
@[stacks 06Y1 "extension of scalars preserves K-flat complexes"]
#check @CochainComplex.IsKFlat.extendScalars
