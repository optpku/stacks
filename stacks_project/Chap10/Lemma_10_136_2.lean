/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.RingHom.Syntomic.BaseChange

@[expose] public section

/-!
# Syntomic Faithfully-Flat Base-Change Recall

The source equivalence belongs to the intrinsic `RingHom.Syntomic` predicate.
The shared leaf also exposes the local-complete-intersection-fiber component,
so applications can use only the part of the statement that they need.

@stack 00SM
-/

/- Lemma 10.136.2, tag 00SM: for a faithfully flat base change `R → R'`, the
map `R → S` is syntomic if and only if the induced map
`R' → R' ⊗[R] S` is syntomic. -/
@[stacks 00SM "syntomic faithfully flat base change"]
#check @RingHom.Syntomic.iff_baseChange_of_faithfullyFlat

#check @RingHom.HasLocalCompleteIntersectionFibers.baseChange
#check @RingHom.HasLocalCompleteIntersectionFibers.iff_baseChange_of_faithfullyFlat
