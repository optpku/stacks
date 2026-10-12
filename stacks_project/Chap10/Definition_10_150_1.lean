/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Etale.Lifting
import StacksCheckRecall

@[expose] public section

/-!
Definition 10.150.1 (Tag 00UQ): a ring map is formally etale when it has
the unique lifting property against square-zero quotients.  The ring-map
predicate is canonical, while the reusable lifting API is stated for the
corresponding ambient algebra structure.

@stack 00UQ
-/
@[stacks 00UQ]
#check @RingHom.FormallyEtale

@[stacks 00UQ]
#check @Algebra.FormallyEtale.iff_existsUnique_lift
#check @Algebra.FormallyEtale.existsUnique_lift
#check @Algebra.FormallyEtale.of_existsUnique_lift
