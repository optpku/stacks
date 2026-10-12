/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Presheaf.Flasque
import StacksCheckRecall

@[expose] public section

/- Definition 20.12.1 (09SW): a presheaf of sets is flasque when every restriction map is
surjective.  The canonical root owner is the categorical Mathlib predicate. -/

@[stacks 09SW]
#check @TopCat.Presheaf.IsFlasque

@[stacks 09SW "surjective restriction maps"]
#check @TopCat.Presheaf.IsFlasque.restriction_surjective

@[stacks 09SW "surjective restriction characterization"]
#check @TopCat.Presheaf.isFlasque_iff_restriction_surjective
