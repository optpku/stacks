/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.OpenImmersion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

/- Lemma 26.3.4: an open immersion is uniquely isomorphic to the restriction
of its target to its image open. -/
#check LocallyRingedSpace.IsOpenImmersion.isoRestrict
#check LocallyRingedSpace.IsOpenImmersion.eq_isoRestrict_hom_iff
@[stacks 01HH] #check LocallyRingedSpace.IsOpenImmersion.existsUnique_isoRestrict
