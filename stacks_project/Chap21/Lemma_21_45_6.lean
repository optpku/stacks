/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.PseudoCoherent.Retracts
import StacksCheckRecall

@[expose] public section

/- Lemma 21.45.6 (1) (08FW): the left summand of an `m`-pseudo-coherent biproduct is
`m`-pseudo-coherent. -/
@[stacks 08FW "(1)"]
#check @RingedSite.Hom.ModuleDerived.IsMPseudoCoherent.left

/- Lemma 21.45.6 (2) (08FW): the right summand of an `m`-pseudo-coherent biproduct is
`m`-pseudo-coherent. -/
@[stacks 08FW "(2)"]
#check @RingedSite.Hom.ModuleDerived.IsMPseudoCoherent.right

/- Lemma 21.45.6 (3) (08FW): the left summand of a pseudo-coherent biproduct is
pseudo-coherent. -/
@[stacks 08FW "(3)"]
#check @RingedSite.Hom.ModuleDerived.IsPseudoCoherent.left

/- Lemma 21.45.6 (4) (08FW): the right summand of a pseudo-coherent biproduct is
pseudo-coherent. -/
@[stacks 08FW "(4)"]
#check @RingedSite.Hom.ModuleDerived.IsPseudoCoherent.right

#check @RingedSite.Hom.ModuleDerived.IsMPseudoCoherent.summands
#check @RingedSite.Hom.ModuleDerived.IsPseudoCoherent.summands
#check @RingedSite.Hom.ModuleDerived.mPseudoCoherent_isStableUnderRetracts
#check @RingedSite.Hom.ModuleDerived.pseudoCoherent_isStableUnderRetracts
