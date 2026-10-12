/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.Stalk
import StacksCheckRecall

/-!
# Pullback and stalks of module sheaves

The reusable statement is the canonical natural comparison and its invertibility in ReasLib. It is formulated for bundled
commutative ringed-site morphisms, their canonical image point, and ModuleCat-valued stalks;
no external module instances or witness-only linear equivalences are required here.
-/

@[expose] public section

/- Lemma 18.36.4: the canonical natural comparison from extension of scalars at the image
point to the stalk after pullback is invertible. -/
@[stacks 05V5]
#check (@RingedSite.Hom.pullbackStalkComparisonNatTrans_isIso)

/- The forward natural transformation retains the canonical textbook comparison as data. -/
#check (@RingedSite.Hom.pullbackStalkComparisonNatTrans)

/- Every objectwise tensor-product comparison is an isomorphism. -/
#check (@RingedSite.Hom.pullbackStalkComparison_isIso)

/- The induced point and map of stalk rings are reusable independently of module pullback. -/
#check (@RingedSite.Hom.pointMap)
#check (@RingedSite.Hom.stalkMap)
