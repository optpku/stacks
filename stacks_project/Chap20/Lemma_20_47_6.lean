module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent.Retracts
import StacksCheckRecall

@[expose] public section

/- Lemma 20.47.6: pseudo-coherence descends to direct summands.  Retract stability is owned at
the ringed-site level; these checks recall its ringed-space biproduct interface. -/

@[stacks 08CE "(1)"]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.IsMPseudoCoherent.left

@[stacks 08CE "(2)"]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.IsMPseudoCoherent.right

@[stacks 08CE "(3)"]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.IsPseudoCoherent.left

@[stacks 08CE "(4)"]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.IsPseudoCoherent.right

-- Bundled conclusions and the actual retract-stability owners remain directly available.
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.IsMPseudoCoherent.summands
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.IsPseudoCoherent.summands
#check @RingedSite.Hom.ModuleDerived.mPseudoCoherent_isStableUnderRetracts
#check @RingedSite.Hom.ModuleDerived.pseudoCoherent_isStableUnderRetracts

