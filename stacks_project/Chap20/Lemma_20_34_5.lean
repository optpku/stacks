/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedSubset.Derived.GlobalSections.Localization
import StacksCheckRecall

@[expose] public section

/- Lemma 20.34.5 (0G71): for a closed subset `Z` with open complement `Z.compl`, the canonical
forget-support and restriction maps extend functorially to a distinguished triangle
`RΓ_Z(X, K) ⟶ RΓ(X, K) ⟶ RΓ(Z.compl, K) ⟶ RΓ_Z(X, K)[1]`.
The bundled closed-subset owner and its objectwise companion live in
`AlgebraicGeometry.RingedSpace.ClosedSubset.GlobalSectionsWithSupport.Localization`. -/

@[stacks 0G71]
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.GlobalSectionsWithSupport.Localization.exists_boundary

#check @AlgebraicGeometry.RingedSpace.ClosedSubset.GlobalSectionsWithSupport.Localization.openTerm
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.GlobalSectionsWithSupport.Localization.shifted
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.GlobalSectionsWithSupport.Localization.triangleFunctor
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.GlobalSectionsWithSupport.Localization.IsBoundary
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.GlobalSectionsWithSupport.Localization.triangle
