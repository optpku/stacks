/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.Filtered.Stupid
import StacksCheckRecall

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.SpectralSequence.Stupid

/- [stacks 0FLK] Example 20.29.4: the stupid filtration of a complex of `𝒪_X`-modules gives a
hypercohomology spectral sequence with `E₁^{p,q} = H^q(X, K^p)`. For a bounded-below complex it
is bounded and converges to hypercohomology, and it compares with the first Cartan--Eilenberg
spectral sequence by an isomorphism from `E₁` onward. -/

#check @CochainComplex.StupidFiltration.stageIso
#check @CochainComplex.stupidFiltration_hasFiniteFiltrations
#check @Realization
#check @Realization.filtered
#check @Realization.sequence
#check @Realization.gradedPieceIso
#check @Realization.pageOneIso
#check @Realization.pageOneMap
#check @Realization.pageOneCommSq
#check @Realization.pageOneIsZero
#check @Realization.targetIso
#check @Realization.isAssociated
@[stacks 0FLK] #check @Realization.nonempty
#check @Realization.isBounded
#check @Realization.finite
#check @Realization.converges
#check @Realization.cartanEilenbergComparison

end AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.SpectralSequence.Stupid
