/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedSubset.Derived.Localization
import StacksCheckRecall

@[expose] public section

/- Lemma 20.34.6 (0G72): the localization triangle for a closed subset and its open complement
is owned by the bundled module-level API.  For a raw closed set `Z` with `hZ : IsClosed Z`, use
the bundled object `Closeds.mk Z hZ`; the owner then exposes the closed-support term, the
open-complement term, both canonical maps, the functorial boundary predicate, and the
objectwise distinguished-triangle statement. -/

@[stacks 0G72]
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.Derived.Localization.closedTerm
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.Derived.Localization.openTerm
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.Derived.Localization.closedMap
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.Derived.Localization.openMap
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.Derived.Localization.shifted
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.Derived.Localization.IsBoundary
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.Derived.Localization.exists_boundary
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.Derived.Localization.triangle
