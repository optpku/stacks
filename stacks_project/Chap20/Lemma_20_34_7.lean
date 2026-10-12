/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedSubset.Derived.OpenPushforward
import StacksCheckRecall

@[expose] public section

/- Lemma 20.34.7 (0G73): if an open subset `U` is disjoint from a closed subset `Z`, then
derived sections with support in `Z` vanish after derived pushforward from `U`.  The reusable
owner uses a bundled `Z : Closeds X`, offers the canonical hypothesis `U ≤ Z.compl`, and also
exposes the source-facing `Disjoint (U : Set X) (Z : Set X)` formulation. -/

@[stacks 0G73]
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.Derived.OpenPushforward.localCohomology
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.Derived.OpenPushforward.disjoint_iff_le_compl
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.Derived.OpenPushforward.isZero_of_le_compl
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.Derived.OpenPushforward.isZero_of_disjoint
