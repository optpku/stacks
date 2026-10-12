/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Koszul
import StacksCheckRecall

/-!
# Definition 17.24.2 compatibility entry point

The canonical free-to-structure-module map and the resulting finite-family Koszul objects are the
only constructions here that genuinely use the topological global-sections API. Their underlying
complex and commutative algebra come directly from the generic ringed-site owner.
-/

@[expose] public section

open AlgebraicGeometry

/- Definition 17.24.2 (062L): a finite family of global sections determines the Koszul complex
of the associated morphism from a finite free module sheaf to the structure module. -/
@[stacks 062L]
#check @RingedSpace.Koszul.complexOfSections

#check @RingedSpace.Koszul.sectionMap
#check @RingedSpace.Koszul.commMonOfSections
#check @RingedSpace.Koszul.commMonOfSections_X
