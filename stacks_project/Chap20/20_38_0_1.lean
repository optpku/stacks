/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Truncation.LowerResolution
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- 20.38.0.1 (070F): the canonical map from a complex into the inverse limit of a
lower-truncation resolution is owned by the generic resolution tower API. -/
@[stacks 071A "20.38.0.1: canonical map into a lower-truncation resolution limit"]
#check @CochainComplex.LowerTruncation.Resolution.intoLimit

/- The map is characterized by its composites with the tower projections. -/
@[stacks 071A "20.38.0.1: projection formula for the lower-truncation limit map"]
#check @CochainComplex.LowerTruncation.Resolution.intoLimit_comp_π

section

variable {X : RingedSpace.{u}}
variable {F : CochainComplex (RingedSpace.Modules X) ℤ}
variable (S : CochainComplex.LowerTruncation.Resolution
  (isInjective (RingedSpace.Modules X)) F)
variable [HasLimit S.tower]

/- Ringed-space specialization of the canonical map; no second chapter-level owner is introduced. -/
@[stacks 071A "20.38.0.1: ringed-space specialization"]
#check (S.intoLimit : F ⟶ limit S.tower)

end

end AlgebraicGeometry.RingedSpace
