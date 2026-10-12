/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.NonvanishingOpen
import StacksCheckRecall

@[expose] public section

/- Remark 17.25.11 (0H78): the inverse image of the nonvanishing open of a section of an
invertible module sheaf is the nonvanishing open of its pulled-back section. -/
@[stacks 0H78]
#check @AlgebraicGeometry.LocallyRingedSpace.SectionNonvanishing.comap_open

/- The underlying nonvanishing-locus equality is valid for every module sheaf. -/
#check @AlgebraicGeometry.LocallyRingedSpace.SectionNonvanishing.preimage_locus

/- The compatible section pulled back by the adjunction unit is reusable independently of
nonvanishing loci. -/
#check @AlgebraicGeometry.LocallyRingedSpace.Hom.pullbackSections
