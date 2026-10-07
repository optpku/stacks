module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.NonvanishingOpen
import StacksCheckRecall

@[expose] public section

/- Lemma 17.25.10 (01CY): the nonvanishing locus of a section of an invertible module on a
locally ringed space is open. -/
@[stacks 01CY "openness"]
#check @AlgebraicGeometry.RingedSpace.sectionNonvanishingLocus_isOpen

/- Lemma 17.25.10 (01CY): on its nonvanishing open, the section trivializes the invertible
module. -/
@[stacks 01CY "trivialization"]
#check @AlgebraicGeometry.RingedSpace.SectionNonvanishing.trivialization

/- Lemma 17.25.10 (01CY): the restricted section has the canonical inverse corresponding to
the inverse section of the negative tensor power. -/
@[stacks 01CY "inverse section"]
#check @AlgebraicGeometry.RingedSpace.sectionOverInv

#check @AlgebraicGeometry.RingedSpace.sectionOverHom_comp_inv
#check @AlgebraicGeometry.RingedSpace.sectionOverInv_comp_hom
#check @AlgebraicGeometry.RingedSpace.SectionNonvanishing.trivialization_hom
#check @AlgebraicGeometry.RingedSpace.SectionNonvanishing.trivialization_inv
