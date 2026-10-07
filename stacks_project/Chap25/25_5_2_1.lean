module

public import ReasLib.CategoryTheory.Sites.Hypercovering.Cech.Cohomology
import StacksCheckRecall

/- Equation 25.5.2.1: the product-of-sections complex of a semi-representable hypercovering is
canonically identified with the Hom complex out of its degreewise free abelian sheafification. -/
@[stacks 01GX] #check
  @CategoryTheory.Hypercovering.Cech.familySectionsComplex_isomorphic_complex

#check @CategoryTheory.Hypercovering.Cech.familySectionsFunctor
#check @CategoryTheory.Hypercovering.Cech.familySectionsComplex
#check @CategoryTheory.HypercoveringOf.Cech.sectionsFunctor
#check @CategoryTheory.Hypercovering.Cech.complex
