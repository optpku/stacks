module

import ReasLib.CategoryTheory.ObjectProperty.Localization.Triangulated.VerdierQuotient.Factorization
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.6.8

The reusable content of the proof is owned by `ReasLib`: vanishing on an
object property implies inversion of its Verdier morphisms, and homological or
exact structure descends through an arbitrary triangulated localization.  This
file retains the source-facing strict existence-and-uniqueness formulation.
-/

/- Lemma 13.6.8 (1): a homological functor vanishing on `P` admits a unique
strict homological factorization through the Verdier quotient. -/
@[stacks 05RJ]
#check @CategoryTheory.ObjectProperty.VerdierQuotient.Homological.existsUnique

/- The reusable homological API exposes the canonical factor, its comparison,
homologicality, and its action on morphisms from the quotient functor. -/
#check @CategoryTheory.ObjectProperty.VerdierQuotient.Homological.factor
#check @CategoryTheory.ObjectProperty.VerdierQuotient.Homological.factor.facIso
#check @CategoryTheory.ObjectProperty.VerdierQuotient.Homological.factor.isHomological
#check @CategoryTheory.ObjectProperty.VerdierQuotient.Homological.factor.map_Q

/- Lemma 13.6.8 (2): an exact functor vanishing on `P` admits a unique strict
factorization through the Verdier quotient with triangulated structure. -/
@[stacks 05RJ]
#check @CategoryTheory.ObjectProperty.VerdierQuotient.Exact.existsUnique

/- The reusable exact API additionally installs the canonical shift comparison
and triangulated-functor instance on the factor. -/
#check @CategoryTheory.ObjectProperty.VerdierQuotient.Exact.factor
#check @CategoryTheory.ObjectProperty.VerdierQuotient.Exact.factor.facIso
#check @CategoryTheory.ObjectProperty.VerdierQuotient.Exact.factor.commShift
#check @CategoryTheory.ObjectProperty.VerdierQuotient.Exact.factor.isTriangulated
#check @CategoryTheory.ObjectProperty.VerdierQuotient.Exact.factor.map_Q
