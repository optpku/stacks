module

import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Biproduct
import ReasLib.CategoryTheory.Functor.Derived.Definedness.Retracts
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.14.7 (05SD)

The chapter entry is a source-facing recall of the neutral biproduct and retract API.  The
essential-constancy statements live under `Functor.RightDerived.DefinedAt` and
`Functor.LeftDerived.DefinedAt`; the weaker `HasPointwise*DerivedFunctorAt` clauses use the
retract-stability instances for the corresponding object properties and mathlib's generic
direct-summand API.  Identity-denominator square calculations are shared by the pointwise-value
leaf.
-/

open CategoryTheory

/- Lemma 13.14.7 (1) and (5): the split distinguished triangle of a binary biproduct gives
source-definedness of the biproduct from source-definedness of both summands. -/
@[stacks 05SD "(1)"] #check @Functor.RightDerived.DefinedAt.of_biprod
@[stacks 05SD "(5)"] #check @Functor.LeftDerived.DefinedAt.of_biprod

/- Lemma 13.14.7 (2), (3), (6), and (7): in a Karoubian target, pointwise existence descends to
the two direct summands by specializing the canonical retract-stability API. -/
@[stacks 05SD "(2)"] #check @ObjectProperty.IsStableUnderRetracts.of_biprod_left
@[stacks 05SD "(3)"] #check @ObjectProperty.IsStableUnderRetracts.of_biprod_right
@[stacks 05SD "(6)"] #check @ObjectProperty.IsStableUnderRetracts.of_biprod_left
@[stacks 05SD "(7)"] #check @ObjectProperty.IsStableUnderRetracts.of_biprod_right

/- Lemma 13.14.7 (4) and (8): the pointwise derived-value comparison induced by the two
biproduct inclusions is invertible. -/
@[stacks 05SD "(4)"] #check @Functor.RightDerived.Biproduct.descIsIso
@[stacks 05SD "(8)"] #check @Functor.LeftDerived.Biproduct.descIsIso

/- The denominator-square and identity-map calculations used by the source proof are now neutral
pointwise-value API, rather than chapter-local helper declarations. -/
#check @CategoryTheory.Functor.RightDerived.Value.ι_of_id_square
#check @CategoryTheory.Functor.LeftDerived.Value.π_of_id_square
#check @CategoryTheory.Functor.RightDerived.Value.map_id
#check @CategoryTheory.Functor.LeftDerived.Value.map_id
