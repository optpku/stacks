module

public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Boundary
public import ReasLib.Algebra.Homology.CochainComplex.Bifunctor.Cohomology
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/-
Lemma 20.25.4 (07MC): the two boundary maps associated to compatible pairings of short exact
sequences agree up to the Koszul sign `(-1)^(n + 1)`.

In the source, the preceding Cech-comparison hypotheses construct the two cohomology products and
show that they descend from the chain-level pairings.  The reusable owner records exactly this
interface through the explicit morphisms `cup₁`, `cup₃` and the propositions
`HomologicalComplex.CohomologyCup.IsInducedTo`; it does not install a chosen cup product as a
typeclass.  The heterogeneous companion
`HomologicalComplex.CohomologyCup.Bifunctor.boundary` keeps the coefficient bifunctor explicit,
which is the source-faithful route for `ModuleCat.TensorProduct` across universes.  The Cech
agreement hypotheses remain upstream data for a topological specialization; they are not silently
replaced by an arbitrary Cartesian monoidal structure on `AddCommGrpCat`.
-/
@[stacks 07MC "boundary morphisms and induced cohomology products"]
#check @HomologicalComplex.CohomologyCup.boundary

#check @HomologicalComplex.CohomologyCup.cycles
#check @HomologicalComplex.CohomologyCup.cyclesTo
#check @HomologicalComplex.CohomologyCup.IsInduced
#check @HomologicalComplex.CohomologyCup.IsInducedTo

/- The same boundary API with an explicit heterogeneous coefficient bifunctor `T`. -/
@[stacks 07MC "heterogeneous boundary morphisms and induced cohomology products"]
#check @HomologicalComplex.CohomologyCup.Bifunctor.boundary

#check @HomologicalComplex.CohomologyCup.Bifunctor.cycles
#check @HomologicalComplex.CohomologyCup.Bifunctor.cyclesTo
#check @HomologicalComplex.CohomologyCup.Bifunctor.IsInducedTo

end
