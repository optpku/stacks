/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialSet.OpenHypercovering.CohomologicalDescent
import StacksCheckRecall

/-!
# Remark 25.11.2

The simplicial family of opens supplies the augmentation, while degreewise pulled-back sheaves
and the descent spectral-sequence predicate are owned by the reusable
`SimplicialObject.Augmented` library.
-/

/- Remark 25.11.2: an open hypercovering determines the augmented simplicial topological space
`U_• → X`. -/
@[stacks 02N9 "augmented simplicial space"] #check
  @SSet.OpenFamily.simplicialSpace.augmented

/- Its degree-`p` object is the disjoint union `Σ i : I_p, U_i`, and its structure and base maps
come from the inclusions among the indexed opens. -/
#check @SSet.OpenFamily.simplicialSpace.obj
#check @SSet.OpenFamily.simplicialSpace.map
#check @SSet.OpenFamily.simplicialSpace.toBase

/- Its `E₁` terms are the canonical objects `H^q(U_p, ε_p^*ℱ)`. -/
#check @CategoryTheory.SimplicialObject.Augmented.pullbackSheaf
#check @CategoryTheory.SimplicialObject.Augmented.degreeCohomology
#check @CategoryTheory.SimplicialObject.Augmented.IsPageOne

/- Cohomological descent for a specified total-cohomology construction is a reusable property,
separate from the open-hypercovering existence theorem. -/
#check @CategoryTheory.SimplicialObject.Augmented.IsCohomologicalDescent
#check @CategoryTheory.CohomologicalSpectralSequenceNat.AbutsTo
#check @CategoryTheory.SimplicialObject.Augmented.IsDescentSpectralSequence
#check @CategoryTheory.SimplicialObject.Augmented.IsDescentSpectralSequence.pageOne
#check @CategoryTheory.SimplicialObject.Augmented.IsDescentSpectralSequence.abutsTo

/- Remark 25.11.2 (Tag 02N9): the resulting `E₁` spectral sequence is represented by the
canonical descent predicate; existence is supplied only after the later cohomological-descent
comparison data are available. -/
@[stacks 02N9 "E1 spectral sequence interface"]
#check @SSet.OpenHypercovering.simplicialSpace.descentPredicate
