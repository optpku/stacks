/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Cech.ComparisonData
import StacksCheckRecall

/-!
# Lemma 25.6.4 compatibility

The coefficient-natural comparison, additive-presheaf second page, functoriality in both
variables, and filtered abutment are owned by the presheaf-target Cech comparison leaf.
-/

/- Lemma 25.6.4 [stacks 09VX], primary comparison clause: the Cech complex maps naturally in
the coefficient sheaf to derived cohomology over the target presheaf in `D⁺`. -/
@[stacks 09VX "derived comparison"] #check
  @CategoryTheory.HypercoveringOf.Cech.derivedComparison_nonempty

/- Lemma 25.6.4 [stacks 09VX], degreewise consequence of the derived comparison. -/
@[stacks 09VX "degreewise comparison"] #check
  @CategoryTheory.HypercoveringOf.Cech.DerivedComparison.degreeSystem_nonempty

/- The comparisons used by the spectral system are simultaneously natural in refinement
classes and coefficient sheaves. -/
#check @CategoryTheory.HypercoveringOf.Cech.RefinementComparison
#check @CategoryTheory.HypercoveringOf.Cech.RefinementComparison.Derived
#check @CategoryTheory.HypercoveringOf.Cech.RefinementComparison.derived_nonempty

/- Lemma 25.6.4 [stacks 09VX], spectral-sequence clause: the construction is functorial in the
coefficient sheaf and the hypercovering, with the canonical Cech second page and a filtered
abutment to cohomology over the target presheaf. -/
@[stacks 09VX "spectral sequence"] #check
  @CategoryTheory.HypercoveringOf.Cech.spectralSequenceSystem_nonempty

#check @CategoryTheory.HypercoveringOf.Cech.DerivedComparison
#check @CategoryTheory.HypercoveringOf.Cech.DegreeComparison
#check @CategoryTheory.HypercoveringOf.Cech.SpectralSequenceSystem
#check @CategoryTheory.HypercoveringOf.Cech.presheafCohomologyInCoefficients
#check @CategoryTheory.Sheaf.cohomologyOverPresheafFunctor
#check @CategoryTheory.E₂CohomologicalSpectralSequenceNat.AbutsTo
