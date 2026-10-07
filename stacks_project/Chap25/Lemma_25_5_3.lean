module

public import ReasLib.CategoryTheory.Sites.Hypercovering.Cech.ComparisonData
import StacksCheckRecall

/-!
# Lemma 25.5.3 compatibility

The natural comparison and bifunctorial spectral-sequence system are owned by
`ReasLib.CategoryTheory.Sites.Hypercovering.Cech.ComparisonData`. This file preserves the
chapter import path and source label.
-/

/- Lemma 25.5.3 (1): the Cech complex of a fixed-target hypercovering maps naturally in the
coefficient sheaf to derived cohomology over the target object in `D⁺`. -/
@[stacks 01GY "derived comparison"] #check
  @CategoryTheory.Hypercovering.Cech.derivedComparison_nonempty

/- Lemma 25.5.3 (1), degreewise consequence. -/
@[stacks 01GY "degreewise comparison"] #check
  @CategoryTheory.Hypercovering.Cech.DerivedComparison.degreeSystem_nonempty

/- The degreewise comparison admits the stronger refinement-natural packaging used by the
colimit API. -/
#check @CategoryTheory.Hypercovering.Cech.RefinementComparison
#check @CategoryTheory.Hypercovering.Cech.RefinementComparison.Derived
#check @CategoryTheory.Hypercovering.Cech.RefinementComparison.Derived.pullback
#check @CategoryTheory.Hypercovering.Cech.RefinementComparison.derived_nonempty

/- Lemma 25.5.3 (2): the first-quadrant spectral sequence is functorial in the hypercovering and
coefficient sheaf, has `E₂^{p,q}` equal to Čech cohomology of the canonical cohomology presheaf,
and abuts to objectwise sheaf cohomology. -/
@[stacks 01GY "spectral sequence"] #check
  @CategoryTheory.Hypercovering.Cech.spectralSequenceSystem_nonempty
#check @CategoryTheory.Hypercovering.Cech.SpectralSequenceSystem
#check @CategoryTheory.Hypercovering.Cech.SpectralSequenceSystem.pullback
#check @CategoryTheory.Hypercovering.Cech.presheafCohomologyInCoefficients
#check @CategoryTheory.E₂CohomologicalSpectralSequenceNat.AbutsTo
