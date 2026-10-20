module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor.SpectralSequence.Kunneth
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.64.4 (Künneth Spectral Sequence)

@stack 0H7Z
-/

/- Lemma 15.64.4 (Künneth Spectral Sequence) (`0H7Z`): the bounded Künneth spectral sequence,
its Tor page-two terms, boundedness, and derived-tensor abutment are owned by ReasLib. -/
@[stacks 0H7Z]
#check @CategoryTheory.exists_kunnethDerivedTensorSpectralSequence

#check @CategoryTheory.boundedDerivedTensorCohomology
#check @CategoryTheory.kunnethDerivedTensorPageTwo
#check @CategoryTheory.ConvergesToDerivedTensorCohomology
#check @CategoryTheory.ConvergesToDerivedTensorCohomology.spec
#check @CategoryTheory.IsKunnethDerivedTensorSpectralSequence
#check @CategoryTheory.IsKunnethDerivedTensorSpectralSequence.spec
#check @CategoryTheory.IsKunnethDerivedTensorSpectralSequence.isBounded
#check @CategoryTheory.IsKunnethDerivedTensorSpectralSequence.pageTwoIso
#check @CategoryTheory.IsKunnethDerivedTensorSpectralSequence.converges
