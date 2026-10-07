module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor.SpectralSequence.Kunneth.Filtered
import StacksCheckRecall

/-!
# Proposition 15.64.3

@stack 0H7Y
-/

@[expose] public section

/- Proposition 15.64.3: the filtered tensor model, first-page formula, and convergence under the
four eventual stage conditions. -/
@[stacks 0H7Y "Proposition 15.64.3"]
#check @CategoryTheory.Kunneth.Filtered.existsSpectralSequence

/- The convergence conclusion uses the canonical filtered-complex criterion. -/
#check @CategoryTheory.FilteredComplex.StageCohomology.associated_converges
