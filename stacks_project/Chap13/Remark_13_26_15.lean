module

import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.AlternativeFiltrations
import StacksCheckRecall

@[expose] public section

/-!
# Remark 13.26.15

The reusable owner records the two alternative filtrations and their comparisons with the
standard Cartan--Eilenberg spectral sequences.
-/

namespace CochainComplex.CartanEilenbergResolution.SpectralSequence

/- Remark 13.26.15 (`015X`) (1): the stupid-filtration construction. -/
@[stacks 015X] #check @Stupid.nonempty
#check @Stupid.Realization
@[stacks 015X] #check @CategoryTheory.CochainComplex.StupidFiltration.stageIso

/- Remark 13.26.15 (`015X`) (2): the truncation-filtration construction. -/
#check @Truncation.nonempty
#check @Truncation.Realization
@[stacks 015X] #check @CategoryTheory.CochainComplex.TruncationFiltration.stageIso
@[stacks 015X] #check @CategoryTheory.CochainComplex.TruncationFiltration.stageIso_hom_comp_inclusion

/- Comparison with the first Cartan--Eilenberg spectral sequence. -/
#check @First.comparison
#check @First.Comparison

/- Comparison with the second Cartan--Eilenberg spectral sequence. -/
#check @Second.comparison
#check @Second.Comparison

end CochainComplex.CartanEilenbergResolution.SpectralSequence
