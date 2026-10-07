module

public import ReasLib.CategoryTheory.Filtration.Complex.InfinityPage
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Lemma 12.24.6 (1) [012Q]: eventual boundary and cycle stages are explicit reusable data, and
their quotient is a bigraded infinity-page object. -/
@[stacks 012Q]
#check SpectralSequence.LimitStages.Data
#check SpectralSequence.LimitStages
#check SpectralSequence.LimitStages.Data.InfinityPage.π
#check SpectralSequence.LimitStages.Data.infinityPageObject
#check SpectralSequence.LimitStages.infinityPage
#check SpectralSequence.LimitStages.infinityPageObject
#check SpectralSequence.LimitStages.InfinityPage.π
#check SpectralSequence.LimitStages.infinityPage_isIsomorphic
#check SpectralSequence.LimitStages.boundary_eq
#check SpectralSequence.LimitStages.cycle_eq
#check SpectralSequence.LimitStages.eq

/- Under complete subobject lattices the limit-stage data is canonical. -/
#check SpectralSequence.canonicalLimitStages

/- Lemma 12.24.6 (2) [012Q]: each graded piece of the induced cohomology filtration is a
subquotient of the corresponding infinity-page entry. -/
@[stacks 012Q]
#check FilteredComplex.Cohomology.GradedPiece.isSubquotient_of_limitPage
#check FilteredComplex.Cohomology.GradedPiece.isSubquotient_of_limitPageQuotient

/- The canonical-lattice specialization targets the existing public infinity page directly. -/
#check FilteredComplex.Cohomology.GradedPiece.isSubquotient_of_infinityPage
