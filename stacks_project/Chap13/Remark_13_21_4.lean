module

import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence
import StacksCheckRecall

@[expose] public section

/-!
# Remark 13.21.4

Associated spectral sequences and their functoriality are owned by the neutral filtered-complex
API.  This source file records the two source-facing recalls.
-/

/- Remark 13.21.4 (1): every filtered complex admits an associated cohomological spectral
sequence. -/
@[stacks 015K] #check @CategoryTheory.FilteredComplex.IsAssociated.exists

/- Remark 13.21.4 (2): a filtered-complex morphism induces a unique compatible morphism between
any chosen associated spectral sequences. -/
@[stacks 015K] #check @CategoryTheory.FilteredComplex.Association.IsCompatible.existsUnique
