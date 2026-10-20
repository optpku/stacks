module

import ReasLib.CategoryTheory.Pretriangulated.Generation.Compact
import StacksCheckRecall

@[expose] public section

open CategoryTheory

-- Definition 13.37.5: compact generation and its generating-family characterizations are owned
-- by the reusable pretriangulated generation API.
@[stacks 09SQ] #check @CategoryTheory.IsCompactlyGenerated
#check @CategoryTheory.isWeakGenerator_coproduct_iff_isGeneratingFamily
#check @CategoryTheory.isCompactlyGenerated_iff_exists_compact_generatingFamily
#check @CategoryTheory.isCompactlyGenerated_iff_exists_compactSubcategory_generatingFamily
