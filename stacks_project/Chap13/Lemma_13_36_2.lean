module

import ReasLib.CategoryTheory.Pretriangulated.Generation.Generated
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty
open scoped CategoryTheory.ObjectProperty.GeneratedNotation

-- Lemma 13.36.2: the generated thick object property and its universal property are now owned
-- by the reusable pretriangulated generation API.
@[stacks 0ATG] #check @CategoryTheory.ObjectProperty.triangEnvelope
#check @CategoryTheory.ObjectProperty.Generated.property
#check @CategoryTheory.ObjectProperty.Generated.Property.eq_triangEnvelope
#check @CategoryTheory.ObjectProperty.Generated.Property.eq_iSup_stage
#check @CategoryTheory.ObjectProperty.Generated.Property.mem_iff
#check @CategoryTheory.ObjectProperty.Generated.Property.le_iff
#check @CategoryTheory.ObjectProperty.Generated.Property.le_of_mem
