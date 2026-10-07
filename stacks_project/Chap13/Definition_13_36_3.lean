module

import ReasLib.CategoryTheory.Pretriangulated.Generation.Generated
import ReasLib.CategoryTheory.Pretriangulated.Generation.Orthogonal
import Mathlib.CategoryTheory.Triangulated.Generators
import StacksCheckRecall

@[expose] public section

open CategoryTheory

-- Definition 13.36.3: weak generation is owned by the reusable orthogonality API, while
-- classical and strong triangulated generation use Mathlib's canonical object-property owners.
@[stacks 09SJ] #check @CategoryTheory.IsWeakGenerator
#check @CategoryTheory.IsGeneratingFamily
#check @CategoryTheory.isWeakGenerator_iff_rightOrthogonal_shifts_eq_isZero
#check @CategoryTheory.ObjectProperty.triangEnvelopeIter
#check @CategoryTheory.ObjectProperty.triangEnvelope
#check @CategoryTheory.ObjectProperty.IsClassicalTriangulatedGenerator
#check @CategoryTheory.ObjectProperty.IsStrongTriangulatedGenerator
#check @CategoryTheory.ObjectProperty.triangEnvelope_le_iff
