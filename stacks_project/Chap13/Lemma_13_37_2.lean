module

import ReasLib.CategoryTheory.Pretriangulated.CompactObject
import StacksCheckRecall

@[expose] public section

open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [Preadditive D]
  [HasCoproducts.{max u v} D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

@[stacks 09QH] #check @isCompactObject_isStableUnderRetracts
#check @isCompactObject_isTriangulated
#check @isCompactObject_of_retract
#check @isCompactObject_iff_of_iso
#check @isCompactObject_of_distinguished
#check (inferInstance : Pretriangulated (compactObjectSubcategory D))

variable [IsTriangulated D]

#check (inferInstance : IsTriangulated (compactObjectSubcategory D))

#check (inferInstance : IsIdempotentComplete D)
#check (inferInstance : IsIdempotentComplete (compactObjectSubcategory D))

end

end CategoryTheory
