/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.ObjectProperty.Zero
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {D : Type u₁} [Category.{v₁} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable {D' : Type u₂} [Category.{v₂} D'] [HasZeroObject D'] [HasShift D' ℤ]
  [Preadditive D'] [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']
variable (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]

/- Lemma 13.6.2 (1): the kernel of an exact functor is strictly full. -/
@[stacks 05RC "strict fullness of the kernel"] #check
  (inferInstance : F.kernel.IsClosedUnderIsomorphisms)

/- Lemma 13.6.2 (2): the kernel is saturated, modeled canonically as retract stability. -/
@[stacks 05RC "retract stability of the kernel"] #check
  (inferInstance : F.kernel.IsStableUnderRetracts)

/- Lemma 13.6.2 (3): the kernel is a pretriangulated object property. -/
@[stacks 05RC "triangulated kernel object property"] #check
  (inferInstance : F.kernel.IsTriangulated)

section

variable [IsTriangulated D]

/- Lemma 13.6.2 (4): in a triangulated ambient category, the full kernel subcategory is
triangulated. -/
@[stacks 05RC "triangulated full kernel subcategory"] #check
  (inferInstance : IsTriangulated F.kernel.FullSubcategory)

end


end CategoryTheory
