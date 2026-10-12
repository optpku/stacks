/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Triangulated.Subcategory

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u v

namespace CategoryTheory.ObjectProperty

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- The inclusion of a full triangulated subcategory is representably coflat. -/
instance representablyCoflat_ι (P : ObjectProperty D) [P.IsTriangulated] :
    RepresentablyCoflat P.ι := sorry

end CategoryTheory.ObjectProperty
