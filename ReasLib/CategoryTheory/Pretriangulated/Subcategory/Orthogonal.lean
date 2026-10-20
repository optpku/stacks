module

public import ReasLib.CategoryTheory.Pretriangulated.Subcategory.Coproduct
public import Mathlib.CategoryTheory.Triangulated.Orthogonal
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Orthogonal Extension Products

This leaf records the two canonical semiorthogonal extension products of a
triangulated object property.  The statements belong to `ObjectProperty`, not
to a particular localization or semiorthogonal-decomposition construction.
-/

namespace CategoryTheory.ObjectProperty

universe v u

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D]

/-- Stacks 0CQR, Lemma 13.40.5: the extension product of a triangulated object property
with its right orthogonal is triangulated. -/
@[stacks 0CQR]
instance extensionProduct_rightOrthogonal_isTriangulated [IsTriangulated D]
    (A : ObjectProperty D) [A.IsTriangulated] :
    (extensionProduct A A.rightOrthogonal).IsTriangulated := sorry

/-- Stacks 0H0N, Lemma 13.40.6: the extension product of the left orthogonal of a
triangulated object property with that property is triangulated. -/
@[stacks 0H0N]
instance leftOrthogonal_extensionProduct_isTriangulated [IsTriangulated D]
    (A : ObjectProperty D) [A.IsTriangulated] :
    (extensionProduct A.leftOrthogonal A).IsTriangulated := sorry

end CategoryTheory.ObjectProperty
