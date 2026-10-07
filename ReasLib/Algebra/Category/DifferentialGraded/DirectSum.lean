module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.DifferentialGraded.Closed

/-!
# Binary direct sums in differential graded categories

Closed degree-zero morphisms already form the ordinary preadditive category `Comp R A`.
Consequently a concrete direct sum in that category is exactly mathlib's
`BinaryBiproductData`; no additional differential-graded choice or typeclass is needed.
-/

@[expose] public section

namespace DifferentialGradedCategory

open CategoryTheory CategoryTheory.Limits

universe u v

variable {R : Type u} [CommRing R]
variable {A : Type v} [DifferentialGradedCategory R A]

/-- Build explicit binary-biproduct data in `Comp R A` from a binary bicone satisfying the
standard total identity.  The bicone itself carries the closed degree-zero structure maps. -/
@[stacks 09P4]
def binaryBiproductDataOfTotal {x y : Comp R A} (c : BinaryBicone x y)
    (total : c.fst ≫ c.inl + c.snd ≫ c.inr = 𝟙 c.pt) :
    BinaryBiproductData x y where
  bicone := c
  isBilimit := isBinaryBilimitOfTotal c total

end DifferentialGradedCategory
