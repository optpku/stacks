/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# A short exact complex from a binary biproduct

In a preadditive category, the difference map from an object to its binary biproduct,
followed by the sum map back to the object, forms a short exact complex.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u v

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (M : C) [HasBinaryBiproduct M M]

/-- The short complex whose first map has components `(-1, 1)` and whose second map has
components `(1, 1)`. -/
noncomputable def biprodDifferenceSum : ShortComplex C :=
  ShortComplex.mk
    (biprod.lift (-𝟙 M) (𝟙 M))
    (biprod.desc (𝟙 M) (𝟙 M))
    (by simp [biprod.lift_desc])

/-- The first map of the difference-sum short complex has components `(-1, 1)`. -/
@[simp]
theorem biprodDifferenceSum_f :
    (biprodDifferenceSum M).f = biprod.lift (-𝟙 M) (𝟙 M) := rfl

/-- The second map of the difference-sum short complex has components `(1, 1)`. -/
@[simp]
theorem biprodDifferenceSum_g :
    (biprodDifferenceSum M).g = biprod.desc (𝟙 M) (𝟙 M) := rfl

variable [HasZeroObject C]

/-- The difference-sum short complex associated to a binary biproduct is short exact. -/
theorem biprodDifferenceSum_shortExact :
    (biprodDifferenceSum M).ShortExact := sorry

end CategoryTheory.ShortComplex
