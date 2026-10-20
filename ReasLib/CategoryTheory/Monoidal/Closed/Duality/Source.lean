module

public import ReasLib.CategoryTheory.Monoidal.Closed.Duality
public import ReasLib.CategoryTheory.Monoidal.Closed.Source

/-!
# Source-order formulas for the canonical closed-monoidal dual

The canonical tensor comparison for `dual X = (ihom X).obj (𝟙_ C)` is the source-order
tensor/internal-Hom comparison followed by the right unitor.  These formulas bridge the generic
duality API and the source-order API used by complexes and derived categories.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe v u

namespace CategoryTheory.MonoidalClosed.Dual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable [BraidedCategory C] [MonoidalClosed C]

/-- The canonical dual tensor comparison is the source-order tensor/internal-Hom comparison
followed by the right unitor in its target. -/
@[stacks 08I2 "source formula for the canonical dual tensor comparison"]
theorem tensorComparison_eq_sourceTensor (X M : C) :
    tensorComparison X M =
      Source.tensor M (𝟙_ C) X ≫ (ihom X).map (ρ_ M).hom := sorry

/-- The tensor-to-endomorphism comparison is the self specialization of the source-order
tensor/internal-Hom comparison followed by the right unitor. -/
@[stacks 0FNY "source formula for the tensor-to-endomorphism comparison"]
theorem tensorIhomUnitToEnd_eq_sourceTensor (X : C) :
    tensorIhomUnitToEnd X =
      Source.tensor X (𝟙_ C) X ≫ (ihom X).map (ρ_ X).hom := sorry

end CategoryTheory.MonoidalClosed.Dual
