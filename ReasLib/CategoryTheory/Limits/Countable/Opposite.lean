module

public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products

/-!
# Countable products and opposite categories

This file promotes the shape-level opposite-category instances to the aggregate countable
product and coproduct classes.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Limits

variable (C : Type u) [Category.{v} C]

/-- Countable products in `C` give countable coproducts in `Cᵒᵖ`. -/
instance hasCountableCoproducts_opposite [HasCountableProducts C] :
    HasCountableCoproducts Cᵒᵖ where
  out X := hasCoproductsOfShape_opposite X

/-- Countable coproducts in `C` give countable products in `Cᵒᵖ`. -/
instance hasCountableProducts_opposite [HasCountableCoproducts C] :
    HasCountableProducts Cᵒᵖ where
  out X := hasProductsOfShape_opposite X

end CategoryTheory.Limits
