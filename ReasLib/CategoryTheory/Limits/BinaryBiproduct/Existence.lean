module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Existence of Binary Biproducts

In a preadditive category, either a binary product or a binary coproduct canonically supplies
the common binary-biproduct owner. This file exposes the resulting existence equivalence.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- A binary product of two objects in a preadditive category exists if and only if their binary
coproduct exists. -/
@[stacks 0101]
theorem hasBinaryProduct_iff_hasBinaryCoproduct (X Y : C) :
    HasBinaryProduct X Y ↔ HasBinaryCoproduct X Y := by
  constructor
  · intro h
    letI := h
    letI : HasBinaryBiproduct X Y := HasBinaryBiproduct.of_hasBinaryProduct X Y
    infer_instance
  · intro h
    letI := h
    letI : HasBinaryBiproduct X Y := HasBinaryBiproduct.of_hasBinaryCoproduct X Y
    infer_instance

end CategoryTheory.Limits
