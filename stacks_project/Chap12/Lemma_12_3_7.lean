module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import StacksCheckRecall

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

section

variable {A : Type u₁} [Category.{v₁} A] [Preadditive A]
variable {B : Type u₂} [Category.{v₂} B] [Preadditive B]
variable (F : A ⥤ B) [F.Additive]

/- Lemma 12.3.7 (1): this is a source-facing use of the canonical owner abstraction
`Functor.Additive`. In mathlib, additivity gives `PreservesFiniteBiproducts F`, and binary direct
sums are then recovered through the canonical derived instance `PreservesBinaryBiproducts F`. -/
@[stacks 0105] #check
  (preservesBinaryBiproducts_of_preservesBiproducts F : PreservesBinaryBiproducts F)

/- Lemma 12.3.7 (2): preservation of zero objects is derived API, not extra primitive data. Once
`F` is additive, the canonical owner theorem is `Functor.map_isZero`. -/
@[stacks 0105] #check @Functor.map_isZero

end

end CategoryTheory
