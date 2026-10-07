module

public import ReasLib.CategoryTheory.Limits.BinaryBiproduct.Existence
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

section

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (X Y : C)

/- Core/canonical owner declaration used in Lemma 12.3.4: in a preadditive category, a binary
product canonically yields a binary biproduct. -/
#check HasBinaryBiproduct.of_hasBinaryProduct

/- Core/canonical owner declaration used in Lemma 12.3.4: dually, a binary coproduct canonically
yields a binary biproduct. -/
#check HasBinaryBiproduct.of_hasBinaryCoproduct

/- Lemma 12.3.4: in a preadditive category, a binary product of `X` and `Y` exists if and only
if a binary coproduct of `X` and `Y` exists. -/
@[stacks 0101] #check hasBinaryProduct_iff_hasBinaryCoproduct X Y

end

section

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable (X Y : C) [HasBinaryBiproduct X Y]

/- The final sentence of Lemma 12.3.4 is the existing mathlib comparison isomorphism `biprodIso`
in the chosen binary biproduct context. -/
#check biprodIso

end

end CategoryTheory
