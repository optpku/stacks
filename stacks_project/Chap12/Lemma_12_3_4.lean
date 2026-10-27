/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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
#check (@HasBinaryBiproduct.of_hasBinaryProduct :
  ∀ {C : Type u} [Category.{v} C] [Preadditive C] (X Y : C) [HasBinaryProduct X Y],
    HasBinaryBiproduct X Y)

/- Core/canonical owner declaration used in Lemma 12.3.4: dually, a binary coproduct canonically
yields a binary biproduct. -/
#check (@HasBinaryBiproduct.of_hasBinaryCoproduct :
  ∀ {C : Type u} [Category.{v} C] [Preadditive C] (X Y : C) [HasBinaryCoproduct X Y],
    HasBinaryBiproduct X Y)

/- Lemma 12.3.4: in a preadditive category, a binary product of `X` and `Y` exists if and only
if a binary coproduct of `X` and `Y` exists. -/
@[stacks 0101] #check (@hasBinaryProduct_iff_hasBinaryCoproduct :
  ∀ {C : Type u} [Category.{v} C] [Preadditive C] (X Y : C),
    HasBinaryProduct X Y ↔ HasBinaryCoproduct X Y)

end

section

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable (X Y : C) [HasBinaryBiproduct X Y]

/- The final sentence of Lemma 12.3.4 is the existing mathlib comparison isomorphism `biprodIso`
in the chosen binary biproduct context. -/
#check (@biprodIso :
  ∀ {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (X Y : C)
    [HasBinaryBiproduct X Y],
    Limits.prod X Y ≅ Limits.coprod X Y)

end

end CategoryTheory
