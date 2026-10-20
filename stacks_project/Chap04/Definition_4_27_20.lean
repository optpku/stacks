/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.MorphismProperty.SaturatedMultiplicativeSystem
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory
namespace MorphismProperty

variable {C : Type u} [Category.{v} C]
variable (W : MorphismProperty C)

/- Definition 4.27.20: a saturated multiplicative system is the reusable bundled property with
the left and right calculi of fractions (MS1--MS3) and the independent saturation axiom (MS4).
-/
@[stacks 05Q8 "saturated multiplicative systems"]
#check (IsSaturatedMultiplicativeSystem W : Prop)

end MorphismProperty
end CategoryTheory
