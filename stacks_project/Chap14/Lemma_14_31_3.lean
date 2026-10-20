/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
import StacksCheckRecall

/-!
@stack 08NW
-/

@[expose] public section

open CategoryTheory HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

namespace SSet.modelCategoryQuillen

variable {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable [Fibration f] [Fibration g]

/- Lemma 14.31.3 (08NW): the composite of Kan fibrations is a Kan fibration. -/
@[stacks 08NW]
#check (inferInstance : Fibration (f ≫ g))

end SSet.modelCategoryQuillen
