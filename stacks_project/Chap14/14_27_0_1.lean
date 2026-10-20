/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Homotopy.AlternatingFace
import StacksCheckRecall

/-!
@stack 019R
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.SimplicialObject

universe u v

namespace CategoryTheory.SimplicialObject.Homotopy

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {X Y : SimplicialObject C} {f g : X ⟶ Y}
variable (H : Homotopy f g) (n : ℕ)

/- Equation 14.27.0.1 is the source-sign form of the canonical chain-homotopy component. -/
@[stacks 019R "Equation 14.27.0.1"]
#check (Homotopy.toChainHomotopy.hom_eq_alternating_sum H n :
  H.toChainHomotopy.hom n (n + 1) =
    ∑ i : Fin (n + 1), ((-1 : ℤ) ^ ((i : ℕ) + 1)) • H.h i)

end CategoryTheory.SimplicialObject.Homotopy
