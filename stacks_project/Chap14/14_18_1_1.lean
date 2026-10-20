/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Splitting.Construction
import StacksCheckRecall

/-!
@stack 017Q
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped SimplexCategory.Truncated

universe v u

namespace CategoryTheory.SimplicialObject.Truncated

variable {C : Type u} [Category.{v} C]
variable {n : ℕ} {X : SimplicialObject.Truncated C n}
variable (s : Splitting X) (m : Fin (n + 1))

/- Equation 14.18.1.1: the summands of a splitting form the canonical colimit cofan in every
truncated degree. -/
@[stacks 017Q "Equation 14.18.1.1"]
#check (s.isColimit (op ⦋m⦌ₙ) : IsColimit (s.cofan (op ⦋m⦌ₙ)))

#check (s.cofan (op ⦋m⦌ₙ))
#check s.cofan_inj_eq
#check @Splitting.desc

end CategoryTheory.SimplicialObject.Truncated
