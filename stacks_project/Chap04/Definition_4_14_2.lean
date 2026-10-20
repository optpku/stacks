/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.IsLimit
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory.Limits

universe vJ uJ vC uC

variable {J : Type uJ} [Category.{vJ} J]
variable {C : Type uC} [Category.{vC} C]
variable {F : J ⥤ C} (c : Cocone F)

/- The source defines when specified cocone data are colimiting. `Cocone` already bundles the
object, legs, and compatibility, while the tagged owner `IsColimit` supplies exactly the unique
factorization property. `ColimitCocone` only repackages these two owners and `HasColimit` merely
asserts existence, so recalling `IsColimit` avoids downstream choice packaging without
generalizing the source and exposes the standard `desc`, `fac`, and `uniq` API for reuse. -/

/- Definition 4.14.2: a colimit of a diagram `M : J ⥤ C` is an object of `C` with a
compatible cocone of morphisms `M.obj i ⟶ c.pt` such that every compatible family
`M.obj i ⟶ W` factors uniquely through `c.pt`. This is exactly the canonical structure
`IsColimit c` for `c : Cocone M`. -/
@[stacks 002F "colimit cocone with unique factorization of compatible families"]
#check (IsColimit c : Type (max (max uJ uC) vC))

end CategoryTheory.Limits
