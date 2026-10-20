/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import StacksCheckRecall

@[expose] public section
universe v u

namespace CategoryTheory
namespace MorphismProperty

variable {C : Type u} [Category.{v} C]
variable (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]
variable {X Y Y' : C} (f : X ⟶ Y') (s : Y ⟶ Y') (hs : W s)

/- A left fraction is a one-step generalized morphism, matching the standard calculus-of-fractions
model used by the source and nLab. Mathlib separates its concrete roof
`LeftFraction.mk f s hs` from its equivalence class in the localization, constructed by
`LeftFraction.Localization.homMk`. Its equality, composition, and comparison with
`(Q W).map f ≫ Qinv s hs` are then provided by `homMk_eq_iff_leftFractionRel`,
`homMk_comp_homMk`, and `Q_map_comp_Qinv`.

The paper notation `s⁻¹f` suppresses the proof that `s` lies in `W`. A faithful Lean notation
would have to expose `hs`, while `⁻¹` is already heavily overloaded and the handedness convention
for fractions is not uniform. Such notation would therefore add ambiguity without shortening the
canonical term, so this item deliberately recalls the constructor rather than adding syntax or a
wrapper. -/

/- Definition 4.27.4: for a left multiplicative system `W`, the equivalence class of a pair
`f : X ⟶ Y'` and `s : Y ⟶ Y'` with `W s` is the canonical morphism
`LeftFraction.Localization.homMk (LeftFraction.mk f s hs)` from `X` to `Y` in the constructed
localization `LeftFraction.Localization W`. -/
@[stacks 0BM2 "left fraction represented by a roof"]
#check (LeftFraction.Localization.homMk (LeftFraction.mk f s hs) :
  (LeftFraction.Localization.Q W).obj X ⟶ (LeftFraction.Localization.Q W).obj Y)

end MorphismProperty
end CategoryTheory
