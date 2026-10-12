/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.MorphismProperty.Localization.LeftFractionColimit.Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.MorphismProperty.LeftFraction.Localization

variable {C : Type u} [Category.{v} C]
variable (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]
variable (X Y : C)

/- 4.27.7.1: for a left multiplicative system `W`, the localized Hom-set
`((Q W).obj X ⟶ (Q W).obj Y)` is canonically isomorphic to the filtered
colimit over `Y / W` of the types `X ⟶ Y'`, where an index is a denominator
`s : Y ⟶ Y'` in `W`.  Lean expresses the source equation as an `Iso` in
`Type`; the `ULift` in `homDiagram` only reconciles universes.
-/
@[stacks 05Q1 "localized Hom-set as a filtered colimit over target denominators"]
#check (homColimit.iso W X Y :
  colimit (homDiagram W X Y) ≅ ((Q W).obj X ⟶ (Q W).obj Y))

end CategoryTheory.MorphismProperty.LeftFraction.Localization
