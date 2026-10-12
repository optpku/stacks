/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.MorphismProperty.Localization.RightFractionColimit.Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u vD uD

namespace CategoryTheory.MorphismProperty.RightFraction.Localization

variable {C : Type u} [Category.{v} C]
variable {D : Type uD} [Category.{vD} D]
variable (L : C ⥤ D) (W : MorphismProperty C)
variable [L.IsLocalization W] [W.HasRightCalculusOfFractions]
variable (X Y : C)

/- 4.27.15.1: let `W` be a right multiplicative system and let `L` be any
localization model for `W`. The source-arrow category `W / X`, whose objects
are denominators `s.hom : s.left ⟶ X` in `W`, is cofiltered. Hence its
opposite indexes the filtered diagram
`RightFraction.Localization.homDiagram W X Y`, with value
`ULift (s.unop.left ⟶ Y)` at `s`. The localized Hom-type is canonically equivalent
to its colimit:

`(colimit (RightFraction.Localization.homDiagram W X Y) : Type (max u v)) ≃`
`  (L.obj X ⟶ L.obj Y)`.

This formulation is independent of the chosen localization model; taking
`L := W.Q` recovers the presentation in the source. -/
@[stacks 05Q5 "localized Hom-set as a colimit over source denominators"]
#check (homColimit.equivTo L W X Y :
  (colimit (homDiagram W X Y) : Type (max u v)) ≃ (L.obj X ⟶ L.obj Y))

end CategoryTheory.MorphismProperty.RightFraction.Localization
