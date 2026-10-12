/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]
variable {X Y Z : C}
variable (f : MorphismProperty.LeftFraction.Localization.Hom W X Y)
variable (g : MorphismProperty.LeftFraction.Localization.Hom W Y Z)

/- The source needs the concrete quotient construction, not merely equality after mapping into a
localization. Mathlib's `MorphismProperty.equivalenceLeftFractionRel`,
`MorphismProperty.LeftFraction.Localization.Hom.comp`, and
`MorphismProperty.LeftFraction.Localization.instCategory` respectively own the relation proof,
quotient-level composition, and category laws. Recalling these owners removes the redundant
`homMk` congruence bridge, introduces no generalization, and exposes the quotient construction and
reusable category instance directly to downstream files. The right-fraction theorem is the strict
dual: `W.HasRightCalculusOfFractions` makes `W.op` admit the construction below, while
`MorphismProperty.equivalenceRightFractionRel` identifies its relation directly. It belongs to
Lemma 4.27.11 rather than this left-handed source item, so no second wrapper is introduced here. -/

/- Lemma 4.27.2 (1): for a left multiplicative system, the canonical relation on left fractions
is an equivalence relation. -/
@[stacks 04VD "equivalence relation on left fractions"]
#check (MorphismProperty.equivalenceLeftFractionRel W X Y :
  @_root_.Equivalence (W.LeftFraction X Y) MorphismProperty.LeftFractionRel)

/- Lemma 4.27.2 (2): the canonical composition rule descends to the quotient of left fractions by
`MorphismProperty.LeftFractionRel`. -/
@[stacks 04VD "composition on equivalence classes of left fractions"]
#check (MorphismProperty.LeftFraction.Localization.Hom.comp f g :
  MorphismProperty.LeftFraction.Localization.Hom W X Z)

/- Lemma 4.27.2 (3): the quotient localization carries the canonical category structure, whose
laws give associativity and the left and right identity axioms. -/
@[stacks 04VD "category structure on the left-fraction localization"]
#check (MorphismProperty.LeftFraction.Localization.instCategory (W := W) :
  Category (MorphismProperty.LeftFraction.Localization W))

end CategoryTheory
