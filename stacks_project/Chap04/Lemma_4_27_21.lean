/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.MorphismProperty.Saturation
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory
namespace MorphismProperty

universe v u

variable {C : Type u} [Category.{v} C]
variable (S : MorphismProperty C)

/- Lemma 4.27.21 (1): saturation is the closure operator defined by the canonical localization. -/
@[stacks 05Q9 "saturation closure operator by the canonical localization"]
#check (saturation (C := C) : ClosureOperator (MorphismProperty C))

section

variable [S.HasLeftCalculusOfFractions] [S.HasRightCalculusOfFractions]
variable {X Y : C} (f : X ⟶ Y)

/- Lemma 4.27.21 (2): membership has the two-sided description under both calculi of fractions. -/
@[stacks 05Q9 "two-sided characterization of morphisms inverted by localization"]
#check (saturation.mem_iff_two_sided S f :
  (saturation (C := C) S) f ↔
    ∃ (Z₁ Z₂ : C) (g : Y ⟶ Z₁) (h : Z₂ ⟶ X),
      S (f ≫ g) ∧ S (h ≫ f))

end

section

variable [S.HasLeftCalculusOfFractions]

/- Lemma 4.27.21 (3): the left calculus of fractions passes to saturation. -/
@[stacks 05Q9 "left calculus for saturation"]
#check (MorphismProperty.saturation.left.hasCalculusOfFractions S :
  ((saturation (C := C)) S).HasLeftCalculusOfFractions)

end

section

variable [S.HasRightCalculusOfFractions]

/- Lemma 4.27.21 (4): the right calculus of fractions passes to saturation. -/
@[stacks 05Q9 "right calculus for saturation"]
#check (MorphismProperty.saturation.right.hasCalculusOfFractions S :
  ((saturation (C := C)) S).HasRightCalculusOfFractions)

end

/- Lemma 4.27.21 (5): saturation satisfies the saturation axiom. -/
@[stacks 05Q9 "saturation axiom for the localization closure"]
#check (saturation.hasSaturationAxiom S :
  ((saturation (C := C)) S).HasSaturationAxiom)

section

variable [S.HasLeftCalculusOfFractions] [S.HasRightCalculusOfFractions]

/- Lemma 4.27.21 (6): saturated multiplicative systems are exactly the fixed points. -/
@[stacks 05Q9 "saturated multiplicative systems are the fixed points of saturation"]
#check (saturation.isClosed_iff S :
  (saturation (C := C)).IsClosed S ↔ S.HasSaturationAxiom)

end

section

variable [S.HasLeftCalculusOfFractions] [S.HasRightCalculusOfFractions]
variable (T : MorphismProperty C)
variable [T.HasLeftCalculusOfFractions] [T.HasRightCalculusOfFractions]
variable [T.HasSaturationAxiom]

/- Lemma 4.27.21 (7): saturation is minimal among saturated multiplicative systems. -/
@[stacks 05Q9 "minimality of saturation"]
#check (saturation.le_iff S (T := T) : (saturation (C := C)) S ≤ T ↔ S ≤ T)

end

end MorphismProperty
end CategoryTheory
