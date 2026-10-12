/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Construction
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Definition
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Basic

/-!
# Closure under explicit based pseudo-pullbacks

This module owns the closure hypotheses for the chosen
`BasedCategory.PseudoPullback` construction.  They are deliberately named below that explicit
model: closure under an arbitrary bicategorical bilimit has a different invariant formulation.

The object-property class is for arbitrary based cospan legs.  The hom-property class is the
relative variant for selected legs in a locally induced bicategory.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace BasedCategory.PseudoPullback.ObjectProperty

/-- An object property of based categories is closed under the explicit chosen
`BasedCategory.PseudoPullback` construction.

The condition is intentionally about this iso-comma model rather than an arbitrary equivalent
bilimit.  This retains strict properties, such as discreteness of fibres, and gives downstream
constructions a computationally fixed apex.  The ambient universe layer is normalized so the
chosen pseudo-pullback is again an object in the same property-selected bicategory. -/
class IsClosedUnder
    (P : CategoryTheory.ObjectProperty
      (BasedCategory.{max v vB, max w (max u (max v vB))} C)) : Prop where
  /-- The explicit pseudo-pullback of a cospan of objects satisfying `P` again satisfies `P`. -/
  pseudoPullback_mem
    {X Y S : BasedCategory.{max v vB, max w (max u (max v vB))} C}
    (hX : P X) (hY : P Y) (hS : P S) (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) :
    P (BasedCategory.PseudoPullback F G)

end BasedCategory.PseudoPullback.ObjectProperty

namespace BasedCategory.PseudoPullback.HomProperty

variable {P : CategoryTheory.ObjectProperty
  (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
variable (Q : Bicategory.HomProperty (fun X : P.FullSubbicategory ↦ X.1))

/-- A selected hom property is closed under the explicit chosen based pseudo-pullback relative
to its selected objects.

Unlike `BasedCategory.PseudoPullback.ObjectProperty.IsClosedUnder`, this only requires closure
for cospan legs selected by `Q`.  The leg hypotheses are mathematically essential for cartesian
morphisms between fibred categories. -/
class IsClosedUnder : Prop where
  /-- The explicit pseudo-pullback of two selected cospan legs is a selected object. -/
  pseudoPullback_mem
    {X Y S : P.FullSubbicategory}
    (F : X.1 ⥤ᵇ S.1) (G : Y.1 ⥤ᵇ S.1)
    (hF : Q X S F) (hG : Q Y S G) :
    P (BasedCategory.PseudoPullback F G)

/-- Arbitrary-leg object-property closure supplies relative closure for every selected hom
property.  More restrictive hom properties may instead provide a stronger direct instance. -/
instance IsClosedUnder.ofProperty
    [BasedCategory.PseudoPullback.ObjectProperty.IsClosedUnder P] :
    IsClosedUnder Q := sorry
/- Proof strategy: apply
`BasedCategory.PseudoPullback.ObjectProperty.IsClosedUnder.pseudoPullback_mem` to the three
selected-object witnesses; arbitrary-leg closure does not need the selected-leg witnesses. -/

end BasedCategory.PseudoPullback.HomProperty

end CategoryTheory
