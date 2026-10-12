/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.Cartesian
public import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.Tactic.CrossRefAttribute

/-!
# The strongly cartesian morphism property

This module packages strong cartesianness over the image of a morphism as a
`MorphismProperty`.  It is the neutral owner used by wide subcategories, localizations, and any
construction that pulls the property back along a functor.
-/

@[expose] public section

universe uC uS vC vS

namespace CategoryTheory
namespace Functor.IsStronglyCartesian

variable {C : Type uC} {S : Type uS}
variable [Category.{vC} C] [Category.{vS} S]

/-- The morphism property on `S` consisting of arrows that are
strongly cartesian over their image under `p`. -/
@[stacks 02XK "strongly cartesian morphisms over their images"]
abbrev property (p : S ⥤ C) : MorphismProperty S :=
  fun {_ _} φ ↦ p.IsStronglyCartesian (p.map φ) φ

/-- Strongly cartesian morphisms over their images contain identities
and are closed under composition. -/
@[stacks 02XL "strongly cartesian morphisms form a multiplicative property"]
instance propertyIsMultiplicative (p : S ⥤ C) :
    (property p).IsMultiplicative := sorry

end Functor.IsStronglyCartesian
end CategoryTheory
