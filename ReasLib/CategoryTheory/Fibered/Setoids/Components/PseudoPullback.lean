module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.Setoids.Components.Map

/-!
# Fibrewise components and bicategorical pseudo-pullbacks

For categories fibred in setoids, the presheaf of fibrewise isomorphism classes sends a
bicategorical pseudo-pullback cone to an ordinary pullback square of presheaves.  The statement
uses `IsPullback`, so it does not choose a particular pullback object.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Limits
open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {X Y Z : FiberedCategoryOver.Setoids C}
variable {F : X ⟶ Y} {G : Z ⟶ Y}

namespace FiberedCategoryOver.Setoids

namespace componentsPresheaf

/-- Applying the fibrewise-component presheaf to a bicategorical pseudo-pullback cone in
categories fibred in setoids gives a pullback square of presheaves. -/
@[stacks 04SD]
theorem isPullback_of_isBilimit
    (P : Bicategory.PseudoPullbackCone F G) (hP : P.IsBilimit) :
    IsPullback
      (componentsMap P.fst) (componentsMap P.snd)
      (componentsMap F) (componentsMap G) := sorry
/- Proof strategy: evaluate at each base object.  An object in the explicit fibre is a compatible
pair together with an isomorphism of images; thinness of the target fibre makes its isomorphism
class unique and independent of representatives.  Naturality is inherited by `componentsMap`
from `BasedFunctor.fiberIsoClassMap`, and `componentsMap.eq_of_hom` makes the result
invariant under the cone's `2`-cells.  Transport the
pointwise pullback property along `hP`. -/

end componentsPresheaf

end FiberedCategoryOver.Setoids

end CategoryTheory
