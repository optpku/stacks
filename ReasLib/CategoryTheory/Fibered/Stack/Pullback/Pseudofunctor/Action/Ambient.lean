module

public import ReasLib.CategoryTheory.Fibered.Stack.Pullback.Pseudofunctor.Construction

import Mathlib.Tactic.CrossRefAttribute

/-!
# Ambient action computations for fixed-base pullback on stacks

This leaf identifies the action of the ambient-valued pullback pseudofunctor before the stack
condition is restored by a full-subbicategory lift.
-/

@[expose] public section

noncomputable section

universe uC uD uS vC vD vS

namespace CategoryTheory

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]

namespace StackOver.Pullback

/-- The object action of the ambient-valued pullback is the neutral fibred-category pullback. -/
@[simp, stacks 04WC "ambient stack-pullback object computation"]
theorem ambient.obj (K : GrothendieckTopology D) (u : C ⥤ D)
    (T : StackOver.{uD, vD, uS, vS} K) :
    (ambient K u).obj T =
      FiberedCategoryOver.pullback u T.toFiberedCategoryOver := sorry

/-- The `1`-cell action of the ambient-valued pullback is the canonical neutral pullback map. -/
@[simp, stacks 04WC "ambient stack-pullback map computation"]
theorem ambient.map (K : GrothendieckTopology D) (u : C ⥤ D)
    {X Y : StackOver.{uD, vD, uS, vS} K} (F : X ⟶ Y) :
    (ambient K u).map F =
      FiberedCategoryOver.Pullback.mapCanonical u F.hom := sorry

/-- The `2`-cell action of the ambient-valued pullback is the canonical neutral pullback
transformation. -/
@[simp, stacks 04WC "ambient stack-pullback 2-cell computation"]
theorem ambient.map₂ (K : GrothendieckTopology D) (u : C ⥤ D)
    {X Y : StackOver.{uD, vD, uS, vS} K}
    {F G : X ⟶ Y} (eta : F ⟶ G) :
    (ambient K u).map₂ eta =
      FiberedCategoryOver.Pullback.map₂ u eta.hom := sorry

/-- The object action of the ambient-valued pullback hom functor is the canonical pullback map. -/
@[simp, stacks 04WC "ambient stack-pullback Hom object computation"]
theorem ambient.mapFunctor.obj (K : GrothendieckTopology D) (u : C ⥤ D)
    {X Y : StackOver.{uD, vD, uS, vS} K} (F : X ⟶ Y) :
    ((ambient K u).mapFunctor X Y).obj F =
      FiberedCategoryOver.Pullback.mapCanonical u F.hom := sorry

/-- The morphism action of the ambient-valued pullback hom functor is the canonical pullback of a
`2`-cell. -/
@[simp, stacks 04WC "ambient stack-pullback Hom morphism computation"]
theorem ambient.mapFunctor.map (K : GrothendieckTopology D) (u : C ⥤ D)
    {X Y : StackOver.{uD, vD, uS, vS} K}
    {F G : X ⟶ Y} (eta : F ⟶ G) :
    ((ambient K u).mapFunctor X Y).map eta =
      FiberedCategoryOver.Pullback.map₂ u eta.hom := sorry

end StackOver.Pullback

end CategoryTheory
