module

public import ReasLib.CategoryTheory.Fibered.Setoids.Hom.OneCell

/-!
# Fiber restrictions of setoid-fibred morphisms

The fiberwise functor and its identity, composition, object, and morphism computations.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open BasedCategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Setoids

variable {X Y : FiberedCategoryOver.Setoids C}

/-- The induced functor on the fiber over `U`. -/
abbrev fiberFunctor (F : X ⟶ Y) (U : C) :=
  (toBasedFunctor F).fiberFunctor U

/-- Restriction of the identity setoid-fibred morphism to a standard fiber is the identity
functor. -/
@[simp]
theorem fiberFunctor.id (X : FiberedCategoryOver.Setoids C) (U : C) :
    fiberFunctor (𝟙 X) U = 𝟭 (X.p.Fiber U) := sorry

/-- Restriction of a composite setoid-fibred morphism is the composite of its restrictions. -/
@[simp]
theorem fiberFunctor.comp
    {Z : FiberedCategoryOver.Setoids C} (F : X ⟶ Y) (G : Y ⟶ Z) (U : C) :
    fiberFunctor (F ≫ G) U = fiberFunctor F U ⋙ fiberFunctor G U := sorry

/-- The total object underlying a fiberwise image is the image under the total functor. -/
@[simp]
theorem fiberFunctor.obj.val (F : X ⟶ Y) (U : C) (x : X.p.Fiber U) :
    ((fiberFunctor F U).obj x).1 = (toFunctor F).obj x.1 := sorry

/-- The total morphism underlying a fiberwise image is the image under the total functor. -/
@[simp]
theorem fiberFunctor.map.val (F : X ⟶ Y) (U : C)
    {x y : X.p.Fiber U} (phi : x ⟶ y) :
    ((fiberFunctor F U).map phi).1 = (toFunctor F).map phi.1 := sorry

end FiberedCategoryOver.Setoids

end CategoryTheory
