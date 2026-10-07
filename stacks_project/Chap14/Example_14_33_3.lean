module

public import ReasLib.AlgebraicTopology.SimplicialObject.Augmented.Composition.Whiskering
import StacksCheckRecall

@[expose] public section

/-!
@stack 0G5P

# Example 14.33.3 compatibility facade

The augmented pre/postcomposition construction is a reusable operation on augmented simplicial
objects and is owned by `ReasLib`.  This file retains only the source-facing recall.
-/

open CategoryTheory
open CategoryTheory.SimplicialObject

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]
variable {X : SimplicialObject (C ⥤ C)}
variable (F : A ⥤ C) (G : C ⥤ B)
variable (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C))
variable (Δ : SimplexCategoryᵒᵖ)

/- Example 14.33.3: pre- and postcomposition of an augmented simplicial endofunctor. -/
@[stacks 0G5P "Example 14.33.3"]
#check (SimplicialObject.Augmented.whisker F G ε :
  SimplicialObject.Augmented (A ⥤ B))

/- The degreewise object of the construction is composition on both sides. -/
#check (SimplicialObject.Augmented.whisker.left_obj F G ε Δ :
  (SimplicialObject.Augmented.whisker F G ε).left.obj Δ = F ⋙ (X.obj Δ ⋙ G))

/- Its augmented point is canonically isomorphic to `F ⋙ G`. -/
#check (SimplicialObject.Augmented.whisker.pointIso F G ε :
  (SimplicialObject.Augmented.whisker F G ε).right ≅ F ⋙ G)

/- Its augmentation is obtained by whiskering the original augmentation. -/
#check (SimplicialObject.Augmented.whisker.hom_app F G ε Δ :
  (SimplicialObject.Augmented.whisker F G ε).hom.app Δ =
    Functor.whiskerLeft F (Functor.whiskerRight (ε.app Δ) G))

end CategoryTheory
