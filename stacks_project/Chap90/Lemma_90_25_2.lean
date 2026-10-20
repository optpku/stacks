module

public import ReasLib.CategoryTheory.Groupoid.KernelPair
import StacksCheckRecall

public section

open CategoryTheory
open scoped BasedFunctor

universe u v w

/- Lemma 90.25.2: the kernel pair of a morphism from a set-valued functor to a category
cofibered in groupoids has the first and second endpoint projections and the canonical
first-and-last composition, and forms a groupoid in functors. -/
@[stacks 06KY] #check (CategoryTheory.GroupoidInFunctors.ofMorphism :
  {C : Type u} → [Category.{v} C] → {U : C ⥤ Type (max v w)} →
  {F : CofiberedCategoryOver.Groupoids.{u, v, max u (max v w), v} C} →
  (Functor.ofTypeValued U ⟶ F) → GroupoidInFunctors.{u, v, max v w} C)
