module

public import ReasLib.CategoryTheory.Groupoid.KernelPair

public section

open CategoryTheory
open scoped BasedFunctor

universe u v w

/- The relation functor of the kernel-pair groupoid consists of pairs of elements with
vertical isomorphisms between their images. -/
#check (CategoryTheory.GroupoidInFunctors.relation :
  {C : Type u} → [Category.{v} C] → {U : C ⥤ Type (max v w)} →
  {F : CofiberedCategoryOver.Groupoids.{u, v, max u (max v w), v} C} →
  (Functor.ofTypeValued U ⟶ F) → (C ⥤ Type (max v w)))
