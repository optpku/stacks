module

public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Comparison
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Computation

@[expose] public section

/-!
# Bounded-Below Derived Comparison

This file restricts the weak-Serre derived comparison to bounded-below objects.
-/

open CategoryTheory.ObjectProperty
open DerivedCategory.TStructure

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory.Plus.CohomologyIn.Comparison

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
variable (P : ObjectProperty A) [IsWeakSerreClass P]
variable [HasDerivedCategory.{w} P.FullSubcategory]

namespace Ambient

/-- The restriction of the derived weak Serre inclusion to bounded-below derived categories. -/
noncomputable abbrev functor :
    DerivedCategory.Plus P.FullSubcategory ⥤ DerivedCategory.Plus A :=
  ExactFunctor.Derived.Plus.functor (ExactFunctor.of P.ι)

/-- Forgetting boundedness recovers the derived inclusion on bounded-below objects. -/
noncomputable def compιIso :
    functor P ⋙ DerivedCategory.Plus.ι ≅
      DerivedCategory.Plus.ι ⋙ P.ι.mapDerivedCategory :=
  ExactFunctor.Derived.Plus.compιIso (ExactFunctor.of P.ι)

end Ambient

/-- The bounded-below derived functor of a weak Serre inclusion has cohomology in the ambient
object property. -/
theorem obj_mem (X : DerivedCategory.Plus P.FullSubcategory) :
    DerivedCategory.Plus.cohomologyIn P ((Ambient.functor P).obj X) := sorry

/-- The canonical bounded-below comparison from the derived category of a weak Serre full
subcategory to the ambient bounded-below category with cohomology in that property. -/
@[stacks 06VV]
noncomputable abbrev functor :
    DerivedCategory.Plus P.FullSubcategory ⥤
      DerivedCategory.Plus.CohomologyIn P :=
  (DerivedCategory.Plus.cohomologyIn P).lift
    (Ambient.functor P) (obj_mem P)

/-- Forgetting the cohomology condition recovers the bounded-below derived functor of the
inclusion. -/
noncomputable def compιIso :
    functor P ⋙ (DerivedCategory.Plus.cohomologyIn P).ι ≅
      Ambient.functor P :=
  (DerivedCategory.Plus.cohomologyIn P).liftCompιIso
    (Ambient.functor P) (obj_mem P)

namespace functor

/-- Forgetting the cohomology condition on a bounded-below comparison object recovers the
ambient bounded-below restriction. -/
@[simp]
theorem obj_obj (X : DerivedCategory.Plus P.FullSubcategory) :
    ((functor P).obj X).obj = (Ambient.functor P).obj X := sorry

/-- Forgetting the cohomology condition on a bounded-below comparison map recovers the ambient
bounded-below restriction. -/
@[simp]
theorem map_hom {X Y : DerivedCategory.Plus P.FullSubcategory} (f : X ⟶ Y) :
    ((functor P).map f).hom = (Ambient.functor P).map f := sorry

end functor

end CategoryTheory.DerivedCategory.Plus.CohomologyIn.Comparison
