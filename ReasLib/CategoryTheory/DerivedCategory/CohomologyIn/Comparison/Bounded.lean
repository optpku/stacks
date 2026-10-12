/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Comparison
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded

@[expose] public section

open CategoryTheory.ObjectProperty
open DerivedCategory.TStructure

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory.Bounded.CohomologyIn.Comparison

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
variable (P : ObjectProperty A) [IsWeakSerreClass P]
variable [HasDerivedCategory.{w} P.FullSubcategory]

namespace Ambient

/-- The derived functor of a weak Serre inclusion preserves bounded objects. -/
theorem obj_mem (X : DerivedCategory.Bounded P.FullSubcategory) :
    (t.bounded : ObjectProperty (DerivedCategory A))
      ((DerivedCategory.Bounded.ι ⋙ P.ι.mapDerivedCategory).obj X) := sorry

/-- The restriction of the derived weak Serre inclusion to bounded derived categories. -/
noncomputable abbrev functor :
    DerivedCategory.Bounded P.FullSubcategory ⥤ DerivedCategory.Bounded A :=
  (t.bounded : ObjectProperty (DerivedCategory A)).lift
    (DerivedCategory.Bounded.ι ⋙ P.ι.mapDerivedCategory) (obj_mem P)

/-- Forgetting boundedness recovers the derived inclusion on bounded objects. -/
noncomputable def compιIso :
    functor P ⋙ DerivedCategory.Bounded.ι ≅
      DerivedCategory.Bounded.ι ⋙ P.ι.mapDerivedCategory :=
  (t.bounded : ObjectProperty (DerivedCategory A)).liftCompιIso
    (DerivedCategory.Bounded.ι ⋙ P.ι.mapDerivedCategory) (obj_mem P)

namespace functor

/-- The underlying object of the bounded ambient restriction is the derived image under the
weak Serre inclusion. -/
@[simp]
theorem obj_obj (X : DerivedCategory.Bounded P.FullSubcategory) :
    ((functor P).obj X).obj = P.ι.mapDerivedCategory.obj X.obj := sorry

/-- The underlying morphism of the bounded ambient restriction is the derived map under the
weak Serre inclusion. -/
@[simp]
theorem map_hom {X Y : DerivedCategory.Bounded P.FullSubcategory} (f : X ⟶ Y) :
    ((functor P).map f).hom = P.ι.mapDerivedCategory.map f.hom := sorry

end functor

end Ambient

/-- The bounded derived functor of a weak Serre inclusion has cohomology in the ambient object
property. -/
theorem obj_mem (X : DerivedCategory.Bounded P.FullSubcategory) :
    DerivedCategory.Bounded.cohomologyIn P ((Ambient.functor P).obj X) := sorry

/-- The canonical bounded comparison from the derived category of a weak Serre full subcategory
to the bounded ambient category with cohomology in that property. -/
noncomputable abbrev functor :
    DerivedCategory.Bounded P.FullSubcategory ⥤
      DerivedCategory.Bounded.CohomologyIn P :=
  (DerivedCategory.Bounded.cohomologyIn P).lift
    (Ambient.functor P) (obj_mem P)

/-- Forgetting the cohomology condition recovers the bounded derived functor of the inclusion. -/
noncomputable def compιIso :
    functor P ⋙ (DerivedCategory.Bounded.cohomologyIn P).ι ≅
      Ambient.functor P :=
  (DerivedCategory.Bounded.cohomologyIn P).liftCompιIso
    (Ambient.functor P) (obj_mem P)

namespace functor

/-- Forgetting the cohomology condition on a bounded comparison object recovers the ambient
bounded restriction. -/
@[simp]
theorem obj_obj (X : DerivedCategory.Bounded P.FullSubcategory) :
    ((functor P).obj X).obj = (Ambient.functor P).obj X := sorry

/-- Forgetting the cohomology condition on a bounded comparison map recovers the ambient bounded
restriction. -/
@[simp]
theorem map_hom {X Y : DerivedCategory.Bounded P.FullSubcategory} (f : X ⟶ Y) :
    ((functor P).map f).hom = (Ambient.functor P).map f := sorry

end functor

end CategoryTheory.DerivedCategory.Bounded.CohomologyIn.Comparison
