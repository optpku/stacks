module

public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Derived Comparison for a Weak Serre Subcategory

The derived functor of the inclusion of a weak Serre full subcategory lands
in the ambient derived subcategory cut out by cohomology in that class.  This
file owns the resulting comparison functor independently of any boundedness
or equivalence criterion.
-/

open CategoryTheory.ObjectProperty

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory.CohomologyIn.Comparison

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
variable (P : ObjectProperty A) [IsWeakSerreClass P]
variable [HasDerivedCategory.{w} P.FullSubcategory]

/-- The derived functor of the weak Serre inclusion has cohomology in the
ambient object property. -/
theorem obj_mem (X : DerivedCategory P.FullSubcategory) :
    DerivedCategory.cohomologyIn P ((P.ι.mapDerivedCategory).obj X) := sorry

/-- The canonical comparison from the derived category of a weak Serre full
subcategory to the ambient cohomology-in subcategory. -/
@[stacks 06UR]
noncomputable abbrev functor :
    DerivedCategory P.FullSubcategory ⥤ DerivedCategory.CohomologyIn P :=
  (DerivedCategory.cohomologyIn P).lift P.ι.mapDerivedCategory (obj_mem P)

/-- Forgetting the comparison functor recovers the derived functor of the
weak Serre inclusion. -/
noncomputable def compιIso :
    functor P ⋙ (DerivedCategory.cohomologyIn P).ι ≅
      P.ι.mapDerivedCategory :=
  (DerivedCategory.cohomologyIn P).liftCompιIso
    P.ι.mapDerivedCategory (obj_mem P)

namespace functor

/-- The underlying object of the weak-Serre derived comparison is the
ordinary derived image under the inclusion. -/
@[simp, stacks 06UR "weak-Serre derived comparison object computation"]
theorem obj_obj (X : DerivedCategory P.FullSubcategory) :
    ((functor P).obj X).obj = P.ι.mapDerivedCategory.obj X := sorry

/-- The underlying morphism of the weak-Serre derived comparison is the
ordinary derived map under the inclusion. -/
@[simp, stacks 06UR "weak-Serre derived comparison map computation"]
theorem map_hom {X Y : DerivedCategory P.FullSubcategory} (f : X ⟶ Y) :
    ((functor P).map f).hom = P.ι.mapDerivedCategory.map f := sorry

end functor

end CategoryTheory.DerivedCategory.CohomologyIn.Comparison
