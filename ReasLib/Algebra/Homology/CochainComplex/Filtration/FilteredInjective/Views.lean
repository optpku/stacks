/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Filtration.FilteredInjective.Plus
public import ReasLib.Algebra.Homology.CochainComplex.InjectiveResolution
public import ReasLib.CategoryTheory.Filtration.Complex.Finite.Bounded
public import ReasLib.CategoryTheory.Filtration.Complex.Finite.Stage
public import ReasLib.CategoryTheory.Filtration.FiniteInjective.Injective
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction

/-!
# Injective Views of Bounded-Below Filtered-Injective Complexes

The graded pieces, filtration stages, and underlying complexes of a bounded-below complex of
finite filtered-injective objects are bounded-below complexes of injective objects.  This module
packages those three operations as functors landing directly in `CochainComplex.InjectivePlus`,
so downstream derived-functor constructions do not need local injectivity instances.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

noncomputable section

universe v u

namespace CochainComplex.FilteredInjectivePlus

variable (C : Type u) [Category.{v} C] [Abelian C]

namespace GradedPiece

/-- Every term of the `p`-th graded piece of a bounded-below filtered-injective complex is
injective. -/
@[stacks 05TW "injective graded-piece view of a filtered-injective complex"]
theorem termInjective (p : ℤ) (I : CochainComplex.FilteredInjectivePlus C) (n : ℤ) :
    Injective (((FilteredObject.Finite.Plus.GradedPiece.cochain C p).obj I.obj).obj.X n) := sorry

/-- Take the `p`-th graded piece of a bounded-below filtered-injective complex, retaining its
canonical termwise-injective presentation. -/
@[stacks 05TW "injective graded-piece view of a filtered-injective complex"]
noncomputable def functor (p : ℤ) :
    CochainComplex.FilteredInjectivePlus C ⥤ CochainComplex.InjectivePlus C :=
  ObjectProperty.FullSubcategory.restrict
    (FilteredObject.Finite.Plus.GradedPiece.cochain C p)
    (fun K hK n => termInjective C p ⟨K, hK⟩ n)

namespace functor

/-- The underlying bounded-below complex of the graded-piece view is computed by the neutral
finite graded-piece functor. -/
@[simp, stacks 05TW "graded-piece view computation"]
theorem obj_obj (p : ℤ) (I : CochainComplex.FilteredInjectivePlus C) :
    ((functor C p).obj I).obj =
      (FilteredObject.Finite.Plus.GradedPiece.cochain C p).obj I.obj := sorry

/-- The underlying map of the graded-piece view is computed by the neutral finite graded-piece
functor. -/
@[simp, stacks 05TU "graded-piece view map computation"]
theorem map_hom (p : ℤ) {I J : CochainComplex.FilteredInjectivePlus C} (f : I ⟶ J) :
    ((functor C p).map f).hom =
      (FilteredObject.Finite.Plus.GradedPiece.cochain C p).map f.hom := sorry

end functor
end GradedPiece

namespace Stage

/-- Every term of the `p`-th stage of a bounded-below filtered-injective complex is injective. -/
@[stacks 05TW "injective stage view of a filtered-injective complex"]
theorem termInjective (p : ℤ) (I : CochainComplex.FilteredInjectivePlus C) (n : ℤ) :
    Injective (((FilteredObject.Finite.Stage.cochain C p).obj I.obj).obj.X n) := sorry

/-- Take the `p`-th filtration stage of a bounded-below filtered-injective complex, retaining its
canonical termwise-injective presentation. -/
@[stacks 05TW "injective stage view of a filtered-injective complex"]
noncomputable def functor (p : ℤ) :
    CochainComplex.FilteredInjectivePlus C ⥤ CochainComplex.InjectivePlus C :=
  ObjectProperty.FullSubcategory.restrict
    (FilteredObject.Finite.Stage.cochain C p)
    (fun K hK n => termInjective C p ⟨K, hK⟩ n)

namespace functor

/-- The underlying bounded-below complex of the stage view is computed by the neutral finite
stage functor. -/
@[simp, stacks 05TW "stage view computation"]
theorem obj_obj (p : ℤ) (I : CochainComplex.FilteredInjectivePlus C) :
    ((functor C p).obj I).obj =
      (FilteredObject.Finite.Stage.cochain C p).obj I.obj := sorry

/-- The underlying map of the stage view is computed by the neutral finite stage functor. -/
@[simp, stacks 05TU "stage view map computation"]
theorem map_hom (p : ℤ) {I J : CochainComplex.FilteredInjectivePlus C} (f : I ⟶ J) :
    ((functor C p).map f).hom =
      (FilteredObject.Finite.Stage.cochain C p).map f.hom := sorry

end functor
end Stage

namespace Underlying

/-- Every term of the underlying complex of a bounded-below filtered-injective complex is
injective. -/
@[stacks 05TW "injective underlying view of a filtered-injective complex"]
theorem termInjective (I : CochainComplex.FilteredInjectivePlus C) (n : ℤ) :
    Injective (((FilteredObject.Finite.Plus.Forget.cochain C).obj I.obj).obj.X n) := sorry

/-- Forget the finite filtration on a bounded-below filtered-injective complex, retaining its
canonical termwise-injective presentation. -/
@[stacks 05TW "injective underlying view of a filtered-injective complex"]
noncomputable def functor :
    CochainComplex.FilteredInjectivePlus C ⥤ CochainComplex.InjectivePlus C :=
  ObjectProperty.FullSubcategory.restrict
    (FilteredObject.Finite.Plus.Forget.cochain C)
    (fun K hK n => termInjective C ⟨K, hK⟩ n)

namespace functor

/-- The underlying bounded-below complex of the underlying view is computed by the neutral
finite forgetful functor. -/
@[simp, stacks 05TW "underlying view computation"]
theorem obj_obj (I : CochainComplex.FilteredInjectivePlus C) :
    ((functor C).obj I).obj =
      (FilteredObject.Finite.Plus.Forget.cochain C).obj I.obj := sorry

/-- The underlying map of the underlying view is computed by the neutral finite forgetful
functor. -/
@[simp, stacks 05TU "underlying view map computation"]
theorem map_hom {I J : CochainComplex.FilteredInjectivePlus C} (f : I ⟶ J) :
    ((functor C).map f).hom =
      (FilteredObject.Finite.Plus.Forget.cochain C).map f.hom := sorry

end functor
end Underlying

end CochainComplex.FilteredInjectivePlus
