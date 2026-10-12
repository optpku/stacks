/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Filtration.FilteredInjective.Resolution.Total
public import ReasLib.Algebra.Homology.CochainComplex.Filtration.FilteredInjective.Resolution.Views

/-!
# Homotopy View of the Total Category of Filtered-Injective Resolutions

This file applies the canonical bounded-below homotopy quotient to the source, target, and
comparison on the total category of strict filtered-injective resolutions.  It introduces no
resolution choices or localization data.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CochainComplex.FilteredInjectivePlus.Resolution.Total.Homotopy

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The source functor on total strict filtered-injective resolutions, valued in the
bounded-below homotopy category. -/
@[stacks 05TW "homotopy source of total strict filtered-injective resolutions"]
noncomputable abbrev source (C : Type u) [Category.{v} C] [Abelian C] :
    Resolution.Total C ⥤ HomotopyCategory.Plus (FilteredObject.Finite.category C) :=
  Total.source C ⋙
    HomotopyCategory.Plus.quotient (FilteredObject.Finite.category C)

/-- The target functor on total strict filtered-injective resolutions, valued in the
bounded-below homotopy category. -/
@[stacks 05TW "homotopy target of total strict filtered-injective resolutions"]
noncomputable abbrev target (C : Type u) [Category.{v} C] [Abelian C] :
    Resolution.Total C ⥤ HomotopyCategory.Plus (FilteredObject.Finite.category C) :=
  Total.targetComplex C ⋙
    HomotopyCategory.Plus.quotient (FilteredObject.Finite.category C)

/-- The total resolution comparison after passing to the bounded-below homotopy category. -/
@[stacks 05TW "homotopy comparison of total strict filtered-injective resolutions"]
noncomputable abbrev comparison (C : Type u) [Category.{v} C] [Abelian C] :
    source C ⟶ target C :=
  Functor.whiskerRight (Total.comparison C)
    (HomotopyCategory.Plus.quotient (FilteredObject.Finite.category C))

/-- The homotopy source of a total resolution is the quotient image of its stored base
complex. -/
@[simp, stacks 05TW "homotopy source of a total strict filtered-injective resolution"]
theorem source_obj (X : Resolution.Total C) :
    (source C).obj X =
      (HomotopyCategory.Plus.quotient
        (FilteredObject.Finite.category C)).obj X.base := sorry

/-- The homotopy source functor sends a total resolution map to the quotient image of its
stored base map. -/
@[simp, stacks 05TU "homotopy source map of a total strict filtered-injective resolution"]
theorem source_map {X Y : Resolution.Total C} (f : X ⟶ Y) :
    (source C).map f =
      (HomotopyCategory.Plus.quotient
        (FilteredObject.Finite.category C)).map f.base := sorry

/-- The homotopy target of a total resolution is its stored resolution's pointwise homotopy
target. -/
@[simp, stacks 05TW "homotopy target of a total strict filtered-injective resolution"]
theorem target_obj (X : Resolution.Total C) :
    (target C).obj X = X.obj.targetHomotopy := sorry

/-- The homotopy target functor sends a total resolution map to its pointwise homotopy target
map. -/
@[simp, stacks 05TU "homotopy target map of a total strict filtered-injective resolution"]
theorem target_map {X Y : Resolution.Total C} (f : X ⟶ Y) :
    (target C).map f = f.displayed.homotopyMap := sorry

/-- A component of the total homotopy comparison is the pointwise homotopy comparison stored by
its resolution. -/
@[simp, stacks 05TW "component of the total strict-resolution homotopy comparison"]
theorem comparison_app (X : Resolution.Total C) :
    (comparison C).app X = X.obj.homotopyComparison := sorry

/-- Forward naturality of the homotopy comparison on total strict-resolution morphisms. -/
@[reassoc, stacks 05TU "forward naturality of total strict-resolution homotopy comparisons"]
theorem comparison_naturality {X Y : Resolution.Total C} (f : X ⟶ Y) :
    (source C).map f ≫ (comparison C).app Y =
      (comparison C).app X ≫ (target C).map f := sorry

end CochainComplex.FilteredInjectivePlus.Resolution.Total.Homotopy
