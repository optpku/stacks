/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Filtration.FilteredInjective.Resolution.Total
public import ReasLib.Algebra.Homology.CochainComplex.Filtration.FilteredInjective.Resolution.Views

/-!
# Underlying Views of the Total Strict-Resolution Category

This leaf forgets finite filtrations from both sides of the functorial comparison carried by the
total category of strict filtered-injective resolutions.  The cochain-level comparison is obtained
by whiskering the bounded filtered comparison, and its homotopy-level counterpart is obtained by
further composition with the bounded homotopy quotient.  No functor laws or representatives are
reconstructed locally.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CochainComplex.FilteredInjectivePlus.Resolution.Total.Underlying

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Forget the finite filtration on the bounded source complex of a total strict resolution. -/
@[stacks 05TW "underlying source of a total strict filtered-injective resolution"]
noncomputable abbrev source (C : Type u) [Category.{v} C] [Abelian C] :
    Resolution.Total C ⥤ CochainComplex.Plus C :=
  Total.source C ⋙ FilteredObject.Finite.Plus.Forget.cochain C

/-- Forget the finite filtration on the bounded target complex of a total strict resolution. -/
@[stacks 05TW "underlying target of a total strict filtered-injective resolution"]
noncomputable abbrev target (C : Type u) [Category.{v} C] [Abelian C] :
    Resolution.Total C ⥤ CochainComplex.Plus C :=
  Total.targetComplex C ⋙ FilteredObject.Finite.Plus.Forget.cochain C

/-- The underlying bounded-complex comparison, natural on the total strict-resolution
category. -/
@[stacks 05TW "underlying comparison of total strict filtered-injective resolutions"]
noncomputable abbrev comparison (C : Type u) [Category.{v} C] [Abelian C] :
    source C ⟶ target C :=
  Functor.whiskerRight (Total.comparison C)
    (FilteredObject.Finite.Plus.Forget.cochain C)

/-- The underlying source of a total resolution is obtained by forgetting the filtration on its
base complex. -/
@[simp, stacks 05TW "underlying source of a total strict filtered-injective resolution"]
theorem source_obj (X : Resolution.Total C) :
    (source C).obj X =
      (FilteredObject.Finite.Plus.Forget.cochain C).obj X.base := sorry

/-- The underlying source functor maps a total morphism by forgetting the filtration on its base
morphism. -/
@[simp, stacks 05TU "underlying source map of a total strict filtered-injective resolution"]
theorem source_map {X Y : Resolution.Total C} (f : X ⟶ Y) :
    (source C).map f =
      (FilteredObject.Finite.Plus.Forget.cochain C).map f.base := sorry

/-- The underlying target of a total resolution is the stored underlying bounded target. -/
@[simp, stacks 05TW "underlying target of a total strict filtered-injective resolution"]
theorem target_obj (X : Resolution.Total C) :
    (target C).obj X = X.obj.underlying := sorry

/-- The underlying target functor maps a total morphism by its stored underlying target map. -/
@[simp, stacks 05TU "underlying target map of a total strict filtered-injective resolution"]
theorem target_map {X Y : Resolution.Total C} (f : X ⟶ Y) :
    (target C).map f = f.displayed.underlyingMap := sorry

/-- A component of the total underlying comparison is the underlying comparison stored by its
resolution. -/
@[simp, stacks 05TW "component of the total underlying strict-resolution comparison"]
theorem comparison_app (X : Resolution.Total C) :
    (comparison C).app X = X.obj.underlyingComparison := sorry

/-- Forward naturality of the underlying comparison on total strict-resolution morphisms. -/
@[reassoc, stacks 05TU "naturality of the total underlying strict-resolution comparison"]
theorem comparison_naturality {X Y : Resolution.Total C} (f : X ⟶ Y) :
    (source C).map f ≫ (comparison C).app Y =
      (comparison C).app X ≫ (target C).map f := sorry

namespace Homotopy

/-- Pass the underlying bounded source complex of a total strict resolution to the bounded-below
homotopy category. -/
@[stacks 05TW "underlying homotopy source of a total strict filtered-injective resolution"]
noncomputable abbrev source (C : Type u) [Category.{v} C] [Abelian C] :
    Resolution.Total C ⥤ HomotopyCategory.Plus C :=
  Underlying.source C ⋙ HomotopyCategory.Plus.quotient C

/-- Pass the underlying bounded target complex of a total strict resolution to the bounded-below
homotopy category. -/
@[stacks 05TW "underlying homotopy target of a total strict filtered-injective resolution"]
noncomputable abbrev target (C : Type u) [Category.{v} C] [Abelian C] :
    Resolution.Total C ⥤ HomotopyCategory.Plus C :=
  Underlying.target C ⋙ HomotopyCategory.Plus.quotient C

/-- The underlying comparison on total strict resolutions after passing to the bounded-below
homotopy category. -/
@[stacks 05TW "underlying homotopy comparison of total strict filtered-injective resolutions"]
noncomputable abbrev comparison (C : Type u) [Category.{v} C] [Abelian C] :
    source C ⟶ target C :=
  Functor.whiskerRight (Underlying.comparison C)
    (HomotopyCategory.Plus.quotient C)

/-- The homotopy source is the bounded filtered source after applying the canonical underlying
homotopy functor. -/
@[simp, stacks 05TW "underlying homotopy source of a total strict resolution"]
theorem source_obj (X : Resolution.Total C) :
    (source C).obj X =
      (FilteredObject.Finite.Plus.Forget.homotopy C).obj X.base := sorry

/-- The homotopy source maps a total morphism by the canonical underlying homotopy functor. -/
@[simp, stacks 05TU "underlying homotopy source map of a total strict resolution"]
theorem source_map {X Y : Resolution.Total C} (f : X ⟶ Y) :
    (source C).map f =
      (FilteredObject.Finite.Plus.Forget.homotopy C).map f.base := sorry

/-- The homotopy target of a total resolution is its stored underlying homotopy target. -/
@[simp, stacks 05TW "underlying homotopy target of a total strict resolution"]
theorem target_obj (X : Resolution.Total C) :
    (target C).obj X = X.obj.underlyingHomotopy := sorry

/-- The homotopy target maps a total morphism by its stored underlying homotopy target map. -/
@[simp, stacks 05TU "underlying homotopy target map of a total strict resolution"]
theorem target_map {X Y : Resolution.Total C} (f : X ⟶ Y) :
    (target C).map f = f.displayed.underlyingHomotopyMap := sorry

/-- A component of the total underlying homotopy comparison is the comparison attached to its
stored resolution. -/
@[simp, stacks 05TW "component of the total underlying homotopy comparison"]
theorem comparison_app (X : Resolution.Total C) :
    (comparison C).app X = X.obj.underlyingHomotopyComparison := sorry

/-- Forward naturality of the underlying homotopy comparison on total strict-resolution
morphisms. -/
@[reassoc, stacks 05TU "naturality of the total underlying homotopy comparison"]
theorem comparison_naturality {X Y : Resolution.Total C} (f : X ⟶ Y) :
    (source C).map f ≫ (comparison C).app Y =
      (comparison C).app X ≫ (target C).map f := sorry

end Homotopy

end CochainComplex.FilteredInjectivePlus.Resolution.Total.Underlying
