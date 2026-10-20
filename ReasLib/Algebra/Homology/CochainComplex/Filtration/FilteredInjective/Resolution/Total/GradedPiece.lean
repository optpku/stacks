/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Filtration.FilteredInjective.Resolution.Total
public import ReasLib.Algebra.Homology.CochainComplex.Filtration.FilteredInjective.Resolution.Views

/-!
# Graded-Piece Functors on the Total Strict-Resolution Category

This leaf applies the bounded graded-piece functor to the source and target functors of the total
category of strict filtered-injective resolutions.  Its comparison transformations are obtained
by whiskering the total resolution comparison.  The homotopy layer is then obtained uniformly by
postcomposing with the bounded-below homotopy quotient.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CochainComplex.FilteredInjectivePlus.Resolution.Total.GradedPiece

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- Take the `p`-th graded piece of the source complex of a total strict filtered-injective
resolution. -/
@[stacks 05TW "graded-piece source functor on total strict resolutions"]
noncomputable abbrev source (p : ℤ) :
    Resolution.Total C ⥤ CochainComplex.Plus C :=
  Total.source C ⋙ FilteredObject.Finite.Plus.GradedPiece.cochain C p

/-- Take the `p`-th graded piece of the bounded target complex of a total strict
filtered-injective resolution. -/
@[stacks 05TW "graded-piece target functor on total strict resolutions"]
noncomputable abbrev target (p : ℤ) :
    Resolution.Total C ⥤ CochainComplex.Plus C :=
  Total.targetComplex C ⋙ FilteredObject.Finite.Plus.GradedPiece.cochain C p

/-- The natural comparison from source graded pieces to target graded pieces on the total
strict-resolution category. -/
@[stacks 05TW "graded-piece comparison on total strict resolutions"]
noncomputable def comparison (p : ℤ) : source C p ⟶ target C p :=
  Functor.whiskerRight (Total.comparison C)
    (FilteredObject.Finite.Plus.GradedPiece.cochain C p)

/-- The source graded-piece functor returns the graded piece of the stored base complex. -/
@[simp, stacks 05TW "object computation for the total graded-piece source"]
theorem source_obj (p : ℤ) (X : Resolution.Total C) :
    (source C p).obj X =
      (FilteredObject.Finite.Plus.GradedPiece.cochain C p).obj X.base := sorry

/-- The source graded-piece functor maps a total morphism through its stored base map. -/
@[simp, stacks 05TU "map computation for the total graded-piece source"]
theorem source_map (p : ℤ) {X Y : Resolution.Total C} (f : X ⟶ Y) :
    (source C p).map f =
      (FilteredObject.Finite.Plus.GradedPiece.cochain C p).map f.base := sorry

/-- The target graded-piece functor returns the graded piece of the stored resolution target. -/
@[simp, stacks 05TW "object computation for the total graded-piece target"]
theorem target_obj (p : ℤ) (X : Resolution.Total C) :
    (target C p).obj X = X.obj.gradedPiece p := sorry

/-- The target graded-piece functor maps a total morphism through its displayed resolution map. -/
@[simp, stacks 05TU "map computation for the total graded-piece target"]
theorem target_map (p : ℤ) {X Y : Resolution.Total C} (f : X ⟶ Y) :
    (target C p).map f = f.displayed.gradedPieceMap p := sorry

/-- A component of the total graded-piece comparison is the comparison of the stored
resolution. -/
@[simp, stacks 05TW "component computation for the total graded-piece comparison"]
theorem comparison_app (p : ℤ) (X : Resolution.Total C) :
    (comparison C p).app X = X.obj.gradedPieceComparison p := sorry

/-- Forward naturality of the total graded-piece comparison in terms of stored source and target
maps. -/
@[reassoc, stacks 05TU "naturality of the total graded-piece comparison"]
theorem comparison_naturality (p : ℤ) {X Y : Resolution.Total C} (f : X ⟶ Y) :
    (source C p).map f ≫ (comparison C p).app Y =
      (comparison C p).app X ≫ (target C p).map f := sorry

/-! ## Homotopy view -/

namespace Homotopy

/-- The source graded-piece functor followed by the bounded-below homotopy quotient. -/
@[stacks 05TW "graded-piece homotopy source functor on total strict resolutions"]
noncomputable abbrev source (p : ℤ) :
    Resolution.Total C ⥤ HomotopyCategory.Plus C :=
  GradedPiece.source C p ⋙ HomotopyCategory.Plus.quotient C

/-- The target graded-piece functor followed by the bounded-below homotopy quotient. -/
@[stacks 05TW "graded-piece homotopy target functor on total strict resolutions"]
noncomputable abbrev target (p : ℤ) :
    Resolution.Total C ⥤ HomotopyCategory.Plus C :=
  GradedPiece.target C p ⋙ HomotopyCategory.Plus.quotient C

/-- The total graded-piece comparison after passing to the bounded-below homotopy category. -/
@[stacks 05TW "graded-piece homotopy comparison on total strict resolutions"]
noncomputable def comparison (p : ℤ) : source C p ⟶ target C p :=
  Functor.whiskerRight (GradedPiece.comparison C p) (HomotopyCategory.Plus.quotient C)

/-- The homotopy source returns the quotient of the graded piece of the stored base complex. -/
@[simp, stacks 05TW "object computation for the total graded-piece homotopy source"]
theorem source_obj (p : ℤ) (X : Resolution.Total C) :
    (source C p).obj X =
      (FilteredObject.Finite.Plus.GradedPiece.homotopy C p).obj X.base := sorry

/-- The homotopy source maps a total morphism by quotienting its graded-piece base map. -/
@[simp, stacks 05TU "map computation for the total graded-piece homotopy source"]
theorem source_map (p : ℤ) {X Y : Resolution.Total C} (f : X ⟶ Y) :
    (source C p).map f =
      (FilteredObject.Finite.Plus.GradedPiece.homotopy C p).map f.base := sorry

/-- The homotopy target returns the graded-piece homotopy view of the stored resolution. -/
@[simp, stacks 05TW "object computation for the total graded-piece homotopy target"]
theorem target_obj (p : ℤ) (X : Resolution.Total C) :
    (target C p).obj X = X.obj.gradedPieceHomotopy p := sorry

/-- The homotopy target maps a total morphism through the graded-piece homotopy map of its
displayed resolution map. -/
@[simp, stacks 05TU "map computation for the total graded-piece homotopy target"]
theorem target_map (p : ℤ) {X Y : Resolution.Total C} (f : X ⟶ Y) :
    (target C p).map f = f.displayed.gradedPieceHomotopyMap p := sorry

/-- A component of the total homotopy comparison is the graded-piece homotopy comparison of the
stored resolution. -/
@[simp, stacks 05TW "component computation for the total graded-piece homotopy comparison"]
theorem comparison_app (p : ℤ) (X : Resolution.Total C) :
    (comparison C p).app X = X.obj.gradedPieceHomotopyComparison p := sorry

/-- Forward naturality of the total graded-piece homotopy comparison in terms of stored maps. -/
@[reassoc, stacks 05TU "naturality of the total graded-piece homotopy comparison"]
theorem comparison_naturality (p : ℤ) {X Y : Resolution.Total C} (f : X ⟶ Y) :
    (source C p).map f ≫ (comparison C p).app Y =
      (comparison C p).app X ≫ (target C p).map f := sorry

end Homotopy

end CochainComplex.FilteredInjectivePlus.Resolution.Total.GradedPiece
