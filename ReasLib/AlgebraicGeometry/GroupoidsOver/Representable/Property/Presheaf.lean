/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fppf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Property
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Presheaf

/-!
# Morphism properties of presheaves and their groupoid fibrations

A morphism of presheaves representable by algebraic spaces has a morphism
property if and only if its canonical associated morphism of groupoid
fibrations has that property.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- A morphism of set-valued presheaves over a scheme that is representable by
algebraic spaces has a base-change-stable, fppf-target-local morphism property
if and only if its canonical associated morphism of categories fibred in
groupoids has that property. -/
@[stacks 045A]
theorem has_iff_ofPresheaf {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u}
    (P : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    {a : F ⟶ G} (ha : AlgebraicSpace.representableByAlgebraicSpaces a) :
    ha.has P ↔
      has P ((Sets.toGroupoids (Over S)).map ((Sets.ofPresheaf (Over S)).map a)) :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
