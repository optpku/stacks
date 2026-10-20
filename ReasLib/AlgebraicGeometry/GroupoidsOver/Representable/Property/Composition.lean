/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fppf
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property

/-!
# Composition of representable morphisms having a morphism property

Properties of algebraic-space morphisms stable under base change and composition
and fppf local on the target are inherited by composites of representable
1-morphisms of groupoid fibrations.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- If a property of algebraic-space morphisms is stable under base change and
composition and fppf local on the target, the composite of two 1-morphisms of
groupoid fibrations representable by algebraic spaces having that property
also has that property. -/
theorem has.comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    (P : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    [P.IsStableUnderComposition]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : relativelyRepresentableByAlgebraicSpaces f)
    (hg : relativelyRepresentableByAlgebraicSpaces g)
    (hfP : has P f) (hgP : has P g) : has P (f ≫ g) :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
