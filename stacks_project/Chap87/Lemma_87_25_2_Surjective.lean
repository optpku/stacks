/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap87.Definition_87_25_1_Surjective
import Mathlib.Tactic.CrossRefAttribute

/-!
# Surjective morphisms of formal algebraic spaces

A morphism of formal algebraic spaces is surjective when the induced map of
algebraic-space reductions is a surjective morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/- The composition of two surjective morphisms of formal algebraic spaces is
surjective. -/
#check (AlgebraicGeometry.FormalAlgebraicSpace.Surjective.comp :
  ∀ {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [IsFormalAlgebraicSpace Z]
    [Reduction X] [Reduction Y] [Reduction Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Surjective f] [Surjective g],
    Surjective (f ≫ g))

#check (AlgebraicGeometry.FormalAlgebraicSpace.mapReduction_comp :
  ∀ {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [IsFormalAlgebraicSpace Z]
    [Reduction X] [Reduction Y] [Reduction Z]
    (f : X ⟶ Y) (g : Y ⟶ Z),
    mapReduction (f ≫ g) = mapReduction f ≫ mapReduction g)

#check (AlgebraicGeometry.FormalAlgebraicSpace.Surjective :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] (f : X ⟶ Y), Prop)

#check (AlgebraicGeometry.FormalAlgebraicSpace.Surjective.id :
  ∀ {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [Reduction X], Surjective (𝟙 X))

#check (AlgebraicGeometry.FormalAlgebraicSpace.Surjective.of :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] {f : X ⟶ Y},
    AlgebraicSpace.Surjective (mapReduction f) → Surjective f)

#check (AlgebraicGeometry.FormalAlgebraicSpace.Surjective.spec :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] (f : X ⟶ Y) [Surjective f],
    AlgebraicSpace.Surjective (mapReduction f))

end AlgebraicGeometry.FormalAlgebraicSpace
