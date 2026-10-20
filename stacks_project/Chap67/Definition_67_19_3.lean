/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.UniversallyInjective
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory

/- Definition 67.19.3: a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S` is universally injective if for every morphism `Y' ⟶ Y` of algebraic spaces
over `S` the induced map `|Y' ×_Y X| ⟶ |Y'|` is injective. -/
@[stacks 03MV] #check (AlgebraicGeometry.AlgebraicSpace.UniversallyInjective :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S},
    (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.universallyInjective_iff :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
    (f : X ⟶ Y),
    AlgebraicGeometry.AlgebraicSpace.UniversallyInjective f ↔
      CategoryTheory.MorphismProperty.universally
        AlgebraicGeometry.AlgebraicSpace.pointsInjective f)

#check (AlgebraicGeometry.AlgebraicSpace.universallyInjective_iff_injective_of_isPullback :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
    (f : X ⟶ Y),
    AlgebraicGeometry.AlgebraicSpace.UniversallyInjective f ↔
      ∀ {Z P : AlgebraicGeometry.AlgebraicSpace S} {g : Z ⟶ Y}
        {pZ : P ⟶ Z} {pX : P ⟶ X},
        CategoryTheory.IsPullback pZ pX g f →
          Function.Injective (AlgebraicGeometry.AlgebraicSpace.Points.map pZ))
