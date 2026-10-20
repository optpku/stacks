module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Valuation.ValuationRing
public import ReasLib.RingTheory.Valuation.Extension
public import stacks_project.Chap66.Definition_66_4_1_Points

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion

/-!
# Valuative criterion for morphisms of algebraic spaces

The valuative-square, dominating-extension, and criterion API is provided by the
shared mathematical owner. These typed checks preserve the chapter import surface.
-/

@[expose] public section

open CategoryTheory

universe u

#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.Uniqueness :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S},
    (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.Existence :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S},
    (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S},
    (X ⟶ Y) → Prop)
