/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Action.OrbitMap
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Small
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.LocallyOfFinitePresentation

/-!
# Algebraicity of quotient stacks of group algebraic space actions

An orbit map gives an algebraicity criterion through flatness and local finite
presentation of the restricted action groupoid.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open GroupoidAlgebraicSpace
open scoped CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace.Action

/-- The quotient stack of a group algebraic space action is algebraic if and
only if some morphism to the action space has an fppf-sheaf-surjective orbit
map and a restricted action groupoid that is flat and locally of finite
presentation. -/
theorem isAlgebraicStack_quotientStack_iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (X : Action G) :
    AlgebraicStack (SmallQuotient.quotientStack (ofAction G X)) ↔
      ∃ (X' : Over B) (φ : X' ⟶ X.X),
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
            (orbitMap G X φ).left ∧
          GroupoidAlgebraicSpace.Flat ((ofAction G X).pullback φ) ∧
            GroupoidAlgebraicSpace.LocallyOfFinitePresentation ((ofAction G X).pullback φ) := sorry

/-- If a morphism `φ : X' ⟶ X` has orbit map a surjection of fppf sheaves and
the restricted action groupoid is flat and locally of finite presentation, then
`[X / G]` is an algebraic stack. -/
theorem isAlgebraicStack_quotientStack_of_orbitMap {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B) (X : Action G)
    {X' : Over B} (φ : X' ⟶ X.X)
    (h_surj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (orbitMap G X φ).left)
    [GroupoidAlgebraicSpace.Flat ((ofAction G X).pullback φ)]
    [GroupoidAlgebraicSpace.LocallyOfFinitePresentation ((ofAction G X).pullback φ)] :
    AlgebraicStack (SmallQuotient.quotientStack (ofAction G X)) := sorry

/-- If `[X / G]` is an algebraic stack, then there exists a morphism
`φ : X' ⟶ X` whose orbit map is a surjection of fppf sheaves and whose
restricted action groupoid is flat and locally of finite presentation. -/
theorem exists_orbitMap_of_isAlgebraicStack_quotientStack {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B) (X : Action G)
    [AlgebraicStack (SmallQuotient.quotientStack (ofAction G X))] :
    ∃ (X' : Over B) (φ : X' ⟶ X.X),
      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
          (orbitMap G X φ).left ∧
        GroupoidAlgebraicSpace.Flat ((ofAction G X).pullback φ) ∧
          GroupoidAlgebraicSpace.LocallyOfFinitePresentation ((ofAction G X).pullback φ) := sorry

/-- The quotient stack of a group algebraic space action is algebraic if and
only if some morphism has an fppf-sheaf-surjective orbit map and both
projections of the restricted arrow space are flat and locally of finite
presentation as morphisms of algebraic spaces. -/
theorem isAlgebraicStack_quotientStack_iff_spec {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B) (X : Action G) :
    AlgebraicStack (SmallQuotient.quotientStack (ofAction G X)) ↔
      ∃ (X' : Over B) (φ : X' ⟶ X.X),
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
            (orbitMap G X φ).left ∧
          AlgebraicSpace.Flat ((ofAction G X).pullback φ).s.left ∧
            AlgebraicSpace.Flat ((ofAction G X).pullback φ).t.left ∧
              AlgebraicSpace.LocallyOfFinitePresentation
                ((ofAction G X).pullback φ).s.left ∧
                AlgebraicSpace.LocallyOfFinitePresentation
                  ((ofAction G X).pullback φ).t.left := sorry

end AlgebraicGeometry.GroupAlgebraicSpace.Action
