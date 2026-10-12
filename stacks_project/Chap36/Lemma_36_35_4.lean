/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Relative.Triangulated
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Relative.Retracts
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 36.35.4 (1): for a flat, locally finitely presented morphism `f : X ⟶ S`,
the `S`-perfect objects of `D(𝒪_X)` form a triangulated subcategory. -/
@[stacks 0DI3] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.perfectRelativeTo_isTriangulated :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f],
      ObjectProperty.IsTriangulated
        (AlgebraicGeometry.Scheme.ModuleDerived.perfectRelativeTo f))

/- Lemma 36.35.4 (2): for a flat, locally finitely presented morphism `f : X ⟶ S`,
the `S`-perfect objects of `D(𝒪_X)` form a saturated subcategory. -/
@[stacks 0DI3] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.perfectRelativeTo_isStableUnderRetracts :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f],
      ObjectProperty.IsStableUnderRetracts
        (AlgebraicGeometry.Scheme.ModuleDerived.perfectRelativeTo f))
