/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import stacks_project.Chap76.Lemma_76_52_4_Relative

/-!
# Retracts of relatively perfect derived modules on algebraic spaces

Relative perfectness for flat, locally finitely presented morphisms of algebraic spaces
is stable under retracts in `D(𝒪_X)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The objects perfect relative to a flat, locally finitely presented morphism of
algebraic spaces are stable under retracts. -/
instance perfectRelativeTo_isStableUnderRetracts (f : X ⟶ Y)
    [Flat f] [LocallyOfFinitePresentation f] :
    ObjectProperty.IsStableUnderRetracts (perfectRelativeTo f) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
