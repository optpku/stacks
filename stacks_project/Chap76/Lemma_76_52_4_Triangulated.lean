/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import stacks_project.Chap76.Lemma_76_52_4_Relative

/-!
# Triangles of relatively perfect derived modules on algebraic spaces

Relative perfectness for flat, locally finitely presented morphisms of algebraic spaces
is closed under the triangulated structure on `D(𝒪_X)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The objects perfect relative to a flat, locally finitely presented morphism of
algebraic spaces form a triangulated object property. -/
instance perfectRelativeTo_isTriangulated (f : X ⟶ Y)
    [Flat f] [LocallyOfFinitePresentation f] :
    ObjectProperty.IsTriangulated (perfectRelativeTo f) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
