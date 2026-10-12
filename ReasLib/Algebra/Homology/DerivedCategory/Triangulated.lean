/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic

@[expose] public section

open CategoryTheory

universe w v u

namespace DerivedCategory

/-- The derived category of an abelian category with a chosen localization
at quasi-isomorphisms is triangulated. -/
instance isTriangulated (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] :
    CategoryTheory.IsTriangulated (DerivedCategory A) := inferInstance

end DerivedCategory
