/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallyEtale

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.FormallyEtale

/-- The composite of two formally étale scheme morphisms is formally étale. -/
instance comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [FormallyEtale f] [FormallyEtale g] : FormallyEtale (f ≫ g) := sorry

end AlgebraicGeometry.FormallyEtale
