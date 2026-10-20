/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.UniversalFirstOrder
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FormallyEtale

/-!
# Universal first-order thickenings over formally étale morphisms

A universal first-order thickening over an algebraic space remains universal
after postcomposition with a formally étale morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder

/-- A universal first-order thickening of `Z` over `Y` via `g : Z' ⟶ Y`
is a universal first-order thickening of `Z` over `X` via `g ≫ f` whenever
`f : Y ⟶ X` is formally étale. -/
instance of_formallyEtale {S : Scheme.{u}} {X Y Z Z' : AlgebraicSpace S}
    (i : Z ⟶ Z') (g : Z' ⟶ Y) (f : Y ⟶ X) [IsUniversalFirstOrder i g]
    [FormallyEtale f] : IsUniversalFirstOrder i (g ≫ f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder
