/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowCohomology.FirstChern
public import ReasLib.AlgebraicGeometry.ChowCohomology.Restriction

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

#check (@AlgebraicGeometry.ChowCohomology.firstChernClass :
  ∀ {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ],
    AlgebraicGeometry.ChowCohomology.degree δ p 1)
