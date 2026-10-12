/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowCohomology.Restriction

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

#check (@AlgebraicGeometry.ChowCohomology.restrict :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] {Y' Y : Scheme.{u}} {p : Y' ⟶ S} {q : Y ⟶ S}
    [LocallyOfFiniteType p] [LocallyOfFiniteType q] (f : Over.mk p ⟶ Over.mk q),
    AlgebraicGeometry.ChowCohomology.ring delta q →ₐ[ℤ]
      AlgebraicGeometry.ChowCohomology.ring delta p)
