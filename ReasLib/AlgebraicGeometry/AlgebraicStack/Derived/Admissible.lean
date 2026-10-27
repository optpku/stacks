/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Triangulated.Orthogonal
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.QuasiCoherent
public import ReasLib.CategoryTheory.ObjectProperty.Orthogonal.Retract
public import ReasLib.CategoryTheory.Pretriangulated.Admissible

/-!
# Admissibility of parasitic cohomology

The parasitic cohomology subcategory of `D_{LQCoh^{fbc}}(𝒪_X)` is left
admissible. Its left orthogonal is right admissible and maps equivalently
to the Verdier quotient `DerivedQCoh X`. Its essential image in
`D(X_fppf, 𝒪_X)` is stable under retracts.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The parasitic cohomology subcategory of `D_{LQCoh^{fbc}}(𝒪_X)` is left
admissible. -/
instance derivedParasitic_isLeftAdmissible {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (derivedParasitic X).IsLeftAdmissible := sorry

/-- The left orthogonal of parasitic cohomology is right admissible in
`D_{LQCoh^{fbc}}(𝒪_X)`. -/
instance derivedParasitic_leftOrthogonal_isRightAdmissible {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (derivedParasitic X).leftOrthogonal.IsRightAdmissible := sorry

namespace DerivedQCoh

/-- The comparison from the left orthogonal of parasitic cohomology to the
Verdier quotient is the inclusion followed by the quotient functor. -/
abbrev leftOrthogonalComparison {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (derivedParasitic X).leftOrthogonal.FullSubcategory ⥤ DerivedQCoh X :=
  (derivedParasitic X).leftOrthogonal.ι ⋙ quotientFunctor X

/-- The canonical comparison from the left orthogonal of parasitic cohomology
to `D_QCoh(𝒪_X)` is an equivalence. -/
instance leftOrthogonalComparison.instIsEquivalence {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (leftOrthogonalComparison X).IsEquivalence := sorry

/-- The inclusion of the left orthogonal of parasitic cohomology into
`D(X_fppf, 𝒪_X)`. -/
abbrev leftOrthogonalInclusion {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (derivedParasitic X).leftOrthogonal.FullSubcategory ⥤ ModuleDerived X :=
  (derivedParasitic X).leftOrthogonal.ι ⋙ DerivedLQCohFbc.inclusion X

namespace leftOrthogonalInclusion

/-- An object of `D(𝒪_X)` lies in the essential image of
`leftOrthogonalInclusion` iff it is isomorphic to the image of a
left-orthogonal object of `D_{LQCoh^{fbc}}(𝒪_X)`. -/
theorem essImage_iff {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (E : ModuleDerived X) :
    (leftOrthogonalInclusion X).essImage E ↔
      ∃ K : DerivedLQCohFbc X, (derivedParasitic X).leftOrthogonal K ∧
        Nonempty ((DerivedLQCohFbc.inclusion X).obj K ≅ E) := sorry

/-- The essential image of `leftOrthogonalInclusion` is stable under retracts
in `D(X_fppf, 𝒪_X)`. -/
instance essImage_isStableUnderRetracts {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (leftOrthogonalInclusion X).essImage.IsStableUnderRetracts := sorry

end leftOrthogonalInclusion

end DerivedQCoh

end AlgebraicGeometry.AlgebraicStack
