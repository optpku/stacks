/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.Admissible
import StacksCheckRecall

/-!
# Remark 104.5.5

For an algebraic stack `X`, Lemma 104.5.4 implies that the parasitic
cohomology subcategory of `D_{LQCoh^{fbc}}(𝒪_X)` is left admissible. Its
left orthogonal `A` is then right admissible, and
`A ⟶ D_{LQCoh^{fbc}}(𝒪_X) ⟶ D_QCoh(𝒪_X)` is an equivalence. Thus
`D_QCoh(𝒪_X)` may be viewed as a strictly full saturated triangulated
subcategory of `D_{LQCoh^{fbc}}(𝒪_X)` and of `D(X_fppf, 𝒪_X)`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open AlgebraicGeometry.GroupoidsOver CategoryTheory.ObjectProperty
open DerivedQCoh

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]

/- Remark 104.5.5: the parasitic cohomology subcategory of
`D_{LQCoh^{fbc}}(𝒪_X)` is left admissible. Its left orthogonal `A` is right
admissible, and the composite `A ⥤ D_{LQCoh^{fbc}}(𝒪_X) ⥤ D_QCoh(𝒪_X)` is an
equivalence. Hence `D_QCoh(𝒪_X)` is realized as a strictly full saturated
triangulated subcategory of both `D_{LQCoh^{fbc}}(𝒪_X)` and `D(X_fppf, 𝒪_X)`. -/
@[stacks 0H11]
#check (AlgebraicGeometry.AlgebraicStack.derivedParasitic_isLeftAdmissible :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    (derivedParasitic X).IsLeftAdmissible)

/- The left orthogonal `A` is right admissible in
`D_{LQCoh^{fbc}}(𝒪_X)`. -/
#check (AlgebraicGeometry.AlgebraicStack.derivedParasitic_leftOrthogonal_isRightAdmissible :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    (derivedParasitic X).leftOrthogonal.IsRightAdmissible)

/- The composition `A ⥤ D_{LQCoh^{fbc}}(𝒪_X) ⥤ D_QCoh(𝒪_X)`
is an equivalence. -/
#check (AlgebraicGeometry.AlgebraicStack.DerivedQCoh.leftOrthogonalComparison.instIsEquivalence :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    (leftOrthogonalComparison X).IsEquivalence)

/- `A` is a strictly full saturated triangulated
subcategory of `D_{LQCoh^{fbc}}(𝒪_X)`. -/
#check (inferInstance : (derivedParasitic X).leftOrthogonal.IsTriangulated)
#check (inferInstance : (derivedParasitic X).leftOrthogonal.IsClosedUnderIsomorphisms)
#check (inferInstance : (derivedParasitic X).leftOrthogonal.IsStableUnderRetracts)

/- The same subcategory view of `D_QCoh(𝒪_X)` is strictly
full, saturated, and triangulated in `D(X_fppf, 𝒪_X)`. -/
#check (inferInstance : (leftOrthogonalInclusion X).essImage.IsTriangulated)
#check (inferInstance : (leftOrthogonalInclusion X).essImage.IsClosedUnderIsomorphisms)
#check (AlgebraicGeometry.AlgebraicStack.DerivedQCoh.leftOrthogonalInclusion.essImage_isStableUnderRetracts :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    (leftOrthogonalInclusion X).essImage.IsStableUnderRetracts)

end AlgebraicGeometry.AlgebraicStack
