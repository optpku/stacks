/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap104.Remark_104_5_5_Admissible
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

/- Remark 104.5.5 (1): `D_{Parasitic ∩ LQCoh^{fbc}}(𝒪_X)` is a left admissible
subcategory of `D_{LQCoh^{fbc}}(𝒪_X)`. -/
@[stacks 0H11]
#check (derivedParasitic_isLeftAdmissible X)

/- Remark 104.5.5 (2): the left orthogonal `A` is right admissible in
`D_{LQCoh^{fbc}}(𝒪_X)`. -/
@[stacks 0H11]
#check (derivedParasitic_leftOrthogonal_isRightAdmissible X)

/- Remark 104.5.5 (3): the composition `A ⟶ D_{LQCoh^{fbc}}(𝒪_X) ⟶ D_QCoh(𝒪_X)`
is an equivalence. -/
@[stacks 0H11]
#check (leftOrthogonalComparison.instIsEquivalence X)

/- Remark 104.5.5 (4): `A` is a strictly full saturated triangulated
subcategory of `D_{LQCoh^{fbc}}(𝒪_X)`. -/
@[stacks 0H11]
#check (inferInstance : (derivedParasitic X).leftOrthogonal.IsTriangulated)
@[stacks 0H11]
#check (inferInstance : (derivedParasitic X).leftOrthogonal.IsClosedUnderIsomorphisms)
@[stacks 0H11]
#check (inferInstance : (derivedParasitic X).leftOrthogonal.IsStableUnderRetracts)

/- Remark 104.5.5 (5): the same subcategory view of `D_QCoh(𝒪_X)` is strictly
full, saturated, and triangulated in `D(X_fppf, 𝒪_X)`. -/
@[stacks 0H11]
#check (inferInstance : (leftOrthogonalInclusion X).essImage.IsTriangulated)
@[stacks 0H11]
#check (inferInstance : (leftOrthogonalInclusion X).essImage.IsClosedUnderIsomorphisms)
@[stacks 0H11]
#check (leftOrthogonalInclusion.essImage_isStableUnderRetracts X)

end AlgebraicGeometry.AlgebraicStack
