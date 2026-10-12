/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_33_5_Equivalence

/-!
# Lemma 85.33.5

Let `S` be a scheme, `X` an algebraic space over `S`, and `U` a simplicial algebraic
space over `S`, with augmentation `a : U ⟶ X`. Let `A` be the weak Serre subcategory
of cartesian abelian sheaves on `U_étale`. If `a` is an fppf hypercovering of `X`,
then `a⁻¹` is an equivalence `D⁺(X_étale) ≌ D_A⁺(U_étale)` with quasi-inverse `Ra_*`,
where `a : Sh(U_étale) ⟶ Sh(X_étale)` is the Section 85.32 spaces-étale augmentation.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.Simplicial
open Functor
open scoped Simplicial

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)

/-- Lemma 85.33.5: Let `S` be a scheme. Let `X` be an algebraic space over `S`. Let `U`
be a simplicial algebraic space over `S`. Let `a : U ⟶ X` be an augmentation. Let `A`
denote the weak Serre subcategory of cartesian abelian sheaves on `U_étale`. If `a` is
an fppf hypercovering of `X`, then `a⁻¹` defines an equivalence
`D⁺(X_étale) ≌ D_A⁺(U_étale)` with quasi-inverse `Ra_*`. Here
`a : Sh(U_étale) ⟶ Sh(X_étale)` is the Section 85.32 spaces-étale augmentation. -/
@[stacks 0DH9]
def plusCartesianEquivalence (ha : IsFppfHypercovering a) :
    DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}) ≌
      DerivedCategory.Plus.CohomologyIn
        (cartesianProperty U AddCommGrpCat.{u + 1}) :=
  CategoryTheory.Equivalence.mk (plusCartesianFunctor a) (plusCartesianInverse a)
    (plusCartesianUnitIso a ha) (plusCartesianCounitIso a ha)

/-- The forward functor of `plusCartesianEquivalence` is `a⁻¹` corestricted to
`D_A⁺(U_étale)`. -/
theorem plusCartesianEquivalence_functor (ha : IsFppfHypercovering a) :
    (plusCartesianEquivalence a ha).functor = plusCartesianFunctor a :=
  sorry

/-- The inverse functor of `plusCartesianEquivalence` is `Ra_*` on `D_A⁺(U_étale)`. -/
theorem plusCartesianEquivalence_inverse (ha : IsFppfHypercovering a) :
    (plusCartesianEquivalence a ha).inverse = plusCartesianInverse a :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
