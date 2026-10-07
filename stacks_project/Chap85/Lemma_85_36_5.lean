module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_36_5_Equivalence

/-!
# Lemma 85.36.5

If `a : U ⟶ X` is a proper hypercovering of an algebraic space `X` over a scheme
`S`, then `a⁻¹` induces an equivalence `D⁺(X_étale) ≌ D_𝒜⁺(U_étale)` with
quasi-inverse `Ra_*`, where `𝒜` is the weak Serre subcategory of cartesian
abelian sheaves on `U_étale` and `a` is the Section 85.32 spaces-étale
augmentation.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.Simplicial
open Functor
open scoped Simplicial

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)

/-- Lemma 85.36.5. Let `S` be a scheme, `X` an algebraic space over `S`, `U` a
simplicial algebraic space over `S`, and `a : U ⟶ X` a proper hypercovering of
`X`. Let `𝒜 ⊂ Ab(U_étale)` denote the weak Serre subcategory of cartesian
abelian sheaves. Then `a⁻¹` defines an equivalence
`D⁺(X_étale) ≌ D_𝒜⁺(U_étale)` with quasi-inverse `Ra_*`. Here
`a : Sh(U_étale) ⟶ Sh(X_étale)` is the Section 85.32 spaces-étale
augmentation, `a⁻¹` is `plusInverseImage a`, `Ra_*` is `plusDirectImage a`, and
`D_𝒜⁺(U_étale)` is `DerivedCategory.Plus.CohomologyIn` of
`cartesianProperty U AddCommGrpCat.{u + 1}`. -/
@[stacks 0DHN]
def properPlusCartesianEquivalence (ha : IsProperHypercovering a) :
    DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}) ≌
      DerivedCategory.Plus.CohomologyIn
        (cartesianProperty U AddCommGrpCat.{u + 1}) :=
  CategoryTheory.Equivalence.mk (properPlusCartesianFunctor a)
    (properPlusCartesianInverse a) (properPlusCartesianUnitIso a ha)
    (properPlusCartesianCounitIso a ha)

/-- The forward functor of `properPlusCartesianEquivalence` is `a⁻¹` corestricted
to `D⁺` objects with cartesian cohomology. -/
theorem properPlusCartesianEquivalence_functor (ha : IsProperHypercovering a) :
    (properPlusCartesianEquivalence a ha).functor =
      properPlusCartesianFunctor a :=
  sorry

/-- The inverse functor of `properPlusCartesianEquivalence` is `Ra_*` on `D⁺`
objects with cartesian cohomology. -/
theorem properPlusCartesianEquivalence_inverse (ha : IsProperHypercovering a) :
    (properPlusCartesianEquivalence a ha).inverse =
      properPlusCartesianInverse a :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
