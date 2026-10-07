module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_33_2_Cartesian
public import stacks_project.Chap85.Lemma_85_33_2_Equivalence
public import stacks_project.Chap85.Lemma_85_33_2_Hypercovering

/-!
# Lemma 85.33.2

Let `S` be a scheme, `X` an algebraic space over `S`, and `U` a simplicial algebraic
space over `S`, with augmentation `a : U ⟶ X`. If `a` is an fppf hypercovering of `X`,
then `a⁻¹ : Sh(X_étale) ⥤ Sh(U_étale)` and `a⁻¹ : Ab(X_étale) ⥤ Ab(U_étale)` are fully
faithful with essential image the cartesian sheaves and quasi-inverse `a_*`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.Simplicial
open Functor
open scoped Simplicial MorphismOfTopoiIn

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)

/-- Lemma 85.33.2 (1): Let `S` be a scheme. Let `X` be an algebraic space over `S`. Let `U`
be a simplicial algebraic space over `S`. Let `a : U ⟶ X` be an augmentation. If `a` is an
fppf hypercovering of `X`, then `a⁻¹ : Sh(X_étale) ⥤ Sh(U_étale)` is fully faithful with
essential image the cartesian sheaves, and `a_*` provides the quasi-inverse functor. Here
`a : Sh(U_étale) ⟶ Sh(X_étale)` is the Section 85.32 spaces-étale augmentation. -/
@[stacks 0DH6]
def sheafCartesianEquivalence (ha : IsFppfHypercovering a) :
    Sheaf (spacesEtaleTopology X) (Type (u + 1)) ≌ Cartesian U (Type (u + 1)) :=
  cartesianEquivalence a (Type (u + 1)) ha

/-- The forward functor of `sheafCartesianEquivalence` is `a⁻¹` corestricted to cartesian
sheaves of sets. -/
theorem sheafCartesianEquivalence_functor (ha : IsFppfHypercovering a) :
    (sheafCartesianEquivalence a ha).functor = cartesianFunctor a (Type (u + 1)) :=
  sorry

/-- The inverse functor of `sheafCartesianEquivalence` is `a_*` on cartesian sheaves of
sets. -/
theorem sheafCartesianEquivalence_inverse (ha : IsFppfHypercovering a) :
    (sheafCartesianEquivalence a ha).inverse = cartesianInverse a (Type (u + 1)) :=
  sorry

/-- A sheaf of sets on `U_étale` lies in the essential image of `a⁻¹` if and only if it
is cartesian. -/
theorem sheaf_mem_essImage_iff_isCartesian (ha : IsFppfHypercovering a)
    (G : Sheaf (spacesEtaleTotalTopology U) (Type (u + 1))) :
    (inverseImage U (Type (u + 1)) a).essImage G ↔ IsCartesian U (Type (u + 1)) G :=
  sorry

/-- Lemma 85.33.2 (2): Let `S` be a scheme. Let `X` be an algebraic space over `S`. Let `U`
be a simplicial algebraic space over `S`. Let `a : U ⟶ X` be an augmentation. If `a` is an
fppf hypercovering of `X`, then `a⁻¹ : Ab(X_étale) ⥤ Ab(U_étale)` is fully faithful with
essential image the cartesian sheaves of abelian groups, and `a_*` provides the
quasi-inverse functor. -/
@[stacks 0DH6]
def abelianCartesianEquivalence (ha : IsFppfHypercovering a) :
    Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1} ≌
      Cartesian U AddCommGrpCat.{u + 1} :=
  cartesianEquivalence a AddCommGrpCat.{u + 1} ha

/-- The forward functor of `abelianCartesianEquivalence` is `a⁻¹` corestricted to cartesian
sheaves of abelian groups. -/
theorem abelianCartesianEquivalence_functor (ha : IsFppfHypercovering a) :
    (abelianCartesianEquivalence a ha).functor = cartesianFunctor a AddCommGrpCat.{u + 1} :=
  sorry

/-- The inverse functor of `abelianCartesianEquivalence` is `a_*` on cartesian sheaves of
abelian groups. -/
theorem abelianCartesianEquivalence_inverse (ha : IsFppfHypercovering a) :
    (abelianCartesianEquivalence a ha).inverse = cartesianInverse a AddCommGrpCat.{u + 1} :=
  sorry

/-- An abelian sheaf on `U_étale` lies in the essential image of `a⁻¹` if and only if it
is cartesian. -/
theorem abelian_mem_essImage_iff_isCartesian (ha : IsFppfHypercovering a)
    (G : Sheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1}) :
    (inverseImage U AddCommGrpCat.{u + 1} a).essImage G ↔
      IsCartesian U AddCommGrpCat.{u + 1} G :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
