/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_33_2_Cartesian
public import stacks_project.Chap85.Lemma_85_36_2_Hypercovering
public import stacks_project.Chap85.Lemma_85_36_2_Equivalence

/-!
# Lemma 85.36.2

If `a : U ⟶ X` is a proper hypercovering of an algebraic space `X` over `S`,
then `a⁻¹` on sheaves of sets and on abelian sheaves is fully faithful with
essential image the cartesian sheaves, and with quasi-inverse `a_*`.
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

/-- Lemma 85.36.2 (1). Let `S` be a scheme, `X` an algebraic space over `S`, `U` a
simplicial algebraic space over `S`, and `a : U ⟶ X` a proper hypercovering of
`X`. Then `a⁻¹ : Sh(X_étale) ⥤ Sh(U_étale)` is fully faithful with essential
image the cartesian sheaves of sets, and `a_*` provides the quasi-inverse. Here
`a` is the Section 85.32 spaces-étale augmentation. -/
@[stacks 0DHK]
def properSheafCartesianEquivalence (ha : IsProperHypercovering a) :
    Sheaf (spacesEtaleTopology X) (Type (u + 1)) ≌ Cartesian U (Type (u + 1)) :=
  properCartesianEquivalence a (Type (u + 1)) ha

/-- The forward functor of `properSheafCartesianEquivalence` is `a⁻¹` corestricted to
cartesian sheaves of sets. -/
theorem properSheafCartesianEquivalence_functor (ha : IsProperHypercovering a) :
    (properSheafCartesianEquivalence a ha).functor =
      properCartesianFunctor a (Type (u + 1)) :=
  sorry

/-- The inverse functor of `properSheafCartesianEquivalence` is `a_*` on cartesian
sheaves of sets. -/
theorem properSheafCartesianEquivalence_inverse (ha : IsProperHypercovering a) :
    (properSheafCartesianEquivalence a ha).inverse =
      properCartesianInverse a (Type (u + 1)) :=
  sorry

/-- A sheaf of sets on `U_étale` lies in the essential image of `a⁻¹` if and only
if it is cartesian. -/
theorem properSheaf_mem_essImage_iff_isCartesian (ha : IsProperHypercovering a)
    (G : Sheaf (spacesEtaleTotalTopology U) (Type (u + 1))) :
    (inverseImage U (Type (u + 1)) a).essImage G ↔ IsCartesian U (Type (u + 1)) G :=
  sorry

/-- Inverse image of sheaves of sets along the spaces-étale augmentation is
`(spacesEtaleAugmentation U a)⁻¹`. -/
theorem properSheafCartesianEquivalence_inverseImage :
    inverseImage U (Type (u + 1)) a = (spacesEtaleAugmentation U a)⁻¹ :=
  sorry

/-- Lemma 85.36.2 (2). Let `S` be a scheme, `X` an algebraic space over `S`, `U` a
simplicial algebraic space over `S`, and `a : U ⟶ X` a proper hypercovering of
`X`. Then `a⁻¹ : Ab(X_étale) ⥤ Ab(U_étale)` is fully faithful with essential
image the cartesian sheaves of abelian groups, and `a_*` provides the
quasi-inverse. Here `a` is the Section 85.32 spaces-étale augmentation. -/
@[stacks 0DHK]
def properAbelianCartesianEquivalence (ha : IsProperHypercovering a) :
    Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1} ≌
      Cartesian U AddCommGrpCat.{u + 1} :=
  properCartesianEquivalence a AddCommGrpCat.{u + 1} ha

/-- The forward functor of `properAbelianCartesianEquivalence` is `a⁻¹` corestricted
to cartesian sheaves of abelian groups. -/
theorem properAbelianCartesianEquivalence_functor (ha : IsProperHypercovering a) :
    (properAbelianCartesianEquivalence a ha).functor =
      properCartesianFunctor a AddCommGrpCat.{u + 1} :=
  sorry

/-- The inverse functor of `properAbelianCartesianEquivalence` is `a_*` on cartesian
sheaves of abelian groups. -/
theorem properAbelianCartesianEquivalence_inverse (ha : IsProperHypercovering a) :
    (properAbelianCartesianEquivalence a ha).inverse =
      properCartesianInverse a AddCommGrpCat.{u + 1} :=
  sorry

/-- An abelian sheaf on `U_étale` lies in the essential image of `a⁻¹` if and only
if it is cartesian. -/
theorem properAbelian_mem_essImage_iff_isCartesian (ha : IsProperHypercovering a)
    (G : Sheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1}) :
    (inverseImage U AddCommGrpCat.{u + 1} a).essImage G ↔
      IsCartesian U AddCommGrpCat.{u + 1} G :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
