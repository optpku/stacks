/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.FppfDerivedEquivalence

/-!
# Lemma 85.33.5

Let `S` be a scheme, `X` an algebraic space over `S`, and `U` a simplicial algebraic
space over `S`, with augmentation `a : U ⟶ X`. Let `A` be the weak Serre subcategory
of cartesian abelian sheaves on `U_étale`. If `a` is an fppf hypercovering of `X`,
then `a⁻¹` is an equivalence `D⁺(X_étale) ≌ D_A⁺(U_étale)` with quasi-inverse `Ra_*`,
where `a : Sh(U_étale) ⟶ Sh(X_étale)` is the Section 85.32 spaces-étale augmentation.
-/

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Simplicial
open scoped Simplicial

/- Lemma 85.33.5: Let `S` be a scheme. Let `X` be an algebraic space over `S`. Let `U`
be a simplicial algebraic space over `S`. Let `a : U ⟶ X` be an augmentation. Let `A`
denote the weak Serre subcategory of cartesian abelian sheaves on `U_étale`. If `a` is
an fppf hypercovering of `X`, then `a⁻¹` defines an equivalence
`D⁺(X_étale) ≌ D_A⁺(U_étale)` with quasi-inverse `Ra_*`. Here
`a : Sh(U_étale) ⟶ Sh(X_étale)` is the Section 85.32 spaces-étale augmentation. -/
@[stacks 0DH9] #check
  (AlgebraicGeometry.AlgebraicSpace.Simplicial.EtaleDerived.plusCartesianEquivalence :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      {U : SimplicialObject (AlgebraicSpace S)}
      (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) (ha : IsFppfHypercovering a),
      DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}) ≌
        DerivedCategory.Plus.CohomologyIn (EtaleCartesian.IsCartesianAbelian U))

#check
  (AlgebraicGeometry.AlgebraicSpace.Simplicial.EtaleDerived.plusCartesianEquivalence_functor :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      {U : SimplicialObject (AlgebraicSpace S)}
      (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) (ha : IsFppfHypercovering a),
      (EtaleDerived.plusCartesianEquivalence a ha).functor = EtaleDerived.plusCartesianFunctor a)

#check
  (AlgebraicGeometry.AlgebraicSpace.Simplicial.EtaleDerived.plusCartesianEquivalence_inverse :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      {U : SimplicialObject (AlgebraicSpace S)}
      (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) (ha : IsFppfHypercovering a),
      (EtaleDerived.plusCartesianEquivalence a ha).inverse = EtaleDerived.plusCartesianInverse a)

