/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Tensor
import StacksCheckRecall

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open CategoryTheory.Sheaf
open CategoryTheory.DerivedCategory
open scoped GrothendieckTopologyDerivedSections
open scoped CategoryTheory.DerivedCategory.DerivedTensor

universe u
/- Lemma 59.92.4: for a quasi-compact and quasi-separated scheme `X`, derived
étale global sections commute with tensoring by the derived constant sheaf of
`K ∈ D⁺(ℤ)`. -/
@[stacks 0F0E] #check
  (AlgebraicGeometry.Scheme.Etale.rGamma_tensor_constant :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
      [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
        (CategoryTheory.Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
      [MonoidalCategory (CategoryTheory.Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
      [MonoidalPreadditive (CategoryTheory.Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
      [MonoidalCategory AddCommGrpCat.{u}]
      [∀ (K L : CochainComplex (CategoryTheory.Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) ℤ),
        HomologicalComplex.HasMapBifunctor K L
          (curriedTensor (CategoryTheory.Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
          (ComplexShape.up ℤ)]
      [MonoidalPreadditive AddCommGrpCat.{u}]
      [∀ (K L : CochainComplex AddCommGrpCat.{u} ℤ),
        HomologicalComplex.HasMapBifunctor K L
          (curriedTensor AddCommGrpCat.{u}) (ComplexShape.up ℤ)]
      [@DerivedTensor.Right.Has
        (CategoryTheory.Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) _ _ _ _ _ _]
      [@DerivedTensor.Right.Has AddCommGrpCat.{u} _ _ _ _ _ _]
      [(constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).Additive]
      [PreservesFiniteLimits (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u})]
      [PreservesFiniteColimits (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u})]
      [Functor.HasRightDerivedFunctor
        (RightDerived.Cochain.toDerived
          (siteAbelianSectionsFunctor X.smallEtaleTopology
            (AlgebraicGeometry.Scheme.Etale.globalEtale X)))
        (HomologicalComplex.quasiIso
          (CategoryTheory.Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
          (ComplexShape.up ℤ))]
      (E : DerivedCategory.Plus
        (CategoryTheory.Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
      (K : DerivedCategory.Plus AddCommGrpCat.{u}),
      Nonempty
        ((siteAbelianSectionsDerived X.smallEtaleTopology
          (AlgebraicGeometry.Scheme.Etale.globalEtale X)).obj
            (DerivedTensor.Right.obj (DerivedCategory.Plus.ι.obj E)
              (AlgebraicGeometry.Scheme.Etale.underlineDerived X K)) ≅
          DerivedTensor.Right.obj
            ((siteAbelianSectionsDerived X.smallEtaleTopology
              (AlgebraicGeometry.Scheme.Etale.globalEtale X)).obj
              (DerivedCategory.Plus.ι.obj E))
            (DerivedCategory.Plus.ι.obj K)))
