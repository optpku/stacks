/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.GroupTheory.Torsion
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.CompactSupport
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open CategoryTheory.Sheaf
open CategoryTheory.DerivedCategory
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- For a separated finite-type morphism between quasi-compact quasi-separated schemes and a
torsion commutative coefficient ring, derived lower shriek satisfies the projection formula
for arbitrary unbounded derived objects, using an explicit compactification. -/
theorem etaleDerivedLowerShriek_tensor_inverseImage
    {Y : Scheme.{u}} (X : Over Y) {Λ : Type u} [CommRing Λ]
    [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    (P : Compactification.Of Y X)
    [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ U : X.left.Etale,
      HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
    [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
    [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ U : P.obj.right.left.Etale,
      HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
    [HasDerivedCategory
      (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ U : Y.Etale,
      HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
    [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
    [(etaleExtensionByZero (Compactification.Of.ι P)
        (ModuleCat.{u} Λ)).Additive]
    [PreservesFiniteLimits
      (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
    [PreservesFiniteColimits
      (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
    [((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Y.smallEtaleTopology
        P.obj.right.left.smallEtaleTopology).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Y.smallEtaleTopology
          P.obj.right.left.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ))]
    [((X.left.smallEtaleTopology.W :
        MorphismProperty (X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ))).IsMonoidal]
    [MonoidalPreadditive (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
    [((Y.smallEtaleTopology.W :
        MorphismProperty (Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ))).IsMonoidal]
    [MonoidalPreadditive (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
    [∀ (K L : CochainComplex (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ),
        HomologicalComplex.HasMapBifunctor K L
          (curriedTensor (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)))
          (ComplexShape.up ℤ)]
    [∀ (K L : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ),
        HomologicalComplex.HasMapBifunctor K L
          (curriedTensor (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))
          (ComplexShape.up ℤ)]
    [hXTensor :
        DerivedTensor.Right.Has (C := Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
    [hYTensor :
        DerivedTensor.Right.Has (C := Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
    [((smallEtalePullback X.hom).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Y.smallEtaleTopology X.left.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback X.hom).sheafPullback
        (ModuleCat.{u} Λ) Y.smallEtaleTopology X.left.smallEtaleTopology).Additive]
    [PreservesFiniteLimits
      ((smallEtalePullback X.hom).sheafPullback
        (ModuleCat.{u} Λ) Y.smallEtaleTopology X.left.smallEtaleTopology)]
    [PreservesFiniteColimits
      ((smallEtalePullback X.hom).sheafPullback
        (ModuleCat.{u} Λ) Y.smallEtaleTopology X.left.smallEtaleTopology)]
    (hΛ : AddMonoid.IsTorsion Λ)
    (E : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) :
    IsIsomorphic
      ((etaleDerivedLowerShriek X P).obj E ⊗ᴸ K)
      ((etaleDerivedLowerShriek X P).obj
        (E ⊗ᴸ
          ((smallEtalePullback X.hom).sheafPullback
              (ModuleCat.{u} Λ) Y.smallEtaleTopology
              X.left.smallEtaleTopology).mapDerivedCategory.obj
            K)) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
