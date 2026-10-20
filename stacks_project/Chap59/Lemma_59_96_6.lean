/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ProjectionFormula
import StacksCheckRecall

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

universe u v

/- Lemma 59.96.6: For a proper morphism of schemes and a torsion coefficient ring,
the unbounded derived étale projection formula holds. -/
@[stacks 0F0G] #check
  (AlgebraicGeometry.Scheme.Etale.etalePushforwardDerived_tensor_inverseImage_of_isProper :
    ∀ {X Y : Scheme.{u}} {Λ : Type v} [CommRing Λ]
      [HasSheafify X.smallEtaleTopology (ModuleCat.{v} Λ)]
      [HasSheafify Y.smallEtaleTopology (ModuleCat.{v} Λ)]
      [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
      [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))]
      [((X.smallEtaleTopology.W :
          MorphismProperty (X.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ))).IsMonoidal]
      [MonoidalPreadditive (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
      [((Y.smallEtaleTopology.W :
          MorphismProperty (Y.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ))).IsMonoidal]
      [MonoidalPreadditive (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))]
      [∀ (K L : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) ℤ),
          HomologicalComplex.HasMapBifunctor K L
            (curriedTensor (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))) (ComplexShape.up ℤ)]
      [∀ (K L : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ)) ℤ),
          HomologicalComplex.HasMapBifunctor K L
            (curriedTensor (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))) (ComplexShape.up ℤ)]
      [hXTensor :
          DerivedTensor.Right.Has (C := Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
      [hYTensor :
          DerivedTensor.Right.Has (C := Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))]
    (f : X ⟶ Y) [IsProper f]
    [((smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{v} Λ) Y.smallEtaleTopology X.smallEtaleTopology).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback f).sheafPushforwardContinuous
          (ModuleCat.{v} Λ) Y.smallEtaleTopology X.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) (ComplexShape.up ℤ))]
    [((smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{v} Λ) Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback f).sheafPullback
        (ModuleCat.{v} Λ) Y.smallEtaleTopology X.smallEtaleTopology).Additive]
    [PreservesFiniteLimits
      ((smallEtalePullback f).sheafPullback
        (ModuleCat.{v} Λ) Y.smallEtaleTopology X.smallEtaleTopology)]
    [PreservesFiniteColimits
      ((smallEtalePullback f).sheafPullback
        (ModuleCat.{v} Λ) Y.smallEtaleTopology X.smallEtaleTopology)]
    (hΛ : AddMonoid.IsTorsion Λ)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))),
    Nonempty
      ((RightDerived.Cochain.functor
            ((smallEtalePullback f).sheafPushforwardContinuous
              (ModuleCat.{v} Λ) Y.smallEtaleTopology X.smallEtaleTopology)).obj E ⊗ᴸ K ≅
        (RightDerived.Cochain.functor
            ((smallEtalePullback f).sheafPushforwardContinuous
              (ModuleCat.{v} Λ) Y.smallEtaleTopology X.smallEtaleTopology)).obj
          (E ⊗ᴸ
            (((smallEtalePullback f).sheafPullback
                (ModuleCat.{v} Λ) Y.smallEtaleTopology X.smallEtaleTopology).mapDerivedCategory.obj
              K))))

end
