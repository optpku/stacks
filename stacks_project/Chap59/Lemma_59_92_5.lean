/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ProjectionFormula
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.Sheaf CategoryTheory.DerivedCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

/- Lemma 59.92.5: for a proper morphism, bounded-below étale complexes satisfy the
projection formula when the first complex has torsion cohomology. Abelian sheaves are
represented by modules over `ULift.{u} ℤ`, canonically identified with integer modules
by `ULift.ringEquiv`. Both tensor expressions are bounded below. -/
@[stacks 0F0F] #check
  (AlgebraicGeometry.Scheme.Hom.etaleDerivedPushforward_tensor_inverseImage :
    ∀ {X Y : Scheme.{u}}
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ))]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ)))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ)))]
    [((X.smallEtaleTopology.W :
        MorphismProperty (X.Etaleᵒᵖ ⥤ ModuleCat.{u} (ULift.{u} ℤ)))).IsMonoidal]
    [MonoidalPreadditive (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ)))]
    [((Y.smallEtaleTopology.W :
        MorphismProperty (Y.Etaleᵒᵖ ⥤ ModuleCat.{u} (ULift.{u} ℤ)))).IsMonoidal]
    [MonoidalPreadditive (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ)))]
    [∀ (K L : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ))) ℤ),
        HomologicalComplex.HasMapBifunctor K L
          (curriedTensor (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ)))) (ComplexShape.up ℤ)]
    [∀ (K L : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ))) ℤ),
        HomologicalComplex.HasMapBifunctor K L
          (curriedTensor (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ)))) (ComplexShape.up ℤ)]
    [hXTensor :
        DerivedTensor.Right.Has (C := Sheaf X.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ)))]
    [hYTensor :
        DerivedTensor.Right.Has (C := Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ)))]
    [X.smallEtaleTopology.HasSheafCompose
        (forget₂ (ModuleCat.{u} (ULift.{u} ℤ)) AddCommGrpCat.{u})]
    (f : X ⟶ Y) [IsProper f]
    [((smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{u} (ULift.{u} ℤ)) Y.smallEtaleTopology X.smallEtaleTopology).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback f).sheafPushforwardContinuous
          (ModuleCat.{u} (ULift.{u} ℤ)) Y.smallEtaleTopology X.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ))) (ComplexShape.up ℤ))]
    [((smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{u} (ULift.{u} ℤ)) Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback f).sheafPullback
        (ModuleCat.{u} (ULift.{u} ℤ)) Y.smallEtaleTopology X.smallEtaleTopology).Additive]
    [PreservesFiniteLimits
      ((smallEtalePullback f).sheafPullback
        (ModuleCat.{u} (ULift.{u} ℤ)) Y.smallEtaleTopology X.smallEtaleTopology)]
    [PreservesFiniteColimits
      ((smallEtalePullback f).sheafPullback
        (ModuleCat.{u} (ULift.{u} ℤ)) Y.smallEtaleTopology X.smallEtaleTopology)]
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ))))
    (hE : ∀ i : ℤ,
      IsLocallyTorsion
        ((sheafCompose X.smallEtaleTopology
            (forget₂ (ModuleCat.{u} (ULift.{u} ℤ)) AddCommGrpCat.{u})).obj
          ((DerivedCategory.Plus.homologyFunctor
              (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ))) i).obj E)))
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ)))),
    (∃ n : ℤ,
      (DerivedCategory.Plus.ι.obj E ⊗ᴸ
        ((smallEtalePullback f).sheafPullback
          (ModuleCat.{u} (ULift.{u} ℤ)) Y.smallEtaleTopology X.smallEtaleTopology).mapDerivedCategory.obj
            (DerivedCategory.Plus.ι.obj K)).IsGE n) ∧
    (∃ n : ℤ,
      ((RightDerived.Cochain.functor
          ((smallEtalePullback f).sheafPushforwardContinuous
            (ModuleCat.{u} (ULift.{u} ℤ)) Y.smallEtaleTopology X.smallEtaleTopology)).obj
              (DerivedCategory.Plus.ι.obj E) ⊗ᴸ DerivedCategory.Plus.ι.obj K).IsGE n) ∧
    Nonempty
      ((RightDerived.Cochain.functor
          ((smallEtalePullback f).sheafPushforwardContinuous
            (ModuleCat.{u} (ULift.{u} ℤ)) Y.smallEtaleTopology X.smallEtaleTopology)).obj
              (DerivedCategory.Plus.ι.obj E) ⊗ᴸ DerivedCategory.Plus.ι.obj K ≅
        (RightDerived.Cochain.functor
          ((smallEtalePullback f).sheafPushforwardContinuous
            (ModuleCat.{u} (ULift.{u} ℤ)) Y.smallEtaleTopology X.smallEtaleTopology)).obj
          (DerivedCategory.Plus.ι.obj E ⊗ᴸ
            ((smallEtalePullback f).sheafPullback
              (ModuleCat.{u} (ULift.{u} ℤ)) Y.smallEtaleTopology X.smallEtaleTopology).mapDerivedCategory.obj
                (DerivedCategory.Plus.ι.obj K))))

end

end
