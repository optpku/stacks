/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.Pushforward.Additive
public import ReasLib.CategoryTheory.DerivedCategory.Functor.KInjectiveModel
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.Pullback
public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.Functor.RightDerived
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Small-étale module sheaves admit K-injective resolutions, giving total
right derivation of étale module pushforward. -/
instance instHasRightDerived_etaleModulePushforward
    {S T : Scheme.{u}} (f : S ⟶ T) (Λ : Type u) [Ring Λ]
    [HasSheafify S.smallEtaleTopology (ModuleCat.{u} Λ)]
    [HasSheafify T.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ V : S.Etale, HasWeakSheafify (S.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
    [∀ V : T.Etale, HasWeakSheafify (T.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
    [HasDerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))]
    [HasDerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ))] :
    HasRightDerivedFunctor (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) :=
  by
    letI : IsGrothendieckAbelian.{u}
        (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) :=
      Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology S (ModuleCat.{u} Λ)
    exact Functor.KInjectiveModel.hasRightDerived (etaleModulePushforward f Λ)

/-- Unfolding `etaleModulePushforward` recovers right-derivability of continuous
small-étale module pushforward. -/
instance instHasRightDerived_sheafPushforwardContinuous
    {S T : Scheme.{u}} (f : S ⟶ T) (Λ : Type u) [Ring Λ]
    [HasSheafify S.smallEtaleTopology (ModuleCat.{u} Λ)]
    [HasSheafify T.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ V : S.Etale, HasWeakSheafify (S.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
    [∀ V : T.Etale, HasWeakSheafify (T.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
    [HasDerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))]
    [HasDerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ))] :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback f).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) T.smallEtaleTopology S.smallEtaleTopology))
      (HomologicalComplex.quasiIso (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) :=
  instHasRightDerived_etaleModulePushforward f Λ

/-- The underived composite `f_* ⋙ g_*` admits a total right derived functor. -/
instance instHasRightDerived_etaleModulePushforward_functorComp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (Λ : Type u) [Ring Λ]
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
    [HasSheafify Z.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ V : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
    [∀ V : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
    [∀ V : Z.Etale, HasWeakSheafify (Z.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
    [HasDerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))] :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f Λ ⋙ etaleModulePushforward g Λ))
      (HomologicalComplex.quasiIso (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) :=
  sorry

/-- Derived étale pushforward satisfies the universal property of the right derived functor. -/
instance instIsRightDerived_etaleDerivedPushforward
    {S T : Scheme.{u}} (f : S ⟶ T) (Λ : Type u) [Ring Λ]
    [HasSheafify S.smallEtaleTopology (ModuleCat.{u} Λ)]
    [HasSheafify T.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ V : S.Etale, HasWeakSheafify (S.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
    [∀ V : T.Etale, HasWeakSheafify (T.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
    [HasDerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))]
    [HasDerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ))] :
    (etaleDerivedPushforward f : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ))).IsRightDerivedFunctor
      (RightDerived.Cochain.unit (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) :=
  Functor.instIsRightDerivedFunctorTotalRightDerivedTotalRightDerivedUnit
    (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
    DerivedCategory.Q
    (HomologicalComplex.quasiIso (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))
      (ComplexShape.up ℤ))


/-- Every additive functor between small-étale module-sheaf categories admits total right
derivation, using K-injective resolutions in its Grothendieck source. -/
instance moduleSheafFunctor_hasRightDerived
    {S T : Scheme.{u}} {Λ : Type u} [Ring Λ]
    [HasSheafify S.smallEtaleTopology (ModuleCat.{u} Λ)]
    [HasSheafify T.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ V : S.Etale, HasWeakSheafify (S.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
    [∀ V : T.Etale, HasWeakSheafify (T.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
    [HasDerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))]
    [HasDerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ))]
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ) ⥤
      Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ)) [F.Additive] :
    HasRightDerivedFunctor (RightDerived.Cochain.toDerived F)
      (HomologicalComplex.quasiIso (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) := by
  letI : IsGrothendieckAbelian.{u}
      (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) :=
    Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology S (ModuleCat.{u} Λ)
  exact Functor.KInjectiveModel.hasRightDerived F

section NormalizedAdjunction

variable {A B : Scheme.{u}} (p : A ⟶ B) (Λ : Type u) [CommRing Λ]
variable [HasSheafify A.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify B.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : A.Etale, HasWeakSheafify (A.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : B.Etale, HasWeakSheafify (B.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf A.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ F : B.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback p).op.HasLeftKanExtension F]

/-- A derived inverse/direct-image adjunction is geometrically normalized when its unit,
on complexes, is the actual sheaf-adjunction unit followed by the right-derived unit.
The exact inverse-image factor identifies the two presentations of its target. -/
abbrev ModuleDerivedAdjunctionIsNormalized
    (adj : etaleModuleDerivedInverseImage p Λ ⊣ etaleDerivedPushforward p) : Prop :=
  ∀ K : CochainComplex (Sheaf B.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ,
    adj.unit.app (DerivedCategory.Q.obj K) ≫
        (etaleDerivedPushforward p).map
          ((Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ)).mapDerivedCategoryFactors.hom.app K) =
      DerivedCategory.Q.map
          ((Adjunction.mapHomologicalComplexAdjunction
            ((smallEtalePullback p).sheafAdjunctionContinuous (ModuleCat.{u} Λ)
              B.smallEtaleTopology A.smallEtaleTopology) (ComplexShape.up ℤ)).unit.app K) ≫
        (RightDerived.Cochain.unit (etaleModulePushforward p Λ)).app
          (((Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)

/-- A supplied derived geometric adjunction, with its normalization separated from the
adjunction data by a subtype.  No adjunction is selected from an existence proposition. -/
abbrev ModuleDerivedAdjunction :=
  {adj : etaleModuleDerivedInverseImage p Λ ⊣ etaleDerivedPushforward p //
    ModuleDerivedAdjunctionIsNormalized p Λ adj}

/-- The geometric unit normalization makes the supplied adjunction unique. -/
theorem moduleDerivedAdjunction_unique (a b : ModuleDerivedAdjunction p Λ) : a = b := sorry

end NormalizedAdjunction

end AlgebraicGeometry.Scheme.Etale

end
