/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.Pushforward.Additive

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
  sorry

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
  RightDerived.Cochain.isRightDerived (etaleModulePushforward f Λ)


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
        (ComplexShape.up ℤ)) := sorry

end AlgebraicGeometry.Scheme.Etale

end
