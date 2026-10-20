/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ProperLowerShriek
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LowerShriek.Composition

/-!
# Horizontal compatibility of derived lower shriek with proper pushforward
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.Functor.RightDerived
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X'' X' X Y'' Y' Y : Scheme.{u}}
variable (f'' : X'' ⟶ Y'') (f' : X' ⟶ Y') (f : X ⟶ Y)
variable (g' : X'' ⟶ X') (g : X' ⟶ X) (h' : Y'' ⟶ Y') (h : Y' ⟶ Y)
variable (h_left : CommSq g' f'' f' h') (h_right : CommSq g f' f h)
variable [IsProper f] [IsProper f'] [IsProper f'']
variable [IsSeparated g] [LocallyQuasiFinite g] [LocallyOfFiniteType g]
variable [IsSeparated g'] [LocallyQuasiFinite g'] [LocallyOfFiniteType g']
variable [IsSeparated h] [LocallyQuasiFinite h] [LocallyOfFiniteType h]
variable [IsSeparated h'] [LocallyQuasiFinite h'] [LocallyOfFiniteType h']
variable (Λ : Type u) [Ring Λ]
variable [X''.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X'.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y''.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y'.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify X''.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y''.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify X''.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y''.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y'.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [X''.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y''.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasWeakSheafify X''.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify Y''.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X''.Etale,
  HasWeakSheafify (X''.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : X'.Etale,
  HasWeakSheafify (X'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y''.Etale,
  HasWeakSheafify (Y''.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y'.Etale,
  HasWeakSheafify (Y'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X''.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y''.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- The whiskered composite of the two square comparisons
`h_! ∘ (left comparison)` then `(right comparison) ∘ g'_!`. -/
def etaleDerivedLowerShriekPushforwardHoriz
    [(etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward f'' Λ).Additive]
    [(etaleModulePushforward f'' Λ ⋙ lowerShriekModule h' Λ).Additive]
    [(lowerShriekModule g' Λ ⋙ etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward f' Λ ⋙ lowerShriekModule h Λ).Additive]
    [(lowerShriekModule g Λ ⋙ etaleModulePushforward f Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f'' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X''.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f'' Λ ⋙ lowerShriekModule h' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X''.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule g' Λ ⋙ etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X''.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f' Λ ⋙ lowerShriekModule h Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule g Λ ⋙ etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    etaleDerivedPushforward f'' ⋙
        lowerShriekModuleDerived h' Λ ⋙ lowerShriekModuleDerived h Λ ⟶
      lowerShriekModuleDerived g' Λ ⋙ lowerShriekModuleDerived g Λ ⋙
        etaleDerivedPushforward f :=
  (Functor.associator (etaleDerivedPushforward f'')
      (lowerShriekModuleDerived h' Λ) (lowerShriekModuleDerived h Λ)).inv ≫
    whiskerRight
      (etaleDerivedLowerShriekPushforward f' f'' h' g' h_left Λ)
      (lowerShriekModuleDerived h Λ) ≫
    (Functor.associator (lowerShriekModuleDerived g' Λ)
      (etaleDerivedPushforward f') (lowerShriekModuleDerived h Λ)).hom ≫
    whiskerLeft (lowerShriekModuleDerived g' Λ)
      (etaleDerivedLowerShriekPushforward f f' h g h_right Λ)

/-- The canonical outer-square comparison, transported to iterated derived
lower shriek by its composition isomorphisms. -/
def etaleDerivedLowerShriekPushforward_horizOuter
    [(etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f'' Λ).Additive]
    [(etaleModulePushforward f'' Λ ⋙ lowerShriekModule (h' ≫ h) Λ).Additive]
    [(lowerShriekModule (g' ≫ g) Λ ⋙ etaleModulePushforward f Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f'' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X''.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f'' Λ ⋙ lowerShriekModule (h' ≫ h) Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X''.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule (g' ≫ g) Λ ⋙ etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X''.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    etaleDerivedPushforward f'' ⋙
        lowerShriekModuleDerived h' Λ ⋙ lowerShriekModuleDerived h Λ ⟶
      lowerShriekModuleDerived g' Λ ⋙ lowerShriekModuleDerived g Λ ⋙
        etaleDerivedPushforward f :=
  whiskerLeft (etaleDerivedPushforward f'')
      (lowerShriekModuleDerivedCompIso h' h Λ).hom ≫
    etaleDerivedLowerShriekPushforward f f'' (h' ≫ h) (g' ≫ g)
      (h_left.horiz_comp h_right) Λ ≫
    whiskerRight
      (lowerShriekModuleDerivedCompIso g' g Λ).inv
      (etaleDerivedPushforward f) ≫
    (Functor.associator (lowerShriekModuleDerived g' Λ)
      (lowerShriekModuleDerived g Λ) (etaleDerivedPushforward f)).hom

/-- For two horizontally adjacent commutative squares with proper vertical
maps and separated locally quasi-finite horizontal maps, the composite of the
canonical derived comparisons equals the transported outer-square comparison. -/
theorem etaleDerivedLowerShriekPushforward_horiz_comp
    [(etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward f'' Λ).Additive]
    [(etaleModulePushforward f'' Λ ⋙ lowerShriekModule h' Λ).Additive]
    [(lowerShriekModule g' Λ ⋙ etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward f' Λ ⋙ lowerShriekModule h Λ).Additive]
    [(lowerShriekModule g Λ ⋙ etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f'' Λ ⋙ lowerShriekModule (h' ≫ h) Λ).Additive]
    [(lowerShriekModule (g' ≫ g) Λ ⋙ etaleModulePushforward f Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f'' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X''.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f'' Λ ⋙ lowerShriekModule h' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X''.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule g' Λ ⋙ etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X''.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f' Λ ⋙ lowerShriekModule h Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule g Λ ⋙ etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f'' Λ ⋙ lowerShriekModule (h' ≫ h) Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X''.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule (g' ≫ g) Λ ⋙ etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X''.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    etaleDerivedLowerShriekPushforwardHoriz
        f'' f' f g' g h' h h_left h_right Λ =
      etaleDerivedLowerShriekPushforward_horizOuter
        f'' f' f g' g h' h h_left h_right Λ := sorry

/-- On each derived étale module sheaf, the composite of two adjacent proper
pushforward comparisons equals the transported outer-square comparison. -/
theorem etaleDerivedLowerShriekPushforward_horiz_comp_app
    [(etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward f'' Λ).Additive]
    [(etaleModulePushforward f'' Λ ⋙ lowerShriekModule h' Λ).Additive]
    [(lowerShriekModule g' Λ ⋙ etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward f' Λ ⋙ lowerShriekModule h Λ).Additive]
    [(lowerShriekModule g Λ ⋙ etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f'' Λ ⋙ lowerShriekModule (h' ≫ h) Λ).Additive]
    [(lowerShriekModule (g' ≫ g) Λ ⋙ etaleModulePushforward f Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f'' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X''.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f'' Λ ⋙ lowerShriekModule h' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X''.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule g' Λ ⋙ etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X''.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f' Λ ⋙ lowerShriekModule h Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule g Λ ⋙ etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f'' Λ ⋙ lowerShriekModule (h' ≫ h) Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X''.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule (g' ≫ g) Λ ⋙ etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X''.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    (K : DerivedCategory (Sheaf X''.smallEtaleTopology (ModuleCat.{u} Λ))) :
    (etaleDerivedLowerShriekPushforwardHoriz
        f'' f' f g' g h' h h_left h_right Λ).app K =
      (etaleDerivedLowerShriekPushforward_horizOuter
        f'' f' f g' g h' h h_left h_right Λ).app K := sorry

end AlgebraicGeometry.Scheme.Etale

end
