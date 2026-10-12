/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.CommSq
public import stacks_project.Chap63.Lemma_63_8_1_Comparison
public import stacks_project.Chap63.Lemma_63_8_3_Comp

/-!
# Horizontal pasting of derived lower shriek / proper pushforward comparisons

The whiskered composite of two adjacent Lemma 63.8.1 comparisons, and the
outer-rectangle comparison rewritten along the composition identifications
`(h' ≫ h)_! ≅ h'_! ⋙ h_!` and `(g' ≫ g)_! ≅ g'_! ⋙ g_!`.
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
variable (Λ : Type u) [CommRing Λ]
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
  (Functor.associator
      (etaleDerivedPushforward f'')
      (lowerShriekModuleDerived h' Λ)
      (lowerShriekModuleDerived h Λ)).inv ≫
    whiskerRight
      (etaleDerivedLowerShriekPushforward f' f'' h' g' h_left Λ)
      (lowerShriekModuleDerived h Λ) ≫
    (Functor.associator
      (lowerShriekModuleDerived g' Λ)
      (etaleDerivedPushforward f')
      (lowerShriekModuleDerived h Λ)).hom ≫
    whiskerLeft
      (lowerShriekModuleDerived g' Λ)
      (etaleDerivedLowerShriekPushforward f f' h g h_right Λ)

/-- `etaleDerivedLowerShriekPushforwardHoriz` is the associator-whiskered
composite of the two Lemma 63.8.1 square comparisons. -/
theorem etaleDerivedLowerShriekPushforwardHoriz_eq
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
    etaleDerivedLowerShriekPushforwardHoriz
        f'' f' f g' g h' h h_left h_right Λ =
      (Functor.associator
          (etaleDerivedPushforward f'')
          (lowerShriekModuleDerived h' Λ)
          (lowerShriekModuleDerived h Λ)).inv ≫
        whiskerRight
          (etaleDerivedLowerShriekPushforward f' f'' h' g' h_left Λ)
          (lowerShriekModuleDerived h Λ) ≫
        (Functor.associator
          (lowerShriekModuleDerived g' Λ)
          (etaleDerivedPushforward f')
          (lowerShriekModuleDerived h Λ)).hom ≫
        whiskerLeft
          (lowerShriekModuleDerived g' Λ)
          (etaleDerivedLowerShriekPushforward f f' h g h_right Λ) :=
  sorry

/-- The outer-rectangle Lemma 63.8.1 comparison, rewritten on iterated lower
shriek via `lowerShriekModuleDerivedCompIso`. -/
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
  whiskerLeft
      (etaleDerivedPushforward f'')
      (lowerShriekModuleDerivedCompIso h' h Λ).hom ≫
    etaleDerivedLowerShriekPushforward f f'' (h' ≫ h) (g' ≫ g)
      (h_left.horiz_comp h_right) Λ ≫
    whiskerRight
      (lowerShriekModuleDerivedCompIso g' g Λ).inv
      (etaleDerivedPushforward f) ≫
    (Functor.associator
      (lowerShriekModuleDerived g' Λ)
      (lowerShriekModuleDerived g Λ)
      (etaleDerivedPushforward f)).hom

end AlgebraicGeometry.Scheme.Etale

end
