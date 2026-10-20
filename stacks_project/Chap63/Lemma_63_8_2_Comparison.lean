/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.Pushforward.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ProperLowerShriek.VerticalComposition
public import stacks_project.Chap63.Lemma_63_8_1_Comparison
public import stacks_project.Chap63.Remark_63_10_9

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Functor.RightDerived
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

section PushforwardComp

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable (Λ : Type u) [Ring Λ]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Z.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Z.Etale,
  HasWeakSheafify (Z.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [(etaleModulePushforward f Λ).Additive]
variable [(etaleModulePushforward g Λ).Additive]
variable [(etaleModulePushforward (f ≫ g) Λ).Additive]
variable [(etaleModulePushforward f Λ ⋙ etaleModulePushforward g Λ).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
  (HomologicalComplex.quasiIso
    (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived (etaleModulePushforward g Λ))
  (HomologicalComplex.quasiIso
    (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived (etaleModulePushforward (f ≫ g) Λ))
  (HomologicalComplex.quasiIso
    (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    (etaleModulePushforward f Λ ⋙ etaleModulePushforward g Λ))
  (HomologicalComplex.quasiIso
    (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]

section

#check (AlgebraicGeometry.Scheme.Etale.etaleDerivedPushforwardComp_iteratedUnit f g Λ :
  RightDerived.Cochain.toDerived
        (etaleModulePushforward f Λ ⋙ etaleModulePushforward g Λ) ⟶
      (DerivedCategory.Q :
          CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
            DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))) ⋙
        ((etaleDerivedPushforward f : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
          DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) ⋙
          (etaleDerivedPushforward g : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
            DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ)))))

end

section

#check (AlgebraicGeometry.Scheme.Etale.etaleDerivedPushforwardComp_iso f g Λ :
  RightDerived.Cochain.functor (etaleModulePushforward (f ≫ g) Λ) ≅
      RightDerived.Cochain.functor
        (etaleModulePushforward f Λ ⋙ etaleModulePushforward g Λ))

end

section

#check (AlgebraicGeometry.Scheme.Etale.etaleDerivedPushforwardComp f g Λ :
  (etaleDerivedPushforward (f ≫ g) :
        DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
          DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))) ⟶
      (etaleDerivedPushforward f : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
        DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) ⋙
        (etaleDerivedPushforward g : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
          DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))))

end

section

#check (AlgebraicGeometry.Scheme.Etale.etaleDerivedPushforwardComp_isIso f g Λ :
  IsIso (etaleDerivedPushforwardComp f g Λ))

end

end PushforwardComp

section VerticalComp

variable {X' X Y' Y Z' Z : Scheme.{u}}
variable (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y ⟶ Z) (g' : Y' ⟶ Z')
variable (k : X' ⟶ X) (l : Y' ⟶ Y) (m : Z' ⟶ Z)
variable (h_top : CommSq k f' f l) (h_bot : CommSq l g' g m)
variable [IsProper f] [IsProper f'] [IsProper g] [IsProper g']
variable [IsSeparated k] [LocallyQuasiFinite k] [LocallyOfFiniteType k]
variable [IsSeparated l] [LocallyQuasiFinite l] [LocallyOfFiniteType l]
variable [IsSeparated m] [LocallyQuasiFinite m] [LocallyOfFiniteType m]
variable (Λ : Type u) [Ring Λ]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X'.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y'.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Z.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Z'.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Z.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Z'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y'.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Z'.smallEtaleTopology AddCommGrpCat.{u}]
variable [X.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Z.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Z'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : X'.Etale,
  HasWeakSheafify (X'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y'.Etale,
  HasWeakSheafify (Y'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Z.Etale,
  HasWeakSheafify (Z.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Z'.Etale,
  HasWeakSheafify (Z'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Z'.smallEtaleTopology (ModuleCat.{u} Λ))]

section

variable
    [(etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward g Λ).Additive]
    [(etaleModulePushforward g' Λ).Additive]
    [(etaleModulePushforward f' Λ ⋙ lowerShriekModule l Λ).Additive]
    [(lowerShriekModule k Λ ⋙ etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward g' Λ ⋙ lowerShriekModule m Λ).Additive]
    [(lowerShriekModule l Λ ⋙ etaleModulePushforward g Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward g' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f' Λ ⋙ lowerShriekModule l Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule k Λ ⋙ etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward g' Λ ⋙ lowerShriekModule m Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule l Λ ⋙ etaleModulePushforward g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]

#check (AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriekPushforward_vcomp_whisker f f' g g' k l m h_top h_bot Λ :
  etaleDerivedPushforward f' ⋙ etaleDerivedPushforward g' ⋙
        lowerShriekModuleDerived m Λ ⟶
      lowerShriekModuleDerived k Λ ⋙ etaleDerivedPushforward f ⋙
        etaleDerivedPushforward g)

end

section

variable
    [(etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward g Λ).Additive]
    [(etaleModulePushforward g' Λ).Additive]
    [(etaleModulePushforward (f' ≫ g') Λ).Additive]
    [(etaleModulePushforward f' Λ ⋙ etaleModulePushforward g' Λ).Additive]
    [(etaleModulePushforward f' Λ ⋙ lowerShriekModule l Λ).Additive]
    [(lowerShriekModule k Λ ⋙ etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward g' Λ ⋙ lowerShriekModule m Λ).Additive]
    [(lowerShriekModule l Λ ⋙ etaleModulePushforward g Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward g' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward (f' ≫ g') Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f' Λ ⋙ etaleModulePushforward g' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f' Λ ⋙ lowerShriekModule l Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule k Λ ⋙ etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward g' Λ ⋙ lowerShriekModule m Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule l Λ ⋙ etaleModulePushforward g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]

#check (AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriekPushforward_vcomp_inner f f' g g' k l m h_top h_bot Λ :
  etaleDerivedPushforward (f' ≫ g') ⋙ lowerShriekModuleDerived m Λ ⟶
      lowerShriekModuleDerived k Λ ⋙ etaleDerivedPushforward f ⋙
        etaleDerivedPushforward g)

end

section

variable
    [(etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward g Λ).Additive]
    [(etaleModulePushforward g' Λ).Additive]
    [(etaleModulePushforward (f ≫ g) Λ).Additive]
    [(etaleModulePushforward (f' ≫ g') Λ).Additive]
    [(etaleModulePushforward f Λ ⋙ etaleModulePushforward g Λ).Additive]
    [(etaleModulePushforward (f' ≫ g') Λ ⋙ lowerShriekModule m Λ).Additive]
    [(lowerShriekModule k Λ ⋙ etaleModulePushforward (f ≫ g) Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward g' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward (f ≫ g) Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward (f' ≫ g') Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f Λ ⋙ etaleModulePushforward g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward (f' ≫ g') Λ ⋙ lowerShriekModule m Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule k Λ ⋙ etaleModulePushforward (f ≫ g) Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]

#check (AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriekPushforward_vcomp_outer f f' g g' k l m h_top h_bot Λ :
  etaleDerivedPushforward (f' ≫ g') ⋙ lowerShriekModuleDerived m Λ ⟶
      lowerShriekModuleDerived k Λ ⋙ etaleDerivedPushforward f ⋙
        etaleDerivedPushforward g)

end

section

variable
    [(etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward g Λ).Additive]
    [(etaleModulePushforward g' Λ).Additive]
    [(etaleModulePushforward (f ≫ g) Λ).Additive]
    [(etaleModulePushforward (f' ≫ g') Λ).Additive]
    [(etaleModulePushforward f Λ ⋙ etaleModulePushforward g Λ).Additive]
    [(etaleModulePushforward f' Λ ⋙ etaleModulePushforward g' Λ).Additive]
    [(etaleModulePushforward f' Λ ⋙ lowerShriekModule l Λ).Additive]
    [(lowerShriekModule k Λ ⋙ etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward g' Λ ⋙ lowerShriekModule m Λ).Additive]
    [(lowerShriekModule l Λ ⋙ etaleModulePushforward g Λ).Additive]
    [(etaleModulePushforward (f' ≫ g') Λ ⋙ lowerShriekModule m Λ).Additive]
    [(lowerShriekModule k Λ ⋙ etaleModulePushforward (f ≫ g) Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward g' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward (f ≫ g) Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward (f' ≫ g') Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f Λ ⋙ etaleModulePushforward g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f' Λ ⋙ etaleModulePushforward g' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f' Λ ⋙ lowerShriekModule l Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule k Λ ⋙ etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward g' Λ ⋙ lowerShriekModule m Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule l Λ ⋙ etaleModulePushforward g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward (f' ≫ g') Λ ⋙ lowerShriekModule m Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule k Λ ⋙ etaleModulePushforward (f ≫ g) Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    (K : DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)))

#check (AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriekPushforward_vcomp_app f f' g g' k l m h_top h_bot Λ K :
  (etaleDerivedLowerShriekPushforward_vcomp_inner f f' g g' k l m
        h_top h_bot Λ).app K =
      (etaleDerivedLowerShriekPushforward_vcomp_outer f f' g g' k l m
        h_top h_bot Λ).app K)

end

end VerticalComp

end AlgebraicGeometry.Scheme.Etale

end
