module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.Pushforward.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.Naturality
public import ReasLib.CategoryTheory.Functor.Derived.Composition.Right

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Functor.RightDerived
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

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

/-- The iterated cochain unit for `Rf_* ⋙ Rg_*` combines the cochain units of
`f_*` and `g_*` with the complex-level composition isomorphism. -/
def etaleDerivedPushforwardComp_iteratedUnit :
    RightDerived.Cochain.toDerived
        (etaleModulePushforward f Λ ⋙ etaleModulePushforward g Λ) ⟶
      (DerivedCategory.Q :
          CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
            DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))) ⋙
        ((etaleDerivedPushforward f : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
          DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) ⋙
          (etaleDerivedPushforward g : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
            DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ)))) :=
  (Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (etaleModulePushforward f Λ ⋙ etaleModulePushforward g Λ))
        (ComplexShape.up ℤ)).symm
      (DerivedCategory.Q :
        CochainComplex (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
          DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ)))).hom ≫
    (Functor.associator
      ((etaleModulePushforward f Λ).mapHomologicalComplex (ComplexShape.up ℤ))
      ((etaleModulePushforward g Λ).mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.Q :
        CochainComplex (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
          DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ)))).hom ≫
    whiskerLeft
      ((etaleModulePushforward f Λ).mapHomologicalComplex (ComplexShape.up ℤ))
      (RightDerived.Cochain.unit (etaleModulePushforward g Λ)) ≫
    (Functor.associator
      ((etaleModulePushforward f Λ).mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.Q :
        CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
          DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))
      (etaleDerivedPushforward g :
        DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
          DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ)))).inv ≫
    whiskerRight
      (RightDerived.Cochain.unit (etaleModulePushforward f Λ))
      (etaleDerivedPushforward g :
        DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
          DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))) ≫
    (Functor.associator
      (DerivedCategory.Q :
        CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
          DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)))
      (etaleDerivedPushforward f : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
        DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))
      (etaleDerivedPushforward g : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
        DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ)))).hom

/-- Derived identification of `R(f ≫ g)_*` with `R(g_* ∘ f_*)` along
`etaleModulePushforwardCompIso.symm`. -/
def etaleDerivedPushforwardComp_iso :
    RightDerived.Cochain.functor (etaleModulePushforward (f ≫ g) Λ) ≅
      RightDerived.Cochain.functor
        (etaleModulePushforward f Λ ⋙ etaleModulePushforward g Λ) :=
  RightDerived.natIsoOfIso
    (DerivedCategory.Q :
      CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
        DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)))
    (HomologicalComplex.quasiIso
      (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))
    (RightDerived.Cochain.unit (etaleModulePushforward (f ≫ g) Λ))
    (RightDerived.Cochain.unit
      (etaleModulePushforward f Λ ⋙ etaleModulePushforward g Λ))
    (Functor.isoWhiskerRight
      (NatIso.mapHomologicalComplex
        (etaleModulePushforwardCompIso f g).symm (ComplexShape.up ℤ))
      (DerivedCategory.Q :
        CochainComplex (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
          DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))))

/-- Canonical Leray comparison `R(f ≫ g)_* ⟶ Rf_* ⋙ Rg_*`. -/
def etaleDerivedPushforwardComp :
    (etaleDerivedPushforward (f ≫ g) :
        DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
          DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))) ⟶
      (etaleDerivedPushforward f : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
        DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) ⋙
        (etaleDerivedPushforward g : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
          DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))) :=
  (etaleDerivedPushforwardComp_iso f g Λ).hom ≫
    (RightDerived.Cochain.functor
        (etaleModulePushforward f Λ ⋙ etaleModulePushforward g Λ)).rightDerivedDesc
      (RightDerived.Cochain.unit
        (etaleModulePushforward f Λ ⋙ etaleModulePushforward g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))
      ((etaleDerivedPushforward f : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
        DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) ⋙
        (etaleDerivedPushforward g : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
          DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))))
      (etaleDerivedPushforwardComp_iteratedUnit f g Λ)

/-- The canonical Leray comparison for two small-étale pushforwards is an
isomorphism. -/
instance etaleDerivedPushforwardComp_isIso :
    IsIso (etaleDerivedPushforwardComp f g Λ) := sorry

end AlgebraicGeometry.Scheme.Etale

end
