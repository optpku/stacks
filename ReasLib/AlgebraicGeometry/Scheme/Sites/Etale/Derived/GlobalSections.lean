module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.Coefficients
public import ReasLib.CategoryTheory.Functor.Derived.Composition.Right
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.Naturality

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {Λ : Type u} [CommRing Λ]

/-- Global sections on the domain of a scheme morphism are naturally isomorphic
to global sections of its small-étale module pushforward. -/
def etaleModuleGlobalSectionsPushforwardIso :
    (sheafSections X.smallEtaleTopology (ModuleCat.{u} Λ)).obj
        (op (globalEtale X)) ≅
      etaleModulePushforward f Λ ⋙
        (sheafSections Y.smallEtaleTopology (ModuleCat.{u} Λ)).obj
          (op (globalEtale Y)) :=
  NatIso.ofComponents
    (fun F ↦ F.obj.mapIso (Iso.op (globalEtalePullbackIso f))) sorry

variable [HasSheafify (smallEtaleTopology X) (ModuleCat.{u} Λ)]
variable [∀ U : X.Etale,
  HasWeakSheafify ((smallEtaleTopology X).over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf (smallEtaleTopology X) (ModuleCat.{u} Λ))]
variable [HasSheafify (smallEtaleTopology Y) (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify ((smallEtaleTopology Y).over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ))]
variable [((smallEtalePullback f).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) (smallEtaleTopology Y) (smallEtaleTopology X)).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback f).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) (smallEtaleTopology Y) (smallEtaleTopology X)))
  (HomologicalComplex.quasiIso
    (Sheaf (smallEtaleTopology X) (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [HasDerivedCategory (ModuleCat.{u} Λ)]
variable [((sheafSections Y.smallEtaleTopology (ModuleCat.{u} Λ)).obj
    (op (globalEtale Y))).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((sheafSections Y.smallEtaleTopology (ModuleCat.{u} Λ)).obj
      (op (globalEtale Y))))
  (HomologicalComplex.quasiIso
    (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
variable [((sheafSections X.smallEtaleTopology (ModuleCat.{u} Λ)).obj
    (op (globalEtale X))).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((sheafSections X.smallEtaleTopology (ModuleCat.{u} Λ)).obj
      (op (globalEtale X))))
  (HomologicalComplex.quasiIso
    (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
variable [(etaleModulePushforward f Λ).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    (etaleModulePushforward f Λ ⋙
      (sheafSections Y.smallEtaleTopology (ModuleCat.{u} Λ)).obj
        (op (globalEtale Y))))
  (HomologicalComplex.quasiIso
    (Sheaf (smallEtaleTopology X) (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]

/-- The derived Leray comparison sends derived global sections on the domain
to derived global sections of the derived small-étale pushforward. -/
def etaleDerivedGammaPushforward :
    etaleDerivedGamma X Λ ⟶
      etaleDerivedPushforward f ⋙ etaleDerivedGamma Y Λ :=
  (RightDerived.natIsoOfIso
      (DerivedCategory.Q :
        CochainComplex (Sheaf (smallEtaleTopology X) (ModuleCat.{u} Λ)) ℤ ⥤
          DerivedCategory (Sheaf (smallEtaleTopology X) (ModuleCat.{u} Λ)))
      (HomologicalComplex.quasiIso
        (Sheaf (smallEtaleTopology X) (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ))
      (RightDerived.Cochain.unit
        ((sheafSections X.smallEtaleTopology (ModuleCat.{u} Λ)).obj
          (op (globalEtale X))))
      (RightDerived.Cochain.unit
        (etaleModulePushforward f Λ ⋙
          (sheafSections Y.smallEtaleTopology (ModuleCat.{u} Λ)).obj
            (op (globalEtale Y))))
      (Functor.isoWhiskerRight
        (NatIso.mapHomologicalComplex
          (etaleModuleGlobalSectionsPushforwardIso f) (ComplexShape.up ℤ))
        (DerivedCategory.Q :
          CochainComplex (ModuleCat.{u} Λ) ℤ ⥤
            DerivedCategory (ModuleCat.{u} Λ)))).hom ≫
    (RightDerived.Cochain.functor
        (etaleModulePushforward f Λ ⋙
          (sheafSections Y.smallEtaleTopology (ModuleCat.{u} Λ)).obj
            (op (globalEtale Y)))).rightDerivedDesc
      (RightDerived.Cochain.unit
        (etaleModulePushforward f Λ ⋙
          (sheafSections Y.smallEtaleTopology (ModuleCat.{u} Λ)).obj
            (op (globalEtale Y))))
      (HomologicalComplex.quasiIso
        (Sheaf (smallEtaleTopology X) (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ))
      (etaleDerivedPushforward f ⋙ etaleDerivedGamma Y Λ)
      ((Functor.isoWhiskerRight
        (mapHomologicalComplexCompIso
          (Iso.refl
            (etaleModulePushforward f Λ ⋙
              (sheafSections Y.smallEtaleTopology (ModuleCat.{u} Λ)).obj
                (op (globalEtale Y))))
          (ComplexShape.up ℤ)).symm
        (DerivedCategory.Q :
          CochainComplex (ModuleCat.{u} Λ) ℤ ⥤
            DerivedCategory (ModuleCat.{u} Λ)) ≪≫
      Functor.associator _ _ _).hom ≫
    RightDerived.Composition.iteratedUnit
      (RightDerived.Cochain.unit
        ((smallEtalePullback f).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) (smallEtaleTopology Y) (smallEtaleTopology X)))
      (RightDerived.Cochain.unit
        ((sheafSections Y.smallEtaleTopology (ModuleCat.{u} Λ)).obj
          (op (globalEtale Y)))))

/-- The derived global-sections Leray comparison along any scheme morphism is
an isomorphism. -/
instance etaleDerivedGammaPushforward_isIso :
    IsIso (etaleDerivedGammaPushforward f (Λ := Λ)) := sorry

end AlgebraicGeometry.Scheme.Etale

end
