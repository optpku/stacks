module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.CompactSupport
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ExtensionByZero
public import ReasLib.CategoryTheory.Functor.Derived.Exact.Cochain
public import ReasLib.CategoryTheory.Functor.Derived.Composition.Right
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.Naturality
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open RightDerived.Cochain
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {Λ : Type u} [CommRing Λ]

variable {Y : Scheme.{u}} (X : Over Y)
  [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace X.left] [QuasiSeparatedSpace X.left]
  (P : Compactification.Of Y X)
variable [HasSheafify (smallEtaleTopology X.left) (ModuleCat.{u} Λ)]
  [∀ U : X.left.Etale,
  HasWeakSheafify ((smallEtaleTopology X.left).over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))]
  [HasSheafify (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)]
  [∀ U : (Over.left P.obj.right).Etale,
  HasWeakSheafify ((smallEtaleTopology (Over.left P.obj.right)).over U)
    (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ))]
  [HasSheafify (smallEtaleTopology Y) (ModuleCat.{u} Λ)]
  [∀ U : Y.Etale,
  HasWeakSheafify ((smallEtaleTopology Y).over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ))]
  [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [(etaleExtensionByZero (Compactification.Of.ι P)
    (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
  [(etaleModulePushforward (Over.hom P.obj.right) Λ).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback (Over.hom P.obj.right)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) (smallEtaleTopology Y)
      (smallEtaleTopology (Over.left P.obj.right))))
  (HomologicalComplex.quasiIso
    (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [(etaleModulePushforward X.hom Λ).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback X.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) (smallEtaleTopology Y) (smallEtaleTopology X.left)))
  (HomologicalComplex.quasiIso
    (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [(etaleRestrictionSheaf (Compactification.Of.ι P)
    (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits
  (etaleRestrictionSheaf (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits
  (etaleRestrictionSheaf (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [(etaleModulePushforward (Compactification.Of.ι P) Λ).Additive]
  [PreservesFiniteLimits
  (((smallEtalePullback (Compactification.Of.ι P)).sheafPushforwardContinuous (ModuleCat.{u} Λ) (smallEtaleTopology (Over.left P.obj.right)) (smallEtaleTopology X.left)))]
  [(etaleModulePushforward
    (Compactification.Of.ι P ≫ Over.hom P.obj.right) Λ).Additive]
variable [(((smallEtalePullback (Compactification.Of.ι P)).sheafPushforwardContinuous (ModuleCat.{u} Λ) (smallEtaleTopology (Over.left P.obj.right)) (smallEtaleTopology X.left)) ⋙
    ((smallEtalePullback (Over.hom P.obj.right)).sheafPushforwardContinuous (ModuleCat.{u} Λ) (smallEtaleTopology Y) (smallEtaleTopology (Over.left P.obj.right)))).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    (((smallEtalePullback (Compactification.Of.ι P)).sheafPushforwardContinuous (ModuleCat.{u} Λ) (smallEtaleTopology (Over.left P.obj.right)) (smallEtaleTopology X.left)) ⋙
      ((smallEtalePullback (Over.hom P.obj.right)).sheafPushforwardContinuous (ModuleCat.{u} Λ) (smallEtaleTopology Y) (smallEtaleTopology (Over.left P.obj.right)))))
  (HomologicalComplex.quasiIso
    (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
/-- Site-level adjunction `etaleRestriction ⊣ smallEtalePullback` along the
compactification interior. -/
def etaleInteriorSiteAdjunction :
    etaleRestriction (Compactification.Of.ι P) ⊣
      smallEtalePullback (Compactification.Of.ι P) :=
  MorphismProperty.Over.mapPullbackAdj @Etale ⊤
    (Compactification.Of.ι P) inferInstance trivial

/-- Sheaf-level adjunction `j⁻¹ ⊣ j_*` of `Λ`-modules along the interior
immersion. -/
def etaleInteriorSheafPushforwardAdjunction :
    etaleRestrictionSheaf (Compactification.Of.ι P) (ModuleCat.{u} Λ) ⊣
      ((smallEtalePullback (Compactification.Of.ι P)).sheafPushforwardContinuous (ModuleCat.{u} Λ) (smallEtaleTopology (Over.left P.obj.right)) (smallEtaleTopology X.left)) :=
  Adjunction.sheafPushforwardContinuous (etaleInteriorSiteAdjunction X P)
    (smallEtaleTopology X.left) (smallEtaleTopology (Over.left P.obj.right))

variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    (((smallEtalePullback (Compactification.Of.ι P)).sheafPushforwardContinuous (ModuleCat.{u} Λ) (smallEtaleTopology (Over.left P.obj.right)) (smallEtaleTopology X.left))))
  (HomologicalComplex.quasiIso
    (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]

/-- Derived interior pushforward `Rj_*` along the compactification immersion. -/
abbrev etaleDerivedInteriorPushforward :
    DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)) :=
  etaleDerivedPushforward (Compactification.Of.ι P) (Λ := Λ)

/-- The named interior pushforward retains its canonical right-derived universal property. -/
instance etaleDerivedInteriorPushforward_rightDerived :
    (etaleDerivedInteriorPushforward X P).IsRightDerivedFunctor
      (RightDerived.Cochain.unit (((smallEtalePullback (Compactification.Of.ι P)).sheafPushforwardContinuous (ModuleCat.{u} Λ) (smallEtaleTopology (Over.left P.obj.right)) (smallEtaleTopology X.left))))
      (HomologicalComplex.quasiIso
        (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)) :=
  RightDerived.Cochain.isRightDerived (((smallEtalePullback (Compactification.Of.ι P)).sheafPushforwardContinuous (ModuleCat.{u} Λ) (smallEtaleTopology (Over.left P.obj.right)) (smallEtaleTopology X.left)))

/-- The compactification direct image retains its canonical right-derived universal property. -/
instance etaleDerivedCompactificationPushforward_rightDerived :
    (etaleDerivedPushforward (Over.hom P.obj.right) (Λ := Λ)).IsRightDerivedFunctor
      (RightDerived.Cochain.unit (((smallEtalePullback (Over.hom P.obj.right)).sheafPushforwardContinuous (ModuleCat.{u} Λ) (smallEtaleTopology Y) (smallEtaleTopology (Over.left P.obj.right)))))
      (HomologicalComplex.quasiIso
        (Sheaf (Over.left P.obj.right).smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) :=
  RightDerived.Cochain.isRightDerived (((smallEtalePullback (Over.hom P.obj.right)).sheafPushforwardContinuous (ModuleCat.{u} Λ) (smallEtaleTopology Y) (smallEtaleTopology (Over.left P.obj.right))))

/-- The derived unit for the composite of exact restriction and `Rj_*` remains left derived. -/
instance etaleInterior_leftRightDerived :
    (etaleDerivedRestriction (Compactification.Of.ι P) Λ ⋙
      etaleDerivedInteriorPushforward X P).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight
        (etaleRestrictionSheaf (Compactification.Of.ι P)
          (ModuleCat.{u} Λ)).mapDerivedCategoryFactors.hom
        (etaleDerivedInteriorPushforward X P))
      (HomologicalComplex.quasiIso
        (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) := sorry

/-- Exact restriction preserves the absolute right-derived model of interior pushforward. -/
instance etaleInterior_rightLeftDerived :
    (etaleDerivedInteriorPushforward X P ⋙
      etaleDerivedRestriction (Compactification.Of.ι P) Λ).IsRightDerivedFunctor
      (Functor.whiskerRight
        (RightDerived.Cochain.unit
          (((smallEtalePullback (Compactification.Of.ι P)).sheafPushforwardContinuous (ModuleCat.{u} Λ) (smallEtaleTopology (Over.left P.obj.right)) (smallEtaleTopology X.left))))
        (etaleDerivedRestriction (Compactification.Of.ι P) Λ) ≫
        (Functor.associator _ _ _).hom)
      (HomologicalComplex.quasiIso
        (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)) := sorry

/-- The adjunction `j⁻¹ ⊣ Rj_*` on unbounded derived categories. -/
def etaleDerivedInteriorPushforwardAdjunction :
    etaleDerivedRestriction (Compactification.Of.ι P) Λ ⊣
      etaleDerivedInteriorPushforward X P :=
  @Adjunction.derived _ _ _ _ _ _ _ _ _ _
    (Adjunction.mapHomologicalComplexAdjunction
      (etaleInteriorSheafPushforwardAdjunction X P) (ComplexShape.up ℤ)) _ _
    (HomologicalComplex.quasiIso
      (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ))
      (ComplexShape.up ℤ))
    (HomologicalComplex.quasiIso
      (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))
    _ _ _ _
    (etaleRestrictionSheaf (Compactification.Of.ι P)
      (ModuleCat.{u} Λ)).mapDerivedCategoryFactors.hom
    (RightDerived.Cochain.unit
      (((smallEtalePullback (Compactification.Of.ι P)).sheafPushforwardContinuous (ModuleCat.{u} Λ) (smallEtaleTopology (Over.left P.obj.right)) (smallEtaleTopology X.left))))
    inferInstance (etaleDerivedInteriorPushforward_rightDerived X P)
    (etaleInterior_leftRightDerived X P) (etaleInterior_rightLeftDerived X P)

variable [(etaleModulePushforward (Over.hom P.obj.right) Λ).IsRightAdjoint]
  [(etaleModuleInverseImage (Over.hom P.obj.right) (Λ := Λ)).Additive]
  [PreservesFiniteLimits (etaleModuleInverseImage (Over.hom P.obj.right) (Λ := Λ))]
  [PreservesFiniteColimits (etaleModuleInverseImage (Over.hom P.obj.right) (Λ := Λ))]

/-- The left composite for the compactification inverse-image/direct-image derived adjunction. -/
instance etaleCompactification_leftRightDerived :
    ((etaleModuleInverseImage (Over.hom P.obj.right) (Λ := Λ)).mapDerivedCategory ⋙
      etaleDerivedPushforward (Over.hom P.obj.right)).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight
        (etaleModuleInverseImage (Over.hom P.obj.right) (Λ := Λ)).mapDerivedCategoryFactors.hom
        (etaleDerivedPushforward (Over.hom P.obj.right)))
      (HomologicalComplex.quasiIso
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)) := sorry

/-- The right composite for the compactification inverse-image/direct-image derived adjunction. -/
instance etaleCompactification_rightLeftDerived :
    (etaleDerivedPushforward (Over.hom P.obj.right) ⋙
      (etaleModuleInverseImage (Over.hom P.obj.right) (Λ := Λ)).mapDerivedCategory).IsRightDerivedFunctor
      (Functor.whiskerRight
        (RightDerived.Cochain.unit (((smallEtalePullback (Over.hom P.obj.right)).sheafPushforwardContinuous (ModuleCat.{u} Λ) (smallEtaleTopology Y) (smallEtaleTopology (Over.left P.obj.right)))))
        (etaleModuleInverseImage (Over.hom P.obj.right) (Λ := Λ)).mapDerivedCategory ≫
        (Functor.associator _ _ _).hom)
      (HomologicalComplex.quasiIso
        (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) := sorry

/-- The genuine derived inverse-image/direct-image adjunction for the compactification map. -/
def etaleDerivedCompactificationPushforwardAdjunction :
    (etaleModuleInverseImage (Over.hom P.obj.right) (Λ := Λ)).mapDerivedCategory ⊣
      etaleDerivedPushforward (Over.hom P.obj.right) :=
  @Adjunction.derived _ _ _ _ _ _ _ _ _ _
    (Adjunction.mapHomologicalComplexAdjunction
      (etaleModuleInverseImageAdjunction (Over.hom P.obj.right) (Λ := Λ))
      (ComplexShape.up ℤ)) _ _
    (HomologicalComplex.quasiIso
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))
    (HomologicalComplex.quasiIso
      (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ))
      (ComplexShape.up ℤ))
    _ _ _ _
    (etaleModuleInverseImage (Over.hom P.obj.right) (Λ := Λ)).mapDerivedCategoryFactors.hom
    (RightDerived.Cochain.unit (((smallEtalePullback (Over.hom P.obj.right)).sheafPushforwardContinuous (ModuleCat.{u} Λ) (smallEtaleTopology Y) (smallEtaleTopology (Over.left P.obj.right)))))
    inferInstance (etaleDerivedCompactificationPushforward_rightDerived X P)
    (etaleCompactification_leftRightDerived X P) (etaleCompactification_rightLeftDerived X P)

/-- Underived Leray identification `f_* ≅ f̄_* ∘ j_*` along the
compactification triangle. -/
def etaleModulePushforwardLerayIso :
    ((smallEtalePullback X.hom).sheafPushforwardContinuous (ModuleCat.{u} Λ) (smallEtaleTopology Y) (smallEtaleTopology X.left)) ≅
      ((smallEtalePullback (Compactification.Of.ι P)).sheafPushforwardContinuous (ModuleCat.{u} Λ) (smallEtaleTopology (Over.left P.obj.right)) (smallEtaleTopology X.left)) ⋙
        ((smallEtalePullback (Over.hom P.obj.right)).sheafPushforwardContinuous (ModuleCat.{u} Λ) (smallEtaleTopology Y) (smallEtaleTopology (Over.left P.obj.right))) :=
  etaleModulePushforwardCongr (Over.w P.obj.hom).symm ≪≫
    (etaleModulePushforwardCompIso (Compactification.Of.ι P)
      (Over.hom P.obj.right)).symm

/-- The cochain pushforward of a composite agrees with the iterated cochain pushforward. -/
def etaleModulePushforwardCompCochainIso :
    RightDerived.Cochain.toDerived
        (((smallEtalePullback (Compactification.Of.ι P)).sheafPushforwardContinuous (ModuleCat.{u} Λ) (smallEtaleTopology (Over.left P.obj.right)) (smallEtaleTopology X.left)) ⋙
          ((smallEtalePullback (Over.hom P.obj.right)).sheafPushforwardContinuous (ModuleCat.{u} Λ) (smallEtaleTopology Y) (smallEtaleTopology (Over.left P.obj.right)))) ≅
      (((smallEtalePullback (Compactification.Of.ι P)).sheafPushforwardContinuous (ModuleCat.{u} Λ) (smallEtaleTopology (Over.left P.obj.right)) (smallEtaleTopology X.left))).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        RightDerived.Cochain.toDerived (((smallEtalePullback (Over.hom P.obj.right)).sheafPushforwardContinuous (ModuleCat.{u} Λ) (smallEtaleTopology Y) (smallEtaleTopology (Over.left P.obj.right)))) :=
  Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (((smallEtalePullback (Compactification.Of.ι P)).sheafPushforwardContinuous (ModuleCat.{u} Λ) (smallEtaleTopology (Over.left P.obj.right)) (smallEtaleTopology X.left)) ⋙
          ((smallEtalePullback (Over.hom P.obj.right)).sheafPushforwardContinuous (ModuleCat.{u} Λ) (smallEtaleTopology Y) (smallEtaleTopology (Over.left P.obj.right))))) (ComplexShape.up ℤ)).symm
      DerivedCategory.Q ≪≫
    Functor.associator _ _ _

/-- Transporting the source of the composite's derived unit preserves its universal property. -/
instance etaleModulePushforwardCompRightDerived :
    (RightDerived.Cochain.functor
      (((smallEtalePullback (Compactification.Of.ι P)).sheafPushforwardContinuous (ModuleCat.{u} Λ) (smallEtaleTopology (Over.left P.obj.right)) (smallEtaleTopology X.left)) ⋙
        ((smallEtalePullback (Over.hom P.obj.right)).sheafPushforwardContinuous (ModuleCat.{u} Λ) (smallEtaleTopology Y) (smallEtaleTopology (Over.left P.obj.right))))).IsRightDerivedFunctor
      ((etaleModulePushforwardCompCochainIso X P).inv ≫
        RightDerived.Cochain.unit
          (((smallEtalePullback (Compactification.Of.ι P)).sheafPushforwardContinuous (ModuleCat.{u} Λ) (smallEtaleTopology (Over.left P.obj.right)) (smallEtaleTopology X.left)) ⋙
            ((smallEtalePullback (Over.hom P.obj.right)).sheafPushforwardContinuous (ModuleCat.{u} Λ) (smallEtaleTopology Y) (smallEtaleTopology (Over.left P.obj.right)))))
      (HomologicalComplex.quasiIso
        (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)) := sorry

/-- Leray comparison identifying `Rf_*` with `R f̄_* ∘ Rj_*` along the
compactification factorization `X.hom = j ≫ f̄`. -/
def etaleDerivedPushforwardLeray :
    (etaleDerivedPushforward X.hom :
        DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ))) ⟶
      etaleDerivedInteriorPushforward X P ⋙
        (etaleDerivedPushforward (Over.hom P.obj.right) :
          DerivedCategory (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ))) :=
  (RightDerived.natIsoOfIso
      (DerivedCategory.Q :
        CochainComplex (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)) ℤ ⥤
          DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)))
      (HomologicalComplex.quasiIso
        (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ))
      (RightDerived.Cochain.unit (((smallEtalePullback X.hom).sheafPushforwardContinuous (ModuleCat.{u} Λ) (smallEtaleTopology Y) (smallEtaleTopology X.left))))
      (RightDerived.Cochain.unit
        (((smallEtalePullback (Compactification.Of.ι P)).sheafPushforwardContinuous (ModuleCat.{u} Λ) (smallEtaleTopology (Over.left P.obj.right)) (smallEtaleTopology X.left)) ⋙
          ((smallEtalePullback (Over.hom P.obj.right)).sheafPushforwardContinuous (ModuleCat.{u} Λ) (smallEtaleTopology Y) (smallEtaleTopology (Over.left P.obj.right)))))
      (Functor.isoWhiskerRight
        (NatIso.mapHomologicalComplex
          (etaleModulePushforwardLerayIso X P) (ComplexShape.up ℤ))
        (DerivedCategory.Q :
          CochainComplex (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)) ℤ ⥤
            DerivedCategory (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ))))).hom ≫
    RightDerived.Composition.comparisonOfModels
      (F := (((smallEtalePullback (Compactification.Of.ι P)).sheafPushforwardContinuous (ModuleCat.{u} Λ) (smallEtaleTopology (Over.left P.obj.right)) (smallEtaleTopology X.left))).mapHomologicalComplex
        (ComplexShape.up ℤ))
      (HomologicalComplex.quasiIso
        (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))
      (RightDerived.Cochain.unit
        (((smallEtalePullback (Compactification.Of.ι P)).sheafPushforwardContinuous (ModuleCat.{u} Λ) (smallEtaleTopology (Over.left P.obj.right)) (smallEtaleTopology X.left))))
      (RightDerived.Cochain.unit
        (((smallEtalePullback (Over.hom P.obj.right)).sheafPushforwardContinuous (ModuleCat.{u} Λ) (smallEtaleTopology Y) (smallEtaleTopology (Over.left P.obj.right)))))
      ((etaleModulePushforwardCompCochainIso X P).inv ≫
        RightDerived.Cochain.unit
          (((smallEtalePullback (Compactification.Of.ι P)).sheafPushforwardContinuous (ModuleCat.{u} Λ) (smallEtaleTopology (Over.left P.obj.right)) (smallEtaleTopology X.left)) ⋙
            ((smallEtalePullback (Over.hom P.obj.right)).sheafPushforwardContinuous (ModuleCat.{u} Λ) (smallEtaleTopology Y) (smallEtaleTopology (Over.left P.obj.right)))))

/-- Leray identifies the derived pushforward of the composite with iterated derived pushforward. -/
instance etaleDerivedPushforwardLeray_isIso : IsIso (etaleDerivedPushforwardLeray X P (Λ := Λ)) := sorry


end AlgebraicGeometry.Scheme.Etale

end
