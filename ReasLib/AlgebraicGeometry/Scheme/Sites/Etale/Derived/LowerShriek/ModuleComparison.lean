module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.ModuleCompactification
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LowerShriek.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LocallyQuasiFinite
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

section GeneralComparison

variable {Y : Scheme.{u}} (X : Over Y) (Λ : Type u) [CommRing Λ]
variable [IsSeparated X.hom] [Scheme.Hom.QuasiFinite X.hom]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (P : Compactification.Of Y X)
variable [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : P.obj.right.left.Etale,
  HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [(etaleExtensionByZero (Compactification.Of.ι P)
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    P.obj.right.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      P.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [X.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [P.obj.right.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [Y.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [P.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Compactification.Of.ι P)).op]
variable [IsGrothendieckAbelian (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
/-- The cochain comparison from exact compact-support direct image to compactification-derived lower shriek. -/
def etaleDerivedLowerShriekModuleComparison_cochain :
    (DerivedCategory.Q :
      CochainComplex (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
        DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) ⋙ lowerShriekModuleDerived X.hom Λ ⟶
      (DerivedCategory.Q :
      CochainComplex (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
        DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) ⋙ etaleDerivedLowerShriek X P :=
  let j := etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ)
  let p := (smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology P.obj.right.left.smallEtaleTopology
  let QY := (DerivedCategory.Q :
    CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))
  (lowerShriekModule X.hom Λ).mapDerivedCategoryFactors.hom ≫
    whiskerRight (Functor.mapHomologicalComplexCompIso
      (etaleModuleLowerShriekCompactifyPushforwardIso X Λ P) (ComplexShape.up ℤ)).inv QY ≫
    (Functor.associator (j.mapHomologicalComplex (ComplexShape.up ℤ))
      (p.mapHomologicalComplex (ComplexShape.up ℤ)) QY).hom ≫
    whiskerLeft (j.mapHomologicalComplex (ComplexShape.up ℤ))
      (RightDerived.Cochain.unit p) ≫
    (Functor.associator _ _ _).inv ≫
    whiskerRight j.mapDerivedCategoryFactors.inv (etaleDerivedPushforward P.obj.right.hom) ≫
    (Functor.associator _ _ _).hom

/-- The canonical transformation from exact compact-support direct image to compactification-derived lower shriek. -/
def etaleDerivedLowerShriekModuleComparison :
    lowerShriekModuleDerived X.hom Λ ⟶ etaleDerivedLowerShriek X P :=
  (Localization.fullyFaithfulWhiskeringLeft
    (DerivedCategory.Q :
      CochainComplex (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
        DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)))
    (HomologicalComplex.quasiIso
      (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))
    (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))).preimage
      (etaleDerivedLowerShriekModuleComparison_cochain X Λ P)

/-- On cochain complexes, the descended lower-shriek comparison is the explicit cochain transformation. -/
theorem etaleDerivedLowerShriekModuleComparison_Q :
    whiskerLeft (DerivedCategory.Q :
      CochainComplex (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
        DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)))
      (etaleDerivedLowerShriekModuleComparison X Λ P) =
      etaleDerivedLowerShriekModuleComparison_cochain X Λ P := sorry

/-- For torsion coefficients, the canonical derived lower-shriek comparison is invertible. -/
instance etaleDerivedLowerShriekModuleComparison_isIso [Fact (AddMonoid.IsTorsion Λ)] :
    IsIso (etaleDerivedLowerShriekModuleComparison X Λ P) := sorry

end GeneralComparison

section FiniteComparison

variable {Y : Scheme.{u}} (X : Over Y) (Λ : Type u) [CommRing Λ]
variable [IsSeparated X.hom] [Scheme.Hom.QuasiFinite X.hom]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (P : Compactification.Of Y X)
variable [IsFinite P.obj.right.hom]
variable [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : P.obj.right.left.Etale,
  HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [(etaleExtensionByZero (Compactification.Of.ι P)
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    P.obj.right.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      P.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [PreservesFiniteLimits
  ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    P.obj.right.left.smallEtaleTopology)]
variable [PreservesFiniteColimits
  ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    P.obj.right.left.smallEtaleTopology)]
variable [X.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [P.obj.right.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [Y.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [P.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Compactification.Of.ι P)).op]
variable [IsGrothendieckAbelian (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
/-- Exact pushforward after extension by zero induces derived compact-support direct image. -/
def etaleDerivedExactLowerShriekIsoModuleDerived :
    etaleDerivedExactLowerShriek X P ≅ lowerShriekModuleDerived X.hom Λ :=
  (ExactFunctor.MapDerivedCategory.compFunctorIso
      (ExactFunctor.of
        (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ)))
      (ExactFunctor.of
        ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Y.smallEtaleTopology
          P.obj.right.left.smallEtaleTopology))).symm ≪≫
    Functor.MapDerivedCategory.functorIso
      (etaleModuleLowerShriekCompactifyPushforwardIso X Λ P)

/-- For a finite compactification, derived lower shriek agrees with exact compact-support direct image. -/
def etaleDerivedLowerShriekIsoModuleDerived :
    (etaleDerivedLowerShriek X P :
        DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) ≅
      lowerShriekModuleDerived X.hom Λ :=
  etaleDerivedLowerShriekIso X P ≪≫
    etaleDerivedExactLowerShriekIsoModuleDerived X Λ P


end FiniteComparison

end AlgebraicGeometry.Scheme.Etale

end
