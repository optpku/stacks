module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.Naturality
public import ReasLib.CategoryTheory.Functor.Derived.Exact.Cochain
public import stacks_project.Chap63.Definition_63_12_1_LowerShriek
public import stacks_project.Chap63.Lemma_63_7_3_ExtensionByZero

/-!
# Exact derived lower shriek along a finite compactification

If the structure map of a compactification is finite, then `Rπ_* = π_*` on
derived categories of small-étale modules, so `Rf_! = Rπ_* ∘ j_!` agrees with
the exact functor `π_* ∘ j_!` of Section 63.7.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

section FinitePushforward

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (Λ : Type u) [CommRing Λ]
variable [IsFinite f]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [((smallEtalePullback f).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology X.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback f).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology X.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
variable [PreservesFiniteLimits
  ((smallEtalePullback f).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology X.smallEtaleTopology)]
variable [PreservesFiniteColimits
  ((smallEtalePullback f).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology X.smallEtaleTopology)]

/-- `Rf_*` is the cochain-level right derived functor of continuous small-étale
module pushforward. -/
instance etaleDerivedPushforward_isRightDerived :
    (etaleDerivedPushforward f).IsRightDerivedFunctor
      (RightDerived.Cochain.unit
        ((smallEtalePullback f).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Y.smallEtaleTopology X.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)) :=
  RightDerived.Cochain.isRightDerived
    ((smallEtalePullback f).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology X.smallEtaleTopology)

/-- For a finite morphism, derived small-étale pushforward `Rf_*` agrees with
the exact functor induced by underived `f_*`. -/
def etaleDerivedPushforward_mapDerivedCategoryIso :
    etaleDerivedPushforward f ≅
      ((smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Y.smallEtaleTopology X.smallEtaleTopology).mapDerivedCategory :=
  RightDerived.natIsoOfIso
    (DerivedCategory.Q :
      CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
        EtaleDerived X Λ)
    (HomologicalComplex.quasiIso
      (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))
    (RightDerived.Cochain.unit
      ((smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Y.smallEtaleTopology X.smallEtaleTopology))
    ((smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Y.smallEtaleTopology X.smallEtaleTopology).mapDerivedCategoryFactors.inv
    (Iso.refl
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback f).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Y.smallEtaleTopology X.smallEtaleTopology)))

/-- The forward map of `etaleDerivedPushforward_mapDerivedCategoryIso` is the
componentwise comparison `Rf_* ⟶ f_*`. -/
theorem etaleDerivedPushforward_mapDerivedCategoryIso_hom (K : EtaleDerived X Λ) :
    (etaleDerivedPushforward_mapDerivedCategoryIso f Λ).hom.app K =
      ((etaleDerivedPushforward_mapDerivedCategoryIso f Λ).app K).hom :=
  sorry

end FinitePushforward

variable {Y : Scheme.{u}} (X : Over Y) {Λ : Type u} [CommRing Λ]
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

/-- The exact derived lower shriek `f_!` of Section 63.7 along a finite
compactification, realized as `π_* ∘ j_!`. -/
def etaleDerivedExactLowerShriek :
    EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ :=
  etaleDerivedExtensionByZero (Compactification.Of.ι P) Λ ⋙
    ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      P.obj.right.left.smallEtaleTopology).mapDerivedCategory

/-- Evaluating the exact derived lower shriek applies extension by zero along
the interior immersion and then exact pushforward along the finite structure
map. -/
theorem etaleDerivedExactLowerShriek_obj (K : EtaleDerived X.left Λ) :
    (etaleDerivedExactLowerShriek X P).obj K =
      (((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Y.smallEtaleTopology
          P.obj.right.left.smallEtaleTopology).mapDerivedCategory).obj
        ((etaleDerivedExtensionByZero (Compactification.Of.ι P) Λ).obj K) :=
  sorry

/-- The exact derived lower shriek is the composite `j_! ⋙ π_*`. -/
theorem etaleDerivedExactLowerShriek_def :
    etaleDerivedExactLowerShriek X P =
      etaleDerivedExtensionByZero (Compactification.Of.ι P) Λ ⋙
        ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Y.smallEtaleTopology
          P.obj.right.left.smallEtaleTopology).mapDerivedCategory :=
  sorry

/-- The comparison isomorphism `Rf_! ≅ π_* ∘ j_!` obtained by whiskering the
finite pushforward identification `Rπ_* ≅ π_*` with extension by zero. -/
def etaleDerivedLowerShriekComparisonIso :
    (etaleDerivedLowerShriek X P :
        EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ) ≅
      etaleDerivedExactLowerShriek X P :=
  Functor.isoWhiskerLeft
    (etaleDerivedExtensionByZero (Compactification.Of.ι P) Λ)
    (RightDerived.natIsoOfIso
      (DerivedCategory.Q :
        CochainComplex
          (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
          EtaleDerived P.obj.right.left Λ)
      (HomologicalComplex.quasiIso
        (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ))
      (RightDerived.Cochain.unit
        ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Y.smallEtaleTopology
          P.obj.right.left.smallEtaleTopology))
      ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Y.smallEtaleTopology
          P.obj.right.left.smallEtaleTopology).mapDerivedCategoryFactors.inv
      (Iso.refl
        (RightDerived.Cochain.toDerived
          ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
            (ModuleCat.{u} Λ) Y.smallEtaleTopology
            P.obj.right.left.smallEtaleTopology))))

/-- The forward comparison `Rf_! ⟶ π_* ∘ j_!`. -/
def etaleDerivedLowerShriekComparison :
    (etaleDerivedLowerShriek X P :
        EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ) ⟶
      etaleDerivedExactLowerShriek X P :=
  (etaleDerivedLowerShriekComparisonIso X P).hom

/-- The compactification comparison `etaleDerivedLowerShriekComparison` is an
isomorphism. -/
instance etaleDerivedLowerShriekComparison_isIso :
    IsIso
      (etaleDerivedLowerShriekComparison X P :
        (etaleDerivedLowerShriek X P :
            EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ) ⟶
          etaleDerivedExactLowerShriek X P) :=
  Iso.isIso_hom (etaleDerivedLowerShriekComparisonIso X P)

/-- The forward map of `etaleDerivedLowerShriekComparisonIso` is the comparison
natural transformation. -/
theorem etaleDerivedLowerShriekComparisonIso_hom :
    (etaleDerivedLowerShriekComparisonIso X P).hom =
      (etaleDerivedLowerShriekComparison X P :
        (etaleDerivedLowerShriek X P :
            EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ) ⟶
          etaleDerivedExactLowerShriek X P) :=
  sorry

/-- The comparison at an object of `D(X_étale, Λ)`. -/
theorem etaleDerivedLowerShriekComparison_app (K : EtaleDerived X.left Λ) :
    (etaleDerivedLowerShriekComparison X P).app K =
      (etaleDerivedLowerShriekComparisonIso X P).hom.app K :=
  sorry

section OpenImmersion

variable [IsOpenImmersion X.hom]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction X.hom).op.HasLeftKanExtension F]
variable [(etaleExtensionByZero X.hom (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits (etaleExtensionByZero X.hom (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits (etaleExtensionByZero X.hom (ModuleCat.{u} Λ))]

/-- If `X.hom` is an open immersion, then `Rf_!` is isomorphic to extension by
zero. -/
theorem etaleDerivedLowerShriek_isIsomorphic_extensionByZero :
    IsIsomorphic (etaleDerivedLowerShriek X P)
      (etaleDerivedExtensionByZero X.hom Λ) :=
  sorry

end OpenImmersion

end AlgebraicGeometry.Scheme.Etale

end
