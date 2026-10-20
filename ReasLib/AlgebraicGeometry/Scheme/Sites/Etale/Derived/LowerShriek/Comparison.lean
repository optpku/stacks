/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.Naturality
public import ReasLib.CategoryTheory.Functor.Derived.Exact.Cochain
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.CompactSupport
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LowerShriek
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ExtensionByZero

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

section FiniteComparison

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
        DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)))
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

/-- The composite of derived extension by zero and exact pushforward along a finite compactification. -/
def etaleDerivedExactLowerShriek :
    DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) :=
  etaleDerivedExtensionByZero (Compactification.Of.ι P) Λ ⋙
    ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      P.obj.right.left.smallEtaleTopology).mapDerivedCategory

/-- Evaluating the exact derived lower shriek applies extension by zero along
the interior immersion and then exact pushforward along the finite structure
map. -/
theorem etaleDerivedExactLowerShriek_obj (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) :
    (etaleDerivedExactLowerShriek X P).obj K =
      (((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Y.smallEtaleTopology
          P.obj.right.left.smallEtaleTopology).mapDerivedCategory).obj
        ((etaleDerivedExtensionByZero (Compactification.Of.ι P) Λ).obj K) :=
  rfl

/-- The exact derived lower shriek is the composite `j_! ⋙ π_*`. -/
theorem etaleDerivedExactLowerShriek_def :
    etaleDerivedExactLowerShriek X P =
      etaleDerivedExtensionByZero (Compactification.Of.ι P) Λ ⋙
        ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Y.smallEtaleTopology
          P.obj.right.left.smallEtaleTopology).mapDerivedCategory :=
  rfl

/-- The comparison isomorphism `Rf_! ≅ π_* ∘ j_!` obtained by whiskering the
finite pushforward identification `Rπ_* ≅ π_*` with extension by zero. -/
def etaleDerivedLowerShriekIso :
    (etaleDerivedLowerShriek X P :
        DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) ≅
      etaleDerivedExactLowerShriek X P :=
  Functor.isoWhiskerLeft
    (etaleDerivedExtensionByZero (Compactification.Of.ι P) Λ)
    (RightDerived.natIsoOfIso
      (DerivedCategory.Q :
        CochainComplex
          (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
          DerivedCategory (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)))
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
        DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) ⟶
      etaleDerivedExactLowerShriek X P :=
  (etaleDerivedLowerShriekIso X P).hom

/-- The compactification comparison `etaleDerivedLowerShriekComparison` is an
isomorphism. -/
instance etaleDerivedLowerShriekComparison_isIso :
    IsIso
      (etaleDerivedLowerShriekComparison X P :
        (etaleDerivedLowerShriek X P :
            DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) ⟶
          etaleDerivedExactLowerShriek X P) :=
  Iso.isIso_hom (etaleDerivedLowerShriekIso X P)

/-- The forward map of `etaleDerivedLowerShriekIso` is the comparison
natural transformation. -/
theorem etaleDerivedLowerShriekIso_hom :
    (etaleDerivedLowerShriekIso X P).hom =
      (etaleDerivedLowerShriekComparison X P :
        (etaleDerivedLowerShriek X P :
            DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) ⟶
          etaleDerivedExactLowerShriek X P) :=
  rfl

/-- The comparison at an object of `D(X_étale, Λ)`. -/
theorem etaleDerivedLowerShriekComparison_app (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) :
    (etaleDerivedLowerShriekComparison X P).app K =
      (etaleDerivedLowerShriekIso X P).hom.app K :=
  rfl

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

end FiniteComparison

section Agreement

variable {Y : Scheme.{u}} (X : Over Y) {Λ : Type u} [Ring Λ]
variable [IsSeparated X.hom] [Scheme.Hom.QuasiFinite X.hom]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
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

/-- Compactification-derived lower shriek agrees with exact proper-support direct image
on the admissible domain, and on the entire derived category for torsion coefficient rings. -/
theorem etaleDerivedLowerShriek_agrees [CompactSpace X.left] [QuasiSeparatedSpace X.left] :
    IsIsomorphic
      ((Derived.compactSupportAdmissible X.left Λ).ι ⋙ etaleDerivedLowerShriek X P)
      ((Derived.compactSupportAdmissible X.left Λ).ι ⋙ etaleExactLowerShriek X.hom Λ) ∧
    (AddMonoid.IsTorsion Λ →
      IsIsomorphic (etaleDerivedLowerShriek X P) (etaleExactLowerShriek X.hom Λ)) := sorry

end Agreement

end AlgebraicGeometry.Scheme.Etale

end
