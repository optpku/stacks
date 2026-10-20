/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.UpperShriek
public import Mathlib.CategoryTheory.Adjunction.Basic
public import stacks_project.Chap63.Definition_63_12_1_LowerShriek

/-!
# Derived upper shriek for étale torsion coefficients

The functor `Rf^!` is the chosen right adjoint of the compactification
presentation `Rf_! = etaleDerivedLowerShriek`. The chosen adjoint requires
formal availability of the lower-shriek adjunction.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {Y : Scheme.{u}} (X : Over Y) (Λ : Type u) [CommRing Λ]
variable [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
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
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable [((etaleDerivedLowerShriek X P :
    EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ)).IsLeftAdjoint]

#check (AlgebraicGeometry.Scheme.Etale.etaleDerivedUpperShriek X Λ P : EtaleDerived Y Λ ⥤ EtaleDerived X.left Λ)

#check (AlgebraicGeometry.Scheme.Etale.etaleDerivedUpperShriek_def X Λ P :
    etaleDerivedUpperShriek X Λ P = (etaleDerivedLowerShriek X P).rightAdjoint)

#check (AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriekAdjunction X Λ P :
    etaleDerivedLowerShriek X P ⊣ etaleDerivedUpperShriek X Λ P)

#check (AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriekAdjunction_homEquiv X Λ P :
  ∀ (L : EtaleDerived X.left Λ) (K : EtaleDerived Y Λ),
    ((etaleDerivedLowerShriek X P).obj L ⟶ K) ≃
      (L ⟶ (etaleDerivedUpperShriek X Λ P).obj K))

end AlgebraicGeometry.Scheme.Etale

end
