/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.GroupTheory.Torsion
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.CompactSupport

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.GrothendieckTopology
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {Y : Scheme.{u}} (X : Over Y) {Λ : Type u} [CommRing Λ]
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

section CoproductComparison

variable {I : Type u} (K : I → DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)))
variable [HasCoproductsOfShape I (DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)))]
variable [HasCoproductsOfShape I (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))]

/-- Derived lower shriek along a separated finite-type morphism of quasi-compact,
quasi-separated schemes commutes with coproducts of uniformly bounded-below
families with torsion cohomology sheaves. -/
theorem etaleDerivedLowerShriek_preservesCoproduct
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    [HasSheafCompose X.left.smallEtaleTopology
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    (a : ℤ) (hK : ∀ i, DerivedCategory.IsGE (K i) a)
    (h_tors : ∀ i, etaleDerivedIsTorsion (K i)) :
    IsIso (CategoryTheory.Limits.sigmaComparison (etaleDerivedLowerShriek X P) K) := sorry

end CoproductComparison

/-- Derived lower shriek along a separated finite-type morphism of quasi-compact,
quasi-separated schemes preserves arbitrary discrete coproducts when the
coefficient ring is additively torsion. -/
theorem etaleDerivedLowerShriek_preservesCoproducts
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    (hΛ : AddMonoid.IsTorsion Λ) (I : Type u)
    [HasCoproductsOfShape I (DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)))]
    [HasCoproductsOfShape I (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))] :
    PreservesColimitsOfShape (Discrete I)
      (etaleDerivedLowerShriek X P :
        DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) := sorry

end AlgebraicGeometry.Scheme.Etale

end
