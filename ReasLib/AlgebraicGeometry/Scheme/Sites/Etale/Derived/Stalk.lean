/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.Coefficients
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint

/-!
# Derived geometric stalks
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.Functor.RightDerived
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint
open AlgebraicGeometry.Scheme.Hom
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {Y : Scheme.{u}} (ybar : GeometricPoint Y)

section GammaStalk

variable {Λ : Type u} [CommRing Λ]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify (Spec (CommRingCat.of ybar.K)).smallEtaleTopology
  (ModuleCat.{u} Λ)]
variable [HasWeakSheafify (Spec (CommRingCat.of ybar.K)).smallEtaleTopology
  (ModuleCat.{u} Λ)]
variable [∀ U : (Spec (CommRingCat.of ybar.K)).Etale,
  HasWeakSheafify ((Spec (CommRingCat.of ybar.K)).smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf (Spec (CommRingCat.of ybar.K)).smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback ybar.hom).op.HasLeftKanExtension F]
variable [HasDerivedCategory (ModuleCat.{u} Λ)]
variable [((sheafSections (Spec (CommRingCat.of ybar.K)).smallEtaleTopology
    (ModuleCat.{u} Λ)).obj
    (op (globalEtale (Spec (CommRingCat.of ybar.K))))).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((sheafSections (Spec (CommRingCat.of ybar.K)).smallEtaleTopology
        (ModuleCat.{u} Λ)).obj
      (op (globalEtale (Spec (CommRingCat.of ybar.K))))))
  (HomologicalComplex.quasiIso
    (Sheaf (Spec (CommRingCat.of ybar.K)).smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]

/-- Geometric stalk `(K)_ȳ` in `D(Λ)`, read as `RΓ(Spec k, ȳ⁻¹ K)`. -/
def etaleDerivedGammaStalk (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) :
    DerivedCategory (ModuleCat.{u} Λ) :=
  (etaleDerivedGamma (Spec (CommRingCat.of ybar.K)) Λ).obj
    ((etaleModuleDerivedInverseImage ybar.hom Λ).obj K)

/-- The geometric stalk is derived global sections of the inverse image along
`ȳ`. -/
theorem etaleDerivedGammaStalk_eq (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) :
    etaleDerivedGammaStalk ybar K =
      (etaleDerivedGamma (Spec (CommRingCat.of ybar.K)) Λ).obj
        ((etaleModuleDerivedInverseImage ybar.hom Λ).obj K) :=
  sorry

end GammaStalk

end AlgebraicGeometry.Scheme.Etale

end
