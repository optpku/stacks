/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InternalHom.Scalar
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.InternalHom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.StructureSheaf
public import Mathlib.Algebra.Homology.Single

/-! # The scalar homothety of a derived module -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.InternalHom

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The scalar multiples of the components of a cochain map form a degree-zero
element of the sheaf Hom complex. -/
def mapComplexZero {F I : CochainComplex (Modules X) ℤ} (φ : F ⟶ I) :
    𝟙_ (Modules X) ⟶ gradedObj F I 0 :=
  Pi.lift fun i => Modules.InternalHom.scalarMap
    (φ.f i ≫ eqToHom (congrArg I.X (Int.add_zero i).symm))

/-- Scalar multiples of a cochain map are closed under every outgoing differential
from degree zero in the sheaf Hom complex. -/
theorem mapComplex_closed {F I : CochainComplex (Modules X) ℤ} (φ : F ⟶ I)
    (k : ℤ) (hk : (ComplexShape.up ℤ).Rel 0 k) :
    mapComplexZero φ ≫ (complex F I).d 0 k = 0 := sorry

/-- A cochain map induces a cochain map from the structure module placed in degree
zero to the sheaf Hom complex by scalar multiplication. -/
def mapComplex {F I : CochainComplex (Modules X) ℤ} (φ : F ⟶ I) :
    (HomologicalComplex.single (Modules X) (ComplexShape.up ℤ) 0).obj
      (𝟙_ (Modules X)) ⟶ complex F I :=
  HomologicalComplex.mkHomFromSingle (mapComplexZero φ) (mapComplex_closed φ)

/-- The canonical scalar homothety into the derived endomorphism object is obtained
by localizing scalar multiplication of the K-injective augmentation. -/
def homothety (E : ModuleDerived X) :
    (DerivedQCoh.structureSheaf X).obj ⟶ obj E E :=
  DerivedCategory.Q.map (mapComplex
    ((CochainComplex.KInjectiveResolution.Construction.augmentation.{u}
      (Modules X)).app (DerivedCategory.Q.objPreimage E)))

/-- The scalar homothety is the localization of the cochain map defined by the
specified K-injective augmentation of the chosen representative. -/
theorem homothety_model (E : ModuleDerived X) :
    homothety E = DerivedCategory.Q.map (mapComplex
      ((CochainComplex.KInjectiveResolution.Construction.augmentation.{u}
        (Modules X)).app (DerivedCategory.Q.objPreimage E))) := rfl

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.InternalHom
