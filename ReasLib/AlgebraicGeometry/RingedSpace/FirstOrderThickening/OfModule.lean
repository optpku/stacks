/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Trivialization
public import ReasLib.AlgebraicGeometry.RingedSpace.SquareZeroExtension

/-!
# Square-zero first-order thickenings associated to modules

An `𝒪_X`-module determines a first-order thickening whose structure sheaf is
the square-zero extension by that module.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.RingedSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.IsFirstOrderThickening

/-- The ringed space with the same underlying space as `X` and structure sheaf `𝒪_X ⊕ M`. -/
def ofModuleSpace {X : RingedSpace.{u}} (M : X.Modules) : RingedSpace.{u} :=
  (squareZeroSheaf M).toRingedSpace

/-- The canonical inclusion into the square-zero extension by `M`. -/
def inclusion {X : RingedSpace.{u}} (M : X.Modules) : X ⟶ ofModuleSpace M :=
  InducedCategory.homMk
    { base := 𝟙 X.carrier
      c := (SquareZeroSheaf.fst M).hom }

/-- The canonical retraction of the square-zero extension by `M`. -/
def retraction {X : RingedSpace.{u}} (M : X.Modules) : ofModuleSpace M ⟶ X :=
  InducedCategory.homMk
    { base := 𝟙 X.carrier
      c := (SquareZeroSheaf.inl M).hom }

/-- The canonical inclusion is a first-order thickening. -/
instance instIsFirstOrderThickening_inclusion {X : RingedSpace.{u}} (M : X.Modules) :
    IsFirstOrderThickening (inclusion M) := sorry

/-- The canonical inclusion is split by the square-zero projection. -/
instance instIsSplitMono_inclusion {X : RingedSpace.{u}} (M : X.Modules) :
    IsSplitMono (inclusion M) :=
  ⟨⟨retraction M, sorry⟩⟩

/-- The square-zero extension by `M` is trivial. -/
instance instIsTrivial_inclusion {X : RingedSpace.{u}} (M : X.Modules) :
    IsTrivial (inclusion M) := inferInstance

/-- The trivialized square-zero extension associated to `M`. -/
def ofModule {X : RingedSpace.{u}} (M : X.Modules) : Trivialized X :=
  Trivialized.mk (ofModuleSpace M) (inclusion M) ⟨retraction M, sorry⟩

/-- The square-zero algebra map induced by a module morphism. -/
def ofModuleMap_sheaf {X : RingedSpace.{u}} {M N : X.Modules} (φ : N ⟶ M) :
    squareZeroSheaf N ⟶ squareZeroSheaf M :=
  ObjectProperty.homMk
    { app U :=
        CommRingCat.ofHom (TrivSqZeroExt.map (φ.val.app U).hom).toRingHom
      naturality {_ _} rho := sorry }

/-- The ringed-space morphism induced by a map of modules. -/
def ofModuleMap_hom {X : RingedSpace.{u}} {M N : X.Modules} (φ : N ⟶ M) :
    ofModuleSpace M ⟶ ofModuleSpace N :=
  InducedCategory.homMk
    { base := 𝟙 X.carrier
      c := (ofModuleMap_sheaf φ).hom }

/-- A module morphism induces a retraction-preserving morphism of square-zero thickenings. -/
def ofModuleMap {X : RingedSpace.{u}} {M N : X.Modules} (φ : N ⟶ M) :
    Trivialized.Hom (ofModule M) (ofModule N) :=
  Trivialized.Hom.mk
    (AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.Hom.mk
      (ofModuleMap_hom φ) sorry)
    sorry

end AlgebraicGeometry.RingedSpace.IsFirstOrderThickening
