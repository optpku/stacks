/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Monoidal
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.StructureSheaf

/-! # The quasi-coherent structure sheaf as tensor unit -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh

variable {S : Scheme.{u}}

/-- The canonical map from the structure sheaf to the quasi-coherent tensor unit. -/
def structureSheafToTensorUnit (X : GroupoidsOver S) [AlgebraicStack X] :
    structureSheaf X ⟶ 𝟙_ (QCoh X) :=
  ObjectProperty.homMk
    ((commFppfModulesEquivalence X).unitIso.hom.app (structureSheaf X).obj ≫
      (fromCommFppfModules X).map (structureSheafCommUnitToTensorUnit X))

/-- The canonical map from the quasi-coherent tensor unit to the structure sheaf. -/
def tensorUnitToStructureSheaf (X : GroupoidsOver S) [AlgebraicStack X] :
    𝟙_ (QCoh X) ⟶ structureSheaf X :=
  ObjectProperty.homMk
    ((fromCommFppfModules X).map (tensorUnitToStructureSheafCommUnit X) ≫
      (commFppfModulesEquivalence X).unitIso.inv.app (structureSheaf X).obj)

/-- The canonical maps between the structure sheaf and the tensor unit are mutual inverses. -/
theorem structureSheaf_tensorUnit_laws (X : GroupoidsOver S) [AlgebraicStack X] :
    structureSheafToTensorUnit X ≫ tensorUnitToStructureSheaf X = 𝟙 (structureSheaf X) ∧
      tensorUnitToStructureSheaf X ≫ structureSheafToTensorUnit X = 𝟙 (𝟙_ (QCoh X)) :=
  sorry

/-- The structure sheaf is canonically isomorphic to the quasi-coherent tensor unit. -/
def structureSheafIsoTensorUnit (X : GroupoidsOver S) [AlgebraicStack X] :
    structureSheaf X ≅ 𝟙_ (QCoh X) where
  hom := structureSheafToTensorUnit X
  inv := tensorUnitToStructureSheaf X
  hom_inv_id := (structureSheaf_tensorUnit_laws X).1
  inv_hom_id := (structureSheaf_tensorUnit_laws X).2

/-- The forward isomorphism map is the canonical structure-sheaf comparison. -/
theorem structureSheafIsoTensorUnit_hom (X : GroupoidsOver S) [AlgebraicStack X] :
    (structureSheafIsoTensorUnit X).hom = structureSheafToTensorUnit X :=
  rfl

/-- The inverse isomorphism map is the canonical tensor-unit comparison. -/
theorem structureSheafIsoTensorUnit_inv (X : GroupoidsOver S) [AlgebraicStack X] :
    (structureSheafIsoTensorUnit X).inv = tensorUnitToStructureSheaf X :=
  rfl

end AlgebraicGeometry.GroupoidsOver.QCoh
