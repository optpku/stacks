/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocalizedChern.Situation
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Tensor

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section
universe u

namespace AlgebraicGeometry.LocalizedChern.Situation

open RingedSpace.ModuleDerived

/-- Tensoring two supported perfect complexes preserves their displayed
cartesian-intersection localized-Chern situation. -/
theorem tensorOnIntersection
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z₁ Z₂ W : Scheme.{u}}
    (i₁ : Z₁ ⟶ X.left) (i₂ : Z₂ ⟶ X.left) (iW : W ⟶ X.left)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion iW]
    (j₁ : Over.mk (iW ≫ X.hom) ⟶ Over.mk (i₁ ≫ X.hom))
    (j₂ : Over.mk (iW ≫ X.hom) ⟶ Over.mk (i₂ ≫ X.hom))
    (square : IsPullback j₁.left j₂.left i₁ i₂)
    (intersection : j₂ ≫ (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) =
      (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X))
    [KFlat.HomotopyTensorDescends X.left.toRingedSpace]
    [KFlat.TensorDescends X.left.toRingedSpace]
    [KFlat.IsLocalization X.left.toRingedSpace]
    (F₁ F₂ : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (situation₁ : LocalizedChern.Situation S δ X i₁ F₁ 0 .vanishing)
    (situation₂ : LocalizedChern.Situation S δ X i₂ F₂ 0 .vanishing) :
    LocalizedChern.Situation S δ X iW
      (CategoryTheory.MonoidalCategory.tensorObj F₁ F₂) 0 .vanishing := by
  sorry

end AlgebraicGeometry.LocalizedChern.Situation
