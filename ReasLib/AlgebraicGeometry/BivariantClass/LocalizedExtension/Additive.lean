/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.LocalizedExtension
public import ReasLib.AlgebraicGeometry.BivariantClass.Additive

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass.IsLocalizedExtension

/-- The sum of two localized extensions is a localized extension of the sum. -/
theorem add
    {S : Scheme.{u}} [UniversallyCatenary S] {delta : S → ℤ}
    [IsDimensionFunction delta] {X : Over S} [LocallyOfFiniteType X.hom]
    {X₁ X₂ : Scheme.{u}} {i₁ : X₁ ⟶ X.left} {i₂ : X₂ ⟶ X.left}
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] {p : ℤ}
    {ambientE ambientF : BivariantClass delta (𝟙 (Over.mk (i₂ ≫ X.hom))) p}
    {localizedE localizedF : BivariantClass delta
      (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) p}
    (hE : IsLocalizedExtension delta X i₁ i₂ p ambientE localizedE)
    (hF : IsLocalizedExtension delta X i₁ i₂ p ambientF localizedF) :
    IsLocalizedExtension delta X i₁ i₂ p
      (BivariantClass.pointwiseAdd delta (𝟙 (Over.mk (i₂ ≫ X.hom))) p
        ambientE ambientF)
      (BivariantClass.pointwiseAdd delta
        (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) p localizedE localizedF) := sorry

end AlgebraicGeometry.BivariantClass.IsLocalizedExtension
