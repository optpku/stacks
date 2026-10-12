/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.LocalizedExtension

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass.IsLocalizedExtension

/-- Restricting a localized extension along cartesian pullbacks of both members of its
closed cover again gives a localized extension. -/
theorem restrict
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X X' : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType X'.hom]
    {X₁ X₂ X₁' X₂' : Scheme.{u}}
    (i₁ : X₁ ⟶ X.left) (i₂ : X₂ ⟶ X.left)
    (i₁' : X₁' ⟶ X'.left) (i₂' : X₂' ⟶ X'.left)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    [IsClosedImmersion i₁'] [IsClosedImmersion i₂']
    (g : X' ⟶ X) [LocallyOfFiniteType g.left]
    (g₁ : Over.mk (i₁' ≫ X'.hom) ⟶ Over.mk (i₁ ≫ X.hom))
    (g₂ : Over.mk (i₂' ≫ X'.hom) ⟶ Over.mk (i₂ ≫ X.hom))
    [LocallyOfFiniteType g₁.left] [LocallyOfFiniteType g₂.left]
    (square₁ : IsPullback g₁.left i₁' i₁ g.left)
    (square₂ : IsPullback g₂.left
      (Over.homMk i₂' : Over.mk (i₂' ≫ X'.hom) ⟶ X').left
      (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X).left g.left)
    (p : ℤ)
    (ambient : BivariantClass δ (𝟙 (Over.mk (i₂ ≫ X.hom))) p)
    (localized : BivariantClass δ
      (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) p)
    (hlocalized : IsLocalizedExtension δ X i₁ i₂ p ambient localized) :
    IsLocalizedExtension δ X' i₁' i₂' p
      (BivariantClass.restrict δ g₂ (𝟙 (Over.mk (i₂' ≫ X'.hom))) g₂
        IsPullback.of_id_snd p ambient)
      (BivariantClass.restrict δ g₂
        (Over.homMk i₂' : Over.mk (i₂' ≫ X'.hom) ⟶ X') g
        square₂ p localized) := sorry

end AlgebraicGeometry.BivariantClass.IsLocalizedExtension
