module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Tensor
public import stacks_project.Chap42.Definition_42_50_3_LocalizedClasses

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern.Situation

open RingedSpace.ModuleDerived

/-- A vanishing localized-Chern situation also supplies every positive rank bound. -/
theorem toRankBound
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    {i : Z ⟶ X.left} [IsClosedImmersion i]
    {E : RingedSpace.ModuleDerived X.left.toRingedSpace}
    (situation : Situation S δ X i E 0 .vanishing) (p : ℕ) (hp : 0 < p) :
    Situation S δ X i E p .rankBound := sorry

/-- The tensor product of two perfect complexes supported on closed subschemes is
supported on any displayed cartesian intersection, and retains the finiteness condition. -/
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
    (situation₁ : Situation S δ X i₁ F₁ 0 .vanishing)
    (situation₂ : Situation S δ X i₂ F₂ 0 .vanishing) :
    Situation S δ X iW (F₁ ⊗ᴸ F₂) 0 .vanishing := sorry

end AlgebraicGeometry.LocalizedChern.Situation
