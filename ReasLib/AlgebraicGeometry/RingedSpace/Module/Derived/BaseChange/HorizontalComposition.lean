module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.BaseChange
public import ReasLib.CategoryTheory.Adjunction.BaseChange.HorizontalComposition
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Horizontal composition of unbounded ringed-space base-change maps

The generic adjunction-mate pasting API specializes directly to derived module pullback and
pushforward.  Composite pullback identifications remain explicit data, so callers may use either
canonical comparison isomorphisms or application-specific ones.
-/

open AlgebraicGeometry CategoryTheory
open scoped RingedSpace.Hom RingedSpaceDerivedPullback RingedSpaceDerivedPushforward

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom.DerivedBaseChange.HorizontalComposition

variable {X₂ X₁ X₀ Y₂ Y₁ Y₀ : RingedSpace.{u}}

/-- The derived-pullback square obtained by horizontally pasting two base-change squares. -/
@[stacks 0ATM "horizontally pasted derived base-change square"]
noncomputable abbrev squareIso
    {g₁ : X₂ ⟶ X₁} {g₀ : X₁ ⟶ X₀}
    {f₂ : X₂ ⟶ Y₂} {f₁ : X₁ ⟶ Y₁} {f₀ : X₀ ⟶ Y₀}
    {h₁ : Y₂ ⟶ Y₁} {h₀ : Y₁ ⟶ Y₀}
    (square₀ : L(h₀)^* ⋙ L(f₁)^* ≅ L(f₀)^* ⋙ L(g₀)^*)
    (square₁ : L(h₁)^* ⋙ L(f₂)^* ≅ L(f₁)^* ⋙ L(g₁)^*)
    (leftComp : modulePullbackDerived (h₁ ≫ h₀) ≅ L(h₀)^* ⋙ L(h₁)^*)
    (rightComp : modulePullbackDerived (g₁ ≫ g₀) ≅ L(g₀)^* ⋙ L(g₁)^*) :
    modulePullbackDerived (h₁ ≫ h₀) ⋙ L(f₂)^* ≅
      L(f₀)^* ⋙ modulePullbackDerived (g₁ ≫ g₀) :=
  CategoryTheory.DerivedBaseChange.HorizontalComposition.squareIso
    square₀ square₁ leftComp rightComp

/-- The objectwise horizontal composite of two unbounded ringed-space base-change components. -/
@[stacks 0ATM "horizontal composite of unbounded base-change components"]
noncomputable abbrev map
    {g₁ : X₂ ⟶ X₁} {g₀ : X₁ ⟶ X₀}
    {f₂ : X₂ ⟶ Y₂} {f₁ : X₁ ⟶ Y₁} {f₀ : X₀ ⟶ Y₀}
    {h₁ : Y₂ ⟶ Y₁} {h₀ : Y₁ ⟶ Y₀}
    (leftComp : modulePullbackDerived (h₁ ≫ h₀) ≅ L(h₀)^* ⋙ L(h₁)^*)
    (rightComp : modulePullbackDerived (g₁ ≫ g₀) ≅ L(g₀)^* ⋙ L(g₁)^*)
    (K : DerivedCategory X₀.Modules)
    (η₀ : (source f₀ h₀).obj K ⟶ (target g₀ f₁).obj K)
    (η₁ : (source f₁ h₁).obj ((L(g₀)^*).obj K) ⟶
      (target g₁ f₂).obj ((L(g₀)^*).obj K)) :
    (source f₀ (h₁ ≫ h₀)).obj K ⟶ (target (g₁ ≫ g₀) f₂).obj K :=
  CategoryTheory.DerivedBaseChange.HorizontalComposition.map
    leftComp rightComp K η₀ η₁

/-- Remark 20.28.5 (0ATM): horizontal composition preserves the objectwise base-change mate
equation. -/
@[stacks 0ATM "horizontal composition preserves unbounded base change"]
theorem map_isMapAt
    {g₁ : X₂ ⟶ X₁} {g₀ : X₁ ⟶ X₀}
    {f₂ : X₂ ⟶ Y₂} {f₁ : X₁ ⟶ Y₁} {f₀ : X₀ ⟶ Y₀}
    {h₁ : Y₂ ⟶ Y₁} {h₀ : Y₁ ⟶ Y₀}
    (square₀ : L(h₀)^* ⋙ L(f₁)^* ≅ L(f₀)^* ⋙ L(g₀)^*)
    (square₁ : L(h₁)^* ⋙ L(f₂)^* ≅ L(f₁)^* ⋙ L(g₁)^*)
    (leftComp : modulePullbackDerived (h₁ ≫ h₀) ≅ L(h₀)^* ⋙ L(h₁)^*)
    (rightComp : modulePullbackDerived (g₁ ≫ g₀) ≅ L(g₀)^* ⋙ L(g₁)^*)
    (adj₀ : L(f₀)^* ⊣ R(f₀)_*) (adj₁ : L(f₁)^* ⊣ R(f₁)_*)
    (adj₂ : L(f₂)^* ⊣ R(f₂)_*)
    (K : DerivedCategory X₀.Modules)
    (η₀ : (source f₀ h₀).obj K ⟶ (target g₀ f₁).obj K)
    (η₁ : (source f₁ h₁).obj ((L(g₀)^*).obj K) ⟶
      (target g₁ f₂).obj ((L(g₀)^*).obj K))
    (hη₀ : IsMapAt adj₀ adj₁ square₀ K η₀)
    (hη₁ : IsMapAt adj₁ adj₂ square₁ ((L(g₀)^*).obj K) η₁) :
    IsMapAt adj₀ adj₂ (squareIso square₀ square₁ leftComp rightComp) K
      (map leftComp rightComp K η₀ η₁) := sorry

/-- The horizontal composite of the two canonical base-change components is the canonical
component for the outer rectangle. -/
@[stacks 0ATM "canonical horizontal base-change composition"]
theorem map_eq
    {g₁ : X₂ ⟶ X₁} {g₀ : X₁ ⟶ X₀}
    {f₂ : X₂ ⟶ Y₂} {f₁ : X₁ ⟶ Y₁} {f₀ : X₀ ⟶ Y₀}
    {h₁ : Y₂ ⟶ Y₁} {h₀ : Y₁ ⟶ Y₀}
    (square₀ : L(h₀)^* ⋙ L(f₁)^* ≅ L(f₀)^* ⋙ L(g₀)^*)
    (square₁ : L(h₁)^* ⋙ L(f₂)^* ≅ L(f₁)^* ⋙ L(g₁)^*)
    (leftComp : modulePullbackDerived (h₁ ≫ h₀) ≅ L(h₀)^* ⋙ L(h₁)^*)
    (rightComp : modulePullbackDerived (g₁ ≫ g₀) ≅ L(g₀)^* ⋙ L(g₁)^*)
    (adj₀ : L(f₀)^* ⊣ R(f₀)_*) (adj₁ : L(f₁)^* ⊣ R(f₁)_*)
    (adj₂ : L(f₂)^* ⊣ R(f₂)_*)
    (K : DerivedCategory X₀.Modules) :
    map leftComp rightComp K
        (DerivedBaseChange.app adj₀ adj₁ square₀ K)
        (DerivedBaseChange.app adj₁ adj₂ square₁ ((L(g₀)^*).obj K)) =
      DerivedBaseChange.app adj₀ adj₂
        (squareIso square₀ square₁ leftComp rightComp) K := sorry

end AlgebraicGeometry.RingedSpace.Hom.DerivedBaseChange.HorizontalComposition
