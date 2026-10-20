module

public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Trivialization

/-!
# Trivial first-order thickenings of ringed spaces

This source-facing module preserves the historical names while exposing the
canonical reusable definitions from `ReasLib`.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.RingedSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.RingedSpace.IsFirstOrderThickening

#check (isTrivial_iff :
  ∀ {X X' : RingedSpace.{u}} (i : X ⟶ X') [h : IsFirstOrderThickening i],
    IsTrivial i ↔ ∃ π : X' ⟶ X, i ≫ π = 𝟙 X)
#check (Trivialization.ofRetraction :
  ∀ {X X' : RingedSpace.{u}} {i : X ⟶ X'} [h : IsFirstOrderThickening i],
    (π : X' ⟶ X) → i ≫ π = 𝟙 X → Trivialization i)
#check (ofSplitting_leftInv :
  ∀ {X X' : RingedSpace.{u}} (i : X ⟶ X') [h : IsFirstOrderThickening i],
    (σ : X.presheaf ⟶ (CategoryTheory.inv i.hom.base) _* X'.presheaf) →
      IsAlgebraSplitting i σ → i ≫ ofSplitting i σ = 𝟙 X)
#check (Trivialized.Hom.mk :
  ∀ {X : RingedSpace.{u}} {T₁ T₂ : Trivialized X},
    (f : Hom T₁.inclusion T₂.inclusion) →
      f.hom ≫ T₂.trivialization.retraction = T₁.trivialization.retraction →
      Trivialized.Hom T₁ T₂)

end AlgebraicGeometry.RingedSpace.IsFirstOrderThickening
