module

public import Mathlib.CategoryTheory.MorphismProperty.Local

public section

universe v u

namespace CategoryTheory.MorphismProperty.IsLocalAtSource

variable {C : Type u} [Category.{v} C]

/-- A morphism property is local at the source for a precoverage if and only if it holds
for a morphism exactly when it holds after precomposition with every member of each covering
family of its source. -/
theorem iff_forall_zeroHypercover (P : MorphismProperty C) (K : Precoverage C)
    [P.RespectsIso] :
    P.IsLocalAtSource K ↔
      ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (𝒰 : Precoverage.ZeroHypercover.{max u v} K X),
        P f ↔ ∀ i, P (𝒰.f i ≫ f) := sorry

end CategoryTheory.MorphismProperty.IsLocalAtSource

namespace CategoryTheory.MorphismProperty.IsLocalAtTarget

variable {C : Type u} [Category.{v} C]

/-- A morphism property is local at the target for a precoverage if and only if it holds
for a morphism exactly when it holds after pullback along every member of each covering
family of its target. -/
theorem iff_forall_zeroHypercover (P : MorphismProperty C) (K : Precoverage C)
    [K.HasPullbacks] [P.RespectsIso] :
    P.IsLocalAtTarget K ↔
      ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (𝒰 : Precoverage.ZeroHypercover.{max u v} K Y),
        P f ↔ ∀ i, P (Limits.pullback.snd f (𝒰.f i)) := sorry

end CategoryTheory.MorphismProperty.IsLocalAtTarget
