module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Resolution

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A resolution is minimal when every resolution over the same integral Noetherian target factors
through it. -/
def IsMinimalResolution {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsNoetherian Y] [IsIntegral Y] [IsResolution f] : Prop :=
  ∀ (Z : Scheme.{u}) (g : Z ⟶ Y) [IsResolution g],
    ∃ u : Z ⟶ X, u ≫ f = g

/-- A resolution is minimal exactly when every resolution over its target factors through it. -/
theorem isMinimalResolution_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsNoetherian Y] [IsIntegral Y] [IsResolution f] :
    IsMinimalResolution f ↔
      ∀ (Z : Scheme.{u}) (g : Z ⟶ Y) [IsResolution g],
        ∃ u : Z ⟶ X, u ≫ f = g := sorry

end AlgebraicGeometry
