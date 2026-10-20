module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiberDimension.Target

/-!
# Target-indexed fibre dimensions of morphisms of algebraic spaces

The fibre dimension at a target point is the supremum of the relative
dimensions along the set-theoretic fibre. The following checks retain the
computation and bound specifications.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.31.1: The target-indexed fibre dimension and its specifications. -/
#check (AlgebraicGeometry.AlgebraicSpace.fiberDimension :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    Points Y → WithBot ℕ∞)

#check (AlgebraicGeometry.AlgebraicSpace.fiberDimension_apply :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (y : Points Y),
    fiberDimension f y = ⨆ x ∈ fiberOver f y, fiberDimensionAt f x)

#check (AlgebraicGeometry.AlgebraicSpace.fiberDimension_eq_bot_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [FiniteType f]
    (y : Points Y), fiberDimension f y = ⊥ ↔ y ∉ Set.range (Points.map f))

#check (AlgebraicGeometry.AlgebraicSpace.fiberDimension_le_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (y : Points Y) (d : ℕ),
    fiberDimension f y ≤ (d : WithBot ℕ∞) ↔
      ∀ x ∈ fiberOver f y, RelativeDimensionLEAt f d x)
