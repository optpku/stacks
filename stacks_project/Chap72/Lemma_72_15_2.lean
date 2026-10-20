module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.DimensionFormula
import StacksCheckRecall

/-!
# Dimension formula for dominant morphisms of integral algebraic spaces

A dominant locally finite-type morphism of integral algebraic spaces with
locally Noetherian target obeys the inequality
`dimension X ≤ dimension Y + residueFieldTrdegAt f x` at a generic point `x`.
If the morphism is proper, equality holds.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 72.15.2 -/
@[stacks 0EDC] #check
  (AlgebraicGeometry.AlgebraicSpace.dimension_le_add_residueFieldTrdegAt :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      {X Y : AlgebraicGeometry.AlgebraicSpace S}
      [AlgebraicGeometry.AlgebraicSpace.IsLocallyNoetherian Y]
      [AlgebraicGeometry.AlgebraicSpace.IsIntegral X]
      [AlgebraicGeometry.AlgebraicSpace.IsIntegral Y]
      (f : X ⟶ Y) [AlgebraicGeometry.AlgebraicSpace.Dominant f]
      [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType f]
      {x : AlgebraicGeometry.AlgebraicSpace.Points X}
      (hx : x ∈ AlgebraicGeometry.AlgebraicSpace.genericPoints X),
      AlgebraicGeometry.AlgebraicSpace.dimension X ≤
        AlgebraicGeometry.AlgebraicSpace.dimension Y +
          (AlgebraicGeometry.AlgebraicSpace.residueFieldTrdegAt f x : WithBot ℕ∞))

/- Lemma 72.15.2 -/
@[stacks 0EDC] #check
  (AlgebraicGeometry.AlgebraicSpace.dimension_eq_add_residueFieldTrdegAt_of_proper :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      {X Y : AlgebraicGeometry.AlgebraicSpace S}
      [AlgebraicGeometry.AlgebraicSpace.IsLocallyNoetherian Y]
      [AlgebraicGeometry.AlgebraicSpace.IsIntegral X]
      [AlgebraicGeometry.AlgebraicSpace.IsIntegral Y]
      (f : X ⟶ Y) [AlgebraicGeometry.AlgebraicSpace.Dominant f]
      [AlgebraicGeometry.AlgebraicSpace.Proper f]
      {x : AlgebraicGeometry.AlgebraicSpace.Points X}
      (hx : x ∈ AlgebraicGeometry.AlgebraicSpace.genericPoints X),
      AlgebraicGeometry.AlgebraicSpace.dimension X =
        AlgebraicGeometry.AlgebraicSpace.dimension Y +
          (AlgebraicGeometry.AlgebraicSpace.residueFieldTrdegAt f x : WithBot ℕ∞))
