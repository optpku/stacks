module

public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.FixedPseudoPullback.RelativeDiagonal
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.FixedPseudoPullback.Comparison
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.FixedPseudoPullback.Inverse
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.FixedPseudoPullback.Equivalence

/-!
# Fixed groupoid-fibred pseudo-pullback comparison

Aggregate for `RelativeInertia.relativeDiagonal`, `diagonalComparison`,
`diagonalComparison.inverse`, and `diagonalComparisonEquivalence`, together with their
object-, morphism-, and automorphism-level computations.
Import the smallest leaf required by new developments.
All four data owners live directly under
`FiberedCategoryOver.Groupoids.RelativeInertia`; no compatibility aliases are exported.
-/

@[expose] public section
