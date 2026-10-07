module

public import ReasLib.CategoryTheory.Pretriangulated.Generation.Orthogonal
public import ReasLib.CategoryTheory.Pretriangulated.Generation.Generated
public import ReasLib.CategoryTheory.Pretriangulated.Generation.Comparison
public import ReasLib.CategoryTheory.Pretriangulated.Generation.Functor
public import ReasLib.CategoryTheory.Pretriangulated.Generation.Compact

/-!
# Generation in Pretriangulated Categories

Convenience import for weak generation, compact generation, object-level positive-stage
bridges for Mathlib's triangulated envelope, and their transport by exact triangulated
functors. Classical and strong triangulated generator predicates are owned directly by
`Mathlib.CategoryTheory.Triangulated.Generators`. Use a narrower leaf when only
one layer is needed.
-/
