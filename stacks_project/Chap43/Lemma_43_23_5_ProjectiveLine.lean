module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.VectorSpace.Line

@[expose] public section

universe u

/- Compatibility bridge for the explicit quotient presentation of projective lines. -/
#check
  (AlgebraicGeometry.ProjectiveSpace.VectorSpace.Line :
    (k : Type u) → [Field k] → (V : Type u) → [AddCommGroup V] → [Module k V] → Type u)
