module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.CartesianSystem

open CategoryTheory AlgebraicGeometry

universe u

/- Directed inverse systems of cartesian scheme squares with chosen cartesian limit cones. -/
#check (AlgebraicGeometry.Scheme.Etale.InverseSystemCartesianSquare :
  (I : Type u) → [Preorder I] → [Nonempty I] → [IsDirected I (· ≤ ·)] → Type (u + 1))
