/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.CartesianSystem

open CategoryTheory AlgebraicGeometry

universe u

/- Directed inverse systems of cartesian scheme squares with chosen cartesian limit cones. -/
#check (AlgebraicGeometry.Scheme.Etale.InverseSystemCartesianSquare :
  (I : Type u) → [Preorder I] → [Nonempty I] → [IsDirected I (· ≤ ·)] → Type (u + 1))
