module
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme
/-! Source facade for representability by a scheme. -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.IsScheme.spec :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsScheme X],
    ∃ (T : Over S), Nonempty (X ≅ ofOver T))
