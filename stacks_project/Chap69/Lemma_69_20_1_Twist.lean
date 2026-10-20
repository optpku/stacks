module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ProjectiveSpace.Twist

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.twistingSheafScheme :
  (n : ℕ) → (S : Scheme.{u}) → (AlgebraicGeometry.ProjectiveSpace n S).Modules)

#check (AlgebraicGeometry.AlgebraicSpace.twistingSheafOfScheme :
  (n : ℕ) → (S : Scheme.{u}) → (ofScheme n S).Modules)

#check (AlgebraicGeometry.AlgebraicSpace.ProjectiveSpace.twistingSheaf :
  (n : ℕ) → {S : Scheme.{u}} → (Y : AlgebraicSpace S) → (ProjectiveSpace n Y).Modules)
