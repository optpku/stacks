module

public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveLineFamily.Section

@[expose] public section

open CategoryTheory

universe u

/- The structure morphism of a projective-line family remains available from its shared owner. -/
#check (AlgebraicGeometry.ProjectiveLineFamily.toBase :
  {S : AlgebraicGeometry.Scheme.{u}} → (X : Over S) →
    AlgebraicGeometry.ProjectiveLineFamily.space X ⟶ S)

/- The zero section of a projective-line family remains available from its shared owner. -/
#check (AlgebraicGeometry.ProjectiveLineFamily.zeroSection :
  {S : AlgebraicGeometry.Scheme.{u}} → (X : Over S) →
    X.left ⟶ AlgebraicGeometry.ProjectiveLineFamily.space X)
