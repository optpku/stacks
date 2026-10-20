module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.LocalGenerators
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FittingIdeal.Stalk

/-!
# Étale local generators and Fitting stalks on algebraic spaces

The generation predicate and the Fitting stalk ideal are provided by their
mathematical owners.
-/

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Modules.existsEtaleGeneratedBy :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S},
    X.Modules → AlgebraicGeometry.AlgebraicSpace.Points X → ℕ → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.fittingIdealStalkIdeal :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
    (F : X.Modules) (r : ℕ) (xbar : AlgebraicGeometry.AlgebraicSpace.GeometricPoint X),
    Ideal (AlgebraicGeometry.AlgebraicSpace.etaleLocalRing X xbar))
