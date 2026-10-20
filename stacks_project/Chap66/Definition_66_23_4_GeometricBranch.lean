module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricBranch

/-!
# Geometric-point branch-number compatibility checks

The geometric-point branch-number API is owned by the geometric-branch module.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.geometricBranchNumberAt :
  {S : Scheme.{u}} → (X : AlgebraicSpace S) → GeometricPoint X → ℕ∞)

#check (AlgebraicGeometry.AlgebraicSpace.geometricBranchNumberAt_eq_encard_minimalPrimes :
  {S : Scheme.{u}} → (X : AlgebraicSpace S) → (xbar : GeometricPoint X) →
    X.geometricBranchNumberAt xbar = (minimalPrimes (etaleLocalRing X xbar)).encard)

#check (AlgebraicGeometry.AlgebraicSpace.geometricBranchNumberAt_eq :
  {S : Scheme.{u}} → {X : AlgebraicSpace S} → {xbar ybar : GeometricPoint X} →
    xbar.image = ybar.image →
    X.geometricBranchNumberAt xbar = X.geometricBranchNumberAt ybar)

#check (AlgebraicGeometry.AlgebraicSpace.geometricBranchNumberAt_ofOver :
  {S : Scheme.{u}} → {U : Over S} → (p : GeometricPoint (ofOver U)) →
    geometricBranchNumberAt (ofOver U) p =
      (minimalPrimes (Scheme.etaleLocalRing U.left p.toScheme)).encard)

#check (AlgebraicGeometry.AlgebraicSpace.geometricBranchNumberAt_eq_nat_iff :
  {S : Scheme.{u}} → {X : AlgebraicSpace S} → (xbar : GeometricPoint X) →
    {n : ℕ} → 0 < n →
    (X.geometricBranchNumberAt xbar = n ↔
      ∀ ybar : GeometricPoint X, ybar.liesOver xbar.image →
        (minimalPrimes (etaleLocalRing X ybar)).encard = n))

end AlgebraicGeometry.AlgebraicSpace
