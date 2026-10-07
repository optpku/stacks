module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Branch

@[expose] public section

universe u v

/- Definition 28.15.4: the number of branches of a scheme at a point is the
number of branches of its local ring, and the number of geometric branches is
the number of geometric branches of its local ring. -/
@[stacks 0C38] #check
  (AlgebraicGeometry.Scheme.branchNumberAt :
    (X : AlgebraicGeometry.Scheme.{u}) → (x : X) →
      (Ah : Type v) → [CommRing Ah] → [Algebra (X.presheaf.stalk x) Ah] →
        [IsHenselizationOf (X.presheaf.stalk x) Ah] → ℕ∞)

#check
  (AlgebraicGeometry.Scheme.geometricBranchNumberAt :
    (X : AlgebraicGeometry.Scheme.{u}) → (x : X) →
      (Ash : Type v) → [CommRing Ash] → [Algebra (X.presheaf.stalk x) Ash] →
        [IsStrictHenselizationOf (X.presheaf.stalk x) Ash] → ℕ∞)
