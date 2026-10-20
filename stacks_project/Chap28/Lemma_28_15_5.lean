module

import ReasLib.AlgebraicGeometry.Scheme.Branch.MinimalPrime
import StacksCheckRecall

open AlgebraicGeometry
open scoped BigOperators

universe u v w

/- Lemma 28.15.5: the number of branches at a scheme point is the sum of the
branch numbers of the irreducible components through that point. -/
@[stacks 0E20] #check
  (AlgebraicGeometry.Scheme.branchNumberAt_eq_tsum_quotient_minimalPrimes :
    ∀ {X : Scheme.{u}} (x : X)
      (Ah : Type v) [CommRing Ah] [Algebra (X.presheaf.stalk x) Ah]
      [IsHenselizationOf (X.presheaf.stalk x) Ah]
      (Ahp : minimalPrimes (X.presheaf.stalk x) → Type w)
      [∀ p, CommRing (Ahp p)]
      [∀ p, Algebra ((X.presheaf.stalk x) ⧸ p.1) (Ahp p)]
      [∀ p, IsHenselizationOf ((X.presheaf.stalk x) ⧸ p.1) (Ahp p)],
      X.branchNumberAt x Ah =
        ∑' p : minimalPrimes (X.presheaf.stalk x),
          branchNumber ((X.presheaf.stalk x) ⧸ p.1) (Ahp p))

/- The geometric branch-number variant of the same decomposition. -/
#check
  (AlgebraicGeometry.Scheme.geometricBranchNumberAt_eq_tsum_quotient_minimalPrimes :
    ∀ {X : Scheme.{u}} (x : X)
      (Ash : Type v) [CommRing Ash] [Algebra (X.presheaf.stalk x) Ash]
      [IsStrictHenselizationOf (X.presheaf.stalk x) Ash]
      (Ashp : minimalPrimes (X.presheaf.stalk x) → Type w)
      [∀ p, CommRing (Ashp p)]
      [∀ p, Algebra ((X.presheaf.stalk x) ⧸ p.1) (Ashp p)]
      [∀ p, IsStrictHenselizationOf ((X.presheaf.stalk x) ⧸ p.1) (Ashp p)],
      X.geometricBranchNumberAt x Ash =
        ∑' p : minimalPrimes (X.presheaf.stalk x),
          geometricBranchNumber ((X.presheaf.stalk x) ⧸ p.1) (Ashp p))
