module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuotientBaseChange
import StacksCheckRecall

universe u

/- Lemma 70.17.4: A quasi-compact quasi-separated algebraic space over an affine
scheme which is not a scheme admits an ideal maximal among those whose quotient
base change is not a scheme. -/
@[stacks 0B81] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_isMaximalNonschemeIdeal :
    ∀ {A : Type u} [CommRing A]
      (X : AlgebraicGeometry.AlgebraicSpace (AlgebraicGeometry.Spec (CommRingCat.of A)))
      [AlgebraicGeometry.AlgebraicSpace.IsQuasiCompact X]
      [AlgebraicGeometry.AlgebraicSpace.IsQuasiSeparated X],
      ¬ AlgebraicGeometry.AlgebraicSpace.IsScheme X →
        ∃ I : Ideal A, AlgebraicGeometry.AlgebraicSpace.IsMaximalNonschemeIdeal X I)
