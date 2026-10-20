module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.NonScheme

/-!
# A family of curves whose total space is not a scheme
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 110.67.1: there exists a field `k` and a family of curves
`X ⟶ affineLine (Spec (CommRingCat.of k))` such that `X` is not a scheme. -/
@[stacks 0D5E] #check (AlgebraicGeometry.AlgebraicSpace.exists_familyOfCurves_affineLine_not_isScheme :
  ∃ (k : Type u) (_ : Field k)
    (X : AlgebraicSpace (Spec (CommRingCat.of k)))
    (f : X ⟶ affineLine (Spec (CommRingCat.of k))),
    FpFlatProper f ∧ RelativeDimensionLE f 1 ∧ ¬ IsScheme X)
