module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalDeformation.DualNumber.FrobeniusShear

/-!
# A versal predeformation quotient that fails Schlessinger's condition (S2)

The explicit Frobenius shear over the square subfield of `F₂(t)` generates a finite
nontrivial dual-number automorphism subgroup fixing epsilon. Its orbit quotient
has a smooth versal presentation, bijective differential on derivation orbits, and
tangent space described by orbit classes, but does not satisfy (S2).

The operator-authorized local erratum restricts the general orbit-bijectivity
claim to subgroups whose infinitesimal scaling coefficients are all one; the
explicit shear satisfies this condition. The original source remains unchanged.
-/

@[expose] public section

open CategoryTheory

/- Example 90.15.3: the explicit Frobenius shear quotient realizes the counterexample,
with the operator-authorized scaling correction and the smoothness and tangent-quotient
clauses retained. -/
@[stacks 06T7] #check
  (ArtinianLocalAlgCat.FrobeniusShear.versal_not_schlessingerS2 :
    Functor.IsPredeformationCategory
        (ArtinianLocalAlgCat.quotientProjection ArtinianLocalAlgCat.FrobeniusShear.shearGroup) ∧
      FormalObject.IsVersal
        (ArtinianLocalAlgCat.quotientFormalObject ArtinianLocalAlgCat.FrobeniusShear.shearGroup) ∧
      FormalObject.BijectiveDifferentialOnOrbits
        (ArtinianLocalAlgCat.quotientFormalObject ArtinianLocalAlgCat.FrobeniusShear.shearGroup) ∧
      ¬ Functor.HasSchlessingerS2
        (ArtinianLocalAlgCat.quotientProjection ArtinianLocalAlgCat.FrobeniusShear.shearGroup) ∧
      BasedFunctor.IsSmooth
        (ArtinianLocalAlgCat.quotientBasedFunctor ArtinianLocalAlgCat.FrobeniusShear.shearGroup) ∧
      Function.Bijective
        (ArtinianLocalAlgCat.tangentSpaceMkQuot ArtinianLocalAlgCat.FrobeniusShear.shearGroup))
